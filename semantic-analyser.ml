#use "tag-parser.ml";;

type var = 
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | Const' of constant
  | Var' of var
  | Box' of var
  | BoxGet' of var
  | BoxSet' of var * expr'
  | If' of expr' * expr' * expr'
  | Seq' of expr' list
  | Set' of var * expr'
  | Def' of var * expr'
  | Or' of expr' list
  | LambdaSimple' of string list * expr'
  | LambdaOpt' of string list * string * expr'
  | Applic' of expr' * (expr' list)
  | ApplicTP' of expr' * (expr' list);;

let rec expr'_eq e1 e2 =
  match e1, e2 with
  | Const' Void, Const' Void -> true
  | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
  | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
  | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
  | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
  | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                            (expr'_eq th1 th2) &&
                                              (expr'_eq el1 el2)
  | (Seq'(l1), Seq'(l2)
  | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
  | (Set'(var1, val1), Set'(var2, val2)
  | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq (Var'(var1)) (Var'(var2))) &&
                                             (expr'_eq val1 val2)
  | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr'_eq body1 body2)
  | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr'_eq body1 body2)
  | Applic'(e1, args1), Applic'(e2, args2)
  | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
	 (expr'_eq e1 e2) &&
	   (List.for_all2 expr'_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type SEMANTICS = sig
  val run_semantics : expr -> expr'
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
end;;

module Semantics : SEMANTICS = struct

(* ---------------------- *)
(* Q3.2 *)
(* ---------------------- *)

(* Returns index of tring x in string list lst, -1 if doesnt exist *)
let index_of x lst = 
  let rec f x lst count =
    match lst with
    | [] -> -1
    | car::cdr -> if (String.equal car x) then count else (f x cdr (count+1))
  in
  f x lst 0;;

(* vars is list of variables(string) list 
    orderd by leftmost is current lexical env, each hop to the right meand on lex above*)
let rec annotate vars e= 
  let get_v vr= 
    match vr with
    | Var(v) -> v
    | _ -> nt_none()
  in
  match e with 
  | Const(e) -> Const'(e) 
  | Var(v) -> Var'(ann_var v vars)
  | If(tst,dit,dif) -> If'((annotate vars tst),(annotate vars dit),(annotate vars dif))
  | Seq(s) -> Seq'((List.map (annotate vars) s))
  | Or(lst) -> Or'((List.map (annotate vars) lst))
  | LambdaSimple(var_list, body) -> LambdaSimple'(var_list,(annotate ([var_list]@vars) body))
  | LambdaOpt(var_list,opt,body) -> LambdaOpt'(var_list,opt,(annotate ([var_list@[opt]]@vars) body))
  | Applic (op,lst) -> Applic'((annotate vars op), (List.map (annotate vars) lst))
  | Set(v,n) -> Set'((ann_var (get_v v) vars),(annotate vars n))
  | Def(a,b) -> Def'((ann_var (get_v a) vars),(annotate vars b))
  
and ann_var v var_list =
  let rec check_bound lst major= 
    match lst with 
    | [] -> (-1,-1)
    | car::cdr -> if car != -1 then (major,car) else  (check_bound cdr (major+1))
  in
  let check =  List.map (index_of v) var_list in
  let res = 
    match check with
    | [] -> VarFree(v)
    | car::cdr ->
      if car > -1 then VarParam(v,car) else 
      (let major,minor = check_bound cdr 0 in 
      if (minor != -1) then VarBound(v,major,minor) else VarFree(v)) 
  in
  res

let annotate_lexical_addresses e = annotate [[]] e;;
  

(* ---------------------- *)
(* Q3.3 *)
(* ---------------------- *)

(* changes all calls is tail position from Applic' -> ApplicTP' *)
let rec change_to_tp in_tp e = 
  let split_last = fun (l) -> ((List.rev (List.tl (List.rev l))),(List.hd (List.rev l))) in
  match e with 
  | If'(tst,dit,dif) -> If'(tst,(change_to_tp in_tp dit),(change_to_tp in_tp dif))
  | Seq'(s) -> let rest,last = split_last s in
    Seq'(((List.map (change_to_tp false) rest))@[change_to_tp in_tp last])
  | Or'(lst) -> let rest,last = split_last lst in
    Or'(((List.map (change_to_tp false) rest))@[change_to_tp in_tp last])
  | LambdaSimple'(var_list, body) -> LambdaSimple'(var_list,(change_to_tp true body))
  | LambdaOpt'(var_list,opt,body) -> LambdaOpt'(var_list,opt,(change_to_tp true body))
  | Applic'(op,lst) -> if in_tp then ApplicTP'((change_to_tp false op),(List.map (change_to_tp false ) lst)) else Applic'((change_to_tp false op),(List.map (change_to_tp false) lst))
  | Set'(v,n) -> Set'(v,(change_to_tp false n))
  | Def'(a,b) -> Def'(a,(change_to_tp in_tp b)) 
  | other -> other ;;

let annotate_tail_calls e = change_to_tp false e;;

(* ---------------------- *)
let box_set e = e;;

let run_semantics expr =
  box_set
    (annotate_tail_calls
       (annotate_lexical_addresses expr));;
  
end;; (* struct Semantics *)


