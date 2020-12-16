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

let box_check param body =
  let rec bound_check param body =
    match body with
    | Var' (VarBound (par, _, _)) -> par=param
    | Def' (e1, e2) -> bound_check param (Var'(e1)) || bound_check param e2
    | If' (pred, dit, dif) -> bound_check param pred || bound_check param dit || bound_check param dif
    | Seq' lst -> ormap (bound_check param) lst
    | Set' (var, expr) -> bound_check param (Var'(var)) || bound_check param expr
    | BoxSet' (_, expr) -> bound_check param expr
    | Or' lst -> ormap (bound_check param) lst
    | Applic' (op, args) | ApplicTP' (op, args) -> bound_check param op || ormap (fun e -> bound_check param e) args
    | LambdaSimple' (params, body) -> if (List.exists (fun e -> e = param) params)
                                      then false
                                      else bound_check param body
    | LambdaOpt' (params, opt, body) -> if (List.exists (fun e -> e = param) (opt::params))
                                       then false
                                       else bound_check param body
    | _ -> false in

  let rec set_check param body =
    match body with
    | If' (pred, dit, dif) -> set_check param pred || set_check param dit || set_check param dif
    | Def' (e1, e2) -> set_check param (Var'(e1)) || set_check param e2
    | Seq' lst -> ormap (set_check param) lst
    | Set' (VarBound (par, _, _), expr) -> par = param || set_check param expr
    | Set' (VarParam (par, _), expr) -> par = param || set_check param expr
    | Set' (var, expr) -> set_check param (Var'(var)) || set_check param expr
    | BoxSet' (_, expr) -> set_check param expr
    | Or' lst -> ormap (set_check param) lst
    | Applic' (op, args) | ApplicTP' (op, args) -> set_check param op || ormap (fun e -> set_check param e) args
    | LambdaSimple' (params, body) ->if (List.exists (fun e -> e = param) params)
                                    then false
                                    else set_check param body
    | LambdaOpt' (params, opt, body) -> if (List.exists (fun e -> e = param) (opt::params))
then false
else set_check param body
| _ -> false in

  let rec get_check param body =
    match body with
    | Var' (VarBound (par, _, _)) | Var' (VarParam (par, _)) -> par = param
    | Def' (e1, e2) -> get_check param (Var'(e1)) || get_check param e2
    | If' (pred, dit, dif) -> get_check param pred || get_check param dit || get_check param dif
    | Seq' lst -> ormap (get_check param) lst
    | Set' (VarBound (par, _, _), expr) | Set' (VarParam (par, _), expr) -> par = param
    | Set' (var, expr) -> get_check param (Var'(var)) || get_check param expr
    | BoxSet' (_, expr) -> get_check param expr
    | Or' lst -> ormap (get_check param) lst
    | Applic' (op, args) | ApplicTP' (op, args) -> get_check param op || ormap (fun e -> get_check param e) args
    | LambdaSimple' (params, body) ->
if (List.exists (fun e -> e = param) params)
then false
else get_check param body
    | LambdaOpt' (params, opt, body) ->
if (List.exists (fun e -> e = param) (opt::params))
then false
else get_check param body
    | _ -> false in

  (bound_check param body) && (set_check param body) && (get_check param body)

  let box_exp param min body =
    let rec add_set_exp param min body =
      match body with
      | Seq' list -> Seq' ([Set' (VarParam (param, min), Box' (VarParam (param, min)))]@list)
      | _ -> Seq' [Set' (VarParam (param, min), Box' (VarParam (param, min))); body] in

    let rec replace_set param body =
      match body with
      | Const' _ | Var' _ | BoxGet' _ | Box' _ -> body
      | BoxSet' (var, expr) -> BoxSet' (var, replace_set param expr)
      | If' (pred, dit, dif) -> If' (replace_set param pred, replace_set param dit, replace_set param dif)
            | Seq' lst -> Seq' (List.map (replace_set param) lst)

      | Def' (VarBound (par, n1, n2), e2) -> 
      let test= replace_set param (Var'(VarBound (par, n1, n2))) in
      (match test with
      | Var'(VarBound (e, n1, n2))-> Def' (VarBound (e, n1, n2), replace_set param e2)
      | _ -> raise X_this_should_not_happen )

      | Def' (VarParam (par, n1), e2) -> 
      let test= replace_set param (Var'(VarParam (par, n1))) in
      (match test with
      | Var'(VarParam (e, n1))-> Def' (VarParam (e, n1), replace_set param e2)
      | _ -> raise X_this_should_not_happen )
      
      | Set' ((VarBound (p, n1, n2)), expr) ->
	      if (p = param)
	      then BoxSet' (VarBound (param, n1, n2), replace_set param expr)
	      else Set' (VarBound (p, n1, n2), replace_set param expr)
      | Set' (VarParam (p, n1), expr) ->
	    if (p = param)
    	then BoxSet' (VarParam (param, n1), replace_set param expr)
	    else Set' (VarParam (p, n1), replace_set param expr)
      | Set' (VarFree var, expr) -> Set' (VarFree var, replace_set param expr)
      | Or' lst -> Or' (List.map (replace_set param) lst)
      | Applic'	(op, args) -> Applic'	(replace_set param op, List.map (replace_set param) args)
      | ApplicTP' (op, args) -> ApplicTP' (replace_set param op, List.map (replace_set param) args)
      | LambdaSimple' (params, body) ->
        if (List.exists (fun e -> e = param) params)
        then LambdaSimple' (params, body)
        else LambdaSimple' (params, replace_set param body)
            | LambdaOpt' (params, opt, body) ->
        if (List.exists (fun e -> e = param) (opt::params))
        then LambdaOpt' (params, opt, body)
        else LambdaOpt' (params, opt, replace_set param body)
            | _ -> raise X_this_should_not_happen in

    let rec replace_get param body =
      match body with
      | Var' (VarBound (par, n1, n2)) ->
          if (par = param)
          then BoxGet' (VarBound (param, n1, n2))
          else body
              | Var' (VarParam (par, n1)) ->
          if (par = param)
          then BoxGet' (VarParam (param, n1))
          else body
      | Const' _ | Var' _ | BoxGet' _ | Box' _ -> body
      | BoxSet' (var, expr) -> BoxSet' (var, replace_get param expr)
      | If' (pred, dit, dif) -> If' (replace_get param pred, replace_get param dit, replace_get param dif)
     
      | Def' (VarBound (par, n1, n2), e2) ->
       let test= replace_get param (Var'(VarBound (par, n1, n2))) in
        (match test with
        | Var'(VarBound (e, n1, n2))-> Def' (VarBound (e, n1, n2), replace_get param e2)
        | _ -> raise X_this_should_not_happen )
     
      | Def' (VarParam (par, n1), e2) ->
      let test= replace_get param (Var'(VarParam (par, n1))) in
        (match test with
        | Var'(VarParam (e, n1))-> Def' (VarParam (e, n1), replace_get param e2)
        | _ -> raise X_this_should_not_happen )
 
      | Seq' lst -> Seq' (List.map (fun e -> replace_get param e) lst)
      | Set' (VarBound (par, n1, n2), expr) ->
	        if (par = param)
          then Set' (VarBound (param, n1, n2), replace_get param expr) 
          else 
          let temp= replace_get param (Var' (VarBound (par, n1, n2))) in
         ( match temp with
          | Var'(VarBound (par, n1, n2))->Set' (VarBound (par, n1, n2), replace_get param expr) 
          |_ -> raise X_this_should_not_happen 
         )
      | Set' (VarParam (par, n1), expr) ->
          if (par = param)
          then Set' (VarParam (param, n1), replace_get param expr) 
          else 
          let temp= replace_get param (Var' (VarParam (par, n1))) in
        ( match temp with
          | Var'(VarParam (par, n1))->Set' (VarParam (par, n1), replace_get param expr) 
          |_ -> raise X_this_should_not_happen 
        )
      | Set' (VarFree (var), expr) -> Set' (VarFree (var), replace_get param expr)
      | Or' lst -> Or' (List.map (fun e -> replace_get param e) lst)
      | Applic' (op, args) ->		Applic'   (replace_get param op, List.map (fun e -> replace_get param e) args)
      | ApplicTP' (op, args) ->	ApplicTP' (replace_get param op, List.map (fun e -> replace_get param e) args)
      | LambdaSimple' (params, body) ->
      if (List.exists (fun e -> e = param) params)
      then LambdaSimple' (params, body)
      else LambdaSimple' (params, replace_get param body)
          | LambdaOpt' (params, opt, body) ->
      if (List.exists (fun e -> e = param) (opt::params))
      then LambdaOpt' (params, opt, body)
      else LambdaOpt' (params, opt, replace_get param body)
          | _ -> raise X_this_should_not_happen in

    let body = replace_get param body in
    let body = replace_set param body in
    add_set_exp param min body;;



let box params body =
  let foldfunc (param, min) body =
    if (box_check param body)
    then (box_exp param min body)
    else body in
  let rec inds = function
    | 0 -> []
    | n -> (inds (n-1))@[(n-1)] in
  let params = List.combine params (inds (List.length params)) in
  List.fold_right foldfunc params body;;
  let box_set2 e = determine_boxing e [];;
  
  let box_set e =
    let rec extract_body exp =
      match exp with
      | Const' _ | Var' _ | Box' _ | BoxGet' _ -> exp
      | BoxSet' (var, expr) -> BoxSet' (var, extract_body expr)

      | Def' (VarBound (par, n1, n2), e2) -> 
        let test= extract_body  (Var'(VarBound (par, n1, n2))) in
        (match test with
          | Var'(VarBound (e, n1, n2))-> Def' (VarBound (e, n1, n2), extract_body  e2)
            | _ -> raise X_this_should_not_happen )
      
      | Def' (VarParam (par, n1), e2) -> 
        let test= extract_body  (Var'(VarParam (par, n1))) in
        (match test with
          | Var'(VarParam (e, n1))-> Def' (VarParam (e, n1), extract_body  e2)
          | _ -> raise X_this_should_not_happen )
      
      | Def' (VarFree (var), e2) -> 
        let test= extract_body  (Var'(VarFree (var))) in
        (match test with
          | Var'(VarFree (var))-> Def' (VarFree (var), extract_body  e2)
          | _ -> raise X_this_should_not_happen )
      
      | If' (pred, dit, dif) -> If' (extract_body pred, extract_body dit, extract_body dif)
      | Seq' lst -> Seq' (List.map extract_body lst)
      
      | Set'(VarParam (variable,indx), e2) -> 
        let test= extract_body  (Var'(VarParam (variable,indx))) in
        (match test with
          | Var'(VarParam (e, n1))-> Set' (VarParam (e, n1), extract_body  e2)
          | _ -> raise X_this_should_not_happen )

      | Set'(VarBound (par, n1, n2), e2)->
        let test= extract_body  (Var'(VarBound (par, n1, n2))) in
        (match test with
          | Var'(VarBound (e, n1, n2))-> Set' (VarBound (e, n1, n2), extract_body  e2)
          | _ -> raise X_this_should_not_happen )

      | Set'(VarFree (par), e2)->
      let test= extract_body  (Var'(VarFree (par))) in
      (match test with
        | Var'(VarFree (e))-> Set' (VarFree (e), extract_body  e2)
        | _ -> raise X_this_should_not_happen )
  
      | Or' lst -> Or' (List.map extract_body lst)
      | Applic' (op, args) -> Applic' (extract_body op, List.map extract_body args)
      | ApplicTP' (op, args) -> ApplicTP' (extract_body op, List.map extract_body args)
      | LambdaSimple' (params, body) -> LambdaSimple' (params, extract_body (box params body))
      | LambdaOpt' (params, opt, body) -> LambdaOpt' (params, opt, extract_body (box (opt::params) body)) in
    extract_body e;;  




    let run_semantics expr =
      box_set
        (annotate_tail_calls
           (annotate_lexical_addresses expr));;
           end;; (* struct Semantics *)
    