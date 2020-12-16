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
let param_name param = List.nth param 0;;

let var_in_list var var_list = ((List.mem ((param_name var)::["1"]) var_list) || (List.mem ((param_name var)::["0"]) var_list));;

let rec remove_duplicates_rec var_list unique_var_list = match var_list with
  | [] -> unique_var_list
  | var::rest -> if (var_in_list var unique_var_list) 
                  then (remove_duplicates_rec rest unique_var_list) 
                  else (remove_duplicates_rec rest (var::unique_var_list));;

let remove_duplicates var_list = remove_duplicates_rec var_list [];;

let extract_variable_name variable = match variable with 
  | VarBound(name, level, index) -> name
  | VarParam(name, index) -> name
  (* TODO: raise exception? *)
  | _ -> "Variable Name Not Found"

let make_param_setter param_name index = Set'(VarParam(param_name, index), Box'(VarParam(param_name, index)));;

let should_box param = List.nth param 1 = "1";;

let rec convert_params_to_sets params index = match params with 
  | [] -> []
  | param::rest -> if(should_box param) 
                    then ((make_param_setter (param_name param) index)::(convert_params_to_sets rest (index+1))) 
                    else (convert_params_to_sets rest (index+1));;

let create_seq params body = Seq'(List.append (convert_params_to_sets params 0) [body]);; 

let rec any_param_for_boxing marked_params = match marked_params with 
  | [] -> false
  | first_param::rest -> if (should_box first_param) then true else any_param_for_boxing rest;;

let rec count_param_writing_occurrences param body count = match body with
  | Const'(value) -> []
  | Var'(variable) -> []
  | Set'(VarParam (variable,indx), value) -> List.append (if (variable = param) then [-1] else []) 
                                               (count_param_writing_occurrences param value (count+1))
  | Set'(VarBound (variable,level,index), value) -> List.append (if (variable = param) then [-1] else []) 
  (count_param_writing_occurrences param value (count+1))
  | Applic'(expression, args) -> List.append (count_param_writing_occurrences param expression count) (map_count_writing_occurences args param count)
  | ApplicTP'(expression, args) -> List.append (count_param_writing_occurrences param expression count) (map_count_writing_occurences args param count)
  | Seq'(exp_list) -> map_count_writing_occurences exp_list param count
  | Or'(exp_list) -> map_count_writing_occurences exp_list param count
  | Def'(variable, value) -> List.append (count_param_writing_occurrences param (Var'(variable)) count) (count_param_writing_occurrences param value count)

  | If'(test, dit, dif) -> List.append 
                            (List.append 
                                (count_param_writing_occurrences param test (count+1)) 
                                (count_param_writing_occurrences param dit (count+1))
                            ) 
                            (count_param_writing_occurrences param dif (count+1))
  (* if param is in the lambda param_list it is in a new lexical scope, so no occurrence *)
  | LambdaSimple'(p_list, b) -> if (List.mem param p_list) 
                                  then [] 
                                  else (if ((count_param_writing_occurrences param b (count+1)) = []) then [] else [count])
  (* if param is in the lambda param_list it is in a new lexical scope, so no occurrence *)
  | LambdaOpt'(p_list, opt_p, b) -> if (List.mem param (List.append p_list [opt_p]))
                                      then [] 
                                      else (if ((count_param_writing_occurrences param b (count+1)) = []) then [] else [count])
  | _ -> []
  
  and map_count_writing_occurences exp_list param count = match exp_list with
    | [] -> []
    | first_exp::rest -> List.append (count_param_writing_occurrences param first_exp count) (map_count_writing_occurences rest param (count+1));;


let rec count_param_reading_occurrences param body count = match body with
  | Const'(value) -> []
  | Var'(variable) -> if ((extract_variable_name variable) = param) then [-1] else []
  | Set'(variable, value) -> (count_param_reading_occurrences param value (count+1))
  | Applic'(expression, args) -> List.append (count_param_reading_occurrences param expression count) (map_count_reading_occurences args param count)
  | ApplicTP'(expression, args) -> List.append (count_param_reading_occurrences param expression count) (map_count_reading_occurences args param count)
  | Seq'(exp_list) -> map_count_reading_occurences exp_list param count
  | Or'(exp_list) -> map_count_reading_occurences exp_list param count
  | Def'(variable, value) -> List.append (count_param_reading_occurrences param  (Var'(variable)) count) (count_param_reading_occurrences param value count)
  | If'(test, dit, dif) -> List.append 
                            (List.append 
                                (count_param_reading_occurrences param test (count+1)) 
                                (count_param_reading_occurrences param dit (count+1))
                            ) 
                            (count_param_reading_occurrences param dif (count+1))
  (* if param is in the lambda param_list it is in a new lexical scope, so no occurrence *)
  | LambdaSimple'(p_list, b) -> if (List.mem param p_list) 
                                  then [] 
                                  else (if ((count_param_reading_occurrences param b (count+1)) = []) then [] else [count])
  (* if param is in the lambda param_list it is in a new lexical scope, so no occurrence *)
  | LambdaOpt'(p_list, opt_p, b) -> if (List.mem param (List.append p_list [opt_p]))
                                      then [] 
                                      else (if ((count_param_reading_occurrences param b (count+1)) = []) then [] else [count])
  | _ -> []

  and map_count_reading_occurences exp_list param count = match exp_list with
    | [] -> []
    | first_exp::rest -> List.append (count_param_reading_occurrences param first_exp count) (map_count_reading_occurences rest param (count+1));;

let match_write_occurance_with_read_occurances write_occur read_occurances = 
  List.fold_left (fun matched read_occur -> (matched || (write_occur != read_occur))) false read_occurances;;

let rec boxing_criterias_are_met read_occurances write_occurances = match write_occurances with 
  | [] -> "0"
  | write_occur::rest -> if(match_write_occurance_with_read_occurances write_occur read_occurances) 
                          then "1" 
                          else (boxing_criterias_are_met read_occurances rest);;

let mark_param_for_boxing param body = 
  let reading_occurences = count_param_reading_occurrences param body 0 in
  let writing_occurences = count_param_writing_occurrences param body 0 in
  let marked_param = param::[boxing_criterias_are_met reading_occurences writing_occurences] in
  marked_param;;

let check_each_param_for_boxing params body = List.map (fun param -> mark_param_for_boxing param body) params;;

(* Return true if the givene variable is in the var list *)
let var_found_in_list variable var_list = List.mem ((variable)::["1"]) var_list;;

let rec determine_boxing exp_for_check var_list = match exp_for_check with
  | Set'(VarParam (variable,indx), value) -> if (List.mem variable var_list) 
                                            then BoxSet'(VarParam (variable,indx), (determine_boxing value var_list)) 
                                             else Set'(VarParam (variable,indx), (determine_boxing value var_list))
  | Set'(VarBound (variable,level,index), value) -> if (List.mem variable  var_list) 
                                                    then BoxSet'(VarBound (variable,level,index), (determine_boxing value var_list)) 
                                                    else Set'(VarBound (variable,level,index), (determine_boxing value var_list))
  | Var'(VarParam (variable,indx)) -> if (List.mem variable var_list)
                                      then BoxGet'(VarParam (variable,indx)) 
                                      else exp_for_check
  | Var'(VarBound (variable,level,index)) -> if (List.mem variable var_list)
                                            then BoxGet'(VarBound (variable,level,index)) 
                                            else exp_for_check
  | Var'(VarFree(variable)) -> if (List.mem variable var_list)
                              then BoxGet'(VarFree(variable)) 
                              else exp_for_check
  | LambdaSimple'(params, body) -> LambdaSimple'(params, (check_body_for_boxing body params var_list))
  | LambdaOpt'(params, opt_param, body) -> LambdaOpt'(params, opt_param, (check_body_for_boxing body (List.append params [opt_param]) var_list))
  | Applic'(expression, args) -> Applic'((determine_boxing expression var_list), (determine_boxing_list args var_list))
  | ApplicTP'(expression, args) -> ApplicTP'((determine_boxing expression var_list), (determine_boxing_list args var_list))
  | If'(test, dit, dif) -> If'((determine_boxing test var_list), (determine_boxing dit var_list), (determine_boxing dif var_list))
  | Def'(variable, value) -> Def'(variable, (determine_boxing value var_list))
  | Seq'(exp_list) -> Seq'(determine_boxing_list exp_list var_list)
  | Or'(exp_list) -> Or'(determine_boxing_list exp_list var_list)
  | _ -> exp_for_check

(* Map determine_boxing on every list element *)
and determine_boxing_list exp_list var_list = List.map (fun item -> determine_boxing item var_list) exp_list

and check_body_for_boxing body params var_list = 
  let marked_params_for_boxing = check_each_param_for_boxing params body in
  (* let merged_var_list = remove_duplicates (List.append marked_params_for_boxing var_list) in *)
  (* let merged_var_list = remove_duplicates (List.append marked_params_for_boxing var_list) in *)

  (* let boxed_body = determine_boxing body merged_var_list in *)
  let boxed_body = determine_boxing body var_list in 
  if (any_param_for_boxing marked_params_for_boxing) then (create_seq marked_params_for_boxing boxed_body) else boxed_body;;

let box_set e = determine_boxing e [];;


  let run_semantics expr =
    box_set
      (annotate_tail_calls
         (annotate_lexical_addresses expr));;
end;; (* struct Semantics *)
