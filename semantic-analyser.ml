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
  (*given number num return list of [1,2,3,....,num]*)
  let rec list_all_nums_befor num = 
    match num with
    | 0 -> []
    | _ -> (list_all_nums_befor (num-1))@[(num-1)] 

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
  (* Q3.4 *)
(* ---------------------- *)
(* return true if we need to do boxing to parameter "param"*)
let  rec need_boxing param body =
  let reading_occurences = count_param_reading_occurrences param body 0 in
  let writing_occurences = count_param_writing_occurrences param body 0 in
  let matched=boxing_criterias_are_met  reading_occurences writing_occurences in
  matched && (has_read_occ param body) && (has_write_occ param body)

  and has_read_occ param body =
  match body with
  (*we have read occ of param if we have Var'(param) *)
  | Var' (VarBound(name, level, index))-> if(name = param) then true else false
  | Var' (VarParam (name, index)) -> if(name = param) then true else false
  
  | Set' (VarBound(name, level, index), expr) -> if(name = param) then true else false
  | Set' (VarParam (name, index), expr) ->if(name = param) then true else false

  | Def' (variable, value) -> has_read_occ param (Var'(variable)) || has_read_occ param value
  | If' (test, dit, dif) -> has_read_occ param test || has_read_occ param dit || has_read_occ param dif
  | Seq' expr_list -> ormap (has_read_occ param) expr_list
  | Set' (var, expr) -> has_read_occ param (Var'(var)) || has_read_occ param expr
  | BoxSet' (_, expr) -> has_read_occ param expr
  | Or' lst -> ormap (has_read_occ param) lst
  | Applic' (op, args) -> has_read_occ param op || ormap (fun e -> has_read_occ param e) args
  | ApplicTP' (op, args) -> has_read_occ param op || ormap (fun e -> has_read_occ param e) args

  | LambdaSimple' (params, body) -> if (List.exists (fun e -> e = param) params)
                                    then false
                                    else has_read_occ param body
  | LambdaOpt' (params, opt, body) -> if (List.exists (fun e -> e = param) (opt::params))
                                      then false
                                      else has_read_occ param body
  | _ -> false 

  and map_count_reading_occurences exp_list param count = match exp_list with
  | [] -> []
  | first_exp::rest -> List.append (count_param_reading_occurrences param first_exp count) (map_count_reading_occurences rest param (count+1))

  and map_count_writing_occurences exp_list param count = match exp_list with
  | [] -> []
  | first_exp::rest -> List.append (count_param_writing_occurrences param first_exp count) (map_count_writing_occurences rest param (count+1))

  and match_write_occurance_with_read_occurances write_occur read_occurances = 
    List.fold_left (fun matched read_occur -> (matched || (write_occur != read_occur))) false read_occurances
  
  and boxing_criterias_are_met read_occurances write_occurances = match write_occurances with 
    | [] -> false
    | write_occur::rest -> if(match_write_occurance_with_read_occurances write_occur read_occurances) 
                            then true
                            else (boxing_criterias_are_met read_occurances rest)

and has_write_occ param body =
  match body with
  | Set' (VarBound (par, index, _), expr) -> par = param || has_write_occ param expr
  | Set' (VarParam (par, index), expr) -> par = param || has_write_occ param expr
  | Set' (VarFree(var), expr) -> has_write_occ param (Var'(VarFree(var))) || has_write_occ param expr

  | If' (test, dit, dif) -> has_write_occ param test || has_write_occ param dit || has_write_occ param dif
  | Def' (e1, e2) -> has_write_occ param (Var'(e1)) || has_write_occ param e2
  | Seq' lst -> ormap (has_write_occ param) lst
  | BoxSet' (var, expr) -> has_write_occ param expr
  | Or' lst -> ormap (has_write_occ param) lst
  | Applic' (op, args) | ApplicTP' (op, args) -> has_write_occ param op || ormap (fun e -> has_write_occ param e) args
  | LambdaSimple' (params, body) ->if (List.exists (fun e -> e = param) params)
                                  then false
                                  else has_write_occ param body
  | LambdaOpt' (params, opt, body) -> if (List.exists (fun e -> e = param) (opt::params))
                                then false
                                else has_write_occ param body
|  _ -> false

and count_param_writing_occurrences param body count = match body with
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
| LambdaOpt'(p_list, opt_p, b) -> if (List.mem param (List.append p_list [opt_p]))
                                    then [] 
                                    else (if ((count_param_writing_occurrences param b (count+1)) = []) then [] else [count])
| _ -> []

and count_param_reading_occurrences param body count = match body with
| Const'(value) -> []
| Var'(VarParam (variable,indx)) -> if ( variable = param) then [-1] else []
| Var'(VarBound (variable,level,index)) -> if ( variable = param) then [-1] else []
| Var'(VarFree (variable)) -> if ( variable = param) then [-1] else []
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
| LambdaOpt'(p_list, opt_p, b) -> if (List.mem param (List.append p_list [opt_p]))
                                    then [] 
                                    else (if ((count_param_reading_occurrences param b (count+1)) = []) then [] else [count])
| _ -> []

(* Replace any set-occurances of v with BoxGet' *)
let rec replace_set_occ param body =
  match body with
  | Const' _ | Var' _ | BoxGet' _ | Box' _ -> body
  | BoxSet' (var, expr) -> BoxSet' (var, replace_set_occ param expr)
  | If' (pred, dit, dif) -> If' (replace_set_occ param pred, replace_set_occ param dit, replace_set_occ param dif)
        | Seq' lst -> Seq' (List.map (replace_set_occ param) lst)

  | Def' (VarBound (par, n1, n2), e2) -> 
  let test= replace_set_occ param (Var'(VarBound (par, n1, n2))) in
  (match test with
  | Var'(VarBound (e, n1, n2))-> Def' (VarBound (e, n1, n2), replace_set_occ param e2)
  | _ -> raise X_this_should_not_happen )

  | Def' (VarParam (par, n1), e2) -> 
  let test= replace_set_occ param (Var'(VarParam (par, n1))) in
  (match test with
  | Var'(VarParam (e, n1))-> Def' (VarParam (e, n1), replace_set_occ param e2)
  | _ -> raise X_this_should_not_happen )
  
  | Set' ((VarBound (p, n1, n2)), expr) ->
    if (p = param)
    then BoxSet' (VarBound (param, n1, n2), replace_set_occ param expr)
    else Set' (VarBound (p, n1, n2), replace_set_occ param expr)
  | Set' (VarParam (p, n1), expr) ->
  if (p = param)
  then BoxSet' (VarParam (param, n1), replace_set_occ param expr)
  else Set' (VarParam (p, n1), replace_set_occ param expr)
  | Set' (VarFree var, expr) -> Set' (VarFree var, replace_set_occ param expr)
  | Or' lst -> Or' (List.map (replace_set_occ param) lst)
  | Applic'	(op, args) -> Applic'	(replace_set_occ param op, List.map (replace_set_occ param) args)
  | ApplicTP' (op, args) -> ApplicTP' (replace_set_occ param op, List.map (replace_set_occ param) args)
  | LambdaSimple' (params, body) ->
    if (List.exists (fun e -> e = param) params)
    then LambdaSimple' (params, body)
    else LambdaSimple' (params, replace_set_occ param body)
        | LambdaOpt' (params, opt, body) ->
    if (List.exists (fun e -> e = param) (opt::params))
    then LambdaOpt' (params, opt, body)
    else LambdaOpt' (params, opt, replace_set_occ param body)
        | _ -> raise X_this_should_not_happen  

(* Replace any get-occurances of v with BoxGet' *)
let rec replace_get_occ param body =
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
  | BoxSet' (var, expr) -> BoxSet' (var, replace_get_occ param expr)
  | If' (pred, dit, dif) -> If' (replace_get_occ param pred, replace_get_occ param dit, replace_get_occ param dif)
  
  | Def' (VarBound (par, n1, n2), e2) ->
    let test= replace_get_occ param (Var'(VarBound (par, n1, n2))) in
    (match test with
    | Var'(VarBound (e, n1, n2))-> Def' (VarBound (e, n1, n2), replace_get_occ param e2)
    | _ -> raise X_this_should_not_happen )
  
  | Def' (VarParam (par, n1), e2) ->
  let test= replace_get_occ param (Var'(VarParam (par, n1))) in
    (match test with
    | Var'(VarParam (e, n1))-> Def' (VarParam (e, n1), replace_get_occ param e2)
    | _ -> raise X_this_should_not_happen )

  | Seq' lst -> Seq' (List.map (fun e -> replace_get_occ param e) lst)
  | Set' (VarBound (par, n1, n2), expr) ->
      if (par = param)
      then Set' (VarBound (param, n1, n2), replace_get_occ param expr) 
      else 
      let temp= replace_get_occ param (Var' (VarBound (par, n1, n2))) in
      ( match temp with
      | Var'(VarBound (par, n1, n2))->Set' (VarBound (par, n1, n2), replace_get_occ param expr) 
      |_ -> raise X_this_should_not_happen 
      )
  | Set' (VarParam (par, n1), expr) ->
      if (par = param)
      then Set' (VarParam (param, n1), replace_get_occ param expr) 
      else 
      let temp= replace_get_occ param (Var' (VarParam (par, n1))) in
    ( match temp with
      | Var'(VarParam (par, n1))->Set' (VarParam (par, n1), replace_get_occ param expr) 
      |_ -> raise X_this_should_not_happen 
    )
  | Set' (VarFree (var), expr) -> Set' (VarFree (var), replace_get_occ param expr)
  | Or' lst -> Or' (List.map (fun e -> replace_get_occ param e) lst)
  | Applic' (op, args) ->		Applic'   (replace_get_occ param op, List.map (fun e -> replace_get_occ param e) args)
  | ApplicTP' (op, args) ->	ApplicTP' (replace_get_occ param op, List.map (fun e -> replace_get_occ param e) args)
  | LambdaSimple' (params, body) ->
  if (List.exists (fun e -> e = param) params)
  then LambdaSimple' (params, body)
  else LambdaSimple' (params, replace_get_occ param body)
      | LambdaOpt' (params, opt, body) ->
  if (List.exists (fun e -> e = param) (opt::params))
  then LambdaOpt' (params, opt, body)
  else LambdaOpt' (params, opt, replace_get_occ param body)
      | _ -> raise X_this_should_not_happen

  let box_param param min body =
    let body = replace_get_occ param body in
    let body = replace_set_occ param body in
    match body with
    | Seq' list -> Seq' ([Set' (VarParam (param, min), Box' (VarParam (param, min)))]@list)
    | _ -> Seq' [Set' (VarParam (param, min), Box' (VarParam (param, min))); body] ;;


let foldfunc (param, minor) body =
    if (need_boxing param body)
    then (box_param param minor body)
    else body;;

let apply_box_on_lambda params body =
  (* comine paran with it's index *)
  let params = List.combine params (list_all_nums_befor (List.length params)) in
  List.fold_right foldfunc params body;;

let rec check_for_lambdas exp =
  match exp with
  | BoxSet' (var, expr) -> BoxSet' (var, check_for_lambdas expr)

  | Def' (VarBound(name, level, index), e2) ->Def' (VarBound(name, level, index), check_for_lambdas  e2)  
  | Def' (VarParam(name, index), e2) -> Def' (VarParam(name, index), check_for_lambdas  e2)
  | Def' (VarFree (var), e2) -> Def' (VarFree (var), check_for_lambdas  e2)
  
  | If' (pred, dit, dif) -> If' (check_for_lambdas pred, check_for_lambdas dit, check_for_lambdas dif)
  | Seq' lst -> Seq' (List.map check_for_lambdas lst)
  
  | Set'(VarParam (variable,indx), e2) ->  Set' (VarParam (variable,indx), check_for_lambdas  e2)
  | Set'(VarBound (par, n1, n2), e2)->Set' (VarBound (par, n1, n2), check_for_lambdas  e2)
  | Set'(VarFree (par), e2)-> Set' (VarFree (par), check_for_lambdas  e2)

  | Or' lst -> Or' (List.map check_for_lambdas lst)
  | Applic' (op, args) -> Applic' (check_for_lambdas op, List.map check_for_lambdas args)
  | ApplicTP' (op, args) -> ApplicTP' (check_for_lambdas op, List.map check_for_lambdas args)
  
  | LambdaSimple' (params, body) -> LambdaSimple' (params, check_for_lambdas (apply_box_on_lambda params body))
  | LambdaOpt' (params, opt, body) -> LambdaOpt' (params, opt, check_for_lambdas (apply_box_on_lambda (opt::params) body))
  |_-> exp
  ;;
    
let box_set e = check_for_lambdas e;;

 let run_semantics expr =
    box_set
    (annotate_tail_calls
    (annotate_lexical_addresses expr));;
  end;; (* struct Semantics *)
    