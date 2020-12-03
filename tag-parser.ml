#use "reader.ml";;

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> String.equal v1 v2
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;
	
                       
exception X_syntax_error;;

module type TAG_PARSER = sig
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "pset!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)

(* ------------------------------------- *)
(* Constants 3.2.1.1 *)
(* ------------------------------------- *)
let selfEval sexpr =
  match sexpr with 
  | Bool e ->  Const(Sexpr(sexpr))
  | Char e -> Const(Sexpr(sexpr))
  | Number e -> Const(Sexpr(sexpr))
  | String e -> Const(Sexpr(sexpr))
  | Nil -> Const(Sexpr(sexpr))
  | _ -> nt_none()

let constQuote sexpr = 
   match sexpr with
  | Pair(Symbol("quote"),Pair(exp,Nil)) -> Const(Sexpr(exp))
  | _ -> nt_none() 

let tag_const sexpr = 
  disj selfEval constQuote sexpr;;


(* ------------------------------------- *)
(* Variables 3.2.1.2 *)
(* ------------------------------------- *)
let is_reserved_word w = 
  List.mem w reserved_word_list ;;

let tag_vars sexpr = 
  match sexpr with
  | Symbol(sym) -> if not (is_reserved_word sym) then Var(sym) else nt_none()
  | _ -> nt_none()


(* ------------------------------------- *)
(* Conditionals 3.2.1.3 *)
(* ------------------------------------- *)

let make_if_exp if_lst = 
  let tst_exp = List.nth if_lst 0 and
  thn_exp = List.nth if_lst 1 and
  els_exp = List.nth if_lst 2 in
  If(tst_exp,thn_exp,els_exp) ;;

(* ------------------------------------- *)
(* Lambda Expressions 3.2.1.4 *)
(* ------------------------------------- *)

let rec get_last_sexpr sexpr = 
  match sexpr with
  | Pair(car,cdr) ->
    (match cdr with
        | Nil -> car
        | _-> get_last_sexpr cdr)
  | _ -> nt_none() ;;

(* ------------------------------------- *)
(* Quasiquated Expressions 3.2.2.1 *)
(* ------------------------------------- *)

let rec make_qq_pair sexpr = 
  match sexpr with
  | Pair(Symbol("unquote"),Pair(e,Nil)) -> e                  (* 1 *)   
  | Pair(Symbol("unquote-splicing"),_) -> nt_none()           (* 2 *)
  | Symbol(s) -> Pair(Symbol("quote"),Pair(Symbol(s),Nil))    (* 3 *)
  | Nil -> Pair(Symbol("quote"),Pair(Nil,Nil))
  | Pair(a,b) ->                                              (* 5 *)
    (
      try match a with 
        | Pair(Symbol("unquote-splicing"),Pair(e,Nil)) -> Pair(Symbol("append"), Pair(e,Pair((make_qq_pair b),Nil)))
        | _ -> Pair(Symbol("cons"),Pair((make_qq_pair a),Pair((make_qq_pair b),Nil)))
      with X_no_match -> 
      try match b with 
        | Pair(Symbol("unquote-splicing"),Pair(e,Nil)) -> Pair(Symbol("cons"), Pair((make_qq_pair a),b))
        | _ -> nt_none()
      with X_no_match ->
        Pair(Symbol("cons"), Pair((make_qq_pair a),Pair((make_qq_pair b),Nil)))
    )
  | _ -> nt_none()  ;;

(* ------------------------------------- *)
(* Let Expressions 3.2.2.3 *)
(* ------------------------------------- *)
let rec open_binding sexpr vars vals =
  match sexpr with
  | Nil -> (vars,vals)
  | Pair(first,rest)-> 
    (
      match first with
      | Pair(vr,Pair(vl,Nil)) -> open_binding rest (vars@[vr]) (vals@[vl])
      | _ -> nt_none()
    )
  | _ -> nt_none();;

let rec list_to_pair ls = 
  if ls = [] then Nil else
  Pair((List.hd ls), (list_to_pair (List.tl ls)));;

let rec pair_to_list p =
  match p with
  | Pair(a,b) -> a::(pair_to_list b)
  | Nil -> []
  | _-> raise X_syntax_error;;

  let is_var expr =
  match expr with
  | Var(_) -> true
  | _ -> false

  let rec drop_seq l =
    match l with
    | [] -> []
    | Seq(s)  :: tl -> drop_seq ((List.hd s)::List.tl s)
    | hd :: tl -> hd :: drop_seq tl;;


let rec let_to_lambda sexpr =
  match sexpr with
  | Pair(defs,body)->
      let vars,vals = open_binding defs [] [] in
      let vars = list_to_pair vars and
          vals = list_to_pair vals in
      let e = Pair(Symbol("lambda"),Pair(vars,body)) in
      Pair(e,vals)
  | _ -> nt_none();;

(* ------------------------------------- *)

(* Recursive Tag Parser *)
let rec rec_tag_parser sexprs exprs =  
  match sexprs with
  | [] -> exprs
  | _ -> let exp = List.hd sexprs in
  let tags = disj_list [tag_const ; tag_vars ; tag_if ; tag_lambda ; tag_applic ; macro_quasiquate ; macro_let ; macro_let_star] in
  rec_tag_parser (List.tl sexprs) (exprs@[tags exp])

  and tag_parse  = function
    | Bool sexpr ->  Const(Sexpr(Bool(sexpr)))
    | Char sexpr -> Const(Sexpr(Char(sexpr)))
    | Number sexpr -> Const(Sexpr(Number(sexpr)))
    | String sexpr -> Const(Sexpr(String(sexpr)))
    | Nil ->  Const(Void)
    | Pair(Symbol("quote"),Pair(exp,Nil)) -> Const(Sexpr(exp))
    | Symbol(sym) -> if not (is_reserved_word sym) then Var(sym) else nt_none()
    | Pair(Symbol("if"),exp) -> tag_if exp
    | Pair(Symbol("or"),exp) -> tag_or exp
    | Pair(Symbol("define"),exp)->tag_define exp
    | Pair(Symbol("set!"),exp)->tag_set exp
    | Pair(Symbol("begin"),exp) -> tag_seq_exp exp
    | Pair(Symbol("and"), exp) -> tag_parse (macro_and exp)    



(* If *)
  and tag_if exp = 
    match exp with
      | Pair(test,Pair(dit,Pair(dif,Nil))) -> 
        If((tag_parse test), (tag_parse dit),(tag_parse dif))
      | Pair(test,Pair(dit,Nil)) -> 
        If((tag_parse test),(tag_parse dit),Const(Void))

(* Lambda *)
  and tag_lambda sexpr = 
    (* helper function *)
    let make_symbols lst = 
      List.map (fun (s) -> match s with |Var(sym) -> sym | _->nt_none()) lst
    and
    check_body body = 
      match body with
      | Pair (bdy,Nil) -> bdy
      | _ ->  get_last_sexpr body
    in
    (* the main function *)
    match sexpr with
    | Pair(Symbol("lambda"),Pair(arglist,body)) -> 
        let body = check_body body in
        let a,b = make_expr_list arglist [] in
        if b = [] then
          LambdaSimple((make_symbols a),(List.hd (rec_tag_parser [body] [])))
        else 
          LambdaOpt((make_symbols a) , (List.hd (make_symbols b)), (List.hd (rec_tag_parser [body] [])))
    | _ -> nt_none() 

(* Applic *)
  and tag_applic sexpr = 
    let get_sexper_list args = 
      let lst,_ = make_expr_list args [] in
      lst 
    in
    match sexpr with
    | Pair(app,args) -> Applic((List.hd (rec_tag_parser [app] [])) , (get_sexper_list args ))
    | _ -> nt_none()

  (* Pair of sexpr -> (exprs list , [last one if dotted])*)  
  and make_expr_list nest_pair lst= 
    let get_exp sexpr = 
      match sexpr with
      | Pair(e,res) -> ((List.hd (rec_tag_parser [e] [])),res)
      | _ ->  nt_none()
    in
    if nest_pair = Nil then (lst,[]) else
    try let v,res = get_exp nest_pair in
      if res = Nil then (lst@[v],[]) else make_expr_list res (lst@[v]) 
    with X_no_match -> (lst,(rec_tag_parser [nest_pair] []))

  (* Quasiquote *)
  and macro_quasiquate sexpr = 
    match sexpr with
    | Pair(Symbol("quasiquote"),Pair(e,Nil)) ->
          let mac = make_qq_pair e in
          (List. hd (rec_tag_parser [mac] []))
    | _ -> nt_none()
  
   (*Disjunctions - which is or-expresion*)
  and tag_or exp =
  match exp with 
  |Pair(sexpr, Nil) -> tag_parse sexpr
  |Pair(sexpr,rest) -> Or((List.map tag_parse (pair_to_list exp)))
  | Nil -> Const(Sexpr(Bool(false)))
  | _-> raise X_syntax_error

  (*Definitions*)
  and tag_define exp= 
    match exp with 
      |Pair(Symbol(str),Nil) ->if not (is_reserved_word str) then Def(Var(str),Const(Void))  else nt_none() (*just declaration*)
      |Pair(Symbol(str),Pair(sexpr,Nil)) ->if not (is_reserved_word str) then  Def(Var(str), (tag_parse sexpr))  else nt_none() 
      | _-> raise X_syntax_error

    
  (*Assignments - set!*)
  and tag_set exp=
      match exp with
      |Pair(x,Pair(y,Nil)) -> 
      let v=tag_parse x in
        if (is_var v) then Set(v,(tag_parse y))  else nt_none()  
      |_ -> raise X_syntax_error
  
  (* Sequences - explicisy*)
  and tag_seq_exp exp= 
  match exp with
    | Nil -> Const(Void) (*An empty sequence should be tag-parsed to Const Void*)
    | Pair(sexpr,Nil)-> tag_parse sexpr
    | Pair(sexpr,rest)-> Seq(drop_seq (List.map tag_parse (pair_to_list exp))) 
  


  (* Let *)
  and macro_let sexpr = 
  match sexpr with
  | Pair(Symbol("let"),e)->
  let app = let_to_lambda e in
          (List. hd (rec_tag_parser [app] []))
  | _ -> nt_none()

  (* Let* *)
  and macro_let_star sexpr = 
    let get_car_cdr p = 
      match p with
      | Pair(car,cdr)->(Pair(car,Nil),cdr) 
      | _ -> nt_none()
    in
    match sexpr with
    | Pair(Symbol("let*"),e)->
      (
        match e with
        | Pair (args,body)->
          (match args with
            (* base case 1 *)
            | Nil -> (List. hd (rec_tag_parser [Pair(Symbol("let"),e)] []))
            (* base case 2 *)   
            | Pair (Pair (v, Pair (a, Nil)),Nil) -> (List. hd (rec_tag_parser [Pair(Symbol("let"),e)] []))
            (* case 3 *) 
            | _ -> let v1,els = get_car_cdr args in
            let els = Pair(Pair(Symbol("let*"),Pair(els,body)),Nil) in
            let exp = Pair(Symbol("let"),Pair(v1,els))in
            (List. hd (rec_tag_parser [exp] []))
          )
        | _ -> nt_none()
      )
    | _ -> nt_none()

  and macro_and exp = match exp with
    | Nil -> Bool(true)
    | Pair(sexpr, Nil) -> sexpr
    | Pair(sexpr, rest) -> Pair(Symbol("if"), Pair(sexpr, Pair( (macro_and rest), Pair( Bool(false), Nil ))))
    | _ -> raise X_syntax_error

let tag_parse_expressions sexpr =(List.map tag_parse sexpr);;

  
end;; (* struct Tag_Parser *)