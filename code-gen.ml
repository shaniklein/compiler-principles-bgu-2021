#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (constant * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)  
  val make_fvars_tbl : expr' list -> (string * int) list

  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second 
     argument is the fvars table type, and the third is an expr' that has been annotated 
     by the semantic analyser.
   *)
  val generate : (constant * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct
  
  (* First scan of the ast to extract all constants 2.2.1 of RS11 *)
  (* Return consant list with duplicates *)
  let rec scan_ast lst tbl = 
    match lst with
    | [] -> tbl
    | car::cdr ->
      (
        match car with 
        | Const'(e) -> scan_ast cdr (tbl@[e])
        | If'(tst,dit,dif) -> 
            let tst_tbl = scan_ast [tst] [] in 
            let dit_tbl = scan_ast [dit] [] in 
            let dif_tbl = scan_ast [dif] [] in
            scan_ast cdr (tbl@tst_tbl@dit_tbl@dif_tbl)
        | Seq'(seq) -> 
            let seq_tbl = scan_ast seq [] in
            scan_ast cdr (tbl@seq_tbl)
        | Set'(a,b) -> 
            let b_tbl = scan_ast [b] [] in
            scan_ast cdr (tbl@b_tbl)
        | Def'(a,b) -> 
            let b_tbl = scan_ast [b] [] in
            scan_ast cdr (tbl@b_tbl)
        | Or'(l) -> 
            let or_tbl = scan_ast l [] in
            scan_ast cdr (tbl@or_tbl)
        | LambdaSimple'(v,body) -> 
            let body_tbl = scan_ast [body] [] in
            scan_ast cdr (tbl@body_tbl)
        | LambdaOpt'(v,vop,body) -> 
            let body_tbl = scan_ast [body] [] in
            scan_ast cdr (tbl@body_tbl)
        | Applic'(op,vals) -> 
            let op_tbl = scan_ast [op] [] in
            let vals_tbl = scan_ast vals [] in
            scan_ast cdr (tbl@op_tbl@vals_tbl)
        | ApplicTP'(op,vals) -> 
            let op_tbl = scan_ast [op] [] in
            let vals_tbl = scan_ast vals [] in
            scan_ast cdr (tbl@op_tbl@vals_tbl)
        | _-> scan_ast cdr tbl
      );;


  (* Extending to sub-constants 2.2.2 RS11*)
  let rec extend_tbl lst tbl = 
    match lst with
    | [] -> tbl
    | car::cdr ->
      (
        match car with 
        | Sexpr(Symbol(s)) -> extend_tbl cdr (tbl@[Sexpr(String(s))]@[car])
        | Sexpr(Pair(car1,cdr1)) -> 
            let ext_car = extend_tbl [Sexpr(car1)] [] in
            let ext_cdr = extend_tbl [Sexpr(cdr1)] [] in
            extend_tbl cdr (tbl@ext_car@ext_cdr@[car])
        | Void -> extend_tbl cdr tbl
        | Sexpr(Nil) -> extend_tbl cdr tbl
        | Sexpr(Bool(_)) -> extend_tbl cdr tbl
        | _ -> extend_tbl cdr (tbl@[car])
      );;
  
  (* Reduce duplicates 2.2.2_b RS11*)  
  let rec reduce_dups lst tbl = 
    let is_duplicate e tbl = 
      List.fold_left
        (fun a b-> if (expr_eq (Const(e)) (Const(b))) then true else a)
        false
        tbl
    in
    match lst with
    | [] -> tbl
    | car::cdr ->
      (
        if not (is_duplicate car tbl)
          then reduce_dups cdr (tbl@[car])
          else reduce_dups cdr tbl
      );;

  (* return the size on the const record *)
  let calc_size c = 
    match c with 
    | Void -> 1 (* Void *)
    | Sexpr(Nil) -> 1 (* Nil *)
    | Sexpr(Bool(_)) -> 2 (* Boolean *)
    | Sexpr(Number(Fraction(_,_))) -> 17 (* Rational *)
    | Sexpr(Number(Float(_))) -> 9 (* Float *)
    | Sexpr(String(s)) -> 9 + (String.length s) (* String *)
    | Sexpr(Symbol(_)) -> 9 (* Symbol *)
    | Sexpr(Pair(_,_)) -> 17 (* Pair *)
    | _ -> 0;;

  (* returns the offset of c from the top *)
  let rec get_const_address c tbl=
    match tbl with
    | [] -> -1
    | car::cdr ->
      let (e,(add,_)) = car in
      if (expr_eq (Const(c)) (Const(e))) then add
        else get_const_address c cdr  ;;



  (* Create Assembly strings *)
  let make_string_lit_rat a b = 
    let sa = string_of_int a in
    let sb = string_of_int b in
    "MAKE_LITERAL_RATIONAL("^sa^","^sb^")";;

  let make_string_lit_float a = 
    let sa = string_of_float a in
    "MAKE_LITERAL_FLOAT("^sa^")";;

  let make_string_lit_string s = 
    "MAKE_LITERAL_STRING("^"\""^s^"\""^")";;

  let make_string_lit_symbol n = 
    let sn = string_of_int n in
    "MAKE_LITERAL_SYMBOL(const_tbl+"^sn^")";;

  let make_string_lit_pair a b = 
    let sa = string_of_int a in
    let sb = string_of_int b in
    "MAKE_LITERAL_FLOAT(const_tbl+"^sa^", "^"const_tbl+"^sb^")";;

  
  (* Add address and assembly string to each instance in the table *)
  let rec populate lst tbl ptr = 
    match lst with
    | [] -> tbl
    | car::cdr ->
      let asm_str = 
        match car with
        | Void -> "db T_VOID"
        | Sexpr(Nil) -> "db T_NIL"
        | Sexpr(Bool(false)) -> "db T_BOOL, 0"
        | Sexpr(Bool(true)) -> "db T_BOOL, 1"
        | Sexpr(Number(Fraction(a,b))) -> make_string_lit_rat a b
        | Sexpr(Number(Float(n))) -> make_string_lit_float n
        | Sexpr(String(s)) -> make_string_lit_string s
        | Sexpr(Symbol(c)) -> 
            let addr = get_const_address (Sexpr(String(c))) tbl in
            make_string_lit_symbol addr
        | Sexpr(Pair(a,b)) -> 
            let car_addr = get_const_address (Sexpr(a)) tbl in
            let cdr_addr = get_const_address (Sexpr(b)) tbl in
            make_string_lit_pair car_addr cdr_addr
        | _ -> ""
      in
      let record = (car,(ptr,asm_str)) in
        populate cdr (tbl@[record]) (ptr+(calc_size car));;

  (* Make Constant Table *)
  let make_consts_tbl asts =
    let tbl_hdr = [ Void;
                    Sexpr(Nil);
                    Sexpr(Bool(false));
                    Sexpr(Bool(true))]
    in
    let tbl = scan_ast asts [] in
    let tbl = extend_tbl tbl [] in
    let tbl = reduce_dups tbl [] in
    let tbl = populate (tbl_hdr@tbl) []  0 in
    tbl;;


    let make_fvars_tbl asts = raise X_not_yet_implemented;;
    let generate consts fvars e = raise X_not_yet_implemented;;
  

end;;

