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
    "MAKE_LITERAL_PAIR(const_tbl+"^sa^", "^"const_tbl+"^sb^")";;

  
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
  
  (* This function recives an expr', extracting free varibale and returns it's name as a string *)
  let rec find_str_in_fvar ex' = match ex' with
  | Var'(VarFree(str)) -> [str]
  | Applic'(expr',ls) -> (find_str_in_fvar expr') @ (List.fold_left (fun a b -> a @ b) [] (List.map find_str_in_fvar ls))
  | ApplicTP'(expr',ls) -> (find_str_in_fvar expr') @ (List.fold_left (fun a b -> a @ b) [] (List.map find_str_in_fvar ls))
  | Def'(expr'1,expr'2) -> (find_str_in_fvar (Var'(expr'1))) @ (find_str_in_fvar expr'2)
  | Or'(ls) -> (List.fold_left (fun a b -> a @ b) [] (List.map find_str_in_fvar ls))
  | LambdaSimple'(param,body) -> (find_str_in_fvar body)
  | BoxSet'(var, expr') -> (find_str_in_fvar expr')
  | If'(test, dit, dif) -> (find_str_in_fvar test) @ (find_str_in_fvar dit) @ (find_str_in_fvar dif)
  | Seq'(ls) -> (List.fold_left (fun a b -> a @ b) [] (List.map find_str_in_fvar ls))
  | Set'(expr'1,expr'2) -> (find_str_in_fvar (Var'(expr'1))) @ (find_str_in_fvar expr'2)
  | LambdaOpt'(param,lastp,body) -> (find_str_in_fvar body)
  | _ -> [];;
      
  let init_fvars_table = 
      [
        "boolean?"; "flonum?";"float?";"rational?"; "pair?";"null?"; "char?"; "string?";
        "procedure?"; "symbol?"; "string-length";
        "string-ref"; "string-set!"; "make-string";
        "symbol->string"; "char->integer"; "integer->char"; "eq?";
        "+"; "*"; "-"; "/"; "<"; "="; 
        "car"; "cdr"; "cons"; "set-car!"; "set-cdr!";"apply" ;
        "numerator";"denominator";"gcd";
        "char->integer";"integer->char";"exact->inexact";
      ] ;;
    
    (*  add_index_to_list on ["a","b","c"] will return [("a",0),("b",1),("c",2)]*)
    let rec add_index_to_list l index = match l with
    | [] -> []
    | head :: tl -> [(head, index)] @ (add_index_to_list tl (index+1));;
    
    let make_index_fvar_table l = (add_index_to_list l 0);;
  

  (* There's no need of duplicates in the free variables table, the following lines deals with removing the duplicates from the table*)
  let rec remove_dup_rec  l new_l = match l with
  | [] -> new_l
  | head :: tail -> if(List.mem head new_l) then (remove_dup_rec  tail new_l) else (remove_dup_rec  tail (new_l @ [head]));;
  let remove_dup_from_llist l = remove_dup_rec l [];;
  
  let  make_fvars_tbl asts = make_index_fvar_table (remove_dup_from_llist (init_fvars_table @ List.flatten (List.map find_str_in_fvar asts)));;
  
  (* Counter for unique labels *)
  (* Code taken from https://www.cs.cornell.edu/courses/cs3110/2020fa/textbook/mut/ex_counter.html *)
  let lambda_counter =ref 0 ;;
  let next_lambd = 
    fun() ->
      lambda_counter:=(!lambda_counter) +1;
      !lambda_counter;;
  let counter = ref 0;;
  let next_val = 
    fun () ->
      counter := (!counter) + 1;
      !counter;;

let rec generate_rec consts fvars env e = match e with
  | Const'(c) ->
      let addr = get_const_address c consts in
      Printf.sprintf "mov rax, const_tbl+%d" addr
  | Var'(VarParam(_, minor))-> Printf.sprintf ("mov rax, qword [rbp + 8 * (4 + %d)]") minor
  | Set'(VarParam(_, minor),exp)->  String.concat "\n" ["; Set VarParam Start" ;
                (generate_rec consts fvars  env exp);
                Printf.sprintf ("mov qword [rbp + 8 * (4 + %d)], rax") minor;
                "mov rax, SOB_VOID_ADDRESS" ;
                "; Set VarParam End\n"]
  | Var'(VarBound(_, major, minor)) -> String.concat "\n" ["; VarBound Start" ;
                                    "mov rax, qword [rbp + 8 * 2]" ;
                                      Printf.sprintf ("mov rax, qword [rax + 8 * %d]") major ;
                                      Printf.sprintf ("mov rax, qword [rax + 8 * %d]") minor ;
                                      "; VarBound End\n"]
  | Set'(VarBound(_, major, minor), exp) -> String.concat "\n" ["; Set VarBound Start";
                                                  (generate_rec consts fvars  env exp) ;
                                                  "mov rbx, qword [rbp + 8 * 2]" ;
                                                    Printf.sprintf ("mov rbx, qword [rbx + 8 * %d]") major ;
                                                    Printf.sprintf ("mov qword [rbx + 8 * %d], rax") minor ;
                                                  "mov rax, SOB_VOID_ADDRESS" ;
                                                  "; Set VarBound End\n"]  
  | Var'(VarFree(variable)) ->  Printf.sprintf ("mov rax, qword [fvar_tbl + WORD_SIZE * (%d)] ; VarFree") (labelInFVarTable variable fvars)  
  | Set'(VarFree(variable), exp) -> String.concat "\n" [ Printf.sprintf "; Set VarFree - %s - Start" variable;                                                                
                                    (generate_rec consts fvars  env exp) ;
                                      Printf.sprintf ("mov qword [fvar_tbl + WORD_SIZE * (%d)], rax") (labelInFVarTable variable fvars) ; 
                                    "mov rax, SOB_VOID_ADDRESS" ;
                                    "; Set VarFree End\n"]
  | Def'(VarFree(variable), exp) -> String.concat "\n" ["; Define Start" ;
                                          (generate_rec consts fvars  env exp); 
                                            Printf.sprintf ("mov [fvar_tbl + WORD_SIZE * (%d)], rax") (labelInFVarTable variable fvars);
                                          "mov rax, SOB_VOID_ADDRESS" ;
                                          "; Define End\n" ;]
  | Seq'(seq) -> String.concat "\n" (List.map (generate_rec consts fvars env) seq)
  | BoxGet'(v) -> String.concat "\n" ["; BoxGet Start"; 
  (generate_rec consts fvars env (Var'(v)) );
  "mov rax, qword [rax]"; "; BoxGet End\n"]
  | BoxSet'(variable, value) -> String.concat "\n" ["; BoxSet Start" ;
  (generate_rec consts fvars env value) ;
  "push rax" ; 
  (generate_rec consts fvars env (Var'(variable)) ) ; 
  "pop qword [rax]" ; 
  "mov rax, SOB_VOID_ADDRESS" ;
  "; BoxSet End\n" ;]

  (* If *)
  | If'(tst,dit,dif) -> let lbl_num = next_val() in
  String.concat "\n" [ "; If Start";
          (generate_rec consts fvars env tst );
          "cmp rax, SOB_FALSE_ADDRESS";
          "je Lelse"^(string_of_int lbl_num);
          (generate_rec consts fvars env dit );
          "jmp Lexit"^(string_of_int lbl_num);
          "Lelse"^(string_of_int lbl_num)^":";
          (generate_rec consts fvars  env dif );
          "Lexit"^(string_of_int lbl_num)^":" ;
          "; If End\n"]
  (* Or *)
  | Or'(lst) -> let gen_lst = List.map (generate_rec consts fvars env) lst in
  let lbl_num = next_val() in
  let asm_code = "\n"^"cmp rax, SOB_FALSE_ADDRESS"^"\n"^"jne Lexit"^(string_of_int lbl_num)^"\n" in
  (String.concat asm_code gen_lst)^"\n"^"Lexit"^(string_of_int lbl_num)^":"
  | LambdaSimple'(params, body) -> let env_num = next_lambd() in
  String.concat "\n" [ lambda_code env_num env "LambdaSimple";
                    (generate_rec consts fvars (env + 1) body);
                    "leave";
                    "ret";
                    Printf.sprintf ("Lcont_LambdaSimple%d:") env_num;
                    ";Lambda simple end"
                    ] 
  | Applic'(proc,args)-> String.concat "\n" ["; Applic' Start"; 
                                                  "push SOB_NIL_ADDRESS ;push magic";
                                                  (* push args - first reverse then push *)
                                                  List.fold_left (fun curr acc -> acc ^ curr) "" 
                                                  (List.map (fun arg -> (generate_rec consts fvars env arg) ^ " \n push rax \n") args);
                                                  (* push number of arguments *)
                                                  Printf.sprintf "push %i\n" (List.length args) ;
                                                  generate_rec consts fvars env proc;
                                                  "CLOSURE_ENV r8,rax" ;                                                     
                                                  "push r8" ; (* env *)
                                                  "CLOSURE_CODE r8, rax" ;
                                                  "call r8" ; (* code *)
                                                  (* this part is directly from lecture *)
                                                  (* pop eviroment *)
                                                  "add rsp , 8*1 ;pop env";
                                                  "pop rbx ; pop arg count";

                                                  "shl rbx , 3  ; rbx=rbx*8"; 
                                                  (* pop args *)
                                                  "add rsp , rbx ; pop args";
                                                  "add rsp, 8 ;pop magic"] 

| ApplicTP'(expression, args) -> String.concat "\n" ["; ApplicTP Start" ;
                                                    "push 7 ; magic number" ;
                                                    (push_applic_args consts fvars args env);
                                                    "; ApplicTP Code Start" ;
                                                    (generate_rec consts fvars env expression) ;
                                                    "; ApplicTP Code End - Continue ApplicTP" ;
                                                    "CLOSURE_ENV rsi,rax" ;                                                     
                                                    "push rsi" ; (* env *)
                                                    "mov rsi,qword [rbp + 8]" ;
                                                    "push rsi" ;
                                                      Printf.sprintf "mov rsi, %d" (4+(List.length args)) ;
                                                    "mov r13, qword [rbp]" ;
                                                    "F_R_S rsi" ;
                                                    "mov rbp, r13" ;
                                                    "CLOSURE_CODE rsi, rax" ;
                                                    "jmp rsi" ; (* code *)
                                                    "; ApplicTP End\n"]


(* NOT WORKING YET *)
| LambdaOpt'(params, opt, body) ->let env_num = next_lambd() in 
                              let expected_params_length = (List.length params) in

                              String.concat "\n" [
                                lambda_code env_num env "LambdaOpt";
                              "mov rcx, qword [rbp + 3*8] ; move number of actual params to rcx";
                              Printf.sprintf("mov rbx, %d")  expected_params_length ;
                                (* check if we got the same number of arguments as we expected *)
                              "cmp rcx, rbx ;rbx contains expected number of param and rcx the actual number of params"; 
                              (* if we got same aguments as we espected jump *)
                              Printf.sprintf("je equal_adjast%d ;if we got same aguments as we espected jump ") env_num;
                              Printf.sprintf("mov rdx, %d")  expected_params_length;
                              "add rdx, 4 ; rdx = expected_params+4" ; 
                              "shl rdx, 3";
                              "add rdx, rbp";
                              Printf.sprintf("sub rcx, %d") expected_params_length ;
                              "mov rdi, const_tbl+1";
                              (* copy params *)
                              Printf.sprintf("move_opt_params%d:") env_num;
                              "dec rcx";
                              "mov rbx, rcx";
                              "shl rbx, 3";
                              "mov rsi, rbx";
                              "add rsi, rdx";
                              "mov rsi, qword [rsi]";
                              "MAKE_PAIR(rax, rsi, rdi)";
                              "mov rdi, rax";
                              "inc rcx";
                              (* extend the enviroment *)
                              Printf.sprintf("loop move_opt_params%d, rcx")  env_num;
                              "mov [rdx], rdi";
                                                                                
                              "mov rax, qword [rbp + 3*8]";
                              "dec rax";
                              "add rax, 4";
                              "shl rax, 3";
                              "add rax, rbp";
                              Printf.sprintf("mov rbx,%d") expected_params_length;
                              "add rbx, 4";
                              "shl rbx, 3";
                              "add rbx, rbp";
                              Printf.sprintf("mov rcx, %d") expected_params_length;
                              "add rcx, 5";

                              adjust_stack env_num expected_params_length;
                              Printf.sprintf("cont_to_body%d:") env_num ;
                              (generate_rec consts fvars  (env + 1) body ) ;
                              "leave";
                              "ret"; 
                              Printf.sprintf("Lcont_LambdaOpt%d:") env_num]
 | _ -> "mov rax , SOB_VOID_ADDRESS\n" 
 and labelInFVarTable var fvars=
 let row = List.find (fun (name, _) -> (compare var name == 0)) fvars in
 match row with  | (_,index) -> index

 and lambda_code env_num env label= String.concat "\n" [Printf.sprintf(";%s start") label;
                                      Printf.sprintf ("%s%d:") label env_num ;
                                      Printf.sprintf ("extend%s%d:") label env_num;
                                    (* rbx <- old_env*) 
                                      "mov rbx, qword [rbp + 8 * 2]";
                                      Printf.sprintf ("MALLOC rax, %d") ((env + 1) * 8);
                                      (* initiailize loop counter with rcx *)
                                      Printf.sprintf ("mov rcx, %d" ) (env);
                                      "cmp rcx, 0";
                                      Printf.sprintf ("je alloc_clousre_%s%d") label env_num ;
                                      (* copy old enviroment's pointer to new one *)
                                      Printf.sprintf ("loop_env_%s%d:") label env_num ;
                                      "dec rcx";
                                      "mov rdx, qword[rbx + 8*rcx]";
                                      "inc rcx";
                                      (* old_env[i] -> new_env[i+1] *)
                                      "mov [rax + 8 * rcx], rdx ";
                                      Printf.sprintf ("loop loop_env_%s%d, rcx") label env_num;
                                      Printf.sprintf ("move_params_%s%d:") label env_num  ;
                                      "mov rcx, qword [rbp + 8 * 3]";
                                      "cmp rcx, 0";
                                      Printf.sprintf ("je alloc_clousre_%s%d") label env_num;
                                      "inc rcx";
                                      "mov rsi, rcx";
                                      "shl rsi, 3";
                                      "MALLOC rbx, rsi";
                                      Printf.sprintf ("get_first_addr_%s%d:") label env_num ;
                                      "mov rdx, 32";
                                      "add rdx, rbp";
                                      Printf.sprintf ("loop_args_%s%d:") label env_num;
                                      "dec rcx";
                                      "mov rsi, [rdx + (8 * rcx)]";
                                      "mov [rbx + 8 * rcx], rsi" ;
                                      "inc rcx";
                                      Printf.sprintf ("loop loop_args_%s%d,rcx") label env_num;           
                                      "mov [rax], rbx";
                                      Printf.sprintf ("alloc_clousre_%s%d:") label env_num;
                                      (* new env adress in rbx *)
                                      "mov rbx, rax";
                                      "MALLOC rax, 17";
                                      "mov rcx, 0";
                                      "mov cl, 9";
                                      "mov byte [rax], cl";
                                      "mov qword [rax + 1], rbx ";
                                      Printf.sprintf ("mov qword [rax + 9], Lcode_%s%d") label env_num ;
                                      Printf.sprintf ("jmp Lcont_%s%d") label env_num;
                                      Printf.sprintf ("Lcode_%s%d:") label env_num;
                                      "push rbp";
                                      "mov rbp , rsp"]
and adjust_stack env_num expected_params_length= String.concat "\n" [
                                          Printf.sprintf("adjust_stack%d:") env_num;
                                          "mov rsi, qword [rbx]";
                                          "mov [rax], rsi";
                                          "sub rax, 8";
                                          "sub rbx, 8";
                                          Printf.sprintf("loop adjust_stack%d,rcx") env_num ;
                                          "add rax, 8";
                                          "mov rbp, rax";
                                          "mov rsp, rax";
                                          Printf.sprintf("mov rbx,%d")  expected_params_length;
                                          "inc rbx";
                                          "mov [rbp + 24], rbx";
                                          Printf.sprintf("jmp cont_to_body%d") env_num ;
                                          Printf.sprintf("equal_adjast%d:") env_num ;                             
                                          Printf.sprintf("mov rbx,%d") expected_params_length ;
                                          "mov [rbp + 24], rbx";]
and push_applic_args consts fvars args env = 
let n = List.length args in
let pushed_args = List.fold_right (fun arg acc -> acc^
                                                  "\n; Pushing Applic Arg\n"^
                                                  (generate_rec consts fvars env arg)^
                                                  "\npush rax\n"^
                                                  "; End Pushing Arg\n") args "" in

String.concat "\n" [pushed_args;(  Printf.sprintf "push %d ; Number of arguments Pushed" n)]

 let generate consts fvars e = generate_rec consts fvars 0 e;;

      end;;
let test_from_read s =  List.map Semantics.run_semantics (Tag_Parser.tag_parse_expressions (Reader.read_sexprs s));;
let test_make_consts_tbl s = (Code_Gen.make_consts_tbl (test_from_read s));;
let test_make_fvars_tbl s = (Code_Gen.make_fvars_tbl (test_from_read s));;
let test_generate s = List.map (Code_Gen.generate (test_make_consts_tbl s) (test_make_fvars_tbl s)) (test_from_read s);;
let test_print s = List.map (fun(x)->print_string(x)) (test_generate s);;