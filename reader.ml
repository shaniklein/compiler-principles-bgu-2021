
#use "pc.ml";;
open PC;;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Fraction of int * int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(Float f1), Number(Float f2) -> abs_float(f1 -. f2) < 0.001
  | Number(Fraction (n1, d1)), Number(Fraction (n2, d2)) -> n1 = n2 && d1 = d2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | _ -> false;;

module Reader: sig
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (lowercase_ascii ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;


let read_sexprs string = raise X_not_yet_implemented;;
  
  
  (*3.3.4 String*)
(* String  *)
let nt_string_meta_chars =
  let nt_return = pack (word_ci "\\r") (fun _ ->'\r') in
  let nt_newline = pack (word_ci "\\n") (fun _ ->'\n') in
  let nt_tab = pack (word_ci "\\t") (fun _ -> '\t') in
  let nt_f = pack (word_ci "\\f") (fun _ -> '\012') in
  let nt_backslash = pack (word "\\\\") (fun _ -> '\\') in
  let nt_quote = pack (word "\\\"") (fun _ -> '"') in
  let nt = disj_list [nt_return; nt_newline; nt_tab; nt_f; nt_backslash; nt_quote;] in
  nt;; 

(*any character other than backslash  or double qoute *)
let nt_string_literal_char = pack (range '\032' '\255') (fun(ds) -> match ds with
    | '\\' -> raise X_no_match
    | '\"' -> raise X_no_match
    | _ -> ds );;

let nt_string_char = 
  let nt = disj nt_string_literal_char nt_string_meta_chars in
  nt;;

let nt_string = 	
	let nt_quote= char '\"' in
	let nt=  caten nt_quote (caten (star nt_string_char) nt_quote) in
	nt;;

(* 3.3.5 Char *)
let nt_char_prefix = word "#\\";;
let nt_nul = word_ci "nul";;
let nt_newline = word_ci "newline";;
let nt_return = word_ci "return";;
let nt_tab = word_ci "tab";;
let nt_page = word_ci "page";;
let nt_space = word_ci "space";;

let nt_null_to_char  = pack nt_nul (fun (ds) -> '\000');;
let nt_newline_to_char  = pack nt_newline (fun (ds) -> '\010');;
let nt_return_to_char  = pack nt_return (fun (ds) -> '\013');;
let nt_tab_to_char  = pack nt_tab (fun (ds) -> '\009');; 
let nt_page_to_char  = pack nt_page (fun (ds) -> '\012');;
let nt_space_to_char  = pack nt_space (fun (ds) -> '\032');;

let nt_named_char = disj_list [nt_null_to_char;nt_newline_to_char;nt_return_to_char;nt_space_to_char;nt_tab_to_char;nt_page_to_char];;

let nt_named_chars = caten nt_char_prefix nt_named_char;;
(*any charachter that greater than the space character in the ASCII table*)
let nt_visible_char = caten nt_char_prefix (range '\032' '\255');;


let nt_char  =
  let test = disj nt_named_chars nt_visible_char in
  pack test (fun (ds) -> match ds with
      |(_,l) -> Char (l)
    );;


  
end;; (* struct Reader *)
