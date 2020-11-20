
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

(*Abstract*)
 (*This code is from RS3*)
let nt_whitespaces = star (char ' ');;
let ntHashtag = char '#';;
let ntSlash = char '/';;
let ntDot = char '.';;

let digit = range '0' '9';;
let digitSeq = plus digit;;

let nt_Quoted = char '\'';;
let nt_QQuoted = char '`';;
let nt_Unquoted = char ',';;
let nt_UnquotedSpliced = word ",@";;

let nt_Sexpr_Comment = word_ci "#;";;
(* ------------------------ *)

(*takes 3 parsers , concate them and remove the left and right parts*)
let make_paired nt_left nt_right nt =
let nt = caten nt_left nt in
let nt = pack nt (function (_, e) -> e) in
let nt = caten nt nt_right in
let nt = pack nt (function (e, _) -> e) in
  nt;;

let nt_char_to_ignore =
  let nt_tab = char '\t' in
  let nt_f = char '\012' in
  let nt_n = char '\n' in
  let nt_r = char '\r' in
  let nt = disj_list [nt_whitespace;nt_tab; nt_f; nt_n; nt_r;] in
  nt;; 
 
 let nt_chars_to_ignore =star nt_char_to_ignore;;
 let make_clean nt = make_paired nt_chars_to_ignore nt_chars_to_ignore nt;;


let make_spaced nt = make_paired nt_whitespaces nt_whitespaces nt;;
let tok_lparen = make_clean ( char '(');;
let tok_rparen = make_clean ( char ')');; 
(*end of code from RS3*)
(* recognize dot with spaces*)
let tok_dot = make_clean (char '.');;



(* 3.3.1 Boolean *)
(* returns sexpr (of Bool ) * char list (of unparesd characters)
		example: parseBool (string_to_list "#Tfg");; *)

let parseBool s = 
	let ntTrue = char_ci 't' 
	and ntFalse = char_ci 'f'
	and rest =  fun (_,r) -> r in
	try let tst = rest (ntHashtag s) in
		try let t = ntTrue ( tst) in
			(Bool(true), rest(t)) 
		with X_no_match -> 
		try let f = ntFalse ( rest (ntHashtag s)) in
			(Bool(false), rest(f)) 
		with X_no_match -> nt_none()
	with X_no_match -> nt_none();;


(* 3.3.2 & 4 & 7 Numbers *)

(* returns  int (-1 or 1 as sign) * char list (rest of the number) 
	later one need to multiply sign by the parsed number *)
let ntSign s = 
	let ntPlus = char '+'
	and ntMinus = char '-' 
	and extractSign = fun (i) -> if i='+' then 1 else -1 in
	try let d = disj ntPlus ntMinus in
		pack d extractSign s;
	with X_no_match -> (1,s)


(* convert char of int to int *)
let char_to_int c = 
	int_of_char c - int_of_char '0';;

(* maps list of chars to int *)
let list_of_char_to_int lst =
  List.map char_to_int lst;;

(* calc natural number from int list *)
let nat s = 	
	List.fold_left 
		(fun a b -> 10*a + b)
		0
		(list_of_char_to_int s);;

let composeFuncs f1 f2 = 
	fun s -> f1 (f2 s);;

(* maps list of chars to list of float *)
let list_of_char_to_float lst =
	let chat_fo_float = composeFuncs float_of_int char_to_int in
  	List.map chat_fo_float lst;;

(* calc mantissa (after the dot) number from int list *)
let mantissa s = 
	let f = 	
	List.fold_right
		(fun a b -> a +. 0.1*.b)
		(list_of_char_to_float s)
		0.0 in
		f /. 10.;;

(* Naturals parser *)
let parseNat s = 
	let sign,ls = ntSign s in
	let numLst, ls =  digitSeq ls in
	(sign * (nat numLst),ls);;

(* Mantissa parser *)
let parseMantissa ls = 
	let nums,ls = digitSeq ls in
	( (mantissa nums), ls);;


(* return the greatest common divisor of two numbers *)
let gcd a b = 
	let a,b = if (a>b) then (a,b) else (b,a) in
	let rec recGcd a b =
		if b=0 then a else recGcd b (a mod b) in
		recGcd a b;;

(* return parsed number as int after E if exists 
	example: parseScientific ['e';'0';'2';...] -> (2,..) *)
let parseScientific s = 
	let ntE = char_ci 'e' in
	let _,ls = ntE s in
	parseNat ls ;;

(* float*int->float
	return nEe *)
let rec raiseExp n e =
	if e =0 then n else 
		if e>0 then raiseExp (n*.10.0) (e -1) 
				 else raiseExp (n/.10.0) (e +1) ;;

(* returns sexpr (of Number ) * char list (of unparesd characters)
		example: parseNum (string_to_list "+0034.0100");; *)
let parseNum s = 
	let n1,ls = parseNat s in
	(* fraction *)
	try let _, ls = ntSlash ls in
		let n2,ls = parseNat ls in
		let gcdNum = gcd n1 n2 in
		(Number(Fraction (n1/gcdNum,n2/gcdNum)) , ls)
	with X_no_match ->
	(* float *)
	try let _, ls = ntDot ls in
		let n2,ls = parseMantissa ls in
		let fltNum = if n1>0 then (float_of_int n1) +. n2 else (float_of_int n1) -. n2 in
		(* scientific float *)
		try let e,ls = parseScientific ls in
			let exp = raiseExp fltNum e in
			(Number(Float(exp)), ls)
		with X_no_match ->
		(Number(Float (fltNum)), ls)
	with X_no_match -> 
	(* scientific int *)
	try let e,ls = parseScientific ls in
		let exp = raiseExp (float(n1)) e in
		(Number(Float(exp)), ls)
	with X_no_match ->
	(* int as fraction*)
	(Number(Fraction (n1,1)),ls);;
	

(*3.3.3 Symbol*)
(*As we saw in RS3 the range parser constructor takes two chars and returns a parser that accepts a single char in the given character range*)
let nt_lower_case = range 'a' 'z';;
(*As requested, Our parser convert all literal symbol characters to lowercase *)
let nt_upper_case = pack (range 'A' 'Z') (fun(x) -> Char.lowercase_ascii x );;
let digits = range '0' '9';;

let nt_special_char = 
  let nt_exclemation = char '!' in
  let nt_dollar =  char '$' in
  let nt_power = char '^' in
  let nt_star = char '*' in
  let nt_score =  char '-'  in
  let nt_underscore =  char '_' in
  let nt_eq =  char '='  in
  let nt_plus = char '+' in
  let nt_left_arrow =  char '<' in
  let nt_right_arrow =  char '>' in
  let nt_slash =  char '/' in
  let nt_quest_mark =  char '?' in
  let nt_colon =  char ':' in  
  let nt = disj_list [nt_exclemation ; nt_dollar ; nt_power ; nt_star ; nt_score ; nt_underscore ; nt_eq ; nt_plus ; 
                      nt_left_arrow ; nt_right_arrow ; nt_quest_mark ; nt_slash ; nt_colon ] in
  nt;;
let nt_dot= char '.';;

let nt_symbol_char_no_dot =    
  let nt = disj_list [nt_lower_case;nt_upper_case;digits ; nt_special_char; ] in
  nt;;
  
  let nt_symbol_char=
	let nt=disj_list[nt_symbol_char_no_dot ;nt_dot ] in
  nt;;
  
	let nt_symbol_char_with_dot=
		let nt=caten nt_symbol_char (plus nt_symbol_char) in
		let nt=pack nt (fun (a,b)->list_to_string(a::b)) in
		nt;;
	
	let nt_symbol = 
	let nt=pack nt_symbol_char_no_dot (fun ds-> list_to_string([ds])) in
	let nt=disj nt_symbol_char_with_dot  nt in 
	let nt=pack nt (fun (ds)->Symbol (ds)) in
	nt;;
		
 (*3.3.4 String*)
  let nt_string_meta_chars =
  let nt_backslash = pack (word "\\\\") (fun _ -> '\\') in
  let nt_quote = pack (word "\\\"") (fun _ -> '"') in
  let nt_tab = pack (word_ci "\\t") (fun _ -> '\t') in
  let nt_f = pack (word_ci "\\f") (fun _ -> '\012') in
  let nt_n = pack (word_ci "\\n") (fun _ ->'\n') in
  let nt_r = pack (word_ci "\\r") (fun _ ->'\r') in
  let nt = disj_list [nt_backslash; nt_quote; nt_tab; nt_f; nt_n; nt_r;] in
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
    let nt_quote = char '\"' in
    let nt_str = diff nt_any (one_of "\\\"") in
    let nt_str = disj nt_str nt_string_meta_chars in
    let nt_str = star nt_str in
    let nt = caten nt_quote (caten nt_str nt_quote) in
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


(*3.3.6 Nil*)
let nt_nil =
	let nt= caten tok_lparen tok_rparen in
    let nt = pack nt (fun _ -> Nil) in
	nt;;
	

let ntSemicolon= char ';';; 
let ntEndOfLine = char '\n';;

(* 3.2.2 Line Comments *)
let rec skipComment s = 
	if s=[] then [] else
	let eol = disj nt_named_char ntEndOfLine in
	try let _,ls = eol s in
		ls
	with X_no_match -> (skipComment (List.tl s));;

let parseLineComment s = 
	let _,ls = ntSemicolon s in
	skipComment ls;;


(* return the string part from parser *)
let getString s = 
	let r,ls = nt_string s in
	let _,(st,_) = r in
	(st,ls);;


	  
(* parse the first sexpr and return the rest as char list *)
let rec parse_One_Sexpr s = 
	if s=[] then ([],[]) else
	(* white spaces *)
	let w,rest = nt_chars_to_ignore s in
		if w != [] then 
		parse_One_Sexpr rest
		else
	(* Bool *)
	let nt_bool = make_clean (not_followed_by parseBool nt_symbol) in
	try let a,rest = nt_bool s in
		([a],rest)
	with X_no_match ->
	(* Char *)
	try let a,rest = make_clean(nt_char) s in
		([a],rest)
	with X_no_match ->
	(* Number *)
	let nt_num = make_clean(not_followed_by parseNum nt_symbol) in
	try let a,rest = nt_num s in
		([a],rest)
	with X_no_match -> 
	(* String *)
	try let a,rest =make_clean( getString) s in
		([String(list_to_string a)],rest)
		
	with X_no_match ->
	(* Line Comments *)
	try let ls = parseLineComment s in
		parse_One_Sexpr ls
	with X_no_match ->
	(* Quotes *)
	try 
		make_clean(parse_QuoteLike) s
	with X_no_match ->
	(*list*)
	try let a,rest = parse_list s in
		([a],rest)
	with X_no_match -> 
	(* Symbol *)
	try let a,rest =  make_clean(nt_symbol) s in
		([a],rest)
	with X_no_match ->

	let rest =  parse_Sexpr_Comments s in
		([],rest)
	

	and parse_list s=
	let rec make_proper_list = function
      | [] -> Nil
      | car::cdr -> Pair (car , make_proper_list cdr) in
	 let rec make_improper_list = function
      | [] -> Nil
	  (*in improper we know the last index*)
      | car::cdr::[] -> Pair (car, cdr)
      | car::cdr -> Pair (car , make_improper_list cdr) in
	
	let nt_plus = caten nt_whitespaces parse_One_Sexpr  in
    let nt_plus = pack nt_plus (fun (_, sexpr) -> sexpr) in
    let nt_plus = caten parse_One_Sexpr (star nt_plus) in
    let nt_plus = pack nt_plus (fun (car, cdr) -> car::cdr) in
	
	let nt_list = caten tok_lparen (caten nt_plus tok_rparen) in
	let nt_list = pack nt_list (fun (_, (sexprs, _)) -> make_proper_list (List.flatten sexprs)) in
    let nt_list = disj nt_nil nt_list in
	let nt_dotted_list = caten tok_lparen (caten nt_plus  (caten tok_dot (caten parse_One_Sexpr tok_rparen))) in
    let nt_dotted_list = pack nt_dotted_list (fun (_, (sexprs, (_, (last_sexpr, _)))) -> make_improper_list ((List.flatten sexprs)@last_sexpr)) in
    let nt = disj  nt_list nt_dotted_list  in
	let nt=make_clean nt in
	nt s
	
	(* 3.3.8 Quote-like forms *)
	and parse_QuoteLike s = 
		let check_empty = fun (p, rest) ->
				match p with 
				| []-> parse_One_Sexpr rest
				| _-> (p,rest) in
		(*qoute*)
		try let _,ls = nt_Quoted s in
			let p,rest = parse_One_Sexpr ls in
			let p,rest = check_empty (p, rest) in
			let p= List.hd p in
				([Pair(Symbol("quote"),Pair(p,Nil))],rest)
		with X_no_match -> 
		(*quasiqoute*)
		try let _,ls = nt_QQuoted s in
			let p,rest = parse_One_Sexpr ls in
			let p,rest = check_empty (p, rest) in
			let p= List.hd p in
			([Pair(Symbol("quasiquote"),Pair(p,Nil))],rest)
		with X_no_match -> 
		(*unquote-splicing*)
		try let _,ls = nt_UnquotedSpliced s in
			let p,rest = parse_One_Sexpr ls in
			let p,rest = check_empty (p, rest) in
			let p= List.hd p in
			([Pair(Symbol("unquote-splicing"),Pair(p,Nil))],rest)
		with X_no_match ->
		(*unquote*)
		try let _,ls = nt_Unquoted s in
			let p,rest = parse_One_Sexpr ls in
			let p,rest = check_empty (p, rest) in
			let p= List.hd p in
			([Pair(Symbol("unquote"),Pair(p,Nil))],rest)
		with X_no_match ->
		nt_none() 


	(* 3.2.3 Sexpr Comments *)
	(* TODO: make sure its VALID sexpr. it works now on any sexpr *)
	and parse_Sexpr_Comments s = 
		let _, ls = nt_Sexpr_Comment s in
		let one,rest = parse_One_Sexpr ls in 
		rest

	(* parse all sexprs 
		s 		- char list
		sexprs  - sexpr list it already parsed *)
	and parse_Sexpr s sexpr_ls= 
		if s=[] then (sexpr_ls,[]) else
		let one,rest = parse_One_Sexpr s in
			parse_Sexpr rest (sexpr_ls@one) ;;
		

let read_sexprs s = let p,_ = parse_Sexpr (string_to_list s) [] in
	p;;



 end;; (* struct Reader *)
 