(* Ex1 *) 
#use "reader.ml";;
open PC;;



(* Atomics *)

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


(* ------------------------ *)

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
	

let ntSemicolon= char ';';; 
(* Need to combine with other StringMetaChar *)
let ntEndOfLine = char '\n';;

(* 3.2.2 Line Comments *)
let rec skipComment s = 
	if s=[] then [] else
	try let _,ls = ntEndOfLine s in
		ls
	with X_no_match -> (skipComment (List.tl s));;

let parseLineComment s = 
	let _,ls = ntSemicolon s in
	skipComment ls;;

(* convert list of chars to Symbol *)
let makeSymbol s = 
	Symbol(list_to_string s);;

(* return the string part from parser *)
let getString s = 
	let r,ls = nt_string s in
	let _,(st,_) = r in
	(st,ls);;

(* convets list of sexper to nested Pair *)
let rec list_to_pair l = 
		let car = List.hd l and
		cdr = List.tl l in
		match cdr with
		| [Nil] -> Pair(car,Nil)
		| [] -> Pair(car,Nil)
		| _ -> Pair(car, (list_to_pair cdr)) ;;
		


(* parse the first sexpr and return the rest as char list *)
let rec parse_One_Sexpr s = 
		if s=[] then (Nil,[]) else
	(* white spaces *)
	let w,rest = nt_whitespaces s in
		if w != [] then 
		parse_One_Sexpr rest
		else
	(* Bool *)
	try let a,rest = parseBool s in
		(a,rest)
	with X_no_match ->
	(* Number *)
	try let a,rest = parseNum s in
		(a,rest)
	with X_no_match -> 
	(* Symbol *)
	try let a,rest = (plus nt_symbol_char) s in
		((makeSymbol a),rest)
	with X_no_match ->
	(* String *)
	try let a,rest = getString s in
		(String(list_to_string a),rest)
	with X_no_match ->
	(* ( *)
	try let a,rest = tok_lparen s in
		let p,rest = parse_Sexpr rest [] in
		(list_to_pair(p),rest)
	with X_no_match ->
	(* ) *)
	try let a,rest = tok_rparen s in
		(Symbol(list_to_string [a]),rest) 
	with X_no_match ->
	(* Line Comments *)
	try let ls = parseLineComment s in
		parse_One_Sexpr ls
	with X_no_match ->
	(* Quotes *)
	try 
		parse_QuoteLike s
	with X_no_match ->
	let rest = parse_Sexpr_Comments s in
		parse_One_Sexpr rest

	(* 3.3.8 Quote-like forms *)
	and parse_QuoteLike s = 
		(*qoute*)
		try let _,ls = nt_Quoted s in
			let p,rest = parse_One_Sexpr ls in
			(Pair(Symbol("qoute"),Pair(p,Nil)),rest)
		with X_no_match -> 
		(*quasiqoute*)
		try let _,ls = nt_QQuoted s in
			let p,rest = parse_One_Sexpr ls in
			(Pair(Symbol("quasiqoute"),Pair(p,Nil)),rest)
		with X_no_match -> 
		(*unquote-splicing*)
		try let _,ls = nt_UnquotedSpliced s in
			let p,rest = parse_One_Sexpr ls in
			(Pair(Symbol("unquote-splicing"),Pair(p,Nil)),rest)
		with X_no_match ->
		(*unquote*)
		try let _,ls = nt_Unquoted s in
			let p,rest = parse_One_Sexpr ls in
			(Pair(Symbol("unquote"),Pair(p,Nil)),rest)
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
			if one=Symbol(")") then (sexpr_ls,rest) else
			parse_Sexpr rest (sexpr_ls@[one]) ;;
		

(* TODO: change this to read_sexprs in reader.ml *)
let read_sexprs3 s =
	let p,_ = parse_Sexpr (string_to_list s) [] in
	p;;