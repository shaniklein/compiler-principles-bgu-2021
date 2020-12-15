#use "semantic-analyser.ml";;

(* test 3.1 *)
let test_annotate str = 
  Semantics.annotate_lexical_addresses (List.hd (Tag_Parser.tag_parse_expressions (Reader.read_sexprs str)));;

(* test 3.2 *)
let test_tp str = 
  Semantics.annotate_tail_calls(test_annotate str);;

(* test Assignemnt2 *)
let tag str = 
  Tag_Parser.tag_parse_expressions (Reader.read_sexprs str);;



  
(* This code was taken from 
https://www.cs.cornell.edu/courses/cs3110/2020fa/textbook/mut/ex_counter.html *)
(* let count = 
  let counter = ref 0 in
  fun() -> incr counter;
  !counter;; *)