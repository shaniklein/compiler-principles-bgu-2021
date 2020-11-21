echo -e "Running tests.."
ocaml -I .. < test_input.txt > tests_output.txt
echo "$(diff -I '^#' -I '^=' output.txt tests_output.txt)"
