﻿# High Level OCamllike Language Compiler

## Description:

Implementation of a compiler that compiles an OCaml-like high-level programming language into a low level stack oriented language. Compilation of a program takes a string input and returns a string of the program translated into the low level stack oriented language, which can then be interpreted and evaluated directly.

## Functionality:

* Parsing:
    * Takes in the string input (high level program) and parses the string using pattern matching and parser combinators in the MyOCaml library
    * Input: String (program)
    * Output: expr (expression which is made up of many different types)

* Compiling:
    * Takes in string input (high level program), parses the program, matches the parsed expr type and converts expr to com list, then match com list and convert to string

    * coms_of_ex
        * Input: expr
        * Output: com list
        * Follows operational semantics provided in the PDF description

    * coms_to_slist
        * Input: com list
        * Output: reversed string list
        * Used to convert com list to string list format

    * format_string_of_list
        * Input: string list
        * Output: string with corrected ordering
        * USed to correctly format the string for valid interpretation

* Interpreting:
    * Takes in a string as input, parses the string according to the low level stack oriented language, then evaluates the program and returns its trace.

    * parse_com
        * Input: string (low level program)
        * Output: com list
        * Parses the program using parse combinators and pattern matching

    * eval
        * Input: com list
        * Output: trace (trace resulted from evalutation of the inputted program)
        * Recursive function that keeps track of the stack, trace, program, and variable environment of the inputted program during evaluation, uses pattern matching and recursive calls

## How to Use: 

1. Open the compile.ml file in utop
2. Create a program following the rules defined in the Compiler_Specifications.pdf file
3. Set the program as a string (ex. let prog = "your program here";;)
4. Call compile function on your program (ex. let cprog = compile prog;;)
5. Call interp function on compiled program (ex. let eval = interp (compile prog);;)

## Sample Programs: 

For more example programs, view Compiler_Specifications.pdf. Follow specifications for syntax and semantics in order to construct a valid program to be compiled and interpreted.

### McCarthy’s 91 Function:

let rec mccarthy n =
    if n > 100 then n - 10
    else mccarthy (mccarthy (n + 11))
in
trace (mccarthy 22)

Outputted Trace: ["91" :: ϵ]

### Digits of π

let rec pi n =
    let q = 1 in
    let r = 180 in
    let t = 60 in
    let j = 2 in
    let rec loop n q r t j =
        if n > 0 then
            let u = 3 * (3 * j + 1) * (3 * j + 2) in
            let y = (q * (27 * j - 12) + 5 * r) / (5 * t) in
            trace y;
            let q' = 10 * q * j * (2 * j - 1) in
            let r' = 10 * u * (q * (5 * j - 2) + r - y * t) in
            let t' = t * u in
            let j' = j + 1 in
            loop (n - 1) q' r' t' j'
        else ()
    in
    loop n q r t j
in
pi 6

Outputted Trace: ["9" :: "5" :: "1" :: "4" :: "1" :: "3" :: ϵ]


