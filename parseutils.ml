(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)

open Sourcepos

exception Error of string

(* ********************* nowhere else to put this ******************************* *)

let parse_formula default string =
  let lexbuf = Lexing.from_string string in
  try
    Settings.temp_setting Settings.allow_tcep true
                          (fun () -> Parser.justaformula Lexer.make_token lexbuf)
  with 
  | Parsing.Parse_error ->
         (match default with 
          | Some default -> 
              let curr = lexbuf.Lexing.lex_curr_p in
              Printf.printf "\n**Parse error at character %d (just before \"%s\") \
                             when parsing assertion-string %s"
                            (curr.Lexing.pos_cnum-curr.Lexing.pos_bol)
                            (Lexing.lexeme lexbuf)
                            string;
              default
          | _            -> raise Parsing.Parse_error
         )
  | exn -> 
         (match default with
          | Some default -> 
              Printf.printf "\n**Unexpected exception %s \
                             when parsing assertion-string %s"
                            (Printexc.to_string exn)
                            string;
              default
          | _            -> raise exn
         )

let parse_axiom = parse_formula (Some Formula._recTrue)

(* ********************* what Arsenic, ToLatex and Compile fall back on ******************************* *)

let parse_program filename =
  let in_channel = open_in filename in
  let lexbuf = Lexing.from_channel in_channel in
  try
    let result = Parser.program Lexer.make_token lexbuf in
    close_in in_channel; 
    result
  with
  | Parsing.Parse_error ->
      (close_in in_channel;
       let curr = lexbuf.Lexing.lex_curr_p in
       raise (Error ("**Parse error at line "^string_of_int (curr.Lexing.pos_lnum)^ 
                     " character "^string_of_int (curr.Lexing.pos_cnum-curr.Lexing.pos_bol)^
                     " (just before \""^Lexing.lexeme lexbuf^"\")"))
                    )
  | Program.ParseError(spos,s) ->
        (close_in in_channel;
         raise (Error ("\n**SYNTAX ERROR at "^string_of_sourcepos spos ^ ": " ^ s))
        )
  | Lexer.LexError(spos,s) -> 
        (close_in in_channel;
         raise (Error ("\n**LEXING ERROR at "^string_of_sourcepos spos ^ ": " ^ s))
        )
  | exn -> (close_in in_channel; raise exn)
