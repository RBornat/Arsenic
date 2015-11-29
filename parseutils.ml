(* This file is part of Arsenic, a proofchecker for New Lace logic.
    Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
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