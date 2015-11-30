(* This file is part of Arsenic, a proofchecker for New Lace logic.
   Copyright (c) 2015 Richard Bornat.
   Licensed under the MIT license (sic): see LICENCE.txt or
   https://opensource.org/licenses/MIT
 *)
 
{
  open Parser
  
  exception LexError of Sourcepos.sourcepos * string
    
  let inc_linenum lexbuf =
  	let curr = lexbuf.Lexing.lex_curr_p in
  	lexbuf.Lexing.lex_curr_p <- 
  		{ lexbuf.Lexing.lex_curr_p with Lexing.pos_lnum = curr.Lexing.pos_lnum+1;
  										Lexing.pos_bol = curr.Lexing.pos_cnum
  		}
  
  let get_linenum lexbuf = 
  	let curr = lexbuf.Lexing.lex_curr_p in
  	curr.Lexing.pos_lnum
  	
  let get_loc lexbuf =
  	(Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)

}

let BLANK = [' ' '\t']
let NEWLINE = '\n'
let LINE = [^ '\n']* ('\n' | eof)
let COMMENT = '#' LINE
let NEXT_THREAD = '-' '-' ['-']+

let NUM = ['0'-'9']
let ALPHA =  ['a'-'z' 'A'-'Z']
let ALPHANUM = ALPHA | NUM | '_'

let number = NUM+

let idem = "idem" | "Idem" | ".." | "..."
let name = ALPHA (ALPHANUM | '\'')*
let pmsc = number ':' 'r' ALPHANUM*

let EOL = '\n'
let BREAK = "break"

rule make_token = parse

  | BLANK       {make_token lexbuf} (* Skip blanks and comments*)
  | NEWLINE     {inc_linenum lexbuf; make_token lexbuf}
  | COMMENT     {inc_linenum lexbuf; make_token lexbuf}
  | "(*"   		{ bracomment (get_loc lexbuf) lexbuf; make_token lexbuf }

  | eof         {EOP}   (* Give up on end of file *)

  | '('         {LPAR}
  | ')'         {RPAR}
  | '{'         {LBRACE}
  | '}'         {RBRACE}
  | '['         {SQBRA}
  | ']'         {SQKET}
  | "/*"        {LSBRACE}
  | "{*"        {LSBRACE}
  | "*/"        {RSBRACE}
  | "*}"        {RSBRACE}
  | "[*"        {LSSQBRA}
  | "*]"        {RSSQBRA}
  
  | NEXT_THREAD {THREADSEP}
  
  | "while"     {WHILE}
  | "do"        {DO}
  | "od"        {OD}
  | "until"     {UNTIL}
  | "if"        {IF}
  | "then"      {THEN}
  | "else"      {ELSE}
  | "fi"        {FI}
  | "assume"    {ASSUME}
  | "skip"      {SKIP}
  | "assert"    {ASSERT}
  
  | ';'         {SEMICOLON}
  
  | ":="        {BECOMES}
  
  | '+'         {PLUS}
  | '-'         {MINUS}
  | '*'         {TIMES}
  | '/'         {DIV}
  | '%'         {MOD}
  | "=>"        {IMPLIES}
  | "<=>"       {IFF}
  | '<'         {LESS}
  | "<="        {LESSEQUAL}
  | '='         {EQUAL}
  | "!="        {NOTEQUAL}
  | '>'         {GREATER}
  | ">="        {GREATEREQUAL}
  | '^'         {HAT}

  | "/\\"       {AND}
  | "\\/"       {OR}
  | "\\->/"     {ORLOOP}
  | '!'         {NOT}
  | ","         {COMMA}
  | ':'         {COLON}
  | '|'         {BAR}
  | '.'         {DOT}
  
  | "++"        {ARRAYSTORE}
  | "->"        {ARRAYMAPS}
    
(* | '_'        {UNDERSCORE} *)
  
  | "true"      {TRUE}
  | "false"     {FALSE}
  | "exists"    {EXISTS}
  | "Exists"    {EXISTS}
  | "forall"    {FORALL}
  | "Forall"    {FORALL}
  
  | "_U"        {UNIV} 
  | "_B"        {BFR} 
  | "since"     {SINCE}
  | "_since"    {SINCE}
  | "_since_"   {SINCE}
  | "ouat"      {OUAT}
  | "_ouat"     {OUAT}
  | "_T"        {OUAT}
  | "_sofar"    {SOFAR}
  | "_S"        {SOFAR}
  | "sofar"     {SOFAR}
  | "_S"        {SOFAR}
  | "fandw"     {FANDW}
  | "sitf"      {SITF}
  | "_c"        {COHERE}
  | "_cv"       {COHEREVAR}
  
  | "guarantee" {GUARANTEE}
  | "guar"      {GUARANTEE}
  | "given"     {GIVEN}
  | "macro"     {MACRO}
  | "tmacro"    {TMACRO}
  | "rely"      {RELY}
  
  | "lo"        {LO}
  | "bo"        {BO}
  | "uo"        {UO}
  | "go"        {GO}
  
  | "_assert"   {Q_ASSERT}
  | "_against"  {Q_AGAINST}
  | "_sp"       {Q_SP}
  | "_sat"      {Q_SAT}

  | number      {INT (Lexing.lexeme lexbuf)}
  | name        {NAME (Lexing.lexeme lexbuf)}
  | pmsc        {PMSREG (Lexing.lexeme lexbuf)}

  | _           {raise (LexError (get_loc lexbuf, "Invalid character '" ^ 
                                                  Lexing.lexeme lexbuf ^ 
                                                  "'"
                                 )
                       )
                }

(* and comment = parse
	|	'\n'	{ inc_linenum lexbuf; token lexbuf }
	|	_		{ comment lexbuf}
 *)
	
(* oh dear lor a recursive lexer ... *)
and bracomment spos = parse
	|	"(*"        { bracomment (get_loc lexbuf) lexbuf; 
					  bracomment spos lexbuf
					}
  	| 	"*)"        { () }
  	| 	'\n'        { inc_linenum lexbuf; bracomment spos lexbuf }
  	|	eof			{ raise (LexError (spos, "unmatched comment-bracket '(*'")) }
  	| 	_           { bracomment spos lexbuf }
      
{

let build_prog_from_string s =
  Parser.program make_token (Lexing.from_string s)

}
