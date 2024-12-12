// function    ::=   identifier '(' identifier ( ',' identifier ) * ')' '=' ( expression | '{' ( expression ',' relation ';' ) + '}' )
// prompt      ::=   relation '?'
// relation    ::=   expression | relation ( '<' | '>' | '<=' | '≤' | '>=' | '≥' | '=' | '<>' | '≠'  ) expression
// expression  ::=   term | expression ( '+' | '-' ) term
// term        ::=   factor | term ( '*' | '/' ) ? factor
// factor      ::=   '(' expression ')' | number | identifier
// number      ::=   ( '0' | [1-9][0-9]* ) ( '.' [0-9]+ ) ?
// identifier  ::=   ( [a-zA-Zα-ωΑ-Ω] | '\'' [a-zA-Z0-9_]+ '\'' )

// TODO - create structs for each above definition

