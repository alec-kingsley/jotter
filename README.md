# Jotter interpreter

Jotter is for throwing math down and just figuring stuff out.
Its syntax is very familiar to real math.

Jotter is not meant to be a full programming language. It won't support complex string manipulation or data structures. Its goal is just to make life easier and solve problems quickly.

## Grammar

```
statement   ::=   prompt | function | relation | reset
function    ::=   identifier '(' identifier ( ',' identifier ) * ')' '=' ( expression | '{' '\n' ( expression ',' relation '\n' ) + '}' )
prompt      ::=   relation '?'
relation    ::=   expression (( '<' | '>' | '<=' | '≤' | '>=' | '≥' | '=' | '<>' | '≠'  ) expression ) *
reset       ::=   '---------' '-' +
expression  ::=   term (( '+' | '-' ) term ) *
term        ::=   factor (( '*' | '/' ) ? factor ) *
factor      ::=   '(' expression ')' | number | identifier | call
call        ::=   identifier '(' expression ( ',' expression ) * ')'
number      ::=   ( '0' | [1-9][0-9]* ) ( '.' [0-9]+ ) ? unit ?
identifier  ::=   ( [a-zA-Zα-ωΑ-Ω] | '\'' [a-zA-Z0-9_ ]+ '\'' )
unit        ::=   '[' unit_term ']'
unit_term   ::=   unit_factor (( '*' | '/') ? unit_factor) *
unit_factor ::=   unit | baseunit ( '^' '-' ? [1-9][0-9]* )
baseunit    ::=   [a-zA-Zα-ωΑ-Ω]+
```

## Basics

Any syntactically invalid lines are assumed to just be comments.

All variables must be one letter (or greek letter).

Here's a program to solve a system of equations:

```
3x + 2y = 7
y - x = -4

Print what x and y are: (the question mark means it's asking for those)
x ?
y ?
```

Expected output:
```
x: 3
y: -1
```

## Units

Another feature of Jotter is how it handles units:
```
t = 3 [ns]
v = 200 [km/s]
tv ?
```

Expected output:
```
tv: 0.6 [mm]
```

Units can also have different powers and sub-units. So
```
x = 3 [m / [m / kg] ^ 2]
```

is equivalent to
```
x = 3 [kg ^ 2 / m]
```

Note that powers can only go on the inside of the main unit block, so `3 [kg] ^2`
is invalid, while `3 [kg ^ 2]` and `3 [[kg] ^ 2]` are both valid.

## Comments and Page Breaks

Another comment format is by using parentheses with stars on the inside.
```
k = 5 [s] (*set k to 5 seconds*)
```

This is great for inline comments, or if a comment would be otherwise valid syntax.

You can only use each variable name once, but "page breaks" can separate groups. 
To insert a page break, simply create a line consisting only of "-" and at least 10 of them.

Example:
```
y = 3
-------------------------------------------------------------------
y = 4
```

## Functions

```
f(x) = 3x + 2 (* example function *)

g(x) = {
    x / 2,  x ≤ 1
    x,      1 < x ≤ 3
    2x,     x > 3
}


g(4) ? 
```

Expected output:
```
g(4): 8
```


