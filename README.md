# Jotter Interpreter

Jotter is for throwing math down and just figuring stuff out.
Its syntax is very familiar to real math.

Jotter is not meant to be a full programming language. It won't support complex string manipulation or data structures. Its goal is just to make life easier and solve problems quickly.

## Usage

`cargo run` - open an interactive Jotter terminal

`cargo run example.jt` - run a Jotter program from a file

## Grammar

```
statement   ::=   prompt | function | relation | reset
function    ::=   identifier '(' identifier ( ',' identifier ) * ')' '=' ( expression | '{' '\n' ( expression ',' relation '\n' ) + '}' )
prompt      ::=   relation '?'
relation    ::=   expression (( '<' | '>' | '<=' | '≤' | '>=' | '≥' | '=' | '<>' | '≠'  ) expression ) *
reset       ::=   '-'{10,}
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
x : 3
y : -1
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
t * v : 600 [μm]
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

So far, only the SI base units are supported. (meter, kilogram, second, ampere, kelvin, mole, candela)
Each unit is only case sensitive if written as an abbreviation (like `km`) but can be written with any case
and with or without an `s` at th end if not abbreviated. (`kilometer`, `Kilometer`, `KILOMETERS` are all acceptable)

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
g(4) : 8
```

Note that any comments within a multi-line function definition must be in the (**) format.

## Planned Features

### Units

- Names for SI units outside base units. (Watt, Hour, etc)
- Support for customary units as well as Metric
- Ability to add user-defined units

### Solver

- Ability to solve non-linear systems of equations
- Add common math functions such as `sin`, `cos`, `tan`, `log`, `mod`

### Functions

- Add integrals and derivatives, as well as a differential equation solver

