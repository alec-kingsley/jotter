# Jotter Interpreter

Jotter is for throwing math down and just figuring stuff out.
Its syntax is very familiar to real math.

Jotter is not meant to be a full programming language. It won't support complex string manipulation or data structures. Its goal is just to make life easier and solve problems quickly.

## Usage

`cargo run` - open an interactive Jotter terminal

`cargo run example.jt` - run a Jotter program from a file

## Basics

Any syntactically invalid lines are assumed to just be comments.

All variables must be one letter (or greek letter).

Here's a program to solve a system of equations:

```
3x + 2y = 7
y - x = -4

Print what x and y are:
('?' represents a prompt)
x ?
y ?
```

Expected output:

```
x ≡ 3
y ≡ -1
```

Jotter will also simplify expressions for you. As an example:

```
(a+b)(a+b)?
```

Expected output:

```
(a + b)(a + b) ≡ aa + 2ab + bb
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
tv ≡ 0.6 [mm]
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

Most common metric and US customary units are supported.

Each unit is only case sensitive if written as an abbreviation (like `km`) but can be written with any case
and with or without an `s` at the end if not abbreviated. (`kilometer`, `Kilometer`, `KILOMETERS` are all acceptable)

## Complex Numbers

Complex numbers are supported, and it will divide them cleanly.

Example:
```
(-15 + 23i)/(5 + 2i)?
(25 - 60i)/(8 - i)?
(3 + 2i)(1 - 5i)?

Expected output:
(23i - 15)/(5 + 2i) ≡ -1 + 5i
(25 - 60i)/(8 - i) ≡ 4 - 7i
(3 + 2i)(1 - 5i) ≡ 13 - 13i
```

Note that it will initially parse all imaginary and real numbers independently, hence why it would display `23i - 15` instead of the more standard `-15 + 23i`. It will combine these in the simplification process, so by itself,

```
-15 + 23i?

yields:
23i - 15 ≡ -15 + 23i
```

A consequence of this is that units work weirdly with imaginary numbers. You can either specify the unit after each term, or multiply by the unit you want. For example,
```
(3 + 2i) [km] = 3[km] + 2i[km]?
3[km] + 2i[km]?

Expected output:
(3 + 2i)*1 [km] = 3 [km] + 2i [km] ≡ True
3 [km] + 2i [km] ≡ (3 + 2i) [km]
```

## Comments

As before, any syntactically invalid line is considered a comment. This can mean that an unintentional typo will silently not do anything, but as this is not meant for large programs it should not be an issue.

Another comment format is by using parentheses with stars on the inside.

```
k = 5 [s] (*set k to 5 seconds*)
```

This is great for inline comments, or if a comment would be otherwise valid syntax.


## Contexts

You can only use each variable name once, but "contexts" can separate groups.
To insert a context, simply create a line with only a ">" token. Return to the previous context
by using just the "<" token.

Example:

```
y = 3
>
x = 2
x + y ?
<
x + y ?
```

Expected output:

```
    x + y ≡ 5
x + y ≡ x + 3
```

Each context can have its own contexts as children. You may think of the `>` as a way to just
save a program state to come back to it. 

In an interactive terminal, it will display as many `>` as are the current context.
To leave a context in a terminal, one can also use `Ctrl+d`. The above usage in a terminal while using `Ctrl+d` would look like this:

```
> y = 3
> >
>> x = 2
>> x + y ?
x + y ≡ 5
>>
> x + y ? (* Ctrl+d pressed before this *)
x + y ≡ x + 3
```

When only one `>` is remaining as the prompt for the interactive Jotter terminal, `Ctrl+d` will end the session.

## Functions

```
f(x) = 3x + 2 (* example function *)

g(x) = {
    x / 2,  x ≤ 1
    x,      1 < x ≤ 3
    2x,     x > 3
}


f(2) ?
g(4) ? 
```

Expected output:

```
f(1) ≡ 5
g(4) ≡ 8
```

Note that any comments within a multi-line function definition must be in the (\*\*) format.

## Number Representation

Numbers have two different representations that they'll switch between: "Rational" and "Decimal".

If a number has been constructed purely from rational components, then it will continue to display it as such. For example,
`3/2 + 4/3?` will yield `2`, and `2 * 1/3` will yield `2/3`.

If instead a number has been constructed using a decimal at any point, or if the number comes from a solving algorithm that involved an approximation, it will store and print as a decimal. So

`3.0/2 + 4/3` will yield `2.`, with the final `.` signifying that the number is stored as a decimal. If the number is stored as a decimal, then it is to be considered approximate.

## Relations

This feature has limited usage in the program's current state, as Jotter can't yet solve non-linear systems. However, these can help with some simplifications.

```
a/a?
Expected output: a/a: a/a
(it won't cancel this out in case a is 0)

a > 0
a/a?
Expected output: a/a ≡ 1
(it can now safely perform this operation)
```

Additionally, if you specify a relation which becomes false, the program will quit. For example,

```
x > 10
x = 3
```
(This will fail)

### Polynomial Solver

Jotter can solve polynomials. Example:

Square root:
```
xx = 4
x?
```
Expected output:
```
x ∈ {-2., 2.}
```

Complex polynomial:
```
xxxxxxx + 850xxxx + 1229xxx + 33454x - 5xxxxxx - 124xxxxx - 16925xx = 18480
x?
```
Expected output:
```
x ∈ {-11., -5., 1., 2., 3., 7., 8.}
```

## Oddities

Some of the grammar yields expressions that could be read a bit ambiguously. For example, a unit is attached directly to the number before it, so
```
3/4 [m]
```

is the same as
```
3/(4 [m])
```

For readability, however, if you were to write
```
(3/4) [m]?
```
, then it would print out
```
3/4 [m]
```

as the result.

Function definitions can also be a bit ambiguous. For example,
```
f(x) = 3x + 2
```
could either be read as a function definition, or as trying to find the intersection between `f(x)` and `3x + 2`. It will always choose the function definition in this case, and so for the other case a user can write `1.0 * f(x) = 3x + 2`, or `3x + 2 = f(x)`.

There is not a negative sign per se, but an expression can start out with subtracting. So
```
-3?
```
Will yield `-3` as expected, but
```
3 + -3?
```
will fail.

## Implementation Details

### Grammar

Tabs and spaces are ignored, but new lines do separate lines.

```

statement   ::=   prompt | function | stateswitch
function    ::=   identifier '(' identifier ( ',' identifier ) * ')' '=' ( expression | '{' '\n' ( expression ',' relation '\n' ) + '}' )
prompt      ::=   relation '?'
relation    ::=   expression (( '<' | '>' | '<=' | '≤' | '>=' | '≥' | '=' | '<>' | '≠'  ) expression ) *
stateswitch ::=   '>' | '<'
expression  ::=   term (( '+' | '-' ) term ) *
term        ::=   factor (( '*' | '/' ) ? factor ) *
factor      ::=   '(' expression ')' | number | identifier | call
call        ::=   identifier '(' expression ( ',' expression ) * ')'
number      ::=   ( '0' | [1-9][0-9]* ) ( '.' [0-9]+ ) ? 'i' ? '%' ? unit ? | unit
identifier  ::=   ( [a-zA-Zα-ωΑ-Ω] | '\'' [a-zA-Z0-9_ ]+ '\'' )
unit        ::=   '[' unit_term ']'
unit_term   ::=   unit_factor (( '*' | '/') ? unit_factor) *
unit_factor ::=   unit | 1 | baseunit ( '^' '-' ? [1-9][0-9]* ) ?
baseunit    ::=   [a-zA-Zα-ωΑ-Ω]+
```

The grammar does not yet allow for the '-' operator to be used outside of subtraction except as the first element of an expression. i.e., `-1 + 3` is fine, as is `3 - 1`, but `3 + -1` is not.

### Piecewise Functions

For piecewise functions, the relations are evaluated top-to-bottom, with the first true one found being picked. As this is atypical for mathematical definitions, it is not recommended to take advantage of this.

### Supported Units

#### Length

- meter (m), inch (in), foot (ft), yard (yd), mile (mi)

#### Volume

- liter (l), cup (c), pint (pt), quart (qt), gallon (gal)

#### Mass

- gram (g), pound (lb)

#### Time

- second (s), minute (min), hour (h), day (d)

#### Electric Current

- ampere (A)

#### Temperature

- kelvin (K)

#### Amount of Substance

- mole (mol)

#### Luminous Intensity

- candela (cd)

#### Unitless

- radian (rad), steradian (sr)

#### Frequency

- hertz (Hz)

#### Force

- newton (N)

#### Pressure

- pascal (Pa)

#### Energy

- joule (J)

#### Power

- watt (W)

#### Electric Charge

- coulomb (C)

#### Voltage

- volt (V)

#### Capacitance

- farad (F)

#### Electric Resistance

- ohm (Ω)

#### Electric Conductance

- siemens (S)

#### Magnetic Flux

- weber (Wb)

#### Magnetic Flux Density

- tesla (T)

#### Electric Inductance

- henry (H)

#### Luminous Flux

- lumen (lm)

#### Illuminance

- lux (lx)

#### Radioactivity

- becquerel (Bq)

#### Absorbed Dose of Ionizing Radiation

- gray (Gy)

#### Stochastic Health Effect of Ionizing Radiation

- sievert (Sv)

#### Catalytic Enzyme/Catalyst Activity

- katal (kat)

All units support all SI prefixes. This includes the US customary units, so "kilofoot" is equivalent to 1000 feet. (This will likely be changed)

Currently, quantity units are treated as though they were unitless. Technically this may be true, but it is not useful for display purposes, and so it will likely be updated. (if I say `1 [rad / s]?` it should print `1 [rad / s]`, whereas it currently prints `1 [1 / s]`).

### Polynomial Solver

The polynomial solver uses the Aberth method.

## Bugs

Bugs are still expected in this project. As I find them, I will add them as failing test cases before fixing them. Run
```
cargo test
```
to see the current bugs.

Before moving on to any further features, I plan to thoroughly test this project.

## Planned Features

### Units

* Ability to add user-defined units

### Solver

* Ability to solve non-linear systems of equations (this can use polynomial solver)
* Add common math functions such as `sin`, `cos`, `tan`, `log`, `mod`

### Functions

* Add integrals and derivatives, as well as a differential equation solver

