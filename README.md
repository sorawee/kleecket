# kleecket

Or Racklee

## Description

Symbolic execution for a mini language.

## Language Features

### Core Features

- Integer, boolean, string, void, and unchecked integer operations
- Symbolic values (only integer and boolean)
- Lambda functions (of one argument)
- Variable mutation
- Exception raising
- Print

### Syntactic Sugar

- Boolean operations
- When, let, letrec, sequencing, and while loop
- Assertion
- Checked integer operations (division specifically)

## Prerequisites

You should have [Racket](http://racket-lang.org) installed in your computer.
Then, install the package [Rosette](https://docs.racket-lang.org/rosette-guide/index.html), either via `raco` or DrRacket's package manager. 

## How to run

Either execute `racket showcase.rkt` or open `showcase.rkt` with DrRacket and run it.

## Details

- We use Rosette simply as an interface to SMT solver, and don't employ any 
  symbolic evaluation capabilities from Rosette.
- We interpret the program instead of embedding symbolic execution because
  we would like to have a complete control over the program state.
  Rosette works around this by a combination of program transformation and
  state rollbacks, which seems more complicated than just directly interpret
  the syntax.
- The usage of shift+reset can be avoided if we interpret in 
  continuation-passing style (CPS).

## Grammar

Please add grammar here!

## Contributors

- Jacob Van Geffen
- Kevin Zhao
- Sorawee Porncharoenwase
