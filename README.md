# kleecket

Or Racklee

## Description

Symbolic execution for a mini language.

We use functional data structures, allowing objects in different paths to be shared,
avoiding the duplication cost. 

Unlike mini-mc, we implement a scheduler, which follows the BFS order. 
This can be customized easily by replacing the queue data structure with
a priority queue. 

## Language Features

Our language is Turing complete, as it contains lambda calculus. We also add more
features so that programming in imperative style is possible.

### Core Features

- Integer, boolean, string, void, and unchecked integer operations
- Pair, empty, and their operations
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

### Unsupported Features (for now)

- Garbage collection: as of now, we do not implement garbage collection 
  for the sake of simplicity.
- Multithreading: this in fact should be achievable easily via 
  Racket's `thread` support. However, the output will be difficult to read, so 
  we don't implement it.

## Installation

First, install [Racket](http://racket-lang.org). Then, install 
[Rosette](https://docs.racket-lang.org/rosette-guide/index.html), either via 
`raco` or DrRacket's package manager. 

## How to run

Either execute `racket showcase.rkt` or open `showcase.rkt` with DrRacket and run it.

## Notes

- We use Rosette simply as an interface to SMT solver. We don't employ any 
  symbolic evaluation capabilities from Rosette.
- We interpret the program instead of embedding symbolic execution because
  we would like to have a complete control over the program state.
  Rosette workarounds this by a combination of program transformation and
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
