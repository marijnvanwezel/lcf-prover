# prover

The prover was written in Haskell. It can be ran like so:

```sh
$ ghc main.hs
$ ./main
```

This opens an interactive session with the prover. By typing the command `help`, you'll get a list of commands to run, and their syntax. Below, an example proof session is given:

```
LCF-style theorem prover
Type 'help' for a list of commands.
> g Imp (Var "A") (Imp (Imp (Var "A") (Var "B")) (Var "B"))
______________________________________Goal
(A → ((A → B) → B))

> top
Theorem not yet proven.
> e intro
A
______________________________________Goal
((A → B) → B)

> e intro
A
(A → B)
______________________________________Goal
B

> e elim (Var "B")
A
(A → B)
______________________________________Goal
(B → B)

> b
A
(A → B)
______________________________________Goal
B

> e elim (Var "A")
A
(A → B)
______________________________________Goal
(A → B)

> e assumption
A
(A → B)
______________________________________Goal
A

> e assumption
QED.

> top
______________________________________Goal
(A → ((A → B) → B))
```
