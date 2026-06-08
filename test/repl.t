Only #check and #eval produce output (#check the normal form and type,
#eval just the normal form); declarations are silent.

  $ mtt <<EOF
  > #check Type
  > #check fun (A : Type) => fun (x : A) => x
  > #check (fun (A : Type 1) => fun (x : A) => x) Type
  > #eval (fun (A : Type 1) => fun (x : A) => x) Type
  > EOF
  Type : Type 1
  fun (A : Type) => fun (x : A) => x : (A : Type) -> A -> A
  fun (x : Type) => x : Type -> Type
  fun (x : Type) => x

Declarations extend the context; defs unfold, theorems are opaque:

  $ mtt <<EOF
  > axiom A : Type
  > axiom a : A
  > def d := a
  > theorem t : A := a
  > #check d
  > #check t
  > EOF
  a : A
  t : A

Errors are reported without ending the session:

  $ mtt <<EOF
  > #check y
  > ?!
  > #check Type Type
  > #check Type
  > EOF
  1:8: unbound variable: y
  1:1: syntax error: unexpected character '?'
  type error: expected a function, but Type has type Type 1
  Type : Type 1

The :help, :env, and :quit meta-commands are handled by the REPL, not the
grammar; :quit ends the session, so the line after it never runs:

  $ mtt <<EOF
  > :help
  > :quit
  > #check Type
  > EOF
  mtt REPL — enter one statement per line. Commands:
    :help, :h        show this help
    :env             list the bindings in scope
    :quit, :q        exit (or Ctrl-D)
  
    #check t         report the normal form and type of t
    #eval t          report just the normal form of t
    #check_equal t u assert t and u are definitionally equal
    axiom x : A      postulate x of type A
    def x [: A] := t define x (annotation optional)
    theorem x : A := t  prove A with t (opaque)
    prelude          first line only: start without the standard prelude


:env lists the bindings in scope, oldest first. Opting out of the prelude
(`prelude` first) keeps the environment to just what is declared:

  $ mtt <<EOF
  > prelude
  > axiom A : Type
  > axiom a : A
  > def d := a
  > :env
  > :quit
  > EOF
  A : Type
  a : A
  d : A

Because the prelude loads lazily (so a leading `prelude` can still opt out),
:env before the first statement reports that nothing has loaded yet:

  $ mtt <<EOF
  > :env
  > :quit
  > EOF
  no bindings yet (the prelude loads on the first statement; `prelude` opts out)

