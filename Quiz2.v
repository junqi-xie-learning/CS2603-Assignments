(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2021/06/07.                                             *)
(* Due: 2020/06/25, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Quiz2.v) on CANVAS.               *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "Quiz2.vo" file is generated.               *)
(*                                                                   *)
(* 5. You should answer questions individually. You should not       *)
(*    discuss with others or try finding answers online.             *)
(*                                                                   *)
(* ***************************************************************** *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import PL.RTClosure PL.Imp PL.Lambda.
Import ListNotations.

Module OptF.

Definition add {A: Type} (f g: A -> option Z): A -> option Z :=
  fun st =>
    match f st, g st with
    | Some v1, Some v2 => Some (v1 + v2)
    | _, _ => None
    end.

Definition sub {A: Type} (f g: A -> option Z): A -> option Z :=
  fun st =>
    match f st, g st with
    | Some v1, Some v2 => Some (v1 - v2)
    | _, _ => None
    end.

Definition mul {A: Type} (f g: A -> option Z): A -> option Z :=
  fun st =>
    match f st, g st with
    | Some v1, Some v2 => Some (v1 * v2)
    | _, _ => None
    end.

End OptF.

(* ################################################################# *)
(** * Task 1: Control flow programs with pointers *)

Module ImpCFPointer.

(** Here we define a programming language with break, continue, addresses and
    pointers. *)

Definition var: Type := nat.

Inductive aexp : Type :=
  | ANum (n : Z)
  | AId (X : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADeref (a1: aexp)
  | AAddr (a1: aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Inductive com : Type :=
  | CSkip
  | CAss (a1 a2 : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CBreak
  | CCont.

(** Its expressions' denotations can be defined as we taught in the lecture of
    Pointer_And_Address. *)

Definition var2addr (X: var): Z := Z.of_nat X + 1.

Definition state: Type := Z -> option Z.

Fixpoint aevalR (a: aexp): state -> option Z :=
  match a with
  | ANum n => fun _ => Some n
  | AId X => fun st => st (var2addr X)
  | APlus a1 a2 => OptF.add (aevalR a1) (aevalR a2)
  | AMinus a1 a2  => OptF.sub (aevalR a1) (aevalR a2)
  | AMult a1 a2 => OptF.mul (aevalR a1) (aevalR a2)
  | ADeref a1 => fun st =>
                   match aevalR a1 st with
                   | Some n1 => st n1
                   | None => None
                   end
  | AAddr a1 => aevalL a1
  end
with aevalL (a: aexp): state -> option Z :=
  match a with
  | ANum n => fun _ => None
  | AId X => fun st => Some (var2addr X)
  | APlus a1 a2 => fun _ => None
  | AMinus a1 a2  => fun _ => None
  | AMult a1 a2 => fun _ => None
  | ADeref a1 => aevalR a1
  | AAddr a1 => fun _ => None
  end.

Record bexp_denote: Type := {
  true_set: state -> Prop;
  false_set: state -> Prop;
  error_set: state -> Prop;
}.

Definition opt_test (R: Z -> Z -> Prop) (X Y: state -> option Z): bexp_denote :=
{|
  true_set := fun st =>
                   match X st, Y st with
                   | Some n1, Some n2 => R n1 n2
                   | _, _ => False
                   end;
  false_set := fun st =>
                   match X st, Y st with
                   | Some n1, Some n2 => ~ R n1 n2
                   | _, _ => False
                   end;
  error_set := fun st =>
                   match X st, Y st with
                   | Some n1, Some n2 => False
                   | _, _ => True
                   end;
|}.

Fixpoint beval (b: bexp): bexp_denote :=
  match b with
  | BTrue =>
      {| true_set := Sets.full;
         false_set := Sets.empty;
         error_set := Sets.empty;
      |}
  | BFalse =>
      {| true_set := Sets.empty;
         false_set := Sets.full;
         error_set := Sets.empty;
      |}
  | BEq a1 a2 =>
      opt_test Z.eq (aevalR a1) (aevalR a2)
  | BLe a1 a2 =>
      opt_test Z.le (aevalR a1) (aevalR a2)
  | BNot b =>
      {| true_set := false_set (beval b);
         false_set := true_set (beval b);
         error_set := error_set (beval b);
      |}
  | BAnd b1 b2 =>
      {| true_set := Sets.intersect
                       (true_set (beval b1))
                       (true_set (beval b2));
         false_set := Sets.union
                        (false_set (beval b1))
                        (Sets.intersect
                           (true_set (beval b1))
                           (false_set (beval b2)));
         error_set := Sets.union
                        (error_set (beval b1))
                        (Sets.intersect
                           (true_set (beval b1))
                           (error_set (beval b2)));
      |}
  end.

(** The commands' denotations are also records. *)

Record denote: Type := {
  NormalExit: state -> state -> Prop;
  BreakExit: state -> state -> Prop;
  ContExit: state -> state -> Prop;
  ErrorExit: state -> Prop;
}.

Definition skip_sem: denote :=
  {|
     NormalExit := BinRel.id;
     BreakExit := BinRel.empty;
     ContExit := BinRel.empty;
     ErrorExit := Sets.empty
  |}.

Definition asgn_sem (DA1 DA2: state -> option Z): denote :=
  {|
     NormalExit :=
       fun st1 st2 =>
         exists a v,
           DA1 st1 = Some a /\
           DA2 st1 = Some v /\
           st1 a <> None /\
           st2 a = Some v /\
           forall a', a <> a' -> st1 a' = st2 a';
     BreakExit := BinRel.empty;
     ContExit := BinRel.empty;
     ErrorExit :=
       fun st =>
         DA1 st = None \/ DA2 st = None \/
         (exists a, DA1 st = Some a /\ st a = None)
  |}.

(** We define the semantics of skips and assignments for you. Your task is to
    define the denotations of break, continue, sequential composition and
    if-then-else. *)

(** **** Exercise: 1 star, standard (break_sem) *)

Definition break_sem: denote
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 1 star, standard (cont_sem) *)

Definition cont_sem: denote
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (seq_sem) *)

Definition seq_sem (d1 d2: denote): denote
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard (if_sem) *)

Definition if_sem (db: bexp_denote) (d1 d2: denote): denote
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

End ImpCFPointer.

(* ################################################################# *)
(** * Task 2: Call by value semantics of lambda calculus *)

Module CBVLambda.
Import LambdaIB.
Local Open Scope Z.
Local Open Scope string.

(** Consider the following lambda expressions. *)

Definition TRUE: tm := abs "t" (abs "f" "t").
Definition FALSE: tm := abs "t" (abs "f" "f").
Definition IFTHENELSE: tm := abs "b" (abs "x" (abs "y" (app (app "b" "x") "y"))).
Definition ZERO: tm := abs "F" (abs "x" "x").
Definition ONE: tm := abs "F" (abs "x" (app "F" "x")).

(** Please describe the evaluation process of the following expressions. *)

(** **** Exercise: 2 stars, standard *)

Definition expr1: tm := app (app (app IFTHENELSE TRUE) ZERO) ONE.

Definition process_1: list tm
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard *)

Definition expr2: tm := app ONE ONE.

Definition process_2: list tm
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

End CBVLambda.

(* ################################################################# *)
(** * Task 3: General Questions regarding compilers *)

Module Compiler.

(** **** Exercise: 1 star, standard  *)

(** Suppose you write a program in a software company and the company uses
    compiler [G]. If your program should have behavior [A] according the
    language's standard documentation [D] but does have behavior [B] when you
    compiler it and run it, which statements below about compiler [G] and
    language standard [D] are correct?

    1. The standard [D] is wrong and should be fixed.

    2. The compiler [G] has a bug.

    3. If the program is designed to have behavior [A], you should modify the
       program.

    This is a multiple-choice problem. You should use an ascending Coq list to
    describe your answer, e.g. [1; 2; 3], [1; 3], [2]. *)

Definition my_choice1: list Z
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 1 star, standard  *)

(** Suppose a verification tool [V] is developed in Coq to verify programs, and
    these programs will be compiled by compiler [G]. If a program is proved in
    Coq to have behavior [A] via [V] but turns our to have behavior [B] when
    developers compile it and run it, which statement below is correct?

    1. The verification tool [V] does not correctly formalize programs'
       behavior.

    2. The compiler [G] has a bug. *)

Definition my_choice2: Z
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

End Compiler.

(* 2021-06-09 22:50 *)
