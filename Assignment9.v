(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2021/05/24.                                             *)
(* Due: 2021/05/28, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Assignment9.v) on CANVAS.         *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "Assignment9.vo" file is generated.         *)
(*                                                                   *)
(* 5. Do not copy and paste others' answer.                          *)
(*                                                                   *)
(* 6. Using any theorems and/or tactics provided by Coq's standard   *)
(*    library is allowed in this assignment, if not specified.       *)
(*                                                                   *)
(* 7. When you finish, answer the following question:                *)
(*                                                                   *)
(*      Who did you discuss with when finishing this                 *)
(*      assignment? Your answer to this question will                *)
(*      NOT affect your grade.                                       *)
(*      (* FILL IN YOUR ANSWER HERE AS COMMENT *)                    *)
(*                                                                   *)
(* ***************************************************************** *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import PL.RTClosure.
Require Import PL.Lambda.
Import LambdaIB.
Local Open Scope Z.
Local Open Scope string.
Notation "[ x ; .. ; y ]" := (@cons tm x .. (@cons tm y (@nil tm)) ..).

(* ################################################################# *)
(** * Lambda Expressions *)

(** **** Exercise: 2 stars, standard *)

(** Please describe the evaluation process of

    - [app
         (app
            (abs "f" (abs "x" (app "f" "x")))
            (abs "x" (app (app Omult "x") "x")))
         2].

    If writing this expression in python, it is:

    - [(lambda f: lambda x: f (x)) (lambda x: x * x) (2)].

    Remark: your answer should be a list of lambda expressions, the first of
    which is the original expression and the last of which is the evaluation
    result. This list should describe the evaluation step by step.
*)

Definition process_1: list tm
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Now you know the evaluation result is 4. Please prove it in Coq. *)

Example result_1:
  clos_refl_trans step
    (app
       (app (abs "f" (abs "x" (app "f" "x")))
            (abs "x" (app (app Omult "x") "x")))
       2)
    4.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard *)

(** We usually call [ abs "f" (abs "x" (app "f" "x")) ] the "apply" function. In
    other words, it APPLIES function "f" on "x". Please prove that it is
    well-typed. *)

Example type_1: forall T1 T2: ty,
  empty_context |-
    (abs "f" (abs "x" (app "f" "x"))) \in ((T1 ~> T2) ~> T1 ~> T2).
Proof.
(* FILL IN HERE *) Admitted.

(** **** Exercise: 2 stars, standard *)

(** Please describe the evaluation process of

    - [app
         (abs "x"
            (app (app (app Oifthenelse (app (app Oeq "x") 0)) 0) 1))
         2].

    If writing this expression in Coq, it is like:

    - [ (fun x => if x ?= 0 then 0 else 1) 2 ].

*)

Definition process_2: list tm
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard *)

(** In the example above, the function

    - [ abs "x" (app (app (app Oifthenelse (app (app Oeq "x") 0)) 0) 1) ]

    is usually called the "test_zero" function. If it applies to zero, the
    result is zero. If it applies to non-zero, the result is one. Of course,
    it has type [TInt ~> TInt]. But, if you write it in a wrong way, you can
    easily make it ill-typed. For example, the following expression writes:
    if "x" is non-zero, return false instead of one. This must cause a chaos
    in types.

    Hint: in order to prove the following property, you need to use [inversion]
    to trace back through the type derivation. You may use

    - [deduce_types_from_head]

    to speed up. But it will only solve parts, but not all, of the problem. *)

Lemma ill_typed_example: forall Gamma T,
  Gamma |-
    abs "x" (app (app (app Oifthenelse (app (app Oeq "x") 0)) 0) false) \in T ->
  False.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 1 star, standard *)

(** It is a nice property that the small step semantics of lambda expressions
    (as we introduced in lectures) are type safe. In other words, for any
    [t: tm] and [T: ty], if

    - [empty_context |- t \in T]

    then evaluating [t] must be safe. But, is the reverse direction also true?
    In other words, is there such an expression [t] that evaluating [t] is safe
    but no type [T] makes [empty_context |- t \in T] true.

    1. There exists such [t].

    2. There does not exist such [t]. *)

Definition my_choice: Z
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** You should start your proof with either one of the following:

    - [ left; split; [reflexivity |] ]

    - [ right; reflexivity ]

*)

Lemma reverse_of_type_safe:
  (my_choice = 1 /\
   exists t t', clos_refl_trans step t t' /\ tm_halt t' /\
                (forall T, empty_context |- t \in T -> False)) \/
  (my_choice = 2).
Proof.
(* FILL IN HERE *) Admitted.

(* 2021-05-24 21:19 *)
