(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2021/03/08.                                             *)
(* Due: 2021/03/12, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Assignment2.v) on CANVAS.         *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "Assignment2.vo" file is generated.         *)
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

Require Import PL.Imp.
Import Assertion_S.
Import Assertion_S_Tac.
Import Assertion_S_Rules.
Import Concrete_Pretty_Printing.

(* ################################################################# *)
(** * Task 1: Loops and Loop Invariants *)

(** **** Exercise: 1 star, standard *)
Module Task1_1.

(** Is the following Hoare triple provable in our Hoare logic?

    {{ {[ X ]} = 0 }}
      While (! (10 < X)) Do
        X ::= X + 1
      EndWhile
    {{ {[ X ]} = 10 }}

Is it possible to prove it using the following loop invariant?

    {[ X ]} <= 10

1. It is possible to prove the triple with the loop invariant above.

2. The triple is provable but using the loop invariant above is not correct.

3. The triple is not provable.
*)

Definition the_correct_statement_above := 3.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)

End Task1_1.
(** [] *)

(** **** Exercise: 1 star, standard *)
Module Task1_2.

(** Is the following Hoare triple provable in our Hoare logic?

    {{ True }}
      While true Do
        Skip
      EndWhile
    {{ True }}

Is it possible to prove it using loop invariant [False]? 

1. It is possible to prove the triple with loop invariant [False].

2. The triple is provable but using loop invariant [False] is not correct.

3. The triple is not provable.
*)

Definition the_correct_statement_above := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)

End Task1_2.
(** [] *)

(** **** Exercise: 1 star, standard *)
Module Task1_3.

(** Is the following Hoare triple provable in our Hoare logic?

    {{ {[ Y ]} = 1 }}
      While Y <= X Do
        Y ::= Y * 2
      EndWhile
    {{ {[ X ]} < {[ Y ]} AND {[ Y ]} <= 2 * {[ X ]} }}

Is it possible to prove it using the following loop invariant?

    {[ Y ]} <= 2 * {[ X ]}

1. It is possible to prove the triple with the loop invariant above.

2. The triple is provable but using the loop invariant above is not correct.

3. The triple is not provable.
*)

Definition the_correct_statement_above := 3.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)

End Task1_3.
(** [] *)

(* ################################################################# *)
(** * Task 2: Assignment Rules *)

(** Find out the pre/postconditions of assignment commands according to
[hoare_asgn_fwd] and [hoare_asgn_bwd]. *)

Module Task2_Example.
Import Axiomatic_semantics.

Local Instance X: var := new_var().
Local Instance Y: var := new_var().
Local Instance U: var := new_var().
Local Instance V: var := new_var().

(** For the following assignment command, write down the postcondition defined
by [hoare_asgn_fwd]. (Here, [X], [Y], [U] and [V] are program variables.

    {{ {[X * Y]} == k + {[U * V]} }}
    X ::= X + Y
    {{ ??? }}
*)
Definition post (k: Z): Assertion :=
  EXISTS x, {[x * Y]} = k + {[U * V]} AND {[X]} = {[x + Y]}.

(** Hint: you can actually check whether such an answer is correct using Coq.
Here is a proof script. Remark: this is only for illustration. For your
assignment later, it is NOT necessary to write a proof. *)

Goal forall k: Z,
      {{ {[X * Y]} = k + {[U * V]} }}
      X ::= X + Y
      {{ EXISTS x, {[x * Y]} = k + {[U * V]} AND {[X]} = {[x + Y]} }}.
Proof.
  intros.
  pose proof hoare_asgn_fwd
             ({[X * Y]} = k + {[U * V]})%assert
             X
             (X + Y).
  assert_subst in H.
  exact H.
Qed.

(** Remark: you should NOT write:

  EXISTS x, x * {[Y]} = k + {[U]} * {[V]} AND {[X]} = x + {[Y]}

although you might gain this assertion using [assert_simpl]. It is NOT the
postcondition generated by [hoare_asgn_fwd]. It is only equivalent to that.
*)

End Task2_Example.

(** **** Exercise: 1 star, standard *)
Module Task2_1.
Import Axiomatic_semantics.

Local Instance A: var := new_var().
Local Instance B: var := new_var().
Local Instance C: var := new_var().

(** For the following assignment command, write down the postcondition defined
by [hoare_asgn_fwd].

    {{ 100 <= {[A + B + C]} AND {[A]} <= 0 }}
    A ::= 0
    {{ ??? }}
*)

Definition post: Assertion :=
  EXISTS a, 100 <= {[a + B + C]} AND {[a]} <= 0 AND {[A]} = {[0]}.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)

End Task2_1.
(** [] *)

(** **** Exercise: 1 star, standard *)
Module Task2_2.
Import Axiomatic_semantics.

Local Instance A: var := new_var().
Local Instance B: var := new_var().

(** For the following assignment command, write down the postcondition defined
by [hoare_asgn_fwd].

    {{ 0 <= {[A]} + {[B]} AND {[A]} * {[B]} <= 100 }}
    A ::= A + B
    {{ ??? }}
*)

Definition post: Assertion :=
  EXISTS a, 0 <= {[a]} + {[B]} AND {[a]} * {[B]} <= 100 AND {[A]} = {[a + B]}.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)

End Task2_2.
(** [] *)

(** **** Exercise: 1 star, standard *)
Module Task2_3.
Import Axiomatic_semantics.

Local Instance X: var := new_var().
Local Instance Y: var := new_var().

(** For the following assignment command, write down the postcondition defined
by [hoare_asgn_fwd].

    {{ EXISTS x, x = a AND {[Y]} = b AND {[X]} = x + b }}
    Y ::= X - Y
    {{ ??? }}
*)

Definition post (a b: Z): Assertion :=
  EXISTS y, (EXISTS x, x = a AND {[y]} = b AND {[X]} = x + b) AND {[Y]} = {[X - y]}.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)

End Task2_3.
(** [] *)

(** **** Exercise: 3 stars, standard *)
Module Task2_4.
Require Import Coq.Lists.List.
Import ListNotations.  
Import Axiomatic_semantics.

Local Instance S: var := new_var().
Local Instance T: var := new_var().

(** For the following assignment command, write down the precondition defined
by [hoare_asgn_bwd].

    {{ ??? }}
    S ::= S * T
    {{ {[S]} = 1000 AND {[T]} = 10 }}
*)

Definition pre: Assertion :=
  {[S * T]} = 1000 AND {[T]} = 10.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)

(** Reversely, consider the same assignment command, please write down the
strongest postcondition defined by [hoare_asgn_fwd]

    {{ Your_precondition [pre] }}
    S ::= S * T
    {{ ??? }}
*)

Definition post: Assertion :=
  EXISTS s, {[s * T]} = 1000 AND {[T]} = 10 AND {[S]} = {[s * T]}.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)

(** Now, if comparing the original postcondition and the strongest postcondition
that you just wrote down. Which one in the following statements is correct?

1. The original postcondition [ {[S]} = 1000 AND {[T]} = 10 ] is strictly
   stronger.

2. The original postcondition [ {[S]} = 1000 AND {[T]} = 10 ] is strictly
   weaker.

3. The original postcondition [ {[S]} = 1000 AND {[T]} = 10 ] is equivalent
   to that strongest postcondition of weakest precondition.

4. They two are not comparable. *)

Definition the_correct_statement_number := 3.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)

End Task2_4.

(** **** Exercise: 4 stars, standard *)
Module Task2_5.
Require Import Coq.Lists.List.
Import ListNotations.  
Import Axiomatic_semantics.

Local Instance X: var := new_var().
Local Instance Y: var := new_var().

(** For the following assignment command, write down the precondition defined
by [hoare_asgn_bwd].

    {{ ??? }}
    Y ::= X - Y
    {{ {[X]} = x + y AND {[Y]} = x }}
*)

Definition pre (x y: Z): Assertion :=
  {[X]} = x + y AND {[X - Y]} = x.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)

(** Reversely, consider the same assignment command, please write down the
strongest postcondition defined by [hoare_asgn_fwd]

    {{ Your_precondition [pre] }}
    Y ::= X - Y
    {{ ??? }}
*)

Definition post (x y: Z): Assertion :=
  EXISTS z, {[X]} = x + y AND {[X - z]} = x AND {[Y]} = {[X - z]}.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)

(** Now, if comparing the original postcondition and the strongest postcondition
that you just wrote down. Which one in the following statements is correct?

1. The original postcondition [ {[X]} = x + y AND {[Y]} = x ] is strictly
   stronger.

2. The original postcondition [ {[X]} = x + y AND {[Y]} = x ] is strictly
   weaker.

3. The original postcondition [ {[X]} = x + y AND {[Y]} = x ] is equivalent
   to that strongest postcondition of weakest precondition.

4. They two are not comparable. *)

Definition the_correct_statement_number := 3.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)

(** More generally, consider an arbitrary assertion [P] and an assignment
command [X ::= E] in our simple toy programming language. Let [Q] be the weakest
precondition of [P] and [X ::= E] and let [R] be the strongest postcondition of
[Q] and [X ::= E]. Which statements about [P] and [R] may be true?

1. [P] is strictly stronger than [R].

2. [P] is strictly weaker than [R].

3. [P] is equivalent to [R].

4. [P] and [R] are not comparable.

Hint: this is a multiple-choice problem. You should use a Coq ascending list to
describe your answer, e.g. [1; 2; 3; 4], [1; 3], [2]. *)

Definition the_statements_that_may_be_true := [2; 3].
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)

End Task2_5.
(** [] *)

(* ################################################################# *)
(** * Task 3: Decorated Programs *)

(** Both of the following programs calculate the minimum number of [X] and [Y].
We provide decorated programs to verify them. You are going to formalize these
proofs in Coq. Related assertion derivation has been claimed as hypotheses.
You do not need to add more hypothesis.

    min_if:
      If A <= B
      Then C ::= A
      Else C ::= B
      EndIf

    min_while:
      C ::= 0;;
      While (! (A == 0) && ! (B == 0)) Do
        A ::= A - 1;;
        B ::= B - 1;;
        C ::= C + 1
      EndWhile
*)

Module Task3.
Import Axiomatic_semantics.
Import Derived_Rules.

Local Instance A: var := new_var().
Local Instance B: var := new_var().
Local Instance C: var := new_var().

(** Here is the decorated program for [min_if]:

  /* {[A]} = a AND {[B]} = b */
  If A <= B
  Then
    /* {[A]} = a AND {[B]} = b AND {[A <= B]} */
    /* {[A]} = a AND a <= b */
    C ::= A
    /* EXISTS c, {[A]} = a AND a <= b AND {[C]} = {[A]} */
    /* {[A]} = a AND a <= b AND {[C]} = {[A]} */
    /* {[C]} = a AND a <= b OR {[C]} = b AND b < a */
  Else
    /* {[A]} = a AND {[B]} = b AND NOT {[A <= B]} */
    /* {[B]} = b AND b < a */
    C ::= B
    /* EXISTS c, {[B]} = b AND b < a AND {[C]} = {[B]} */
    /* {[B]} = b AND b < a AND {[C]} = {[B]} */
    /* {[C]} = a AND a <= b OR {[C]} = b AND b < a */
  EndIf
  /* {[C]} = a AND a <= b OR {[C]} = b AND b < a */.

And here are the derivation needed in proof. *)

Hypothesis der1_1: forall a b: Z,
  {[A]} = a AND {[B]} = b AND {[A <= B]} |-- 
  {[A]} = a AND a <= b.

Hypothesis der1_2: forall a b: Z,
  {[A]} = a AND a <= b AND {[C]} = {[A]} |--
  {[C]} = a AND a <= b OR {[C]} = b AND b < a.

Hypothesis der1_3: forall a b: Z,
  {[A]} = a AND {[B]} = b AND NOT {[A <= B]} |-- 
  {[B]} = b AND b < a.

Hypothesis der1_4: forall a b: Z,
  {[B]} = b AND b < a AND {[C]} = {[B]} |--
  {[C]} = a AND a <= b OR {[C]} = b AND b < a.

(** Now, your task is to write a formal Coq proof.  Hint: [hoare_asgn_fwd] will
be useful in this proofs.*)

(** **** Exercise: 2 stars, standard (min_if_correct) *)
Fact min_if_correct: forall a b: Z,
      {{ {[A]} = a AND {[B]} = b }}
      If A <= B
      Then C ::= A
      Else C ::= B
      EndIf
      {{ {[C]} = a AND a <= b OR {[C]} = b AND b < a }}.
Proof.
  intros.
  apply hoare_if.
  + eapply hoare_consequence.
    1: apply der1_1.
    2: apply der1_2.
    eapply hoare_consequence_post.
    - apply hoare_asgn_fwd.
    - assert_subst.
      assert_simpl.
      apply derives_refl.
  + eapply hoare_consequence.
    1: apply der1_3.
    2: apply der1_4.
    eapply hoare_consequence_post.
    - apply hoare_asgn_fwd.
    - assert_subst.
      assert_simpl.
      apply derives_refl.
Qed.
(** [] *)

(** Here is the decorated program for [min_while]:

  /* {[A]} = a AND {[B]} = b AND 0 <= a AND 0 <= b */
  /* {[A]} + {[0]} = a AND 0 <= a AND a <= b OR {[B]} + {[0]} = b AND 0 <= b AND b < a */
  C ::= 0;;
  /* {[A]} + {[C]} = a AND 0 <= a AND a <= b OR {[B]} + {[C]} = b AND 0 <= b AND b < a */
  While (! (A == 0) && ! (B == 0)) Do
    /* ({[A]} + {[C]} = a AND 0 <= a AND a <= b OR
        {[B]} + {[C]} = b AND 0 <= b AND b < a) AND
       {[! (A == 0) && ! (B == 0)]} */
    /* {[A - 1]} + {[C + 1]} = a AND 0 <= a AND a <= b OR
       {[B - 1]} + {[C + 1]} = b AND 0 <= b AND b < a */
    A ::= A - 1;;
    /* {[A]} + {[C + 1]} = a AND 0 <= a AND a <= b OR
       {[B - 1]} + {[C + 1]} = b AND 0 <= b AND b < a */
    B ::= B - 1;;
    /* {[A]} + {[C + 1]} = a AND 0 <= a AND a <= b OR
       {[B]} + {[C + 1]} = b AND 0 <= b AND b < a */
    C ::= C + 1
    /* {[A]} + {[C]} = a AND 0 <= a AND a <= b OR
       {[B]} + {[C]} = b AND 0 <= b AND b < a */
  EndWhile
  /* ({[A]} + {[C]} = a AND 0 <= a AND a <= b OR
      {[B]} + {[C]} = b AND 0 <= b AND b < a) AND
     NOT {[! (A == 0) && ! (B == 0)]} */
  /* {[C]} = a AND a <= b OR {[C]} = b AND b < a */.

And here are the derivation needed in proof. *)

Hypothesis der2_1: forall a b: Z,
  {[A]} = a AND {[B]} = b AND 0 <= a AND 0 <= b |--
  {[A]} + {[0]} = a AND 0 <= a AND a <= b OR {[B]} + {[0]} = b AND 0 <= b AND b < a.

Hypothesis der2_2: forall a b: Z,
  ({[A]} + {[C]} = a AND 0 <= a AND a <= b OR {[B]} + {[C]} = b AND 0 <= b AND b < a)
  AND {[! (A == 0) && ! (B == 0)]} |--
  {[A - 1]} + {[C + 1]} = a AND 0 <= a AND a <= b OR {[B - 1]} + {[C + 1]} = b AND 0 <= b AND b < a.

Hypothesis der2_3: forall a b: Z,
  {[A]} + {[C]} = a AND 0 <= a AND a <= b OR {[B]} + {[C]} = b AND 0 <= b AND b < a |--
  {[A]} + {[C]} = a AND 0 <= a AND a <= b OR {[B]} + {[C]} = b AND 0 <= b AND b < a.

Hypothesis der2_4: forall a b: Z,
  ({[A]} + {[C]} = a AND 0 <= a AND a <= b OR {[B]} + {[C]} = b AND 0 <= b AND b < a)
  AND NOT {[! (A == 0) && ! (B == 0)]} |--
  {[C]} = a AND a <= b OR {[C]} = b AND b < a.

(** Now, your task is to write a formal Coq proof.  Hint: [hoare_asgn_bwd] will
be useful in this proofs.*)

(** **** Exercise: 3 stars, standard (min_while_correct) *)
Fact min_while_correct: forall a b: Z,
      {{ {[A]} = a AND {[B]} = b AND 0 <= a AND 0 <= b }}
      C ::= 0;;
      While (! (A == 0) && ! (B == 0)) Do
        A ::= A - 1;;
        B ::= B - 1;;
        C ::= C + 1
      EndWhile
      {{ {[C]} = a AND a <= b OR {[C]} = b AND b < a }}.
Proof.
  intros.
  eapply hoare_consequence.
  1: { apply der2_1. }
  2: { apply der2_4. }

  apply hoare_seq with
    ({[A]} + {[C]} = a AND 0 <= a AND a <= b OR {[B]} + {[C]} = b AND 0 <= b AND b < a)%assert.
  + pose proof hoare_asgn_bwd
               ({[A]} + {[C]} = a AND 0 <= a AND a <= b OR {[B]} + {[C]} = b AND 0 <= b AND b < a)
               C
               0.
    exact H.
  + apply hoare_while.

    eapply hoare_seq.
    - eapply hoare_consequence_pre.
      apply der2_2.
      pose proof hoare_asgn_bwd
                 ({[A]} + {[C + 1]} = a AND 0 <= a AND a <= b OR
                 {[B - 1]} + {[C + 1]} = b AND 0 <= b AND b < a)
                 A
                 (A - 1).
      exact H.
    - eapply hoare_seq.
      pose proof hoare_asgn_bwd
                 ({[A]} + {[C + 1]} = a AND 0 <= a AND a <= b OR
                 {[B]} + {[C + 1]} = b AND 0 <= b AND b < a)
                 B
                 (B - 1).
      exact H.
      pose proof hoare_asgn_bwd
                 ({[A]} + {[C]} = a AND 0 <= a AND a <= b OR
                 {[B]} + {[C]} = b AND 0 <= b AND b < a)
                 C
                 (C + 1).
      exact H.
Qed.
(** [] *)

End Task3.

(* ################################################################# *)
(** * Task 4: First order logic in Coq *)

(** Remember how to reason about FOL connectives?
    - for [/\], using [destruct] (for assumptions)
                  and [split] (for conclusions)
    - for [\/], using [destruct] (for assumptions)
                  and [left]/[right] (for conclusions)
    - for [exists], using [destruct] (for assumptions)
                  and [exists] (for conclusions)
    - for [->] and [forall], using [apply]/[pose proof]/[specialize]
                  (for assumptions) and [intros] (for conclusions)
    - for [~] and [False], using [contradiction] and [pose proof classic].
*)

(** **** Exercise: 2 stars, standard (swap_assum) *)
Theorem swap_assum : forall (P Q R : Prop),
  (P -> Q -> R) -> (Q -> P -> R).
Proof.
  intros.
  specialize (H H1 H0).
  exact H.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (contrapositive) *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros.
  pose proof classic P.
  destruct H1.
  + specialize (H H1).
    contradiction.
  + exact H1.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (and_dup) *)
Theorem and_dup: forall (P: Prop),
  P <-> P /\ P.
Proof.
  intros.
  unfold iff.
  split.
  + intros.
    split.
    - exact H.
    - exact H.
  + intros.
    destruct H.
    exact H.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (and_not_or) *)
Theorem and_not_or: forall (P Q: Prop),
  ~ P /\ ~ Q -> ~ (P \/ Q).
Proof.
  intros.
  pose proof classic (P \/ Q).
  destruct H0.
  + destruct H.
    destruct H0.
    - contradiction.
    - contradiction.
  + exact H0.
Qed.
(** [] *)

(* ################################################################# *)
(** * Task 5: Hoare Logic Proofs *)

Module Task5.
Import Assertion_S.
Import Assertion_S_Tac.
Import Assertion_S_Rules.
Import Concrete_Pretty_Printing.
Import Axiomatic_semantics.
Import Derived_Rules.

Module Task5_1.
Import Axiomatic_semantics.
Import Derived_Rules.

(** **** Exercise: 3 stars, standard (tri_correct) *)

(** The following program try to find the smallest number [N] such
that [1 + 2 + 3 + .. + N > X].

    S ::= 0;;
    N ::= 0;;
    While S <= X Do
      N ::= N + 1;;
      S ::= S + N
    EndWhile.

Remember, you can always add auxiliary lemmas before start proving
the main theorem in every subtasks. But of course, these lemmas needs
to be proved. *)

Local Instance X: var := new_var().
Local Instance S: var := new_var().
Local Instance N: var := new_var().

Lemma der1_1:
  0 <= {[X]} AND {[S]} = 0 AND {[N]} = 0 |--
  {[N * (N - 1)]} = 2 * {[S - N]} AND 2 * {[S]} = {[N * (N + 1)]}
  AND {[S - N]} <= {[X]}.
Proof.
  entailer.
  intros.
  nia.
Qed.

Lemma der1_2:
  {[N * (N - 1)]} = 2 * {[S - N]} AND 2 * {[S]} = {[N * (N + 1)]}
  AND {[S - N]} <= {[X]} AND NOT {[S <= X]} |--
  {[N * (N - 1)]} <= 2 * {[X]} AND 2 * {[X]} < {[N * (N + 1)]}.
Proof.
  entailer.
  intros.
  nia.
Qed.

Lemma der1_3:
  {[N * (N - 1)]} = 2 * {[S - N]} AND 2 * {[S]} = {[N * (N + 1)]}
  AND {[S - N]} <= {[X]} AND {[S <= X]} |--
  {[(N + 1) * (N + 1 - 1)]} = 2 * {[S]} AND 2 * {[S + (N + 1)]} = {[(N + 1) * (N + 1 + 1)]}
    AND {[S]} <= {[X]}.
Proof.
  entailer.
  intros.
  nia.
Qed.

Lemma der1_4:
  {[N * (N - 1)]} = 2 * {[S]} AND 2 * {[S + N]} = {[N * (N + 1)]}
  AND {[S]} <= {[X]} |--
  {[N * (N - 1)]} = 2 * {[S + N - N]} AND 2 * {[S + N]} = {[N * (N + 1)]}
  AND {[S + N - N]} <= {[X]}.
Proof.
  entailer.
  intros.
  nia.
Qed.

Fact tri_correct:
  {{ 0 <= {[X]} }}
    S ::= 0;;
    N ::= 0;;
    While S <= X Do
      N ::= N + 1;;
      S ::= S + N
    EndWhile
  {{ {[N * (N - 1)]} <= 2 * {[X]} AND
     2 * {[X]} < {[N * (N + 1)]} }}.
Proof.
  eapply hoare_seq.
  { apply hoare_asgn_fwd. }
  assert_subst.
  assert_simpl.

  eapply hoare_seq.
  { apply hoare_asgn_fwd. }
  assert_subst.
  assert_simpl.

  eapply hoare_consequence.
  1: apply der1_1.
  2: apply der1_2.
  apply hoare_while.

  apply hoare_seq with
    ({[N * (N - 1)]} = 2 * {[S]} AND 2 * {[S + N]} = {[N * (N + 1)]}
    AND {[S]} <= {[X]})%assert.
  + eapply hoare_consequence_pre.
    - apply der1_3.
    - pose proof hoare_asgn_bwd
                 ({[N * (N - 1)]} = 2 * {[S]} AND 2 * {[S + N]} = {[N * (N + 1)]}
                 AND {[S]} <= {[X]})
                 N
                 (N + 1).
      exact H.
  + eapply hoare_consequence_pre.
    - apply der1_4.
    - pose proof hoare_asgn_bwd
                 ({[N * (N - 1)]} = 2 * {[S - N]} AND 2 * {[S]} = {[N * (N + 1)]}
                 AND {[S - N]} <= {[X]})
                 S
                 (S + N).
      exact H.
Qed.
(** [] *)

End Task5_1.

Module Task5_2.
Import Axiomatic_semantics.
Import Derived_Rules.

(** **** Exercise: 3 stars, standard (sqrt_correct) *)

(** The following program computes the integer part of [X]'s square
root.

    I ::= 0;;
    While (I + 1) * (I + 1) <= X Do
      I ::= I + 1
    EndWhile.

Your task is to prove its correctness. *)

Local Instance X: var := new_var().
Local Instance I: var := new_var().

Lemma der2_1: forall m: Z,
  0 <= {[X]} AND {[X]} = m AND {[I]} = 0 |--
  {[I]} * {[I]} <= m AND {[X]} = m.
Proof.
  intros.
  entailer.
  nia.
Qed.

Lemma der2_2: forall m: Z,
  {[I]} * {[I]} <= m AND {[X]} = m AND NOT {[(I + 1) * (I + 1) <= X]} |--
  {[I]} * {[I]} <= m AND m < ({[I]} + 1) * ({[I]} + 1).
Proof.
  intros.
  entailer.
  intros.
  nia.
Qed.

Lemma der2_3: forall m: Z,
  {[I]} * {[I]} <= m AND {[X]} = m AND {[(I + 1) * (I + 1) <= X]} |--
  {[I + 1]} * {[I + 1]} <= m AND {[X]} = m.
Proof.
  intros.
  entailer.
  intros.
  nia.
Qed.

Fact sqrt_correct: forall m: Z,
  {{ 0 <= {[X]} AND {[X]} = m }}
    I ::= 0;;
    While (I + 1) * (I + 1) <= X Do
      I ::= I + 1
    EndWhile
  {{ {[I]} * {[I]} <= m AND m < ({[I]} + 1) * ({[I]} + 1) }}.
Proof.
  intros.
  eapply hoare_seq.
  { apply hoare_asgn_fwd. }
  assert_subst.
  assert_simpl.

  eapply hoare_consequence.
  1: apply der2_1.
  2: apply der2_2.

  apply hoare_while.
  eapply hoare_consequence_pre.
  + apply der2_3.
  + pose proof hoare_asgn_bwd
               ({[I]} * {[I]} <= m AND {[X]} = m)
               I
               (I + 1).
    exact H.
Qed.
(** [] *)

End Task5_2.

End Task5.

(* ################################################################# *)
(** * Task 6: Derived Rules *)

(** In this task you need to derive more rules from primary rules. *)

Module Task6.

Import Axiomatic_semantics.
Import Derived_Rules.

(** **** Exercise: 2 stars, standard (hoare_while_single) *)
Lemma hoare_while_single: forall P Q R b c,
  P |-- Q ->
  {{ Q AND {[ b ]} }} c {{ Q }} ->
  Q AND NOT {[ b ]} |-- R ->
  {{ P }} While b Do c EndWhile {{ R }}.
Proof.
  intros.
  eapply hoare_consequence.
  1: apply H.
  2: apply H1.
  apply hoare_while.
  exact H0.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (hoare_if_then) *)
Lemma hoare_if_then: forall P Q b c,
  {{ P AND {[ b ]} }} c {{ Q }} ->
  P AND NOT {[ b ]} |-- Q ->  
  {{ P }} If b Then c Else Skip EndIf {{ Q }}.
Proof.
  intros.
  eapply hoare_consequence_post.
  + apply hoare_if.
    apply H.
    eapply hoare_consequence_post.
    - apply hoare_skip.
    - apply H0.
  + apply derives_refl.
Qed.
(** [] *)

End Task6.

(* 2021-03-08 20:56 *)
