(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2021/03/29.                                             *)
(* Due: 2021/04/02, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Assignment4.v) on CANVAS.         *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "Assignment4.vo" file is generated.         *)
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

Require Import Coq.Lists.List. Import ListNotations.
Require Import PL.Imp PL.RTClosure.
Import Abstract_Pretty_Printing.

(* ################################################################# *)
(** * Task 1: Understanding Inductive Definition *)

Module Task1.

(** Consider potential integer expression transformations defined by the
    following relation [optimize]. *)

Inductive optimize: aexp -> aexp -> Prop :=
| optimize_plus_0_l: forall a, optimize (APlus 0 a) a
| optimize_plus_0_r: forall a, optimize (APlus a 0) a
| optimize_minus_0_r: forall a, optimize (AMinus a 0) a
| optimize_mult_1_l: forall a, optimize (AMult 1 a) a
| optimize_mult_1_r: forall a, optimize (AMult a 1) a
| optimize_mult_0_l: forall a, optimize (AMult 0 a) 0
| optimize_mult_0_r: forall a, optimize (AMult a 0) 0
| optimize_congr_APlus: forall a1 a2 a3 a4,
    optimize a1 a2 ->
    optimize a3 a4 ->
    optimize (a1 + a3) (a2 + a4)
| optimize_congr_AMinus: forall a1 a2 a3 a4,
    optimize a1 a2 ->
    optimize a3 a4 ->
    optimize (a1 - a3) (a2 - a4)
| optimize_congr_AMult: forall a1 a2 a3 a4,
    optimize a1 a2 ->
    optimize a3 a4 ->
    optimize (a1 * a3) (a2 * a4)
| optimize_refl: forall a,
    optimize a a
| optimize_trans: forall a1 a2 a3,
    optimize a1 a2 ->
    optimize a2 a3 ->
    optimize a1 a3
.

(** We call this relation [optimize] since it represents some kind of constant
    related optimization. You first task is to prove some of its instances. *)

(** **** Exercise: 1 star, standard: (optimize_sample1) *)

Example optimize_sample1: forall X Y: var,
  optimize (X + 0 * Y) X.
Proof.
  intros.
  eapply optimize_trans.
  2: apply optimize_plus_0_r.
  apply optimize_congr_APlus.
  + apply optimize_refl.
  + apply optimize_mult_0_l.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard: (optimize_sample2) *)

Example optimize_sample2: forall X Y: var,
  optimize ((0 * X) * 1) 0.
Proof.
  intros.
  eapply optimize_trans.
  2: apply optimize_mult_0_l.
  apply optimize_congr_AMult.
  + apply optimize_mult_0_l.
  + apply optimize_refl.
Qed.
(** [] *)

(** The next task for you is to prove [optimize] sound. Hint: you may need to
    use some properties about expression equivalence. You can use Coq's [Search]
    command to find those we have proved. For example, you can try

    [[
         Search APlus aexp_equiv.
    ]]
*)

(** **** Exercise: 3 stars, standard: (optimize_sound) *)

Theorem optimize_sound: forall a1 a2,
  optimize a1 a2 ->
  aexp_equiv a1 a2.
Proof.
  intros.
  induction H.
  + apply zero_plus_equiv.
  + apply plus_zero_equiv.
  + apply minus_zero_equiv.
  + apply one_mult_equiv.
  + apply mult_one_equiv.
  + apply zero_mult_equiv.
  + apply mult_zero_equiv.
  + apply APlus_congr.
    apply IHoptimize1.
    apply IHoptimize2.
  + apply AMinus_congr.
    apply IHoptimize1.
    apply IHoptimize2.
  + apply AMult_congr.
    apply IHoptimize1.
    apply IHoptimize2.
  + reflexivity.
  + rewrite IHoptimize1.
    rewrite IHoptimize2.
    reflexivity.
Qed.
(** [] *)

End Task1.

(* ################################################################# *)
(** * Task 2: Understanding Steps *)

Module Task2.

(** Prove the following step relations. *)

(** **** Exercise: 1 star, standard: (step_sample1) *)

Example step_sample1: forall (X: var) (st: state),
  st X = 5 ->
  astep st ((1 + X) * 2) ((1 + 5) * 2).
Proof.
  intros.
  apply AS_Mult1.
  apply AS_Plus2.
  { apply AH_num. }
  rewrite <- H.
  apply AS_Id.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard: (step_sample2) *)

Example step_sample2: forall (X: var) (st: state),
  cstep (If (0 <= (1 + 5) * 2) Then X ::= X - 1 Else Skip EndIf, st)%imp
        (If (0 <= 6 * 2) Then X ::= X - 1 Else Skip EndIf, st)%imp.
Proof.
  intros.
  apply CS_IfStep.
  apply BS_Le2.
  { apply AH_num. }
  apply AS_Mult1.
  apply AS_Plus.
Qed.
(** [] *)

End Task2.

(* ################################################################# *)
(** * Task 3: Alternative Small Step Semantics *)

Module Task3.
Local Open Scope imp.

(** Alice wrote three alternative definitions of [cstep]. Her purpose is to
    avoid administrative steps, i.e. the step from [Skip;; c] to [c]. These
    three definitions are [A1.cstep], [A2.cstep] and [A3.cstep] as follows.
    Her definitions only differ from the original [cstep] definition at the
    places of [CS_Seq]. *)

Module A1.

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st X a a',
      astep st a a' ->
      cstep (CAss X a, st) (CAss X a', st)
  | CS_Ass : forall st1 st2 X n,
      st2 X = n ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      cstep (CAss X (ANum n), st1) (Skip, st2)
  | CS_SeqStep : forall st c1 c1' st' c2,
      cstep (c1, st) (c1', st') ->
      cstep (c1 ;; c2 , st) (c1' ;; c2, st')
  | CS_Seq : forall st c2 st' c2',
      cstep (c2, st) (Skip ;; c2', st') ->
      cstep (c2, st) (c2', st')   (* <- This is different. *)
  | CS_IfStep : forall st b b' c1 c2,
      bstep st b b' ->
      cstep
        (If b  Then c1 Else c2 EndIf, st)
        (If b'  Then c1 Else c2 EndIf, st)
  | CS_IfTrue : forall st c1 c2,
      cstep (If BTrue Then c1 Else c2 EndIf, st) (c1, st)
  | CS_IfFalse : forall st c1 c2,
      cstep (If BFalse Then c1 Else c2 EndIf, st) (c2, st)
  | CS_While : forall st b c,
      cstep
        (While b Do c EndWhile, st)
        (If b Then (c;; While b Do c EndWhile) Else Skip EndIf, st).

End A1.

Module A2.

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st X a a',
      astep st a a' ->
      cstep (CAss X a, st) (CAss X a', st)
  | CS_Ass : forall st1 st2 X n,
      st2 X = n ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      cstep (CAss X (ANum n), st1) (Skip, st2)
  | CS_SeqStep : forall st c1 c1' st' c2,
      cstep (c1, st) (c1', st') ->
      cstep (c1 ;; c2 , st) (c1' ;; c2, st')
  | CS_Seq : forall st c2 st' c2',
      cstep (c2, st) (c2', st') ->
      cstep (Skip ;; c2, st) (c2', st')   (* <- This is different. *)
  | CS_IfStep : forall st b b' c1 c2,
      bstep st b b' ->
      cstep
        (If b  Then c1 Else c2 EndIf, st)
        (If b'  Then c1 Else c2 EndIf, st)
  | CS_IfTrue : forall st c1 c2,
      cstep (If BTrue Then c1 Else c2 EndIf, st) (c1, st)
  | CS_IfFalse : forall st c1 c2,
      cstep (If BFalse Then c1 Else c2 EndIf, st) (c2, st)
  | CS_While : forall st b c,
      cstep
        (While b Do c EndWhile, st)
        (If b Then (c;; While b Do c EndWhile) Else Skip EndIf, st).

End A2.

Module A3.

Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st X a a',
      astep st a a' ->
      cstep (CAss X a, st) (CAss X a', st)
  | CS_Ass : forall st1 st2 X n,
      st2 X = n ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      cstep (CAss X (ANum n), st1) (Skip, st2)
  | CS_SeqStep : forall st c1 c1' st' c2,
      cstep (c1, st) (c1', st') ->
      cstep (c1 ;; c2 , st) (c1' ;; c2, st')
  | CS_Seq : forall st c1 c2 st' c2',
      remove_skip c1 = CSkip ->
      cstep (c2, st) (c2', st') ->
      cstep (c1 ;; c2, st) (c2', st')   (* <- This is different. *)
  | CS_IfStep : forall st b b' c1 c2,
      bstep st b b' ->
      cstep
        (If b  Then c1 Else c2 EndIf, st)
        (If b'  Then c1 Else c2 EndIf, st)
  | CS_IfTrue : forall st c1 c2,
      cstep (If BTrue Then c1 Else c2 EndIf, st) (c1, st)
  | CS_IfFalse : forall st c1 c2,
      cstep (If BFalse Then c1 Else c2 EndIf, st) (c2, st)
  | CS_While : forall st b c,
      cstep
        (While b Do c EndWhile, st)
        (If b Then (c;; While b Do c EndWhile) Else Skip EndIf, st).

End A3.

(** But she is not sure, on what extent these [cstep] are well-defined
    semantics. Your task is to give her an answer using the following
    examples. *)

(** **** Exercise: 2 stars, standard *)

(** Which alternative semantics define a program execution process as follows?

    - 1. [A1.cstep]

    - 2. [A2.cstep]

    - 3. [A3.cstep]

    The execution process:

    [[
        Skip;; Y ::= X, st -->
        Y ::= 1, st
    ]]

    where [st X = 1].

    Remark: Your answer should be an ascending list of integers (which can be
    an empty list, a list with singleton element, or a list with more than one
    element, e.g. [], [1;3], [2], [1;2;3]). *)

Definition my_choice1: list Z := [2; 3].
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 2 stars, standard *)

(** Which alternative semantics define a program execution process as follows?

    - 1. [A1.cstep]

    - 2. [A2.cstep]

    - 3. [A3.cstep]

    The execution process:

    [[
        (Y ::= 1;; Skip);; X ::= 0, st -->
        (Skip;; Skip);; X ::= 0, st' -->
        Skip, st'' -->
    ]]

    where [st X = st' X = 1], [st' Y = st'' Y = 1] and all other variables on
    [st], [st'], [st''] have value [0].

    Remark: Your answer should be an ascending list of integers. *)

Definition my_choice2: list Z := [3].
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 2 stars, standard *)

(** Which alternative semantics define a program execution process as follows?

    - 1. [A1.cstep]

    - 2. [A2.cstep]

    - 3. [A3.cstep]

    The execution process:

    [[
        (Y ::= 1;; Skip);; X ::= 0, st -->
        X ::= 0, st' -->
        Skip, st'' -->
    ]]

    where [st X = st' X = 1], [st' Y = st'' Y = 1] and all other variables on
    [st], [st'], [st''] have value [0].

    Remark: Your answer should be an ascending list of integers. *)

Definition my_choice3: list Z := [1].
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

End Task3.

(* ################################################################# *)
(** * Task 4: Understanding Simulation *)

Module Task4.
Import Task3.
Local Open Scope imp.

(** In this task, you need to prove a simulation between our original small step
    semantics [cstep] and Alice's third alternative [A3.cstep] (which is defined
    by [A3.CS_AssStep], [A3.CS_Ass], etc.). *)

Inductive match_com: com -> com -> Prop :=
| MatRefl: forall c, match_com c c
| MatSkipSeq: forall c1_1 c1_2 c2_2,
    remove_skip c1_1 = CSkip ->
    match_com c1_2 c2_2 ->
    match_com (c1_1 ;; c1_2) c2_2
| MatSeq: forall c1_1 c1_2 c2_1,
    match_com c1_1 c2_1 ->
    match_com (c1_1 ;; c1_2) (c2_1 ;; c1_2).

Definition A3cstep_or_not (X Y: com * state): Prop :=
  X = Y \/ A3.cstep X Y.

(** We provide the definition of [match_com] for you. The idea is, if
    [match_com c1 c2], then [c1] has more [Skip] on the left than [c2]. Thus, 
    [c1]'s execution via [A3.cstep] can eliminate those left-side skip in one
    step in the future, and simulate [c2]'s execution via [cstep], i.e.

    [[
        forall c1 c2 c2' st st',
          match_com c1 c2 ->
          cstep (c2, st) (c2', st') ->
          exists c1',
            match_com c1' c2' /\
            A3cstep_or_not (c1, st) (c1', st').
    ]]

    The following auxiliary lemma may be help! Prove it first. *)

(** **** Exercise: 2 stars, standard *)

Lemma match_com_skip_spec: forall c,
  match_com c Skip ->
  remove_skip c = Skip.
Proof.
  assert (forall c1 c2, match_com c1 c2 -> c2 = Skip -> remove_skip c1 = Skip).
  2: { intros; eapply H; eauto. }
  intros.
  induction H; simpl.
  + rewrite H0.
    reflexivity.
  + rewrite H.
    apply IHmatch_com.
    rewrite H0.
    reflexivity.
  + discriminate H0.
Qed.

(** **** Exercise: 4 stars, standard, optional *)

(** In order to prove the simulation property, you must be careful when choosing
    your proof strategy. There are mainly three candidates:

      - by induction over the proof of [match_com c1 c2],

      - by induction over the proof of [cstep (c2, st) (c2', st')],

      - by induction over the structure of [c1] (or [c2], [c2']).

    Make sure to find a good one before start typing your Coq proofs.

    Remark: this is an optional task, you do not lose points if you cannot solve
    it but you will get additional points if you complete it. *)

Theorem cstep_simulate_cstep: forall c1 c2 c2' st st',
  match_com c1 c2 ->
  cstep (c2, st) (c2', st') ->
  exists c1',
    match_com c1' c2' /\ A3cstep_or_not (c1, st) (c1', st').
Proof.
(* FILL IN HERE *) Admitted.
  
End Task4.

(* 2021-03-29 18:48 *)
