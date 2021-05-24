(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2021/05/08.                                             *)
(* Due: 2021/05/12, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Assignment7.v) on CANVAS.         *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "Assignment7.vo" file is generated.         *)
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

Require Import PL.Imp PL.ImpCF PL.RTClosure.
Require Import Coq.Lists.List.
Local Open Scope imp.
Import Abstract_Pretty_Printing.

(* ################################################################# *)
(** * Task 1: Control flow --- denotations *)

(** When we write real programs, we do not write break/continue outside loops.
    We can formalize this property as follows. *)

Fixpoint legal (c: com): Prop :=
  match c with
  | CSkip => True
  | CAss _ _ => True
  | CSeq c1 c2 => legal c1 /\ legal c2
  | CIf _ c1 c2 => legal c1 /\ legal c2
  | CWhile _ _ => True
  | CBreak => False
  | CCont => False
  end.

(** For example, the following sample program 1 is legal but the following
    sample program 2 is not. *)

Definition sample_com_1 (X: var): com :=
  CSeq
    (CAss X 10)
    (CWhile
       (BTrue)
       (CSeq
          (CAss X (X - 1))
          (CIf (0 <= X) CSkip CBreak))).

Definition sample_com_2 (X: var): com :=
  CSeq
    (CAss X 10)
    (CSeq
      (CWhile
        (0 <= X)
        (CAss X (X - 1)))
      CCont).

(** **** Exercise: 1 star, standard *)
Fact sample_com_1_legal: forall X, legal (sample_com_1 X).
Proof.
  intros.
  simpl.
  tauto.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard *)
Fact sample_com_2_legal: forall X, ~ legal (sample_com_2 X).
Proof.
  intros.
  simpl.
  tauto.
Qed.
(** [] *)

(** This definition of [legal] is syntactic. We can also define its semantic
    counterpart using denotational semantics. *)

Definition sem_legal (c: com): Prop :=
  BinRel.equiv (BreakExit (ceval c)) (BinRel.empty) /\
  BinRel.equiv (ContExit (ceval c)) (BinRel.empty).

(** Now, your task is to prove that: if a program is syntactically [legal] then
    it must be semantically legal, i.e. it satisfies [sem_legal]. Here,
    [BinRel_concat_empty] are auxiliary lemmas for proving [legal_sem_legal]. *)

(** **** Exercise: 2 stars, standard (BinRel_concat_empty) *)
Lemma BinRel_concat_empty: forall {A B C} (R: A -> B -> Prop),
  BinRel.equiv (BinRel.concat R (@BinRel.empty B C)) BinRel.empty.
Proof.
  intros.
  unfold BinRel.equiv, BinRel.concat, BinRel.empty.
  intros; split; intros.
  + destruct H as [? [? ?]].
    exact H0.
  + contradiction.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (BinRel_union_empty) *)
Lemma BinRel_union_empty: forall {A B} (R: A -> B -> Prop),
  BinRel.equiv (BinRel.union R BinRel.empty) R.
Proof.
  intros.
  unfold BinRel.equiv, BinRel.union, BinRel.empty.
  intros; split; intros.
  + destruct H.
    - exact H.
    - contradiction.
  + left.
    exact H.
Qed.
(** [] *)

(** Hint: remember that [rewrite] can be used for [BinRel.equiv] and may
    significantly simplify your proof for [legal_sem_legal]. *)

(** **** Exercise: 3 stars, standard (legal_sem_legal) *)
Lemma legal_sem_legal: forall c,
  legal c -> sem_legal c.
Proof.
  intros.
  induction c; unfold sem_legal; simpl.
  + split; reflexivity.
  + split; reflexivity.
  + destruct H.
    specialize (IHc1 H).
    specialize (IHc2 H0).
    clear H H0.
    unfold sem_legal in IHc1, IHc2.
    destruct IHc1, IHc2.
    rewrite H, H0, H1, H2.
    split;
    rewrite BinRel_concat_empty, BinRel_union_empty;
    reflexivity.
  + destruct H.
    specialize (IHc1 H).
    specialize (IHc2 H0).
    clear H H0.
    unfold sem_legal in IHc1, IHc2.
    destruct IHc1, IHc2.
    rewrite H, H0, H1, H2.
    unfold BinRel.test_rel, Sets.complement.
    split;
    rewrite BinRel_concat_empty, BinRel_concat_empty, BinRel_union_empty;
    reflexivity.
  + split; reflexivity.
  + destruct H.
  + destruct H.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard *)

(** Is it true that every semantically legal command is also syntactically 
    legal? 1. Yes. 2. No. *)

Definition my_choice: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(* ################################################################# *)
(** * Task 2: Control flow --- steps *)

(** We learnt two small step semantics for programs with break/continue. We
    investigate an alternative definition of control-stack-based semantics. *)

Module S0.

(** We first define stack-irrelevant step relation: [si_cstep]. *)

Inductive si_cstep: (com * state) -> (com * state) -> Prop :=
  | CS_AssStep : forall st X a a',
      astep st a a' ->
      si_cstep (CAss X a, st) (CAss X a', st)
  | CS_Ass : forall st1 st2 X n,
      st2 X = n ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      si_cstep (CAss X (ANum n), st1) (CSkip, st2)
  | CS_SeqStep : forall st c1 c1' st' c2,
      si_cstep (c1, st) (c1', st') ->
      si_cstep (CSeq c1 c2 , st) (CSeq c1' c2, st')
  | CS_Seq : forall st c2,
      si_cstep (CSeq CSkip c2, st) (c2, st)
  | CS_IfStep : forall st b b' c1 c2,
      bstep st b b' ->
      si_cstep
        (CIf b c1 c2, st)
        (CIf b' c1 c2, st)
  | CS_IfTrue : forall st c1 c2,
      si_cstep (CIf BTrue c1 c2, st) (c1, st)
  | CS_IfFalse : forall st c1 c2,
      si_cstep (CIf BFalse c1 c2, st) (c2, st).

(** We then define a new [cstep]. A step is either a stack-irrelevant step, or
    some stack related step. *)

Inductive cstep : (com * cstack * state) -> (com * cstack * state) -> Prop :=
  | CS_SIStep : forall s st c st' c',   (* <--- stack-irrelevant step *)
      si_cstep (c, st) (c', st') ->
      cstep (c, s, st) (c', s, st')
  | CS_While : forall st s c b c1 c2,   (* <--- enter a loop *)
      start_with_loop c b c1 c2 ->
      cstep
        (c, s, st)
        (CIf b c1 CBreak, (b, c1, c2) :: s, st)
  | CS_Skip : forall st s b c1 c2,      (* <--- end of loop body *)
      cstep
        (CSkip, (b, c1, c2) :: s, st)
        (CIf b c1 CBreak, (b, c1, c2) :: s, st)
  | CS_Break : forall st s b c1 c2 c,   (* <--- break *)
      start_with_break c ->
      cstep
        (c, (b, c1, c2) :: s, st)
        (c2, s, st)
  | CS_Cont : forall st s b c1 c2 c,    (* <--- continue *)
      start_with_cont c ->
      cstep
        (c, (b, c1, c2) :: s, st)
        (CIf b c1 CBreak, (b, c1, c2) :: s, st)
.

End S0.

(** This task is to prove that our new small step semantics is the same as the
    original one. You only need to prove one direction. Hint: you can use
    [induction_cstep] to apply induction proof on [S0.si_cstep] or [S0.cstep]. *)

(** **** Exercise: 2 stars, standard (si_cstep_cstep) *)
Lemma si_cstep_cstep: forall s c st c' st',
  S0.si_cstep (c, st) (c', st') ->
  cstep (c, s, st) (c', s, st').
Proof.
  intros.
  induction_cstep H;
  constructor;
  try tauto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (S0_cstep_cstep) *)
Lemma S0_cstep_cstep: forall c s st c' s' st',
  S0.cstep (c, s, st) (c', s', st') ->
  cstep (c, s, st) (c', s', st').
Proof.
  intros.
  induction_cstep H;
  [ apply si_cstep_cstep | constructor.. ];
  try tauto.
Qed.
(** [] *)

(* ################################################################# *)
(** * Task 3: Control flow --- Hoare logic *)

Module Task3.

(** In this task, we also consider the programming language in our lecture about
    control flows. In other words, there is no run time error. *)

(** **** Exercise: 1 star, standard *)

(** Can we prove the following Hoare triple, using the Hoare logic for control
    flow programs? Suppose the logic for assertion derivation is sound and
    complete. 1. Yes. 2. No.

       {{ {[ X ]} = n }}
          X ::= X - 1
       {{ {[ X ]} = n - 1 }}
       {{ False }}
       {{ {[ X ]} = n - 1 }}
*)

Definition my_choice1: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Is the following statement true? Suppose [c] is an arbitrary program with
    possibly control flow commands involved and [b] is a boolean expression.
    [
       {{ P }}
          If b Then (c ;; While b Do c EndWhile) Else Skip EndIf
       {{ Q }}
       {{ QB }}
       {{ QC }}
    ]
    if and only if
    [
       {{ P }}
          While b Do c EndWhile
       {{ Q }}
       {{ QB }}
       {{ QC }}
    ].
    
    1. Yes. 2. No.
*)

Definition my_choice2: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Is the following statement true? Suppose [c] is an arbitrary program with
    possibly control flow commands involved and [b] is a boolean expression.
    [
       {{ P }}
          While b Do c EndWhile
       {{ Q }}
       {{ QB }}
       {{ QC }}
    ]
    if and only if
    [
       {{ P }}
          While b Do c EndWhile
       {{ Q }}
       {{ False }}
       {{ False }}
    ]
    
    1. Yes. 2. No.
*)

Definition my_choice3: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

End Task3.

(* ################################################################# *)
(** * Task 4: Control flow --- loops *)

Module Task4.

(** In this task, we also consider the programming language in our lecture about
    control flows. In other words, there is no run time error. *)

(** **** Exercise: 1 star, standard *)

(** Is the following statement true? If [c] is an arbitrary program with
    possibly control flow commands involved and [b] is a boolean expression,
    then the components in
    [[
       ceval (While b Do c EndWhile)
    ]]
    are equivalent to corresponding components in
    [[
       ceval (While (0 == 0) Do If b Then c Else Break EndIf EndWhile).
    ]]
    
    1. Yes. 2. No.
*)

Definition my_choice1: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Is the following statement true? Suppose [c] is an arbitrary program with
    possibly control flow commands involved and [b] is a boolean expression.
    For any [st], [c'], [s'], [st'],
    [[
       clos_refl_trans cstep
         (While b Do c EndWhile, nil, st)
         (c', s', st')
    ]]
    if and only if
    [[
       clos_refl_trans cstep
         (While (0 == 0) Do If b Then c Else Break EndIf EndWhile, nil, st)
         (c', s', st')
    ]]
    Here, we use the small step semantics with control stack.

    1. Yes. 2. No.
*)

Definition my_choice2: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

End Task4.

(* ################################################################# *)
(** * Task 5: Diamond operator *)

Module Task5.

Local Open Scope Z.

(** Consider the following sample relations and sample sets. Please point out
    the results of [BinRel.dia]. *)

Definition relation_sample_1: Z -> Z -> Prop :=
  fun n m => n + 1 = m.

Definition relation_sample_2: Z -> Z -> Prop :=
  fun n m => n + 1 = m \/ n + 2 = m.

Definition set_sample_1: Z -> Prop :=
  fun n => exists m, n = m * 2.

Definition set_sample_2: Z -> Prop :=
  fun n => exists m, n = m * 3.

(** **** Exercise: 1 star, standard *)

(** Question 1: which of the following sets equals to

      [[  BinRel.dia relation_sample_1 set_sample_1?  ]]

    1. All even numbers.
    2. All odd numbers.
    3. All integers. *)

Definition my_choice1: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Question 2: which of the following sets equals to

      [[  BinRel.dia relation_sample_2 set_sample_1?  ]]

    1. All even numbers.
    2. All odd numbers.
    3. All integers. *)

Definition my_choice2: Z := 3.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Question 3: which of the following sets equals to

      [[  BinRel.dia relation_sample_2 set_sample_2?  ]]

    1. All integers in [set_sample_2].
    2. All integers outside [set_sample_2].
    3. All integers. *)

Definition my_choice3: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

End Task5.

(* ################################################################# *)
(** * Task 6: Integer expressions with division *)

Module Task6.

(** Consider expression evaluation when divisions are involved. *)

(** **** Exercise: 1 star, standard *)

(** Is the following statement correct?

    - When [st (X) = 1], evaluating [X / (X - 1)] on [st] ends in an error.

    1. Yes. 2. No. *)

Definition my_choice1: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Is the following statement correct?

    - When [st (X) = 1] and [st (Y) = -1], evaluating [(X + Y) / (X - 1)] on
      [st] ends in an error.

    1. Yes. 2. No. *)

Definition my_choice2: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Is the following statement correct?

    - When [st (X) = 1], evaluating [ (! (X == 0)) && (X / (X - 1) <= 10) ] on
      [st] ends in an error.

    1. Yes. 2. No. *)

Definition my_choice3: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Is the following statement correct?

    - When [st (X) = 1], evaluating [(2 <= X) && (X / (X - 1) <= 10) ] on [st]
      ends in an error.

    1. Yes. 2. No. *)

Definition my_choice4: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

End Task6.

(* 2021-05-08 18:58 *)
