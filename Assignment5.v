(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2021/04/12.                                             *)
(* Due: 2021/04/16, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Assignment5.v) on CANVAS.         *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "Assignment5.vo" file is generated.         *)
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

Require Import PL.Imp PL.RTClosure.

(* ################################################################# *)
(** * Task 1: Middle Step Relation *)

Module MiddleStep.
Import Abstract_Pretty_Printing.
Local Open Scope imp.

(** Between denotational semantics (also called big step semantics) and small
   step semantics, there could be other choices. The famous certified compiler
   CompCert formalizes the program semantics of C using "middle step semantics".
   Here is a similar version for [IMP]. *)

Inductive mstep : (com * state) -> (com * state) -> Prop :=
  | MS_Ass : forall st1 st2 X E,
      st2 X = aeval E st1 ->
      (forall Y, X <> Y -> st1 Y = st2 Y) ->
      mstep (CAss X E, st1) (Skip, st2)
  | MS_SeqStep : forall st c1 c1' st' c2,
      mstep (c1, st) (c1', st') ->
      mstep (c1 ;; c2 , st) (c1' ;; c2, st')
  | MS_Seq : forall st c2,
      mstep (Skip ;; c2, st) (c2, st)
  | MS_IfTrue : forall st b c1 c2,
      beval b st ->
      mstep (If b Then c1 Else c2 EndIf, st) (c1, st)
  | MS_IfFalse : forall st b c1 c2,
      ~ beval b st ->
      mstep (If b Then c1 Else c2 EndIf, st) (c2, st)
  | MS_WhileTrue : forall st b c,
      beval b st ->
      mstep
        (While b Do c EndWhile, st)
        (c;; While b Do c EndWhile, st)
  | MS_WhileFalse : forall st b c,
      ~ beval b st ->
      mstep (While b Do c EndWhile, st) (Skip, st).

Definition multi_mstep := clos_refl_trans mstep.

(** Here are some simple examples. Please prove them in Coq. *)

(** **** Exercise: 1 star, standard (mstep_example_1) *)
Example mstep_example_1: forall (st: state) (X Y: var),
  (forall X0, st X0 = 0) ->
  mstep (X ::= Y, st) (Skip, st).  
Proof.
  intros.
  apply MS_Ass.
  + unfold aeval, query_var.
    pose proof (H X).
    pose proof (H Y).
    rewrite H0, H1; tauto.
  + intros.
    reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (mstep_example_2) *)
Example mstep_example_2: forall (st1 st0: state) (X: var),
  st1 X = 1 ->
  st0 X = 0 ->
  (forall Y, X <> Y -> st1 Y = 0) ->
  (forall Y, X <> Y -> st0 Y = 0) ->
  mstep (X ::= X - 1, st1) (Skip, st0).  
Proof.
  intros.
  apply MS_Ass.
  + unfold aeval, Func.sub.
    unfold query_var, constant_func.
    rewrite H, H0; tauto.
  + intros.
    specialize H1 with Y.
    specialize H2 with Y.
    rewrite H1, H2; tauto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (mstep_example_3) *)

(** In the following example, you are going to prove a multi-step relation.
    Mainly, the program

    [[ While ! (X <= 0) Do X ::= X - 1 EndWhile ]]

    will decrease the value of [X] until it equals to zero. Here we consider a
    specialized case, where [st n] is a sequence of program states, and the
    program variable [X] has value [n] on [st n] for every integer [n].
    Obviously, starting from [st n], the program above will go through the
    following states in order:

    [[ st n, st (n-1), st (n-2), ..., st 1, st 0. ]]

    Your task is to prove this claim for the [n = 2] case. Hint: you can use
    [transitivity], [transitivity_1n], [transitivity_n1], [reflexivity] and
    other tactics for proving a [multi_mstep] relation, since it is defined
    as a reflexive transitive closure of [mstep]. *)

Example mstep_example_3: forall (st: Z -> state) (X: var),
  (forall n: Z, (st n) X = n) ->
  (forall n: Z, forall Y, X <> Y -> (st n) Y = 0) ->
  multi_mstep (While ! (X <= 0) Do X ::= X - 1 EndWhile, st 2) (Skip, st 0).  
Proof.
  intros.
  etransitivity_1n.
  {
    apply MS_WhileTrue.
    unfold beval, Sets.complement, Func.test_le.
    unfold aeval, query_var, constant_func.
    pose proof (H 2).
    rewrite H1; eauto.
  }
  etransitivity_1n.
  {
    apply MS_SeqStep, MS_Ass; eauto. 
    intros.
    unfold aeval, Func.sub, query_var, constant_func.
    pose proof (H 2).
    pose proof (H0 2 Y).
    rewrite H2, H3; eauto; simpl.
    pose proof (H0 1 Y).
    rewrite H4; eauto.
  }
  etransitivity_1n.
  {
    apply MS_Seq.
  }
  etransitivity_1n.
  {
    apply MS_WhileTrue.
    unfold beval, Sets.complement, Func.test_le.
    unfold aeval, Func.sub, query_var, constant_func.
    pose proof (H 2).
    rewrite H1; eauto; simpl.
    pose proof (H 1).
    rewrite H2; eauto.
  }
  etransitivity_1n.
  {
    apply MS_SeqStep, MS_Ass; eauto. 
    intros.
    unfold aeval, Func.sub, query_var, constant_func.
    pose proof (H 2).
    rewrite H2; eauto; simpl.
    pose proof (H 1).
    pose proof (H0 1 Y).
    rewrite H3, H4; eauto; simpl.
    pose proof (H0 0).
    rewrite H5; eauto.
  }
  etransitivity_1n.
  {
    apply MS_Seq.
  }
  etransitivity_1n.
  {
    apply MS_WhileFalse.
    unfold beval, Sets.complement, Func.test_le.
    unfold aeval, Func.sub, query_var, constant_func.
    pose proof (H 2).
    rewrite H1; eauto; simpl.
    pose proof (H 1).
    rewrite H2; eauto; simpl.
    pose proof (H 0).
    rewrite H3; eauto; lia.
  }
  unfold aeval, Func.sub, query_var, constant_func.
  pose proof (H 2).
  rewrite H1; eauto; simpl.
  pose proof (H 1).
  rewrite H2; eauto; simpl.
  reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Task 2: From Middles Steps to Small Steps *)

(** This task is to prove the first half of the semantic equivalence between
    the middle step semantics defined above and the small step semantics that we
    learnt in class. Specifically, your eventual goal is:

    [[
        Theorem Multi_MidStep_To_SmallStep: forall c st1 st2,
          multi_mstep (c, st1) (Skip, st2) ->
          multi_cstep (c, st1) (Skip, st2).
    ]]

    To prove this theorem, the main idea is to discover the relation between
    middle steps [mstep] and small steps [cstep]. It is critical to see the
    following observation: every middle step can be represented by finite small
    steps. In your proof, you can freely use the following theorems, which we
    have demostrated in class. *)

Check semantic_equiv_aexp1.

(* semantic_equiv_aexp1: forall st a n,
  aeval a st = n -> multi_astep st a (ANum n). *)

Check semantic_equiv_bexp1.

(* semantic_equiv_bexp1: forall st b,
  (beval b st -> multi_bstep st b BTrue) /\
  (~ beval b st -> multi_bstep st b BFalse). *)

Check multi_congr_CAss.

(* multi_congr_CAss: forall st X a a',
  multi_astep st a a' ->
  multi_cstep (CAss X a, st) (CAss X a', st). *)

Check multi_congr_CSeq.

(* multi_congr_CSeq: forall st1 c1 st1' c1' c2,
  multi_cstep (c1, st1) (c1', st1') ->
  multi_cstep (CSeq c1 c2, st1) (CSeq c1' c2, st1'). *)

Check multi_congr_CIf.

(* multi_congr_CIf: forall st b b' c1 c2,
  multi_bstep st b b' ->
  multi_cstep (CIf b c1 c2, st) (CIf b' c1 c2, st). *)

(** **** Exercise: 4 stars, standard (One_MidStep_To_SmallStep) *)

(** Hint: In the following lemma, [a] and [b] are pairs of program commands and
    program states. You may use tactics like [ destruct a as [c1 st1] ] so that
    a real pair is demonstrated in the proof goal. But, you are the one to
    choose between destructing them and not destructing them, depending on
    which way is more convenient for building a Coq proof. Specifically, you
    may start you proof by:

    - [intros. induction H.]

    - or [intros. destruct a, b.] *)

Lemma One_MidStep_To_SmallStep: forall a b,
  mstep a b -> multi_cstep a b.
Proof.
  intros.
  induction H.
  + etransitivity_n1.
    - apply multi_congr_CAss, semantic_equiv_aexp1.
      reflexivity.
    - apply CS_Ass; tauto.
  + etransitivity.
    - apply multi_congr_CSeq, IHmstep.
    - reflexivity.
  + etransitivity_1n.
    - apply CS_Seq.
    - reflexivity.
  + pose proof semantic_equiv_bexp1 st b.
    destruct H0.
    etransitivity.
    - apply multi_congr_CIf, H0, H.
    - etransitivity_1n; [apply CS_IfTrue | reflexivity].
  + pose proof semantic_equiv_bexp1 st b.
    destruct H0.
    etransitivity.
    - apply multi_congr_CIf, H1, H.
    - etransitivity_1n; [apply CS_IfFalse | reflexivity].
  + pose proof semantic_equiv_bexp1 st b.
    destruct H0.
    etransitivity_1n; [apply CS_While |].
    etransitivity. 
    - apply multi_congr_CIf, H0, H.
    - etransitivity_1n; [apply CS_IfTrue | reflexivity].
  + pose proof semantic_equiv_bexp1 st b.
    destruct H0.
    etransitivity_1n; [apply CS_While |].
    etransitivity. 
    - apply multi_congr_CIf, H1, H.
    - etransitivity_1n; [apply CS_IfFalse | reflexivity].
Qed.
(** [] *)

(** Now, from this conclusion above to our final target, we only need two
    properties about reflexive transitive closures. Hint: you may choose
    among [induction_1n], [induction_n1] and/or [induction] for different
    induction strategies. *)

(** **** Exercise: 2 stars, standard (rt_idempotent) *)
Theorem rt_idempotent : forall (X: Type) (R: X -> X -> Prop) (x y: X),
  clos_refl_trans (clos_refl_trans R) x y <-> clos_refl_trans R x y.
Proof.
  intros.
  split; intros.
  + induction_1n H.
    - reflexivity.
    - rewrite IHrt in H.
      exact H.
  + apply rt_step.
    exact H.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (rt_mono) *)
Theorem rt_mono : forall (X: Type) (R1 R2: X -> X -> Prop),
  (forall x y, R1 x y -> R2 x y) ->
  (forall x y, clos_refl_trans R1 x y -> clos_refl_trans R2 x y).
Proof.
  intros.
  induction_n1 H0.
  + reflexivity.
  + transitivity_n1 y.
    - exact IHrt.
    - specialize H with y y0.
      apply H, H0.
Qed.
(** [] *)

(** Here is our final target! *)

(** **** Exercise: 2 stars, standard (Multi_MidStep_To_SmallStep) *)

Theorem Multi_MidStep_To_SmallStep: forall c st1 st2,
  multi_mstep (c, st1) (Skip, st2) ->
  multi_cstep (c, st1) (Skip, st2).
Proof.
  intros.
  induction H.
  + apply One_MidStep_To_SmallStep.
    exact H.
  + reflexivity.
  + apply (rt_mono _ _ _ One_MidStep_To_SmallStep) in H.
    apply (rt_mono _ _ _ One_MidStep_To_SmallStep) in H0.
    apply rt_idempotent.
    transitivity y.
    - apply H.
    - apply H0.
Qed.
(** [] *)

(* ################################################################# *)
(** * Task 3: From Small Steps to Middle Steps *)

(** Your task here is to prove the second half of the semantic equivalence
    between [mstep] and [cstep]. Specifically, your eventual goal is:

    [[
        Theorem Multi_SmallStep_To_MidStep: forall c st1 st2,
          multi_cstep (c, st1) (Skip, st2) ->
          multi_mstep (c, st1) (Skip, st2).
    ]]

    To prove this theorem, the main idea is to establish a simulation relation
    [match_com], so that we can prove: every small step correspond to zero or
    one middle step. Here is our simulation statement: *)

Definition mstep_or_not (X Y: com * state): Prop :=
  X = Y \/ mstep X Y.

Definition Simulation01_Statement (match_com: state -> com -> com -> Prop): Prop :=
  forall c1 c2 c1' st st',
    match_com st c1 c2 ->
    cstep (c1, st) (c1', st') ->
    exists c2',
      match_com st' c1' c2' /\
      mstep_or_not (c2, st) (c2', st').

(** The main proof skeleton for [Multi_SmallStep_To_MidStep] is to find such a
    [match_com] relation, and at the same time

    - this relation is reflexive, i.e. [match_com st c c] for every [c];

    - only [Skip] can match [Skip] via [match_com], i.e. [c' = Skip] if
      [match_com st Skip c'].

    Why these conditions are enough for proving [Multi_SmallStep_To_MidStep]?
    Consider the following diagram:

    [[

                 match_com
             c ------------- c

      cstep  |               |  mstep_or_not
             v               v

             c1 ----------- c1'

      cstep  |               |  mstep_or_not
             v               v

             c2 ----------- c2'

             |               |
             .               .
             |               |
             .               .
             |               |
             v               v

             c0 ----------- c0'

    ]]

    From the initial command [c], the left side matches the right side via the
    [match_com] relation. Whenever the left side takes one step, zero or one
    step on the right can be taken so that both sides still matches. In the end,
    if [c0 = Skip], [c0'] must be [Skip] according to our assumption, which
    proves [Multi_SmallStep_To_MidStep]. Please formalize this proof strategy
    in Coq. *)

(** **** Exercise: 2 stars, standard (Multi_SmallStep_To_MidStep_strategy) *)
Theorem Multi_SmallStep_To_MidStep_strategy: forall match_com,
  Simulation01_Statement match_com ->
  (forall st c, match_com st c c) ->  
  (forall st c', match_com st Skip c' -> c' = Skip) ->
  (forall c st1 st2,
    multi_cstep (c, st1) (Skip, st2) ->
    multi_mstep (c, st1) (Skip, st2)).
Proof.
  intros ? ?.
  assert
    (forall c2,
       (forall st c2', match_com st c2 c2' -> c2' = Skip) ->  
       (forall c1 c1' st1 st2,
          match_com st1 c1 c1' ->
          multi_cstep (c1, st1) (c2, st2) ->
          multi_mstep (c1', st1) (Skip, st2))).
  2: {
    intros.
    specialize (H0 Skip H2); clear H2.
    specialize (H0 c c st1 st2 (H1 st1 c)); clear H1.
    tauto.
  }

  intros.
  revert c1' H1.
  induction_1n H2; intros.
  + specialize (H0 _ _ H1).
    rewrite H0.
    reflexivity.
  + unfold Simulation01_Statement in H.
    specialize (H _ _ _ _ _ H3 H1).
    destruct H; destruct H.
    destruct H4.
    - specialize (IHrt _ H).
      injection H4 as ? ?; subst.
      exact IHrt.
    - specialize (IHrt _ H).
      etransitivity_1n; eauto.
Qed.
(** [] *)

(** Let us find such a [match_com] and prove these properties now. This is its
    definition. *)

Inductive match_com (st: state): com -> com -> Prop :=
  | MatSkip: match_com st CSkip CSkip
  | MatAss: forall X a1 a2,
      aeval a1 st = aeval a2 st ->
      match_com st (CAss X a1) (CAss X a2)
  | MatSeq: forall c1 c2 c0,
      match_com st c1 c2 ->
      match_com st (c1;; c0) (c2;; c0)
  | MatIf: forall b1 b2 c c',
      (beval b1 st <-> beval b2 st) ->
      match_com st (If b1 Then c Else c' EndIf) (If b2 Then c Else c' EndIf)
  | MatWhile: forall b c,
      match_com st (While b Do c EndWhile) (While b Do c EndWhile)
  | MatIfWhile: forall b1 b2 c,
      (beval b1 st <-> beval b2 st) ->
      match_com st
        (If b1 Then (c;; While b2 Do c EndWhile) Else Skip EndIf)
        (While b2 Do c EndWhile).

(** Most parts of this definition is trivial. The only interesting clause is
    the [MatIfWhile] clause for while loops. The following diagram illustrates
    the intuition of [MS_WhileTrue] case:

    [[

                                     match_com
             While b Do c EndWhile ------------- While b Do c EndWhile

                        |                                 |
                 cstep  |                                 |  no step
                        |                                 |
                        v                                 v
         If b
           Then c ;; While b Do c EndWhile ----- While b Do c EndWhile
           Else Skip

                        |                                 |
                 cstep  |                                 |  no step
                        |                                 |
                        v                                 v
         If b'
           Then c ;; While b Do c EndWhile ----- While b Do c EndWhile
           Else Skip

                        |                                 |
                 cstep  |                                 |  no step
                        |                                 |
                        v                                 v
         If b''
           Then c ;; While b Do c EndWhile ----- While b Do c EndWhile
           Else Skip

                        .                                 |
                        .                                 |
                        .                                 |  no step
                        .                                 |
                        v                                 v
         If True
           Then c ;; While b Do c EndWhile ----- While b Do c EndWhile
           Else Skip

                        |                                 |
                 cstep  |                                 |  mstep
                        |                                 |
                        v                                 v

            c;; While b Do c EndWhile --------- c;; While b Do c EndWhile

    ]]
*)

(** For proving [Multi_SmallStep_To_MidStep], we first prove that [match_com] is
    reflexive. *)

(** **** Exercise: 1 star, standard (match_com_refl) *)
Lemma match_com_refl: forall st c, match_com st c c.
Proof.
  intros.
  induction c; constructor; tauto.
Qed.
(** [] *)

(** Second, only [Skip] can match [Skip] via [match_com]. *)

(** **** Exercise: 1 star, standard (only_skip_matches_skip) *)
Lemma only_skip_matches_skip:
  forall (st : state) (c' : com), match_com st Skip c' -> c' = Skip.
Proof.
  intros.
  inversion H.
  reflexivity.
Qed.
(** [] *)

(** Third, and most importantly, [match_com] is a simulation relation:

    [[ 
        Definition Simulation01_Statement match_com: Prop :=
          forall c1 c2 c1' st st',
            match_com st c1 c2 ->
            cstep (c1, st) (c1', st') ->
            exists c2',
              match_com st' c1' c2' /\
              mstep_or_not (c2, st) (c2', st').
    ]]

    We prove it by induction over the [cstep] relation, which means we need
    to complete base steps and induction steps as follow:

    [[

        (* CS_AssStep case *)
        
        forall st X a a',
          astep st a a' ->
          forall c2,
          match_com st (X ::= a) c2 ->
          exists c2',
             match_com st (X ::= a') c2' /\
             mstep_or_not (c2, st) (c2', st)

        (* CS_SeqStep case *)

        forall st st' c1_1 c1_1' c1_2,
          cstep (c1_1, st) (c1_1', st') ->
          (forall c2_1,
            match_com st c1_1 c2_1 ->
            exists c2_1' : com,
              match_com st' c1_1' c2_1' /\
              mstep_or_not (c2_1, st) (c2_1', st')) ->
          (forall c2,
            match_com st (c1_1;; c1_2) c2 ->
            exists c2',
              match_com st' (c1_1';; c1_2) c2' /\
              mstep_or_not (c2, st) (c2', st'))

    ]]
*)

(** For completing the [CS_AssStep] case, you may need the [aeval_preserve]
    property that we proved in class. *)

(** **** Exercise: 1 star, standard (MiddleStep_Simulate_SmallStep_CS_AssStep) *)
Lemma MiddleStep_Simulate_SmallStep_CS_AssStep:
  forall st X a a',
    astep st a a' ->
      forall c2,
      match_com st (X ::= a) c2 ->
      exists c2',
         match_com st (X ::= a') c2' /\
         mstep_or_not (c2, st) (c2', st).
Proof.
  intros.
  inversion H0; subst.
  exists (X ::= a2).
  split; constructor.
  + apply aeval_preserve in H.
    rewrite <- H, <- H4.
    reflexivity.
  + reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (MiddleStep_Simulate_SmallStep_CS_Ass) *)
Lemma MiddleStep_Simulate_SmallStep_CS_Ass:
  forall st1 st2 (X: var) (n: Z),
    st2 X = n ->
    (forall Y, X <> Y -> st1 Y = st2 Y) ->
    forall c2,
      match_com st1 (X ::= n) c2 ->
      exists c2',
        match_com st2 Skip c2' /\
        mstep_or_not (c2, st1) (c2', st2).
Proof.
  intros.
  inversion H1; subst.
  exists Skip.
  split; [constructor | right].
  constructor; [| exact H0].
  rewrite <- H5; reflexivity.
Qed.

(** For the [CS_SeqStep] case, you may need [mstep_or_not]'s congruence property
    for [;;]. *)

(** **** Exercise: 1 star, standard (mstep_or_not_congr_CSeq) *)
Lemma mstep_or_not_congr_CSeq: forall c1 st c1' st' c2,
  mstep_or_not (c1, st) (c1', st') ->
  mstep_or_not (c1;; c2, st) (c1';; c2, st').
Proof.
  intros.
  inversion H.
  + unfold mstep_or_not; left.
    injection H0 as ? ?.
    rewrite H0, H1.
    reflexivity.
  + unfold mstep_or_not; right.
    apply MS_SeqStep.
    exact H0.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (MiddleStep_Simulate_SmallStep_CS_SeqStep) *)
Lemma MiddleStep_Simulate_SmallStep_CS_SeqStep:
  forall st st' c1_1 c1_1' c1_2,
    cstep (c1_1, st) (c1_1', st') ->
    (forall c2_1,
      match_com st c1_1 c2_1 ->
      exists c2_1' : com,
        match_com st' c1_1' c2_1' /\
        mstep_or_not (c2_1, st) (c2_1', st')) ->
    (forall c2,
      match_com st (c1_1;; c1_2) c2 ->
      exists c2',
        match_com st' (c1_1';; c1_2) c2' /\
        mstep_or_not (c2, st) (c2', st')).
Proof.
  intros.
  inversion H1; subst.
  apply H0 in H5.
  destruct H5, H2.
  exists (x;; c1_2).
  split.
  + constructor.
    exact H2.
  + eapply mstep_or_not_congr_CSeq in H3.
    exact H3.
Qed.
(** [] *)

(** For the [CS_Seq] case, you may need [match_com]'s reflexivity, which you
    have already proved as [match_com_refl]. *)

(** **** Exercise: 1 star, standard (MiddleStep_Simulate_SmallStep_CS_Seq) *)
Lemma MiddleStep_Simulate_SmallStep_CS_Seq:
  forall st c1_2,
    forall c2,
      match_com st (Skip;; c1_2) c2 ->
      exists c2',
        match_com st c1_2 c2' /\
        mstep_or_not (c2, st) (c2', st).
Proof.
  intros.
  inversion H; subst.
  exists c1_2.
  split.
  + apply match_com_refl.
  + unfold mstep_or_not; right.
    apply only_skip_matches_skip in H3.
    rewrite H3.
    apply MS_Seq.
Qed.
(** [] *)

(** Each case of [CS_IfStep], [CS_IfTrue] and [CS_IfFalse] has two sub-cases,
    since a if-command may match another if command and may match a while-loop
    too. The diagram that illustrates [MS_WhileTrue] case's intuition may help
    (the diagram appeared right after the definition of [match_com]). *)

(** **** Exercise: 1 star, standard (MiddleStep_Simulate_SmallStep_CS_IfStep) *)
Lemma MiddleStep_Simulate_SmallStep_CS_IfStep:
  forall st b b' c1_1 c1_2,
    bstep st b b' ->
    forall c2,
      match_com st (If b Then c1_1 Else c1_2 EndIf) c2 ->
      exists c2',
        match_com st (If b' Then c1_1 Else c1_2 EndIf) c2' /\
        mstep_or_not (c2, st) (c2', st).
Proof.
  intros.
  inversion H0; subst.
  + exists (If b2 Then c1_1 Else c1_2 EndIf).
    split; constructor.
    - apply beval_preserve in H.
      rewrite <- H, <- H5.
      reflexivity.
    - reflexivity.
  + exists (While b2 Do c EndWhile).
    split; constructor.
    - apply beval_preserve in H.
      rewrite <- H, <- H5.
      reflexivity.
    - reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (MiddleStep_Simulate_SmallStep_CS_IfTrue) *)
Lemma MiddleStep_Simulate_SmallStep_CS_IfTrue:
  forall st c1_1 c1_2,
    forall c2,
      match_com st (If true Then c1_1 Else c1_2 EndIf) c2 ->
      exists c2',
        match_com st c1_1 c2' /\ mstep_or_not (c2, st) (c2', st).
Proof.
  intros.
  inversion H; subst.
  + exists c1_1.
    split.
    - apply match_com_refl.
    - unfold mstep_or_not; right.
      constructor.
      rewrite <- H4.
      constructor.
  + exists (c;; While b2 Do c EndWhile).
    split.
    - apply match_com_refl.
    - unfold mstep_or_not; right.
      constructor.
      rewrite <- H4.
      constructor.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (MiddleStep_Simulate_SmallStep_CS_IfFalse) *)
Lemma MiddleStep_Simulate_SmallStep_CS_IfFalse:
  forall st c1_1 c1_2,
    forall c2,
      match_com st (If false Then c1_1 Else c1_2 EndIf) c2 ->
      exists c2',
        match_com st c1_2 c2' /\ mstep_or_not (c2, st) (c2', st).
Proof.
  intros.
  inversion H; subst.
  + exists c1_2.
    split.
    - apply match_com_refl.
    - unfold mstep_or_not; right.
      constructor.
      rewrite <- H4.
      tauto.
  + exists (Skip).
    split.
    - apply match_com_refl.
    - unfold mstep_or_not; right.
      constructor.
      rewrite <- H4.
      tauto.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (MiddleStep_Simulate_SmallStep_CS_While) *)
Lemma MiddleStep_Simulate_SmallStep_CS_While:
  forall st b c,
    forall c2,
       match_com st (While b Do c EndWhile) c2 ->
       exists c2',
         match_com
           st
           (If b Then c;; While b Do c EndWhile Else Skip EndIf)
           c2' /\
         mstep_or_not (c2, st) (c2', st).
Proof.
  intros.
  inversion H; subst.
  exists (While b Do c EndWhile).
  split.
  + apply MatIfWhile.
    reflexivity.
  + unfold mstep_or_not; left.
    reflexivity.
Qed.
(** [] *)

(** Now, you can connects all induction steps above together. *)

(** **** Exercise: 1 star, standard (MiddleStep_Simulate_SmallStep) *)
Lemma MiddleStep_Simulate_SmallStep: Simulation01_Statement match_com.
Proof.
  unfold Simulation01_Statement.
  intros.
  revert c2 H; induction_cstep H0; intros.

  + eapply MiddleStep_Simulate_SmallStep_CS_AssStep; eauto.
  + eapply MiddleStep_Simulate_SmallStep_CS_Ass; eauto.
  + eapply MiddleStep_Simulate_SmallStep_CS_SeqStep; eauto.
  + eapply MiddleStep_Simulate_SmallStep_CS_Seq; eauto.
  + eapply MiddleStep_Simulate_SmallStep_CS_IfStep; eauto.
  + eapply MiddleStep_Simulate_SmallStep_CS_IfTrue; eauto.
  + eapply MiddleStep_Simulate_SmallStep_CS_IfFalse; eauto.
  + eapply MiddleStep_Simulate_SmallStep_CS_While; eauto.
Qed.
(** [] *)

(** ... and use [Multi_SmallStep_To_MidStep_strategy] to prove
    [Multi_SmallStep_To_MidStep]. *)

Theorem Multi_SmallStep_To_MidStep: forall c st1 st2,
  multi_cstep (c, st1) (Skip, st2) ->
  multi_mstep (c, st1) (Skip, st2).
Proof.
  intros.
  eapply Multi_SmallStep_To_MidStep_strategy.
  + apply MiddleStep_Simulate_SmallStep.
  + apply match_com_refl.
  + apply only_skip_matches_skip.
  + exact H.
Qed.
(** [] *)

End MiddleStep.

(* ################################################################# *)
(** * Task 4: Understanding Assertion Syntax Trees *)

Module Task4.

(** **** Exercise: 1 star, standard *)

(** Is the following claim correct?

    If [X], [Y] and [Z] are distinct program variables and [x] is a logical
    variable, then the subtitution result of
      [   ({[ X + Y ]} = {[Z]} + x) [X |-> x]   ]
    is
      [   {[ x + Y ]} = {[Z]} + x   ].

    1: Yes. 2: No. *)

Definition my_choice1: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Is the following claim correct?

    If [X] and [Y] are distinct program variables, [E1] and [E2] are integer
    expressions, [P] is an assertion, then 
      [   P [X |-> E1] [Y |-> E2]   ]
    and
      [   P [Y |-> E2] [X |-> E1]   ]
    are always equivalent assertions.

    1: Yes. 2: No. *)

Definition my_choice2: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Is the following claim correct?

    If [X] is a program variables, [E1] and [E2] are integer expressions, [P] is
    an assertion, then 
      [   P [X |-> E1] [X |-> E2]   ]
    and
      [   P [X |-> E1]   ]
    are always equivalent assertions.

    1: Yes. 2: No. *)

Definition my_choice3: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Is the following claim correct?

    If [X] is a program variables, [x] is a logical variable, [P] is an
    assertion, then [P] is a stronger assertion than
      [   EXISTS x, P [X |-> x]   ].

    1: Yes. 2: No. *)

Definition my_choice4: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

End Task4.

(** Task 5: Understanding Validity and Provability *)

Module Task5.

(** **** Exercise: 1 star, standard *)

(** Is the following reasoning about "valid" correct?

    BECAUSE the subtitution result of
    [    ({[X]} = m AND {[Y]} = n) [Y |-> Y - X]    ]
    is
    [    {[X]} = m AND {[Y - X]} = n    ],
    the following Hoare triple is VALID due to the backward assignment rule:
    [
          {{ {[X]} = m AND {[Y - X]} = n }}
             Y ::= Y - X
          {{ {[X]} = m AND {[Y]} = n }}.
    ]

    1: Yes. 2: No. *)

Definition my_choice1: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Is the following reasoning about "valid" correct?

    The following Hoare triple is VALID:
    [
          {{ True }}
             While X <= X Do X ::= X + 1 EndWhile
          {{ False }}.
    ]
    BECAUSE the loop will never terminate according to the denotational
    semantics [ceval].

    1: Yes. 2: No. *)

Definition my_choice2: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Is the following reasoning about "provable" correct?

    BECAUSE the ending state of [Skip] is always the same as its beginning
    state (according to the definition of [ceval]), this following Hoare triple
    is always PROVABLE:
        [    {{ P }} Skip {{ P }}.   ]

    1: Yes. 2: No. *)

Definition my_choice3: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Is the following reasoning about "valid" correct?

    Using [hoare_seq] and [hoare_asgn_bwd], we can build a Hoare logic proof for
    the following Hoare triple:
    [
          {{ {[(X + Y) - X]} = m AND {[(X + Y) - (X + Y - X)]} = n }}
             Y ::= X + Y;;
             X ::= Y - X;;
             Y ::= Y - X
          {{ {[X]} = m AND {[Y]} = n }}.
    ]
    IF our Hoare logic is complete, THEN this Hoare triple is also valid.

    1: Yes. 2: No. *)

Definition my_choice4: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

End Task5.

(* ################################################################# *)
(** * Task 6: Alternative Primary Proof Rules *)

Module Task6.
Import Assertion_D.
Import Abstract_Pretty_Printing.

(** Consider the following proof rule for if-commands:

    - If [  {{ P }} c1 {{ Q }}  ] and [  {{ P }} c2 {{ Q }}  ], then
      [  {{ P }} If b Then c1 Else c2 EndIf {{ Q }}  ].

    We may add it to our proof system. If doing that, the logic is still sound.
    Your task is to show why. Hint: remember that [ceval_CIf] describes the
    denotational semantics of if-commands. *)

(** **** Exercise: 1 star, standard (new_if_rule_sound) *)

Lemma new_if_rule_sound: forall P b c1 c2 Q,
  |== {{ P }} c1 {{ Q }} ->
  |== {{ P }} c2 {{ Q }} ->
  |== {{ P }} If b Then c1 Else c2 EndIf {{ Q }}.
Proof.
  unfold valid.
  intros.
  rewrite ceval_CIf in H2.
  unfold if_sem, BinRel.union, BinRel.concat, BinRel.test_rel in H2.
  destruct H2; destruct H2; destruct H2; destruct H2; subst; firstorder.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard *)

(** If replacing our original proof rule for if-commands [hoare_if] with this
    new proof rule in the proof system, is the logic still complete?

    1: Yes. 2: No. *)

Definition my_choice1: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 2 stars, standard *)

(** Consider the following proof rule for assignment commands:

    - If [X] is a program variable that does not appear in [E], then
      [  {{ P }} X ::= E {{ P [X |-> E] }}  ].

    Is the Hoare logic still sound if this additional rule is added to the proof
    system? (Suppose the underlying logic for assertion derivation is sound.)

    1: Yes. 2: No. *)

Definition my_choice2: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 2 stars, standard *)

(** Consider the following proof rule for assignment commands:

    - If [X] is a program variable that does not appear in [E] or [P], then
      [  {{ P }} X ::= E {{ P AND {[ X ]} = {[ E ]} }}  ].

    Is the Hoare logic still sound if this additional rule is added to the proof
    system? (Suppose the underlying logic for assertion derivation is sound.)

    1: Yes. 2: No. *)

Definition my_choice3: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

End Task6.

(* 2021-04-12 16:19 *)
