(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2021/04/28.                                             *)
(* Due: 2021/05/07, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Quiz1.v) on CANVAS.               *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "Quiz1.vo" file is generated.               *)
(*                                                                   *)
(* 5. You should answer questions individually. You should not       *)
(*    discuss with others or try finding answers online.             *)
(*                                                                   *)
(* ***************************************************************** *)

Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import PL.RTClosure.
Require Import PL.Imp. Import Assertion_D. Import Abstract_Pretty_Printing.

(** In this assignment, we are going to establish another denotational semantics
    for our simple imperative language. This time, a program's denotation is
    defined as a ternary relation. Specifically, [st1, t, st2] belongs to the
    denotation of program [c] if and only if executing [c] from [st1] may take
    time [t] and stop at state [st2].

    We could write a more realistic definition here, but in order to make things
    simple, we assume every assignment command takes one unit of time, every
    testing (for either if-command, or loop condition testing) takes one unit of
    time and the [Skip] command does not take any time. *)

Definition skip_sem: state -> Z -> state -> Prop :=
  fun st1 t st2 =>
    st1 = st2 /\ t = 0.

Definition asgn_sem (X: var) (E: aexp): state -> Z -> state -> Prop :=
  fun st1 t st2 =>
    st2 X = aeval E st1 /\
    forall Y, X <> Y -> st1 Y = st2 Y /\
    t = 1.

Definition seq_sem (d1 d2: state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  fun st1 t st3 =>
    exists t1 t2 st2,
      d1 st1 t1 st2 /\ d2 st2 t2 st3 /\ t = t1 + t2.

Definition test_sem (X: state -> Prop): state -> Z -> state -> Prop :=
  fun st1 t st2 =>
    st1 = st2 /\ X st1 /\ t = 1.

Definition union_sem (d d': state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  fun st1 t st2 =>
    d st1 t st2 \/ d' st1 t st2.

Definition if_sem (b: bexp) (d1 d2: state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  union_sem
    (seq_sem (test_sem (beval b)) d1)
    (seq_sem (test_sem (beval (! b))) d2).

Fixpoint iter_loop_body
  (b: bexp)
  (loop_body: state -> Z -> state -> Prop)
  (n: nat)
  : state -> Z -> state -> Prop
:=
  match n with
  | O => test_sem (beval (! b))
  | S n' => seq_sem
              (test_sem (beval b))
              (seq_sem loop_body (iter_loop_body b loop_body n'))
  end.

Definition omega_union_sem (d: nat -> state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  fun st1 t st2 => exists n, d n st1 t st2.

Definition loop_sem (b: bexp) (loop_body: state -> Z -> state -> Prop)
  : state -> Z -> state -> Prop
:=
  omega_union_sem (iter_loop_body b loop_body).

Fixpoint ceval (c: com): state -> Z -> state -> Prop :=
  match c with
  | CSkip => skip_sem
  | CAss X E => asgn_sem X E
  | CSeq c1 c2 => seq_sem (ceval c1) (ceval c2)
  | CIf b c1 c2 => if_sem b (ceval c1) (ceval c2)
  | CWhile b c => loop_sem b (ceval c)
  end.

(* ################################################################# *)
(** * Task 1: The Theory Of Ternary Relations *)

Definition sem_equiv (d1 d2: state -> Z -> state -> Prop): Prop :=
  forall st1 t st2, d1 st1 t st2 <-> d2 st1 t st2.

(** You should first prove that [sem_equiv] is an equivalence relation and it
    is preserved by [seq_sem], [union_sem], [omega_union_sem]. Also, [test_sem]
    will always turn equivalent state sets into equivalent ternary relations. *)

(** **** Exercise: 1 star, standard (sem_equiv_refl) *)

Lemma sem_equiv_refl: Reflexive sem_equiv.
Proof.
  unfold Reflexive, sem_equiv.
  intros.
  reflexivity.
Qed.
(** [] *)
  
(** **** Exercise: 1 star, standard (sem_equiv_sym) *)

Lemma sem_equiv_sym: Symmetric sem_equiv.
Proof.
  unfold Symmetric, sem_equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.
(** [] *)
  
(** **** Exercise: 1 star, standard (sem_equiv_trans) *)

Lemma sem_equiv_trans: Transitive sem_equiv.
Proof.
  unfold Transitive, sem_equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (seq_sem_equiv) *)

Lemma seq_sem_equiv: Proper (sem_equiv ==> sem_equiv ==> sem_equiv) seq_sem.
Proof.
  unfold Proper, respectful.
  unfold sem_equiv, seq_sem.
  intros; split; intros.
  + destruct H1 as [t1 [t2 [st0 [? [? ?]]]]].
    exists t1, t2, st0.
    rewrite <- H, <- H0.
    tauto.
  + destruct H1 as [t1 [t2 [st0 [? [? ?]]]]].
    exists t1, t2, st0.
    rewrite H, H0.
    tauto.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (union_sem_equiv) *)

Lemma union_sem_equiv: Proper (sem_equiv ==> sem_equiv ==> sem_equiv) union_sem.
Proof.
  unfold Proper, respectful.
  unfold sem_equiv, union_sem.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (omega_union_sem_equiv) *)

Lemma omega_union_sem_equiv: forall d1 d2: nat -> state -> Z -> state -> Prop,
  (forall n: nat, sem_equiv (d1 n) (d2 n)) ->
  sem_equiv (omega_union_sem d1) (omega_union_sem d2).  
Proof.
  unfold sem_equiv, omega_union_sem.
  intros; split; intros.
  + destruct H0 as [n ?].
    exists n.
    rewrite <- H.
    exact H0.
  + destruct H0 as [n ?].
    exists n.
    rewrite H.
    exact H0.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (test_sem_equiv) *)

Lemma test_sem_equiv: Proper (Sets.equiv ==> sem_equiv) test_sem.
Proof.
  unfold Proper, respectful.
  unfold Sets.equiv, sem_equiv, test_sem.
  intros.
  rewrite H.
  reflexivity.
Qed.
(** [] *)

Existing Instances sem_equiv_refl
                   sem_equiv_sym
                   sem_equiv_trans
                   seq_sem_equiv
                   union_sem_equiv
                   test_sem_equiv.

(* ################################################################# *)
(** * Task 2: Program Equivalence Is An Equivalence *)

(** By a different program semantics, we can have a different sense of program
    equivalence. For example, the following two program were thought to be
    equivalent in class because they have the same effects: [ X ::= 0 ] vs.
    [ X ::= 1;; X ::= 0 ]. However, they take different amount of time to
    execute according to our semantic model. Thus, in some sense, they are
    not that equivalent.

    In this task, we will prove for you that our new program equivalence (see
    below) is an equivalence relation. You need to answer some questions about
    these proofs. *)

Definition com_equiv (c1 c2: com): Prop :=
  sem_equiv (ceval c1) (ceval c2).

Lemma com_equiv_refl: Reflexive com_equiv.
Proof.
  unfold Reflexive, com_equiv.
  intros.
  reflexivity.
Qed.

(** **** Exercise: 1 star, standard (com_equiv_refl_uses) *)

(** Which property/properties about [sem_equiv] does this proof use?

    1. Reflexivity, [sem_equiv_refl];

    2. Symmetry, [sem_equiv_sym];

    3. Transitivity, [sem_equiv_trans].

    Hint: this is a multiple-choice problem. You should use an ascending Coq
    list to describe your answer, e.g. [1; 2; 3; 4], [1; 3], [2]. *)

Definition com_equiv_refl_uses: list Z := [1].
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

Lemma com_equiv_sym: Symmetric com_equiv.
Proof.
  unfold Symmetric, com_equiv.
  intros.
  rewrite H.
  reflexivity.
Qed.

(** **** Exercise: 1 star, standard (com_equiv_sym_uses) *)

(** Which property/properties about [sem_equiv] does this proof use?

    1. Reflexivity, [sem_equiv_refl];

    2. Symmetry, [sem_equiv_sym];

    3. Transitivity, [sem_equiv_trans]. *)

Definition com_equiv_sym_uses: list Z := [1; 2; 3].
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

Lemma com_equiv_trans: Transitive com_equiv.
Proof.
  unfold Transitive, com_equiv.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

(** **** Exercise: 1 star, standard (com_equiv_trans_uses) *)

(** Which property/properties about [sem_equiv] does this proof use?

    1. Reflexivity, [sem_equiv_refl];

    2. Symmetry, [sem_equiv_sym];

    3. Transitivity, [sem_equiv_trans]. *)

Definition com_equiv_trans_uses: list Z := [1; 3].
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(* ################################################################# *)
(** * Task 3: Program Equivalence Is A Congruence *)

(** In this task, you need to prove that [com_equiv] is a congruence. The first
    one is done for you.*)

Lemma CSeq_congr: Proper (com_equiv ==> com_equiv ==> com_equiv) CSeq.
Proof.
  unfold Proper, respectful.
  unfold com_equiv.
  intros c1 c1' ? c2 c2' ?.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.

(** **** Exercise: 1 star, standard (CAss_congr) *)

Lemma CAss_congr: forall (X: var),
  Proper (aexp_equiv ==> com_equiv) (CAss X).
Proof.
  unfold Proper, respectful.
  unfold aexp_equiv, com_equiv.
  intros X E E' ?.
  simpl.
  unfold asgn_sem.
  intros st1 t st2.
  unfold Func.equiv in H.
  rewrite H.
  reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (CIf_congr) *)

Lemma CIf_congr:
  Proper (bexp_equiv ==> com_equiv ==> com_equiv ==> com_equiv) CIf.
Proof.
  unfold Proper, respectful.
  unfold bexp_equiv, com_equiv.
  intros b b' ? c1 c1' ? c2 c2' ?.
  simpl.
  unfold if_sem.
  simpl.
  rewrite H, H0, H1.
  reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (CWhile_congr) *)

Lemma CWhile_congr:
  Proper (bexp_equiv ==> com_equiv ==> com_equiv) CWhile.
Proof.
  unfold Proper, respectful.
  unfold bexp_equiv, com_equiv.
  intros b b' ? c c' ?.
  simpl.
  unfold loop_sem.
  apply omega_union_sem_equiv.
  intros.
  induction n; simpl.
  + rewrite H.
    reflexivity.
  + rewrite IHn, H, H0.
    reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Task 4: Assertions as sets of program states *)

(** We always define assertions as their syntax trees in course lectures. In
    fact, we could also define assertions as sets of program states. That is: *)

Definition Assertion: Type := state -> Prop.

(** And we can define logically connectives like [AND], [IMPLY] and [NOT]. *)

Definition AssnAnd (P Q: Assertion): Assertion := fun st => P st /\ Q st.

Definition AssnImpl (P Q: Assertion): Assertion := fun st => P st -> Q st.

Definition AssnNot (P: Assertion): Assertion := fun st => ~ P st.

Notation "P1 'AND' P2" := (AssnAnd P1 P2) (at level 74, left associativity).
Notation "P1 'IMPLY' P2" := (AssnImpl P1 P2) (at level 77, right associativity).
Notation "'NOT' P" := (AssnNot P) (at level 73, right associativity).

(** Now, please prove some basic properties of these connectives. Remember that
    you can use [unfold AssnAnd], [unfold AssnImpl] and  [unfold AssnNot] to
    unfold definitions. *)

(** **** Exercise: 1 star, standard (AND_comm) *)

Lemma AND_comm: forall (P Q: Assertion) (st: state),
  (P AND Q) st -> (Q AND P) st.
Proof.
  unfold AssnAnd.
  intros.
  tauto.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (AND_classic) *)

Lemma AND_classic: forall (P Q: Assertion) (st: state),
  P st -> (P AND Q) st \/ (P AND NOT Q) st.
Proof.
  unfold AssnAnd, AssnNot.
  intros.
  tauto.
Qed.
(** [] *)

(* ################################################################# *)
(** * Task 5: Hoare logic and soundness *)

(** Based on this new definition of assertions, we can still define Hoare
    triples and their validity. Notice that we choose to use the new
    denotational semantics that we defined in this file. *)

Inductive hoare_triple: Type :=
| Build_hoare_triple (P: Assertion) (c: com) (Q: Assertion).

Notation "{{ P }}  c  {{ Q }}" :=
  (Build_hoare_triple P c%imp Q) (at level 90, c at next level).

Definition valid (Tr: hoare_triple): Prop :=
  match Tr with
  | Build_hoare_triple P c Q =>
      forall st1 st2 t,
        P st1 -> ceval c st1 t st2 -> Q st2
  end.

Notation "|==  Tr" := (valid Tr) (at level 91, no associativity).

(** Prove that the sequence rule and the if rule preserves the validity defined
    above. *)

(** **** Exercise: 2 stars, standard (hoare_seq_sound) *)

Lemma hoare_seq_sound: forall P c1 Q c2 R,
  |== {{ P }} c1 {{ Q }} ->
  |== {{ Q }} c2 {{ R }} ->
  |== {{ P }} c1 ;; c2 {{ R }}.
Proof.
  unfold valid.
  intros.
  simpl in H2.
  unfold seq_sem in H2.
  destruct H2 as [t1 [t1' [st1' [? [? ?]]]]].
  specialize (H _ _ _ H1 H2).
  specialize (H0 _ _ _ H H3).
  exact H0.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (hoare_if_sound) *)

Definition AssnDenote (b: bexp): Assertion :=
  fun st => beval b st.

Notation "{[ b ]}" := (AssnDenote ((b)%vimp)) (at level 30, no associativity).

Lemma hoare_if_sound: forall P b c1 c2 Q,
  |== {{ P AND {[b]} }} c1 {{ Q }} ->
  |== {{ P AND NOT {[b]} }} c2 {{ Q }} ->
  |== {{ P }} If b Then c1 Else c2 EndIf {{ Q }}.
Proof.
  unfold valid.
  intros.
  simpl in H2.
  unfold if_sem in H2.
  unfold union_sem,
         seq_sem,
         test_sem in H2.
  destruct H2 as [H2 | H2].
  destruct H2 as [t1 [t1' [st1' [[? ?] ?]]]]; subst st1'.
  + apply H with st1 t1'.
    - unfold AssnAnd, AssnDenote.
      tauto.
    - tauto.
  + simpl in H2.
    unfold Sets.complement in H2.
    destruct H2 as [t1 [t1' [st1' [[? ?] ?]]]]; subst st1'.
    apply H0 with st1 t1'.
    - unfold AssnAnd, AssnNot, AssnDenote.
      tauto.
    - tauto.
Qed.
(** [] *)

(* ################################################################# *)
(** * Task 6: Denotations vs. Steps *)

(** In this task, you need find out the connection between our new denotational
    semantics and the small step semantics that we learnt in class. *)

(** **** Exercise: 1 star, standard *)

(** Is the following statement correct?

    - For any command [c], program states [st1], [st2], and integer [t], if
      [ceval c st1 t st2], then [multi_cstep (c, st1) (Skip, st2)].

    1: Yes. 2: No. *)

Definition my_choice61: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Is the following statement correct?

    - For any command [c1], [c2], program states [st1], [st2], [st3], and
      integer [t], if [cstep (c1, st1) (c2, st2)] and [ceval c2 st2 t st3], then
      [ceval c1 st1 t st3].

    1: Yes. 2: No. *)

Definition my_choice62: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Is the following statement correct?

    - For any command [c], program states [st1], [st2], and integer [t], if
      it takes [t] steps (according to [cstep]) getting to [ (Skip, st2) ] from
      [ (c, st1) ] and [c] contains no loop, then [ceval c st1 t st2].

    1: Yes. 2: No. *)

Definition my_choice63: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(* ################################################################# *)
(** * Task 7: The VST tool *)

(** In this task, you need to answer several questions about VST. *)

(** **** Exercise: 1 star, standard *)

(** As we learn in class, a program correctness proof (a proof of [semax_body])
    in VST is:

    - 1: a Hoare logic proof;

    - 2: a proof about C program's denotation;

    - 3: a proof about C program's small step semantics. *)

Definition my_choice71: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Suppose a C program is proved in VST satisfying a triple with precondition
    [P] and postcondition [Q], but running this C program from an initial state
    satisfying [P] may cause an undefined behavior according to C standard.
    Which statement below is correct?

    - 1. VST does not correctly formalize C language's behavior.

    - 2. VST proves that C standard is buggy.

    - 3. Nothing is wrong. *)

Definition my_choice72: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Suppose [listrep] is the representation predicate that we defined in class
    for describing linked lists. Is the following statement is provable in VST?

    [[
       forall a l p,
         listrep (a :: l) p |--
           EX q, data_at Tsh t_struct_list (Vint (Int.repr a), q) p
    ]]

    - 1. Yes.
    
    - 2. No. *)

Definition my_choice73: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(* 2021-04-28 20:03 *)
