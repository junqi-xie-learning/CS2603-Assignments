(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2021/03/22.                                             *)
(* Due: 2021/03/26, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Assignment3.v) on CANVAS.         *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "Assignment3.vo" file is generated.         *)
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
Require Import Coq.micromega.Psatz.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

(* ################################################################# *)
(** * Task 1: Understanding Denotations *)

(** In this task, you will read descriptions about program states and decide
    whether the following pairs of programs states belong to corresponding
    programs' denotations. *)

(** **** Exercise: 1 star, standard *)
Module Task1_1.

(** Suppose [X] and [Y] are different program variables. If [st X = 1] and
    [st Y = 2], then does (st, st) belong to the following program's denotation?

    Y ::= X + 1

    1: Yes. 2: No. *)

Definition my_choice: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)

End Task1_1.
(** [] *)

(** **** Exercise: 1 star, standard *)
Module Task1_2.

(** Suppose [X] is a program variables. If [st1 X = 100], [st2 X = 1] and all
    other variables in [st1] and [st2] are zero, then does (st1, st2) belong to
    the following program's denotation?

    While 1 <= X Do X ::= X + 1 EndWhile

    1: Yes. 2: No. *)

Definition my_choice: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)

End Task1_2.
(** [] *)

(** **** Exercise: 1 star, standard *)
Module Task1_3.

(** Suppose [X] and [Y] are different program variables. If [st1 X = 1],
    [st1 Y = 2], [st2 X = 2], [st2 Y = 1] and all other variables in [st1] and
    [st2] are zero, then does (st1, st2) belong to the following program's
    denotation?

    Z ::= X;; X ::= Y;; Y ::= Z

    1: Yes. 2: No. *)

Definition my_choice: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)

End Task1_3.
(** [] *)

(* ################################################################# *)
(** * Task 2: Understanding Higher-Order Functions *)

(** Suppose [f] and [g] are both functions from [A] to [A]. How shall we define
    the function that applies [f] first and then applies [g]? *)

(** **** Exercise: 2 stars, standard (compose) *)

Definition compose {A: Type} (f g: A -> A): A -> A :=
  fun a => g (f a).
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)

(** It is obvious that [ compose f (compose g h) ] is equivalent with
    [ compose (compose f g) h ]. Your task is to prove it in Coq. *)

Theorem compose_assoc: forall f g h: Z -> Z,
  Func.equiv (compose f (compose g h)) (compose (compose f g) h).
Proof.
  intros.
  unfold Func.equiv, compose.
  intros.
  reflexivity.
Qed.
(** [] *)

(* ################################################################# *)
(** * Task 3: Recursive Reasoning About Expressions, A Transformation *)

(** We know that for any integer expressions [a1], [a2] and [a3],

    [[ a1 + (a2 + a3) and (a1 + a2) + a3 ]]
    [[ a1 * (a2 * a3) and (a1 * a2) * a3 ]]

    are equivalent expressions. In other words, [APlus] and [AMult] are
    associative in the sense of expressions equivalence. Also, if [AMinus] is
    taken into consideration,

    [[ a1 - (a2 + a3) and (a1 - a2) - a3 ]]
    [[ a1 - (a2 - a3) and (a1 - a2) + a3 ]]
    [[ a1 + (a2 - a3) and (a1 + a2) - a3 ]]

    are also equivalent expressions. Here are their Coq statements. *)

(** **** Exercise: 1 star, standard (APlus_assoc) *)
Lemma APlus_assoc: forall a1 a2 a3,
  aexp_equiv (a1 + (a2 + a3)) ((a1 + a2) + a3).
Proof.
  intros.
  unfold aexp_equiv, Func.equiv.
  intros.
  simpl.
  unfold Func.add.
  lia.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (APlus_AMinus_assoc) *)
Lemma APlus_AMinus_assoc: forall a1 a2 a3,
  aexp_equiv (a1 + (a2 - a3)) ((a1 + a2) - a3).
Proof.
  intros.
  unfold aexp_equiv, Func.equiv.
  intros.
  simpl.
  unfold Func.add, Func.sub.
  lia.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (AMinus_APlus_assoc) *)
Lemma AMinus_APlus_assoc: forall a1 a2 a3,
  aexp_equiv (a1 - (a2 + a3)) ((a1 - a2) - a3).
Proof.
  intros.
  unfold aexp_equiv, Func.equiv.
  intros.
  simpl.
  unfold Func.add, Func.sub.
  lia.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (AMinus_AMinus_assoc) *)
Lemma AMinus_AMinus_assoc: forall a1 a2 a3,
  aexp_equiv (a1 - (a2 - a3)) ((a1 - a2) + a3).
Proof.
  intros.
  unfold aexp_equiv, Func.equiv.
  intros.
  simpl.
  unfold Func.add, Func.sub.
  lia.
Qed.
(** [] *)

Lemma AMult_assoc: forall a1 a2 a3,
  aexp_equiv (a1 * (a2 * a3)) ((a1 * a2) * a3).
Proof.
  intros.
  unfold aexp_equiv, Func.equiv.
  intros.
  simpl.
  unfold Func.mul.
  lia.
Qed.
(** [] *)

(* Due to this consideration, we can always transform an expression to a
   ''left-associative'' one. We define this transformation as follows.
   The first three are auxiliary definitions. *)

Fixpoint APlus_left_assoc (a0 a: aexp): aexp :=
  (* Suppose [a0] and [a] are both ''left-associative'', define the
     transformation result of [a0 + a] *)
  match a with
  | APlus a1 a2 => APlus (APlus_left_assoc a0 a1) a2
  | AMinus a1 a2 => AMinus (APlus_left_assoc a0 a1) a2
  | _ => APlus a0 a
  end.

Fixpoint AMinus_left_assoc (a0 a: aexp): aexp :=
  (* Suppose [a0] and [a] are both ''left-associative'', define the
     transformation result of [a0 - a] *)
  match a with
  | APlus a1 a2 => AMinus (AMinus_left_assoc a0 a1) a2
  | AMinus a1 a2 => APlus (AMinus_left_assoc a0 a1) a2
  | _ => AMinus a0 a
  end.

Fixpoint AMult_left_assoc (a0 a: aexp): aexp :=
  (* Suppose [a0] and [a] are both ''left-associative'', define the
     transformation result of [a0 * a] *)
  match a with
  | AMult a1 a2 => AMult (AMult_left_assoc a0 a1) a2
  | _ => AMult a0 a
  end.

(** Then, [left_assoc] is our final definition. *)
Fixpoint left_assoc (a: aexp): aexp :=
  match a with
  | ANum n => ANum n
  | AId X => AId X
  | APlus a1 a2 => APlus_left_assoc (left_assoc a1) (left_assoc a2)
  | AMinus a1 a2 => AMinus_left_assoc (left_assoc a1) (left_assoc a2)
  | AMult a1 a2 => AMult_left_assoc (left_assoc a1) (left_assoc a2)
  end.

(** Now, your task is to prove it sound, i.e. the expression after [left_assoc]
    transformation is equivalent to the original one. We first prove three
    auxiliary functions's soundness. *)

(** **** Exercise: 2 stars, standard (APlus_left_assoc_sound) *)
Lemma APlus_left_assoc_sound: forall a0 a,
  aexp_equiv (APlus_left_assoc a0 a) (APlus a0 a).
Proof.
  intros.
  induction a; simpl;
  [ reflexivity | reflexivity | .. ].
  + rewrite IHa1.
    rewrite APlus_assoc.
    reflexivity.
  + rewrite IHa1.
    rewrite APlus_AMinus_assoc.
    reflexivity.
  + reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (AMinus_left_assoc_sound) *)
Lemma AMinus_left_assoc_sound: forall a0 a,
  aexp_equiv (AMinus_left_assoc a0 a) (AMinus a0 a).
Proof.
  intros.
  induction a; simpl;
  [ reflexivity | reflexivity | .. ].
  + rewrite IHa1.
    rewrite AMinus_APlus_assoc.
    reflexivity.
  + rewrite IHa1.
    rewrite AMinus_AMinus_assoc.
    reflexivity.
  + reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (AMult_left_assoc_sound) *)
Lemma AMult_left_assoc_sound: forall a0 a,
  aexp_equiv (AMult_left_assoc a0 a) (AMult a0 a).
Proof.
  intros.
  induction a; simpl;
  [ reflexivity | reflexivity | .. ].
  + reflexivity.
  + reflexivity.
  + rewrite IHa1.
    rewrite AMult_assoc.
    reflexivity.
Qed.
(** [] *)

(** Now, you are ready to prove our main theorem. *)

(** **** Exercise: 2 stars, standard (left_assoc_sound) *)
Theorem left_assoc_sound: forall a,
  aexp_equiv (left_assoc a) a.
Proof.
  intros.
  induction a; simpl;
  [ reflexivity | reflexivity | .. ].
  + rewrite APlus_left_assoc_sound.
    rewrite IHa1, IHa2.
    reflexivity.
  + rewrite AMinus_left_assoc_sound.
    rewrite IHa1, IHa2.
    reflexivity.
  + rewrite AMult_left_assoc_sound.
    rewrite IHa1, IHa2.
    reflexivity.
Qed.
(** [] *)

(** Besides soundness, it is critical that results of [left_assoc] are actually
    in a ''left-associative'' form. We first define [partially_right_assoc], the
    negation of ''left-associative'', that is, at least one subexpression is
    right associative. Described as follows, its definition contains two _match_
    expressions. The first one says: [a]'s top level syntax tree is right
    associative. The second one says: [a]'s subexpressions has at least one
    right associative subexpression inside. *)

Fixpoint partially_right_assoc (a: aexp): Prop :=
  match a with
  | APlus _ (APlus _ _) => True
  | APlus _ (AMinus _ _) => True
  | AMinus _ (APlus _ _) => True
  | AMinus _ (AMinus _ _) => True
  | AMult _ (AMult _ _) => True
  | _ => False
  end \/
  match a with
  | APlus a1 a2 => partially_right_assoc a1 \/ partially_right_assoc a2
  | AMinus a1 a2 => partially_right_assoc a1 \/ partially_right_assoc a2
  | AMult a1 a2 => partially_right_assoc a1 \/ partially_right_assoc a2
  | _ => False
  end.

(** Then we define [fully_left_associative]. *)

Definition fully_left_associative (a: aexp): Prop :=
  ~ partially_right_assoc a.

(** Similar to your soundness proof above, you need to prove three lemmas about
    auxiliary funcstions and [fully_left_associative] first. Hint: remember that
    you can use [tauto] solve propositional logic proof goals automatically. *)

(** **** Exercise: 2 stars, standard (APlus_left_assoc_fully_left_associative) *)
Lemma APlus_left_assoc_fully_left_associative: forall a0 a,
  fully_left_associative a0 ->
  fully_left_associative a ->
  fully_left_associative (APlus_left_assoc a0 a).
Proof.
  unfold fully_left_associative.
  intros.
  induction a; simpl; simpl in H0; tauto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (AMinus_left_assoc_fully_left_associative) *)
Lemma AMinus_left_assoc_fully_left_associative: forall a0 a,
  fully_left_associative a0 ->
  fully_left_associative a ->
  fully_left_associative (AMinus_left_assoc a0 a).
Proof.
  unfold fully_left_associative.
  intros.
  induction a; simpl; simpl in H0; tauto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (AMult_left_assoc_fully_left_associative) *)
Lemma AMult_left_assoc_fully_left_associative: forall a0 a,
  fully_left_associative a0 ->
  fully_left_associative a ->
  fully_left_associative (AMult_left_assoc a0 a).
Proof.
  unfold fully_left_associative.
  intros.
  induction a; simpl; simpl in H0; tauto.
Qed.
(** [] *)

(** Lastly, please prove that results of [left_assoc] always satisfy
    [fully_left_associative]. *)

(** **** Exercise: 2 stars, standard (left_assoc_fully_left_associative) *)
Lemma left_assoc_fully_left_associative: forall a,
  fully_left_associative (left_assoc a).
Proof.
  unfold fully_left_associative.
  intros.
  induction a; simpl;
  [ tauto | tauto | .. ].
  + apply APlus_left_assoc_fully_left_associative.
    apply IHa1.
    apply IHa2.
  + apply AMinus_left_assoc_fully_left_associative.
    apply IHa1.
    apply IHa2.
  + apply AMult_left_assoc_fully_left_associative.
    apply IHa1.
    apply IHa2.
Qed.
(** [] *)

(** You may wonder whether [left_assoc] is a meaningful operation. Well, it
    might be. Try to answer the following questions about it. *)

(** **** Exercise: 1 star, standard *)

(** In comparison, which one of the following is the better optimazation?

    - do [fold_constants] directly;

    - do [fold_constants] after [left_assoc].

    Choose one correct statement:

    0. They always generate results with the same length.

    1. The first one always generates shorter (or equivalent) result and
       statement 0 is wrong.

    2. The second one always generates shorter (or equivalent) result and
       statement 0 is wrong.

    3. They are not comparable. *)

Definition my_choice_1 := 3.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** In comparison, which one of the following is the better optimazation?

    - do [fold_constants] directly;

    - do [fold_constants], then [left_assoc], and [fold_constants] again
      in the end

    Choose one correct statement:

    0. They always generate results with the same length.

    1. The first one always generates shorter (or equivalent) result and
       statement 0 is wrong.

    2. The second one always generates shorter (or equivalent) result and
       statement 0 is wrong.

    3. They are not comparable. *)

Definition my_choice_2 := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(* ################################################################# *)
(** * Task 4: Equivalence and Congruence *)

(** In lectures, we defined a [same_structure] relation for binary trees. *)

Inductive tree: Type :=
| Leaf: tree
| Node (l: tree) (v: Z) (r: tree): tree.

Fixpoint same_structure (t1 t2: tree): Prop :=
  match t1, t2 with
  | Leaf, Leaf => True
  | Leaf, Node _ _ _ => False
  | Node _ _ _, Leaf => False
  | Node l1 _ r1, Node l2 _ r2 => same_structure l1 l2 /\ same_structure r1 r2
  end.

(** Now, your task is prove that it is a equivalence relation and a congruence
    w.r.t. tree construction [Node] and tree reverse operation. *)

(** **** Exercise: 1 star, standard (same_structure_refl) *)
Lemma same_structure_refl: Reflexive same_structure.
Proof.
  unfold Reflexive.
  intros.
  induction x; simpl.
  + exact I.
  + split.
    - exact IHx1.
    - exact IHx2.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (same_structure_sym) *)
Lemma same_structure_sym: Symmetric same_structure.
Proof.
  unfold Symmetric.
  intros.
  revert y H.
  induction x; intros.
  + destruct y.
    - reflexivity.
    - simpl in H.
      contradiction.
  + destruct y; simpl in H.
    { contradiction. }
    destruct H.
    apply IHx1 in H.
    apply IHx2 in H0.
    simpl.
    tauto.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (same_structure_trans) *)
Lemma same_structure_trans: Transitive same_structure.
Proof.
  unfold Transitive.
  intros.
  revert y z H H0.
  induction x; intros; revert y H H0.
  + induction y; intros.
    - destruct z; exact H0.
    - destruct z; simpl in H; contradiction.
  + induction y; intros.
    - destruct z; simpl in H; contradiction.
    - destruct z; simpl in H.
      { contradiction. }
      destruct H, H0.
      specialize IHx1 with y1 z1.
      specialize IHx2 with y2 z2.
      simpl.
      tauto.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (same_structure_Node_congr) *)
Lemma same_structure_Node_congr:
  Proper (same_structure ==> eq ==> same_structure ==> same_structure) Node.
Proof.
  unfold Proper, respectful.
  intros.
  simpl.
  tauto.
Qed.
(** [] *)

Fixpoint tree_reverse (t: tree): tree :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node (tree_reverse r) v (tree_reverse l)
  end.

(** **** Exercise: 2 stars, standard (same_structure_tree_reverse_congr) *)
Lemma same_structure_tree_reverse_congr:
  Proper (same_structure ==> same_structure) tree_reverse.
Proof.
  unfold Proper, respectful.
  intros.
  revert y H.
  induction x; intros.
  + destruct y.
    - reflexivity.
    - simpl in H.
      contradiction.
  + destruct y; simpl in H.
    { contradiction. }
    destruct H.
    apply IHx1 in H.
    apply IHx2 in H0.
    simpl.
    tauto.
Qed.
(** [] *)

(* ################################################################# *)
(** * Task 5: Understanding Bourbaki-Witt Fix Points *)

Module Task5_1.

(** Let [A] be the set of all subsets of integers and let [<=] be the inclusion
    relation. In other words, for any [a b: A], [a <= b] if and only if [a] is
    a subset of [b]. Obviously, [<=] is a partial order on [A], and moreover, it
    is a complete partial ordering on [A].

    Consider the following function [f] from [A] to [A] and answer questions.

    - Given [X: A], an integer [u] is an element of [ f(X) ] if and only if [-u]
      is an element of [X]. *)

(** **** Exercise: 1 star, standard *)

(** Is this function [f] a monotonic function w.r.t. the partial order [<=] on
    [A]? 1: Yes. 2: No. *)

Definition my_answer_1: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Is this function [f] a continuous function w.r.t. the CPO [<=]? 1: Yes.
    2: No. *)

Definition my_answer_2: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** How many fixpoints does [f] have? 1: Zero. 2: Exactly one. 3: Finite but
    more than one. 4: Infinite. *)

Definition my_answer_3: Z := 4.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Is the following statement correct? 1: Yes. 2: No.

    The function [f] has at least one fixpoint and the singleton set [ {0} ] is
    its least fixpoint w.r.t. the order [<=]. *)

Definition my_answer_4: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

End Task5_1.

Module Task5_2.

(** Let [A] and [<=] be the same set and CPO described in the last sub-task.
    Consider the following function [f] from [A] to [A] and answer questions.

    - Given [X: A], an integer [u] is an element of [ f(X) ] if and only if
      [u = 0] or [u - 1] is an element of [X]. *)

(** **** Exercise: 1 star, standard *)

(** Is this function [f] a monotonic function w.r.t. the partial order [<=] on
    [A]? 1: Yes. 2: No. *)

Definition my_answer_1: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Is this function [f] a continuous function w.r.t. the CPO [<=]? 1: Yes.
    2: No. *)

Definition my_answer_2: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Which is the least fixpoint of [f] w.r.t. [<=]?

    1: The empty set.
    2: The set of all integers.
    3: The set of all non-negative integers.
    4: The singleton set with integer zero.
    5: None of the above. *)

Definition my_answer_3: Z := 3.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** Which is the greatest fixpoint of [f] w.r.t. [<=]?

    1: The empty set.
    2: The set of all integers.
    3: The set of all non-negative integers.
    4: The singleton set with integer zero.
    5: None of the above. *)

Definition my_answer_4: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

End Task5_2.

Module Task5_3.

(** Let [A] and [<=] be the same set and CPO described in the last sub-task.
    Consider the following function [f] from [A] to [A] and answer questions.
    Given [X: A],

    - [0] is an element of [ f(X) ] if all positive integers are elements of [X]

    - [1] is an element of [ f(X) ]

    - a integer [u], other than zero and one, is an element of [ f(X) ] if
      [u - 1] is an element of [X]. *)

(** **** Exercise: 1 star, standard *)

(** Is this function [f] a monotonic function w.r.t. the partial order [<=] on
    [A]? 1: Yes. 2: No. *)

Definition my_answer_1: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Is this function [f] a continuous function w.r.t. the CPO [<=]? 1: Yes.
    2: No. *)

Definition my_answer_2: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Which is the least fixpoint of [f] w.r.t. [<=]?

    1: The empty set.
    2: The set of all integers.
    3: The set of all positive integers.
    4: The singleton set with integer zero.
    5: None of the above. *)

Definition my_answer_3: Z := 5.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

End Task5_3.

(* ################################################################# *)
(** * Task 6: Understanding Loops' Denotational Semantics *)

Section BW_FixPoint.

(** Given a boolean expression [b] and a loop body's denotation [d], we have
    defined [loop_sem b d] as the whole loop's denotation in lectures. We also
    know that [loop_sem b d] is the least fix point of the following function
    [F], although its construction is not identical to the one in Bourbaki-Witt
    Fix Point theorem. *)

Variable b: bexp.
Variable d: state -> state -> Prop.
  
Definition F X := if_sem b (BinRel.concat d X) BinRel.id.

(** In other words, [loop_sem b d] is equivalent with [F (loop_sem b d)]. *)

(** Now, let's discover the relation between our definition of [loop_sem] and
    Bourbaki-Witt's construction. Bourbaki-Witt's construction is based on a
    bottom element, in this case, the empty relation. *)

Definition Bot: state -> state -> Prop := BinRel.empty.

(** And the least fix point is the least upper bound of:

    - Bot

    - F Bot

    - F (F Bot)

    - F (F (F Bot))

    - ... *)

Fixpoint FBot (n: nat) :=
  match n with
  | O => Bot
  | S n' => F (FBot n')
  end.

Definition loop_sem' := BinRel.omega_union (FBot).

(** In this case, the least upper bound of a ternary relation sequence is their
    [omega_union_sem]. Thus, Bourbaki-Witt's fixpoint can be formalized as
    [loop_sem'] above. *)

End BW_FixPoint.

(** Now, let's discover the relationship between [loop_sem]'s construction and
    [loop_sem']'s construction.

    Hint 1: Both [iter_loop_body] and [FBot] are recursively defined. You may
    write [simpl] to use their definitions.

    Hint 2: Proving some extra properties about [Bot], [BinRel.union] and
    [BinRel.concat] could make your proofs more concise. For example:

    [[
        forall d: state -> state -> Prop,
          BinRel.equiv (BinRel.union Bot d) d.

        forall d: state -> state -> Prop,
          BinRel.equiv (BinRel.union d Bot) d.

        forall d: state -> state -> Prop,
          BinRel.equiv (BinRel.concat d Bot) Bot.

        forall d: state -> state -> Prop,
          BinRel.equiv (BinRel.concat Bot d) Bot.

        forall d: state -> state -> Prop,
          BinRel.equiv (BinRel.concat d BinRel.id) d.

        forall d: state -> state -> Prop,
          BinRel.equiv (BinRel.concat BinRel.id d) d.
    ]]
*)

Lemma Union_bot_d: forall d: state -> state -> Prop,
  BinRel.equiv (BinRel.union Bot d) d.
Proof.
  intros.
  unfold Bot.
  unfold BinRel.empty, BinRel.union, BinRel.equiv.
  tauto.
Qed.

Lemma Union_d_bot: forall d: state -> state -> Prop,
  BinRel.equiv (BinRel.union d Bot) d.
Proof.
  intros.
  unfold Bot.
  unfold BinRel.empty, BinRel.union, BinRel.equiv.
  tauto.
Qed.

Lemma Concat_d_bot: forall d: state -> state -> Prop,
  BinRel.equiv (BinRel.concat d Bot) Bot.
Proof.
  intros.
  unfold Bot.
  unfold BinRel.empty, BinRel.concat, BinRel.equiv.
  unfold iff; split; intros.
  + destruct H.
    tauto.
  + tauto.
Qed.

Lemma Concat_bot_d: forall d: state -> state -> Prop,
  BinRel.equiv (BinRel.concat Bot d) Bot.
Proof.
  intros.
  unfold Bot.
  unfold BinRel.empty, BinRel.concat, BinRel.equiv.
  unfold iff; split; intros.
  + destruct H.
    tauto.
  + tauto.
Qed.

Lemma Concat_d_id: forall d: state -> state -> Prop,
  BinRel.equiv (BinRel.concat d BinRel.id) d.
Proof.
  intros.
  unfold BinRel.id, BinRel.concat, BinRel.equiv.
  unfold iff; split; intros.
  + destruct H; destruct H.
    rewrite H0 in H.
    tauto.
  + exists b.
    tauto.
Qed.

Lemma Concat_id_d: forall d: state -> state -> Prop,
  BinRel.equiv (BinRel.concat BinRel.id d) d.
Proof.
  intros.
  unfold BinRel.id, BinRel.concat, BinRel.equiv.
  unfold iff; split; intros.
  + destruct H; destruct H.
    rewrite <- H in H0.
    tauto.
  + exists a.
    tauto.
Qed.

(** **** Exercise: 2 stars, standard (FBot1_fact) *)

Fact FBot1_fact: forall b d, BinRel.equiv (iter_loop_body b d 0) (FBot b d 1).
Proof.
  intros.
  simpl.
  unfold F, if_sem.
  rewrite Concat_d_bot.
  rewrite Concat_d_bot, Concat_d_id.
  rewrite Union_bot_d.
  simpl.
  reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (FBot2_fact) *)

Fact FBot2_fact: forall b d,
  BinRel.equiv
    (BinRel.union (iter_loop_body b d 1) (iter_loop_body b d 0))
    (FBot b d 2).
Proof.
  intros.
  simpl.
  unfold F, if_sem.
  rewrite Concat_d_bot.
  rewrite Concat_d_bot, Concat_d_id.
  rewrite Union_bot_d.
  simpl.
  reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (FBot_n_fact_statement) *)

(** For generic natural number [n], what is the connection between [FBot b d n]
    and [iter_loop_body]? Write down a proposition to describe this connection.
    Note that your [FBot_n_fact_statement] should have the following form:

    - forall b d n, BinRel.equiv (...) (FBot b d n).

    And you probably need to write some auxiliary definition(s) first. *)

Fixpoint iter_loop_union (b: bexp)
                         (d: state -> state -> Prop)
                         (n: nat): state -> state -> Prop :=
  match n with
  | O =>
         BinRel.empty
  | S n' =>
         BinRel.union (iter_loop_body b d (n - 1))
                      (iter_loop_union b d n')
end.

Definition FBot_n_fact_statement: Prop := forall b d n,
  BinRel.equiv (iter_loop_union b d n) (FBot b d n).
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(* 2021-03-22 18:13 *)
