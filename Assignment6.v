(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2021/04/21.                                             *)
(* Due: 2021/04/25, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Assignment6.v) on CANVAS.         *)
(*                                                                   *)
(* 4. Only valid Coq files are accepted. In other words, please      *)
(*    make sure that your file does not generate a Coq error. A      *)
(*    way to check that is: click "compile buffer" for this file     *)
(*    and see whether an "Assignment6.vo" file is generated.         *)
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
(*      (* Software Foundations Volume 5 *)                          *)
(*                                                                   *)
(* ***************************************************************** *)

(* ################################################################# *)
(** * Task 1: Understanding Weakest Preconditions *)

Module Task1.

Require Import PL.Imp.
Require Import Coq.Lists.List.
Import ListNotations.
Import Assertion_D.
Import Abstract_Pretty_Printing.

(** **** Exercise: 3 stars, standard *)

(** Which of the following statements about weakest preconditions are correct?

    - 1. For any assertion [P], program variable [X] and integer expression [E],
      [ P [X |-> E] ] is a weakest precondition of [X ::= E] and [P].

    - 2. For any assertion [P], logical variable [x], program variable [X] and
      integer expression [E], if [x] does not freely occur in [P], then [ P ] is
      a weakest precondition of [X ::= E] and
          [    EXISTS x, P [X |-> x] AND {[ X ]} = {[ E [X |-> x] ]}    ].
    
    - 3. If [P] is a weakest precondition of [c] and [Q], and [P] is equivalent
      to [P'], then [P'] is also a weakest precondition of [c] and [Q]. (Here,
      we say that [P] and [P'] are equivalent when: for any interpretation [J],
      [J |== P] if and only if [J |== P'].)

    This is a multiple-choice problem. You should use an ascending Coq list to
    describe your answer, e.g. [1; 2; 3], [1; 3], [2]. *)

Definition my_choice1: list Z := [1; 2; 3].
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 3 stars, standard *)

(** Which of the following statements about weakest preconditions are correct?

    - 1. [True] is a weakest precondition of [While (X <= X) Do Skip EndWhile]
      and [False].

    - 2. [False] is a weakest precondition of [While (X <= X) Do Skip EndWhile]
      and [False].
    
    - 3. For any assertions [P], [Q], any boolean expression [b] and any loop
      body [c], if [P] is a weakest precondition of [While b Do c EndWhile] and
      [Q], and [P] is also a weakest precondition of [While b Do c EndWhile] and
      [ P AND NOT {[ b ]} ].

    This is a multiple-choice problem. You should use an ascending Coq list to
    describe your answer, e.g. [1; 2; 3], [1; 3], [2]. *)

Definition my_choice2: list Z := [1; 3].
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

End Task1.

(* ################################################################# *)
(** * Task 2: Understanding VST *)

Module Task2.

Require Import PL.Imp.
Require Import Coq.Lists.List.
Import ListNotations.
Import Assertion_D.
Import Abstract_Pretty_Printing.

(** **** Exercise: 1 star, standard *)

(** In our tutorial, we cannot prove that the following C program satisfying
    the Hoare triple below.

      int add(int x, int y) {
        int z;
        z = x + y;
        return z;
      }

      Definition add_spec :=
       DECLARE _add
        WITH x: Z, y: Z
        PRE  [ tint, tint ]
           PROP    ()
           PARAMS  (Vint (Int.repr x); Vint (Int.repr y))
           GLOBALS ()
           SEP     ()
        POST [ tint ]
           PROP  ()
           RETURN (Vint (Int.repr (x + y)))
           SEP   ().

      The reason is that overflow in signed integer arithmetic is undefined
      behavior in C and the precondition does not exclude that possibility.

      Is the explanation above correct? 1. Yes. 2. No. *)

Definition my_choice1: Z := 1.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** In VST, [forward] is a powerful command for forward symbolic execution. For
    example, the following is to one proof goal before [forward] and the
    corresponding proof goal after [forward].

    [

     semax Delta
       (PROP  ( )
        LOCAL (temp _w w;
               temp _v v)
        SEP   (listrep s1 w;
               data_at Tsh t_struct_list (Vint (Int.repr s2a), y) v;
               listrep s2b y))
       (_t = (_v -> _tail);
        MORE_COMMANDS)
     POSTCONDITION

    ]

    [

     semax Delta
       (PROP  ( )
        LOCAL (temp _t y;
               temp _w w;
               temp _v v)
        SEP   (listrep s1 w;
               data_at Tsh t_struct_list (Vint (Int.repr s2a), y) v;
               listrep s2b y))
       ((_v -> _tail) = _w;
        MORE_COMMANDS)
       POSTCONDITION

    ]

    The [forward] tactic actually builds a Hoare logic proof tree for the former
    triple from a proof tree for the latter triple. In this proof, it uses
    VST's consequence rule and some other Hoare logic proof rules.

    Which of the following proof rules are needed?
    1. The assgnment rule.
    2. The sequence rule.
    3. The assgnment rule and the sequence rule. *)

Definition my_choice2: Z := 3.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Is the following statement correct? 1. Yes. 2. No.

    In VST, we can prove the following assertion derivation:

       forall p v, data_at Tsh tint v p |--
                   data_at Tsh tint v p * data_at Tsh tint v p  *)

Definition my_choice3: Z := 2.
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *)
(** [] *)

End Task2.

(* ################################################################# *)
(** * Task 3: List Segments and Append *)

Module append.

Require Import VST.floyd.proofauto.
Require Import EV.AuxiliaryTac.
Require Import EV.append.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

(** In this part, we will verify the following C functions:

      struct list {
        unsigned int head;
        struct list * tail;
      };

      struct list *append (struct list *x, struct list *y) {
        struct list *t, *u;
        if (x==NULL)
          return y;
        else {
          t = x;
          u = t->tail;
          while (u!=NULL) {
            t = u;
            u = t->tail;
          }
          t->tail = y;
          return x;
        }
      }

    Using [listrep], we can state their specification.
*)

Definition t_struct_list := Tstruct _list noattr.

Fixpoint listrep (sigma: list Z) (x: val) : mpred :=
 match sigma with
 | h::hs => 
    EX y:val, 
      data_at Tsh t_struct_list (Vint (Int.repr h),y) x  *  listrep hs y
 | nil => 
    !! (x = nullval) && emp
 end.

Arguments listrep sigma x : simpl never.

Definition append_spec :=
 DECLARE _append
  WITH x: val, y: val, s1: list Z, s2: list Z
  PRE [ tptr t_struct_list , tptr t_struct_list ]
     PROP()
     PARAMS (x; y)
     SEP (listrep s1 x; listrep s2 y)
  POST [ tptr t_struct_list ]
    EX r: val,
     PROP()
     RETURN (r)
     SEP (listrep (s1++s2) r).

(** Both C functions traverse a linked list using a while loop. Thus, the
    keypoint of verifying them is to write down the correct loop invariant.
    The following diagram demonstrates an intermediate state in traversing.

        +---+---+            +---+---+   +---+---+   +---+---+   
  x ==> |   |  ===> ... ===> |   | y ==> |   | z ==> |   |  ===> ... 
        +---+---+            +---+---+   +---+---+   +---+---+

      | <==== Part 1 of sigma =====> |            | <== Part 2 ==> |

      | <========================== sigma =======================> |

    To properly describe loop invariants, we need a predicate to describe
    the partial linked list from address [x] to address [y]. We provide its
    definition for you. But it is your task to prove its important properties.
*)

Fixpoint lseg (sigma: list Z) (x y: val) : mpred :=
  match sigma with
  | nil => !! (x = y) && emp
  | h::hs => EX u:val, data_at Tsh t_struct_list (Vint (Int.repr h), u) x * lseg hs u y
  end.

Arguments lseg sigma x y : simpl never.

(** **** Exercise: 1 star, standard (singleton_lseg) *)
Lemma singleton_lseg: forall (a: Z) (x y: val),
  data_at Tsh t_struct_list (Vint (Int.repr a), y) x |-- lseg [a] x y.
Proof.
  intros.
  unfold lseg.
  Exists y.
  entailer!.
Qed.
(** [] *)

(** In the next lemma, try to understand how to use [sep_apply]. *)
Lemma lseg_nullval: forall sigma x,
  lseg sigma x nullval |-- listrep sigma x.
Proof.
  intros.
  revert x; induction sigma; intros.
  + unfold listrep, lseg.
    entailer!.
  + unfold lseg; fold lseg.
    unfold listrep; fold listrep.
    Intros u.
    Exists u.
    (** The following tactic "apply" [IHsigma] on the left side of derivation. *)
    sep_apply (IHsigma u).
    entailer!.
Qed.

(** **** Exercise: 2 stars, standard (lseg_lseg) *)
Lemma lseg_lseg: forall (s1 s2: list Z) (x y z: val),
  lseg s1 x y * lseg s2 y z |-- lseg (s1 ++ s2) x z.
Proof.
  intros.
  revert x; induction s1; intros.
  + unfold lseg; fold lseg.
    rewrite app_nil_l.
    entailer!.
  + rewrite <- app_comm_cons.
    unfold lseg; fold lseg.
    Intros u.
    Exists u.
    sep_apply IHs1.
    entailer!.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (lseg_list) *)
Lemma lseg_list: forall (s1 s2: list Z) (x y: val),
  lseg s1 x y * listrep s2 y |-- listrep (s1 ++ s2) x.
Proof.
  intros.
  revert x; induction s1; intros.
  + unfold lseg; fold lseg.
    rewrite app_nil_l.
    entailer!.
  + rewrite <- app_comm_cons.
    unfold lseg; fold lseg.
    unfold listrep; fold listrep.
    Intros u.
    Exists u.
    sep_apply IHs1.
    entailer!.
Qed.
(** [] *)

(** Try to use prove the following assertion derivation use the lemmas above.
    The first step is done for you. *)

(** **** Exercise: 1 star, standard (lseg_ex0) *)
Example lseg_ex0: forall s1 s2 s3 x y z,
  lseg s1 x y * lseg s2 y z * lseg s3 z nullval |-- listrep (s1 ++ s2 ++ s3) x.
Proof.
  intros.
  sep_apply (lseg_lseg s2 s3 y z nullval).
  sep_apply lseg_nullval.
  sep_apply lseg_list.
  entailer!.
Qed.
(** [] *)

(** Using similar proof techniques, you can prove the following two entailments.
    And you may use them later in your program verification proof. *)

(** **** Exercise: 1 star, standard (lseg_ex1) *)
Example lseg_ex1: forall (s1a: list Z) (s1b: Z) (x y z: val),
  lseg s1a x y * data_at Tsh t_struct_list (Vint (Int.repr s1b), z) y
    |-- lseg (s1a ++ [s1b]) x z.
Proof.
  intros.
  sep_apply singleton_lseg.
  sep_apply (lseg_lseg s1a [s1b] x y z).
  entailer!.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (lseg_ex2) *)
Example lseg_ex2: forall (s1a: list Z) (s1b: Z) (s2: list Z) (x y z: val),
  lseg s1a x y * data_at Tsh t_struct_list (Vint (Int.repr s1b), z) y *
  listrep s2 z |-- listrep ((s1a ++ [s1b]) ++ s2) x.
Proof.
  intros.
  sep_apply lseg_ex1.
  sep_apply lseg_list.
  entailer!.
Qed.
(** [] *)

(** Now, you are going to prove [sumlist] correct. The following lemmas are
    copied from tutorial for proof automation. *)

Lemma listrep_local_facts:
  forall sigma p,
   listrep sigma p |--
   !! (is_pointer_or_null p /\ (p=nullval <-> sigma=nil)).
Proof.
  intros.
  revert p; induction sigma; 
    unfold listrep; fold listrep; intros; normalize.
  apply prop_right; split; simpl; auto. intuition.
  entailer!.
  split; intro. subst p. destruct H; contradiction. inv H2.
Qed.

Hint Resolve listrep_local_facts : saturate_local.

Lemma listrep_valid_pointer:
  forall sigma p,
   listrep sigma p |-- valid_pointer p.
Proof.
  destruct sigma; unfold listrep; fold listrep;
  intros; normalize.
  auto with valid_pointer.
  apply sepcon_valid_pointer1.
  apply data_at_valid_ptr; auto.
  simpl; computable.
Qed.

Hint Resolve listrep_valid_pointer : valid_pointer.

Definition Gprog : funspecs :=
  ltac:(with_library prog [ append_spec ]).

(** Remark. The following proof strategy is from << Software Foundation >>
volume 5. *)

(** **** Exercise: 1 star, standard (listrep_null) *)
Lemma listrep_null: forall contents x,
  x = nullval ->
  listrep contents x = !! (contents=nil) && emp.
Proof.
  intros.
  apply pred_ext.
  + entailer!.
    - apply H0; reflexivity.
    - destruct H0; clear H0.
      rewrite H.
      2: reflexivity.
      unfold listrep.
      entailer!.
  + unfold listrep.
    entailer!.
Qed.
(** [] *)

(** **** Exercise: 1 star, standard (listrep_nonnull) *)
Lemma listrep_nonnull: forall contents x,
  x <> nullval ->
  listrep contents x =
    EX h: Z, EX hs: list Z, EX y: val,
      !! (contents = h :: hs) &&
        data_at Tsh t_struct_list (Vint (Int.repr h), y) x  *  listrep hs y.
Proof.
  intros.
  apply pred_ext; entailer!.
  + induction contents.
    - unfold listrep at 1.
      Intros.
      contradiction.
    - unfold listrep; fold listrep.
      Intros y.
      Exists a contents y.
      entailer!.
  + unfold listrep; fold listrep.
    Exists y.
    entailer!.
Qed.
(** [] *)

(** **** Exercise: 4 stars, standard (body_append) *)
Lemma body_append: semax_body Vprog Gprog f_append append_spec.
Proof.
  start_function.
  forward_if. (* if (x == NULL) *)
  + (* If-then *)
    rewrite (listrep_null _ x) by auto.
    forward.
    rewrite app_nil_l.
    Exists y.
    entailer!.
  + (* If-else *)
    rewrite (listrep_nonnull _ x) by auto.
    Intros h r u.
    forward. (* t = x; *)
    forward. (* u = t -> tail; *)

    forward_while
        ( EX s1a: list Z, EX b: Z, EX s1c: list Z, EX t: val, EX u: val,
          PROP (s1 = s1a ++ b :: s1c)
          LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
          SEP (lseg s1a x t;
               data_at Tsh t_struct_list (Vint (Int.repr b), u) t;
               listrep s1c u;
               listrep s2 y))%assert.
    - (* current assertion implies loop invariant *)
      Exists (@nil Z) h r x u.
      subst s1.
      entailer!.
      unfold lseg; entailer!.
    - (* loop test is safe to execute *)
      entailer!.
    - (* loop body preserves invariant *)
      clear h r u H0; rename u0 into u.
      rewrite (listrep_nonnull _ u) by auto.
      Intros c s1d z.
      forward. (* t = u; *)
      forward. (* u = t -> tail; *)

      Exists ((s1a ++ b :: nil), c, s1d, u, z).
      unfold fst, snd.
      entailer!.
      * rewrite app_assoc_reverse.
        simpl.
        reflexivity.
      * apply lseg_ex1.
    - (* after the loop *)
      clear h r u H0; rename u0 into u.
      rewrite (listrep_null s1c) by auto.
      Intros.
      subst s1c.

      forward.
      forward.
      Exists x.
      entailer!.
      apply lseg_ex2.
Qed.
(** [] *)

End append.

(* 2021-04-21 17:20 *)
