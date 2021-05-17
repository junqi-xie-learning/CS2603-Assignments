(* ***************************************************************** *)
(*                                                                   *)
(* Released: 2021/05/17.                                             *)
(* Due: 2021/05/21, 23:59:59, CST.                                   *)
(*                                                                   *)
(* 0. Read instructions carefully before start writing your answer.  *)
(*                                                                   *)
(* 1. You should not add any hypotheses in this assignment.          *)
(*    Necessary ones have been provided for you.                     *)
(*                                                                   *)
(* 2. In order to check whether you have finished all tasks or not,  *)
(*    just see whether all "Admitted" has been replaced.             *)
(*                                                                   *)
(* 3. You should submit this file (Assignment8.v) on CANVAS.         *)
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
Require Import PL.RTClosure PL.Imp.

(* ################################################################# *)
(** * Task 1: Mix typed expressions *)

Module Task1.
Local Open Scope Z.

(** This is our definition of mix typed expressions. In this task, you need to
    answer questions about their evaluation process and type checking results. *)

Definition var: Type := nat.

Definition state: Type := var -> Z.

Inductive mexp : Type :=
  | MNum (n : Z)
  | MId (X : var)
  | MPlus (a1 a2 : mexp)
  | MMinus (a1 a2 : mexp)
  | MMult (a1 a2 : mexp)
  | MTrue
  | MFalse
  | MEq (a1 a2 : mexp)
  | MLe (a1 a2 : mexp)
  | MNot (b : mexp)
  | MAnd (b1 b2 : mexp)
.

(** Here is some coercion and notations for pretty printing. *)

Declare Scope mexp.
Delimit Scope mexp with mexp.
Local Open Scope mexp.

Coercion MNum : Z >-> mexp.
Coercion MId : var >-> mexp.
Notation "x + y" := (MPlus x y) (at level 50, left associativity) : mexp.
Notation "x - y" := (MMinus x y) (at level 50, left associativity) : mexp.
Notation "x * y" := (MMult x y) (at level 40, left associativity) : mexp.
Notation "x <= y" := (MLe x y) (at level 70, no associativity) : mexp.
Notation "x == y" := (MEq x y) (at level 70, no associativity) : mexp.
Notation "x && y" := (MAnd x y) (at level 40, left associativity) : mexp.
Notation "'!' b" := (MNot b) (at level 39, right associativity) : mexp.
Notation "[ x ; .. ; y ]" := (@cons mexp x .. (@cons mexp y (@nil mexp)) ..).

Module Task1_Examples.

Parameter X: var.
Parameter S: var.
  
(** Suppose [X] and [S] are program variables and [st: state] satisfies:

    - [st X = 0]

    - [st S = 0].

    Please describe the evaluation process of

    - [S + (X == 0)]

    on [st] using a Coq list. Specifically, this Coq list must demonstrate the
    result of every step (see lecture notes: run time error 2) from the
    beginning to the end. The ending expression can be a evaluation result (an
    integer constant or a boolean constant) or a stuck state (no step can be
    taken since an error occurs).
*)

Definition my_answer_1: list mexp :=
  [ S + (X == 0);
    0 + (X == 0);
    0 + (0 == 0);
    0 + MTrue;
    0 + 1;
    1 ]
.

(** Suppose [X] and [S] are program variables and [st: state] satisfies:

    - [st X = 0]

    - [st S = 0].

    Please describe the evaluation process of

    - [S && (X == 0)]

    on [st] using a Coq list. Specifically, this Coq list must demonstrate the
    result of every step (see lecture notes: run time error 2) from the
    beginning to the end. The ending expression can be a evaluation result (an
    integer constant or a boolean constant) or a stuck state (no step can be
    taken since an error occurs).
*)

Definition my_answer_2: list mexp :=
  [ S && (X == 0);
    0 && (X == 0) ]
.

End Task1_Examples.

(** **** Exercise: 2 stars, standard *)

Parameter P: var.
Parameter X: var.

(** Suppose [P] and [X] are program variables and [st: state] satisfies:

    - [st P = 0]

    - [st X = 1].

    Please describe the evaluation process of

    - [(P == 0) && (X && (X + 1))]

    on [st] using a Coq list. Specifically, this Coq list must demonstrate the
    result of every step (see lecture notes: run time error 2) from the
    beginning to the end. The ending expression can be a evaluation result (an
    integer constant or a boolean constant) or a stuck state (no step can be
    taken since an error occurs).
*)

Definition my_answer_1_1: list mexp
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 2 stars, standard *)

(** This time, consider a slightly different situation. Suppose [st: state]
    satisfies:

    - [st P = 1]

    - [st X = 1].

    Please describe the evaluation process of

    - [(P == 0) && (X && (X + 1))]

    on [st] using a Coq list. Specifically, this Coq list must demonstrate the
    result of every step (see lecture notes: run time error 2) from the
    beginning to the end. The ending expression can be a evaluation result (an
    integer constant or a boolean constant) or a stuck state (no step can be
    taken since an error occurs).
*)

Definition my_answer_1_2: list mexp
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Does [(P == 0) && (X && (X + 1))] type check?
    1. Yes. 2. No.
*)

Definition my_answer_1_3: Z
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 1 star, standard *)

(** Does [(P == 0) && (P == 1) && (X && (X + 1))] type check?
    1. Yes. 2. No.
*)

Definition my_answer_1_4: Z
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

Import ListNotations.

(** **** Exercise: 1 star, standard *)

(** Which of the following statements are correct about [mexp]'s small step
    semantics and type checking function?

    1. Its semantics is type safe since it has the progress property and
       the preservation property.

    2. Every legal expression (according the type checking function) can be
       evaluated safely to the end on any program state and the evaluation
       process will either end in an integer constant or a boolean constant.

    3. If an expression [m: mexp] can be safely evaluated on a state [st],
       then [m] must be a well-typed expression.

    4. If an expression [m: mexp] can be safely evaluated on any state [st],
       then [m] must be a well-typed expression.

    This is a multiple-choice problem. You should use an ascending Coq list to
    describe your answer, e.g. [1; 2; 3], [1; 3], [2]. *)

Definition my_answer_1_5: list Z
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

End Task1.

(* ################################################################# *)
(** * Task 2: Nondeterministic programs *)

Module Task2.

(** Consider the programming language with [CChoice] we discussed in class.
    Please determine whether sample programs satisfy one of the following
    properties or not. Here are the list of properties.

    - 1. The program has deterministic behavior and will terminate.

    - 2. The program has nondeterministic behavior but will always terminate.

    - 3. The program has deterministic behavior and will not terminate.

    - 4. It is possible for the program to terminate and also possible not to
         terminate . *)

(** **** Exercise: 1 star, standard *)

(** The program [c] is:
        [[
            CChoice (X ::= 1) (X ::= 2)
        ]]
    The initial state [st] satisfies:
        [[
            st Y = 0
        ]]
    for any program variable [Y]. Which property listed in the beginning of this
    task is true for executing [c] from [st] according to the denotational
    semantics? *)

Definition my_answer_2_1: Z
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 1 star, standard *)

(** The program [c] is:
        [[
            CChoice (X ::= 1) (X ::= X + 1)
        ]]
    The initial state [st] satisfies:
        [[
            st Y = 0
        ]]
    for any program variable [Y]. Which property listed in the beginning of this
    task is true for executing [c] from [st] according to the small step
    semantics? *)

Definition my_answer_2_2: Z
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 1 star, standard *)

(** The program [c] is:
        [[
            X ::= 1000;;
            While (! (X == 0)) Do
               CChoice (X ::= X - 1) (Skip)
            EndWhile
        ]]
    The initial state [st] satisfies:
        [[
            st Y = 0
        ]]
    for any program variable [Y]. Which property listed in the beginning of this
    task is true for executing [c] from [st] according to the small step
    semantics? *)

Definition my_answer_2_3: Z
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 1 star, standard *)

(** The program [c] is:
        [[
            X ::= 1001;;
            While (! (X == 0)) Do
               CChoice (X ::= X - 2) (Skip)
            EndWhile
        ]]
    The initial state [st] satisfies:
        [[
            st Y = 0
        ]]
    for any program variable [Y]. Which property listed in the beginning of this
    task is true for executing [c] from [st] according to the denotational
    semantics? *)

Definition my_answer_2_4: Z
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

End Task2.

(* ################################################################# *)
(** * Task 3: Pointers and addresses *)

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

Module Task3.
Local Open Scope Z.

(** The following are the programming language we discussed in class. We paste
    its integer expression, its denotational semantics and its small step
    semantics. *)

Definition var: Type := nat.

Inductive aexp : Type :=
  | ANum (n : Z)
  | AId (X : var)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADeref (a1: aexp)
  | AAddr (a1: aexp).

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

Inductive aexp_halt: aexp -> Prop :=
  | AH_num : forall n, aexp_halt (ANum n).

Inductive astepR : state -> aexp -> aexp -> Prop :=
  | ASR_Id : forall st X n,
      st (var2addr X) = Some n ->
      astepR st
        (AId X) (ANum n)

  | ASR_Plus1 : forall st a1 a1' a2,
      astepR st
        a1 a1' ->
      astepR st
        (APlus a1 a2) (APlus a1' a2)
  | ASR_Plus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astepR st
        a2 a2' ->
      astepR st
        (APlus a1 a2) (APlus a1 a2')
  | ASR_Plus : forall st n1 n2,
      astepR st
        (APlus (ANum n1) (ANum n2)) (ANum (n1 + n2))

  | ASR_Minus1 : forall st a1 a1' a2,
      astepR st
        a1 a1' ->
      astepR st
        (AMinus a1 a2) (AMinus a1' a2)
  | ASR_Minus2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astepR st
        a2 a2' ->
      astepR st
        (AMinus a1 a2) (AMinus a1 a2')
  | ASR_Minus : forall st n1 n2,
      astepR st
        (AMinus (ANum n1) (ANum n2)) (ANum (n1 - n2))

  | ASR_Mult1 : forall st a1 a1' a2,
      astepR st
        a1 a1' ->
      astepR st
        (AMult a1 a2) (AMult a1' a2)
  | ASR_Mult2 : forall st a1 a2 a2',
      aexp_halt a1 ->
      astepR st
        a2 a2' ->
      astepR st
        (AMult a1 a2) (AMult a1 a2')
  | ASR_Mult : forall st n1 n2,
      astepR st
        (AMult (ANum n1) (ANum n2)) (ANum (n1 * n2))

  | ASR_DerefStep : forall st a1 a1',
      astepR st
        a1 a1' ->
      astepR st
        (ADeref a1) (ADeref a1')
  | ASR_Deref : forall st n n',
      st n = Some n' ->
      astepR st
        (ADeref (ANum n)) (ANum n')

  | ASR_AddrStep : forall st a1 a1',
      astepL st
        a1 a1' ->
      astepR st
        (AAddr a1) (AAddr a1')
  | ASR_Addr : forall st n,
      astepR st
        (AAddr (ADeref (ANum n))) (ANum n)
with astepL : state -> aexp -> aexp -> Prop :=
  | ASL_Id: forall st X,
      astepL st
        (AId X) (ADeref (ANum (var2addr X)))

  | ASL_DerefStep: forall st a1 a1',
      astepR st
        a1 a1' ->
      astepL st
        (ADeref a1) (ADeref a1')
.

(** Then, we can define multi-step relations like we did before. *)

Definition multi_astepR st := clos_refl_trans (astepR st).
Definition multi_astepL st := clos_refl_trans (astepL st).

(** The following tasks require you to show congruence properties of small step
    relations for [AAddr]. Remember that you can use [induction_n1],
    [induction_1n], [etransitivity_n1] and [etransitivity_1n] to automate your
    proof. *)

(** **** Exercise: 2 stars, standard (multi_congr_AAddr) *)
Lemma multi_congr_AAddr: forall st a a',
  multi_astepL st a a' ->
  multi_astepR st (AAddr a) (AAddr a').  
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** How to formally state the connection between the denotational semantics and
    the small step semantics? One direction should be:
        [[
           forall st a n,
             aevalR a st = Some n -> multi_astepR st a (ANum n)
        ]]
    and
        [[
           forall st a n,
             aevalL a st = Some n -> multi_astepL st a (ADeref (ANum n)).
        ]]
    We can prove these properties by induction over [a]. The next task requires
    you to prove the induction step for [AAddr]. *)

(** **** Exercise: 2 stars, standard (semantic_equiv_aexp_AAddr) *)
Lemma semantic_equiv_aexp_AAddr: forall st a
  (IH: forall n: Z, aevalL a st = Some n -> multi_astepL st a (ADeref (ANum n))),
  (forall n: Z, aevalR (AAddr a) st = Some n -> multi_astepR st (AAddr a) (ANum n)).
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

End Task3.

(* 2021-05-17 20:13 *)
