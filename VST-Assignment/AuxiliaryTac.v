Require Import VST.floyd.proofauto.

Ltac field_address_solver :=
  match goal with
  | |- @eq val ?p (field_address _ _ ?p) => idtac
  | |- @eq val (offset_val _ ?p) (field_address _ _ ?p) => idtac
  | |- @eq val (field_address _ _ ?p) ?p => idtac
  | |- @eq val (field_address _ _ ?p) (offset_val _ ?p) => idtac
  | _ => fail 1 "The proof goal is not in a form of (p = field_address _ _ p) or (offset_val _ p = field_address _ _ p)"
  end;
  unfold field_address; simpl;
  (rewrite if_true by auto with field_compatible || fail 1 "Not enough field_compatible information to derive the equality.");
  rewrite ? isptr_offset_val_zero; auto.

Ltac check_vl_eq_args ::=
first [ 
   cbv beta; go_lower;
   repeat (( simple apply derives_extract_prop
                || simple apply derives_extract_prop');
                fancy_intros true);
   gather_prop;
   repeat (( simple apply derives_extract_prop
                || simple apply derives_extract_prop');
                fancy_intros true);
 repeat erewrite unfold_reptype_elim in * by reflexivity;
   try autorewrite with entailer_rewrite in *;
   simpl; auto;
   saturate_local;
 apply prop_right;
 match goal with
 | |- ?A = ?B =>
    unify (Datatypes.length A) (Datatypes.length B)
 | |- @eq (list val) _ _ =>
    fail 100 "Length of PARAMS list is not equal to the number of formal parameters of the funsig"
 | |- _ => fail 100 "Mysterious error in check_vl_eq_args"
 end;    
 repeat match goal with |- _ :: _ = _ :: _ => f_equal end;
 normalize;
 unfold field_address, field_address0;
 rewrite if_true; auto;
 auto with field_compatible;
 match goal with |- ?G => 
  match G with
  | field_compatible0 _ _ _ => idtac
  | field_compatible _ _ _ => idtac
  end;
  fail 100 "Before forward_call, assert and prove" G
 end
  | idtac (*alternative: fail 99 "Fail in tactic check_vl_eq_args"*)] .

Ltac handle_force_val :=
  match goal with
  | |- context [force_val ?A] => simpl (force_val A)
  | |- context [firstn ?A ?B] => simpl (firstn A B)
  | _ => idtac
  end.

Ltac entbang ::=
 intros;
 try match goal with POSTCONDITION := @abbreviate ret_assert _ |- _ =>
        clear POSTCONDITION
      end;
 try match goal with MORE_COMMANDS := @abbreviate statement _ |- _ =>
        clear MORE_COMMANDS
      end;
 match goal with
 | |- local _ && ?P |-- _ => clean_up_stackframe; go_lower; try apply empTrue
 | |- ?P |-- _ =>
    match type of P with
    | ?T => unify T mpred; pull_out_props
    end
 | |- _ => fail "The entailer tactic works only on entailments  _ |-- _ "
 end;
 repeat match goal with
        | |- context [force_val (sem_binary_operation' ?op ?t1 ?t2 ?v1 ?v2)] =>
          progress 
              simpl  (* This simpl is safe, because its argument is not
                           arbitrarily complex user expressions, it is ASTs
                           produced by clightgen *)
                (force_val (sem_binary_operation' op t1 t2 v1 v2))
        end;
 simpl  (* This simpl is safe, because its argument is not
                           arbitrarily complex user expressions, it is ASTs
                           produced by clightgen *)
        sem_cast;
 saturate_local;
 ent_iter;
 repeat change (mapsto_memory_block.spacer _ _ _ _) with emp;
 first [ contradiction
        | simple apply prop_right; handle_force_val; my_auto
        | match goal with |- ?Q |-- !! _ && ?Q' => constr_eq  Q Q';
                      simple apply prop_and_same_derives'; handle_force_val; my_auto
          end
        | simple apply andp_right;
            [apply prop_right; handle_force_val; my_auto 
            | cancel; rewrite <- ?sepcon_assoc; autorewrite with norm ]
        | seplog_tactics.normalize; cancel; rewrite <- ?sepcon_assoc
        ].
