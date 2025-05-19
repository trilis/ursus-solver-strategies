Require Import UrsusEnvironment.Solidity.current.Environment.

Module Type WithLedger.

Axiom Ledger: Type.

End WithLedger.

Module ContractTactics (WL: WithLedger).
Import WL.

Ltac compute_destructed_ledgers := let Ledger' := eval cbv delta [Ledger] in Ledger in compute_destructed_ledgers' Ledger'.
Ltac prepare ll P loc_ := prepare_all ll P; compute_destructed_ledgers loc_.
Ltac prepare_ifs ll P loc_ := prepare_all ll P; compute_destructed_ledgers loc_;
  match goal with 
    | |- _ = ?y => remember y as P eqn:HeqP; lazy in HeqP; subst P
  end; elpi sort_vars -1.

Ltac nested_if_destruct b :=
  lazymatch b with
    | context[if ?b0 then _ else _] => 
      nested_if_destruct b0
    | _ => idtac b; destruct b
    end.

Ltac topdown_lazy' :=
  clear_unneeded_hyps; repeat match reverse goal with 
      | H: ?y = ?t |- _ =>
      idtac y; (match t with 
          | if ?b then _ else _ => 
              let b' := fresh "b'" in
              let Heqb' := fresh "Heqb'" in
              remember b as b' eqn:Heqb'; lazy in Heqb';
              match type of Heqb' with 
                | _ = ?b0 =>
                  nested_if_destruct b0
              end;
              subst b'
          | _ => idtac
      end); 
      match type of t with
        | ULValue _ => subst y
        | _ =>
          lazy in H; subst y
      end
  end.

Ltac topdown_cbv' :=
  clear_unneeded_hyps; repeat match reverse goal with 
      | H: ?y = ?t |- _ =>
      idtac y; (match t with 
          | if ?b then _ else _ => 
              let b' := fresh "b'" in
              let Heqb' := fresh "Heqb'" in
              remember b as b' eqn:Heqb'; cbv in Heqb';
              match type of Heqb' with 
                | _ = ?b0 =>
                  nested_if_destruct b0
              end;
              subst b'
          | _ => idtac
      end); 
      match type of t with
        | ULValue _ => subst y
        | _ =>
          cbv in H; subst y
      end
  end.

Ltac bottomup_naive_lazy' :=
  repeat match goal with 
    | H: ?y = _ |- _ => subst y
  end;
  repeat (match reverse goal with 
  | H: ?y = if ?b then _ else _ |- _ =>
    idtac y;
    let b' := fresh "b'" in
    let Heqb' := fresh "Heqb'" in
    remember b as b' eqn:Heqb'; lazy in Heqb';
    match type of Heqb' with 
      | _ = ?b0 =>
        nested_if_destruct b0
    end;
    subst b'; subst y
end;
repeat (match reverse goal with 
    | H: ?y = ?t |- _ => 
      lazymatch t with 
        | if _ then _ else _ => fail
        | _ => subst y
      end
  end)
).

Ltac bottomup_naive_cbv' :=
  repeat match goal with 
    | H: ?y = _ |- _ => subst y
  end;
  repeat (match reverse goal with 
  | H: ?y = if ?b then _ else _ |- _ =>
    idtac y;
    let b' := fresh "b'" in
    let Heqb' := fresh "Heqb'" in
    remember b as b' eqn:Heqb'; cbv in Heqb';
    match type of Heqb' with 
      | _ = ?b0 =>
        nested_if_destruct b0
    end;
    subst b'; subst y
end;
repeat (match reverse goal with 
    | H: ?y = ?t |- _ => 
      lazymatch t with 
        | if _ then _ else _ => fail
        | _ => subst y
      end
  end)
).

Ltac bottomup_reductions_lazy' :=
  repeat match goal with 
    | H: ?y = ?t |- _ => match t with 
    | if ?b then _ else _ => 
        let b' := fresh "b'" in
        let Heqb' := fresh "Heqb'" in
        remember b as b' eqn:Heqb'; lazy in Heqb';
        match type of Heqb' with 
          | _ = ?b0 =>
            nested_if_destruct b0
        end;
        subst b'
    | _ => idtac
  end; lazy in H; subst y
  end.

Ltac bottomup_reductions_cbv' :=
  repeat match goal with 
    | H: ?y = ?t |- _ => match t with 
    | if ?b then _ else _ => 
        let b' := fresh "b'" in
        let Heqb' := fresh "Heqb'" in
        remember b as b' eqn:Heqb'; cbv in Heqb';
        match type of Heqb' with 
          | _ = ?b0 =>
            nested_if_destruct b0
        end;
        subst b'
    | _ => idtac
  end; cbv in H; subst y
  end.

Ltac native_lazy' := 
clear_unneeded_hyps; repeat match reverse goal with 
    | H: ?y = ?t |- _ =>
    is_var y; 
    match t with 
    | if ?b then _ else _ => 
      fail 1
    | _ =>
        let x := fresh "x" in
        set (x := t); replace y with x in *; clear H
    end
end;
repeat (match reverse goal with 
    | H: ?y = if ?b then _ else _ |- _ =>
      idtac y;
      let b' := fresh "b'" in
      let Heqb' := fresh "Heqb'" in
      remember b as b' eqn:Heqb'; lazy in Heqb';
      match type of Heqb' with 
        | _ = ?b0 =>
          nested_if_destruct b0
      end;
      subst b'; subst y
  end;
  repeat (match reverse goal with 
      | H: ?y = ?t |- _ => 
        lazymatch t with 
          | if _ then _ else _ => fail
          | _ => subst y
        end
    end)
).

Ltac native_cbv' := 
clear_unneeded_hyps; repeat match reverse goal with 
    | H: ?y = ?t |- _ =>
    is_var y; 
    match t with 
    | if ?b then _ else _ => 
      fail 1
    | _ =>
        let x := fresh "x" in
        set (x := t); replace y with x in *; clear H
    end
end;
repeat (match reverse goal with 
    | H: ?y = if ?b then _ else _ |- _ =>
      idtac y;
      let b' := fresh "b'" in
      let Heqb' := fresh "Heqb'" in
      remember b as b' eqn:Heqb'; cbv in Heqb';
      match type of Heqb' with 
        | _ = ?b0 =>
          nested_if_destruct b0
      end;
      subst b'; subst y
  end;
  repeat (match reverse goal with 
      | H: ?y = ?t |- _ => 
        lazymatch t with 
          | if _ then _ else _ => fail
          | _ => subst y
        end
    end)
).

Ltac contractions_typebased :=
  clear_unneeded_hyps; repeat match reverse goal with
    | H: ?y = ?t |- _ =>
    is_var y;
    match t with 
      | if _ then _ else _ => fail 1
      | _ => 
        match type of y with
          | mapping (bytes ** nat) _ => subst y
          | field_type _ => subst y
        end
    end
  end.

Ltac contractions_strong_typebased Ledger :=
  clear_unneeded_hyps; repeat match reverse goal with
    | H: ?y = ?t |- _ =>
    is_var y;
    match t with 
      | if _ then _ else _ => fail 1
      | _ => 
        match type of y with
          | Ledger => fail 1
          | _ => subst y
        end
    end
  end.

Definition wrapper {T: Type} (x: T) : True := I.
Inductive meta :=
  | meta_y: True -> Datatypes.list True -> Datatypes.list True -> meta.
Inductive used :=
  | used_y: True -> used.

Ltac contractions := repeat match goal with 
  | _: ?y1 = ?t1 |- _ =>
    is_var y1;
    match goal with
      | _ := meta_y (wrapper y1) _ _ |- _ => fail 1
      | |- _ => pose (meta_y (wrapper y1) Datatypes.nil Datatypes.nil)
    end
  end;
  repeat match goal with 
    | _: ?y1 = ?t1 |- _ =>
    is_var y1;
    set (l := @Datatypes.nil True);
    match goal with
      | _ := used_y (wrapper y1) |- _ => fail 1
      | |- _ => idtac
    end;
    repeat match goal with 
      | _: ?y2 = ?t2 |- _ =>
        is_var y2;
        match eval cbv delta [l] in l with 
          | context[y2] => fail 1
          | _ => idtac
        end;
        match t1 with 
          | context[y2] =>
            set (l' := Datatypes.cons (wrapper y2) l);
            subst l; rename l' into l;
            match t2 with 
              | if _ then _ else _ => idtac
              | _ => match goal with
                | x := meta_y (wrapper y2) ?l1 ?l2 |- _ =>
                  clear x; pose (meta_y (wrapper y2) l1 (Datatypes.cons (wrapper y1) l2))
              end
            end
        end
    end;
    match goal with
      | x := meta_y (wrapper y1) _ ?l2 |- _ =>
        let l' := eval cbv delta [l] in l in
        clear x; pose (meta_y (wrapper y1) l' l2)
    end;
    clear l;
    pose (used_y (wrapper y1))
  end;
  repeat match goal with 
  | x := used_y _ |- _ => clear x
  end;
  repeat match goal with 
    | x := meta_y (wrapper ?y) ?l1 ?l2 |- _ =>
    match l1 with 
    | Datatypes.cons _ Datatypes.nil =>
      match l2 with 
        | Datatypes.cons _ Datatypes.nil =>
          clear x; subst y
        | _ => clear x
      end
    | _ => clear x
    end
  end.

Ltac contractions_strong := repeat match goal with 
  | _: ?y1 = ?t1 |- _ =>
    is_var y1;
    match goal with
      | _ := meta_y (wrapper y1) _ _ |- _ => fail 1
      | |- _ => pose (meta_y (wrapper y1) Datatypes.nil Datatypes.nil)
    end
  end;
  repeat match goal with 
    | _: ?y1 = ?t1 |- _ =>
    is_var y1;
    set (l := @Datatypes.nil True);
    match goal with
      | _ := used_y (wrapper y1) |- _ => fail 1
      | |- _ => idtac
    end;
    repeat match goal with 
      | _: ?y2 = ?t2 |- _ =>
        is_var y2;
        match eval cbv delta [l] in l with 
          | context[y2] => fail 1
          | _ => idtac
        end;
        match t1 with 
          | context[y2] =>
            set (l' := Datatypes.cons (wrapper y2) l);
            subst l; rename l' into l;
            match t2 with 
              | if _ then _ else _ => idtac
              | _ => match goal with
                | x := meta_y (wrapper y2) ?l1 ?l2 |- _ =>
                  clear x; pose (meta_y (wrapper y2) l1 (Datatypes.cons (wrapper y1) l2))
              end
            end
        end
    end;
    match goal with
      | x := meta_y (wrapper y1) _ ?l2 |- _ =>
        let l' := eval cbv delta [l] in l in
        clear x; pose (meta_y (wrapper y1) l' l2)
    end;
    clear l;
    pose (used_y (wrapper y1))
  end;
  repeat match goal with 
  | x := used_y _ |- _ => clear x
  end;
  repeat match goal with 
    | x := meta_y (wrapper ?y) _ ?l2 |- _ =>
      match l2 with 
        | Datatypes.cons _ Datatypes.nil =>
          clear x; subst y
    | _ => clear x
    end
  end.

Ltac native_lazy := native_lazy'; lazy; auto.
Ltac native_cbv := native_cbv'; cbv; auto.
Ltac native_contractions_typebased_lazy := contractions_typebased; native_lazy'; lazy; auto.
Ltac native_contractions_typebased_cbv := contractions_typebased; native_cbv'; cbv; auto.
Ltac native_contractions_strong_typebased_lazy := let Ledger' := eval cbv delta [Ledger] in Ledger in contractions_strong_typebased Ledger'; native_lazy'; lazy; auto.
Ltac native_contractions_strong_typebased_cbv := let Ledger' := eval cbv delta [Ledger] in Ledger in contractions_strong_typebased Ledger'; native_cbv'; cbv; auto.
Ltac native_contractions_lazy := contractions; native_lazy'; lazy; auto.
Ltac native_contractions_cbv := contractions; native_cbv'; cbv; auto.
Ltac native_contractions_strong_lazy := contractions_strong; native_lazy'; lazy; auto.
Ltac native_contractions_strong_cbv := contractions_strong; native_cbv'; cbv; auto.

Ltac bottomup_naive_lazy := bottomup_naive_lazy'; lazy; auto.
Ltac bottomup_naive_cbv := bottomup_naive_cbv'; cbv; auto.
Ltac bottomup_naive_contractions_typebased_lazy := contractions_typebased; bottomup_naive_lazy'; lazy; auto.
Ltac bottomup_naive_contractions_typebased_cbv := contractions_typebased; bottomup_naive_cbv'; cbv; auto.
Ltac bottomup_naive_contractions_strong_typebased_lazy := let Ledger' := eval cbv delta [Ledger] in Ledger in contractions_strong_typebased Ledger'; bottomup_naive_lazy'; lazy; auto.
Ltac bottomup_naive_contractions_strong_typebased_cbv := let Ledger' := eval cbv delta [Ledger] in Ledger in contractions_strong_typebased Ledger'; bottomup_naive_cbv'; cbv; auto.
Ltac bottomup_naive_contractions_lazy := contractions; bottomup_naive_lazy'; lazy; auto.
Ltac bottomup_naive_contractions_cbv := contractions; bottomup_naive_cbv'; cbv; auto.
Ltac bottomup_naive_contractions_strong_lazy := contractions_strong; bottomup_naive_lazy'; lazy; auto.
Ltac bottomup_naive_contractions_strong_cbv := contractions_strong; bottomup_naive_cbv'; cbv; auto.

Ltac bottomup_reductions_lazy := bottomup_reductions_lazy'; lazy; auto.
Ltac bottomup_reductions_cbv := bottomup_reductions_cbv'; cbv; auto.
Ltac bottomup_reductions_contractions_typebased_lazy := contractions_typebased; bottomup_reductions_lazy'; lazy; auto.
Ltac bottomup_reductions_contractions_typebased_cbv := contractions_typebased; bottomup_reductions_cbv'; cbv; auto.
Ltac bottomup_reductions_contractions_strong_typebased_lazy := let Ledger' := eval cbv delta [Ledger] in Ledger in contractions_strong_typebased Ledger'; bottomup_reductions_lazy'; lazy; auto.
Ltac bottomup_reductions_contractions_strong_typebased_cbv := let Ledger' := eval cbv delta [Ledger] in Ledger in contractions_strong_typebased Ledger'; bottomup_reductions_cbv'; cbv; auto.
Ltac bottomup_reductions_contractions_lazy := contractions; bottomup_reductions_lazy'; lazy; auto.
Ltac bottomup_reductions_contractions_cbv := contractions; bottomup_reductions_cbv'; cbv; auto.
Ltac bottomup_reductions_contractions_strong_lazy := contractions_strong; bottomup_reductions_lazy'; lazy; auto.
Ltac bottomup_reductions_contractions_strong_cbv := contractions_strong; bottomup_reductions_cbv'; cbv; auto.

Ltac topdown_lazy := topdown_lazy'; lazy; auto.
Ltac topdown_cbv := topdown_cbv'; cbv; auto.
Ltac topdown_contractions_typebased_lazy := contractions_typebased; topdown_lazy'; lazy; auto.
Ltac topdown_contractions_typebased_cbv := contractions_typebased; topdown_cbv'; cbv; auto.
Ltac topdown_contractions_strong_typebased_lazy := let Ledger' := eval cbv delta [Ledger] in Ledger in contractions_strong_typebased Ledger'; topdown_lazy'; lazy; auto.
Ltac topdown_contractions_strong_typebased_cbv := let Ledger' := eval cbv delta [Ledger] in Ledger in contractions_strong_typebased Ledger'; topdown_cbv'; cbv; auto.
Ltac topdown_contractions_lazy := contractions; topdown_lazy'; lazy; auto.
Ltac topdown_contractions_cbv := contractions; topdown_cbv'; cbv; auto.
Ltac topdown_contractions_strong_lazy := contractions_strong; topdown_lazy'; lazy; auto.
Ltac topdown_contractions_strong_cbv := contractions_strong; topdown_cbv'; cbv; auto.

Ltac fast_solver := native_contractions_strong_typebased_lazy.

Ltac process_message_flags := let Ledger' := eval cbv delta [Ledger] in Ledger in process_message_flags' Ledger'.
Ltac solve_full_error := let Ledger' := eval cbv delta [Ledger] in Ledger in solve_full_error' Ledger'.
Ltac try_auto_pure := let Ledger' := eval cbv delta [Ledger] in Ledger in try_auto_pure' Ledger'.

(* rewrite abtract tactic declared in CommonTactics *)
Ltac equalify_arguments := let Ledger' := eval cbv delta [Ledger] in Ledger in equalify_arguments' Ledger'.
Ltac unify_condition := let Ledger' := eval cbv delta [Ledger] in Ledger in unify_condition' Ledger'.
Ltac equalify_particular_arguments := let Ledger' := eval cbv delta [Ledger] in Ledger in equalify_particular_arguments' Ledger'.
Ltac find_destructed_ledger_subst_compute := let Ledger' := eval cbv delta [Ledger] in Ledger in find_destructed_ledger_subst_compute' Ledger'.
(* Ltac process_wellformed := let Ledger' := eval cbv delta [Ledger] in Ledger in process_wellformed' Ledger'. *)

Ltac process_multiexists := let Ledger' := eval cbv delta [Ledger] in Ledger in process_multiexists' Ledger'.

End ContractTactics.

Tactic Notation "subst_needed" "in" hyp(H) :=
  idtac "substing needed in" H;
  repeat match reverse goal with
    | H' : ?y = _ |- _ =>
        match goal with
        | H'' : ?x |- _ =>
            match H'' with
            | H =>
                lazymatch H' with
                | H => fail
                | _ => match x with
                      | context [y] =>
                          subst y
                      end
                end
            end
        end
    end.

Ltac subst_needed :=
  idtac "substing needed in goal";
  clear_unneeded_hyps;
  repeat match reverse goal with
    | H : ?y = _ |- context [?y] =>
        subst y
    end.