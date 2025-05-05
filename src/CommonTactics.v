Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import SpecLang.

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
  end.

Ltac topdown_lazy' :=
  clear_unneeded_hyps; repeat match reverse goal with 
      | H: ?y = ?t |- _ =>
      idtac y; (match t with 
          | if _ then _ else _ => 
            lazy in H; match type of H with 
              | _ = if ?b then _ else _ =>
                destruct b
            end
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
          | if _ then _ else _ => 
            cbv in H; match type of H with 
              | _ = if ?b then _ else _ =>
                destruct b
            end
          | _ => idtac
      end); 
      match type of t with
        | ULValue _ => subst y
        | _ =>
          cbv in H; subst y
      end
  end.

Ltac bottomup_naive :=
  repeat match goal with 
    | H: ?y = _ |- _ => subst y
  end.

Ltac bottomup_reductions_lazy' :=
  repeat match goal with 
    | H: ?y = _ |- _ => lazy in H; subst y
  end.

Ltac bottomup_reductions_cbv' :=
  repeat match goal with 
    | H: ?y = _ |- _ => cbv in H; subst y
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
repeat match reverse goal with 
  | H: ?y = if ?b then _ else _ |- _ =>
    let b' := fresh "b'" in
    let Heqb' := fresh "Heqb'" in
    remember b as b' eqn:Heqb'; lazy in Heqb'; 
    match type of Heqb' with
      | b' = ?t => destruct t 
    end; subst b'; subst y
end.

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
repeat match reverse goal with 
  | H: ?y = if ?b then _ else _ |- _ =>
    let b' := fresh "b'" in
    let Heqb' := fresh "Heqb'" in
    remember b as b' eqn:Heqb'; cbv in Heqb'; 
    match type of Heqb' with
      | b' = ?t => destruct t 
    end; subst b'; subst y
end.

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
      | _: ?y2 = _ |- _ =>
        is_var y2;
        match eval cbv delta [l] in l with 
          | context[y2] => fail 1
          | _ => idtac
        end;
        match t1 with 
          | context[y2] =>
            set (l' := Datatypes.cons (wrapper y2) l);
            subst l; rename l' into l;
            match goal with
              | x := meta_y (wrapper y2) ?l1 ?l2 |- _ =>
                clear x; pose (meta_y (wrapper y2) l1 (Datatypes.cons (wrapper y1) l2))
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
      | _: ?y2 = _ |- _ =>
        is_var y2;
        match eval cbv delta [l] in l with 
          | context[y2] => fail 1
          | _ => idtac
        end;
        match t1 with 
          | context[y2] =>
            set (l' := Datatypes.cons (wrapper y2) l);
            subst l; rename l' into l;
            match goal with
              | x := meta_y (wrapper y2) ?l1 ?l2 |- _ =>
                clear x; pose (meta_y (wrapper y2) l1 (Datatypes.cons (wrapper y1) l2))
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

Ltac bottomup_naive_lazy := bottomup_naive; lazy; auto.
Ltac bottomup_naive_cbv := bottomup_naive; cbv; auto.
Ltac bottomup_naive_contractions_typebased_lazy := contractions_typebased; bottomup_naive; lazy; auto.
Ltac bottomup_naive_contractions_typebased_cbv := contractions_typebased; bottomup_naive; cbv; auto.
Ltac bottomup_naive_contractions_strong_typebased_lazy := let Ledger' := eval cbv delta [Ledger] in Ledger in contractions_strong_typebased Ledger'; bottomup_naive; lazy; auto.
Ltac bottomup_naive_contractions_strong_typebased_cbv := let Ledger' := eval cbv delta [Ledger] in Ledger in contractions_strong_typebased Ledger'; bottomup_naive; cbv; auto.
Ltac bottomup_naive_contractions_lazy := contractions; bottomup_naive; lazy; auto.
Ltac bottomup_naive_contractions_cbv := contractions; bottomup_naive; cbv; auto.
Ltac bottomup_naive_contractions_strong_lazy := contractions_strong; bottomup_naive; lazy; auto.
Ltac bottomup_naive_contractions_strong_cbv := contractions_strong; bottomup_naive; cbv; auto.

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

End ContractTactics.
