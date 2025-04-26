Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import SpecLang.

Module Type WithLedger.

Axiom Ledger: Type.

End WithLedger.

Module ContractTactics (WL: WithLedger).
Import WL.
Ltac compute_destructed_ledgers := let Ledger' := eval cbv delta [Ledger] in Ledger in compute_destructed_ledgers' Ledger'.
Ltac prepare ll P loc_ := prepare_all ll P; compute_destructed_ledgers loc_.

Ltac topdown :=
  clear_unneeded_hyps; repeat match reverse goal with 
      | H: ?y = ?t |- _ =>
      idtac y; (match t with 
          | if ?b then _ else _ => destruct b
          | _ => idtac
      end); 
      match type of t with
        | ULValue _ => subst y
        | _ =>
          lazy in H; subst y
      end
  end; lazy; auto.

Ltac bottomup_naive :=
  repeat match goal with 
    | H: ?y = _ |- _ => subst y
  end.

Ltac bottomup_reductions :=
  repeat match goal with 
    | H: ?y = _ |- _ => lazy in H; subst y
  end.

Ltac native := 
clear_unneeded_hyps; repeat match reverse goal with 
    | H: ?y = ?t |- _ =>
    is_var y; 
    match t with 
    | if ?b then _ else _ => 
      let b' := fresh "b'" in
      let Heqb' := fresh "Heqb'" in
      remember b as b' eqn:Heqb'; lazy in Heqb'; 
      match type of Heqb' with
        | b' = ?t => destruct t 
      end; subst b'
    | _ =>
        let x := fresh "x" in
        set (x := t); replace y with x in *; clear H
    end
end.

Ltac contractions_typebased :=
  clear_unneeded_hyps; repeat match reverse goal with
    | H: ?y = _ |- _ =>
    is_var y;
    match type of y with
      | mapping (bytes ** nat) _ => subst y
      | field_type _ => subst y
      | _ => fail 1
    end
  end.

Ltac contractions_strong_typebased Ledger :=
  clear_unneeded_hyps; repeat match reverse goal with
    | H: ?y = _ |- _ =>
    is_var y;
    match type of y with
      | Ledger => fail 1
      | _ => subst y
    end
  end.

(* for ifs *)
(*time (clear_unneeded_hyps; repeat match reverse goal with
    | H: ?y = ?t |- _ =>
    is_var y;
    match t with 
      | if ?b then _ else _ =>
        fail 1 
      | _ =>
        match type of y with
          | LedgerLRecord rec => fail 1
          | _ => subst y
        end
    end
  end;
  repeat match reverse goal with 
      | H: ?y = ?t |- _ => 
        is_var y;
        match type of t with 
        | LedgerLRecord rec => idtac 
        | _ => fail 1
        end;
        assert_fails (idtac; multimatch goal with 
          | H2: ?y2 = _ |- _ => 
              match t with 
                  | context[y2] => idtac
                  | _ => fail
              end
      end); idtac y; lazy in H; subst y
  end;
  repeat match reverse goal with 
    | H: ?y = ?t |- _ => 
        is_var y;
        match t with 
        | if ?b then _ else _ => 
          idtac y;
          let b' := fresh "b'" in
          let Heqb' := fresh "Heqb'" in
          remember b as b' eqn:Heqb'; lazy in Heqb'; 
          match type of Heqb' with
            | b' = ?t => destruct t 
          end; subst b'
        | _ => fail 1
        end
  end;
  repeat match reverse goal with 
      | H: ?y = ?t |- _ => 
        is_var y;
        assert_fails (idtac; multimatch goal with 
          | H2: ?y2 = _ |- _ => 
              match t with 
                  | context[y2] => idtac
                  | _ => fail
              end
      end); idtac y; lazy in H; subst y
  end; lazy; auto).*)

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

Ltac native_lazy := native; lazy; auto.
Ltac native_cbv := native; cbv; auto.
Ltac native_contractions_typebased_lazy := contractions_typebased; native; lazy; auto.
Ltac native_contractions_typebased_cbv := contractions_typebased; native; cbv; auto.
Ltac native_contractions_strong_typebased_lazy := let Ledger' := eval cbv delta [Ledger] in Ledger in contractions_strong_typebased Ledger'; native; lazy; auto.
Ltac native_contractions_strong_typebased_cbv := let Ledger' := eval cbv delta [Ledger] in Ledger in contractions_strong_typebased Ledger'; native; cbv; auto.
Ltac native_contractions_lazy := contractions; native; lazy; auto.
Ltac native_contractions_cbv := contractions; native; cbv; auto.
Ltac native_contractions_strong_lazy := contractions_strong; native; lazy; auto.
Ltac native_contractions_strong_cbv := contractions_strong; native; cbv; auto.

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

Ltac bottomup_reductions_lazy := bottomup_reductions; lazy; auto.
Ltac bottomup_reductions_cbv := bottomup_reductions; cbv; auto.
Ltac bottomup_reductions_contractions_typebased_lazy := contractions_typebased; bottomup_reductions; lazy; auto.
Ltac bottomup_reductions_contractions_typebased_cbv := contractions_typebased; bottomup_reductions; cbv; auto.
Ltac bottomup_reductions_contractions_strong_typebased_lazy := let Ledger' := eval cbv delta [Ledger] in Ledger in contractions_strong_typebased Ledger'; bottomup_reductions; lazy; auto.
Ltac bottomup_reductions_contractions_strong_typebased_cbv := let Ledger' := eval cbv delta [Ledger] in Ledger in contractions_strong_typebased Ledger'; bottomup_reductions; cbv; auto.
Ltac bottomup_reductions_contractions_lazy := contractions; bottomup_reductions; lazy; auto.
Ltac bottomup_reductions_contractions_cbv := contractions; bottomup_reductions; cbv; auto.
Ltac bottomup_reductions_contractions_strong_lazy := contractions_strong; bottomup_reductions; lazy; auto.
Ltac bottomup_reductions_contractions_strong_cbv := contractions_strong; bottomup_reductions; cbv; auto.

Ltac topdown_lazy := topdown; lazy; auto.
Ltac topdown_cbv := topdown; cbv; auto.
Ltac topdown_contractions_typebased_lazy := contractions_typebased; topdown; lazy; auto.
Ltac topdown_contractions_typebased_cbv := contractions_typebased; topdown; cbv; auto.
Ltac topdown_contractions_strong_typebased_lazy := let Ledger' := eval cbv delta [Ledger] in Ledger in contractions_strong_typebased Ledger'; topdown; lazy; auto.
Ltac topdown_contractions_strong_typebased_cbv := let Ledger' := eval cbv delta [Ledger] in Ledger in contractions_strong_typebased Ledger'; topdown; cbv; auto.
Ltac topdown_contractions_lazy := contractions; topdown; lazy; auto.
Ltac topdown_contractions_cbv := contractions; topdown; cbv; auto.
Ltac topdown_contractions_strong_lazy := contractions_strong; topdown; lazy; auto.
Ltac topdown_contractions_strong_cbv := contractions_strong; topdown; cbv; auto.

End ContractTactics.
