Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import SpecLang.

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

(* Ltac process_wellformed' Ledger C x prf :=
  multidestruct C;
  subst x; (* the term structured after decomposition *)
  match goal with
  | H: ?y = ?Y |- _ => let t := type of y in 
                          match Y with
                          | context [decode] =>
                              lazymatch t with
                              | @ControlResultP _ _ _ _ => eassert (y = ControlValue _ _);
                                                            [ > with_strategy opaque 
                                                            [unMaybe encode decode 
                                                            pair_storeable uint_storeable address_storeable
                                                            pair_loadable uint_loadable address_loadable] 
                                                            bottom_up_goal_solver' Ledger;
                                                            setoid_rewrite prf; [| try assumption ..];
                                                            reflexivity | clear H; try (setoid_rewrite prf; [ (* simpl *) | try assumption ..]) ]
                              | _ => idtac "do not have edefault for" t 
                              end   
                          end
  | _ => idtac "no decode found"
  end. *)

Module Type WithLedger.

Axiom Ledger: Type.

End WithLedger.

Module ContractTactics (WL: WithLedger).
Import WL.

Ltac new_top_down_solver' :=
  clear_unneeded_hyps; repeat match reverse goal with
    | H: ?y = ?t |- _ =>
    is_var y;
    match type of y with
      | Ledger => fail 1
      | _ => subst y
    end
    end;
    repeat match reverse goal with 
      | H: ?y = ?t |- _ => 
        is_var y; lazy in H; 
        match t with 
          | if ?b then _ else _ =>
            destruct b
          | _ => subst y
        end
  end; lazy; auto.

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

Ltac new_top_down_solver := let Ledger' := eval cbv delta [Ledger] in Ledger in new_top_down_solver' Ledger'.
Ltac bottom_up_goal_solver := let Ledger' := eval cbv delta [Ledger] in Ledger in bottom_up_goal_solver' Ledger'.
Ltac process_message_flags := let Ledger' := eval cbv delta [Ledger] in Ledger in process_message_flags' Ledger'.
Ltac compute_destructed_ledgers := let Ledger' := eval cbv delta [Ledger] in Ledger in compute_destructed_ledgers' Ledger'.
Ltac solve_full_error := let Ledger' := eval cbv delta [Ledger] in Ledger in solve_full_error' Ledger'.
Ltac try_auto_pure := let Ledger' := eval cbv delta [Ledger] in Ledger in try_auto_pure' Ledger'.

(* rewrite abtract tactic declared in CommonTactics *)
Ltac equalify_arguments := let Ledger' := eval cbv delta [Ledger] in Ledger in equalify_arguments' Ledger'.
Ltac unify_condition := let Ledger' := eval cbv delta [Ledger] in Ledger in unify_condition' Ledger'.
Ltac equalify_particular_arguments := let Ledger' := eval cbv delta [Ledger] in Ledger in equalify_particular_arguments' Ledger'.
Ltac find_destructed_ledger_subst_compute := let Ledger' := eval cbv delta [Ledger] in Ledger in find_destructed_ledger_subst_compute' Ledger'.
(* Ltac process_wellformed := let Ledger' := eval cbv delta [Ledger] in Ledger in process_wellformed' Ledger'.
 *)
Ltac process_multiexists := let Ledger' := eval cbv delta [Ledger] in Ledger in process_multiexists' Ledger'.

End ContractTactics.

Ltac top_down_solver :=
  clear_unneeded_hyps; repeat match reverse goal with 
      | H: ?y = ?t |- _ =>
      idtac y; (match t with 
          | context[if ?b then _ else _] => destruct b
          | _ => idtac
      end); 
      match type of t with
        | ULValue _ => subst y
        | _ =>
          lazy in H; subst y
      end
  end; lazy; auto.

Ltac let_form_solver := 
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
end; lazy; auto. 

Axiom false_: False.

Ltac abort := exfalso; exact false_.

Definition wrapper {T: Type} (x: T) : True := I.
Inductive meta :=
  | meta_y: True -> Datatypes.list True -> Datatypes.list True -> meta.

Ltac do_rewrites m H :=
  match m with
    | Datatypes.cons (wrapper ?y2) ?ms =>
      match goal with 
        | H2: ?y2 = _ |- _ =>
          rewrite H in H2; do_rewrites ms H  
      end
    | Datatypes.nil => idtac
  end.

(*Ltac topdown_graph :=
  repeat match goal with 
    | _: ?y1 = ?t1 |- _ =>
      is_var y1;
      match goal with
        | _ := meta_y (wrapper y1) _ _ |- _ => fail 1
        | |- _ => idtac
      end;
      set (l := @Datatypes.nil True);
      set (l2 := @Datatypes.nil True);
      repeat match goal with 
        | H2: ?y2 = ?t2 |- _ =>
          is_var y2;
          match eval cbv delta [l] in l with 
            | context[y2] => fail 1
            | _ => idtac
          end;
          match t1 with 
            | context[y2] =>
              set (l' := Datatypes.cons (wrapper y2) l);
              subst l; rename l' into l
          end
      end;
      repeat match goal with 
        | H2: ?y2 = ?t2 |- _ =>
          is_var y2;
          match eval cbv delta [l2] in l2 with 
            | context[y2] => fail 1
            | _ => idtac
          end;
          match t2 with 
            | context[y1] =>
              set (l2' := Datatypes.cons (wrapper y2) l2);
              subst l2; rename l2' into l2
          end
      end;
      pose (meta_y (wrapper y1) l l2);
      subst l; subst l2
  end;
  clear_unneeded_hyps; repeat match reverse goal with 
      | H: ?y = ?t |- _ =>
      assert_fails (idtac; multimatch goal with 
          | H2: ?y2 = _ |- _ => 
              match t with 
                  | context[y2] => idtac
                  | _ => fail
              end
      end);
      idtac y; (match t with 
          | if ?b then _ else _ => destruct b
          | _ => idtac
      end); 
      match type of y with
        | LedgerLRecord rec => cbv in H; subst y
        | _ => 
          match goal with
          | _ := meta_y (wrapper y) _ (Datatypes.nil) |- _ =>
            repeat rewrite H; clear H
          | _ : meta_y (wrapper y) _ (Datatypes.cons ?y2 Datatypes.nil) |- _ =>
            match reverse goal with
              | H2: ?y2 = _ |- _ =>
                rewrite H in H2; clear H
            end
          | _ := meta_y (wrapper y) _ ?l |- _ =>
            subst y
          end
      end
  end; lazy; auto.*)