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


Ltac new_top_down_solver' Ledger :=
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
          | if ?b then _ else _ => lazy in H; match reverse goal with
            | H' : y = if ?b' then _ else _ |- _ => destruct b'
            end
          | _ => idtac
      end); 
      (match type of y with
        | Ledger => idtac "LEDGER"; lazy in H; subst y
        | ULValue _ => idtac "ULVALUE"; subst y
        | _ =>
      match reverse goal with 
        | H2: ?y2 = ?t2 |- _ =>
          match t2 with
            | context[y] => (rewrite H in H2; clear H; clear y; idtac "EASY") ||
              (lazy in H; subst y)
            | _ => fail
          end
      end
      end) || (lazy in H; subst y)
  end; lazy; auto.

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
      assert_fails (idtac; multimatch goal with 
          | H2: ?y2 = _ |- _ => 
              match t with 
                  | context[y2] => idtac
                  | _ => fail
              end
      end);
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
    assert_fails (idtac; multimatch goal with 
        | H2: ?y2 = _ |- _ => 
            match t with 
                | context[y2] => idtac
                | _ => fail
            end
    end);
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