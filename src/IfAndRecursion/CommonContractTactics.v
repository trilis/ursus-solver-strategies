Require Export CommonTactics.

Require Import IfAndRecursion.IfAndRecursion.
Import IfAndRecursion.

Require Import IfAndRecursion.Common.

Module IfAndRecursionLedger <: WithLedger.

Definition Ledger := LedgerLRecord rec.

End IfAndRecursionLedger.

Module Export ContractTactics := ContractTactics IfAndRecursionLedger.

Ltac preprocess_ifs :=
  repeat match reverse goal with 
  | H: context[if ?b then _ else _] |- _ =>
    match goal with 
      | H0: b = ?t |- _=> repeat (
        match goal with 
          | _: b = ?t' |- _ => 
            match goal with
              | H: ?y = _ |- _ =>
                match t' with 
                  | context[y] => 
                    rewrite H in H0
                end
            end
        end
      ); lazy in H0; match type of H0 with 
        | ?x = true => subst x
        | ?x = false => subst x
        | _ => rewrite <- H0; clear H0; destruct b
        end
    end
end.


Ltac bottom_up_goal_solver' := preprocess_ifs; bottom_up_goal_solver.
