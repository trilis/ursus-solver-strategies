Require Export CommonTactics.

Require Import Simple.Simple.
Import Simple.

Require Import Simple.Common.

Module SimpleLedger <: WithLedger.

Definition Ledger := LedgerLRecord rec.

End SimpleLedger.

Module Export ContractTactics := ContractTactics SimpleLedger.


Ltac top_down_solver :=
  clear_unneeded_hyps; repeat match goal with 
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
        | ExecGenDefs.ULValue _ => subst y
        | _ =>
          lazy in H; subst y
      end
  end; lazy; auto.

Ltac convert_to_let_form := 
repeat match goal with 
    | H: ?y = ?t |- _ =>
    is_var y; 
    assert_fails (idtac; multimatch goal with 
        | H2: ?y2 = _ |- _ => 
            match t with 
                | context[y2] => idtac
                | _ => fail
            end
    end);
    let x := fresh "x" in
    set (x := t); replace y with x in *; clear H
end.  
Ltac let_form_solver := clear_unneeded_hyps; convert_to_let_form; lazy; auto.
