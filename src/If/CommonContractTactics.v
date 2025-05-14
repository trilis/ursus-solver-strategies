Require Export CommonTactics.
Require Import UrsusEnvironment.Solidity.current.Environment.

Require Import If.If.
Import If.

Require Import If.Common.

Module IfLedger <: WithLedger.

Definition Ledger := LedgerLRecord rec.

End IfLedger.

Module Export ContractTactics := ContractTactics IfLedger.

Ltac preprocess_ifs :=
    repeat match goal with 
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
        ); lazy in H0; rewrite <- H0; clear H0
      end
  end.
