Require Export CommonTactics.

Require Import If.If.
Import If.

Require Import If.Common.

Module IfLedger <: WithLedger.

Definition Ledger := LedgerLRecord rec.

End IfLedger.

Module Export ContractTactics := ContractTactics IfLedger.
