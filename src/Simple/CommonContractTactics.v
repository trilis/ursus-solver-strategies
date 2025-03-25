Require Export CommonTactics.

Require Import Simple.Simple.
Import Simple.

Require Import Simple.Common.

Module SimpleLedger <: WithLedger.

Definition Ledger := LedgerLRecord rec.

End SimpleLedger.

Module Export ContractTactics := ContractTactics SimpleLedger.
