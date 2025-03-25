Require Export CommonTactics.

Require Import Recursion.Recursion.
Import Recursion.

Require Import Recursion.Common.

Module RecursionLedger <: WithLedger.

Definition Ledger := LedgerLRecord rec.

End RecursionLedger.

Module Export ContractTactics := ContractTactics RecursionLedger.
