Require Export CommonTactics.

Require Import IfAndRecursion.IfAndRecursion.
Import IfAndRecursion.

Require Import IfAndRecursion.Common.

Module IfAndRecursionLedger <: WithLedger.

Definition Ledger := LedgerLRecord rec.

End IfAndRecursionLedger.

Module Export ContractTactics := ContractTactics IfAndRecursionLedger.
