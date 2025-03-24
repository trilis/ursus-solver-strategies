Require Export CommonTactics.

Require Import SimpleContract.SimpleContract.
Import SimpleContract.

Require Import SimpleContract.Common.

Module SimpleContractLedger <: WithLedger.

Definition Ledger := LedgerLRecord rec.

End SimpleContractLedger.

Module Export ContractTactics := ContractTactics SimpleContractLedger.
