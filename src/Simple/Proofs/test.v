Require Import Simple.Tactics.test.

Set Keyed Unification.
SetDefaultOpaques "Simple".
Opaque N.mul N.modulo.
Opaque arrLookup.

Definition test_correct_def (ll: LedgerLRecord rec) (a b : uint64): Prop.
execs0 (test rec def a b) : ll | "result" -> l1 | "result".
con (result' = xIntMinus (xIntPlus result a) b).
Defined.

Lemma test_top_solver_prf (ll: LedgerLRecord rec) (a b : uint64): test_correct_def ll a b.
  start_proof.
  time test_start.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  continue_all @plusassign @minusassign.
  time "[simple][topdown][test]" top_down_solver.
Time Qed.