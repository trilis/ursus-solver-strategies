Require Import Simple.Tactics.hash_10.

Set Keyed Unification.
SetDefaultOpaques "Simple".
Opaque N.mul N.modulo.
Opaque arrLookup.

Definition hash_10_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_10 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 10%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Lemma hash_10_top_solver_prf (ll : LedgerLRecord rec) : hash_10_correct_def ll.
  start_proof.
  time hash_10_start.
  destruct_ledger ll.
  time "[simple][topdown][10]" top_down_solver.
Time Qed.

Lemma hash_10_let_form_prf (ll : LedgerLRecord rec) : hash_10_correct_def ll.
  start_proof.
  time hash_10_start.
  destruct_ledger ll.
  time "[simple][letform][10]" let_form_solver.
Time Qed.

Lemma hash_10_bottom_up_prf (ll : LedgerLRecord rec) : hash_10_correct_def ll.
  start_proof.
  time hash_10_start.
  destruct_ledger ll.
  timeout 300 time "[simple][bottomup][10]" bottom_up_goal_solver.
Time Qed.
