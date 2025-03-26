Require Import Simple.Tactics.hash_9.

Set Keyed Unification.
SetDefaultOpaques "Simple".
Opaque N.mul N.modulo.
Opaque arrLookup.

Definition hash_9_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_9 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 9%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Lemma hash_9_top_solver_prf (ll : LedgerLRecord rec) : hash_9_correct_def ll.
  start_proof.
  time hash_9_start.
  destruct_ledger ll.
  time "[simple][topdown][9]" top_down_solver.
Time Qed.

Lemma hash_9_let_form_prf (ll : LedgerLRecord rec) : hash_9_correct_def ll.
  start_proof.
  time hash_9_start.
  destruct_ledger ll.
  time "[simple][letform][9]" let_form_solver.
Time Qed.

Lemma hash_9_bottom_up_prf (ll : LedgerLRecord rec) : hash_9_correct_def ll.
  start_proof.
  time hash_9_start.
  destruct_ledger ll.
  timeout 300 time "[simple][bottomup][9]" bottom_up_goal_solver.
Time Qed.
