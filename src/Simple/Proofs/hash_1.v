Require Import Simple.Tactics.hash_1.

Set Keyed Unification.
SetDefaultOpaques "Simple".
Opaque N.mul N.modulo.
Opaque arrLookup.

Definition hash_1_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_1 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 1%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Lemma hash_1_top_solver_prf (ll : LedgerLRecord rec) : hash_1_correct_def ll.
  start_proof.
  time hash_1_start.
  destruct_ledger ll.
  time "[simple][topdown][1]" top_down_solver.
Time Qed.

Lemma hash_1_let_form_prf (ll : LedgerLRecord rec) : hash_1_correct_def ll.
  start_proof.
  time hash_1_start.
  destruct_ledger ll.
  time "[simple][letform][1]" let_form_solver.
Time Qed.

Lemma hash_1_bottom_up_prf (ll : LedgerLRecord rec) : hash_1_correct_def ll.
  start_proof.
  time hash_1_start.
  destruct_ledger ll.
  timeout 300 time "[simple][bottomup][1]" bottom_up_goal_solver.
Time Qed.
