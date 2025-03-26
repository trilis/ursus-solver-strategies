Require Import Simple.Tactics.hash_4.

Set Keyed Unification.
SetDefaultOpaques "Simple".
Opaque N.mul N.modulo.
Opaque arrLookup.

Definition hash_4_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_4 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 4%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Lemma hash_4_top_solver_prf (ll : LedgerLRecord rec) : hash_4_correct_def ll.
  start_proof.
  time hash_4_start.
  destruct_ledger ll.
  time "[simple][topdown][4]" top_down_solver.
Time Qed.

Lemma hash_4_let_form_prf (ll : LedgerLRecord rec) : hash_4_correct_def ll.
  start_proof.
  time hash_4_start.
  destruct_ledger ll.
  time "[simple][letform][4]" let_form_solver.
Time Qed.

Lemma hash_4_bottom_up_prf (ll : LedgerLRecord rec) : hash_4_correct_def ll.
  start_proof.
  time hash_4_start.
  destruct_ledger ll.
  timeout 300 time "[simple][bottomup][4]" bottom_up_goal_solver.
Time Qed.
