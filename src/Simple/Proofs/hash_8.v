Require Import Simple.Tactics.hash_8.

Set Keyed Unification.
SetDefaultOpaques "Simple".
Opaque N.mul N.modulo.
Opaque arrLookup.

Definition hash_8_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_8 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 8%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Lemma hash_8_top_solver_prf (ll : LedgerLRecord rec) : hash_8_correct_def ll.
  start_proof.
  time hash_8_start.
  destruct_ledger ll.
  time "[simple][topdown][8]" top_down_solver.
Time Qed.

Lemma hash_8_let_form_prf (ll : LedgerLRecord rec) : hash_8_correct_def ll.
  start_proof.
  time hash_8_start.
  destruct_ledger ll.
  time "[simple][letform][8]" let_form_solver.
Time Qed.

Lemma hash_8_bottom_up_prf (ll : LedgerLRecord rec) : hash_8_correct_def ll.
  start_proof.
  time hash_8_start.
  destruct_ledger ll.
  time "[simple][bottomup][8]" timeout 300 bottom_up_goal_solver.
Time Qed.
