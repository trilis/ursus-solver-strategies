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
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  time "[simple][topdown][8]" top_down_solver.
Time Qed.

Lemma hash_8_let_form_prf (ll : LedgerLRecord rec) : hash_8_correct_def ll.
  start_proof.
  time hash_8_start.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  time "[simple][letform][8]" let_form_solver.
Time Qed.

Lemma hash_8_bottom_up_prf (ll : LedgerLRecord rec) : hash_8_correct_def ll.
  start_proof.
  time hash_8_start.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  try time "[simple][bottomup][8]" timeout 300 bottom_up_goal_solver; abort.
Time Qed.

Lemma hash_8_new_top_solver_prf (ll : LedgerLRecord rec) : hash_8_correct_def ll.
  start_proof.
  time hash_8_start.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  time "[simple][newtopdown][8]" new_top_down_solver.
Time Qed.
