Require Import Simple.Tactics.hash_7.

Set Keyed Unification.
SetDefaultOpaques "Simple".
Opaque N.mul N.modulo.
Opaque arrLookup.

Definition hash_7_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_7 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 7%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Lemma hash_7_top_solver_prf (ll : LedgerLRecord rec) : hash_7_correct_def ll.
  start_proof.
  time hash_7_start.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  time "[simple][topdown][7]" top_down_solver.
Time Qed.

Lemma hash_7_let_form_prf (ll : LedgerLRecord rec) : hash_7_correct_def ll.
  start_proof.
  time hash_7_start.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  time "[simple][letform][7]" let_form_solver.
Time Qed.

Lemma hash_7_bottom_up_prf (ll : LedgerLRecord rec) : hash_7_correct_def ll.
  start_proof.
  time hash_7_start.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  try time "[simple][bottomup][7]" timeout 300 bottom_up_goal_solver; abort.
Time Qed.

Lemma hash_7_new_top_solver_prf (ll : LedgerLRecord rec) : hash_7_correct_def ll.
  start_proof.
  time hash_7_start.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  time "[simple][newtopdown][7]" new_top_down_solver.
Time Qed.
