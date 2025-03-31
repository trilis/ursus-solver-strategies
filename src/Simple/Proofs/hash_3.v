Require Import Simple.Tactics.hash_3.

Set Keyed Unification.
SetDefaultOpaques "Simple".
Opaque N.mul N.modulo.
Opaque arrLookup.

Definition hash_3_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_3 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 3%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Lemma hash_3_top_solver_prf (ll : LedgerLRecord rec) : hash_3_correct_def ll.
  start_proof.
  time hash_3_start.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  time "[simple][topdown][3]" top_down_solver.
Time Qed.

Lemma hash_3_let_form_prf (ll : LedgerLRecord rec) : hash_3_correct_def ll.
  start_proof.
  time hash_3_start.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  time "[simple][letform][3]" let_form_solver.
Time Qed.

Lemma hash_3_bottom_up_prf (ll : LedgerLRecord rec) : hash_3_correct_def ll.
  start_proof.
  time hash_3_start.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  time "[simple][bottomup][3]" timeout 300 bottom_up_goal_solver.
Time Qed.

Lemma hash_3_new_top_solver_prf (ll : LedgerLRecord rec) : hash_3_correct_def ll.
  start_proof.
  time hash_3_start.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  time "[simple][newtopdown][3]" new_top_down_solver.
Time Qed.
