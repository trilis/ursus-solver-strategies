Require Import Recursion.Tactics.hash_4.

Set Keyed Unification.
SetDefaultOpaques "Recursion".
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
  time continue_all @hash_3 @hash_2 @hash_1.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  time "[recursion][topdown][4]" top_down_solver.
Time Qed.

Lemma hash_4_let_form_prf (ll : LedgerLRecord rec) : hash_4_correct_def ll.
  start_proof.
  time hash_4_start.
  time continue_all @hash_3 @hash_2 @hash_1.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  time "[recursion][letform][4]" let_form_solver.
Time Qed.

Lemma hash_4_bottom_up_prf (ll : LedgerLRecord rec) : hash_4_correct_def ll.
  start_proof.
  time hash_4_start.
  time continue_all @hash_3 @hash_2 @hash_1.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  timeout 300 time "[recursion][bottomup][4]" bottom_up_goal_solver.
Time Qed.
