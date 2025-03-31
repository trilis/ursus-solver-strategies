Require Import Recursion.Tactics.hash_9.

Set Keyed Unification.
SetDefaultOpaques "Recursion".
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
  time continue_all @hash_8 @hash_7 @hash_6 @hash_5 @hash_4 @hash_3 @hash_2 @hash_1.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  time "[recursion][topdown][9]" top_down_solver.
Time Qed.

Lemma hash_9_let_form_prf (ll : LedgerLRecord rec) : hash_9_correct_def ll.
  start_proof.
  time hash_9_start.
  time continue_all @hash_8 @hash_7 @hash_6 @hash_5 @hash_4 @hash_3 @hash_2 @hash_1.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  time "[recursion][letform][9]" let_form_solver.
Time Qed.

Lemma hash_9_bottom_up_prf (ll : LedgerLRecord rec) : hash_9_correct_def ll.
  start_proof.
  time hash_9_start.
  time continue_all @hash_8 @hash_7 @hash_6 @hash_5 @hash_4 @hash_3 @hash_2 @hash_1.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  timeout 300 time "[recursion][bottomup][9]" bottom_up_goal_solver.
Time Qed.
