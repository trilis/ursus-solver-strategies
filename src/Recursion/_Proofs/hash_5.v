Require Import Recursion.Tactics.hash_5.

Set Keyed Unification.
SetDefaultOpaques "Recursion".
Opaque N.mul N.modulo.
Opaque arrLookup.

Definition hash_5_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_5 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 5%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Lemma hash_5_top_solver_prf (ll : LedgerLRecord rec) : hash_5_correct_def ll.
  start_proof.
  time hash_5_start.
  time continue_all @hash_4 @hash_3 @hash_2 @hash_1.
  destruct_ledger ll.
  time "[recursion][topdown][5]" top_down_solver.
Time Qed.

Lemma hash_5_let_form_prf (ll : LedgerLRecord rec) : hash_5_correct_def ll.
  start_proof.
  time hash_5_start.
  time continue_all @hash_4 @hash_3 @hash_2 @hash_1.
  destruct_ledger ll.
  time "[recursion][letform][5]" let_form_solver.
Time Qed.

Lemma hash_5_bottom_up_prf (ll : LedgerLRecord rec) : hash_5_correct_def ll.
  start_proof.
  time hash_5_start.
  time continue_all @hash_4 @hash_3 @hash_2 @hash_1.
  destruct_ledger ll.
  time "[recursion][bottomup][5]" timeout 300 bottom_up_goal_solver.
Time Qed.
