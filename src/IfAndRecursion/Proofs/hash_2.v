Require Import IfAndRecursion.Tactics.hash_2.

Set Keyed Unification.
SetDefaultOpaques "IfAndRecursion".
Opaque N.mul N.modulo.
Opaque arrLookup.

Definition hash_2_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_2 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (fst (reference_hash_implementation 2%nat m_string (uint2N m_multiplier) (uint2N m_modulo)))).
Defined.

Lemma hash_2_top_solver_prf (ll : LedgerLRecord rec) : hash_2_correct_def ll.
  start_proof.
  time hash_2_start.
  time continue_all @hash_1.
  compute_destructed_ledgers loc_.
  time prepare_all ll P.
  match goal with 
    | |- _ = ?y => remember y as P; lazy in HeqP; subst P
  end.

  try timeout 300 time "[if&recursion][topdown][2]" top_down_solver.
Time Qed.

Lemma hash_2_let_form_prf (ll : LedgerLRecord rec) : hash_2_correct_def ll.
  start_proof.
  time hash_2_start.
  time continue_all @hash_1.
  compute_destructed_ledgers loc_.
  time prepare_all ll P.
  match goal with
    | |- _ = ?y => remember y as P; lazy in HeqP; subst P
  end.

  try timeout 300 time "[if&recursion][letform][2]" let_form_solver.
Time Qed.

Lemma hash_2_bottom_up_prf (ll : LedgerLRecord rec) : hash_2_correct_def ll.
  start_proof.
  time hash_2_start.
  time continue_all @hash_1.
  compute_destructed_ledgers loc_.
  time prepare_all ll P.
  match goal with 
    | |- _ = ?y => remember y as P; lazy in HeqP; subst P
  end.

  try timeout 300 time "[if&recursion][bottomup][2]" bottom_up_goal_solver'.
Time Qed.

Lemma hash_2_new_top_solver_prf (ll : LedgerLRecord rec) : hash_2_correct_def ll.
  start_proof.
  time hash_2_start.
  time continue_all @hash_1.
  compute_destructed_ledgers loc_.
  time prepare_all ll P.
  match goal with 
    | |- _ = ?y => remember y as P; lazy in HeqP; subst P
  end.
  try timeout 300 time "[if&recursion][newtopdown][2]" new_top_down_solver.
Time Qed.