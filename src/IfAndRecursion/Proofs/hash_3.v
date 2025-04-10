Require Import IfAndRecursion.Tactics.hash_3.

Set Keyed Unification.
SetDefaultOpaques "IfAndRecursion".
Opaque N.mul N.modulo.
Opaque arrLookup.

Definition hash_3_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_3 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (fst (reference_hash_implementation 3%nat m_string (uint2N m_multiplier) (uint2N m_modulo)))).
Defined.

Lemma hash_3_top_solver_prf (ll : LedgerLRecord rec) : hash_3_correct_def ll.
  start_proof.
  time hash_3_start.
  time continue_all @hash_2 @hash_1.
  compute_destructed_ledgers loc_.
  time prepare_all ll P.
  match goal with 
    | |- _ = ?y => remember y as P; lazy in HeqP; subst P
  end.
  try timeout 300 time "[if&recursion][topdown][3]" top_down_solver; abort.
Time Qed.

Lemma hash_3_let_form_prf (ll : LedgerLRecord rec) : hash_3_correct_def ll.
  start_proof.
  time hash_3_start.
  time continue_all @hash_2 @hash_1.
  compute_destructed_ledgers loc_.
  time prepare_all ll P.
  match goal with 
    | |- _ = ?y => remember y as P; lazy in HeqP; subst P
  end.
  try timeout 300 time "[if&recursion][letform][3]" let_form_solver; abort.
Time Qed.

Lemma hash_3_bottom_up_prf (ll : LedgerLRecord rec) : hash_3_correct_def ll.
  start_proof.
  time hash_3_start.
  time continue_all @hash_2 @hash_1.
  compute_destructed_ledgers loc_.
  time prepare_all ll P.
  match goal with 
    | |- _ = ?y => remember y as P; lazy in HeqP; subst P
  end.
  try timeout 300 time "[if&recursion][bottomup][3]" bottom_up_goal_solver'; abort.
Time Qed.

Lemma hash_3_new_top_solver_prf (ll : LedgerLRecord rec) : hash_3_correct_def ll.
  start_proof.
  time hash_3_start.
  time continue_all @hash_2 @hash_1.
  compute_destructed_ledgers loc_.
  time prepare_all ll P.
  match goal with 
    | |- _ = ?y => remember y as P; lazy in HeqP; subst P
  end.
  try timeout 300 time "[if&recursion][newtopdown][3]" new_top_down_solver; abort.
Time Qed.
