Require Import IfAndRecursion.Tactics.hash_4.

Set Keyed Unification.
SetDefaultOpaques "IfAndRecursion".
Opaque N.mul N.modulo.
Opaque arrLookup.

Definition hash_4_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_4 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (fst (reference_hash_implementation 4%nat m_string (uint2N m_multiplier) (uint2N m_modulo)))).
Defined.

Lemma hash_4_top_solver_prf (ll : LedgerLRecord rec) : hash_4_correct_def ll.
  start_proof.
  time hash_4_start.
  time continue_all @hash_3 @hash_2 @hash_1.
  compute_destructed_ledgers loc_.
  time prepare_all ll P.
  match goal with 
    | |- _ = ?y => remember y as P; lazy in HeqP; subst P
  end.
  try timeout 300 time "[if&recursion][topdown][4]" top_down_solver; abort.
Time Qed.

Lemma hash_4_let_form_prf (ll : LedgerLRecord rec) : hash_4_correct_def ll.
  start_proof.
  time hash_4_start.
  time continue_all @hash_3 @hash_2 @hash_1.
  compute_destructed_ledgers loc_.
  time prepare_all ll P.
  match goal with 
    | |- _ = ?y => remember y as P; lazy in HeqP; subst P
  end.
  try timeout 300 time "[if&recursion][letform][4]" let_form_solver; abort.
Time Qed.

Lemma hash_4_bottom_up_prf (ll : LedgerLRecord rec) : hash_4_correct_def ll.
  start_proof.
  time hash_4_start.
  time continue_all @hash_3 @hash_2 @hash_1.
  compute_destructed_ledgers loc_.
  time prepare_all ll P.
  match goal with 
    | |- _ = ?y => remember y as P; lazy in HeqP; subst P
  end.
  try timeout 300 time "[if&recursion][bottomup][4]" bottom_up_goal_solver'; abort.
Time Qed.

Lemma hash_4_new_top_solver_prf (ll : LedgerLRecord rec) : hash_4_correct_def ll.
  start_proof.
  time hash_4_start.
  time continue_all @hash_3 @hash_2 @hash_1.
  compute_destructed_ledgers loc_.
  time prepare_all ll P.
  match goal with 
    | |- _ = ?y => remember y as P; lazy in HeqP; subst P
  end.
  try timeout 300 time "[if&recursion][newtopdown][4]" new_top_down_solver; abort.
Time Qed.
