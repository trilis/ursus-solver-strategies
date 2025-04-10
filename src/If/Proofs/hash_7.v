Require Import If.Tactics.hash_7.

Set Keyed Unification.
SetDefaultOpaques "If".
Opaque N.mul N.modulo.
Opaque arrLookup.

Definition hash_7_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_7 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (fst (reference_hash_implementation 7%nat m_string (uint2N m_multiplier) (uint2N m_modulo)))).
Defined.

Lemma hash_7_top_solver_prf (ll : LedgerLRecord rec) : hash_7_correct_def ll.
  start_proof.
  time hash_7_start.
  compute_destructed_ledgers loc_.
  time prepare_all ll P.
  match goal with 
    | |- _ = ?y => remember y as P; lazy in HeqP; subst P
  end.
  timeout 300 time "[if][topdown][7]" top_down_solver.
Time Qed.

Lemma hash_7_let_form_prf (ll : LedgerLRecord rec) : hash_7_correct_def ll.
  start_proof.
  time hash_7_start.
  compute_destructed_ledgers loc_.
  time prepare_all ll P.
  match goal with 
    | |- _ = ?y => remember y as P; lazy in HeqP; subst P
  end.
  timeout 300 time "[if][letform][7]" let_form_solver.
Time Qed.

Lemma hash_7_bottom_up_prf (ll : LedgerLRecord rec) : hash_7_correct_def ll.
  start_proof.
  time hash_7_start.
  compute_destructed_ledgers loc_.
  time prepare_all ll P.
  match goal with 
    | |- _ = ?y => remember y as P; lazy in HeqP; subst P
  end.
  timeout 300 time "[if][bottomup][7]" bottom_up_goal_solver'.
Time Qed.
