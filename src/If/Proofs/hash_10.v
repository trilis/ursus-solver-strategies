Require Import If.Tactics.hash_10.

Set Keyed Unification.
SetDefaultOpaques "If".
Opaque N.mul N.modulo.
Opaque arrLookup.

Definition hash_10_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_10 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (fst (reference_hash_implementation 10%nat m_string (uint2N m_multiplier) (uint2N m_modulo)))).
Defined.

Lemma hash_10_top_solver_prf (ll : LedgerLRecord rec) : hash_10_correct_def ll.
  start_proof.
  time hash_10_start.
  compute_destructed_ledgers loc_.
  time prepare_all ll P.
  match goal with 
    | |- _ = ?y => remember y as P; lazy in HeqP; subst P
  end.
  timeout 300 time "[if][topdown][10]" top_down_solver.
Time Qed.

Lemma hash_10_let_form_prf (ll : LedgerLRecord rec) : hash_10_correct_def ll.
  start_proof.
  time hash_10_start.
  compute_destructed_ledgers loc_.
  time prepare_all ll P.
  match goal with 
    | |- _ = ?y => remember y as P; lazy in HeqP; subst P
  end.
  timeout 300 time "[if][letform][10]" let_form_solver.
Time Qed.

Lemma hash_10_bottom_up_prf (ll : LedgerLRecord rec) : hash_10_correct_def ll.
  start_proof.
  time hash_10_start.
  compute_destructed_ledgers loc_.
  time prepare_all ll P.
  match goal with 
    | |- _ = ?y => remember y as P; lazy in HeqP; subst P
  end.
  timeout 300 time "[if][bottomup][10]" bottom_up_goal_solver'.
Time Qed.
