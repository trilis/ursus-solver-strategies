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
  #[local]
  Existing Instance _ex_hash_5_cbv | 0.
  hash_5_start.
  prepare_goal  @hash_5.
  let ee := constr:(__exec (f:=hash_5)) in
                           let e := match ee with
                           | @__exec _ _ _ _ ?I => eval cbv beta iota delta [__exec I] in ee
                           end in
  erewrite <- ?hash_5_cbv_0_exec_prf.
  [
    (* |- fun_exec... *)
    let ll := fresh "ll" in
    let ll' := fresh "ll'" in
    destructor_helper (f a1) ll ll'(*; (* ? *)
    (* ll = fun_exec, ll' := ll |- f (ll) *)
    change_no_check ll with ll';
    (* ll = fun_exec, ll' := ll |- f (ll')  *)
    revert ll';
    (* ll = fun_exec |- let ll' := ll in f (ll')  *)
    let P0 := fresh "P" in 
    match goal with
    | |- let ll' := _ in @?F ll' => (* remember F as P0 *)
         let HF := fresh "HeqF" in 
         pose F as P0; assert (P0 = F) as HF by (* (exact_no_check eq_refl) *)reflexivity; clearbody P0
    end;
    intros;
    (* ll = fun_exec, ll' := ll, P0 = |- P0 (ll')  *)
    (* match goal with
    | |- ?G => *) assert (P0 ll'); [| subst P0; (* subst P; *) auto]
    (* end *);
    subst ll' ll;
    cbv beta delta [f_exec];
    lift_lets P0 Heql Hprev | ..*) ].
  cbv beta delta [hash_5_cbv_0_exec].
  continue_all @hash_5.
  continue_all  @hash_5 @hash_4 @hash_3 @hash_2 @hash_1.
  simplify_tails  .
  time hash_5_start.
  time continue_all @hash_4 @hash_3 @hash_2 @hash_1.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  time "[recursion][topdown][5]" top_down_solver.
Time Qed.

Lemma hash_5_let_form_prf (ll : LedgerLRecord rec) : hash_5_correct_def ll.
  start_proof.
  time hash_5_start.
  time continue_all @hash_4 @hash_3 @hash_2 @hash_1.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  time "[recursion][letform][5]" let_form_solver.
Time Qed.

Lemma hash_5_bottom_up_prf (ll : LedgerLRecord rec) : hash_5_correct_def ll.
  start_proof.
  time hash_5_start.
  time continue_all @hash_4 @hash_3 @hash_2 @hash_1.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  timeout 300 time "[recursion][bottomup][5]" bottom_up_goal_solver.
Time Qed.
