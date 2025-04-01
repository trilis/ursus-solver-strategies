Require Import Recursion.Tactics.hash_10.

SetDefaultOpaques "Recursion".
Opaque N.mul N.modulo.
Opaque arrLookup.

Definition hash_10_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_10 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 10%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

(* Set Debug "tactic-unification".
(* Opaque hash_10 hash_9 hash_8 hash_7 hash_6 hash_5 hash_4 hash_3 hash_2 hash_1.
Opaque hash_10_cbv_0_exec hash_9_cbv_0_exec hash_8_cbv_0_exec hash_7_cbv_0_exec hash_6_cbv_0_exec hash_5_cbv_0_exec hash_4_cbv_0_exec hash_3_cbv_0_exec hash_2_cbv_0_exec hash_1_cbv_0_exec.
Opaque exec_state eval_state. *)
Fail Timeout 1
Check __exec (f:=@hash_10). *)

Lemma hash_10_top_solver_prf (ll : LedgerLRecord rec) : hash_10_correct_def ll.
  start_proof.
  Print Instances ExecsIndex.
  Set Typeclasses Debug.
  Remove Hints _ex_slice_load _ex_tvm_commit _ex_suicide _ex_tvm_newContract _ex_send_internal_message_empty _ex_deduct_currencies _ex_get _ex_send_internal_message _ex_cell_decode _ex_cell_encode _ex_tvm_transfer _ex_builder_store: typeclass_instances.
  Print Instances ExecsIndex.
  Check _ex_hash_10_cbv.
  #[local] Hint Opaque _ex_hash_10_cbv : typeclass_instances.
  Set Typeclasses Debug Verbosity 2.
  time hash_10_start.
  time continue_all @hash_9 @hash_8 @hash_7 @hash_6 
                    @hash_5 @hash_4 @hash_3 @hash_2 
                    @hash_1.
  (* destruct_ledger ll. *)
  time prepare_all ll P.
  compute_destructed_ledgers loc_.

  time "[recursion][topdown][10]" top_down_solver. (* 46.378 secs *)
Time Qed.

Lemma hash_10_let_form_prf (ll : LedgerLRecord rec) : hash_10_correct_def ll.
  start_proof.
  time hash_10_start.
  time continue_all @hash_9 @hash_8 @hash_7 @hash_6 @hash_5 @hash_4 @hash_3 @hash_2 @hash_1.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  time "[recursion][letform][10]" let_form_solver.
Time Qed.

Lemma hash_10_bottom_up_prf (ll : LedgerLRecord rec) : hash_10_correct_def ll.
  start_proof.
  time hash_10_start.
  time continue_all @hash_9 @hash_8 @hash_7 @hash_6 @hash_5 @hash_4 @hash_3 @hash_2 @hash_1.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.
  timeout 300 time "[recursion][bottomup][10]" bottom_up_goal_solver.
Time Qed.
