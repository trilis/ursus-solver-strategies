Require Import Recursion.Tactics.hash_10.

Set Keyed Unification.
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
  (* destruct_ledger ll. *)
  time prepare_all ll P.
  compute_destructed_ledgers loc_.

  Ltac let_form_solver := 
  clear_unneeded_hyps; repeat match goal with 
      | H: ?y = ?t |- _ =>
      is_var y;
      assert_fails (idtac; multimatch goal with 
          | H2: ?y2 = _ |- _ => 
              match t with 
                  | context[y2] => idtac
                  | _ => fail
              end
      end);
      idtac y;
      match t with 
      | if ?b then _ else _ => destruct b; clear_unneeded_hyps
      | _ =>
        let x := fresh "x" in
        set (x := t); 
        replace y with x in * ; 
        clear H
      end
  end; lazy; auto.

  (* Too long ... *)
  (* time "[recursion][letform][10]" let_form_solver. *)
Abort.

Lemma hash_10_bottom_up_prf (ll : LedgerLRecord rec) : hash_10_correct_def ll.
  start_proof.
  time hash_10_start.
  time continue_all @hash_9 @hash_8 @hash_7 @hash_6 
                    @hash_5 @hash_4 @hash_3 @hash_2 @hash_1.
  time prepare_all ll P.
  compute_destructed_ledgers loc_.

  time "[recursion][bottomup][10]" (* timeout 300 *) bottom_up_goal_solver. (* 41.982 secs *)
Time Qed.
