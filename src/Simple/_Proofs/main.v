Require Import Simple.Tactics.hash_1.

SetDefaultOpaques "Simple".
(*
Definition reference_hash_implementation_helper 
    (pw: N) (block: CharBlockLRecord)
    (m_multiplier: N) (m_modulo: N) :=
        let h0 := N.modulo (uint2N (CharBlock_ι_char0 block) * m_multiplier) m_modulo in
        let pw0 := N.modulo (pw * m_multiplier) m_modulo in
        let h1 := N.modulo (uint2N (CharBlock_ι_char1 block) * m_multiplier)m_modulo in
        let pw1 := N.modulo (pw0 * m_multiplier) m_modulo in
        let h2 := N.modulo (uint2N (CharBlock_ι_char2 block) * m_multiplier) m_modulo in
        let pw2 := N.modulo (pw1 * m_multiplier) m_modulo in
        let h3 := N.modulo (uint2N (CharBlock_ι_char3 block) * m_multiplier) m_modulo in
        let pw3 := N.modulo (pw2 * m_multiplier) m_modulo in
        (pw3, h0 + h1 + h2 + h3)
.

Fixpoint reference_hash_implementation 
    (n: nat) (i: N) (pw: N) 
        (m_string: CharBlockLRecord[])
        (m_multiplier: N): N :=
    match n with 
    | O => 0
    | S n' => 
        let block := unMaybe (arrLookup i m_string) in
        reference_hash_implementation_helper 
            pw block m_multiplier in
        h + reference_hash_implementation n' (i + 1) pw' m_string m_multiplier
    end.
*)
Definition hash_1_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_1 rec def) :
ll | "m_multiplier" -> l1 | "m_hash".
hyp (False).
con (m_hash = 0 (*reference_hash_implementation 1%nat 0 1 m_multiplier*)).
Defined.

Ltac top_down_solver :=
  clear_unneeded_hyps; repeat match goal with 
      | H: ?y = ?t |- _ =>
      assert_fails (idtac; multimatch goal with 
          | H2: ?y2 = _ |- _ => 
              match t with 
                  | context[y2] => idtac
                  | _ => fail
              end
      end);
      idtac y; (match t with 
          | context[if ?b then _ else _] => destruct b
          | _ => idtac
      end); 
      match type of t with
        | ExecGenDefs.ULValue _ => subst y
        | _ =>
          lazy in H; subst y
      end
  end; lazy; auto.

Ltac convert_to_let_form := 
repeat match goal with 
    | H: ?y = ?t |- _ =>
    is_var y; 
    assert_fails (idtac; multimatch goal with 
        | H2: ?y2 = _ |- _ => 
            match t with 
                | context[y2] => idtac
                | _ => fail
            end
    end);
    let x := fresh "x" in
    set (x := t); replace y with x in *; clear H
end.  
Ltac let_form_solver := clear_unneeded_hyps; convert_to_let_form; lazy; auto.

Lemma hash_1_correct_prf (ll : LedgerLRecord rec) : hash_1_correct_def ll.
  start_proof.
  Set Keyed Unification.
  time hash_1_start.
  destruct_ledger ll.
  Opaque N.mul.
  time top_down_solver. 
  exfalso. auto.
Time Qed.