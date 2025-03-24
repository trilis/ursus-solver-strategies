Require Import SimpleContract.Tactics.hash_1.

SetDefaultOpaques "SimpleContract".

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
        (m_multiplier: N)
        (m_modulo: N): N :=
    match n with 
    | O => 0
    | S n' => 
        let block := unMaybe (arrLookup i m_string) in
        let '(pw', h) := reference_hash_implementation_helper 
            pw block m_multiplier m_modulo in
        h + reference_hash_implementation n' (i + 1) pw' m_string m_multiplier m_modulo
    end.

Definition hash_1_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_1 rec def) :
ll | "m_string" "m_multiplier" "m_modulo" ->  l1 | "m_hash".
con (m_hash = reference_hash_implementation 1%nat 0 1 m_string 
    (uint2N m_multiplier) (uint2N m_modulo)).
Defined.

Lemma hash_1_correct_prf (ll : LedgerLRecord rec) : hash_1_correct_def ll.
  start_proof.
  Set Typeclasses Debug.
  time hash_1_start.
  time prepare_all ll P.

  time process_pure_eval_execs.
  compute_destructed_ledgers loc_.
  time process_multiexists.
  time test_solver.
Time Qed.