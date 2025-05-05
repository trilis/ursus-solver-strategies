From Hammer Require Import Tactics Hammer. 

Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import SpecLang.

Require Import If.If.
Import If.
Require Import If.Common.

Fixpoint reference_hash_implementation 
    (n: nat)
        (m_string: uint64[])
        (m_multiplier: N)
        (m_modulo: N): (N * N * bool) :=
    match n with 
    | O => (0, 1, false)
    | S n' => 
        let c := match (arrLookup (N.of_nat n') m_string) with
            | Some c => c
            | None => Build_XUBInteger 0
        end in
        let '(h, pw, finished) := reference_hash_implementation n' m_string m_multiplier m_modulo in
        if Common.eqb c default: bool then (h, pw, true) else
        if finished then (h, pw, true) else
        let h' := N.modulo (h + uint2N c * pw) m_modulo in
        let pw' := N.modulo (pw * m_multiplier) m_modulo in
        (h', pw', false)
    end.


Definition hash_1_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_1 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (fst (reference_hash_implementation 1%nat m_string (uint2N m_multiplier) (uint2N m_modulo)))).
Defined.

Definition hash_2_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_2 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (fst (reference_hash_implementation 2%nat m_string (uint2N m_multiplier) (uint2N m_modulo)))).
Defined.

Definition hash_3_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_3 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (fst (reference_hash_implementation 3%nat m_string (uint2N m_multiplier) (uint2N m_modulo)))).
Defined.

Definition hash_4_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_4 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (fst (reference_hash_implementation 4%nat m_string (uint2N m_multiplier) (uint2N m_modulo)))).
Defined.

Definition hash_5_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_5 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (fst (reference_hash_implementation 5%nat m_string (uint2N m_multiplier) (uint2N m_modulo)))).
Defined.

Definition hash_6_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_6 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (fst (reference_hash_implementation 6%nat m_string (uint2N m_multiplier) (uint2N m_modulo)))).
Defined.

Definition hash_7_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_7 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (fst (reference_hash_implementation 7%nat m_string (uint2N m_multiplier) (uint2N m_modulo)))).
Defined.

Definition hash_8_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_8 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (fst (reference_hash_implementation 8%nat m_string (uint2N m_multiplier) (uint2N m_modulo)))).
Defined.

Definition hash_9_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_9 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (fst (reference_hash_implementation 9%nat m_string (uint2N m_multiplier) (uint2N m_modulo)))).
Defined.

Definition hash_10_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_10 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (fst (reference_hash_implementation 10%nat m_string (uint2N m_multiplier) (uint2N m_modulo)))).
Defined.