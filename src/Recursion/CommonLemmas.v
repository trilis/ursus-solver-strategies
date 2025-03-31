From Hammer Require Import Tactics Hammer. 

Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import SpecLang.

Fixpoint reference_hash_implementation 
    (n: nat)
        (m_string: uint64[])
        (m_multiplier: N)
        (m_modulo: N): (N * N) :=
    match n with 
    | O => (0, 1)
    | S n' => 
        let c := unMaybe (arrLookup (N.of_nat n') m_string) in
        let '(h, pw) := reference_hash_implementation n' m_string m_multiplier m_modulo in
        let h' := N.modulo (h + uint2N c * pw) m_modulo in
        let pw' := N.modulo (pw * m_multiplier) m_modulo in
        (h', pw')
    end.