Require Import UrsusEnvironment.Solidity.current.Environment.
From Hammer Require Import Tactics Hammer. 

Require Import UMLang.ExecGenerator.

Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Structures.Monad.

Import MonadNotation.
Local Open Scope monad_scope.

Require Import TVMModel.Notations.Loadable.
Require Import TVMModel.Notations.Storeable.
Require Import TVMModel.Base.Proofs.EncodeDecode.
Require Import TVMModel.Base.Proofs.TVMBitString.
Require Import TVMModel.Base.Definitions.TVMBitString.
Require Import TVMModel.Base.Definitions.TVMCell.
Require Import TVMModel.Base.Definitions.StateInit.

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
        if Common.eqb c 0: bool then (h, pw, true) else
        if finished then (h, pw, true) else
        let h' := N.modulo (h + uint2N c * pw) m_modulo in
        let pw' := N.modulo (pw * m_multiplier) m_modulo in
        (h', pw', false)
    end.