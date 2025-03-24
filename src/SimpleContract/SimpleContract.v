Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import UrsusQC.CommonQCEnvironment.
Require Import UrsusContractCreator.UrsusFieldUtils.
Require Import UrsusContractCreator.BaseContracts.EverContract.
Set UrsusPrefixTactic "PrefixOnlyURValue".

#[translation = off]
#[quickchick = off]
#[language = solidity]
Contract SimpleContract ;
Sends To  ; 
Inherits EverBaseContract ;
Types 
Record CharBlock := {
    char0: uint8;
    char1: uint8;
    char2: uint8;
    char3: uint8
};
Record Contract := {
    m_string: (_ResolveRecord("CharBlock"))[];
    m_multiplier: uint64;
    m_modulo: uint64;
    m_hash: uint64
}.
SetUrsusOptions.

Local Close Scope N_scope.
Local Close Scope Q_scope.
Local Close Scope nat_scope.

UseLocal Definition _ := [
    uint64;
    CharBlockLRecord
].

Local Open Scope nat_scope.
Local Open Scope Q_scope.
Local Open Scope N_scope. 

Local Open Scope ursus_scope_CharBlock.

Ursus Definition hash_1: UExpression uint64 false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// var00 current_block: CharBlockLRecord := m_string[[{0}]];_|.
    ::// m_hash := {0}.
    ::// m_hash := (m_hash + current_block->char0 * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + current_block->char1 * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + current_block->char2 * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + current_block->char3 * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo |.
}
return.
Defined.
Sync.

EndContract.
(* End MultisigWallet. *)
GenerateLocalState 0 SimpleContract.
Fail GenerateLocalState 1 SimpleContract.
GenerateLocalState SimpleContract.
