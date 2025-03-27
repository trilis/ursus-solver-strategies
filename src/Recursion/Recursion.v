Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusEnvironment.Solidity.current.LocalGenerator.
Require Import UrsusQC.CommonQCEnvironment.
Require Import UrsusContractCreator.UrsusFieldUtils.
Require Import UrsusContractCreator.BaseContracts.EverContract.
Set UrsusPrefixTactic "PrefixOnlyURValue".

#[translation = off]
#[quickchick = off]
#[language = solidity]
Contract Recursion ;
Sends To  ; 
Inherits EverBaseContract ;
Types ;
Record Contract := {
    m_string: uint64[];
    m_multiplier: uint64;
    m_modulo: uint64;
    m_current_power: uint64;
    m_hash: uint64
}.
SetUrsusOptions.

Local Close Scope N_scope.
Local Close Scope Q_scope.
Local Close Scope nat_scope.

UseLocal Definition _ := [
    uint64
].

Local Open Scope nat_scope.
Local Open Scope Q_scope.
Local Open Scope N_scope. 

Ursus Definition hash_1: UExpression PhantomType false.
{
    ::// m_hash := {0}.
    ::// m_current_power := {1}.
    ::// m_hash := (m_hash + m_string[[{0}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_2: UExpression PhantomType false.
{
    ::// hash_1().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_3: UExpression PhantomType false.
{
    ::// hash_2().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{2}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_4: UExpression PhantomType false.
{
    ::// hash_3().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{3}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_5: UExpression PhantomType false.
{
    ::// hash_4().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{4}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_6: UExpression PhantomType false.
{
    ::// hash_5().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{5}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.  

Ursus Definition hash_7: UExpression PhantomType false.
{
    ::// hash_6().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{6}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_8: UExpression PhantomType false.
{
    ::// hash_7().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{7}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_9: UExpression PhantomType false.
{
    ::// hash_8().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{8}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_10: UExpression PhantomType false.
{
    ::// hash_9().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{9}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.

EndContract.
GenerateLocalState 0 Recursion.
Fail GenerateLocalState 1 Recursion.
GenerateLocalState Recursion.
