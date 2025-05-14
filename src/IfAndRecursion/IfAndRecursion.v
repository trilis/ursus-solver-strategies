Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusPatterns.Solidity.TVM.EverBase.

Set UrsusPrefixTactic "PrefixOnlyURValue".

#[translation = off]
#[quickchick = off]
#[language = solidity]
Contract IfAndRecursion ;
Sends To  ; 
Inherits EverBaseContract ;
Types ;
Record Contract := {
    m_string: uint64[];
    m_multiplier: uint64;
    m_modulo: uint64;
    m_current_power: uint64;
    m_hash: uint64;
    m_should_exit: bool;
    m_unused1: uint64;
    m_unused2: uint64;
    m_unused3: uint64;
    m_unused4: uint64;
    m_unused5: uint64;
    m_unused6: uint64;
    m_unused7: uint64;
    m_unused8: uint64;
    m_unused9: uint64;
    m_unused10: uint64;
    m_unused11: uint64;
    m_unused12: uint64;
    m_unused13: uint64;
    m_unused14: uint64;
    m_unused15: uint64;
    m_unused16: uint64;
    m_unused17: uint64;
    m_unused18: uint64;
    m_unused19: uint64;
    m_unused20: uint64
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

Ursus Definition hash_1: UExpression PhantomType true.
{
    ::// m_hash := {0}.
    ::// m_current_power := {1}.
    ::// m_should_exit := {false}.
    ::// if (m_string[[{0}]] == {0} || m_should_exit) then { 
        m_should_exit := {true}; exit_
    }.
    ::// m_hash := (m_hash + m_string[[{0}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_2: UExpression PhantomType true.
{
    ::// hash_1().
    ::// if (m_string[[{1}]] == {0} || m_should_exit) then { 
        m_should_exit := {true}; exit_
    }.
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_3: UExpression PhantomType true.
{
    ::// hash_2().
    ::// if (m_string[[{2}]] == {0} || m_should_exit) then { 
        m_should_exit := {true}; exit_
    }.
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{2}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_4: UExpression PhantomType true.
{
    ::// hash_3().
    ::// if (m_string[[{3}]] == {0} || m_should_exit) then { 
        m_should_exit := {true}; exit_
    }.
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{3}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_5: UExpression PhantomType true.
{
    ::// hash_4().
    ::// if (m_string[[{4}]] == {0} || m_should_exit) then { 
        m_should_exit := {true}; exit_
    }.
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{4}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_6: UExpression PhantomType true.
{
    ::// hash_5().
    ::// if (m_string[[{5}]] == {0} || m_should_exit) then { 
        m_should_exit := {true}; exit_ 
    }.
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{5}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_7: UExpression PhantomType true.
{
    ::// hash_6().
    ::// if (m_string[[{6}]] == {0} || m_should_exit) then { 
        m_should_exit := {true}; exit_ 
    }.
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{6}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_8: UExpression PhantomType true.
{
    ::// hash_7().
    ::// if (m_string[[{7}]] == {0} || m_should_exit) then { 
        m_should_exit := {true}; exit_ 
    }.
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{7}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_9: UExpression PhantomType true.
{
    ::// hash_8().
    ::// if (m_string[[{8}]] == {0} || m_should_exit) then { 
        m_should_exit := {true}; exit_ 
    }.
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{8}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_10: UExpression PhantomType true.
{
    ::// hash_9().
    ::// if (m_string[[{9}]] == {0} || m_should_exit) then { 
        m_should_exit := {true}; exit_ 
    }.
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{9}]] * m_current_power) % m_modulo |.
}
return.
Defined.
Sync.

EndContract.
GenerateLocalState 0 IfAndRecursion.
Fail GenerateLocalState 1 IfAndRecursion.
GenerateLocalState IfAndRecursion.
