Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusPatterns.Solidity.TVM.EverBase.

Set UrsusPrefixTactic "PrefixOnlyURValue".

#[translation = off]
#[quickchick = off]
#[language = solidity]
Contract If ;
Sends To  ; 
Inherits EverBaseContract ;
Types ;
Record Contract := {
    m_string: uint64[];
    m_multiplier: uint64;
    m_modulo: uint64;
    m_hash: uint64;
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
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    ::// if (m_string[[{0}]] == {0}) then { exit_ }.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_2: UExpression PhantomType true.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    ::// if (m_string[[{0}]] == {0}) then { exit_ }.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo.
    ::// if (m_string[[{1}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_3: UExpression PhantomType true.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    |-----------------------------.
    ::// if (m_string[[{0}]] == {0}) then { exit_ }.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo.
    ::// if (m_string[[{1}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{2}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{2}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_4: UExpression PhantomType true.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    |-----------------------------.
    ::// if (m_string[[{0}]] == {0}) then { exit_ }.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo.
    ::// if (m_string[[{1}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{2}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{2}]] * current_power) % m_modulo.
    ::// if (m_string[[{3}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{3}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_5: UExpression PhantomType true.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    |-----------------------------.
    ::// if (m_string[[{0}]] == {0}) then { exit_ }.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo.
    ::// if (m_string[[{1}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{2}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{2}]] * current_power) % m_modulo.
    ::// if (m_string[[{3}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{3}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{4}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{4}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_6: UExpression PhantomType true.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    |-----------------------------.
    ::// if (m_string[[{0}]] == {0}) then { exit_ }.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo.
    ::// if (m_string[[{1}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{2}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{2}]] * current_power) % m_modulo.
    ::// if (m_string[[{3}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{3}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{4}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{4}]] * current_power) % m_modulo.
    ::// if (m_string[[{5}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{5}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_7: UExpression PhantomType true.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    |-----------------------------.
    ::// if (m_string[[{0}]] == {0}) then { exit_ }.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo.
    ::// if (m_string[[{1}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{2}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{2}]] * current_power) % m_modulo.
    ::// if (m_string[[{3}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{3}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{4}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{4}]] * current_power) % m_modulo.
    ::// if (m_string[[{5}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{5}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{6}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{6}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_8: UExpression PhantomType true.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    |-----------------------------.
    ::// if (m_string[[{0}]] == {0}) then { exit_ }.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo.
    ::// if (m_string[[{1}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{2}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{2}]] * current_power) % m_modulo.
    ::// if (m_string[[{3}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{3}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{4}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{4}]] * current_power) % m_modulo.
    ::// if (m_string[[{5}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{5}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{6}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{6}]] * current_power) % m_modulo.
    ::// if (m_string[[{7}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{7}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_9: UExpression PhantomType true.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    |-----------------------------.
    ::// if (m_string[[{0}]] == {0}) then { exit_ }.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo.
    ::// if (m_string[[{1}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{2}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{2}]] * current_power) % m_modulo.
    ::// if (m_string[[{3}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{3}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{4}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{4}]] * current_power) % m_modulo.
    ::// if (m_string[[{5}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{5}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{6}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{6}]] * current_power) % m_modulo.
    ::// if (m_string[[{7}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{7}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{8}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{8}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_10: UExpression PhantomType true.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    |-----------------------------.
    ::// if (m_string[[{0}]] == {0}) then { exit_ }.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo.
    ::// if (m_string[[{1}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{2}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{2}]] * current_power) % m_modulo.
    ::// if (m_string[[{3}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{3}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{4}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{4}]] * current_power) % m_modulo.
    ::// if (m_string[[{5}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{5}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{6}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{6}]] * current_power) % m_modulo.
    ::// if (m_string[[{7}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{7}]] * current_power) % m_modulo.
    |-----------------------------.
    ::// if (m_string[[{8}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{8}]] * current_power) % m_modulo.
    ::// if (m_string[[{9}]] == {0}) then { exit_ }.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync. 

EndContract.
GenerateLocalState 0 If.
Fail GenerateLocalState 1 If.
GenerateLocalState If.
