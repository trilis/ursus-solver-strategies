Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusContractCreator.BaseContracts.EverContract.
Set UrsusPrefixTactic "PrefixOnlyURValue".

#[translation = off]
#[quickchick = off]
#[language = solidity]
Contract Simple ;
Sends To  ; 
Inherits EverBaseContract ;
Types ;
Record Contract := {
    m_string: uint64[];
    m_multiplier: uint64;
    m_modulo: uint64;
    m_hash: uint64;
    result: uint64
}.
SetUrsusOptions.

Local Close Scope N_scope.
Local Close Scope Q_scope.
Local Close Scope nat_scope.

UseLocal Definition _ := [
    uint64;
    slice_;
    cell_
].

Local Open Scope nat_scope.
Local Open Scope Q_scope.
Local Open Scope N_scope. 

Ursus Definition hash_1: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_2: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_3: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{2}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_4: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{2}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{3}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_5: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{2}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{3}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{4}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_6: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{2}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{3}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{4}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{5}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_7: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{2}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{3}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{4}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{5}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{6}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_8: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{2}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{3}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{4}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{5}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{6}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{7}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_9: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{2}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{3}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{4}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{5}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{6}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{7}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{8}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_10: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0}.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{0}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{2}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{3}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{4}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{5}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{6}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{7}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{8}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

(*
uint64 result;
function f(uint64 a, uint64 b) {
    uint64 x = result;
    x = x + a;
    x = x - b;
    result = x;
}
*)
Ursus Definition test (a: uint64) (b: uint64): UExpression PhantomType false.
{
    ::// var00 x: uint64 := result ;_|.
    ::// x := x + a.
    ::// x := x - b.
    ::// result := x |.
}
return.
Defined.
Sync.

EndContract.
GenerateLocalState 0 Simple.
Fail GenerateLocalState 1 Simple.
GenerateLocalState Simple.
