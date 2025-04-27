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

Ursus Definition hash_11: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_12: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_13: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_14: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_15: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_16: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_17: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_18: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_19: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_20: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_21: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_22: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_23: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{22}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_24: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{22}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{23}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_25: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{22}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{23}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{24}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_26: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{22}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{23}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{24}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{25}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_27: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{22}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{23}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{24}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{25}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{26}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_28: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{22}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{23}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{24}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{25}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{26}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{27}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_29: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{22}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{23}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{24}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{25}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{26}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{27}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{28}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_30: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{22}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{23}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{24}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{25}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{26}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{27}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{28}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{29}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_31: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{22}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{23}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{24}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{25}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{26}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{27}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{28}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{29}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{30}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_32: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{22}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{23}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{24}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{25}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{26}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{27}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{28}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{29}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{30}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{31}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_33: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{22}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{23}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{24}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{25}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{26}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{27}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{28}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{29}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{30}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{31}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{32}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_34: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{22}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{23}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{24}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{25}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{26}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{27}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{28}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{29}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{30}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{31}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{32}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{33}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_35: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{22}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{23}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{24}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{25}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{26}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{27}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{28}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{29}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{30}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{31}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{32}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{33}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{34}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_36: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{22}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{23}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{24}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{25}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{26}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{27}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{28}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{29}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{30}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{31}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{32}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{33}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{34}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{35}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_37: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{22}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{23}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{24}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{25}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{26}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{27}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{28}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{29}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{30}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{31}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{32}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{33}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{34}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{35}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{36}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_38: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{22}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{23}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{24}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{25}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{26}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{27}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{28}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{29}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{30}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{31}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{32}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{33}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{34}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{35}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{36}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{37}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_39: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{22}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{23}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{24}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{25}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{26}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{27}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{28}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{29}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{30}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{31}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{32}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{33}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{34}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{35}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{36}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{37}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{38}]] * current_power) % m_modulo |.
}
return.
Defined.
Sync.

Ursus Definition hash_40: UExpression PhantomType false.
{
    ::// var00 current_power: uint64 := {1} ;_|.
    ::// m_hash := {0} ;_|.
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
    ::// m_hash := (m_hash + m_string[[{9}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{10}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{12}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{14}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{16}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{18}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{20}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{22}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{23}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{24}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{25}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{26}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{27}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{28}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{29}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{30}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{31}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{32}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{33}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{34}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{35}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{36}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{37}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    |-----------------------------.
    ::// m_hash := (m_hash + m_string[[{38}]] * current_power) % m_modulo.
    ::// current_power := (current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{39}]] * current_power) % m_modulo |.
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
