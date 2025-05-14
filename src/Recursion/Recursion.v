Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UrsusPatterns.Solidity.TVM.EverBase.

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
    uint64 * uint64
].

Local Open Scope nat_scope.
Local Open Scope Q_scope.
Local Open Scope N_scope. 

#[returns=ret_]
Ursus Definition hash_1: UExpression (uint64 * uint64) false.
{
    ::// m_hash := {0}.
    ::// m_current_power := {1}.
    ::// m_hash := (m_hash + m_string[[{0}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_2: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_1().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{1}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_3: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_2().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{2}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_4: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_3().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{3}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_5: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_4().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{4}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_6: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_5().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{5}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.  

#[returns=ret_]
Ursus Definition hash_7: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_6().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{6}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_8: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_7().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{7}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_9: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_8().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{8}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_10: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_9().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{9}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_11: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_10().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{10}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_12: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_11().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{11}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_13: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_12().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{12}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_14: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_13().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{13}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_15: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_14().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{14}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_16: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_15().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{15}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_17: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_16().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{16}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_18: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_17().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{17}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_19: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_18().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{18}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_20: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_19().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{19}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_21: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_20().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{20}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_22: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_21().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{21}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_23: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_22().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{22}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_24: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_23().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{23}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_25: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_24().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{24}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_26: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_25().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{25}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_27: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_26().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{26}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_28: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_27().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{27}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_29: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_28().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{28}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_30: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_29().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{29}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_31: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_30().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{30}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_32: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_31().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{31}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_33: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_32().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{32}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_34: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_33().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{33}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_35: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_34().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{34}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_36: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_35().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{35}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_37: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_36().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{36}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_38: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_37().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{37}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_39: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_38().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{38}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

#[returns=ret_]
Ursus Definition hash_40: UExpression (uint64 * uint64) false.
{
    ::// [m_current_power, m_hash] := hash_39().
    ::// m_current_power := (m_current_power * m_multiplier) % m_modulo.
    ::// m_hash := (m_hash + m_string[[{39}]] * m_current_power) % m_modulo.
    ::// ret_ := [m_current_power, m_hash] |.
}
return.
Defined.
Sync.

EndContract.
GenerateLocalState 0 Recursion.
Fail GenerateLocalState 1 Recursion.
GenerateLocalState Recursion.
