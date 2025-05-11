From Hammer Require Import Tactics Hammer.

Require Import UrsusEnvironment.Solidity.current.Environment.

Require Import Simple.Simple.
Import Simple.

Require Import Simple.Common.
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

Definition hash_1_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_1 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 1%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_2_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_2 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 2%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_3_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_3 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 3%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_4_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_4 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 4%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_5_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_5 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 5%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_6_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_6 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash". 
con (m_hash = fst (reference_hash_implementation 6%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_7_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_7 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 7%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_8_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_8 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 8%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_9_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_9 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 9%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_10_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_10 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 10%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_11_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_11 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 11%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_12_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_12 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 12%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_13_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_13 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 13%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_14_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_14 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 14%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_15_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_15 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 15%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_16_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_16 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 16%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_17_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_17 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 17%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_18_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_18 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 18%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_19_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_19 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 19%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_20_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_20 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 20%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_21_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_21 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 21%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_22_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_22 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 22%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_23_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_23 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 23%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_24_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_24 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 24%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_25_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_25 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 25%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_26_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_26 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 26%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_27_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_27 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 27%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_28_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_28 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 28%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_29_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_29 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 29%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_30_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_30 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 30%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_31_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_31 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 31%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_32_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_32 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 32%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_33_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_33 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 33%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_34_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_34 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 34%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_35_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_35 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 35%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_36_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_36 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 36%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_37_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_37 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 37%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_38_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_38 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 38%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_39_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_39 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 39%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.

Definition hash_40_correct_def (ll: LedgerLRecord rec) : Prop.
execs0 (hash_40 rec def) :
ll | "m_string" "m_modulo" "m_multiplier" -> l1 | "m_hash".
con (m_hash = fst (reference_hash_implementation 40%nat m_string (uint2N m_multiplier) (uint2N m_modulo))).
Defined.