Require Import SimpleContract.Tactics.confirmTransaction.

SetDefaultOpaques "SimpleContract".

(*
Arguments setPruvendoRecordPair {T} {FT} & {H} _ _.

Definition MUL11_TCI_def (ll: LedgerLRecord rec) 
                   (transactionId : uint64): Prop.
err0 (confirmTransaction rec def transactionId) ll
    | "msg_pubkey" "m_custodians" "m_ownerKey".
execs0 (removeExpiredTransactions_ rec def ) : ll  -> l2 |  "m_transactions" "m_transactions[transactionId]/confirmationsMask".
set (oindex := m_custodians[msg_pubkey]? ).
set (index := unMaybe oindex).
set (otxn := m_transactions[transactionId]? ).
set (confirmed := xIntBitOpAnd (uint2N confirmationsMask) (uint2N (xIntBitOpLeft (1:uint8) index): uint32)).
set (req1 := isSome oindex).
set (req2 := isSome otxn).
set (req3 := negb (negb (Common.eqb confirmed 0 ))).
con (negb (req1 && req2 && req3)).
Defined.


Definition TC01_1_def (ll: LedgerLRecord rec) 
                   (transactionId : uint64): Prop.
execs0 (confirmTransaction rec def transactionId) :
ll  ->  l1 | "m_transactions".
no_err (confirmTransaction rec def transactionId) l0.
execs0 (removeExpiredTransactions_ rec def ) : ll  -> l2 |  "m_transactions[transactionId]/signsReceived"
                                                            "m_transactions[transactionId]/signsRequired".
hyp (xIntGeb (xIntPlus signsReceived  1)  signsRequired  = true).
set (otxn := m_transactions[transactionId]? ).
con (otxn = None).
Defined.

Definition TC01_2_def (ll: LedgerLRecord rec) 
                   (transactionId : uint64): Prop.
execs0 (confirmTransaction rec def transactionId) :
ll  | "block_timestamp" "_address" ->  l1 |  "#msgs#IDefault".
no_err (confirmTransaction rec def transactionId) l0.
execs0 (removeExpiredTransactions_ rec def ) : ll  -> l2 |  "m_transactions[transactionId]/signsReceived" 
                                                            "m_transactions[transactionId]/signsRequired"
                                                            "m_transactions[transactionId]/dest"
                                                            "m_transactions[transactionId]/value"
                                                            "m_transactions[transactionId]/bounce"
                                                            "m_transactions[transactionId]/sendFlags"
                                                            "m_transactions[transactionId]/payload"
                                                            "m_transactions[transactionId]/cc".
hyp (xIntGeb (xIntPlus signsReceived  1)  signsRequired  = true).
msg_transfer 0 IDefaultQueue.

(*NOT SPECIFIED*)split. con false. (*internal*)
split. con dest. (* dest *)
(*NOT SPECIFIED*)split. con block_timestamp. (* time *)
(*NOT SPECIFIED*)split. con payload. (* body *)
(*NOT SPECIFIED*)split. con default. (* stateInit *)
(*NOT SPECIFIED*)split. con (convert_uint _ sendFlags). compute. congruence. (* flags *)
(*NOT SPECIFIED*)split. con default. (* callback *)
(*NOT SPECIFIED*)split. con default. (* sig *)
(*NOT SPECIFIED*)split. con default. (* expire *)
(*NOT SPECIFIED*)split. con default. (* pubkey *)
(*NOT SPECIFIED*)split. con default. (* onErrorId *)
(*NOT SPECIFIED*)split. con default. (* signBox *)
split. con _address. (* sender *)
(*NOT SPECIFIED*)split. con value. (* value *)
(*NOT SPECIFIED*)split. con bounce. (* bounce *)
con cc.

Defined.



Definition TC01_3_def (ll: LedgerLRecord rec) 
                   (transactionId : uint64): Prop.
execs0 (confirmTransaction rec def transactionId) :
ll | "m_custodians" "msg_pubkey" ->  l1 |  "m_requestsMask".
no_err (confirmTransaction rec def transactionId) l0.
execs0 (removeExpiredTransactions_ rec def ) : ll  -> l2 |  "m_transactions[transactionId]/signsReceived" "m_transactions[transactionId]/signsRequired" "m_requestsMask".
hyp (xIntGeb (xIntPlus signsReceived  1)  signsRequired  = true).
set (oindex := m_custodians[msg_pubkey]? ).
set (index := unMaybe oindex).
(*mask-({1}<<({8}*uint256(index__)))*)
con (m_requestsMask = xIntMinus m_requestsMask'   (xIntBitOpLeft (1:uint256) (xIntMult (8:uint256) (uint2N ( index):uint256))) ).
Defined.

Definition TC03_def (ll: LedgerLRecord rec) 
                   (transactionId : uint64): Prop.
execs0 (confirmTransaction rec def transactionId) :
ll | "m_custodians" "msg_pubkey" ->  l1 |   "m_transactions[transactionId]/confirmationsMask" "m_transactions[transactionId]/signsReceived".
no_err (confirmTransaction rec def transactionId) l0.
execs0 (removeExpiredTransactions_ rec def ) : ll  -> l2 |  "m_transactions[transactionId]/signsReceived" "m_transactions[transactionId]/signsRequired"  "m_transactions[transactionId]/confirmationsMask".
hyp (xIntGeb (xIntPlus signsReceived'  1)  signsRequired  = false).
set (oindex := m_custodians[msg_pubkey]? ).
set (index := unMaybe oindex).
(*mask | (uint32({1})<<custodianIndex)*)
con+ (Common.eqb confirmationsMask  (xIntBitOpOr confirmationsMask'   (uint2N (xIntBitOpLeft (1:uint8)  index):uint32) ) = true).
con (Common.eqb signsReceived (xIntPlus signsReceived'  1) = true).
Defined.


(************************************************************************************)

Lemma removeExpiredTransactions__eval_exists  (l: LedgerLRecord rec):
exists s, 
eval_state
(Uinterpreter
   (removeExpiredTransactions_ rec def )) l = ControlValue _ s. Admitted.


#[global] Instance _eve_removeExpiredTransactions_: 
          ExistsEvalIndex _ _ (@removeExpiredTransactions_) :=
{|
  __eval_exists := @removeExpiredTransactions__eval_exists;
|}.


Lemma removeExpiredTransactions__exec_exists (ll: LedgerLRecord rec): 
exists m_transactions m_requestsMask, 
exec_state (Uinterpreter (removeExpiredTransactions_ rec def)) ll = 
{$$ ll with {$$ Ledger_MainState ll with m_transactions ⇒ _m_transactions;
                                            m_requestsMask ⇒ _m_requestsMask $$}
                                          ⇒ Ledger_MainState $$}.
Admitted.

#[global] Instance _exe_removeExpiredTransactions_: 
          ExistsExecIndex _ _ (@removeExpiredTransactions_) :=
{|
  __exec_exists := @removeExpiredTransactions__exec_exists;
|}.

Axiom removeExpiredTransactions__loc_safe : forall (ll: LedgerLRecord rec),
exec_state (Uinterpreter (removeExpiredTransactions_ rec def)) ll = 
exec_state (Uinterpreter (removeExpiredTransactions_ rec def)) {$$ ll with Ledger_LocalState := default $$}.

Lemma confirmTransaction__eval_exists (l: LedgerLRecord rec) (transactionId : uint64) (txn : TransactionLRecord) (custodianIndex : uint8):
exists s,
eval_state
(Uinterpreter
   (confirmTransaction_ rec def transactionId txn custodianIndex)) l = ControlValue _ s. 
Proof.
    match goal with
        | |- context [ eval_state ?f ?l ] => remember (eval_state f l) as v
    end.
    dependent destruction v.
    now eexists.
Qed.

#[global] Instance _eve_confirmTransaction_: 
          ExistsEvalIndex _ _ (@confirmTransaction_) :=
{|
  __eval_exists := @confirmTransaction__eval_exists;
|}.


Lemma confirmTransaction__exec_exists (ll: LedgerLRecord rec) (transactionId : uint64) (txn : TransactionLRecord) (custodianIndex : uint8): 
exists m_transactions m_requestsMask, 
exec_state (Uinterpreter (confirmTransaction_ rec def transactionId txn custodianIndex)) ll = 
{$$ ll with {$$ Ledger_MainState ll with m_transactions ⇒ _m_transactions;
                                            m_requestsMask ⇒ _m_requestsMask $$}
                                          ⇒ Ledger_MainState $$}.
Admitted.

#[global] Instance _exe_confirmTransaction_: 
          ExistsExecIndex _ _ (@confirmTransaction_) :=
{|
  __exec_exists := @confirmTransaction__exec_exists;
|}.


(* ********************************************************************************************** *)

Ltac compute_destructed_ledgers' Ledger pat ::=
    repeat
    multimatch goal with 
    | H: ?x = ?X |- _ => match type of x with
                          | _ => match X with 
                                      | context [pat] => timeout 5 vm_compute in H
                                      end 
                          end
    end.

(* ********************************************************************************************** *)

Lemma MUL11_TCI_prf ll transactionId :
MUL11_TCI_def ll transactionId.
Proof. Admitted. (*
    start_proof. 
    time confirmTransaction_start. (* 4.093 secs *)
    time continue_all @findCustodian_
                      @isConfirmed_
                      @checkBit_
                      (* @confirmTransaction_ *) 
                      @setConfirmed_
                      @decMaskValue_
                      @get. (* 1.138 secs *) 

    time prepare_all ll P. (* 15.797 secs *)
    time process_pure_eval_execs. (* 0.000 secs *)
    print_ifs2.

(*     compute in H0. subst y0.
 *)    compute_destructed_ledgers loc_.

    print_ifs2.
    check_evals_execs. 


    single_replace y54 s3.
    2: { 
        time bottom_up_goal_solver. (*  secs *)
    }
    single_replace y1 msg8.
    2: { 
        time bottom_up_goal_solver. (*  secs *) 
    }
    setoid_rewrite <- H55.
    clear H55.
    single_replace y59 y55.
    2: { 
        time bottom_up_goal_solver. (*  secs *)
    }
    destruct y55; compute in H65; subst y65.
    -
    match goal with
        | |- context [ exec_state _ ?l ] => replace l with {$$y6 with Ledger_LocalState := default $$} 
    end.
    2: {
        time bottom_up_goal_solver. (* 24.39 secs *)
    }

    rewrite <- removeExpiredTransactions__loc_safe.
    setoid_rewrite <- H7.
    time process_multiexists. (*  secs *)

    match goal with
        | |- context [ ?trx [transactionId] ? ] => replace trx with y8 
    end.
    unfold hmapFindWithDefault.
    setoid_rewrite <- H9.
    print_ifs2.
    single_replace y13 y9.
    2: {
        time bottom_up_goal_solver. (*  secs *)
    }
print_ifs2.
    destruct y9; compute in H38; subst y38.
    +
    time solve_full_error.
    +
    with_strategy opaque [isError]
    compute.
    with_strategy opaque 
    [N.land N.ltb N.leb N.shiftl N.shiftr N.mul]
    time solve_full_error. (* 93.537 secs *)
    -
    with_strategy opaque [isError]
    compute.
     time process_multiexists. (*  secs *)
     with_strategy opaque 
     [N.land N.ltb N.leb N.shiftl N.shiftr N.mul]
     time solve_full_error. (* 163 secs *)
 
Time Qed. (* 1777.585 secs *)
 *)


Lemma TC01_1_prf ll transactionId :
      TC01_1_def ll transactionId.
Proof.
     start_proof. process_no_err_hyp C MUL11_TCI_prf.
     time confirmTransaction_start. (* 11.538 secs *) (* AL: 0.855 secs *)
     time continue_all @findCustodian_
                       @isConfirmed_
                       @checkBit_
                       @confirmTransaction_ 
(*                           @tvm_transfer @deduct_currencies 
 *)                       @setConfirmed_
                       @decMaskValue_
                       @get. (* 4.625 secs *) (* AL: 1.936 secs*)
 
     time prepare_all ll P. (*  94.514 secs *) (* AL: 23.949 secs *)
     time process_pure_eval_execs. (* 0.000 secs *) (* AL: 0.000 secs *)
     print_ifs2. (* AL: 0.000 secs *)
 
 (*     compute in H0. subst y0.
  *)    compute_destructed_ledgers loc_.
 
     print_ifs2.
     single_replace y54 s3.
     2: { 
         time bottom_up_goal_solver. (*  AL: 3.068 secs *)
     }
     single_replace y1 msg8.
     2: { 
         time bottom_up_goal_solver. (*  secs *) 
     }
     single_replace y59 y55.
     2: { 
         time bottom_up_goal_solver. (* AL: 7.065 secs *)
     }

(* req1 = C *)
print_ifs2.
single_replace y65 true.
2 : { rewrite <- C. time bottom_up_goal_solver. } 
remember (s3 [msg8]?).
destruct y; try discriminate C.
subst y55.
(*      destruct y55; compute in H65; subst y65.
2 :{ setoid_rewrite <- H55 in C. compute in C. discriminate C. }
clear C.
 *)
match goal with
| C0: isSome (toValue (eval_state (sRReader (m_transactions_right rec def)) ?l )) [transactionId] ? = _  |- _ => remember l as l_ret 
end.
match goal with
| Heql_ret: l_ret = exec_state _ ?l  |- _ => remember l as l_y6 
end.
assert (l_y6 = {$$y6 with Ledger_LocalState := default $$} ).
with_strategy opaque [ removeExpiredTransactions_ ]
time bottom_up_goal_solver. (*  17.478 secs *) (* AL: 9.77 secs *)
(* rewrite H in Heql_ret.
 *)clear Heql_y6.  subst l_y6. 

rewrite <- removeExpiredTransactions__loc_safe in Heql_ret.
setoid_rewrite <- H7 in Heql_ret.
subst l_ret.
time process_multiexists. (* 6.24 secs *) (* AL: 3.174 secs *)

check_evals_execs. 
print_ifs2.
(* req 2 = C0*)
clear Heqy.
unfold hmapFindWithDefault in C1.
unfold hmapFindWithDefault in C2.
match goal with
    | C0 :  isSome ?x [transactionId] ? = _ |-  _ => single_replace x y8 (* remember x  as trx *)
end.
2 : { time bottom_up_goal_solver. (*  secs *) }

(*  single_replace y13 y9.

2: { 
    time bottom_up_goal_solver. (*  secs *)
}
 *)
 setoid_rewrite <- H9 in C0.
 setoid_rewrite <- H9 in C1.
 setoid_rewrite <- H9 in C2.
clear H9.
destruct y9; try discriminate C0.
clear C0 C.

single_replace y13 (Some t).
2 : {
    with_strategy opaque [TransactionLGetField 
                          TransactionLSetField]
     time bottom_up_goal_solver. (* AL: 17.95 secs *)
}

single_replace y38 true.
2 : {
    with_strategy opaque [TransactionLGetField 
                          TransactionLSetField]
     time bottom_up_goal_solver. (* AL: 0 secs *)
}

(* 
     unfold hmapFindWithDefault.
     unfold hmapFindWithDefault in C1.
     unfold hmapFindWithDefault in C2.
     single_replace y13 y9.
     2: { 
         time bottom_up_goal_solver. (*  secs *)
     }
match goal with
    | C0 :  isSome ?x [transactionId] ? = _ |-  _ => remember x  as trx
 end.
assert (trx = y8).
time bottom_up_goal_solver. (*  1.234 secs *)
rewrite H in Heqtrx.
subst trx.

     destruct y9; compute in H116; subst y166.
2 :{ setoid_rewrite <- H9 in C0. compute in C0. discriminate C0. }
clear C0.
(* setoid_rewrite <- H9.
 *)compute in H38. subst y38.
setoid_rewrite <- H9 in C1.
setoid_rewrite <- H9 in C2.

time process_multiexists. (* 0.25 secs *)

     print_ifs2.
 *)
 (* req3 = C1 *)
print_ifs2.
single_replace y42 true.
2 : {
    rewrite <- C1.
    with_strategy opaque [TransactionLSetField 
                          TransactionLGetField 
                          N.add N.land N.ltb N.leb N.shiftl N.shiftr N.mul
                          negb N.eqb]
    time bottom_up_goal_solver. (* 152.531 sec*) (* AL: 47.511 secs *)
} clear C1.
(* 
setoid_rewrite <- H55 in C1.
match goal with
    | C1 :  negb(?x ) = _ |-  _ => remember x  as x_y92
 end.

 assert (x_y92 =  y92).
{ clear H9. clear H8. clear H55.
 with_strategy opaque 
    [N.land N.ltb N.leb N.shiftl N.shiftr N.mul]
 time bottom_up_goal_solver. (*  1.234 secs *)
}
rewrite H in C1.
clear H. subst x_y92.
single_replace y82 y92.
2: { 
    time bottom_up_goal_solver. (*  139.603 secs *)
}

destruct y92; compute in H42; subst y42.
{ compute in C1. discriminate C1. } clear C1.
 *)
print_ifs2.
(* condition C2 *)
single_replace y144 true.
2 : {
    rewrite <- C2. 
    with_strategy opaque [TransactionLSetField 
                          TransactionLGetField 
                          N.land N.ltb N.leb N.shiftl N.shiftr N.mul
                          negb N.eqb]
    time bottom_up_goal_solver. (* 196.717 sec*) (* AL: 80.784 secs *)
} clear C2.


(* 

match goal with
    | C2 : xIntGeb ?x ?y = true |-  _ => remember x  as x_y102; remember y  as x_y103
 end.
assert (x_y102 = y102). time bottom_up_goal_solver. (*  102.654  secs *)
assert (x_y103 = y103). time bottom_up_goal_solver. (*  96.651 secs *)
rewrite H in C2; clear H; subst x_y102.
rewrite H1 in C2; clear H1; subst x_y103.
setoid_rewrite <- H144 in C2.
destruct y144; compute in H145; subst y145.
2: {discriminate C2. } clear C2.
time process_multiexists. (* 0.25 secs *)

 *)print_ifs2. (* no more ifs *)
check_evals_execs. 

with_strategy opaque [TransactionLSetField 
    TransactionLGetField deduct_currencies_helper 
    N.land N.ltb N.leb N.shiftl N.shiftr N.mul
    deleteListPair deleteListPair_list]
time bottom_up_goal_solver. (*  1098.819 secs *) (* AL: 68.397 secs *)
apply lookup_delete_none.

Unset Kernel Term Sharing.
Optimize Proof.
Optimize Heap.

Time Qed. (* AL: 64.844 secs *)

 Lemma TC01_2_prf ll transactionId :
 TC01_2_def ll transactionId.
 Proof.
     start_proof. process_no_err_hyp C MUL11_TCI_prf.
     time confirmTransaction_start. (* 11.538 secs *)
     time continue_all @findCustodian_
                       @isConfirmed_
                       @checkBit_
                       @confirmTransaction_ 
                          @tvm_transfer @deduct_currencies 
                       @setConfirmed_
                       @decMaskValue_
                       @get. (* 4.625 secs *) 
 
     time prepare_all ll P. (*  94.514 secs *)
     time process_pure_eval_execs. (* 0.000 secs *)
     print_ifs2.
 
 (*     compute in H0. subst y0.
  *)    compute_destructed_ledgers loc_.
 
     print_ifs2.
     single_replace y54 s3.
     2: { 
         time bottom_up_goal_solver. (*  secs *)
     }
     single_replace y1 msg8.
     2: { 
         time bottom_up_goal_solver. (*  secs *) 
     }
     single_replace y59 y55.
     2: { 
         time bottom_up_goal_solver. (*  secs *)
     }

(* req1 = C*)
     destruct y55; compute in H65; subst y65.
2 :{ setoid_rewrite <- H55 in C. compute in C. discriminate C. }
clear C.
match goal with
| |- context [ eval_state (sRReader (m_transactions_right rec def))?l ] => remember l as l_ret 
end.
match goal with
| Heql_ret: l_ret = exec_state _ ?l  |- _ => remember l as l_y6 
end.
assert (l_y6 = {$$y6 with Ledger_LocalState := default $$} ).
time bottom_up_goal_solver. (*  17.478 secs *)
rewrite H in Heql_ret.
clear H. subst l_y6. 

rewrite <- removeExpiredTransactions__loc_safe in Heql_ret.
setoid_rewrite <- H7 in Heql_ret.
subst l_ret.
time process_multiexists. (* 6.24 secs *)

     check_evals_execs. 
     print_ifs2.
(* req 2 = C0*)
     unfold hmapFindWithDefault.
     unfold hmapFindWithDefault in C1.
     unfold hmapFindWithDefault in C2.
     single_replace y13 y9.
     2: { 
         time bottom_up_goal_solver. (*  secs *)
     }
match goal with
    | C0 :  isSome ?x [transactionId] ? = _ |-  _ => remember x  as trx
 end.
assert (trx = y8).
time bottom_up_goal_solver. (*  1.234 secs *)
rewrite H in Heqtrx.
subst trx.

     destruct y9; compute in H116; subst y166.
2 :{ setoid_rewrite <- H9 in C0. compute in C0. discriminate C0. }
clear C0.
setoid_rewrite <- H9.
compute in H38. subst y38.
setoid_rewrite <- H9 in C1.
setoid_rewrite <- H9 in C2.

time process_multiexists. (* 0.25 secs *)

     print_ifs2.
(* req3 = C1 *)
setoid_rewrite <- H55 in C1.
match goal with
    | C1 :  negb(?x ) = _ |-  _ => remember x  as x_y92
 end.

 assert (x_y92 =  y92).
{ clear H9. clear H8. clear H55.
 with_strategy opaque 
    [N.land N.ltb N.leb N.shiftl N.shiftr N.mul]
 time bottom_up_goal_solver. (*  1.234 secs *)
}
rewrite H in C1.
clear H. subst x_y92.
single_replace y82 y92.
2: { 
    time bottom_up_goal_solver. (*  139.603 secs *)
}

destruct y92; compute in H42; subst y42.
{ compute in C1. discriminate C1. } clear C1.

print_ifs2.
(* condition C2 *)
match goal with
    | C2 : xIntGeb ?x ?y = true |-  _ => remember x  as x_y102; remember y  as x_y103
 end.
assert (x_y102 = y102). time bottom_up_goal_solver. (*  102.654  secs *)
assert (x_y103 = y103). time bottom_up_goal_solver. (*  96.651 secs *)
rewrite H in C2; clear H; subst x_y102.
rewrite H1 in C2; clear H1; subst x_y103.
setoid_rewrite <- H144 in C2.
destruct y144; compute in H145; subst y145.
2: {discriminate C2. } clear C2.
time process_multiexists. (* 0.25 secs *)

print_ifs2.
rewrite H9. clear H8. clear H55.
with_strategy opaque [deduct_currencies_helper]
time bottom_up_goal_solver. (*  secs *)
Admitted.*)