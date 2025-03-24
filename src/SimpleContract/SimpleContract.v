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
Record Transaction := {
    id : uint64;
    confirmationsMask : uint32;
    signsRequired : uint8;
    signsReceived : uint8;
    creator : uint256;
    index : uint8;
    dest : address;
    value : uint128;
    cc : mapping(uint32)(varUint32);
    sendFlags : uint16;
    payload : TvmCell;
    bounce : bool
},
Record UpdateRequest := {
    id : uint64;
    index : uint8;
    signs : uint8;
    confirmationsMask : uint32;
    creator : uint256;
    codeHash : uint256;
    custodians : uint256[];
    reqConfirms : uint8
},
Record CustodianInfo := {
    index : uint8;
    pubkey : uint256
};
Constants 
Definition MAX_QUEUED_REQUESTS : uint8 := 5
Definition EXPIRATION_TIME : uint64 := 3601
Definition MAX_CUSTODIAN_COUNT : uint8 := 32
Definition MIN_VALUE : uint128 := 1000000
Definition MAX_CLEANUP_TXNS : uint256 := 40
Definition FLAG_PAY_FWD_FEE_FROM_BALANCE : uint8 := 1
Definition FLAG_IGNORE_ERRORS : uint8 := 2
Definition FLAG_SEND_ALL_REMAINING : uint8 := 128;
Record Contract := {
    m_ownerKey:uint256;
    m_requestsMask:uint256;
    m_transactions:mapping(uint64)((_ResolveRecord("Transaction")));
    m_custodians:mapping(uint256)(uint8);
    m_custodianCount:uint8;
    m_updateRequests:mapping(uint64)((_ResolveRecord("UpdateRequest")));
    m_updateRequestsMask:uint32;
    m_require_dVotes:uint8;
    m_defaultRequiredConfirmations:uint8
}.
SetUrsusOptions.

Local Close Scope N_scope.
Local Close Scope Q_scope.
Local Close Scope nat_scope.

UseLocal Definition _ := [
    (string**string);
    uint64;
    TvmCell;
    uint256;
    uint256[];
    uint8;
    UpdateRequestLRecord[];
    CustodianInfoLRecord[];
    uint64[];
    TransactionLRecord[];
    TransactionLRecord;
    (uint8**uint8**uint64**uint128**uint8**uint8);
    uint32;
    bool;
    address;
    uint128;
    mapping(uint32)(varUint32);
    bytes;
    (uint8**uint128**mapping(uint32)(varUint32));
    (uint256**uint256);
    optional(uint8);
    optional((uint64**TransactionLRecord));
    optional(TransactionLRecord);
    optional((uint256**uint8));
    optional((uint64**UpdateRequestLRecord));
    UpdateRequestLRecord;
    optional(UpdateRequestLRecord)
].

Local Open Scope nat_scope.
Local Open Scope Q_scope.
Local Open Scope N_scope. 

(* #[nonpayable, public, returns=result_]
Ursus Definition calcbkreward (vpd  : uint128) (rac  : uint128) (t : uint128) (totalstake : uint128) (valstake : uint128) (maxrt : uint128): UExpression (uint128) false. 
::// result_ := {} |. return. Defined. Sync.
#[nonpayable, public, no_body]
Ursus Definition mintecc (vpstaked  : uint64) (key  : uint32): UExpression (PhantomType) false. 
return. Defined. Sync.
#[nonpayable, public, no_body]
Ursus Definition exchange (stake  : uint64): UExpression (PhantomType) false. 
return. Defined. Sync.
#[nonpayable, public, no_body]
Ursus Definition mintshell (stake  : uint64): UExpression (PhantomType) false. 
return. Defined. Sync.
#[nonpayable, public, no_body]
Ursus Definition calcminstake (bkpd : uint128)(t : uint128)(bk_num : uint128)(need_bk_num : uint128): UExpression varUint32 false. 
return. Defined. Sync.
#[nonpayable, public, no_body]
Ursus Definition poseidon (index_mod_4:uint8) (expire_at:uint64) (epk:uint256) (modulus:bytes) (iss_base_64:string) (header_base_64:string) (zkaddr_:string):UExpression bytes false.
return. Defined. Sync.
#[nonpayable, public, no_body]
Ursus Definition cnvrtshellq (value__ : uint64): UExpression PhantomType false.
return. Defined. Sync.
#[nonpayable, public, no_body]
Ursus Definition vergrth16 (proof : bytes) (factors_: bytes) (num_: uint256): UExpression boolean false.
return. Defined. Sync. *)

Local Open Scope ursus_scope_Transaction.
Local Open Scope ursus_scope_UpdateRequest.
Local Open Scope ursus_scope_CustodianInfo.

Definition tvm_ctos_pure (cell : TvmCell): uint256 := default.

#[pure, private, returns=result_]
Ursus Definition tvm_ctos (cell : TvmCell): UExpression (uint256) false.
{
    :://  result_ := {urvalue_bind cell (fun c => URScalar of tvm_ctos_pure c) } |.
}
return.
Defined.
Sync.

Definition tvm_tree_cell_size_pure (slice : uint256): uint256 ** uint256 := default.

#[pure, private, returns=result_]
Ursus Definition tvm_tree_cell_size (slice : uint256): UExpression (uint256 ** uint256) false. 
{
    :://  result_ := {urvalue_bind slice (fun c => URScalar of tvm_tree_cell_size_pure c) } |.
}
return.
Defined.
Sync.


#[nonpayable, private]
Ursus Definition initialize_ (owners : uint256[]) (reqConfirms : uint8): UExpression PhantomType true.
{
    :://  var00 ownerCount: uint8 := {0} ;_|.
    :://  m_ownerKey := owners[[{0}]].
    :://  var00 len: uint256 := owners->length ;_|.
    :://  for (var00 i: uint256 := {0} , ((i<len)&&(ownerCount<MAX_CUSTODIAN_COUNT)) , i ++ ) do { ->> }  .
    {
        :://  var00 key: uint256 := owners[[i]] ;_|.
        :://  if (! m_custodians->exists(key)) then { ->> }  |.
        {
            :://  m_custodians[[key]] := (++) (ownerCount) |.
        }
    }
    :://  m_defaultRequiredConfirmations := (ownerCount<=reqConfirms) ? ownerCount : reqConfirms.
    :://  m_require_dVotes := (ownerCount<={2}) ? ownerCount : (((ownerCount*{2})+{1})/{3}).
    :://  m_custodianCount := ownerCount |.
}
return.
Defined.
Sync.

Elpi FullPrint initialize_.

#[nonpayable, public]
Ursus Definition constructor (owners : uint256[]) (reqConfirms : uint8) (value__ : uint64): UExpression PhantomType true.
{
    :://  cnvrtshellq(value__).
    :://  require_((msg->pubkey()==tvm->pubkey()), #{(IntError 100)}).
    :://  require_(((owners->length>{0})&&(owners->length<=MAX_CUSTODIAN_COUNT)), #{(IntError 117)}).
    :://  require_((reqConfirms>{0}), #{(IntError 123)}).
    :://  tvm->accept().
    :://  initialize_(owners, reqConfirms) |.
}
return.
Defined.
Sync.

#[pure, private, returns=result_]
Ursus Definition getMaskValue_ (mask : uint256) (index__ : uint8): UExpression (uint8) true.
{
    :://  result_ := uint8!(((mask>>({8}*uint256(index__)))&{0xFF})) |.
}
return.
Defined.
Sync.

Elpi FullPrint getMaskValue_.

#[pure, private, returns=result_]
Ursus Definition incMaskValue_ (mask : uint256) (index__ : uint8): UExpression (uint256) false.
{
    :://  result_ := (mask+({1}<<({8}*uint256(index__)))) |.
}
return.
Defined.
Sync.

#[pure, private, returns=result_]
Ursus Definition decMaskValue_ (mask : uint256) (index__ : uint8): UExpression (uint256) false.
{
    :://  result_ := (mask-({1}<<({8}*uint256(index__)))) |.
}
return.
Defined.
Sync.

#[pure, private, returns=result_]
Ursus Definition checkBit_ (mask : uint32) (index__ : uint8): UExpression (bool) false.
{
    :://  result_ := ((mask&(uint32({1})<<index__))!={0}) |.
}
return.
Defined.
Sync.

#[pure, private, returns=result_]
Ursus Definition isConfirmed_ (mask : uint32) (custodianIndex : uint8): UExpression (bool) false.
{
    :://  result_ := checkBit_(mask,custodianIndex) |.
}
return.
Defined.
Sync.

#[pure, private, returns=result_]
Ursus Definition isSubmitted_ (mask : uint32) (custodianIndex : uint8): UExpression (bool) false.
{
    :://  result_ := checkBit_(mask,custodianIndex) |.

}
return.
Defined.
Sync.

#[pure, private, write=mask, returns=result_]
Ursus Definition setConfirmed_ (mask : uint32) (custodianIndex : uint8): UExpression (uint32) false.
{
    :://  mask |= (uint32({1})<<custodianIndex).
    :://  result_ := mask |.
}
return.
Defined.
Sync.

#[pure, private, returns=result_]
Ursus Definition setSubmitted_ (mask : uint32) (custodianIndex : uint8): UExpression (uint32) false.
{
    :://  result_ := setConfirmed_(mask,custodianIndex) |.
}
return.
Defined.
Sync.

#[view, private, returns=result_]
Ursus Definition findCustodian_ (senderKey : uint256): UExpression (uint8) true.
{
    :://  var00 index__: optional(uint8) := m_custodians->fetch(senderKey) ;_|.
    :://  require_(index__->hasValue(), #{(IntError 100)}).
    :://  result_ := index__->get() |.
}
return.
Defined.
Sync.

Elpi FullPrint findCustodian_.

#[view, public]
Ursus Definition exchangeToken (value__ : uint64): UExpression PhantomType true.
{
    :://  var00 index_: uint8 := findCustodian_(msg->pubkey()) ;_|.
 (* warning: impossible identifier in UrsusStatement *)
    :://  tvm->accept().
    :://  cnvrtshellq(value__)|.
}
return.
Defined.
Sync.

(* Notation " x '|' y " := (wrapURValue (un_or' x y)) 
(in custom URValue at level 95, x custom URValue, y custom URValue at level 95) : ursus_scope.
 *)

#[pure, private, returns=result_]
Ursus Definition generateId_ : UExpression (uint64) false.
{
    :://  result_ := ((uint64(block->timestamp) << {32}) \ (block->timestamp & {0xFFFFFFFF}) ) | .

}
return.
Defined.
Sync.

#[pure, private, returns=result_]
Ursus Definition getExpirationBound_ : UExpression (uint64) false.
{
    :://  result_ := ((uint64(block->timestamp)-EXPIRATION_TIME)<<{32}) |.
}
return.
Defined.
Sync.


#[pure, private, write=value__, write=cc, returns=result_]
Ursus Definition getSendFlags_ (value__ : uint128) (allBalance : bool) (cc : mapping(uint32)(varUint32)): UExpression (uint8 ** uint128 ** mapping(uint32)(varUint32)) false.
{
    :://  var00 flags: uint8 := (FLAG_IGNORE_ERRORS \ FLAG_PAY_FWD_FEE_FROM_BALANCE) ;_|.
    :://  if (allBalance) then { ->> } .
    {
        :://  flags := (FLAG_IGNORE_ERRORS \ FLAG_SEND_ALL_REMAINING).
        :://  value__ := uint128(address(this)->balance).
        :://  cc := address(this)->currencies |.
    }
    :://  result_ := [flags, value__, cc] |.
}
return.
Defined.
Sync.

#[nonpayable, external, no_body]
Ursus Definition acceptTransfer (payload : bytes): UExpression PhantomType false.
return.
Defined.
Sync.

#[view, public, write=dest]
Ursus Definition sendTransaction (dest : address) (value__ : uint128) (cc : mapping(uint32)(varUint32)) (bounce : bool) (flags : uint8) (payload : TvmCell): UExpression PhantomType true.
{
    :://  require_((m_custodianCount=={1}), #{(IntError 108)}).
    :://  require_((msg->pubkey()==m_ownerKey), #{(IntError 100)}).
    :://  tvm->accept().
    :://  tvm->transfer(dest, (* varuint16 *) (value__), bounce, uint16(flags), payload, cc) |.
}
return.
Defined.
Sync.

#[nonpayable, private, write=txn]
Ursus Definition confirmTransaction_ (transactionId : uint64) (txn : TransactionLRecord) (custodianIndex : uint8): UExpression PhantomType false.
{
    :://  if (((txn->Transaction_ι_signsReceived+{1})>=txn->Transaction_ι_signsRequired)) then { ->> } else { ->> } | .
    {
        :://  tvm->transfer(txn->Transaction_ι_dest, (* varuint16 *) (txn->Transaction_ι_value), txn->Transaction_ι_bounce, txn->Transaction_ι_sendFlags, txn->Transaction_ι_payload, txn->Transaction_ι_cc).
        :://  m_requestsMask := decMaskValue_(m_requestsMask,txn->Transaction_ι_index).
        :://  m_transactions [transactionId] -> delete |.
    }
    {
        :://  txn->Transaction_ι_confirmationsMask := setConfirmed_(txn->Transaction_ι_confirmationsMask,custodianIndex).
        :://  (txn->Transaction_ι_signsReceived) := (txn->Transaction_ι_signsReceived) + {1}.
        :://  m_transactions[[transactionId]] := txn |.
    }
}
return.
Defined.
Sync.


#[nonpayable, private]
Ursus Definition removeExpiredTransactions_ : UExpression PhantomType true.
{
    :://  var00 marker: uint64 := getExpirationBound_() ;_|.
    :://  var00 otxn: optional((uint64**TransactionLRecord)) := m_transactions->min() ;_|.
    :://  if (! otxn->hasValue()) then { ->/> } .
    {
        :://  exit |.
    }
    :://  var00 (trId : uint64, txn : TransactionLRecord) := otxn->get() ;_|.
    :://  var00 needCleanup: bool := (trId<=marker) ;_|.
    :://  if (! needCleanup) then { ->/> } .
    {
        :://  exit |.
    }
    :://  tvm->accept().
    |----------------------.
    :://  var00 i: uint256 := {0} ;_|.
    :://  while ((needCleanup&&(i<MAX_CLEANUP_TXNS))) do { ->/> }.
    {
        :://  i ++.
        :://  m_requestsMask := decMaskValue_(m_requestsMask,txn->Transaction_ι_index).
        :://  m_transactions [trId] -> delete.
        :://  otxn := m_transactions->next(trId).
        :://  if (! otxn->hasValue()) then { ->> } else { ->/> }  |.
        {
            :://  needCleanup := {false} |.
        }
        {
            :://  [trId, txn] := otxn->get().
            :://  needCleanup := (trId<=marker) |.
        }
    }
    :://  tvm->commit() |.
}
return.
Defined.
Sync.

#[nonpayable, public, write=dest, returns=transId]
Ursus Definition submitTransaction (dest : address) (value__ : uint128) (cc : mapping(uint32)(varUint32)) (bounce : bool) (allBalance : bool) (payload : TvmCell): UExpression (uint64) true.
{
    :://  var00 senderKey: uint256 := msg->pubkey() ;_|.
    :://  var00 index__: uint8 := findCustodian_(senderKey) ;_|.
    :://  require_((value__>=MIN_VALUE), #{(IntError 107)}).
    :://  var00 (bits : uint256, cells : uint256) := tvm_tree_cell_size(tvm_ctos(payload)) ;_|.
    :://  require_(((bits<{8192})&&(cells<{8})), #{(IntError 121)}).
    :://  removeExpiredTransactions_().
    :://  var00 __maskValue__: uint8 := getMaskValue_(m_requestsMask,index__) ;_|.
    :://  require_((__maskValue__<MAX_QUEUED_REQUESTS), #{(IntError 113)}).
    :://  tvm->accept().
    |----------------------.
    :://  var00 (flags : uint8, realValue : uint128, realcc : mapping(uint32)(varUint32)) := getSendFlags_(value__,allBalance,cc) ;_|.
    :://  var00 require_dSigns: uint8 := m_defaultRequiredConfirmations ;_|.
    :://  if ((require_dSigns=={1})) then { ->> } else { ->> } | .
    {
        :://  tvm->transfer(dest, (* varuint16 *) (realValue), bounce, uint16(flags), payload, realcc).
        :://  transId := {0} |.
    }
    {
        :://  m_requestsMask := incMaskValue_(m_requestsMask,index__).
        :://  var00 trId: uint64 := generateId_() ;_|.
        :://  var00 txn: TransactionLRecord := (* Transaction *) [trId,{0},require_dSigns,{0},senderKey,index__,dest,realValue,realcc,uint16(flags),payload,bounce] ;_|.
        :://  confirmTransaction_(trId, txn, index__).
        :://  transId := trId |.
    }
}
return.
Defined.
Sync.


#[nonpayable, public]
Ursus Definition confirmTransaction (transactionId : uint64): UExpression PhantomType true.
{
    :://  var00 index__: uint8 := findCustodian_(msg->pubkey()) ;_|.
    :://  removeExpiredTransactions_().
    :://  var00 otxn: optional(TransactionLRecord) := m_transactions->fetch(transactionId) ;_|.
    :://  require_(otxn->hasValue(), #{(IntError 102)}).
    :://  var00 txn: TransactionLRecord := otxn->get() ;_|.
    :://  require_(! isConfirmed_(txn->Transaction_ι_confirmationsMask,index__), #{(IntError 103)}).
    :://  tvm->accept().
    :://  confirmTransaction_(transactionId, txn, index__) |.
}
return.
Defined.
Sync.

#[pure, public, returns=confirmed]
Ursus Definition isConfirmed (mask : uint32) (index__ : uint8): UExpression (bool) false.
{
    :://  confirmed := isConfirmed_(mask,index__) |.
}
return.
Defined.
Sync.

#[view, public, returns=result_]
Ursus Definition getParameters : UExpression (uint8 ** uint8 ** uint64 ** uint128 ** uint8 ** uint8) false.
{
:://  result_ := [ MAX_QUEUED_REQUESTS, MAX_CUSTODIAN_COUNT, EXPIRATION_TIME, MIN_VALUE, m_defaultRequiredConfirmations, m_require_dVotes ] |.
}
return.
Defined.
Sync.

#[view, public, returns=trans]
Ursus Definition getTransaction (transactionId : uint64): UExpression (TransactionLRecord) true.
{
    :://  var00 txn: optional(TransactionLRecord) := m_transactions->fetch(transactionId) ;_|.
    :://  require_(txn->hasValue(), #{(IntError 102)}).
    :://  trans := txn->get() |.
}
return.
Defined.
Sync.


#[view, public, returns=transactions]
Ursus Definition getTransactions : UExpression (TransactionLRecord[]) true.
{
    :://  var00 bound: uint64 := getExpirationBound_() ;_|.
    :://  var00 otxn: optional((uint64**TransactionLRecord)) := m_transactions->min() ;_|.
    :://  while (otxn->hasValue()) do { ->/> } |.
    {
        :://  var00 (id__ : uint64, txn : TransactionLRecord) := otxn->get() ;_|.
        :://  if ((id__>bound)) then { ->> } .
        {
            :://  transactions->push(txn) |.
        }
        :://  otxn := m_transactions->next(id__) |.
    }
}
return.
Defined.
Sync.

#[view, public, returns=ids]
Ursus Definition getTransactionIds : UExpression (uint64[]) true.
{
    :://  var00 trId: uint64 := {0} ;_|.
    :://  var00 otxn: optional((uint64**TransactionLRecord)) := m_transactions->min() ;_|.
    :://  while (otxn->hasValue()) do { ->/> } |.
    {
        :://  var00 otxn_2: TransactionLRecord ;_|. 
        :://  [trId,  otxn_2 ] := otxn->get().
        :://  ids->push(trId).
        :://  otxn := m_transactions->next(trId) |.
    }
}
return.
Defined.
Sync.


#[view, public, returns=custodians]
Ursus Definition getCustodians : UExpression (CustodianInfoLRecord[]) true.
{
    :://  var00 oind: optional((uint256**uint8)) := m_custodians->min() ;_|.
    :://  while (oind->hasValue()) do { ->/> } |.
    {
        :://  var00 (key : uint256, index__ : uint8) := oind->get() ;_|.
        :://  custodians->push((* CustodianInfo *) [index__,key]).
        :://  oind := m_custodians->next(key) |.
    }
}
return.
Defined.
Sync.

#[view, public, returns=updates]
Ursus Definition getUpdateRequests : UExpression (UpdateRequestLRecord[]) true.
{
    :://  var00 bound: uint64 := getExpirationBound_() ;_|.
    :://  var00 oreq: optional((uint64**UpdateRequestLRecord)) := m_updateRequests->min() ;_|.
    :://  while (oreq->hasValue()) do { ->/> } |.
    {
        :://  var00 (updateId : uint64, req : UpdateRequestLRecord) := oreq->get() ;_|.
        :://  if ((updateId>bound)) then { ->> } .
        {
            :://  updates->push(req) |.
        }
        :://  oreq := m_updateRequests->next(updateId) |.
    }
}
return.
Defined.
Sync.

#[nonpayable, private]
Ursus Definition onCodeUpgrade2 (newOwners : uint256[]) (reqConfirms : uint8): UExpression PhantomType true.
{
    :://  tvm->resetStorage().
    :://  initialize_(newOwners, reqConfirms) |.
}
return.
Defined.
Sync.

#[nonpayable, private]
Ursus Definition confirmUpdate_ (updateId : uint64) (custodianIndex : uint8): UExpression PhantomType false.
{
    :://  var00 request: UpdateRequestLRecord := m_updateRequests[[updateId]] ;_|.
    :://  request->(* UpdateRequest_ι_ *)signs := request->(* UpdateRequest_ι_ *)signs + {1}.
    :://  request->(* UpdateRequest_ι_ *)confirmationsMask := setConfirmed_(request->(* UpdateRequest_ι_ *)confirmationsMask,custodianIndex).
    :://  m_updateRequests[[updateId]] := request |.

}
return.
Defined.
Sync.


#[nonpayable, private]
Ursus Definition deleteUpdateRequest_ (updateId : uint64) (index__ : uint8): UExpression PhantomType false.
{
    :://  m_updateRequestsMask &= ~ (uint32({1})<<index__).
    :://  m_updateRequests [updateId] -> delete |.
}
return.
Defined.
Sync.

#[nonpayable, private]
Ursus Definition removeExpiredUpdateRequests_ : UExpression PhantomType true.
{
    :://  var00 marker: uint64 := getExpirationBound_() ;_|.
    :://  var00 oreq: optional((uint64**UpdateRequestLRecord)) := m_updateRequests->min() ;_|.
    :://  if (! oreq->hasValue()) then { ->/> } .
    {
        :://  exit |.
    }
    :://  var00 (updateId : uint64, req : UpdateRequestLRecord) := oreq->get() ;_|.
    :://  var00 needCleanup: bool := (updateId<=marker) ;_|.
    :://  if (! needCleanup) then { ->/> } .
    {
        :://  exit |.
    }
    :://  tvm->accept().
    |----------------------.
    :://  while (needCleanup) do { ->/> }.
    {
        :://  deleteUpdateRequest_(updateId, req->UpdateRequest_ι_index).
        :://  oreq := m_updateRequests->next(updateId).
        :://  needCleanup := oreq->hasValue().
        :://  if (needCleanup) then { ->/> }  |.
        {
            :://  [updateId, req] := oreq->get().
            :://  needCleanup := (updateId<=marker) |.
        }
    }
    :://  tvm->commit() |.
}
return.
Defined.
Sync.

#[nonpayable, public, returns=updateId]
Ursus Definition submitUpdate (codeHash : uint256) (owners : uint256[]) (reqConfirms : uint8): UExpression (uint64) true.
{
    :://  var00 sender: uint256 := msg->pubkey() ;_|.
    :://  var00 index__: uint8 := findCustodian_(sender) ;_|.
    :://  require_(((owners->length>{0})&&(owners->length<=MAX_CUSTODIAN_COUNT)), #{(IntError 117)}).
    :://  removeExpiredUpdateRequests_().
    :://  require_(! isSubmitted_(m_updateRequestsMask,index__), #{(IntError 113)}).
    :://  tvm->accept().
    :://  m_updateRequestsMask := setSubmitted_(m_updateRequestsMask,index__).
    :://  updateId := generateId_().
    :://  m_updateRequests[[updateId]] := (* UpdateRequest *) [updateId,index__,{0},{0},sender,codeHash,owners,reqConfirms].
    :://  confirmUpdate_(updateId, index__) |.
}
return.
Defined.
Sync.

#[nonpayable, public]
Ursus Definition confirmUpdate (updateId : uint64): UExpression PhantomType true.
{
    :://  var00 index__: uint8 := findCustodian_(msg->pubkey()) ;_|.
    :://  removeExpiredUpdateRequests_().
    :://  var00 oreq: optional(UpdateRequestLRecord) := m_updateRequests->fetch(updateId) ;_|.
    :://  require_(oreq->hasValue(), #{(IntError 115)}).
    :://  var00 request: UpdateRequestLRecord := oreq->get() ;_|.
    :://  require_(! isConfirmed_(request->UpdateRequest_ι_confirmationsMask,index__), #{(IntError 116)}).
    :://  tvm->accept().
    :://  confirmUpdate_(updateId, index__) |.
}
return.
Defined.
Sync.

#[nonpayable, public]
Ursus Definition executeUpdate (updateId : uint64) (code : TvmCell): UExpression PhantomType true.
{
    :://  require_(m_custodians->exists(msg->pubkey()), #{(IntError 100)}).
    :://  removeExpiredUpdateRequests_().
    :://  var00 oreq: optional(UpdateRequestLRecord) := m_updateRequests->fetch(updateId) ;_|.
    :://  require_(oreq->hasValue(), #{(IntError 115)}).
    :://  var00 request: UpdateRequestLRecord := oreq->get() ;_|.
    :://  require_((tvm->hash(code)==request->UpdateRequest_ι_codeHash), #{(IntError 119)}).
    :://  require_((request->UpdateRequest_ι_signs>=m_require_dVotes), #{(IntError 120)}).
    |----------------------.
    :://  tvm->accept().
    :://  deleteUpdateRequest_(updateId, request->UpdateRequest_ι_index).
    :://  tvm->setcode(code).
    :://  tvm->setCurrentCode(code).
    :://  onCodeUpgrade2(request->UpdateRequest_ι_custodians, request->UpdateRequest_ι_reqConfirms) |.
}
return.
Defined.
Sync.

#[nonpayable, external, no_body]
Ursus Definition fallback_ : UExpression PhantomType false. (* warning:  *)
return.
Defined.
Sync.

#[nonpayable, external, no_body]
Ursus Definition receive_ : UExpression PhantomType false. (* warning:  *)
return.
Defined.
Sync.

#[pure, external, returns=result_]
Ursus Definition getVersion : UExpression (string ** string) false.
{
    :://  result_ := [{"1.0.0"}, {"Multisig"}] |.
}
return.
Defined.
Sync.

EndContract.
(* End MultisigWallet. *)
GenerateLocalState 0 SimpleContract.
GenerateLocalState 1 SimpleContract.
Fail GenerateLocalState 2 SimpleContract.
GenerateLocalState SimpleContract.
