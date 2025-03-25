Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import UMLang.ExecGenerator.

From Hammer Require Import Tactics Hammer. 

Require Import ExtLib.Data.Monads.OptionMonad.
Require Import ExtLib.Data.Option.
Require Import ExtLib.Structures.Monad.

Require Import TVMModel.Notations.Loadable.
Require Import TVMModel.Notations.Storeable.
Require Import TVMModel.Base.Proofs.EncodeDecode.
Require Import TVMModel.Base.Definitions.TVMBitString.

Require Import SpecLang.
Require Import CommonProofs.

Require Import Simple.Simple.
Import Simple.

Require Import Simple.Common.
Require Import Simple.CommonContractTactics.

Import MonadNotation.
Local Open Scope monad_scope.

Definition local_with {X} (l: rec) (i: nat) (s: string) (x: X) `{H:LocalStateField XHMap rec X}: rec :=
    let m : XHMap (string * nat) X :=  projEmbed (EmbeddedType := @local_embedded XHMap rec X H) l in
    let idx: XHMap string nat := projEmbed (EmbeddedType := @local_index_embedded XHMap rec X H) l in 
    let m': XHMap (string * nat) X := _xHMapInsert (XBool:=XBool) (XInteger:=N) (XList:=XList) (XProd:=XProd) (XMaybe:=XMaybe) (XHMap:=XHMap) (hmapFunRec_gen:=hmapFunRec) (s,i) x m in 
    let idx': XHMap string nat :=  _xHMapInsert (XBool:=XBool) (XInteger:=N) (XList:=XList) (XProd:=XProd) (XMaybe:=XMaybe) (XHMap:=XHMap) (hmapFunRec_gen:=hmapFunRec) s i idx in 
    injEmbed (EmbeddedType := @local_embedded XHMap rec X H) m' l.


Lemma tvm_transfer_exec_exists: forall dest value bounce flags body currencies stateInit (l: LedgerLRecord rec),
exists m,
      exec_state (Uinterpreter (tvm_transfer dest value bounce flags body currencies stateInit)) l = 
      {$$ l with Ledger_MessagesState := m $$}. Admitted.

#[global] Instance _exe_tvm_transfer: 
          ExistsExecIndex _ _ (@tvm_transfer) :=
{|
  __exec_exists := @tvm_transfer_exec_exists;
|}.

(* ********************************** *)

Lemma send_internal_message_exec_exists: forall I lm a p (f: I) (l: LedgerLRecord rec),
exists m,
      exec_state (Uinterpreter (send_internal_message lm a p f)) l = 
      {$$ l with Ledger_MessagesState := m $$}. Admitted.

#[global] Instance _exe_send_internal_message: 
          ExistsExecIndex _ _ (@send_internal_message) :=
{|
  __exec_exists := @send_internal_message_exec_exists;
|}.

(* ********************************** *)

Lemma tvm_newContract_exec_exists: forall I (H: MessageQueue I) di (constr: I) (l: LedgerLRecord rec),
exists m,
      exec_state (Uinterpreter (tvm_newContract (H:=H) di constr)) l = 
      {$$ l with Ledger_MessagesState := m $$}. Admitted.

#[global] Instance _exe_tvm_newContract: 
          ExistsExecIndex _ _ (@tvm_newContract) :=
{|
  __exec_exists := @tvm_newContract_exec_exists;
|}.

(* ********************************** *)

Lemma send_internal_message_empty_exec_exists: forall I lm a p (l: LedgerLRecord rec),
exists m,
      exec_state (Uinterpreter (send_internal_message_empty (I:=I) lm a p)) l = 
      {$$ l with Ledger_MessagesState := m $$}. Admitted.

#[global] Instance _exe_send_internal_message_empty: 
          ExistsExecIndex _ _ (@send_internal_message_empty) :=
{|
  __exec_exists := @send_internal_message_empty_exec_exists;
|}.

(* ********************************** *)

Lemma suicide_exec_exists: forall a (l: LedgerLRecord rec),
exists m,
      exec_state (Uinterpreter (suicide a)) l =
      {$$ l with Ledger_MessagesState := m $$}. Admitted.

#[global] Instance _exe_suicide: 
          ExistsExecIndex _ _ (@suicide) :=
{|
  __exec_exists := @suicide_exec_exists;
|}.

(* ********************************************************************** *)

Lemma send_internal_message_exec_exists2 I: 
exists (m: queue (OutgoingMessage I)),
forall lm a p (f: I) (l: LedgerLRecord rec),
      exec_state (Uinterpreter (send_internal_message lm a p f)) l = 
      exec_state (rpureLWriterN lm m) l. Admitted.

Lemma send_internal_message_empty_exec_exists2 I: 
exists (m: queue (OutgoingMessage I)),
forall lm a p (f: I) (l: LedgerLRecord rec),
      exec_state (Uinterpreter (send_internal_message_empty lm a p)) l = 
      exec_state (rpureLWriterN lm m) l. Admitted.

Lemma tvm_newContract_exec_exists2 I: 
exists (m: queue (OutgoingMessage I)),
forall (H: MessageQueue I) di (constr: I) (l: LedgerLRecord rec),
      exec_state (Uinterpreter (tvm_newContract (H:=H) di constr)) l = 
      exec_state (rpureLWriterN messageLQ m) l. Admitted.

Lemma suicide_exec_exists2: 
exists m,
forall (H: DefaultMessageQueue) a (l: LedgerLRecord rec),
      exec_state (Uinterpreter (suicide a)) l = 
      exec_state (rpureLWriterN defaultMessageQueue m) l. Admitted.

Lemma tvm_transfer_exec_exists2: 
exists m,
forall (H: DefaultMessageQueue) dest value bounce flags body currencies stateInit (l: LedgerLRecord rec),
      exec_state (Uinterpreter (tvm_transfer dest value bounce flags body currencies stateInit)) l = 
      exec_state (rpureLWriterN defaultMessageQueue m) l. Admitted.


(* ********************************************************************** *)

(* TODO: the next 3 admits are incorrect - change forall and exists *)

Lemma gosh_cnvrtshellq_exec_exists: 
exists m1 m2,
forall x (l: LedgerLRecord rec),
      exec_state (Uinterpreter (gosh_cnvrtshellq x)) l = 
      {$$ l with Ledger_MainState := 
            {$$ Ledger_MainState l with __persistent_contract_data := 
                {$$ {$$ __persistent_contract_data (Ledger_MainState l) with PersistentContractData_ι_balance := m1 $$} 
                                                                        with PersistentContractData_ι_currencies := m2 $$} $$} $$}. Admitted.

#[global] Instance _exe_gosh_cnvrtshellq: 
          ExistsExecIndex _ _ (@gosh_cnvrtshellq) :=
{|
  __exec_exists := @gosh_cnvrtshellq_exec_exists;
|}.


Lemma gosh_mintshell_exec_exists: 
exists m,
forall x (l: LedgerLRecord rec),
      exec_state (Uinterpreter (gosh_mintshell x)) l = 
      {$$ l with Ledger_MainState := 
            {$$ Ledger_MainState l with __persistent_contract_data := 
                {$$ __persistent_contract_data (Ledger_MainState l) with PersistentContractData_ι_balance := m $$} $$} $$}. Admitted.

#[global] Instance _exe_gosh_mintshell: 
          ExistsExecIndex _ _ (@gosh_mintshell) :=
{|
  __exec_exists := @gosh_mintshell_exec_exists;
|}.

Lemma gosh_mintecc_exec_exists: 
exists m,
forall x y (l: LedgerLRecord rec),
      exec_state (Uinterpreter (gosh_mintecc x y)) l = 
      {$$ l with Ledger_MainState := 
            {$$ Ledger_MainState l with __persistent_contract_data := 
                {$$ __persistent_contract_data (Ledger_MainState l) with PersistentContractData_ι_currencies := m $$} $$} $$}. Admitted.

#[global] Instance _exe_gosh_mintecc: 
          ExistsExecIndex _ _ (@gosh_mintecc) :=
{|
  __exec_exists := @gosh_mintecc_exec_exists;
|}.