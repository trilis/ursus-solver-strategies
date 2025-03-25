Require Import UrsusEnvironment.Solidity.current.Environment.

Require Import UrsusContractCreator.UrsusEndContract.
Require Import UrsusContractCreator.UrsusRunContract.
Require Export UrsusContractCreator.UrsusStartContract.
Require Import UrsusContractCreator.Templates.

Require Import If.If.

Section Run1.

SetUrsusOptions.

Set Dune Build Root "_build/default".
Elpi SetProjectRoot .

Set Coq Root "src".
Set Project Source Path "If". 
Set Functions Path "Functions".
Set Execs Path "Execs".
Set Evals Path "Evals".
Set Tactics Path "Tactics". 
Set Run Script Path "build.sh".
Set Log Path "res.log". 
Set Fake Proofs Path "_FakeProofs".

Import ListNotations.
Local Open Scope list_scope.

Definition roots_eval : Datatypes.list string := [
                                       "hash_1"
].

Definition roots_exec : Datatypes.list string := [
                                        "hash_1"
].


Elpi GenerateFunction If "Run1" "Functions1" .

End Run1.   