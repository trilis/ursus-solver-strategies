Require Import SimpleContract.SimpleContract.

Require Import UrsusEnvironment.Solidity.current.Environment.

Require Import UrsusContractCreator.UrsusEndContract.
Require Import UrsusContractCreator.UrsusRunContract.
Require Export UrsusContractCreator.UrsusStartContract.
Require Import UrsusContractCreator.Templates.

Section Main.

SetUrsusOptions.

Set Dune Build Root "_build/default".

Elpi SetProjectRoot .
Set Coq Root "src".

Elpi GenerateCommon SimpleContract "SimpleContract" .

End Main .