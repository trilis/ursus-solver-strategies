Require Import UrsusEnvironment.Solidity.current.Environment.

Require Import Simple.Simple.
(*Require Import If.If.
Require Import Recursion.Recursion.
Require Import IfAndRecursion.IfAndRecursion.*)

Section Main.

SetUrsusOptions.

Set Dune Build Root "_build/default".

Elpi SetProjectRoot .
Set Coq Root "src".

Elpi GenerateCommon Simple "Simple" .
(*Elpi GenerateCommon If "If" .
Elpi GenerateCommon Recursion "Recursion" .
Elpi GenerateCommon IfAndRecursion "IfAndRecursion" .*)

End Main .