Require Import UrsusEnvironment.Solidity.current.Environment.
Require Import IfAndRecursion.IfAndRecursion.

Section Run.

SetUrsusOptions.

Set Dune Build Root "_build/default".
Elpi SetProjectRoot .

Set Coq Root "src".
Set Project Source Path "IfAndRecursion". 
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
                                       "hash_1";
                                       "hash_2";
                                       "hash_3";
                                       "hash_4";
                                       "hash_5";
                                       "hash_6";
                                       "hash_7";
                                       "hash_8";
                                       "hash_9";
                                       "hash_10"
].

Definition roots_exec : Datatypes.list string := [
                                        "hash_1";
                                        "hash_2";
                                        "hash_3";
                                        "hash_4";
                                        "hash_5";
                                        "hash_6";
                                        "hash_7";
                                        "hash_8";
                                        "hash_9";
                                        "hash_10"
].


Elpi GenerateFunction IfAndRecursion "Run" "Functions" .

End Run.   