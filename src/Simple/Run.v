Require Import UrsusEnvironment.Solidity.current.Environment.

Require Import Simple.Simple.

Section Run.

SetUrsusOptions.

Set Dune Build Root "_build/default".
Elpi SetProjectRoot .

Set Coq Root "src".
Set Project Source Path "Simple". 
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
                                       "hash_10";
                                       "hash_11";
                                       "hash_12";
                                       "hash_13";
                                       "hash_14";
                                       "hash_15";
                                       "hash_16";
                                       "hash_17";
                                       "hash_18";
                                       "hash_19";
                                       "hash_20";
                                       "hash_21";
                                       "hash_22";
                                       "hash_23";
                                       "hash_24";
                                       "hash_25";
                                       "hash_26";
                                       "hash_27";
                                       "hash_28";
                                       "hash_29";
                                       "hash_30";
                                       "hash_31";
                                       "hash_32";
                                       "hash_33";
                                       "hash_34";
                                       "hash_35";
                                       "hash_36";
                                       "hash_37";
                                       "hash_38";
                                       "hash_39";
                                       "hash_40";
                                       "test"
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
                                        "hash_10";
                                        "hash_11";
                                        "hash_12";
                                        "hash_13";
                                        "hash_14";
                                        "hash_15";
                                        "hash_16";
                                        "hash_17";
                                        "hash_18";
                                        "hash_19";
                                        "hash_20";
                                        "hash_21";
                                        "hash_22";
                                        "hash_23";
                                        "hash_24";
                                        "hash_25";
                                        "hash_26";
                                        "hash_27";
                                        "hash_28";
                                        "hash_29";
                                        "hash_30";
                                        "hash_31";
                                        "hash_32";
                                        "hash_33";
                                        "hash_34";
                                        "hash_35";
                                        "hash_36";
                                        "hash_37";
                                        "hash_38";
                                        "hash_39";
                                        "hash_40";
                                        "test"
].
Elpi GenerateFunction Simple "Run" "Functions" .

End Run.   