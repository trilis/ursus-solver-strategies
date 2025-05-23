Require Import IfAndRecursion.Proofs.TacticsAll.
Set Keyed Unification.
SetDefaultOpaques "IfAndRecursion".
Opaque N.mul N.modulo arrLookup.

Ltac solver := native_contractions_lazy.

Lemma hash_1_prf (ll : LedgerLRecord rec) : hash_1_correct_def ll.
  start_proof; hash_1_start; prepare_ifs ll P loc_.
  time "[if&recursion][native-contractions-lazy][1]" timeout 300 solver.
Time Qed.

Lemma hash_2_prf (ll : LedgerLRecord rec) : hash_2_correct_def ll.
  start_proof; hash_2_start.
  continue_all @hash_1.
  prepare_ifs ll P loc_.
  time "[if&recursion][native-contractions-lazy][2]" timeout 300 solver.
Time Qed.

Lemma hash_3_prf (ll : LedgerLRecord rec) : hash_3_correct_def ll.
  start_proof; hash_3_start.
  continue_all @hash_2 @hash_1.
  prepare_ifs ll P loc_.
  time "[if&recursion][native-contractions-lazy][3]" timeout 300 solver.
Time Qed.

Lemma hash_4_prf (ll : LedgerLRecord rec) : hash_4_correct_def ll.
  start_proof; hash_4_start.
  continue_all @hash_3 @hash_2 @hash_1.
  prepare_ifs ll P loc_.
  time "[if&recursion][native-contractions-lazy][4]" timeout 300 solver.
Time Qed.

Lemma hash_5_prf (ll : LedgerLRecord rec) : hash_5_correct_def ll.
  start_proof; hash_5_start.
  continue_all @hash_4 @hash_3 @hash_2 @hash_1.
  prepare_ifs ll P loc_.
  time "[if&recursion][native-contractions-lazy][5]" timeout 300 solver.
Time Qed.

Lemma hash_6_prf (ll : LedgerLRecord rec) : hash_6_correct_def ll.
  start_proof; hash_6_start.
  continue_all @hash_5 @hash_4 @hash_3 @hash_2 @hash_1.
  prepare_ifs ll P loc_.
  time "[if&recursion][native-contractions-lazy][6]" timeout 300 solver.
Time Qed.

Lemma hash_7_prf (ll : LedgerLRecord rec) : hash_7_correct_def ll.
  start_proof; hash_7_start.
  continue_all @hash_6 @hash_5 @hash_4 @hash_3 @hash_2 @hash_1.
  prepare_ifs ll P loc_.
  time "[if&recursion][native-contractions-lazy][7]" timeout 300 solver.
Time Qed.

Lemma hash_8_prf (ll : LedgerLRecord rec) : hash_8_correct_def ll.
  start_proof; hash_8_start.
  continue_all @hash_7 @hash_6 @hash_5 @hash_4 @hash_3 @hash_2 @hash_1.
  prepare_ifs ll P loc_.
  time "[if&recursion][native-contractions-lazy][8]" timeout 300 solver.
Time Qed.

Lemma hash_9_prf (ll : LedgerLRecord rec) : hash_9_correct_def ll.
  start_proof; hash_9_start.
  continue_all @hash_8 @hash_7 @hash_6 @hash_5 @hash_4 @hash_3 @hash_2 @hash_1.
  prepare_ifs ll P loc_.
  time "[if&recursion][native-contractions-lazy][9]" timeout 300 solver.
Time Qed.

Lemma hash_10_prf (ll : LedgerLRecord rec) : hash_10_correct_def ll.
  start_proof; hash_10_start.
  continue_all @hash_9 @hash_8 @hash_7 @hash_6 @hash_5 @hash_4 @hash_3 @hash_2 @hash_1.
  prepare_ifs ll P loc_.
  time "[if&recursion][native-contractions-lazy][10]" timeout 300 solver.
Time Qed. 