Require Import Simple.Proofs.TacticsAll.
Set Keyed Unification.
SetDefaultOpaques "Simple".
Opaque N.mul N.modulo arrLookup.

Ltac solver := bottomup_reductions_cbv.

Lemma hash_1_prf (ll : LedgerLRecord rec) : hash_1_correct_def ll.
  start_proof; hash_1_start; prepare ll P loc_.
  time "[simple][bottomup-reductions-cbv][1]" timeout 300 solver.
Time Qed.

Lemma hash_2_prf (ll : LedgerLRecord rec) : hash_2_correct_def ll.
  start_proof; hash_2_start; prepare ll P loc_.
  time "[simple][bottomup-reductions-cbv][2]" timeout 300 solver.
Time Qed.

Lemma hash_3_prf (ll : LedgerLRecord rec) : hash_3_correct_def ll.
  start_proof; hash_3_start; prepare ll P loc_.
  time "[simple][bottomup-reductions-cbv][3]" timeout 300 solver.
Time Qed.

Lemma hash_4_prf (ll : LedgerLRecord rec) : hash_4_correct_def ll.
  start_proof; hash_4_start; prepare ll P loc_.
  time "[simple][bottomup-reductions-cbv][4]" timeout 300 solver.
Time Qed.

Lemma hash_5_prf (ll : LedgerLRecord rec) : hash_5_correct_def ll.
  start_proof; hash_5_start; prepare ll P loc_.
  time "[simple][bottomup-reductions-cbv][5]" timeout 300 solver.
Time Qed.

Lemma hash_6_prf (ll : LedgerLRecord rec) : hash_6_correct_def ll.
  start_proof; hash_6_start; prepare ll P loc_.
  time "[simple][bottomup-reductions-cbv][6]" timeout 300 solver.
Time Qed.

Lemma hash_7_prf (ll : LedgerLRecord rec) : hash_7_correct_def ll.
  start_proof; hash_7_start; prepare ll P loc_.
  time "[simple][bottomup-reductions-cbv][7]" timeout 300 solver.
Time Qed.

Lemma hash_8_prf (ll : LedgerLRecord rec) : hash_8_correct_def ll.
  start_proof; hash_8_start; prepare ll P loc_.
  time "[simple][bottomup-reductions-cbv][8]" timeout 300 solver.
Time Qed.

Lemma hash_9_prf (ll : LedgerLRecord rec) : hash_9_correct_def ll.
  start_proof; hash_9_start; prepare ll P loc_.
  time "[simple][bottomup-reductions-cbv][9]" timeout 300 solver.
Time Qed.

Lemma hash_10_prf (ll : LedgerLRecord rec) : hash_10_correct_def ll.
  start_proof; hash_10_start; prepare ll P loc_.
  time "[simple][bottomup-reductions-cbv][10]" timeout 300 solver.
Time Qed. 