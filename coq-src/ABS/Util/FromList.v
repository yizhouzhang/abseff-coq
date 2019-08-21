Require Import TLC.LibList.
Require Import TLC.LibFset.
Require Import CpdtTactics.
Set Implicit Arguments.

Lemma from_list_spec A : forall (x : A) L, mem x (from_list L) = LibList.mem x L.
Proof using.
  unfold from_list. induction L; rew_listx.
  rewrite in_empty. auto.
  rewrite in_union, in_singleton. congruence.
Qed.