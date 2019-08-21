Require Import Utf8.
Require Import LibTactics LibFset.
Require Import CpdtTactics.
Local Set Implicit Arguments.

Section section_subset_facts.
Context (A : Type).
Context (E F G : fset A).

Lemma subset_trans :
E \c F → F \c G → E \c G.
Proof.
intros_all ; crush.
Qed.

Lemma subset_union_l :
E \c F → E \c (F \u G).
Proof.
intros_all.
rewrite in_union.
crush.
Qed.

Lemma subset_union_r :
E \c G → E \c (F \u G).
Proof.
intros_all.
rewrite in_union.
crush.
Qed.

Lemma notin_subset (a : A) :
a \notin F → E \c F → a \notin E.
Proof.
intros_all ; crush.
Qed.

Lemma subset_refl' :
E = F → E \c F.
Proof.
crush.
Qed.

Lemma union_subset :
E \c G → F \c G → (E \u F) \c G.
Proof.
intros_all.
rewrite in_union in *.
crush.
Qed.

Lemma union_subset_inv_l :
E \u F \c G → E \c G.
Proof.
intros H1 x H2.
apply (H1 x).
rewrite in_union ; crush.
Qed.

Lemma union_subset_inv_r :
E \u F \c G → F \c G.
Proof.
intros H1 x H2.
apply (H1 x).
rewrite in_union ; crush.
Qed.

Lemma union_subset_inv :
E \u F \c G → E \c G ∧ F \c G.
Proof.
intro ; split ; [ apply union_subset_inv_l | apply union_subset_inv_r ] ; trivial.
Qed.

End section_subset_facts.
