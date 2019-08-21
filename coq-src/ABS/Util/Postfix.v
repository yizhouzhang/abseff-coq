Require Import Utf8 List.
Require Import Cpdt.CpdtTactics.
Require Import TLC.LibFset.
Require Import ABS.Util.Subset.
Local Set Implicit Arguments.
Local Open Scope list_scope.

Inductive postfix A : list A → list A → Prop :=
| postfix_same l : postfix l l
| postfix_tail a l1 l2 : postfix l1 l2 → postfix l1 (a :: l2)
.

Section section_postfix_facts.

Context (A : Set).

Hint Constructors postfix.

Lemma postfix_refl (l : list A) : postfix l l.
Proof.
auto.
Qed.

Lemma tail_is_postfix_aux (a : A) l1 l2 l3 :
postfix l2 l3 → l2 = a :: l1 → postfix l1 l3.
Proof.
induction 1 ; crush.
Qed.

Lemma tail_is_postfix (a : A) l1 l2 :
postfix (a :: l1) l2 → postfix l1 l2.
Proof.
intro ; eapply tail_is_postfix_aux with (l2 := a :: l1) ; crush.
Qed.

Hint Resolve tail_is_postfix.

Lemma postfix_trans_aux (l1 l2 : list A) :
postfix l1 l2 → ∀ l3, postfix l2 l3 → postfix l1 l3.
Proof.
induction 1 ; intros l3 H23 ; crush.
inversion H23 ; subst ; clear H23 ; eauto.
Qed.

Lemma postfix_trans (l1 l2 l3 : list A) :
postfix l1 l2 → postfix l2 l3 → postfix l1 l3.
Proof.
intros ; eapply postfix_trans_aux ; eauto.
Qed.

Hint Resolve subset_union_weak_r.

Lemma postfix_is_subset (l1 l2 : list A) :
postfix l1 l2 → from_list l1 \c from_list l2.
Proof.
induction 1.
+ apply subset_refl.
+ rewrite from_list_cons.
  eapply subset_trans ; eauto.
Qed.

Lemma postfix_In (l1 l2 : list A) :
postfix l1 l2 → ∀ a, In a l1 → In a l2.
Proof.
induction 1 ; intros ; crush.
Qed.

Lemma postfix_inv_app (l1 l2 : list A) :
postfix l1 l2 →
∃ l3, l2 = l3 ++ l1.
Proof.
induction 1 as [ | a ? ? ? IH ].
+ exists nil ; rewrite app_nil_l ; reflexivity.
+ destruct IH as [l3 IH] ; subst.
  exists (a :: l3).
  rewrite app_comm_cons ; reflexivity.
Qed.

Lemma In_from_list (a : A) l :
In a l → a \in from_list l.
Proof.
induction l as [ | a' l' ] ; intro ; simpl in H.
+ contradict H.
+ rewrite from_list_cons, in_union, in_singleton ; crush.
Qed.

End section_postfix_facts.
