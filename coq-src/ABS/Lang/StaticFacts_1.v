Require Import Lang.Syntax.
Require Import Lang.Bindings.
Require Import Lang.Static.
Require Import Lang.BindingsFacts.
Require Import Util.Subset.
Require Import LibReflect.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Section section_Xs_sub.

Hint Resolve subset_empty_l in_inv.
Hint Rewrite in_empty in_singleton in_union.

Lemma Xs_se
EV HV L (E E' : eff EV HV L) (Q : se E E') :
∀ X, X \in Xs_eff E → X \in Xs_eff E'.
Proof.
induction E as [ | ε E IHE ] ; simpl ; [ crush | ].
intros X HX.
rewrite in_union in HX ; destruct HX as [ HX | HX ].
+ clear IHE.
  assert (In ε E') as Hε ; [crush|].
  destruct ε as [|[|[|Y]]] ; simpl in HX ; [crush|crush|crush|].
  rewrite in_singleton in HX ; subst Y.
  clear - Hε.
  induction E' ; crush.
+ assert (se E E') ; crush.
Qed.

Hint Resolve Xs_se.

Fixpoint Xs_st
EV HV (T T' : ty EV HV ∅) (Q : st T T') :
∀ X, X \in Xs_ty T → X \in Xs_ty T'.
Proof.
destruct Q ; simpl ; intros X HX.
+ crush.
+ repeat rewrite in_union in HX |- *.
  destruct HX as [ | [ | ] ] ; eauto.
+ eauto.
+ eauto.
+ eauto.
Qed.

End section_Xs_sub.
