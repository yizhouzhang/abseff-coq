Require Import Rel.Definitions.
Require Import Lang.OperationalFacts Lang.BindingsFacts.
Require Import Util.Subset.
Set Implicit Arguments.

(** * The small-step transition relation reflects [𝓞] (and [𝓣]) on both sides *)

Lemma 𝓞_step_l n ξ₁ t₁ ξ₁' t₁' ξ₂ t₂ :
  step ⟨ξ₁, t₁⟩ ⟨ξ₁', t₁'⟩ → n ⊨ ▷ 𝓞 ξ₁' ξ₂ t₁' t₂ → n ⊨ 𝓞 ξ₁ ξ₂ t₁ t₂.
Proof.
  intros.
  apply 𝓞_roll.
  iright.
  iexists ξ₁' ; iexists t₁' ; isplit.
  { iintro_prop ; assumption. }
  { assumption. }
Qed.

Local Lemma 𝓞_step_tran_l_aux c₁ c₁' :
  step_tran c₁ c₁' →
  ∀ ξ₁ t₁ ξ₁' t₁', c₁ = ⟨ξ₁, t₁⟩ → c₁' = ⟨ξ₁', t₁'⟩ →
  ∀ n ξ₂ t₂, n ⊨ ▷ 𝓞 ξ₁' ξ₂ t₁' t₂ → n ⊨ 𝓞 ξ₁ ξ₂ t₁ t₂.
Proof.
  induction 1 as [ | ? [ξ₁'' t₁''] ? ? ? IH ] ; intros ; subst.
  + eapply 𝓞_step_l ; eauto.
  + eapply 𝓞_step_l ; eauto.
    iintro_later.
    eapply IH ; eauto.
Qed.

Lemma 𝓞_step_tran_l ξ₁ t₁ ξ₁' t₁' :
  step_tran ⟨ξ₁, t₁⟩ ⟨ξ₁', t₁'⟩ → ∀ n ξ₂ t₂, n ⊨ ▷ 𝓞 ξ₁' ξ₂ t₁' t₂ → n ⊨ 𝓞 ξ₁ ξ₂ t₁ t₂.
Proof.
  intros ; eapply 𝓞_step_tran_l_aux ; eauto.
Qed.

Local Lemma 𝓞_step_r_aux ξ₂ t₂ ξ₂' t₂' :
  step ⟨ξ₂, t₂⟩ ⟨ξ₂', t₂'⟩ → ∀ n, n ⊨ ∀ᵢ ξ₁ t₁, 𝓞 ξ₁ ξ₂' t₁ t₂' ⇒ 𝓞 ξ₁ ξ₂ t₁ t₂.
Proof.
  intros H_step n.
  loeb_induction LöbIH.
  iintro ξ₁ ; iintro t₁ ; iintro H.
  apply 𝓞_roll ; apply 𝓞_unroll in H.
  idestruct H as H H.
  - apply I_Prop_elim in H.
    destruct H as [ [v₁ ?] [ξ₂'' [v₂ ?]] ] ; subst.
    ileft.
    iintro_prop ; split.
    { eexists ; trivial. }
    { eexists ; eexists ; econstructor ; eauto. }
  - idestruct H as ξ₁' H ; idestruct H as t₁' H.
    idestruct H as H1 H2.
    iright.
    iexists ξ₁' ; iexists t₁'.
    isplit ; [ trivial | ].
    later_shift.
    iespecialize LöbIH ; iapply LöbIH.
    trivial.
Qed.

Lemma 𝓞_step_r n ξ₁ t₁ ξ₂ t₂ ξ₂' t₂' :
  step ⟨ξ₂, t₂⟩ ⟨ξ₂', t₂'⟩ → n ⊨ 𝓞 ξ₁ ξ₂' t₁ t₂' → n ⊨ 𝓞 ξ₁ ξ₂ t₁ t₂.
Proof.
  intros H_step H1.
  specialize (𝓞_step_r_aux H_step n) as H.
  iespecialize H.
  iapply H ; trivial.
Qed.

Local Lemma 𝓞_step_refl_tran_r_aux c₂ c₂' :
  step_refl_tran c₂ c₂' →
  ∀ ξ₂ t₂ ξ₂' t₂', c₂ = ⟨ξ₂, t₂⟩ → c₂' = ⟨ξ₂', t₂'⟩ →
  ∀ n ξ₁ t₁, n ⊨ 𝓞 ξ₁ ξ₂' t₁ t₂' → n ⊨ 𝓞 ξ₁ ξ₂ t₁ t₂.
Proof.
  induction 1 as [ | ? [ξ₂'' t₂''] ? ? ? IH ] ; intros ; subst.
  + match goal with [ H : _ = _ |- _ ] => inversion H end.
    assumption.
  + eapply 𝓞_step_r ; eauto.
Qed.

Lemma 𝓞_step_refl_tran_r ξ₂ t₂ ξ₂' t₂' :
  step_refl_tran ⟨ξ₂, t₂⟩ ⟨ξ₂', t₂'⟩ →
  ∀ n ξ₁ t₁, n ⊨ 𝓞 ξ₁ ξ₂' t₁ t₂' → n ⊨ 𝓞 ξ₁ ξ₂ t₁ t₂.
Proof.
  intros ; eapply 𝓞_step_refl_tran_r_aux ; eauto.
Qed.


(** * The expansion of allocated labels preserves the logical relations
[𝓡] [𝓥] [𝓗] *)

Section section_monotone.
Context (EV HV V : Set).
Context (Ξ : XEnv EV HV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig).
Context (γ₁ γ₂ : V → val0).

Hint Resolve postfix_trans.

Lemma 𝓡_monotone_l n T 𝓔 ξ₁ ξ₁' ξ₂ K₁ K₂ :
postfix ξ₁ ξ₁' →
n ⊨ 𝓡⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂ →
n ⊨ 𝓡⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂ K₁ K₂.
Proof.
intros Hξ₁' HK ; idestruct HK as HKv HKw ; isplit.
+ iintro ξ₁'' ; iintro ξ₂' ; iintro v₁ ; iintro v₂.
  iintro Hξ₁'' ; iintro Hξ₂' ; iintro Hv.
  ispecialize HKv ξ₁''.
  ispecialize HKv ξ₂'.
  repeat iespecialize HKv.
  ispecialize HKv ; [eauto|].
  ispecialize HKv ; [auto|].
  ispecialize HKv ; [eauto|].
  apply HKv.
+ iintro ξ₁'' ; iintro ξ₂' ; iintro J₁ ; iintro J₂ ; iintro s₁ ; iintro s₂.
  iintro Hξ₁'' ; iintro Hξ₂' ; iintro Hv.
  ispecialize HKw ξ₁''.
  ispecialize HKw ξ₂'.
  repeat iespecialize HKw.
  ispecialize HKw ; [eauto|].
  ispecialize HKw ; [auto|].
  ispecialize HKw ; [eauto|].
  apply HKw.
Qed.

Lemma 𝓡_monotone_r n T 𝓔 ξ₁ ξ₂ ξ₂' K₁ K₂ :
postfix ξ₂ ξ₂' →
n ⊨ 𝓡⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂ →
n ⊨ 𝓡⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂' K₁ K₂.
Proof.
intros Hξ₂' HK ; idestruct HK as HKv HKw ; isplit.
+ iintro ξ₁' ; iintro ξ₂'' ; iintro v₁ ; iintro v₂.
  iintro Hξ₁' ; iintro Hξ₂'' ; iintro Hv.
  ispecialize HKv ξ₁'.
  ispecialize HKv ξ₂''.
  repeat iespecialize HKv.
  ispecialize HKv ; [auto|].
  ispecialize HKv ; [eauto|].
  ispecialize HKv ; [eauto|].
  apply HKv.
+ iintro ξ₁' ; iintro ξ₂'' ; iintro J₁ ; iintro J₂ ; iintro s₁ ; iintro s₂.
  iintro Hξ₁' ; iintro Hξ₂'' ; iintro Hv.
  ispecialize HKw ξ₁'.
  ispecialize HKw ξ₂''.
  repeat iespecialize HKw.
  ispecialize HKw ; [auto|].
  ispecialize HKw ; [eauto|].
  ispecialize HKw ; [eauto|].
  apply HKw.
Qed.

Hint Resolve 𝓡_monotone_l 𝓡_monotone_r.

Corollary 𝓡_monotone n T 𝓔 ξ₁ ξ₁' ξ₂ ξ₂' K₁ K₂ :
n ⊨ 𝓡⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂ →
postfix ξ₁ ξ₁' →
postfix ξ₂ ξ₂' →
n ⊨ 𝓡⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' K₁ K₂.
Proof.
eauto.
Qed.

Lemma 𝓚_monotone_l n 𝓥a 𝓤a 𝓥b 𝓤b ξ₁ ξ₁' ξ₂ K₁ K₂ :
postfix ξ₁ ξ₁' →
n ⊨ 𝓚_Fun 𝓥a 𝓤a 𝓥b 𝓤b ξ₁ ξ₂ K₁ K₂ →
n ⊨ 𝓚_Fun 𝓥a 𝓤a 𝓥b 𝓤b ξ₁' ξ₂ K₁ K₂.
Proof.
intros Hξ₁' HK.
iintro ξ₁'' ; iintro ξ₂' ; iintro t₁ ; iintro t₂.
iintro Hξ₁'' ; iintro Hξ₂' ; iintro Ht.
ispecialize HK ξ₁''.
ispecialize HK ξ₂'.
repeat iespecialize HK.
ispecialize HK ; [eauto|].
ispecialize HK ; [auto|].
ispecialize HK ; [eauto|].
apply HK.
Qed.

Lemma 𝓚_monotone_r n 𝓥a 𝓤a 𝓥b 𝓤b ξ₁ ξ₂ ξ₂' K₁ K₂ :
postfix ξ₂ ξ₂' →
n ⊨ 𝓚_Fun 𝓥a 𝓤a 𝓥b 𝓤b ξ₁ ξ₂ K₁ K₂ →
n ⊨ 𝓚_Fun 𝓥a 𝓤a 𝓥b 𝓤b ξ₁ ξ₂' K₁ K₂.
Proof.
intros Hξ₂' HK.
iintro ξ₁' ; iintro ξ₂'' ; iintro t₁ ; iintro t₂.
iintro Hξ₁' ; iintro Hξ₂'' ; iintro Ht.
ispecialize HK ξ₁'.
ispecialize HK ξ₂''.
repeat iespecialize HK.
ispecialize HK ; [auto|].
ispecialize HK ; [eauto|].
ispecialize HK ; [eauto|].
apply HK.
Qed.

Hint Resolve 𝓚_monotone_l 𝓚_monotone_r.

Lemma 𝓚_monotone n 𝓥a 𝓤a 𝓥b 𝓤b ξ₁ ξ₁' ξ₂ ξ₂' K₁ K₂ :
postfix ξ₁ ξ₁' →
postfix ξ₂ ξ₂' →
n ⊨ 𝓚_Fun 𝓥a 𝓤a 𝓥b 𝓤b ξ₁ ξ₂ K₁ K₂ →
n ⊨ 𝓚_Fun 𝓥a 𝓤a 𝓥b 𝓤b ξ₁' ξ₂' K₁ K₂.
Proof.
eauto.
Qed.

Lemma 𝓥_monotone_l n T ξ₁ ξ₁' ξ₂ v₁ v₂ :
postfix ξ₁ ξ₁' →
n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ →
n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂ v₁ v₂.
Proof.
destruct T as [ | | | ] ; intros Hξ₁' Hv ; simpl in Hv |- *.
+ crush.
+ iintro ξ₁'' ; iintro ξ₂' ; iintro Hξ₁'' ; iintro Hξ₂'.
  iintro u₁ ; iintro u₂ ; iintro Hu.
  ispecialize Hv ξ₁''.
  ispecialize Hv ξ₂'.
  ispecialize Hv ; [eauto|].
  ispecialize Hv ; [auto|].
  iespecialize Hv.
  ispecialize Hv ; [eauto|].
  apply Hv.
+ iintro ξ₁'' ; iintro ξ₂' ; iintro Hξ₁'' ; iintro Hξ₂'.
  iintro 𝓔₁ ; iintro 𝓔₂ ; iintro φ ; iintro cl_φ.
  ispecialize Hv ξ₁''.
  ispecialize Hv ξ₂'.
  ispecialize Hv ; [eauto|].
  ispecialize Hv ; [auto|].
  ispecialize Hv 𝓔₁ ; ispecialize Hv 𝓔₂ ; ispecialize Hv φ.
  ispecialize Hv ; [auto|].
  apply Hv.
+ iintro ξ₁'' ; iintro ξ₂' ; iintro Hξ₁'' ; iintro Hξ₂'.
  iintro r₁ ; iintro r₂ ; iintro X₁ ; iintro X₂ ; iintro φ ; iintro Hr.
  ispecialize Hv ξ₁''.
  ispecialize Hv ξ₂'.
  ispecialize Hv ; [eauto 6|].
  ispecialize Hv ; [auto|].
  iespecialize Hv.
  ispecialize Hv ; [eauto|].
  apply Hv.
Qed.

Lemma 𝓥_monotone_r n T ξ₁ ξ₂ ξ₂' v₁ v₂ :
postfix ξ₂ ξ₂' →
n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ →
n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂' v₁ v₂.
Proof.
intros Hξ₂' Hv ; destruct T as [ | | | ] ; simpl in Hv |- *.
+ crush.
+ iintro ξ₁' ; iintro ξ₂'' ; iintro Hξ₁' ; iintro Hξ₂''.
  iintro u₁ ; iintro u₂ ; iintro Hu.
  ispecialize Hv ξ₁'.
  ispecialize Hv ξ₂''.
  ispecialize Hv ; [auto|].
  ispecialize Hv ; [eauto|].
  iespecialize Hv.
  ispecialize Hv ; [eauto|].
  apply Hv.
+ iintro ξ₁' ; iintro ξ₂'' ; iintro Hξ₁' ; iintro Hξ₂''.
  iintro 𝓔₁ ; iintro 𝓔₂ ; iintro φ.
  ispecialize Hv ξ₁'.
  ispecialize Hv ξ₂''.
  ispecialize Hv ; [auto|].
  ispecialize Hv ; [eauto|].
  ispecialize Hv 𝓔₁ ; ispecialize Hv 𝓔₂ ; ispecialize Hv φ.
  apply Hv.
+ iintro ξ₁' ; iintro ξ₂'' ; iintro Hξ₁' ; iintro Hξ₂''.
  iintro r₁ ; iintro r₂ ; iintro X₁ ; iintro X₂ ; iintro φ ; iintro Hr.
  ispecialize Hv ξ₁'.
  ispecialize Hv ξ₂''.
  ispecialize Hv ; [auto|].
  ispecialize Hv ; [eauto 6|].
  iespecialize Hv.
  ispecialize Hv ; [eauto|].
  apply Hv.
Qed.

Hint Resolve 𝓥_monotone_l 𝓥_monotone_r.

Corollary 𝓥_monotone n T ξ₁ ξ₁' ξ₂ ξ₂' v₁ v₂ :
n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ →
postfix ξ₁ ξ₁' →
postfix ξ₂ ξ₂' →
n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' v₁ v₂.
Proof.
eauto.
Qed.

Lemma 𝓗_Fun'_monotone_l n 𝓥 𝔽 φ ξ₁ ξ₁' ξ₂ t₁ t₂ :
postfix ξ₁ ξ₁' →
n ⊨ 𝓗_Fun' 𝓥 𝔽 φ ξ₁ ξ₂ t₁ t₂ →
n ⊨ 𝓗_Fun' 𝓥 𝔽 φ ξ₁' ξ₂ t₁ t₂.
Proof.
intros Hξ₁' Ht.
iintro ξ₁'' ; iintro ξ₂' ; iintro Hξ₁'' ; iintro Hξ₂'.
iintro v₁ ; iintro v₂ ; iintro X₁ ; iintro X₂ ; iintro K₁ ; iintro K₂.
iintro Hv ; iintro HK.
ispecialize Ht ξ₁''.
ispecialize Ht ξ₂'.
ispecialize Ht ; [eauto|].
ispecialize Ht ; [auto|].
iespecialize Ht.
ispecialize Ht ; [exact Hv|].
ispecialize Ht ; [exact HK|].
exact Ht.
Qed.

Lemma 𝓗_Fun'_monotone_r n 𝓥 𝔽 φ ξ₁ ξ₂ ξ₂' t₁ t₂ :
postfix ξ₂ ξ₂' →
n ⊨ 𝓗_Fun' 𝓥 𝔽 φ ξ₁ ξ₂ t₁ t₂ →
n ⊨ 𝓗_Fun' 𝓥 𝔽 φ ξ₁ ξ₂' t₁ t₂.
Proof.
intros Hξ₂' Ht.
iintro ξ₁' ; iintro ξ₂'' ; iintro Hξ₁' ; iintro Hξ₂''.
iintro v₁ ; iintro v₂ ; iintro X₁ ; iintro X₂ ; iintro K₁ ; iintro K₂.
iintro Hv ; iintro HK.
ispecialize Ht ξ₁'.
ispecialize Ht ξ₂''.
ispecialize Ht ; [auto|].
ispecialize Ht ; [eauto|].
iespecialize Ht.
ispecialize Ht ; [exact Hv|].
ispecialize Ht ; [exact HK|].
exact Ht.
Qed.

Hint Resolve 𝓗_Fun'_monotone_l 𝓗_Fun'_monotone_r.

Corollary 𝓗_Fun'_monotone n 𝓥 𝔽 φ ξ₁ ξ₁' ξ₂ ξ₂' t₁ t₂ :
n ⊨ 𝓗_Fun' 𝓥 𝔽 φ ξ₁ ξ₂ t₁ t₂ →
postfix ξ₁ ξ₁' →
postfix ξ₂ ξ₂' →
n ⊨ 𝓗_Fun' 𝓥 𝔽 φ ξ₁' ξ₂' t₁ t₂.
Proof.
eauto.
Qed.

Hint Resolve 𝓗_Fun'_monotone.

Lemma 𝑷_monotone n P ξ₁ ξ₁' ξ₂ ξ₂' :
n ⊨ 𝑷⟦ ⊢ P ⟧ ξ₁ ξ₂ ρ₁ ρ₂ ρ →
postfix ξ₁ ξ₁' →
postfix ξ₂ ξ₂' →
n ⊨ 𝑷⟦ ⊢ P ⟧ ξ₁' ξ₂' ρ₁ ρ₂ ρ.
Proof.
intros Hρ Η₁ Η₂.
iintro p ; ispecialize Hρ p.
idestruct Hρ as r₁ Hρ ; idestruct Hρ as r₂ Hρ.
idestruct Hρ as X₁ Hρ ; idestruct Hρ as X₂ Hρ ; idestruct Hρ as Hρ Hr.
repeat ieexists ; isplit ; [ eauto | ].
later_shift ; eauto.
Qed.

Lemma 𝜞_monotone n Γ ξ₁ ξ₁' ξ₂ ξ₂' :
n ⊨ 𝜞⟦ Ξ ⊢ Γ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ γ₁ γ₂ →
postfix ξ₁ ξ₁' →
postfix ξ₂ ξ₂' →
n ⊨ 𝜞⟦ Ξ ⊢ Γ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' γ₁ γ₂.
Proof.
intros Hγ ? ? ; iintro x ; ispecialize Hγ x.
eauto.
Qed.

Hint Resolve postfix_is_subset subset_trans.

Lemma 𝜩_monotone ξ₁ ξ₂ ξ₁' ξ₂' :
𝜩 Ξ ξ₁ ξ₂ →
postfix ξ₁ ξ₁' →
postfix ξ₂ ξ₂' →
𝜩 Ξ ξ₁' ξ₂'.
Proof.
intros H ? ?.
destruct H ; split ; eauto.
Qed.

Lemma closed_δ_monotone n ξ₁ ξ₂ ξ₁' ξ₂' :
n ⊨ closed_δ ξ₁ ξ₂ δ →
postfix ξ₁ ξ₁' →
postfix ξ₂ ξ₂' →
n ⊨ closed_δ ξ₁' ξ₂' δ.
Proof.
intros H ? ? ; repeat iintro.
iespecialize H ; ispecialize H ; [ eassumption | ].
ielim_prop H ; destruct H ; split ; eauto.
Qed.

Hint Resolve postfix_In.

Lemma closed_ρ_monotone ξ₁ ξ₂ ξ₁' ξ₂' :
closed_ρ ξ₁ ξ₂ ρ₁ ρ₂ →
postfix ξ₁ ξ₁' →
postfix ξ₂ ξ₂' →
closed_ρ ξ₁' ξ₂' ρ₁ ρ₂.
Proof.
intros H H₁ H₂ ; repeat iintro.
intros α X ; specialize (H α X).
apply postfix_is_subset in H₁.
apply postfix_is_subset in H₂.
destruct H ; split ; intro ; auto.
Qed.

End section_monotone.


Section section_𝓣_step.

Context (EV HV : Set).
Context (Ξ : XEnv EV HV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig).
Context (T : ty EV HV ∅) (𝓔 : eff EV HV ∅).

Hint Resolve 𝓡_monotone_l 𝓡_monotone_r.
Hint Resolve step_monotone_config step_tran_monotone_config
  step_refl_tran_monotone_config.

Lemma 𝓣_step_l ξ₁ ξ₁' ξ₂ (t₁ t₁' t₂ : tm0) n :
  step ⟨ξ₁, t₁⟩ ⟨ξ₁', t₁'⟩ →
  n ⊨ ▷ 𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂ t₁' t₂ →
  n ⊨ 𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂.
Proof.
  intros H_step H.
  iintro K₁ ; iintro K₂.
  iintro HK.
  eapply 𝓞_step_l.
  + apply ktx_congruence ; apply H_step.
  + later_shift.
    iespecialize H ; iapply H.
    eauto.
Qed.

Lemma 𝓣_step_tran_l ξ₁ ξ₁' ξ₂ (t₁ t₁' t₂ : tm0) n :
  step_tran ⟨ξ₁, t₁⟩ ⟨ξ₁', t₁'⟩ →
  n ⊨ ▷ 𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂ t₁' t₂ →
  n ⊨ 𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂.
Proof.
  intros H_step H.
  iintro K₁ ; iintro K₂.
  iintro HK.
  eapply 𝓞_step_tran_l.
  + apply ktx_tran_congruence ; apply H_step.
  + later_shift.
    iespecialize H ; iapply H.
    eauto.
Qed.

Lemma 𝓣_step_r ξ₁ ξ₂ ξ₂' (t₁ t₂ t₂' : tm0) n :
  step ⟨ξ₂, t₂⟩ ⟨ξ₂', t₂'⟩ →
  n ⊨ 𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂' t₁ t₂' →
  n ⊨ 𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂.
Proof.
  intros H_step H.
  iintro K₁ ; iintro K₂.
  iintro HK.
  eapply 𝓞_step_r.
  + apply ktx_congruence ; apply H_step.
  + iespecialize H ; iapply H.
    eauto.
Qed.

Lemma 𝓣_step_refl_tran_r ξ₁ ξ₂ ξ₂' (t₁ t₂ t₂' : tm0) n :
  step_refl_tran ⟨ξ₂, t₂⟩ ⟨ξ₂', t₂'⟩ →
  n ⊨ 𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂' t₁ t₂' →
  n ⊨ 𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂.
Proof.
  intros H_step H.
  iintro K₁ ; iintro K₂.
  iintro HK.
  eapply 𝓞_step_refl_tran_r.
  + apply ktx_refl_tran_congruence ; apply H_step.
  + iespecialize H ; iapply H.
    eauto.
Qed.

End section_𝓣_step.


(** * The [𝓥] and [𝓦] relations are smaller than [𝓣]. *)

Section section_𝓥_and_𝓦_are_in_𝓣.

Context (EV HV : Set).
Context (Ξ : XEnv EV HV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig).
Context (T : ty EV HV ∅) (𝓔 : eff EV HV ∅).
Context (n : nat).

Hint Resolve postfix_refl.

Lemma 𝓥_in_𝓣
    ξ₁ ξ₂ v₁ v₂ :
    n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ →
    n ⊨ 𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂.
Proof.
  intro H.
  iintro K₁ ; iintro K₂.
  iintro HK.
  idestruct HK as HKV HKW.
  iespecialize HKV.
  ispecialize HKV ; [auto|].
  ispecialize HKV ; [auto|].
  iapply HKV.
  apply H.
Qed.

Lemma 𝓦_in_𝓣
    ξ₁ ξ₂ J₁ J₂ t₁ t₂ :
    n ⊨ 𝓦⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ J₁ J₂ t₁ t₂ →
    n ⊨ 𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
        ξ₁ ξ₂ (ktx_plug J₁ t₁) (ktx_plug J₂ t₂).
Proof.
  intro H.
  iintro K₁ ; iintro K₂.
  iintro HK.
  idestruct HK as HKV HKW.
  iespecialize HKW.
  ispecialize HKW ; [auto|].
  ispecialize HKW ; [auto|].
  iapply HKW.
  apply H.
Qed.

End section_𝓥_and_𝓦_are_in_𝓣.


Section section_plug.

Context (EV HV : Set).
Context (Ξ : XEnv EV HV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig).
Context (Ta : ty EV HV ∅) (𝓔a : eff EV HV ∅).
Context (Tb : ty EV HV ∅) (𝓔b : eff EV HV ∅).
Context (ξ₁ ξ₂ : list var).
Context (K₁ K₂ : ktx0).
Context (n : nat).

Hint Resolve postfix_trans.
Hint Resolve 𝓡_monotone.

Lemma plug' :
  n ⊨ 𝓚v⟦ Ξ ⊢ Ta ⇢ Tb # 𝓔b ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂ →
  n ⊨ 𝓚w⟦ Ξ ⊢ Ta # 𝓔a ⇢ Tb # 𝓔b ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂ →
  n ⊨ 𝓚⟦ Ξ ⊢ Ta # 𝓔a ⇢ Tb # 𝓔b ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂.
Proof.
  intros HKv HKw.
  unfold 𝓚_Fun.
  iintro ξ₁' ; iintro ξ₂' ; iintro t₁ ; iintro t₂ ; 
  iintro Hξ₁' ; iintro Hξ₂' ; iintro Ht.
  iintro J₁ ; iintro J₂ ; iintro HJ.
  repeat rewrite ktx_plug_comp.
  iespecialize Ht ; iapply Ht ; clear Ht.
  isplit.
  * iintro ξ₁'' ; iintro ξ₂'' ; iintro v₁ ; iintro v₂ ;
    iintro Hξ₁'' ; iintro Hξ₂'' ; iintro Hv.
    repeat rewrite <- ktx_plug_comp.
    ispecialize HKv ξ₁''.
    ispecialize HKv ξ₂''.
    ielim_prop Hξ₁' ; ielim_prop Hξ₂' ; ielim_prop Hξ₁'' ; ielim_prop Hξ₂''.
    iespecialize HKv.
    ispecialize HKv ; [eauto|].
    ispecialize HKv ; [eauto|].
    ispecialize HKv ; [apply Hv|clear Hv].
    iespecialize HKv ; iapply HKv.
    eauto.
  * iintro ξ₁'' ; iintro ξ₂'' ;
    iintro L₁ ; iintro L₂ ; iintro s₁ ; iintro s₂ ;
    iintro Hξ₁'' ; iintro Hξ₂'' ; iintro Hw.
    repeat rewrite <- ktx_plug_comp.
    ispecialize HKw ξ₁''.
    ispecialize HKw ξ₂''.
    ielim_prop Hξ₁' ; ielim_prop Hξ₂' ; ielim_prop Hξ₁'' ; ielim_prop Hξ₂''.
    iespecialize HKw.
    ispecialize HKw ; [eauto|].
    ispecialize HKw ; [eauto|].
    ispecialize HKw ; [apply Hw|].
    iespecialize HKw ; iapply HKw.
    eauto.
Qed.

Lemma plug t₁ t₂ :
  n ⊨ 𝓚v⟦ Ξ ⊢ Ta ⇢ Tb # 𝓔b ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂ →
  n ⊨ 𝓚w⟦ Ξ ⊢ Ta # 𝓔a ⇢ Tb # 𝓔b ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂ →
  ∀ ξ₁' ξ₂', postfix ξ₁ ξ₁' → postfix ξ₂ ξ₂' →
  n ⊨ 𝓣⟦ Ξ ⊢ Ta # 𝓔a ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' t₁ t₂ →
  n ⊨ 𝓣⟦ Ξ ⊢ Tb # 𝓔b ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' (ktx_plug K₁ t₁) (ktx_plug K₂ t₂).
Proof.
  intros.
  eapply unfold_𝓚 ; eauto.
  apply plug' ; auto.
Qed.

End section_plug.


Section section_plug0.

Context (EV HV : Set).
Context (Ξ : XEnv EV HV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig).
Context (Ta : ty EV HV ∅).
Context (Tb : ty EV HV ∅) (𝓔 : eff EV HV ∅).
Context (ξ₁ ξ₂ : list var).
Context (K₁ K₂ : ktx0).
Context (K₁_tun : ∀ ℓ, tunnels ℓ K₁).
Context (K₂_tun : ∀ ℓ, tunnels ℓ K₂).

Hint Resolve postfix_trans.

Lemma plug0' n :
  n ⊨ 𝓚v⟦ Ξ ⊢ Ta ⇢ Tb # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂ →
  n ⊨ 𝓚⟦ Ξ ⊢ Ta # 𝓔 ⇢ Tb # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂.
Proof.
intro HKv.
loeb_induction LöbIH.
eapply plug'.
+ apply HKv.
+ iintro ξ₁' ; iintro ξ₂' ;
  iintro L₁ ; iintro L₂ ; iintro s₁ ; iintro s₂ ;
  iintro Hξ₁' ; iintro Hξ₂' ; iintro Hw.
  apply unfold_𝓦 in Hw.
  destruct Hw as [ψ [Xs₁ [Xs₂ [Hs [HXs₁Xs₂ Hw]]]]].
  repeat rewrite ktx_plug_comp.
  apply 𝓦_in_𝓣.
  iexists ψ ; iexists Xs₁ ; iexists Xs₂.
  repeat isplit.
  - apply Hs.
  - iintro_prop ; intro X.
    specialize (HXs₁Xs₂ X) ; destruct HXs₁Xs₂.
    split ; intro HX ; apply tunnels_ktx_comp ; crush.
  - iintro ξ₁'' ; iintro ξ₂'' ;
    iintro t₁' ; iintro t₂' ;
    iintro Hξ₁'' ; iintro Hξ₂'' ; iintro Ht'.
    ielim_prop Hξ₁' ; ielim_prop Hξ₂' ; ielim_prop Hξ₁'' ; ielim_prop Hξ₂''.
    repeat rewrite <- ktx_plug_comp.
    iespecialize Hw.
    ispecialize Hw ; [eauto|].
    ispecialize Hw ; [eauto|].
    ispecialize Hw ; [eauto|].
    later_shift.
    apply 𝓣_roll.
    ispecialize LöbIH ξ₁'' ; ispecialize LöbIH ξ₂''.
    iespecialize LöbIH.
    ispecialize LöbIH ; [eauto|].
    ispecialize LöbIH ; [eauto|].
    iapply LöbIH.
    exact Hw.
Qed.

Lemma plug0 n t₁ t₂ :
  n ⊨ 𝓚v⟦ Ξ ⊢ Ta ⇢ Tb # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂ →
  ∀ ξ₁' ξ₂', postfix ξ₁ ξ₁' → postfix ξ₂ ξ₂' →
  n ⊨ 𝓣⟦ Ξ ⊢ Ta # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' t₁ t₂ →
  n ⊨ 𝓣⟦ Ξ ⊢ Tb # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' (ktx_plug K₁ t₁) (ktx_plug K₂ t₂).
Proof.
  intros.
  eapply unfold_𝓚 ; eauto.
  apply plug0' ; auto.
Qed.

End section_plug0.


Section section_plug1.

Context (EV HV : Set).
Context (Ξ : XEnv EV HV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig).
Context (Ta : ty EV HV ∅) (ε : ef EV HV ∅) (𝓔 : eff EV HV ∅).
Context (Tb : ty EV HV ∅).
Context (ξ₁ ξ₂ : list var).
Context (X : var).

Definition 𝓚_w' : IProp :=
  ∀ᵢ ξ₁' ξ₂',
  (postfix ξ₁ ξ₁')ᵢ ⇒
  (postfix ξ₂ ξ₂')ᵢ ⇒
  ∀ᵢ J₁ J₂ s₁ s₂ ψ Xs₁ Xs₂,
  𝓾⟦ Ξ ⊢ ε ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' s₁ s₂ ψ Xs₁ Xs₂ ⇒
  (∀ X, (X ∈ Xs₁ → tunnels X J₁) ∧ (X ∈ Xs₂ → tunnels X J₂))ᵢ ⇒
  ( ∀ᵢ ξ₁'' ξ₂'' t₁' t₂',
    (postfix ξ₁' ξ₁'')ᵢ ⇒
    (postfix ξ₂' ξ₂'')ᵢ ⇒
    ψ ξ₁'' ξ₂'' t₁' t₂' ⇒
      ▷ 𝓣⟦ Ξ ⊢ Ta # ε :: 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
        ξ₁'' ξ₂'' (ktx_plug J₁ t₁') (ktx_plug J₂ t₂')
  ) ⇒
  𝓣⟦ Ξ ⊢ Tb # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
    ξ₁' ξ₂'
    (ktx_plug (ktx_down ktx_hole X) (ktx_plug J₁ s₁))
    (ktx_plug (ktx_down ktx_hole X) (ktx_plug J₂ s₂)).

Hint Resolve postfix_trans.

Lemma plug1' n :
  n ⊨ (∀ᵢ ξ₁' ξ₂' t₁ t₂ ψ Xs₁ Xs₂,
      𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' t₁ t₂ ψ Xs₁ Xs₂ ⇒
      (X \notin Xs₁ ∧ X \notin Xs₂)ᵢ) →
  n ⊨ 𝓚v⟦ Ξ ⊢ Ta ⇢ Tb # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
      ξ₁ ξ₂ (ktx_down ktx_hole X) (ktx_down ktx_hole X) →
  n ⊨ 𝓚_w' →
  n ⊨ 𝓚⟦ Ξ ⊢ Ta # (ε :: 𝓔) ⇢ Tb # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
      ξ₁ ξ₂ (ktx_down ktx_hole X) (ktx_down ktx_hole X).
Proof.
intros FrX HKv HKw.
loeb_induction LöbIH.
eapply plug' ; [apply HKv|].

iintro ξ₁' ; iintro ξ₂' ;
iintro L₁ ; iintro L₂ ; iintro s₁ ; iintro s₂ ;
iintro Hξ₁' ; iintro Hξ₂'.
iintro Hw.

apply unfold_𝓦 in Hw.
destruct Hw as [ψ [Xs₁ [Xs₂ [Hs [H_Xs Hw]]]]].

simpl in Hs ; idestruct Hs as Hs Hs.
+ ispecialize HKw ξ₁' ; ispecialize HKw ξ₂'.
  ispecialize HKw ; [eauto|].
  ispecialize HKw ; [eauto|].
  iespecialize HKw.
  ispecialize HKw ; [apply Hs|].
  ispecialize HKw ; [iintro_prop ; apply H_Xs|].
  iapply HKw ; clear HKw.
  apply Hw.
+ repeat rewrite ktx_plug_comp.
  apply 𝓦_in_𝓣.
  iexists ψ ; iexists Xs₁ ; iexists Xs₂.
  repeat isplit.
  - apply Hs.
  - iintro_prop ; intro Y.
    iespecialize FrX.
    ispecialize FrX ; [apply Hs|ielim_prop FrX ; destruct FrX].
    specialize (H_Xs Y).
    crush.
  - iintro ξ₁'' ; iintro ξ₂'' ;
    iintro s₁' ; iintro s₂' ;
    iintro Hξ₁'' ; iintro Hξ₂'' ;
    iintro Hs'.
    iespecialize Hw.
    ispecialize Hw ; [ eauto | ].
    ispecialize Hw ; [ eauto | ].
    ispecialize Hw ; [ apply Hs' | ].
    later_shift.
    apply 𝓣_roll.
    repeat rewrite <- ktx_plug_comp.
    ielim_prop Hξ₁' ; ielim_prop Hξ₂' ; ielim_prop Hξ₁'' ; ielim_prop Hξ₂''.
    ispecialize LöbIH ξ₁'' ; ispecialize LöbIH ξ₂'' ; iespecialize LöbIH.
    ispecialize LöbIH ; [ eauto |].
    ispecialize LöbIH ; [ eauto |].
    ispecialize LöbIH ; [ apply Hw |].
    exact LöbIH.
Qed.

Corollary plug1 n t₁ t₂ :
  n ⊨ (∀ᵢ ξ₁' ξ₂' t₁ t₂ ψ Xs₁ Xs₂,
      𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' t₁ t₂ ψ Xs₁ Xs₂ ⇒
      (X \notin Xs₁ ∧ X \notin Xs₂)ᵢ) →
  n ⊨ 𝓚v⟦ Ξ ⊢ Ta ⇢ Tb # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
      ξ₁ ξ₂ (ktx_down ktx_hole X) (ktx_down ktx_hole X) →
  n ⊨ 𝓚_w' →
  ∀ ξ₁' ξ₂', postfix ξ₁ ξ₁' → postfix ξ₂ ξ₂' →
  n ⊨ 𝓣⟦ Ξ ⊢ Ta # (ε :: 𝓔) ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' t₁ t₂ →
  n ⊨ 𝓣⟦ Ξ ⊢ Tb # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
      ξ₁' ξ₂'
      (ktx_plug (ktx_down ktx_hole X) t₁)
      (ktx_plug (ktx_down ktx_hole X) t₂).
Proof.
  intros.
  eapply unfold_𝓚 ; [ eassumption | eassumption | | eassumption ].
  apply plug1' ; assumption.
Qed.

End section_plug1.


Section section_Xs_is_𝓤_bounded.

Context (EV HV : Set).
Context (Ξ : XEnv EV HV).
Context (𝓔 : eff EV HV ∅).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig).
Context (ξ₁ ξ₂ : list var).

Hint Rewrite in_singleton.

Lemma Xs_is_𝓤_bounded n :
𝜩 Ξ ξ₁ ξ₂ →
n ⊨ closed_δ ξ₁ ξ₂ δ →
closed_ρ ξ₁ ξ₂ ρ₁ ρ₂ →
∀ ξ₁' ξ₂' t₁ t₂ ψ Xs₁ Xs₂, n ⊨ 𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' t₁ t₂ ψ Xs₁ Xs₂ →
Xs₁ \c from_list ξ₁ ∧ Xs₂ \c from_list ξ₂.
Proof.
intros Hξ₁ξ₂ cl_δ cl_ρ₁ρ₂ ξ₁' ξ₂' t₁ t₂ ψ Xs₁ Xs₂ Ht.
induction 𝓔 as [ | ε 𝓔' IH𝓔' ] ; [ cbn in Ht ; icontradict Ht | ].
simpl in Ht ; idestruct Ht as Ht Ht ; [ clear 𝓔 IH𝓔' | auto ].
destruct ε as [ α | [ p | [ ι | Y ] ] ] ; simpl in Ht.
+ iespecialize cl_δ.
  ispecialize cl_δ ; [ apply Ht | ].
  auto.
+ specialize (cl_ρ₁ρ₂ p).
  idestruct Ht as 𝔽 Ht ; idestruct Ht as X₁ Ht ; idestruct Ht as X₂ Ht ;
  idestruct Ht as h₁ Ht ; idestruct Ht as h₂ Ht ;
  idestruct Ht as v₁ Ht ; idestruct Ht as v₂ Ht ;
  idestruct Ht as Hρ₁ρ₂ Ht ;
  idestruct Ht as Ht₁t₂ Ht ; idestruct Ht as HXs₁Xs₂ Ht ;
  idestruct Ht as Hr Ht ; idestruct Ht as Hv₁v₂ Hψ.

  idestruct Hr as r₁ Hr ; idestruct Hr as r₂ Hr ;
  idestruct Hr as _X₁ Hr ; idestruct Hr as _X₂ Hr ;
  idestruct Hr as Hh₁h₂ Hr ; idestruct Hr as _Hρ₁ρ₂ Hr.

  ielim_prop HXs₁Xs₂ ; destruct HXs₁Xs₂ ; subst.
  ielim_prop Ht₁t₂ ; destruct Ht₁t₂ ; subst.
  ielim_prop Hρ₁ρ₂ ; destruct Hρ₁ρ₂ as [Hρ₁ Hρ₂].
  ielim_prop Hh₁h₂ ; destruct Hh₁h₂ ; subst.
  ielim_prop _Hρ₁ρ₂ ; destruct _Hρ₁ρ₂ as [_Hρ₁ _Hρ₂].
  rewrite _Hρ₁, _Hρ₂ in *.
  inversion Hρ₁ ; inversion Hρ₂ ; subst.
  destruct (ρ₁ p) eqn : Hρ₁p ; destruct (ρ₂ p) eqn : Hρ₂p ;
  inversion _Hρ₁ ; inversion _Hρ₂ ; subst.

  clear - cl_ρ₁ρ₂.
  specialize (cl_ρ₁ρ₂ X₁) as HX₁ ; destruct HX₁ as [HX₁ _].
  specialize (cl_ρ₁ρ₂ X₂) as HX₂ ; destruct HX₂ as [_ HX₂].
  split ; intro ; crush.
+ contradict ι.
+ idestruct Ht as 𝔽 Ht ; idestruct Ht as X₁ Ht ; idestruct Ht as X₂ Ht ;
  idestruct Ht as h₁ Ht ; idestruct Ht as h₂ Ht ;
  idestruct Ht as v₁ Ht ; idestruct Ht as v₂ Ht ;
  idestruct Ht as HX₁X₂ Ht ;
  idestruct Ht as Ht₁t₂ Ht ; idestruct Ht as HXs₁Xs₂ Ht ;
  idestruct Ht as Hr Ht ; idestruct Ht as Hv₁v₂ Hψ.

  idestruct Hr as r₁ Hr ; idestruct Hr as r₂ Hr ; idestruct Hr as Hh₁h₂ Hr.
  idestruct Hr as T Hr ; idestruct Hr as 𝓔 Hr ; idestruct Hr as BindsY Hr.

  ielim_prop HXs₁Xs₂ ; destruct HXs₁Xs₂ ; subst.
  ielim_prop Ht₁t₂ ; destruct Ht₁t₂ ; subst.
  ielim_prop HX₁X₂ ; destruct HX₁X₂ as [HX₁ HX₂].
  ielim_prop Hh₁h₂ ; destruct Hh₁h₂ ; subst.
  inversion HX₁ ; inversion HX₂ ; subst X₁ X₂.
  ielim_prop BindsY ; apply get_some_inv in BindsY as Y_in_Ξ.

  clear - Y_in_Ξ Hξ₁ξ₂.
  destruct Hξ₁ξ₂.
  split ; intro ; crush.
Qed.

End section_Xs_is_𝓤_bounded.


Ltac bind_hole :=
  match goal with
  | [ |- ?n ⊨ 𝓣⟦ ?Ξ ⊢ ?T # ?𝓔 ⟧ _ _ _ _ _ _ _ _ ?t₁ ?t₂ ] =>
  replace t₁ with (ktx_plug ktx_hole t₁) by reflexivity ;
  replace t₂ with (ktx_plug ktx_hole t₂) by reflexivity
  end.

Ltac bind_let :=
  match goal with
  | [ |- ?n ⊨ 𝓣⟦ ?Ξ ⊢ ?T # ?𝓔 ⟧ _ _ _ _ _ _ _ _
              (tm_let ?t₁ ?s₁) (tm_let ?t₂ ?s₂) ] =>
    replace (tm_let t₁ s₁)
    with (ktx_plug (ktx_let ktx_hole s₁) t₁) by reflexivity ;
    replace (tm_let t₂ s₂)
    with (ktx_plug (ktx_let ktx_hole s₂) t₂) by reflexivity
  end.

Ltac bind_app1 :=
  match goal with
  | [ |- ?n ⊨ 𝓣⟦ ?Ξ ⊢ ?T # ?𝓔 ⟧ _ _ _ _ _ _ _ _
              (tm_app ?t₁ ?s₁)
              (tm_app ?t₂ ?s₂)
    ] =>
    replace (tm_app t₁ s₁) with (ktx_plug (ktx_app1 ktx_hole s₁) t₁)
    by reflexivity ;
    replace (tm_app t₂ s₂) with (ktx_plug (ktx_app1 ktx_hole s₂) t₂)
    by reflexivity
  end.

Ltac bind_app2 :=
  match goal with
  | [ |- ?n ⊨ 𝓣⟦ ?Ξ ⊢ ?T # ?𝓔 ⟧ _ _ _ _ _ _ _ _
         (tm_app (tm_val ?v₁) ?s₁)
         (tm_app (tm_val ?v₂) ?s₂)
    ] =>
    replace (tm_app (tm_val v₁) s₁)
    with (ktx_plug (ktx_app2 ktx_hole v₁) s₁) by reflexivity ;
    replace (tm_app (tm_val v₂) s₂)
    with (ktx_plug (ktx_app2 ktx_hole v₂) s₂) by reflexivity
  end.

Ltac bind_eapp :=
  match goal with
  | [ |- ?n ⊨ 𝓣⟦ ?Ξ ⊢ ?T # ?𝓔 ⟧ _ _ _ _ _ _ _ _
              (tm_eapp ?t₁ ?𝓔₁)
              (tm_eapp ?t₂ ?𝓔₂)
    ] =>
    replace (tm_eapp t₁ 𝓔₁)
    with (ktx_plug (ktx_eapp ktx_hole 𝓔₁) t₁)
    by reflexivity ;
    replace (tm_eapp t₂ 𝓔₂)
    with (ktx_plug (ktx_eapp ktx_hole 𝓔₂) t₂)
    by reflexivity
  end.

Ltac bind_happ :=
  match goal with
  | [ |- ?n ⊨ 𝓣⟦ ?Ξ ⊢ ?T # ?𝓔 ⟧ _ _ _ _ _ _ _ _
              (tm_happ ?t₁ ?ℓ₁)
              (tm_happ ?t₂ ?ℓ₂)
    ] =>
    replace (tm_happ t₁ ℓ₁)
    with (ktx_plug (ktx_happ ktx_hole ℓ₁) t₁)
    by reflexivity ;
    replace (tm_happ t₂ ℓ₂)
    with (ktx_plug (ktx_happ ktx_hole ℓ₂) t₂)
    by reflexivity
  end.
