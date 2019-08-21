Require Import Rel.Definitions.
Require Import Rel.BasicFacts.
Require Import Rel.Compat_weaken_X.
Require Import Util.Subset.
Require Import Lang.BindingsFacts.
Require Import Lang.Static.
Set Implicit Arguments.

Section section_ccompat_tm_down.
Context (EV HV : Set).
Context (Ξ : XEnv EV HV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig).
Context (X : var).
Context (T : ty EV HV ∅) (𝓔 : eff EV HV ∅).

Hint Resolve postfix_refl.
Hint Rewrite in_singleton.

Lemma ccompat_tm_down_aux n :
n ⊨ ( ∀ᵢ ξ₁' ξ₂' t₁' t₂' ψ Xs₁ Xs₂,
      𝓤⟦ (Ξ & X ~ (T, 𝓔)) ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' t₁' t₂' ψ Xs₁ Xs₂ ⇒
      (X ∉ Xs₁ ∧ X ∉ Xs₂)ᵢ
    ) →
n ⊨ ∀ᵢ ζ₁ ζ₂ ξ₁ ξ₂ t₁ t₂,
    𝓣⟦ Ξ & (X ~ (T,𝓔)) ⊢ T # (ef_lbl (lbl_id (lid_f X))) :: 𝓔 ⟧
      δ₁ δ₂ δ ρ₁ ρ₂ ρ
      (ζ₁ ++ X :: ξ₁) (ζ₂ ++ X :: ξ₂) t₁ t₂ ⇒
    𝓣⟦ Ξ & (X ~ (T,𝓔)) ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
      (ζ₁ ++ X :: ξ₁) (ζ₂ ++ X :: ξ₂)
      (ktx_plug (ktx_down ktx_hole X) t₁)
      (ktx_plug (ktx_down ktx_hole X) t₂).
Proof.
intro FrX.
loeb_induction LöbIH.
iintro ζ₁ ; iintro ζ₂ ; iintro ξ₁ ; iintro ξ₂ ; iintro t₁ ; iintro t₂ ; iintro Ht.
apply plug1 with
  (ε := ef_lbl (lbl_id (lid_f X))) (Ta := T) (ξ₁ := ζ₁ ++ X :: ξ₁) (ξ₂ := ζ₂ ++ X :: ξ₂).
+ exact FrX.
+ iintro ξ₁' ; iintro ξ₂' ; iintro v₁ ; iintro v₂ ;
  iintro Hξ₁' ; iintro Hξ₂' ; iintro Hv.
  ielim_prop Hξ₁' ; ielim_prop Hξ₂'.
  eapply 𝓣_step_r.
  { simpl.
    apply step_down_val.
  }
  eapply 𝓣_step_l.
  { simpl.
    apply step_down_val.
  }
  iintro_later.
  apply 𝓥_in_𝓣 ; apply Hv.
+ clear - LöbIH.
  iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂'.
  iintro K₁ ; iintro K₂ ;
  iintro s₁ ; iintro s₂ ; iintro ψ ; iintro Xs₁ ; iintro Xs₂.
  iintro H.
  iintro Xs_K₁K₂.
  iintro Hw.
  ielim_prop Hξ₁' ; ielim_prop Hξ₂'.
  ielim_prop Xs_K₁K₂.

  idestruct H as 𝔽 H ;
  idestruct H as X₁ H ; idestruct H as X₂ H ;
  idestruct H as h₁ H ; idestruct H as h₂ H ;
  idestruct H as v₁ H ; idestruct H as v₂ H ;
  idestruct H as Hρ₁ρ₂ H ;
  idestruct H as Hs₁s₂ H ; idestruct H as HXs₁Xs₂ H ; idestruct H as Hr H ;
  idestruct H as Hv Hψ.

  ielim_prop Hρ₁ρ₂ ; destruct Hρ₁ρ₂ as [Hρ₁ Hρ₂].
  ielim_prop Hs₁s₂ ; destruct Hs₁s₂ as [Hs₁ Hs₂].
  ielim_prop HXs₁Xs₂ ; destruct HXs₁Xs₂ as [HXs₁ HXs₂].
  simpl in Hρ₁, Hρ₂ ; inversion Hρ₁ ; inversion Hρ₂ ; clear Hρ₁ Hρ₂.
  subst s₁ s₂ Xs₁ Xs₂ X₁ X₂.

  idestruct Hr as r₁ Hr ; idestruct Hr as r₂ Hr ; idestruct Hr as H_r₁r₂ Hr.
  ielim_prop H_r₁r₂ ; destruct H_r₁r₂ as [H_r₁ H_r₂].
  subst h₁ h₂.

  idestruct Hr as _T Hr ; idestruct Hr as _𝓔 Hr ; idestruct Hr as _BindsX Hr.
  ielim_prop _BindsX.
  apply binds_concat_inv in _BindsX.
  destruct _BindsX as [ _BindsX | [ H1 H2 ] ] ;
  [ | rewrite dom_single in H1 ; apply notin_same in H1 ; contradict H1 ].
  apply binds_single_inv in _BindsX.
  destruct _BindsX as [ _ H' ] ; inversion H' ; clear H' ; subst _T _𝓔.

  simpl.
  specialize (Xs_K₁K₂ X).
  assert (tunnels X K₁) ; [ crush | ].
  assert (tunnels X K₂) ; [ crush | ].
  eapply 𝓣_step_r.
  { apply step_down_up ; eauto. }
  eapply 𝓣_step_l.
  { apply step_down_up ; eauto. }
  later_shift.

  ispecialize Hr ξ₁' ; ispecialize Hr ξ₂'.
  ispecialize Hr ; [ auto | ].
  ispecialize Hr ; [ auto | ].
  iespecialize Hr.
  ispecialize Hr ; [ apply Hv | ].
  erewrite I_iff_elim_M ; [ | apply fold_𝓥𝓤_in_𝓣 ].
  iapply Hr.

  clear - LöbIH Hψ Hw Hξ₁' Hξ₂'.
  iintro ξ₁'' ; iintro ξ₂'' ; iintro u₁ ; iintro u₂ ;
  iintro Hξ₁'' ; iintro  Hξ₂'' ; iintro Hu.
  ispecialize Hψ ξ₁'' ; ispecialize Hψ ξ₂''.
  iespecialize Hψ ; idestruct Hψ as Hψ Hψr ; clear Hψr.
  ispecialize Hψ.
  { iintro_later ; repeat ieexists ; isplit.
    + iintro_prop ; split ; reflexivity.
    + eassumption.
  }
  iespecialize Hw.
  ispecialize Hw ; [ apply Hξ₁'' | ].
  ispecialize Hw ; [ apply Hξ₂'' | ].
  ispecialize Hw ; [ apply Hψ | ].

  later_shift.
  erewrite <- I_iff_elim_M ; [ | apply fold_𝓥𝓤_in_𝓣 ].

  simpl ktx_plug in LöbIH.
  ielim_prop Hξ₁'' ; ielim_prop Hξ₂''.
  apply postfix_inv_app in Hξ₁'' ; destruct Hξ₁'' as [ ζ₁'' Hξ₁'' ].
  apply postfix_inv_app in Hξ₂'' ; destruct Hξ₂'' as [ ζ₂'' Hξ₂'' ].
  apply postfix_inv_app in Hξ₁' ; destruct Hξ₁' as [ ζ₁' Hξ₁' ].
  apply postfix_inv_app in Hξ₂' ; destruct Hξ₂' as [ ζ₂' Hξ₂' ].
  ispecialize LöbIH (ζ₁'' ++ ζ₁' ++ ζ₁) ;
  ispecialize LöbIH (ζ₂'' ++ ζ₂' ++ ζ₂) ;
  ispecialize LöbIH ξ₁ ;
  ispecialize LöbIH ξ₂.
  repeat rewrite <- app_assoc in LöbIH.
  rewrite <- Hξ₁', <- Hξ₂', <- Hξ₁'', <- Hξ₂'' in LöbIH.
  iespecialize LöbIH.
  ispecialize LöbIH ; [ apply Hw | ].
  apply LöbIH.
+ crush.
+ crush.
+ assumption.
Qed.

Context (FrX_Ξ : X # Ξ).
Context (Wf_Ξ : wf_XEnv Ξ).
Context (Wf_T : wf_ty Ξ T).
Context (Wf_𝓔 : wf_eff Ξ 𝓔).

Hint Constructors wf_XEnv.

Lemma ccompat_tm_down n ξ₁ ξ₂ t₁ t₂ :
n ⊨ ( ∀ᵢ ξ₁' ξ₂' t₁' t₂' ψ Xs₁ Xs₂,
      𝓤⟦ (Ξ & X ~ (T, 𝓔)) ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' t₁' t₂' ψ Xs₁ Xs₂ ⇒
      (X ∉ Xs₁ ∧ X ∉ Xs₂)ᵢ
    ) →
X ∉ from_list ξ₁ → X ∉ from_list ξ₂ →
n ⊨ 𝓣⟦ (Ξ & (X ~ (T, 𝓔))) ⊢ T # (ef_lbl (lbl_id (lid_f X))) :: 𝓔 ⟧
    δ₁ δ₂ δ ρ₁ ρ₂ ρ
    (X :: ξ₁) (X :: ξ₂)
    (L_subst_tm (lid_f X) t₁) (L_subst_tm (lid_f X) t₂) →
n ⊨ 𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ (⬇ t₁) (⬇ t₂).
Proof.
intros FrX_𝓔 FrX_ξ₁ FrX_ξ₂ Ht.
specialize (ccompat_tm_down_aux FrX_𝓔) as H.
ispecialize H ([] : list var).
ispecialize H ([] : list var).
iespecialize H.
repeat rewrite app_nil_l in H.
simpl ktx_plug in H.

eapply 𝓣_step_r.
{ apply step_Down with (X := X) ; assumption. }
eapply 𝓣_step_l.
{ apply step_Down with (X := X) ; assumption. }

iintro_later.
iespecialize H ; ispecialize H ; [ apply Ht | ].
erewrite I_iff_elim_M ; [ apply H | apply X_weaken_𝓣 ] ; crush.
Qed.

End section_ccompat_tm_down.


Section section_compat_tm_down.
Context (n : nat).
Context (EV HV V : Set).
Context (Ξ : XEnv EV HV).
Context (P : HV → F).
Context (Γ : V → ty EV HV ∅).
Context (Wf_Γ : wf_Γ Ξ Γ).
Context (t₁ t₂ : tm EV HV V (inc ∅)).
Context (T : ty EV HV ∅) (𝓔 : eff EV HV ∅).
Context (Wf_Ξ : wf_XEnv Ξ).
Context (Wf_T : wf_ty Ξ T).
Context (Wf_𝓔 : wf_eff Ξ 𝓔).

Hint Resolve subset_union_l subset_union_r postfix_refl.
Hint Resolve 𝓥_monotone.
Hint Rewrite in_union.
Hint Constructors wf_XEnv postfix.

Lemma compat_tm_down (B : vars) :
( ∀ X, X \notin B →
  n ⊨ ⟦ (Ξ & (X ~ (T, 𝓔))) P Γ ⊢
        (L_subst_tm (lid_f X) t₁) ≼ˡᵒᵍ (L_subst_tm (lid_f X) t₂) :
        T # (ef_lbl (lbl_id (lid_f X))) :: 𝓔 ⟧
) →
n ⊨ ⟦ Ξ P Γ ⊢ (⬇ t₁) ≼ˡᵒᵍ (⬇ t₂) : T # 𝓔 ⟧.
Proof.
intro Ht.
iintro ξ₁ ; iintro ξ₂ ; iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ; iintro γ₁ ; iintro γ₂.
pick_fresh_gen (from_list ξ₁ \u from_list ξ₂ \u B) X.
assert (X ∉ B) as FrB ; [ crush | ].
specialize (Ht X FrB).
iintro Hξ ; iintro cl_δ ; iintro cl_ρ₁ρ₂ ; iintro Hρ ; iintro Hγ.
ielim_prop Hξ ; ielim_prop cl_ρ₁ρ₂.
specialize Hξ as Hξ_copy ; destruct Hξ_copy as [Hξ₁ Hξ₂].

assert (X ∉ from_list ξ₁) as Frξ₁ ; [ crush | ].
assert (X ∉ from_list ξ₂) as Frξ₂ ; [ crush | ].
assert (X ∉ dom Ξ) as FrΞ ; [ intro ; crush | ].

ispecialize Ht (X :: ξ₁) ; ispecialize Ht (X :: ξ₂).
ispecialize Ht δ₁ ; ispecialize Ht δ₂ ; ispecialize Ht δ.
ispecialize Ht ρ₁ ; ispecialize Ht ρ₂ ; ispecialize Ht ρ.
ispecialize Ht γ₁ ; ispecialize Ht γ₂.
ispecialize Ht.
{ iintro_prop ; split ; [ clear - Hξ₁ | clear - Hξ₂ ] ;
  rewrite dom_concat, from_list_cons, dom_single, union_comm ;
  apply subset_union_2 ; crush.
}
ispecialize Ht.
{ repeat iintro ; iespecialize cl_δ ; ispecialize cl_δ ; [ eassumption | ].
  repeat rewrite from_list_cons ; ielim_prop cl_δ.
  crush.
}
ispecialize Ht.
{ iintro_prop ; intros α Y ; specialize (cl_ρ₁ρ₂ α Y) ;
  clear - cl_ρ₁ρ₂ ; repeat rewrite from_list_cons ; crush.
}
ispecialize Ht.
{ eapply 𝑷_monotone ; eauto. }
ispecialize Ht.
{ iintro x ; ispecialize Hγ x ; clear - Wf_Ξ Wf_Γ Wf_T Wf_𝓔 FrΞ Hγ.
  erewrite <- I_iff_elim_M ; [ | apply X_weaken_𝓥 ] ; eauto.
}

simpl.
apply ccompat_tm_down with (X := X) ; try assumption.
+ iintro ξ₁' ; iintro ξ₂' ;
  iintro s₁ ; iintro s₂ ; iintro ψ ; iintro Xs₁ ; iintro Xs₂ ; iintro Hs.
  erewrite <- I_iff_elim_M in Hs ; [ | apply X_weaken_𝓤 ; crush ].
  iintro_prop.
  assert (Xs₁ \c from_list ξ₁ ∧ Xs₂ \c from_list ξ₂) as HXs₁Xs₂.
  { eapply Xs_is_𝓤_bounded ; eassumption. }
  clear - HXs₁Xs₂ Frξ₁ Frξ₂.
  destruct HXs₁Xs₂.
  split ; intro ; auto.
+ clear - Ht.
  repeat erewrite <- V_L_bind_tm, <- HV_L_bind_tm, <- EV_L_bind_tm.
  { apply Ht. }
  { intro ; unfold compose.
    erewrite L_bind_map_eff, L_bind_eff_id, L_map_eff_id ; crush. }
  { intro ; unfold compose.
    erewrite L_bind_map_hd, L_bind_hd_id, L_map_hd_id ; crush. }
  { intro ; unfold compose.
    erewrite L_bind_map_val, L_bind_val_id, L_map_val_id ; crush. }
  { intro ; unfold compose.
    erewrite L_bind_map_eff, L_bind_eff_id, L_map_eff_id ; crush. }
  { intro ; unfold compose.
    erewrite L_bind_map_hd, L_bind_hd_id, L_map_hd_id ; crush. }
  { intro ; unfold compose.
    erewrite L_bind_map_val, L_bind_val_id, L_map_val_id ; crush. }

Qed.

End section_compat_tm_down.
