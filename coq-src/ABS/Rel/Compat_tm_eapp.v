Require Import Rel.Definitions.
Require Import Rel.BasicFacts.
Require Import Rel.Compat_sub.
Require Import Rel.Compat_bind_EV.
Require Import Util.Subset.
Require Import Lang.BindingsFacts.
Require Import Lang.Static.
Require Import Lang.StaticFacts.
Set Implicit Arguments.

Section section_compat_tm_eapp.

Context (EV HV V : Set).
Context (Ξ : XEnv EV HV).
Context (Γ : V → ty EV HV ∅).
Context (P : HV → F).
Context (T : ty (inc EV) HV ∅).
Context (𝓔 𝓕 : eff EV HV ∅).
Context (t₁ t₂ : tm EV HV V ∅).

Hint Resolve subset_trans st_reflexive postfix_is_subset postfix_refl.
Hint Rewrite lbl_V_map_hd.

Lemma compat_tm_eapp n :
n ⊨ ⟦ Ξ P Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : (ty_efun T) # 𝓕 ⟧ →
n ⊨ ⟦ Ξ P Γ ⊢ (tm_eapp t₁ 𝓔) ≼ˡᵒᵍ (tm_eapp t₂ 𝓔) : (EV_subst_ty 𝓔 T) # 𝓕 ⟧.
Proof.
intro Ht.
iintro ξ₁ ; iintro ξ₂ ; iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ; iintro γ₁ ; iintro γ₂.
iintro Hξ ; iintro cl_δ ; iintro cl_ρ₁ρ₂ ; iintro Hρ ; iintro Hγ.
iespecialize Ht.
repeat (ispecialize Ht ; [ eassumption | ]).

simpl.
generalize Ht.
generalize (subst_tm δ₁ ρ₁ γ₁ t₁), (subst_tm δ₂ ρ₂ γ₂ t₂).
clear Ht t₁ t₂.
intros t₁ t₂ Ht.

bind_eapp.
eapply plug0 with (ξ₁ := ξ₁) (ξ₂ := ξ₂) ; [auto|auto| |auto|auto|exact Ht].

iintro ξ₁' ; iintro ξ₂' ; iintro v₁ ; iintro v₂ ; iintro Hξ₁' ; iintro Hξ₂' ; iintro Hv.
simpl in Hv |- *.
ispecialize Hv ξ₁' ; ispecialize Hv ξ₂'.
ispecialize Hv ; [auto 6|].
ispecialize Hv ; [auto 6|].
ispecialize Hv (subst_eff δ₁ ρ₁ 𝓔).
ispecialize Hv (subst_eff δ₂ ρ₂ 𝓔).
ispecialize Hv (𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ).
ispecialize Hv.
{ iintro ; iintro ; iintro ; iintro ; iintro ; iintro Xs₁ ; iintro Xs₂ ; iintro.
  iintro_prop ; assert (Xs₁ \c from_list ξ₁ ∧ Xs₂ \c from_list ξ₂) as HXs₁Xs₂.
  - eapply Xs_is_𝓤_bounded ; eauto.
  - clear - Hξ₁' Hξ₂' HXs₁Xs₂.
    destruct HXs₁Xs₂.
    split ; eauto.
}

change (
  λ _ _ _ _ _ _ _, (False)ᵢ
) with (
  𝓤⟦ (EV_shift_XEnv Ξ) ⊢ [] ⟧
  (env_ext δ₁ (subst_eff δ₁ ρ₁ 𝓔))
  (env_ext δ₂ (subst_eff δ₂ ρ₂ 𝓔))
  (env_ext δ (𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ))
  ρ₁ ρ₂ ρ
) in Hv.

replace (subst_eff δ₁ (V_open_hd ∘ ρ₁) 𝓔) with (subst_eff δ₁ ρ₁ 𝓔) by
  (clear ; apply HV_bind_eff_eq ; crush).
replace (subst_eff δ₂ (V_open_hd ∘ ρ₂) 𝓔) with (subst_eff δ₂ ρ₂ 𝓔) by
  (clear ; apply HV_bind_eff_eq ; crush).
replace Ξ with (EV_bind_XEnv (EV_substfun 𝓔) (EV_shift_XEnv Ξ)) by
  (clear ; erewrite EV_bind_map_XEnv, EV_bind_XEnv_id, EV_map_XEnv_id ; crush).
apply ccompat_sub with (T := EV_subst_ty 𝓔 T) (𝓔 := EV_subst_eff 𝓔 []) ; [crush|crush|].
erewrite <- I_iff_elim_M ; [ exact Hv | apply EV_bind_𝓣 ; clear ].

{ intro α ; destruct α ; unfold compose ; simpl ; [ crush | ].
  rewrite app_nil_r.
  unshelve erewrite HV_bind_map_eff, HV_bind_eff_id, HV_map_eff_id ; crush.
}
{ intro α ; destruct α ; unfold compose ; simpl ; [ crush | ].
  rewrite app_nil_r.
  unshelve erewrite HV_bind_map_eff, HV_bind_eff_id, HV_map_eff_id ; crush.
}
{ iintro α ; repeat iintro.
  destruct α ; simpl.
  + erewrite EV_bind_map_XEnv, EV_bind_XEnv_id, EV_map_XEnv_id ;
    try apply auto_contr_id ; crush.
  + isplit ; iintro H ; [ ileft | idestruct H as H H ] ; crush.
}
Qed.

End section_compat_tm_eapp.
