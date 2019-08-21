Require Import Rel.Definitions.
Require Import Rel.BasicFacts.
Require Import Rel.Compat_sub.
Require Import Rel.Compat_bind_HV.
Require Import Util.Subset.
Require Import Lang.BindingsFacts.
Require Import Lang.Static.
Require Import Lang.StaticFacts.
Set Implicit Arguments.

Section section_compat_tm_happ.

Context (EV HV V : Set).
Context (Ξ : XEnv EV HV).
Context (Γ : V → ty EV HV ∅).
Context (P : HV → F).
Context (𝔽 : F).
Context (T : ty EV (inc HV) ∅).
Context (𝓔 : eff EV HV ∅).
Context (ℓ : lbl HV ∅).
Context (t₁ t₂ : tm EV HV V ∅).
Context (h₁ h₂ : hd EV HV V ∅).
Context (H_lbl_h₁ : lbl_hd h₁ = ℓ).
Context (H_lbl_h₂ : lbl_hd h₂ = ℓ).
Context (Wf_lbl_h₁ : wf_lbl Ξ (lbl_hd h₁)).

Hint Resolve subset_trans subset_refl st_reflexive get_some_inv postfix_refl postfix_is_subset.
Hint Constructors wf_lbl.

Lemma compat_tm_happ n :
n ⊨ ⟦ Ξ P Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : (ty_hfun 𝔽 T) # 𝓔 ⟧ →
n ⊨ ⟦ Ξ P Γ ⊢ h₁ ≼ˡᵒᵍₕ h₂ : 𝔽 # ℓ ⟧ →
n ⊨ ⟦ Ξ P Γ ⊢ (tm_happ t₁ h₁) ≼ˡᵒᵍ (tm_happ t₂ h₂) : (HV_subst_ty h₁ T) # 𝓔 ⟧.
Proof.
intros Ht Hh.
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

bind_happ.
eapply plug0 with (ξ₁ := ξ₁) (ξ₂ := ξ₂) ; [auto|auto| |auto|auto|exact Ht].

iintro ξ₁' ; iintro ξ₂' ; iintro v₁ ; iintro v₂ ; iintro Hξ₁' ; iintro Hξ₂' ; iintro Hv.
simpl in Hv |- *.
ispecialize Hv ξ₁' ; ispecialize Hv ξ₂'.
ispecialize Hv ; [auto 6|].
ispecialize Hv ; [auto 6|].
eapply ccompat_sub
  with (T := HV_subst_ty h₁ T) (𝓔 := HV_subst_eff h₁ []) ; [crush|crush| ].

replace Ξ with (HV_bind_XEnv (HV_substfun h₁) (HV_shift_XEnv Ξ)) by (
  erewrite
    HV_bind_map_XEnv with (g₁ := @hd_var EV HV V ∅),
    HV_bind_XEnv_id, HV_map_XEnv_id ;
  crush
).
erewrite <- I_iff_elim_M ; [ |
  eapply HV_bind_𝓣 with
    (ρ₁ := env_ext ρ₁ (subst_hd δ₁ ρ₁ γ₁ h₁))
    (ρ₂ := env_ext ρ₂ (subst_hd δ₂ ρ₂ γ₂ h₂))
    (ρ := env_ext ρ (𝓣𝓛⟦ HV_subst_XEnv h₁ (HV_shift_XEnv Ξ) ⊢ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ))
].
+ ispecialize Hh ξ₁' ; ispecialize Hh ξ₂'.
  ispecialize Hh δ₁ ; ispecialize Hh δ₂ ; ispecialize Hh δ.
  ispecialize Hh ρ₁ ; ispecialize Hh ρ₂ ; ispecialize Hh ρ.
  ispecialize Hh γ₁ ; ispecialize Hh γ₂.
  ispecialize Hh.
  { clear - Hξ Hξ₁' Hξ₂'.
    repeat match goal with [ H : _ ⊨ (_)ᵢ |- _ ] => ielim_prop H end.
    destruct Hξ ; iintro_prop ; split ; eauto.
  }
  ispecialize Hh.
  { clear - cl_δ Hξ₁' Hξ₂'.
    repeat iintro ; iespecialize cl_δ ; ispecialize cl_δ ; [ eassumption | ].
    repeat match goal with [ H : _ ⊨ (_)ᵢ |- _ ] => ielim_prop H end.
    destruct cl_δ ; split ; eauto.
  }
  ispecialize Hh.
  { clear - cl_ρ₁ρ₂ Hξ₁' Hξ₂'.
    repeat match goal with [ H : _ ⊨ (_)ᵢ |- _ ] => ielim_prop H end.
    iintro_prop ; eapply closed_ρ_monotone ; eauto.
  }
  ispecialize Hh.
  { eapply 𝑷_monotone ; eauto. }
  ispecialize Hh.
  { eapply 𝜞_monotone ; eauto. }

  destruct ℓ as [ p | [ | X ] ] ; [ | auto | ] ; simpl in Hh |- *.
  - idestruct Hh as r₁ Hh ; idestruct Hh as r₂ Hh ;
    idestruct Hh as X₁ Hh ; idestruct Hh as X₂ Hh ;
    idestruct Hh as Hh₁h₂ Hh ; idestruct Hh as Hρ₁ρ₂ Hr.
    ielim_prop Hh₁h₂ ; destruct Hh₁h₂ as [Hh₁ Hh₂] ; rewrite Hh₁, Hh₂.
    ielim_prop Hρ₁ρ₂ ; destruct Hρ₁ρ₂ as [Hρ₁ Hρ₂].
    ispecialize Hv r₁ ; ispecialize Hv r₂ ;
    ispecialize Hv X₁ ; ispecialize Hv X₂ ; ispecialize Hv (ρ p).
    ispecialize Hv.
    { clear - Hρ₁ Hρ₂ cl_ρ₁ρ₂ Hξ₁' Hξ₂'.
      repeat match goal with [ H : _ ⊨ (_)ᵢ |- _ ] => ielim_prop H end.
      specialize (cl_ρ₁ρ₂ p X₁) as cl_ρ₁ ; destruct cl_ρ₁ as [cl_ρ₁ _].
      specialize (cl_ρ₁ρ₂ p X₂) as cl_ρ₂ ; destruct cl_ρ₂ as [_ cl_ρ₂].
      apply postfix_is_subset in Hξ₁'.
      apply postfix_is_subset in Hξ₂'.
      crush.
    }
    ispecialize Hv ; [ exact Hr | exact Hv ].
  - idestruct Hh as r₁ Hh ; idestruct Hh as r₂ Hh ; idestruct Hh as Hh₁h₂ Hh ;
    idestruct Hh as S Hh ; idestruct Hh as 𝓕 Hh ; idestruct Hh as BindsX Hr.
    ielim_prop Hh₁h₂ ; destruct Hh₁h₂ as [Hh₁ Hh₂] ; rewrite Hh₁, Hh₂.
    ielim_prop BindsX.
    erewrite
      HV_bind_map_XEnv with (g₁ := @hd_var EV HV V ∅),
      HV_bind_XEnv_id, HV_map_XEnv_id ;
    [ | crush | crush | crush ].
    rewrite BindsX.
    ispecialize Hv r₁ ; ispecialize Hv r₂ ;
    ispecialize Hv X ; ispecialize Hv X ;
    ispecialize Hv (𝓣⟦ Ξ ⊢ S # 𝓕 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ).
    ispecialize Hv.
    { clear - BindsX Hξ Hξ₁' Hξ₂'.
      repeat match goal with [ H : _ ⊨ (_)ᵢ |- _ ] => ielim_prop H end.
      apply postfix_is_subset in Hξ₁'.
      apply postfix_is_subset in Hξ₂'.
      destruct Hξ.
      iintro_prop ; split ; eauto.
    }
    ispecialize Hv ; [ | exact Hv ].
    erewrite I_iff_elim_M ; [ apply Hr | clear ].
    auto_contr.
    apply 𝓗_Fun'_nonexpansive.
    * repeat iintro ; apply auto_contr_id.
    * repeat iintro ; apply fold_𝓥𝓤_in_𝓣.

+ destruct p as [ | p ] ; simpl ; [ crush | ].
  unfold compose ; erewrite V_bind_map_hd, V_bind_hd_id, V_map_hd_id ; crush.

+ destruct p as [ | p ] ; simpl.
  - destruct h₁ as [ p₁ | ? X₁ ? ], h₂ as [ p₂ | ? X₂ ? ] ;
    simpl in H_lbl_h₁, H_lbl_h₂ ;
    rewrite <- H_lbl_h₂ in H_lbl_h₁ ; inversion H_lbl_h₁ ;
    subst ; reflexivity.
  - unfold compose ; erewrite V_bind_map_hd, V_bind_hd_id, V_map_hd_id ; crush.

+ iintro p ; repeat iintro.
  destruct p as [ | p ] ; simpl ; try rewrite H_lbl_h₁ ; apply auto_contr_id.

+ assert (Wf_ℓ : wf_lbl Ξ ℓ).
  { clear - H_lbl_h₁ Wf_lbl_h₁ ; subst.
    auto.
  }
  destruct p as [ | p ] ; simpl ; try rewrite H_lbl_h₁ ; [ | constructor ].
  erewrite
    HV_bind_map_XEnv with (g₁ := @hd_var EV HV V ∅),
    HV_bind_XEnv_id, HV_map_XEnv_id ; crush.

Qed.

End section_compat_tm_happ.
