Require Import Rel.Definitions Rel.BasicFacts Rel.Compat_map_HV.
Require Import Util.Subset.
Require Import Lang.BindingsFacts.
Set Implicit Arguments.

Section section_compat_val_hfun.

Context (EV HV V : Set).
Context (Ξ : XEnv EV HV).
Context (Γ : V → ty EV HV ∅).
Context (P : HV → F).
Context (𝔽 : F).
Context (T : ty EV (inc HV) ∅).
Context (t₁ t₂ : tm EV (inc HV) V ∅).

Hint Resolve subset_trans postfix_is_subset.

Lemma compat_val_hfun n :
n ⊨ ⟦ (HV_shift_XEnv Ξ) (env_ext P 𝔽) (HV_shift_ty ∘ Γ) ⊢ t₁ ≼ˡᵒᵍ t₂ : T # [] ⟧ →
n ⊨ ⟦ Ξ P Γ ⊢ (val_hfun t₁) ≼ˡᵒᵍᵥ (val_hfun t₂) : (ty_hfun 𝔽 T) ⟧.
Proof.
intro Ht.
iintro ξ₁ ; iintro ξ₂ ; iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ; iintro γ₁ ; iintro γ₂.
iintro Hξ ; iintro cl_δ ; iintro cl_ρ₁ρ₂ ; iintro Hρ ; iintro Hγ.
ielim_prop Hξ ; destruct Hξ as [Hξ₁ Hξ₂].
ielim_prop cl_ρ₁ρ₂.

simpl.
iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
iintro r₁ ; iintro r₂ ; iintro X₁ ; iintro X₂ ;
iintro η ; iintro cl_η ; iintro Hr.
ielim_prop Hξ₁' ; ielim_prop Hξ₂'.
pose (h₁ := hd_def 𝔽 (lid_f X₁) r₁).
pose (h₂ := hd_def 𝔽 (lid_f X₂) r₂).
ispecialize Ht ξ₁' ; ispecialize Ht ξ₂'.
ispecialize Ht δ₁ ; ispecialize Ht δ₂ ; ispecialize Ht δ.
ispecialize Ht (env_ext ρ₁ h₁) ; ispecialize Ht (env_ext ρ₂ h₂) ;
ispecialize Ht (env_ext ρ η).
ispecialize Ht γ₁ ; ispecialize Ht γ₂.
ispecialize Ht.
{ clear - Hξ₁ Hξ₂ Hξ₁' Hξ₂'.
  iintro_prop ; split ; rewrite HV_map_XEnv_dom ; eauto.
}
ispecialize Ht.
{ clear - cl_δ Hξ₁' Hξ₂'.
  repeat iintro ; iespecialize cl_δ ; ispecialize cl_δ ; [ eassumption | ].
  ielim_prop cl_δ ; destruct cl_δ ; split ; eauto.
}
ispecialize Ht.
{ clear - cl_ρ₁ρ₂ cl_η Hξ₁' Hξ₂'.
  iintro_prop ; intros p X.
  destruct p as [ | p ] ; simpl.
  + ielim_prop cl_η ; destruct cl_η.
    split ; let H := fresh in (intro H ; inversion H) ; subst ; auto.
  + specialize (cl_ρ₁ρ₂ p X) ; destruct cl_ρ₁ρ₂ as [cl_ρ₁ cl_ρ₂].
    split ; intro H ; [ apply cl_ρ₁ in H | apply cl_ρ₂ in H ].
    - apply postfix_is_subset in Hξ₁' ; auto.
    - apply postfix_is_subset in Hξ₂' ; auto.
}
ispecialize Ht.
{ clear - Hρ Hr Hξ₁' Hξ₂'.
  iintro p ; destruct p as [ | p ] ; simpl.
  + repeat ieexists ; isplit ; try iintro_prop ; crush.
  + clear - Hρ Hξ₁' Hξ₂' ; iespecialize Hρ.
    idestruct Hρ as r₁ Hρ ; idestruct Hρ as r₂ Hρ.
    idestruct Hρ as X₁ Hρ ; idestruct Hρ as X₂ Hρ ; idestruct Hρ as Hρ Hr.
    repeat ieexists ; isplit ; [ eauto | ].
    later_shift ; eapply 𝓗_Fun'_monotone ; eauto.
}
ispecialize Ht.
{ clear - Hγ Hξ₁' Hξ₂'.
  iintro x ; iespecialize Hγ.
  eapply 𝓥_monotone ; try eassumption.
  erewrite <- I_iff_elim_M ; [ exact Hγ | apply HV_map_𝓥 ] ; simpl.
  - auto.
  - auto.
  - repeat iintro ; apply auto_contr_id.
}

clear - Ht.
change (
  λ _ _ _ _ _ _ _, (False)ᵢ
) with (
  𝓤⟦ (HV_shift_XEnv Ξ) ⊢ [] ⟧
  δ₁ δ₂ δ
  (env_ext ρ₁ (hd_def 𝔽 (lid_f X₁) r₁))
  (env_ext ρ₂ (hd_def 𝔽 (lid_f X₂) r₂))
  (env_ext ρ η)
).
eapply 𝓣_step_r ; [ apply step_happ | ].
eapply 𝓣_step_l ; [ apply step_happ | ].
iintro_later.

repeat erewrite <- HV_V_bind_tm.
repeat erewrite HV_bind_bind_tm.
unfold compose.
rewrite EV_bind_tm_eq with
  (f := λ x : EV, HV_shift_eff (HV_open_eff (δ₁ x)))
  (g := HV_open_eff ∘ δ₁).
rewrite EV_bind_tm_eq with
  (f := λ x : EV, HV_shift_eff (HV_open_eff (δ₂ x)))
  (g := HV_open_eff ∘ δ₂).
exact Ht.

{ intro ; erewrite HV_map_map_eff ; crush. }
{ intro ; erewrite HV_map_map_eff ; crush. }
{ intro p ; destruct p as [ | p ] ; unfold compose ; simpl.
  - match goal with [ |- ?g VZ = ?h ] =>
      replace g with (λ (p : inc ∅), h)
    end ; reflexivity.
  - erewrite HV_bind_map_hd, HV_bind_hd_id, HV_map_hd_id ; crush.
}
{ intro p ; destruct p as [ | p ] ; unfold compose ; simpl.
  - match goal with [ |- ?g VZ = ?h ] =>
      replace g with (λ (p : inc ∅), h)
    end ; reflexivity.
  - erewrite HV_bind_map_hd, HV_bind_hd_id, HV_map_hd_id ; crush.
}
{ intro p ; destruct p ; simpl ; [ | crush ].
  erewrite V_bind_map_tm , V_bind_tm_id, V_map_tm_id ; crush.
}
{ intro x ; unfold compose ; simpl.
  erewrite HV_bind_map_val, HV_bind_val_id, HV_map_val_id ; crush.
}
{ intro p ; destruct p ; simpl ; [ | crush ].
  erewrite V_bind_map_tm , V_bind_tm_id, V_map_tm_id ; crush.
}
{ intro x ; unfold compose ; simpl.
  erewrite HV_bind_map_val, HV_bind_val_id, HV_map_val_id ; crush.
}
Qed.

End section_compat_val_hfun.
