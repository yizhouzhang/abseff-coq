Require Import Rel.Definitions.
Require Import Rel.BasicFacts.
Require Import Rel.Compat_map.
Require Import Util.Subset.
Require Import Lang.BindingsFacts.
Require Import Lang.Static.
Require Import Lang.StaticFacts.

Section section_compat_hd_def.

Hint Resolve subset_trans.
Hint Resolve postfix_is_subset.

Context (EV HV V : Set).
Context (Ξ : XEnv EV HV).
Context (Wf_Ξ : wf_XEnv Ξ).
Context (P : HV → F).
Context (Γ : V → ty EV HV ∅).
Context (𝔽 : F) (X : var).
Context (T : ty EV HV ∅) (𝓔 : eff EV HV ∅).
Context (t₁ t₂ : tm EV HV (inc (inc V)) ∅).

Lemma compat_hd_def n :
binds X (T, 𝓔) Ξ →
n ⊨ ⟦ Ξ P (
        env_ext
        (env_ext Γ (HV_open_ty (EV_open_ty (fst (Σ 𝔽)))))
        (ty_fun (HV_open_ty (EV_open_ty (snd (Σ 𝔽)))) T 𝓔)
      ) ⊢ t₁ ≼ˡᵒᵍ t₂ : T # 𝓔 ⟧ →
n ⊨ ⟦ Ξ P Γ ⊢ (hd_def 𝔽 (lid_f X) t₁) ≼ˡᵒᵍₕ (hd_def 𝔽 (lid_f X) t₂) :
      𝔽 # (lbl_id (lid_f X)) ⟧.
Proof.
specialize (Wf_Σ 𝔽) as Wf_Σ.
intros BindsX Ht.
iintro ξ₁ ; iintro ξ₂ ; iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ; iintro γ₁ ; iintro γ₂.
iintro Hξ ; iintro cl_δ ; iintro cl_ρ₁ρ₂ ; iintro Hρ ; iintro Hγ.

repeat ieexists ; repeat isplit ; [ auto | ].
repeat ieexists ; repeat isplit ; [ eauto | ].
iintro_later.
iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
iintro v₁ ; iintro v₂ ; iintro X₁ ; iintro X₂ ; iintro K₁ ; iintro K₂ ;
iintro Hv ; iintro HK.
apply 𝓥_unroll in Hv.

pose (k₁ := val_fun (⇩ X₁ (ktx_plug (V_open_ktx K₁) (val_var VZ))) : val0).
pose (k₂ := val_fun (⇩ X₂ (ktx_plug (V_open_ktx K₂) (val_var VZ))) : val0).
assert (
  n ⊨ 𝓥⟦ Ξ ⊢ ty_fun (HV_open_ty (EV_open_ty (snd (Σ 𝔽)))) T 𝓔 ⟧
      δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' k₁ k₂
) as Hk ; [ clear - HK Wf_Σ Wf_Ξ | clear HK ].
{ simpl.
  iintro ξ₁'' ; iintro ξ₂'' ; iintro Hξ₁'' ; iintro Hξ₂''.
  iintro v₁ ; iintro v₂ ; iintro Hv.
  iespecialize HK.
  repeat (ispecialize HK ; [ eassumption | ]).
  ispecialize HK.
  { apply 𝓥_roll.
    erewrite I_iff_elim_M ; [ apply Hv | ].
    apply closed_weaken_𝓥 ; crush.
  }
  eapply 𝓣_step_r ; [ apply step_app | ].
  eapply 𝓣_step_l ; [ apply step_app | ].
  later_shift.
  simpl V_subst_tm.
  repeat erewrite V_bind_ktx_plug.
  repeat unshelve erewrite V_bind_map_ktx, V_map_ktx_id, V_bind_ktx_id ;
    try (intro x ; destruct x).
  simpl V_bind_tm.
  erewrite I_iff_elim_M ; [ apply HK | ].
  apply fold_𝓥𝓤_in_𝓣.
}

ispecialize Ht ξ₁' ; ispecialize Ht ξ₂'.
ispecialize Ht δ₁ ; ispecialize Ht δ₂ ; ispecialize Ht δ.
ispecialize Ht ρ₁ ; ispecialize Ht ρ₂ ; ispecialize Ht ρ.
ispecialize Ht (env_ext (env_ext γ₁ v₁) k₁).
ispecialize Ht (env_ext (env_ext γ₂ v₂) k₂).
ispecialize Ht.
{ clear - Hξ Hξ₁' Hξ₂'.
  repeat match goal with [ H : _ ⊨ (_)ᵢ |- _ ] => ielim_prop H end.
  destruct Hξ ; iintro_prop ; split ; eauto.
}
ispecialize Ht.
{ clear - cl_δ Hξ₁' Hξ₂'.
  repeat iintro ; iespecialize cl_δ ; ispecialize cl_δ ; [ eassumption | ].
  repeat match goal with [ H : _ ⊨ (_)ᵢ |- _ ] => ielim_prop H end.
  destruct cl_δ ; split ; eauto.
}
ispecialize Ht.
{ clear - cl_ρ₁ρ₂ Hξ₁' Hξ₂'.
  iintro_prop.
  eapply closed_ρ_monotone ; eauto.
}
ispecialize Ht.
{ eapply 𝑷_monotone ; eauto. }
ispecialize Ht.
{ clear - Hγ Hξ₁' Hξ₂' Hv Hk Wf_Σ Wf_Ξ.
  iintro x.
  destruct x as [ | [ | x ] ] ; simpl env_ext.
  + apply Hk.
  + erewrite <- I_iff_elim_M ; [ | apply closed_weaken_𝓥 ] ; crush.
  + eapply 𝓥_monotone ; try iapply Hγ ; auto.
}

clear - Ht.
erewrite <- I_iff_elim_M ; [ | apply fold_𝓥𝓤_in_𝓣 ].
repeat erewrite V_bind_bind_tm.
unfold compose.
rewrite HV_bind_tm_eq with
  (f := λ x : HV, V_shift_hd (V_shift_hd (V_open_hd (ρ₁ x))))
  (g := V_open_hd ∘ ρ₁).
rewrite HV_bind_tm_eq with
  (f := λ x : HV, V_shift_hd (V_shift_hd (V_open_hd (ρ₂ x))))
  (g := V_open_hd ∘ ρ₂).
apply Ht.
{ intro ; unfold compose.
  repeat erewrite V_map_map_hd ; crush. }
{ intro ; unfold compose.
  repeat erewrite V_map_map_hd ; crush. }
{ destruct x as [ | [ | x ] ] ; simpl ; [ crush | crush | ].
  erewrite V_map_map_val, V_bind_map_val, V_map_val_id, V_bind_val_id ;
    crush.
}
{ destruct x as [ | [ | x ] ] ; simpl ; [ crush | crush | ].
  erewrite V_map_map_val, V_bind_map_val, V_map_val_id, V_bind_val_id ;
    crush.
}

Qed.

End section_compat_hd_def.
