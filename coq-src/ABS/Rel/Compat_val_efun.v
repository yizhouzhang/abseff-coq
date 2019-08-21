Require Import Rel.Definitions Rel.BasicFacts Rel.Compat_map_EV.
Require Import Util.Subset.
Require Import Lang.BindingsFacts.
Set Implicit Arguments.

Section section_compat_val_efun.

Context (EV HV V : Set).
Context (Ξ : XEnv EV HV).
Context (Γ : V → ty EV HV ∅).
Context (P : HV → F).
Context (T : ty (inc EV) HV ∅).
Context (t₁ t₂ : tm (inc EV) HV V ∅).

Hint Resolve subset_trans.
Hint Resolve postfix_is_subset.
Hint Extern 1 => match goal with
| [ H : postfix ?ξ ?ξ', _ : ?X ∈ from_list ?ξ |- ?X ∈ from_list ?ξ' ] =>
  apply postfix_is_subset in H
end.

Lemma compat_val_efun n :
n ⊨ ⟦ (EV_shift_XEnv Ξ) P (EV_shift_ty ∘ Γ) ⊢ t₁ ≼ˡᵒᵍ t₂ : T # [] ⟧ →
n ⊨ ⟦ Ξ P Γ ⊢ (val_efun t₁) ≼ˡᵒᵍᵥ (val_efun t₂) : (ty_efun T) ⟧.
Proof.
intro Ht.
iintro ξ₁ ; iintro ξ₂ ; iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ; iintro γ₁ ; iintro γ₂.
iintro Hξ ; iintro cl_δ ; iintro cl_ρ₁ρ₂ ; iintro Hρ ; iintro Hγ.
ielim_prop Hξ ; destruct Hξ as [Hξ₁ Hξ₂].
ielim_prop cl_ρ₁ρ₂.

simpl.
iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
iintro 𝓔₁ ; iintro 𝓔₂ ; iintro φ ; iintro cl_φ.
ispecialize Ht ξ₁' ; ispecialize Ht ξ₂'.
ispecialize Ht (env_ext δ₁ 𝓔₁) ; ispecialize Ht (env_ext δ₂ 𝓔₂) ;
ispecialize Ht (env_ext δ φ).
iespecialize Ht.

ispecialize Ht.
{ iintro_prop ; split ; rewrite EV_map_XEnv_dom ; eauto. }
ispecialize Ht.
{ iintro α ; destruct α as [ | α ] ; simpl ; [ crush | ].
  repeat iintro ; iespecialize cl_δ ; ispecialize cl_δ ; [ eassumption | ].
  ielim_prop cl_δ ; destruct cl_δ ; split ; eauto.
}
ispecialize Ht.
{ iintro_prop.
  eapply closed_ρ_monotone ; eauto.
}
ispecialize Ht.
{ eapply 𝑷_monotone ; eauto. }
ispecialize Ht.
{ iintro x ; ispecialize Hγ x.
  apply 𝓥_monotone with (ξ₁ := ξ₁) (ξ₂ := ξ₂) ; [ |auto|auto].
  erewrite <- I_iff_elim_M ; [ exact Hγ | apply EV_map_𝓥 ].
  - crush.
  - crush.
  - repeat iintro ; apply auto_contr_id.
}

clear - Ht.
change (
  λ _ _ _ _ _ _ _, (False)ᵢ
) with (
  𝓤⟦ (EV_shift_XEnv Ξ) ⊢ [] ⟧
  (env_ext δ₁ 𝓔₁) (env_ext δ₂ 𝓔₂) (env_ext δ φ) ρ₁ ρ₂ ρ
).
eapply 𝓣_step_r ; [ apply step_eapp | ].
eapply 𝓣_step_l ; [ apply step_eapp | ].
iintro_later.
repeat erewrite <- EV_V_bind_tm.
repeat erewrite EV_HV_bind_tm.
repeat erewrite EV_bind_bind_tm.
exact Ht.
{ intro α ; destruct α as [ | α ] ; unfold compose ; simpl.
  - rewrite app_nil_r.
    match goal with [ |- ?g VZ = ?𝓔 ] =>
      replace g with (λ (p : inc ∅), 𝓔)
    end ; reflexivity.
  - erewrite EV_bind_map_eff, EV_map_eff_id, EV_bind_eff_id ; crush.
}
{ intro α ; destruct α as [ | α ] ; unfold compose ; simpl.
  - rewrite app_nil_r.
    match goal with [ |- ?g VZ = ?𝓔 ] =>
      replace g with (λ (p : inc ∅), 𝓔)
    end ; reflexivity.
  - erewrite EV_bind_map_eff, EV_map_eff_id, EV_bind_eff_id ; crush.
}
{ intro p ; unfold compose ; simpl.
  erewrite EV_bind_map_hd, EV_map_hd_id, EV_bind_hd_id ; crush.
}
{ intro α ; destruct α ; unfold compose ; simpl ; [ | crush ].
  unshelve erewrite HV_bind_map_eff, HV_map_eff_id, HV_bind_eff_id ; crush.
}
{ intro p ; unfold compose ; simpl.
  erewrite EV_bind_map_hd, EV_map_hd_id, EV_bind_hd_id ; crush.
}
{ intro α ; destruct α ; unfold compose ; simpl ; [ | crush ].
  unshelve erewrite HV_bind_map_eff, HV_map_eff_id, HV_bind_eff_id ; crush.
}
{ intro x ; unfold compose ; simpl.
  erewrite EV_bind_map_val, EV_map_val_id, EV_bind_val_id ; crush.
}
{ intro x ; unfold compose ; simpl.
  erewrite EV_bind_map_val, EV_map_val_id, EV_bind_val_id ; crush.
}

Qed.

End section_compat_val_efun.
