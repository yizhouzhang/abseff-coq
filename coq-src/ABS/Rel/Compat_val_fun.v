Require Import Rel.Definitions Rel.BasicFacts.
Require Import Util.Subset.
Require Import Lang.BindingsFacts.
Set Implicit Arguments.

Section section_compat_val_fun.

Context (EV HV V : Set).
Context (Ξ : XEnv EV HV).
Context (Γ : V → ty EV HV ∅).
Context (P : HV → F).
Context (𝔽 : F).
Context (S T : ty EV HV ∅).
Context (𝓔 : eff EV HV ∅).
Context (t₁ t₂ : tm EV HV (inc V) ∅).

Hint Resolve subset_trans postfix_is_subset.

Lemma compat_val_fun n :
n ⊨ ⟦ Ξ P (env_ext Γ S) ⊢ t₁ ≼ˡᵒᵍ t₂ : T # 𝓔 ⟧ →
n ⊨ ⟦ Ξ P Γ ⊢ (val_fun t₁) ≼ˡᵒᵍᵥ (val_fun t₂) : ty_fun S T 𝓔 ⟧.
Proof.
intro Ht.
iintro ξ₁ ; iintro ξ₂ ; iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ; iintro γ₁ ; iintro γ₂.
iintro Hξ ; iintro cl_δ ; iintro cl_ρ₁ρ₂ ; iintro Hρ ; iintro Hγ.
ielim_prop Hξ ; destruct Hξ as [Hξ₁ Hξ₂].
ielim_prop cl_ρ₁ρ₂.

simpl.
iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
iintro u₁ ; iintro u₂ ; iintro Hu.
ielim_prop Hξ₁' ; ielim_prop Hξ₂'.

ispecialize Ht ξ₁' ; ispecialize Ht ξ₂'.
ispecialize Ht δ₁ ; ispecialize Ht δ₂ ; ispecialize Ht δ.
ispecialize Ht ρ₁ ; ispecialize Ht ρ₂ ; ispecialize Ht ρ.
ispecialize Ht (env_ext γ₁ u₁) ; ispecialize Ht (env_ext γ₂ u₂).
ispecialize Ht.
{ clear - Hξ₁ Hξ₂ Hξ₁' Hξ₂'.
  iintro_prop ; split ; eauto.
}
ispecialize Ht.
{ clear - cl_δ Hξ₁' Hξ₂'.
  repeat iintro ; iespecialize cl_δ ; ispecialize cl_δ ; [ eassumption | ].
  ielim_prop cl_δ ; destruct cl_δ ; split ; eauto.
}
ispecialize Ht.
{ clear - cl_ρ₁ρ₂ Hξ₁' Hξ₂'.
  iintro_prop ; eapply closed_ρ_monotone ; eauto.
}
ispecialize Ht.
{ clear - Hρ Hξ₁' Hξ₂'.
  eapply 𝑷_monotone ; eauto.
}
ispecialize Ht.
{ clear - Hγ Hu Hξ₁' Hξ₂'.
  iintro x ; destruct x as [ | x ] ; simpl ; [ crush | ].
  iespecialize Hγ.
  eapply 𝓥_monotone ; eassumption.
}
clear - Ht.

eapply 𝓣_step_r ; [ apply step_app | ].
eapply 𝓣_step_l ; [ apply step_app | ].
iintro_later.
repeat erewrite V_bind_bind_tm.
rewrite HV_bind_tm_eq with
  (f := V_shift_hd ∘ (V_open_hd ∘ ρ₁))
  (g := V_open_hd ∘ ρ₁).
rewrite HV_bind_tm_eq with
  (f := V_shift_hd ∘ (V_open_hd ∘ ρ₂))
  (g := V_open_hd ∘ ρ₂).
exact Ht.

{ intro ; unfold compose ; erewrite V_map_map_hd ; crush. }
{ intro ; unfold compose ; erewrite V_map_map_hd ; crush. }
{ intro x ; destruct x as [ | x ] ; simpl ; [ crush | ].
  erewrite V_bind_map_val, V_bind_val_id, V_map_val_id ; crush.
}
{ intro x ; destruct x as [ | x ] ; simpl ; [ crush | ].
  erewrite V_bind_map_val, V_bind_val_id, V_map_val_id ; crush.
}

Qed.

End section_compat_val_fun.
