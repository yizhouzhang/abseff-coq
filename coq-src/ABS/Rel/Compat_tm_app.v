Require Import Rel.Definitions.
Require Import Rel.BasicFacts.
Require Import Util.Subset.
Require Import Lang.Static.
Require Import Lang.StaticFacts.
Set Implicit Arguments.

Section section_compat_tm_app.

Context (EV HV V : Set).
Context (Ξ : XEnv EV HV).
Context (Γ : V → ty EV HV ∅).
Context (P : HV → F).
Context (S T : ty EV HV ∅).
Context (𝓔 : eff EV HV ∅).
Context (t₁ t₂ : tm EV HV V ∅).
Context (s₁ s₂ : tm EV HV V ∅).

Hint Resolve subset_trans postfix_refl postfix_is_subset.

Lemma compat_tm_app n :
n ⊨ ⟦ Ξ P Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : (ty_fun S T 𝓔) # 𝓔 ⟧ →
n ⊨ ⟦ Ξ P Γ ⊢ s₁ ≼ˡᵒᵍ s₂ : S # 𝓔 ⟧ →
n ⊨ ⟦ Ξ P Γ ⊢ (tm_app t₁ s₁) ≼ˡᵒᵍ (tm_app t₂ s₂) : T # 𝓔 ⟧.
Proof.
intros Ht Hs.
iintro ξ₁ ; iintro ξ₂ ; iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ; iintro γ₁ ; iintro γ₂.
iintro Hξ ; iintro cl_δ ; iintro cl_ρ₁ρ₂ ; iintro Hρ ; iintro Hγ.

iespecialize Ht.
repeat (ispecialize Ht ; [ eassumption | ]).
simpl.
generalize Ht.
generalize (subst_tm δ₁ ρ₁ γ₁ t₁), (subst_tm δ₂ ρ₂ γ₂ t₂).
clear Ht t₁ t₂ ; intros t₁ t₂ Ht.
bind_app1.
eapply plug0 with (ξ₁ := ξ₁) (ξ₂ := ξ₂) ; [crush|crush| |auto|auto|exact Ht].
iintro ξ₁' ; iintro ξ₂' ; iintro v₁ ; iintro v₂ ;
iintro Hξ₁' ; iintro Hξ₂' ; iintro Hv.
ielim_prop Hξ₁' ; ielim_prop Hξ₂'.

ispecialize Hs ξ₁' ; ispecialize Hs ξ₂' ;
ispecialize Hs δ₁ ; ispecialize Hs δ₂ ; ispecialize Hs δ ;
ispecialize Hs ρ₁ ; ispecialize Hs ρ₂ ; ispecialize Hs ρ ;
ispecialize Hs γ₁ ; ispecialize Hs γ₂.
ielim_prop Hξ ; destruct Hξ as [Hξ₁ Hξ₂].
ielim_prop cl_ρ₁ρ₂.
ispecialize Hs.
{ clear - Hξ₁ Hξ₂ Hξ₁' Hξ₂'.
  iintro_prop ; split ; eauto.
}
ispecialize Hs.
{ clear - cl_δ Hξ₁' Hξ₂'.
  eapply closed_δ_monotone ; eauto.
}
ispecialize Hs.
{ clear - cl_ρ₁ρ₂ Hξ₁' Hξ₂'.
  iintro_prop ; eapply closed_ρ_monotone ; eauto.
}
ispecialize Hs.
{ clear - Hρ Hξ₁' Hξ₂'.
  eapply 𝑷_monotone ; eauto.
}
ispecialize Hs.
{ clear - Hγ Hξ₁' Hξ₂'.
  eapply 𝜞_monotone ; eauto.
}
simpl.
generalize Hs.
generalize (subst_tm δ₁ ρ₁ γ₁ s₁), (subst_tm δ₂ ρ₂ γ₂ s₂).
clear Hs s₁ s₂.
intros s₁ s₂ Hs.
bind_app2.
eapply plug0 with (ξ₁ := ξ₁') (ξ₂ := ξ₂') ; [crush|crush| |auto|auto|exact Hs].
iintro ξ₁'' ; iintro ξ₂'' ; iintro u₁ ; iintro u₂ ;
iintro Hξ₁'' ; iintro Hξ₂'' ; iintro Hu.
ielim_prop Hξ₁'' ; ielim_prop Hξ₂''.

clear - Hv Hu Hξ₁' Hξ₂' Hξ₁'' Hξ₂''.
simpl in Hv |- *.
ispecialize Hv ξ₁'' ; ispecialize Hv ξ₂''.
repeat (ispecialize Hv ; [ eauto | ]).
iespecialize Hv.
ispecialize Hv ; [ eassumption | ].
exact Hv.

Qed.

End section_compat_tm_app.
