Require Import Rel.Definitions.
Require Import Rel.BasicFacts.
Require Import Rel.Compat_sub.
Require Import Rel.Compat_map.
Require Import Util.Subset.
Require Import Lang.Static.
Require Import Lang.BindingsFacts.
Require Import Lang.StaticFacts.
Set Implicit Arguments.

Section section_compat_val_up.

Context (EV HV V : Set).
Context (Ξ : XEnv EV HV).
Context (P : HV → F).
Context (Γ : V → ty EV HV ∅).
Context (𝔽 : F).
Context (h₁ h₂ : hd EV HV V ∅).
Context (ℓ : lbl HV ∅).
Context (H_lbl₁ : lbl_hd h₁ = ℓ).
Context (H_lbl₂ : lbl_hd h₂ = ℓ).
Context (𝓔 : eff EV HV ∅).
Context (H𝓔 : 𝓔 = [ef_lbl ℓ]).
Context (Wf_Ξ : wf_XEnv Ξ).
Hint Resolve st_reflexive.

Lemma compat_val_up n :
n ⊨ ⟦ Ξ P Γ ⊢ h₁ ≼ˡᵒᵍₕ h₂ : 𝔽 # ℓ ⟧ →
n ⊨ ⟦ Ξ P Γ ⊢ (⇧ h₁) ≼ˡᵒᵍᵥ (⇧ h₂) :
      ty_fun
      (HV_open_ty (EV_open_ty (fst (Σ 𝔽))))
      (HV_open_ty (EV_open_ty (snd (Σ 𝔽))))
      𝓔 ⟧.
Proof.
specialize (Wf_Σ 𝔽) as Wf_Σ.
intro Hh.
iintro ξ₁ ; iintro ξ₂ ; iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ; iintro γ₁ ; iintro γ₂.
iintro Hξ ; iintro cl_δ ; iintro cl_ρ₁ρ₂ ; iintro Hρ ; iintro Hγ.
simpl.
iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
iintro v₁ ; iintro v₂ ; iintro Hv.

iespecialize Hh.
repeat (ispecialize Hh ; [ eassumption | ]).

bind_hole.
eapply 𝓦_in_𝓣.
destruct ℓ as [ p | [ | X ] ] ; [ | auto | ] ; simpl in Hh |- *.
+ idestruct Hh as r₁ Hh ; idestruct Hh as r₂ Hh ;
  idestruct Hh as X₁ Hh ; idestruct Hh as X₂ Hh ;
  idestruct Hh as Hh₁h₂ Hh ; idestruct Hh as Hρ₁ρ₂ Hr.
  iexists (λ ξ₁'' ξ₂'' t₁ t₂,
    match t₁, t₂ with
    | tm_val v₁, tm_val v₂ =>
      ▷ 𝓥⟦ Ξ ⊢ HV_open_ty (EV_open_ty (snd (Σ 𝔽))) ⟧
        δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁'' ξ₂'' v₁ v₂
    | _, _ => (False)ᵢ
    end
  ).
  repeat ieexists ; repeat isplit.
  - subst 𝓔 ; simpl.
    ileft ; repeat ieexists ; repeat isplit.
    * eassumption.
    * auto.
    * auto 9.
    * repeat ieexists ; repeat isplit ; [ eassumption | eassumption | ].
      later_shift.
      eapply 𝓗_Fun'_monotone ; eauto.
    * clear - Hv Wf_Ξ Wf_Σ.
      iintro_later ; apply 𝓥_roll.
      erewrite I_iff_elim_M ; [ | apply closed_weaken_𝓥 ; crush ] ; eauto.
    * clear - Wf_Ξ Wf_Σ.
      iintro ξ₁ ; iintro ξ₂ ; iintro t₁ ; iintro t₂.
      isplit ; iintro H ; later_shift.
      { idestruct H as v₁ H ; idestruct H as v₂ H ; idestruct H as Ht₁t₂ Hv.
        ielim_prop Ht₁t₂ ; destruct Ht₁t₂ ; subst.
        apply 𝓥_unroll in Hv.
        erewrite <- I_iff_elim_M ; [ | apply closed_weaken_𝓥 ] ; crush.
      }
      { repeat ieexists ; isplit ; [ crush | ].
        apply 𝓥_roll.
        erewrite I_iff_elim_M ; [ | apply closed_weaken_𝓥 ; crush ] ; eauto.
      }
  - iintro_prop ; crush.
  - clear.
    iintro ξ₁'' ; iintro ξ₂'' ; iintro t₁ ; iintro t₂ ; iintro Hξ₁'' ; iintro Hξ₂''.
    iintro H ; destruct t₁, t₂ ; try icontradict H.
    later_shift.
    eapply 𝓥_in_𝓣 in H.
    apply 𝓣_roll ; exact H.

+ idestruct Hh as r₁ Hh ; idestruct Hh as r₂ Hh ; idestruct Hh as Hh₁h₂ Hh ;
  idestruct Hh as T Hh ; idestruct Hh as 𝓕 Hh ; idestruct Hh as BindsX Hr.
  iexists (λ ξ₁'' ξ₂'' t₁ t₂,
    match t₁, t₂ with
    | tm_val v₁, tm_val v₂ =>
      ▷ 𝓥⟦ Ξ ⊢ HV_open_ty (EV_open_ty (snd (Σ 𝔽))) ⟧
        δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁'' ξ₂'' v₁ v₂
    | _, _ => (False)ᵢ
    end
  ).
  repeat ieexists ; repeat isplit.
  - subst 𝓔 ; simpl.
    ileft ; repeat ieexists ; repeat isplit.
    * auto 9.
    * auto.
    * auto 9.
    * repeat ieexists ; repeat isplit ; [ eassumption | ].
      repeat ieexists ; isplit ; [ eassumption | ].
      later_shift.
      eapply 𝓗_Fun'_monotone ; eauto.
    * clear - Hv Wf_Ξ Wf_Σ.
      iintro_later ; apply 𝓥_roll.
      erewrite I_iff_elim_M ; [ | apply closed_weaken_𝓥 ; crush ] ; eauto.
    * clear - Wf_Ξ Wf_Σ.
      iintro ξ₁ ; iintro ξ₂ ; iintro t₁ ; iintro t₂.
      isplit ; iintro H ; later_shift.
      { idestruct H as v₁ H ; idestruct H as v₂ H ; idestruct H as Ht₁t₂ Hv.
        ielim_prop Ht₁t₂ ; destruct Ht₁t₂ ; subst.
        apply 𝓥_unroll in Hv.
        erewrite <- I_iff_elim_M ; [ | apply closed_weaken_𝓥 ] ; crush.
      }
      { repeat ieexists ; isplit ; [ crush | ].
        apply 𝓥_roll.
        erewrite I_iff_elim_M ; [ | apply closed_weaken_𝓥 ; crush ] ; eauto.
      }
  - iintro_prop ; crush.
  - clear.
    iintro ξ₁'' ; iintro ξ₂'' ; iintro t₁ ; iintro t₂ ; iintro Hξ₁'' ; iintro Hξ₂''.
    iintro H ; destruct t₁, t₂ ; try icontradict H.
    later_shift.
    eapply 𝓥_in_𝓣 in H.
    apply 𝓣_roll ; exact H.
Qed.

End section_compat_val_up.
