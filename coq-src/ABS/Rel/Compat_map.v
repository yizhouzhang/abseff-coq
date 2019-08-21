Require Export Rel.Compat_map_EV.
Require Export Rel.Compat_map_HV.
Require Export Rel.Compat_weaken_X.

Require Import Rel.Definitions.
Require Import Rel.Compat_weaken_X.
Require Import Rel.Compat_map_EV.
Require Import Rel.Compat_map_HV.
Require Import Util.Subset.
Require Import Lang.Static.
Require Import Lang.BindingsFacts.
Require Import Lang.StaticFacts.
Set Implicit Arguments.

Section section_closed_weaken.
Context (EV HV : Set).
Context (Ξ : XEnv EV HV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig).
Context (T : ty0).
Context (Wf_Ξ : wf_XEnv Ξ).
Context (Wf_T : wf_ty empty T).

Hint Rewrite concat_empty_l EV_map_XEnv_empty HV_map_XEnv_empty.
Hint Resolve HV_map_wf_ty EV_map_wf_ty.

Fact closed_weaken_𝓥 n ξ₁ ξ₂ t₁ t₂ :
n ⊨ 𝓥⟦ empty ⊢ T ⟧ ∅→ ∅→ ∅→ ∅→ ∅→ ∅→ ξ₁ ξ₂ t₁ t₂ ⇔
    𝓥⟦ Ξ ⊢ HV_open_ty (EV_open_ty T) ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂.
Proof.
replace Ξ with ((HV_map_XEnv ∅→ (EV_map_XEnv ∅→ empty)) & Ξ) by crush.
eapply I_iff_transitive ; [ | apply X_weaken_𝓥 ; crush ].
eapply I_iff_transitive ; [ apply EV_map_𝓥 | apply HV_map_𝓥 ] ; auto.
Qed.

End section_closed_weaken.
