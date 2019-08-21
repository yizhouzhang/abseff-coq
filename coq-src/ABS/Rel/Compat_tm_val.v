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
Context (T : ty EV HV ∅).
Context (𝓔 : eff EV HV ∅).
Context (v₁ v₂ : val EV HV V ∅).

Hint Resolve subset_trans subset_refl.

Lemma compat_tm_val n :
n ⊨ ⟦ Ξ P Γ ⊢ v₁ ≼ˡᵒᵍᵥ v₂ : T ⟧ →
n ⊨ ⟦ Ξ P Γ ⊢ v₁ ≼ˡᵒᵍ v₂ : T # 𝓔 ⟧.
Proof.
intro Ht.
iintro ξ₁ ; iintro ξ₂ ; iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ; iintro γ₁ ; iintro γ₂ ;
iintro Hξ ; iintro cl_δ ; iintro cl_ρ₁ρ₂ ; iintro Hρ ; iintro Hγ.
simpl.
apply 𝓥_in_𝓣.

iespecialize Ht.
repeat (ispecialize Ht ; [ eassumption | ]).
exact Ht.
Qed.

End section_compat_tm_app.