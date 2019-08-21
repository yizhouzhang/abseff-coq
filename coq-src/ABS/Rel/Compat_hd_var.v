Require Import Rel.Definitions.
Require Import Lang.BindingsFacts.

Section section_compat_hd_var.

Context (EV HV V : Set).
Context (Ξ : XEnv EV HV).
Context (P : HV → F).
Context (Γ : V → ty EV HV ∅).
Context (p : HV).

Lemma compat_hd_var n :
n ⊨ ⟦ Ξ P Γ ⊢ (hd_var p) ≼ˡᵒᵍₕ (hd_var p) : (P p) # lbl_var p ⟧.
Proof.
iintro ξ₁ ; iintro ξ₂ ; iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ; iintro γ₁ ; iintro γ₂.
iintro Hξ ; iintro cl_δ ; iintro cl_ρ₁ρ₂ ; iintro Hρ ; iintro Hγ.

ispecialize Hρ p.
idestruct Hρ as r₁ Hρ ; idestruct Hρ as r₂ Hρ ;
idestruct Hρ as X₁ Hρ ; idestruct Hρ as X₂ Hρ ; idestruct Hρ as Hρ Hr.

simpl.
repeat ieexists ; repeat isplit.
+ unfold compose.
  repeat erewrite V_bind_map_hd, V_bind_hd_id, V_map_hd_id ; crush.
  eassumption.
+ ielim_prop Hρ ; crush.
+ assumption.
Qed.

End section_compat_hd_var.