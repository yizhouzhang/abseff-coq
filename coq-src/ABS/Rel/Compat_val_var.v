Require Import Rel.Definitions.
Require Import Lang.BindingsFacts.

Section section_compat_val_var.

Context (EV HV V : Set).
Context (Ξ : XEnv EV HV).
Context (P : HV → F).
Context (Γ : V → ty EV HV ∅).
Context (x : V).

Lemma compat_val_var n :
n ⊨ ⟦ Ξ P Γ ⊢ (val_var x) ≼ˡᵒᵍᵥ (val_var x) : (Γ x) ⟧.
Proof.
iintro ξ₁ ; iintro ξ₂ ; iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ; iintro γ₁ ; iintro γ₂.
iintro Hξ ; iintro cl_δ ; iintro cl_ρ₁ρ₂ ; iintro Hρ ; iintro Hγ.

ispecialize Hγ x.
repeat erewrite V_bind_map_hd, V_bind_hd_id, V_map_hd_id ; crush.
Qed.

End section_compat_val_var.