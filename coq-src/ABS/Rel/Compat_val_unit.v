Require Import Rel.Definitions.

Section section_compat_val_unit.

Context (EV HV V : Set).
Context (Ξ : XEnv EV HV).
Context (P : HV → F).
Context (Γ : V → ty EV HV ∅).

Lemma compat_val_unit n :
n ⊨ ⟦ Ξ P Γ ⊢ val_unit ≼ˡᵒᵍᵥ val_unit : 𝟙 ⟧.
Proof.
repeat iintro ; crush.
Qed.

End section_compat_val_unit.
