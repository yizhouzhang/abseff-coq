Require Import ABS.Lang.Static.
Require Import ABS.Rel.Definitions.
Require Import ABS.Rel.Adequacy.
Require Import ABS.Rel.Parametricity.

Section section_type_safety.

Hint Rewrite from_list_nil.
Hint Resolve LibList.noduplicates_nil.

Theorem type_safety t T ξ' t' n :
  wf_tm empty ∅→ ∅→ t T [] →
  Xs_tm t = \{} →
  step_n n ⟨[], t⟩ ⟨ξ', t'⟩ →
  (∃ v : val0, t' = v) ∨ (∃ ξ'' t'', step ⟨ξ', t'⟩ ⟨ξ'', t''⟩).
Proof.
intros WF_t Closed_t StepRT.
eapply 𝓞_left_is_sound with (cfg := ⟨[], t⟩) (cfg' := ⟨ξ', t'⟩) (ζ := []) ;
try reflexivity ; try eassumption ; crush.
eapply n_adequacy.
+ split ; rewrite dom_empty ; apply subset_empty_l.
+ eapply parametricity_tm ; [ constructor | intro ; auto | eauto ].
Qed.

End section_type_safety.