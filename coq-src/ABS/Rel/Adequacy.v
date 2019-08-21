Require Import ABS.Rel.Definitions.
Require Import ABS.Lang.BindingsFacts.
Require Import ABS.Lang.OperationalFacts.
Require Import ABS.Lang.Sim.
Require Import ABS.Lang.SimFacts.

Section section_𝓞_is_adequate.

Lemma 𝓞_left_is_not_stuck n :
∀ ξ₁ ξ₂ t₁ t₂,
n ⊨ 𝓞 ξ₁ ξ₂ t₁ t₂ →
(∃ v₁ : val0, t₁ = v₁) ∨
(∃ ξ₁' t₁', step ⟨ξ₁, t₁⟩ ⟨ξ₁', t₁'⟩).
Proof.
induction n ; intros ξ₁ ξ₂ t₁ t₂ Ot.
+ apply 𝓞_unroll in Ot.
  idestruct Ot as Ot Ot.
  - ielim_prop Ot.
    destruct Ot as [ [? ?] [? [? ?]] ].
    left ; eexists ; eassumption.
  - idestruct Ot as ξ₁' Ot ; idestruct Ot as t₁' Ot ;
    idestruct Ot as St₁ Ot_later.
    ielim_prop St₁.
    right ; repeat eexists ; eassumption.
+ eapply (IHn _ _ _ t₂) ; clear IHn.
  apply 𝓞_roll.
  apply 𝓞_unroll in Ot.
  idestruct Ot as Ot Ot.
  - ielim_prop Ot.
    destruct Ot as [ [v₁ ?] [ξ₂' [v₂ ?]] ] ; subst.
    ileft.
    iintro_prop.
    split ; repeat eexists ; eauto.
  - idestruct Ot as ξ₁' Ot ; idestruct Ot as t₁' Ot ;
    idestruct Ot as St₁ Ot_later.
    ielim_prop St₁.
    apply I_valid_elim in Ot_later ; simpl in Ot_later.
    iright.
    repeat ieexists ; isplit.
    * iintro_prop ; eassumption.
    * iintro_later ; assumption.
Qed.

Lemma sim_preserves_𝓞_l_aux n ξ' t' :
n ⊨ ∀ᵢ ξ₁ ξ₂ t₁ t₂,
(LibList.noduplicates ξ₁)ᵢ ⇒ (LibList.noduplicates ξ₂)ᵢ ⇒
(tm_sim ξ₁ ξ₂ t₁ t₂)ᵢ ⇒ 𝓞 ξ₁ ξ' t₁ t' ⇒ 𝓞 ξ₂ ξ' t₂ t'.
Proof.
loeb_induction.
iintro ξ₁ ; iintro ξ₂ ; iintro t₁ ; iintro t₂.
iintro NoDup_ξ₁ ; iintro NoDup_ξ₂.
iintro Sim ; iintro Obs.
ielim_prop Sim.
apply 𝓞_unroll in Obs ; apply 𝓞_roll.
idestruct Obs as Obs Obs.
+ ileft.
  ielim_prop Obs.
  destruct Obs as [[v₁ ?] [ξ'next [v₂ ?]]] ; subst t₁.
  inversion Sim ; subst ; clear Sim.
  iintro_prop ; eauto.
+ iright.
  idestruct Obs as ξ₁next Obs ; idestruct Obs as t₁next Obs ;
  idestruct Obs as Step₁ Obs.
  ielim_prop Step₁.
  eapply sim_preserves_step in Sim as Step₂ ; eauto.
  destruct Step₂ as [ξ₂next [t₂next Step₂]].
  eapply step_preserves_sim in Step₂ as H ; [
    | exact Step₁ | reflexivity | reflexivity | auto | auto | exact Sim
  ].
  destruct H as [? _].
  repeat ieexists ; isplit.
  - eauto.
  - later_shift.
    ispecialize LöbIH ξ₁next ; ispecialize LöbIH ξ₂next ;
    ispecialize LöbIH t₁next ; ispecialize LöbIH t₂next.
    ispecialize LöbIH ; [ eauto using step_preserves_noduplicates | ].
    ispecialize LöbIH ; [ eauto using step_preserves_noduplicates | ].
    ispecialize LöbIH ; [ eauto | ].
    ispecialize LöbIH ; [ apply Obs | apply LöbIH ].
Qed.

Lemma sim_preserves_𝓞_l n ξ' t' ξ₁ ξ₂ t₁ t₂ :
LibList.noduplicates ξ₁ → LibList.noduplicates ξ₂ → tm_sim ξ₁ ξ₂ t₁ t₂ →
n ⊨ 𝓞 ξ₁ ξ' t₁ t' →
n ⊨ 𝓞 ξ₂ ξ' t₂ t'.
Proof.
specialize (sim_preserves_𝓞_l_aux n ξ' t') as H.
ispecialize H ξ₁ ; ispecialize H ξ₂ ; ispecialize H t₁ ; ispecialize H t₂.
intros.
repeat (ispecialize H ; [ eauto | ]).
assumption.
Qed.

Lemma 𝓞_left_is_sound n cfg cfg' :
  step_n n cfg cfg' →
  ∀ ξ ξ' t t',
  cfg = ⟨ξ, t⟩ →
  cfg' = ⟨ξ', t'⟩ →
  LibList.noduplicates ξ →
  Xs_tm t \c from_list ξ →
  ∀ ζ s,
  n ⊨ 𝓞 ξ ζ t s →
  (∃ v : val0, t' = v) ∨
  (∃ ξ'' t'', step ⟨ξ', t'⟩ ⟨ξ'', t''⟩).
Proof.
induction 1 as [ | n cfg [ξ'' t''] cfg' t_steps t''_steps IH ] ;
intros ξ ξ' t t' Eq_cfg Eq_cfg' NoDupξ Xst ζ s Obs.
+ rewrite Eq_cfg' in Eq_cfg ; inversion Eq_cfg ; subst ξ' t'.
  clear - Obs ; apply 𝓞_unroll in Obs ; unfold 𝓞_Fun in Obs.
  idestruct Obs as Obs Obs.
  - ielim_prop Obs ; crush.
  - idestruct Obs as ξ' Obs ; idestruct Obs as t' Obs ;
    idestruct Obs as t_steps Obs.
    eauto.
+ subst cfg cfg'.
  apply 𝓞_unroll in Obs ; unfold 𝓞_Fun in Obs.
  idestruct Obs as Obs Obs.
  - ielim_prop Obs ; destruct Obs as [ [v ?] [ζ' [u ?]] ].
    subst t.
    inversion t_steps.
  - idestruct Obs as _ξ'' Obs ; idestruct Obs as _t'' Obs ;
    idestruct Obs as _t_steps Obs.
    ielim_prop _t_steps.
    assert (LibList.noduplicates ξ'') as NoDupξ''.
    { eapply step_preserves_noduplicates ; try apply t_steps ; eauto. }
    assert (LibList.noduplicates _ξ'') as NoDup_ξ''.
    { eapply step_preserves_noduplicates ; try apply _t_steps ; eauto. }
    eapply IH ; [
      reflexivity | reflexivity | eassumption |
      eapply (step_preserves_closedness t_steps) ; [reflexivity|reflexivity|exact Xst] |
      clear IH
    ].
    rewrite I_later_shift in Obs.
    eapply sim_preserves_𝓞_l ; [ eassumption | eassumption | | eassumption ].
    eapply step_preserves_sim in t_steps as H ; [
      idtac | exact _t_steps | reflexivity | reflexivity |
      exact NoDupξ | exact NoDupξ | apply tm_sim_refl ; apply Xst
    ].
    destruct H as [H _] ; exact H.
Qed.

Theorem 𝓞_is_adequate n :
∀ ξ₁ ξ₂ t₁ t₂,
n ⊨ 𝓞 ξ₁ ξ₂ t₁ t₂ →
LibList.noduplicates ξ₁ →
Xs_tm t₁ \c from_list ξ₁ →
∀ ξ₁' (v₁ : val0), step_n n ⟨ξ₁, t₁⟩ ⟨ξ₁', v₁⟩ →
∃ ξ₂' (v₂ : val0), step_refl_tran ⟨ξ₂, t₂⟩ ⟨ξ₂', v₂⟩.
Proof.
induction n as [|n] ; intros ? ? ? ? Obs NoDup_ξ₁ Xst ξ₁' v₁ Step_n_t₁.
+ inversion Step_n_t₁ ; subst.
  apply 𝓞_unroll in Obs.
  idestruct Obs as Obs Obs.
  - ielim_prop Obs ; crush.
  - idestruct Obs as ξ₁'' Obs ; idestruct Obs as t₁'' Obs ;
    idestruct Obs as Step_v₁ Obs.
    ielim_prop Step_v₁ ; inversion Step_v₁.
+ inversion Step_n_t₁ as [ | ? ? [ξ₁'' t₁'' ] ? Step_t₁_t₁'' Step_n_t₁'' ] ; subst.
  apply 𝓞_unroll in Obs.
  idestruct Obs as Obs Obs.
  - ielim_prop Obs ; crush.
  - idestruct Obs as ξ₁''' Obs ; idestruct Obs as t₁''' Obs ;
    idestruct Obs as Step_t₁_t₁''' Obs ; ielim_prop Step_t₁_t₁'''.
    apply I_valid_elim in Obs ; simpl in Obs.
    assert (LibList.noduplicates ξ₁'') as NoDup_ξ₁''.
    { eauto using step_preserves_noduplicates. }
    assert (LibList.noduplicates ξ₁''') as NoDup_ξ₁'''.
    { eauto using step_preserves_noduplicates. }
    eapply IHn ; [
      idtac | exact NoDup_ξ₁'' |
      eauto using (step_preserves_closedness Step_t₁_t₁'') | exact Step_n_t₁''
    ].
    eapply sim_preserves_𝓞_l ; [ eassumption | eassumption | | exact Obs ].
    eapply step_preserves_sim in Step_t₁_t₁'' as H ; [
      idtac | exact Step_t₁_t₁''' | reflexivity | reflexivity |
      exact NoDup_ξ₁ | exact NoDup_ξ₁ | auto using tm_sim_refl
    ].
    destruct H as [H _] ; exact H.
Qed.

End section_𝓞_is_adequate.

Section section_logref_is_adequate.

Hint Rewrite dom_empty.
Hint Resolve subset_empty_l.
Hint Unfold step_refl_tran.
Hint Constructors Relation_Operators.clos_refl_trans_1n.

Lemma n_adequacy Ξ ξ₁ ξ₂ (t₁ t₂ : tm0) T n :
  𝜩 Ξ ξ₁ ξ₂ →
  n ⊨ ⟦ Ξ ∅→ ∅→ ⊢ t₁ ≼ˡᵒᵍ t₂ : T # [] ⟧ →
  n ⊨ 𝓞 ξ₁ ξ₂ t₁ t₂.
Proof.
  intro HΞ.
  intro Ht.
  ispecialize Ht ξ₁ ; ispecialize Ht ξ₂.
  repeat ispecialize Ht (∅→ : ∅ → eff0).
  ispecialize Ht (∅→ : ∅ → IRel 𝓤_Sig).
  repeat ispecialize Ht (∅→ : ∅ → hd0).
  ispecialize Ht (∅→ : ∅ → IRel 𝓣_Sig).
  repeat ispecialize Ht (∅→ : ∅ → val0).
  ispecialize Ht.
  { iintro_prop ; crush. }
  ispecialize Ht.
  { iintro ; auto. }
  ispecialize Ht.
  { iintro_prop ; split ; crush. }
  ispecialize Ht.
  { iintro ; auto. }
  ispecialize Ht.
  { iintro ; auto. }
  repeat (erewrite V_bind_tm_id, HV_bind_tm_id, EV_bind_tm_id in Ht ; auto).
  repeat ispecialize Ht (ktx_hole : ktx0).
  iapply Ht.

  isplit.
  + repeat iintro ; simpl.
    apply 𝓞_roll.
    ileft.
    iintro_prop ; split ; repeat eexists ; auto.
  + iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
    iintro K₁ ; iintro K₂ ; iintro s₁ ; iintro s₂ ; iintro HKs.
    idestruct HKs as ψ HKs ; idestruct HKs as Xs₁ HKs ; idestruct HKs as Xs₂ HKs.
    idestruct HKs as HFalse HKs.
    icontradict HFalse.
Qed.

Hint Rewrite from_list_nil.

Theorem adequacy t₁ t₂ T :
⊨ ⟦ empty ∅→ ∅→ ⊢ t₁ ≼ˡᵒᵍ t₂ : T # [] ⟧ →
Xs_tm t₁ = \{} →
∀ ξ₁ (v₁ : val0), step_refl_tran ⟨[], t₁⟩ ⟨ξ₁, v₁⟩ →
∃ ξ₂ (v₂ : val0), step_refl_tran ⟨[], t₂⟩ ⟨ξ₂, v₂⟩.
Proof.
intros Ht Closed_t₁ ξ₁ v₁ Step_t₁.
apply step_refl_tran_to_step_n in Step_t₁.
destruct Step_t₁ as [n Step_t₁].
eapply 𝓞_is_adequate with (ξ₁ := []) ; [ |constructor|crush|exact Step_t₁].
specialize (Ht n).
eapply n_adequacy with (Ξ := empty) ; [split;crush|eauto].
Qed.

End section_logref_is_adequate.
