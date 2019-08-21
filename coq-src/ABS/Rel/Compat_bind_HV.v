Require Import Rel.Definitions.
Require Import Lang.BindingsFacts.
Require Import Lang.Static.
Require Import Lang.StaticFacts.
Require Import Wf_natnat.
Require Import Compat_sub.
Require Import Compat_map_EV.
Require Import Compat_map_HV.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Section section_HV_bind_aux.

Hint Extern 0 => match goal with
| [ |- ?n ⊨ ?X ⇔ ?X ] => apply auto_contr_id
| [ |- ?n ⊨ ?X ≈ᵢ ?X ] => repeat iintro ; apply auto_contr_id
| [ |- Acc lt' (_, _) ] => try lt'_solve
| [ H : _ ⊨ (False)ᵢ |- _ ] => icontradict H
end.
Hint Resolve in_or_app.
Hint Resolve EV_map_wf_lbl HV_map_wf_lbl.
Hint Rewrite lbl_EV_bind_hd lbl_EV_map_hd lbl_HV_map_hd lbl_V_map_hd.

Fixpoint
  HV_bind_𝓥_aux
  n EV HV HV' V
  (Ξ : XEnv EV HV)
  (f : HV → hd EV HV' V ∅)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig)
  (ρ₁' ρ₂' : HV' → hd0) (ρ' : HV' → IRel 𝓣_Sig)
  (γ₁ γ₂ : V → val0)
  (Hρ₁ : ∀ p, lbl_hd (ρ₁ p) = lbl_hd (subst_hd δ₁ ρ₁' γ₁ (f p)))
  (Hρ₂ : ∀ p, lbl_hd (ρ₂ p) = lbl_hd (subst_hd δ₂ ρ₂' γ₂ (f p)))
  (Hρ :
    n ⊨ ∀ᵢ p ξ₁ ξ₂ t₁ t₂,
        𝓣𝓛⟦ Ξ ⊢ lbl_var p ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
        𝓣𝓛⟦ (HV_bind_XEnv f Ξ) ⊢ lbl_hd (f p) ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂
  )
  (Wf_f : ∀ p, wf_lbl (HV_bind_XEnv f Ξ) (lbl_hd (f p)))
  (ξ₁ ξ₂ : list var)
  (v₁ v₂ : val0) (T : ty EV HV ∅)
  (W : Acc lt' (n, size_ty T))
  {struct W} :
  (n ⊨
    𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
    𝓥⟦ (HV_bind_XEnv f Ξ) ⊢ HV_bind_ty f T ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ v₁ v₂)
with
  HV_bind_𝓾_aux
  n EV HV HV' V
  (Ξ : XEnv EV HV)
  (f : HV → hd EV HV' V ∅)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig)
  (ρ₁' ρ₂' : HV' → hd0) (ρ' : HV' → IRel 𝓣_Sig)
  (γ₁ γ₂ : V → val0)
  (Hρ₁ : ∀ p, lbl_hd (ρ₁ p) = lbl_hd (subst_hd δ₁ ρ₁' γ₁ (f p)))
  (Hρ₂ : ∀ p, lbl_hd (ρ₂ p) = lbl_hd (subst_hd δ₂ ρ₂' γ₂ (f p)))
  (Hρ :
    n ⊨ ∀ᵢ p ξ₁ ξ₂ t₁ t₂,
        𝓣𝓛⟦ Ξ ⊢ lbl_var p ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
        𝓣𝓛⟦ (HV_bind_XEnv f Ξ) ⊢ lbl_hd (f p) ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂
  )
  (Wf_f : ∀ p, wf_lbl (HV_bind_XEnv f Ξ) (lbl_hd (f p)))
  (ξ₁ ξ₂ : list var)
  (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) l₁ l₂ (ε : ef EV HV ∅)
  (W : Acc lt' (n, 0))
  {struct W} :
  (n ⊨
    𝓾⟦ Ξ ⊢ ε ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓾⟦ (HV_bind_XEnv f Ξ) ⊢ HV_bind_ef f ε ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂)
with
  HV_bind_𝓤_aux
  n EV HV HV' V
  (Ξ : XEnv EV HV)
  (f : HV → hd EV HV' V ∅)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig)
  (ρ₁' ρ₂' : HV' → hd0) (ρ' : HV' → IRel 𝓣_Sig)
  (γ₁ γ₂ : V → val0)
  (Hρ₁ : ∀ p, lbl_hd (ρ₁ p) = lbl_hd (subst_hd δ₁ ρ₁' γ₁ (f p)))
  (Hρ₂ : ∀ p, lbl_hd (ρ₂ p) = lbl_hd (subst_hd δ₂ ρ₂' γ₂ (f p)))
  (Hρ :
    n ⊨ ∀ᵢ p ξ₁ ξ₂ t₁ t₂,
        𝓣𝓛⟦ Ξ ⊢ lbl_var p ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
        𝓣𝓛⟦ (HV_bind_XEnv f Ξ) ⊢ lbl_hd (f p) ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂
  )
  (Wf_f : ∀ p, wf_lbl (HV_bind_XEnv f Ξ) (lbl_hd (f p)))
  (ξ₁ ξ₂ : list var)
  (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) l₁ l₂ (𝓔 : eff EV HV ∅)
  (W : Acc lt' (n, size_eff 𝓔))
  {struct W} :
  (n ⊨
    𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓤⟦ (HV_bind_XEnv f Ξ) ⊢ HV_bind_eff f 𝓔 ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂)
.

Proof.
{
destruct T eqn:HT.
+ crush.
+ simpl 𝓥_Fun ; auto_contr.
  - eapply HV_bind_𝓥_aux ; eauto.
  - apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; eauto.
+ simpl 𝓥_Fun ; auto_contr.
  replace (EV_shift_XEnv (HV_bind_XEnv f Ξ))
    with (HV_bind_XEnv (EV_shift_hd ∘ f) (EV_shift_XEnv Ξ))
    by (erewrite HV_bind_EV_map_XEnv ; crush).
  apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; [ |auto].
  eapply HV_bind_𝓥_aux ;
    [clear-Hρ₁|clear-Hρ₂|clear-Hρ|clear-Wf_f|auto].
  * intro ; rewrite Hρ₁.
    unfold compose.
    erewrite EV_bind_map_hd, EV_map_hd_id ; [crush|crush|].
    intro ; simpl ; rewrite EV_map_eff_id ; crush.
  * intro ; rewrite Hρ₂.
    unfold compose.
    erewrite EV_bind_map_hd, EV_map_hd_id ; [crush|crush|].
    intro ; simpl ; rewrite EV_map_eff_id ; crush.
  * iintro p ; iintro ξ₁ ; iintro ξ₂ ; iintro t₁ ; iintro t₂ ; simpl.
    iespecialize Hρ.
    eapply I_iff_transitive ; [ apply Hρ | ].
    replace (HV_bind_XEnv (EV_shift_hd ∘ f) (EV_shift_XEnv Ξ))
      with (EV_shift_XEnv (HV_bind_XEnv f Ξ))
      by (erewrite HV_bind_EV_map_XEnv ; crush).
    unfold compose ; rewrite lbl_EV_map_hd.
    destruct (lbl_hd (f p)) as [ | [ |X] ] ; simpl ; [auto|auto| ].
    isplit ; iintro' H.
    { destruct (get X (HV_bind_XEnv f Ξ)) as [[? ?]|] eqn:HX ; [ |auto].
      eapply binds_EV_map in HX.
      rewrite HX.
      erewrite <- I_iff_elim_M ; [apply H | ].
      apply EV_map_𝓣 ; [ auto | auto | repeat iintro ; crush].
    }
    { destruct (get X (EV_shift_XEnv (HV_bind_XEnv f Ξ))) as [[? ?]|] eqn:HX ;
      [|auto].
      eapply binds_EV_map_inv in HX.
      destruct HX as [? [? [? [? HX]]]] ; subst.
      rewrite HX.
      erewrite I_iff_elim_M ; [apply H | ].
      apply EV_map_𝓣 ; [ auto | auto | repeat iintro ; crush].
    }
  * intro ; unfold compose.
    rewrite lbl_EV_map_hd, <- HV_bind_EV_map_XEnv with (f₁ := f) ; crush.
+ simpl 𝓥_Fun ; auto_contr.
 replace (HV_shift_XEnv (HV_bind_XEnv f Ξ))
    with (HV_bind_XEnv (HV_lift_inc f) (HV_shift_XEnv Ξ))
    by (erewrite HV_bind_map_XEnv ; crush).
  apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; [ |auto].
  eapply HV_bind_𝓥_aux ;
    [clear-Hρ₁|clear-Hρ₂|clear-Hρ|clear-Wf_f|auto].
  * destruct p ; simpl ; [ crush | ].
    rewrite Hρ₁.
    unfold compose.
    erewrite EV_bind_HV_map_hd, HV_bind_map_hd, HV_map_hd_id ; [crush|crush| |].
    - intro ; simpl ; rewrite HV_map_hd_id ; crush.
    - intro ; simpl ; erewrite HV_map_map_eff ; crush.
  * destruct p ; simpl ; [ crush | ].
    rewrite Hρ₂.
    unfold compose.
    erewrite EV_bind_HV_map_hd, HV_bind_map_hd, HV_map_hd_id ; [crush|crush| |].
    - intro ; simpl ; rewrite HV_map_hd_id ; crush.
    - intro ; simpl ; erewrite HV_map_map_eff ; crush.
  * iintro p ; iintro ξ₁ ; iintro ξ₂ ; iintro t₁ ; iintro t₂.
    destruct p as [ | p ] ; simpl ; [ crush | ].
    replace (HV_bind_XEnv (HV_lift_inc f) (HV_shift_XEnv Ξ))
      with (HV_shift_XEnv (HV_bind_XEnv f Ξ))
      by (erewrite HV_bind_map_XEnv ; crush).
    rewrite lbl_HV_map_hd ; simpl.
    iespecialize Hρ ; simpl in Hρ.
    eapply I_iff_transitive ; [ apply Hρ | ].
    destruct (lbl_hd (f p)) as [ | [ |X] ] ; simpl ; [auto|auto| ].
    isplit ; iintro' H.
    { destruct (get X (HV_bind_XEnv f Ξ)) as [[? ?]|] eqn:HX ; [ |auto].
      eapply binds_HV_map in HX.
      rewrite HX.
      erewrite <- I_iff_elim_M ; [apply H | ].
      apply HV_map_𝓣 ; [auto|auto|repeat iintro ; crush].
    }
    { destruct (get X (HV_shift_XEnv (HV_bind_XEnv f Ξ))) as [[? ?]|] eqn:HX ;
      [|auto].
      eapply binds_HV_map_inv in HX.
      destruct HX as [? [? [? [? HX]]]] ; subst.
      rewrite HX.
      erewrite I_iff_elim_M ; [apply H | ].
      apply HV_map_𝓣 ; [auto|auto|repeat iintro ; crush].
    }
  * destruct p as [|p] ; simpl ; [constructor|].
    erewrite lbl_HV_map_hd, HV_bind_map_XEnv ; crush.
}

{
destruct ε as [ α | [ p | [ | X ] ] ] ; simpl.
+ auto.
+ rewrite Hρ₁, Hρ₂.
  auto_contr.
  { repeat (erewrite lbl_V_bind_hd, lbl_HV_bind_hd, lbl_EV_bind_hd) ;
    [ reflexivity | crush | crush ].
  }
  isplit ; iintro' H.
  { idestruct H as r₁ H ; idestruct H as r₂ H ;
    idestruct H as X₁ H ; idestruct H as X₂ H ;
    idestruct H as Hh₁h₂ H ; idestruct H as HX₁X₂ Hr.
    ielim_prop Hh₁h₂ ; destruct Hh₁h₂ ; subst.
    ielim_prop HX₁X₂ ; destruct HX₁X₂ as [HX₁ HX₂].
    specialize (Wf_f p) ; ispecialize Hρ p.
    destruct (lbl_hd (f p)) as [q|[|X]] eqn : Hl ; simpl ; [|auto|].
    + destruct (f p) as [p'|] ; simpl in * ; inversion Hl.
      subst q.
      unfold compose in HX₁ ;
        erewrite V_bind_map_hd, V_bind_hd_id, V_map_hd_id in HX₁ ;
        try reflexivity ; try (intro y ; destruct y).
      unfold compose in HX₂ ;
        erewrite V_bind_map_hd, V_bind_hd_id, V_map_hd_id in HX₂ ;
        try reflexivity ; try (intro y ; destruct y).
      repeat ieexists ; repeat isplit ; [crush|crush|].
      clear - Hr Hρ ; later_shift.
      erewrite <- I_iff_elim_M ; [apply Hr| ].
      apply 𝓗_Fun'_nonexpansive ; repeat iintro ; [auto|].
      iespecialize Hρ.
      apply Hρ.
    + destruct (f p) as [|𝔽 [|X'] r'] eqn:Hh ; simpl in * ; inversion Hl.
      subst X'.
      inversion HX₂ ; inversion HX₁ ; subst X₁ X₂ ; subst.
      repeat ieexists ; repeat isplit ; [crush|].
      clear - Hr Hh Hρ Wf_f.
      destruct (get X (HV_bind_XEnv f Ξ)) as [[??]|] eqn:BindsX.
      - repeat ieexists ; repeat isplit ; [ eauto | ].
        later_shift.
        erewrite <- I_iff_elim_M ; [apply Hr| ].
        apply 𝓗_Fun'_nonexpansive ; repeat iintro ; [auto|].
        iespecialize Hρ.
        eapply I_iff_transitive ; [apply Hρ|].
        apply fold_𝓥𝓤_in_𝓣.
      - exfalso.
        clear - Hh Hρ Wf_f BindsX.
        inversion Wf_f as [ ? HX | ] ; subst ; clear Wf_f.
        apply get_some in HX ; crush.
  }
  { specialize (Hρ₁ p) ; specialize (Hρ₂ p) ; ispecialize Hρ p.
    specialize (Wf_f p).
    destruct (lbl_hd (f p)) as [p'|[|X]] eqn : Hl ; simpl in H|-* ; [|auto|].
    + idestruct H as r₁ H ; idestruct H as r₂ H ;
      idestruct H as X₁ H ; idestruct H as X₂ H ;
      idestruct H as Hh₁h₂ H ; idestruct H as Hρ₁ρ₂ Hr.
      ielim_prop Hh₁h₂ ; destruct Hh₁h₂ ; subst.
      ielim_prop Hρ₁ρ₂ ; destruct Hρ₁ρ₂ as [Hρ₁p Hρ₂p].
      destruct (f p) as [q|] ; simpl in * ; inversion Hl ; subst.
      rewrite <- Hρ₁, <- Hρ₂.
      unfold compose in Hρ₁, Hρ₂.
      erewrite V_bind_map_hd, V_map_hd_id, V_bind_hd_id in Hρ₁ ;
        try reflexivity ; try (intro y ; destruct y).
      erewrite V_bind_map_hd, V_map_hd_id, V_bind_hd_id in Hρ₂ ;
        try reflexivity ; try (intro y ; destruct y).
      repeat ieexists ; repeat isplit ; [crush|crush|].
      later_shift.
      erewrite I_iff_elim_M ; [apply Hr|].
      apply 𝓗_Fun'_nonexpansive ; repeat iintro ; [auto|].
      iespecialize Hρ; apply Hρ.
    + idestruct H as r₁ H ; idestruct H as r₂ H ;
      idestruct H as Hh₁h₂ Hr.
      ielim_prop Hh₁h₂ ; destruct Hh₁h₂ ; subst.
      destruct (f p) as [|𝔽 [|X'] r'] eqn:Hh ; simpl in * ; inversion Hl.
      subst X'.
      idestruct Hr as T' Hr ; idestruct Hr as 𝓔' Hr ; idestruct Hr as BindsX Hr.
      ielim_prop BindsX.
      rewrite BindsX in Hρ.
      repeat ieexists ; repeat isplit ; [crush|crush|].
      clear - Hr Hρ.
      later_shift.
      erewrite I_iff_elim_M ; [apply Hr|].
      apply 𝓗_Fun'_nonexpansive ; repeat iintro ; [auto|].
      iespecialize Hρ.
      eapply I_iff_transitive ; [ apply Hρ | ].
      apply fold_𝓥𝓤_in_𝓣.
  }
+ auto.
+ auto_contr.
  isplit ; iintro' H.
  { idestruct H as T H ; idestruct H as 𝓔 H ; idestruct H as BindsX H.
    ielim_prop BindsX.
    eapply binds_HV_bind in BindsX.
    iexists (HV_bind_ty f T) ; iexists (HV_bind_eff f 𝓔) ; repeat isplit.
    { repeat erewrite <- subst_ty_eq, <- subst_eff_eq ;
        try eassumption ; eauto. }
    later_shift.
    erewrite <- I_iff_elim_M ; [apply H| ].
    apply 𝓗_Fun'_nonexpansive ; repeat iintro ; [auto|].
    eapply I_iff_transitive ; [ | apply fold_𝓥𝓤_in_𝓣 ].
    eapply I_iff_transitive ; [ apply I_iff_symmetric ; apply fold_𝓥𝓤_in_𝓣 | ].
    apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; eauto.
  }
  { idestruct H as T' H ; idestruct H as 𝓔' H ; idestruct H as BindsX H.
    ielim_prop BindsX.
    apply binds_HV_bind_inv in BindsX.
    destruct BindsX as [T [𝓔 [? [? BindsX]]]] ; subst.
    repeat ieexists ; repeat isplit.
    { iintro_prop ; apply BindsX. }
    later_shift.
    erewrite I_iff_elim_M ; [apply H| ].
    apply 𝓗_Fun'_nonexpansive ; repeat iintro ; [auto|].
    eapply I_iff_transitive ; [ | apply fold_𝓥𝓤_in_𝓣 ].
    eapply I_iff_transitive ; [ apply I_iff_symmetric ; apply fold_𝓥𝓤_in_𝓣 | ].
    apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; eauto.
  }
}

{ destruct 𝓔 as [ | ε 𝓔 ] ; simpl ; auto_contr ; eauto. }

Qed.

End section_HV_bind_aux.


Section section_HV_bind.
Context (n : nat).
Context (EV HV HV' V : Set).
Context (Ξ : XEnv EV HV).
Context (f : HV → hd EV HV' V ∅).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig).
Context (ρ₁' ρ₂' : HV' → hd0) (ρ' : HV' → IRel 𝓣_Sig).
Context (γ₁ γ₂ : V → val0).
Context (Hρ₁ : ∀ p, lbl_hd (ρ₁ p) = lbl_hd (subst_hd δ₁ ρ₁' γ₁ (f p))).
Context (Hρ₂ : ∀ p, lbl_hd (ρ₂ p) = lbl_hd (subst_hd δ₂ ρ₂' γ₂ (f p))).
Context (Hρ : n ⊨ ∀ᵢ p ξ₁ ξ₂ t₁ t₂,
              𝓣𝓛⟦ Ξ ⊢ lbl_var p ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
              𝓣𝓛⟦ (HV_bind_XEnv f Ξ) ⊢ lbl_hd (f p) ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂
).
Context (Wf_f : ∀ p, wf_lbl (HV_bind_XEnv f Ξ) (lbl_hd (f p))).

Hint Resolve lt'_wf.

Lemma HV_bind_𝓥 T ξ₁ ξ₂ v₁ v₂ :
n ⊨
  𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
  𝓥⟦ (HV_bind_XEnv f Ξ) ⊢ HV_bind_ty f T ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ v₁ v₂.
Proof.
eapply HV_bind_𝓥_aux ; eauto.
Qed.

Lemma HV_bind_𝓤 𝓔 ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ :
n ⊨
  𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ ⇔
  𝓤⟦ (HV_bind_XEnv f Ξ) ⊢ HV_bind_eff f 𝓔 ⟧ δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂.
Proof.
eapply HV_bind_𝓤_aux ; eauto.
Qed.

Hint Resolve HV_bind_𝓥 HV_bind_𝓤.

Lemma HV_bind_𝓣 T 𝓔 ξ₁ ξ₂ t₁ t₂ :
n ⊨
  𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
  𝓣⟦ (HV_bind_XEnv f Ξ) ⊢ (HV_bind_ty f T) # (HV_bind_eff f 𝓔) ⟧
  δ₁ δ₂ δ ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂.
Proof.
apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; auto.
Qed.

End section_HV_bind.
