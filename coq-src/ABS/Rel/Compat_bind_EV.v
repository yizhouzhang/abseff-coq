Require Import Rel.Definitions.
Require Import Lang.BindingsFacts.
Require Import Wf_natnat.
Require Import Compat_sub.
Require Import Compat_map_EV.
Require Import Compat_map_HV.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Section section_EV_bind_aux.

Hint Extern 1 => match goal with
| [ x : ?V |- ∃ _ : ?V, _ ] => exists x ; crush
end.

Hint Extern 0 => match goal with
| [ |- ?n ⊨ ?X ⇔ ?X ] => apply auto_contr_id
| [ |- ?n ⊨ ?X ≈ᵢ ?X ] => repeat iintro ; apply auto_contr_id
| [ |- Acc lt' (_, _) ] => try lt'_solve
| [ H : _ ⊨ (False)ᵢ |- _ ] => icontradict H
end.

Hint Resolve in_or_app.

Fixpoint
  EV_bind_𝓥_aux
  n EV EV' HV
  (Ξ : XEnv EV HV)
  (f : EV → eff EV' HV ∅)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig)
  (Hδ₁ : ∀ α, δ₁ α = subst_eff δ₁' ρ₁ (f α))
  (Hδ₂ : ∀ α, δ₂ α = subst_eff δ₂' ρ₂ (f α))
  (Hδ :
    n ⊨ ∀ᵢ α ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂,
        𝓾⟦ Ξ ⊢ ef_var α ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
        𝓤⟦ (EV_bind_XEnv f Ξ) ⊢ f α ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂
  )
  (ξ₁ ξ₂ : list var)
  (v₁ v₂ : val0) (T : ty EV HV ∅)
  (W : Acc lt' (n, size_ty T))
  {struct W} :
  (n ⊨
    𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
    𝓥⟦ (EV_bind_XEnv f Ξ) ⊢ EV_bind_ty f T ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂)
with
  EV_bind_𝓾_aux
  n EV EV' HV
  (Ξ : XEnv EV HV)
  (f : EV → eff EV' HV ∅)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig)
  (Hδ₁ : ∀ α, δ₁ α = subst_eff δ₁' ρ₁ (f α))
  (Hδ₂ : ∀ α, δ₂ α = subst_eff δ₂' ρ₂ (f α))
  (Hδ :
    n ⊨ ∀ᵢ α ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂,
        𝓾⟦ Ξ ⊢ ef_var α ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
        𝓤⟦ (EV_bind_XEnv f Ξ) ⊢ f α ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂
  )
  (ξ₁ ξ₂ : list var)
  (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) l₁ l₂ (ε : ef EV HV ∅)
  (W : Acc lt' (n, 0))
  {struct W} :
  (n ⊨
    𝓾⟦ Ξ ⊢ ε ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓤⟦ (EV_bind_XEnv f Ξ) ⊢ EV_bind_ef f ε ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂)
with
  EV_bind_𝓤_aux
  n EV EV' HV
  (Ξ : XEnv EV HV)
  (f : EV → eff EV' HV ∅)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig)
  (Hδ₁ : ∀ α, δ₁ α = subst_eff δ₁' ρ₁ (f α))
  (Hδ₂ : ∀ α, δ₂ α = subst_eff δ₂' ρ₂ (f α))
  (Hδ :
    n ⊨ ∀ᵢ α ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂,
        𝓾⟦ Ξ ⊢ ef_var α ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
        𝓤⟦ (EV_bind_XEnv f Ξ) ⊢ f α ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂
  )
  (ξ₁ ξ₂ : list var)
  (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) l₁ l₂ (𝓔 : eff EV HV ∅)
  (W : Acc lt' (n, size_eff 𝓔))
  {struct W} :
  (n ⊨
    𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓤⟦ (EV_bind_XEnv f Ξ) ⊢ EV_bind_eff f 𝓔 ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂)
.

Proof.
{
destruct T eqn:HT.
+ crush.
+ simpl 𝓥_Fun ; auto_contr.
  - apply EV_bind_𝓥_aux ; auto.
  - apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; auto.
+ simpl 𝓥_Fun ; auto_contr.
  replace (EV_shift_XEnv (EV_bind_XEnv f Ξ))
    with (EV_bind_XEnv (EV_lift_inc f) (EV_shift_XEnv Ξ))
    by (erewrite EV_bind_map_XEnv ; crush).
  apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; [ |auto].
  apply EV_bind_𝓥_aux ; [ | | |auto].
  * destruct α as [ | α ] ; unfold compose ; simpl.
    { rewrite app_nil_r.
      unshelve erewrite HV_bind_map_eff, HV_bind_eff_id, HV_map_eff_id ; crush. }
    { rewrite Hδ₁ ; clear.
      erewrite EV_bind_map_eff, EV_map_eff_id ; try reflexivity.
      intro ; unfold compose ; simpl.
      erewrite EV_HV_map_eff, EV_map_eff_id ; crush.
    }
  * destruct α as [ | α ] ; unfold compose ; simpl.
    { rewrite app_nil_r.
      unshelve erewrite HV_bind_map_eff, HV_bind_eff_id, HV_map_eff_id ; crush. }
    { rewrite Hδ₂ ; clear.
      erewrite EV_bind_map_eff, EV_map_eff_id ; try reflexivity.
      intro ; unfold compose ; simpl.
      erewrite EV_HV_map_eff, EV_map_eff_id ; crush.
    }
  * iintro α ; repeat iintro.
    destruct α as [ | α ] ; simpl ; [ clear | clear - Hδ ].
    { isplit ; iintro' H ; [ ileft ; apply H | ].
      idestruct H as H H ; [ apply H | auto ].
    }
    { iespecialize Hδ.
      eapply I_iff_transitive ; [ apply Hδ | ].
      replace (EV_bind_XEnv (EV_lift_inc f) (EV_shift_XEnv Ξ))
       with (EV_shift_XEnv (EV_bind_XEnv f Ξ))
       by (erewrite EV_bind_map_XEnv ; crush).
      apply EV_map_𝓤 ; [auto|auto| ].
      repeat iintro ; simpl ; apply auto_contr_id.
    }
+ simpl 𝓥_Fun ; auto_contr.
  replace (HV_shift_XEnv (EV_bind_XEnv f Ξ))
    with (EV_bind_XEnv (HV_shift_eff ∘ f) (HV_shift_XEnv Ξ))
    by (erewrite EV_bind_HV_map_XEnv ; crush).
  apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; [ |auto].
  apply EV_bind_𝓥_aux ; [clear-Hδ₁|clear-Hδ₂|clear-Hδ|auto].
  * intro ; unfold compose ; rewrite Hδ₁.
    erewrite EV_bind_HV_map_eff, HV_bind_map_eff, HV_map_eff_id ; try reflexivity.
    { intro ; simpl.
      erewrite HV_map_lbl_id ; crush. }
    { intro ; unfold compose.
      erewrite HV_map_map_eff ; crush. }
  * intro ; unfold compose ; rewrite Hδ₂.
    erewrite EV_bind_HV_map_eff, HV_bind_map_eff, HV_map_eff_id ; try reflexivity.
    { intro ; simpl.
      erewrite HV_map_lbl_id ; crush. }
    { intro ; unfold compose.
      erewrite HV_map_map_eff ; crush. }
  * repeat iintro ; simpl.
    iespecialize Hδ.
    eapply I_iff_transitive ; [ apply Hδ | ].
    replace (EV_bind_XEnv (HV_shift_eff ∘ f) (HV_shift_XEnv Ξ))
      with (HV_shift_XEnv (EV_bind_XEnv f Ξ))
      by (erewrite EV_bind_HV_map_XEnv ; crush).
    apply HV_map_𝓤 ; [auto|auto| ].
    repeat iintro ; simpl ; apply auto_contr_id.
}

{
destruct ε as [ α | [ p | [ | X ] ] ] ; simpl.
+ iespecialize Hδ ; apply Hδ.
+ isplit ; iintro' H ; [ ileft ; apply H | ].
  idestruct H as H H ; [ apply H | auto ].
+ auto.
+ match goal with
  | [ |- n ⊨ ?P ⇔ ?Q ∨ᵢ (False)ᵢ ] =>
    cut (n ⊨ P ⇔ Q)
  end.
  { clear ; intro H.
    isplit ; iintro' H' ; [ ileft | idestruct H' as H' H' ; [ | auto ] ].
    + erewrite <- I_iff_elim_M ; eassumption.
    + erewrite I_iff_elim_M ; eassumption.
  }
  auto_contr.
  isplit ; iintro' H.
  - idestruct H as T H ; idestruct H as 𝓔 H ; idestruct H as HX H.
    ielim_prop HX ; eapply binds_EV_bind in HX.
    repeat ieexists ; repeat isplit ; [ eauto | ].
    later_shift.
    erewrite <- I_iff_elim_M ; [ apply H | ].
    apply 𝓗_Fun'_nonexpansive ; repeat iintro ; [auto| ].
    apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro.
    { erewrite <- 𝓥_roll_unroll_iff ; auto. }
    { erewrite <- 𝓤_roll_unroll_iff ; auto. }
  - idestruct H as T' H ; idestruct H as 𝓔' H ; idestruct H as HX H.
    ielim_prop HX ; apply binds_EV_bind_inv in HX.
    destruct HX as [ T [ 𝓔 [ HT [ H𝓔 HX ] ] ] ] ; subst.
    repeat ieexists ; repeat isplit ; [ eauto | ].
    later_shift.
    erewrite I_iff_elim_M ; [ apply H | ].
    apply 𝓗_Fun'_nonexpansive ; repeat iintro ; [auto|].
    apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro.
    { erewrite <- 𝓥_roll_unroll_iff ; auto. }
    { erewrite <- 𝓤_roll_unroll_iff ; auto. }
}

{
destruct 𝓔 as [ | ε 𝓔 ] ; simpl ; [ auto | ].
isplit ; iintro' H.
+ idestruct H as H H.
  - eapply ccompat_se with (𝓔 := EV_bind_ef f ε).
    * crush.
    * erewrite <- I_iff_elim_M ; [ apply H | ].
      apply EV_bind_𝓾_aux ; auto.
  - apply ccompat_se with (𝓔 := EV_bind_eff f 𝓔).
    * crush.
    * erewrite <- I_iff_elim_M ; [ apply H | ].
      apply EV_bind_𝓤_aux ; auto.
+ apply ccompat_eff_In_inverse in H.
  destruct H as [ε' [Hε' H]].
  apply in_app_or in Hε'.
  destruct Hε' as [Hε' | Hε'] ; [ ileft | iright ].
  - eapply ccompat_eff_In in Hε' ; [ clear H | apply H ].
    erewrite I_iff_elim_M ; [ apply Hε' | ].
    apply EV_bind_𝓾_aux ; auto.
  - eapply ccompat_eff_In in Hε' ; [ clear H | apply H ].
    erewrite I_iff_elim_M ; [ apply Hε' | ].
    apply EV_bind_𝓤_aux ; auto.
}
Qed.

End section_EV_bind_aux.


Section section_EV_bind.
Context (n : nat).
Context (EV EV' HV : Set).
Context (Ξ : XEnv EV HV).
Context (f : EV → eff EV' HV ∅).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig).
Context (Hδ₁ : ∀ α, δ₁ α = subst_eff δ₁' ρ₁ (f α)).
Context (Hδ₂ : ∀ α, δ₂ α = subst_eff δ₂' ρ₂ (f α)).
Context (Hδ :
  n ⊨ ∀ᵢ α ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂,
      𝓾⟦ Ξ ⊢ ef_var α ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
      𝓤⟦ (EV_bind_XEnv f Ξ) ⊢ f α ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂
).

Hint Resolve lt'_wf.

Lemma EV_bind_𝓥 T ξ₁ ξ₂ v₁ v₂ :
n ⊨
  𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
  𝓥⟦ (EV_bind_XEnv f Ξ) ⊢ EV_bind_ty f T ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂.
Proof.
apply EV_bind_𝓥_aux ; auto.
Qed.

Lemma EV_bind_𝓤 𝓔 ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ :
n ⊨
  𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ ⇔
  𝓤⟦ (EV_bind_XEnv f Ξ) ⊢ EV_bind_eff f 𝓔 ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂.
Proof.
apply EV_bind_𝓤_aux ; auto.
Qed.

Hint Resolve EV_bind_𝓥 EV_bind_𝓤.

Lemma EV_bind_𝓣 T 𝓔 ξ₁ ξ₂ t₁ t₂ :
n ⊨
  𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
  𝓣⟦ (EV_bind_XEnv f Ξ) ⊢ (EV_bind_ty f T) # (EV_bind_eff f 𝓔) ⟧
  δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂.
Proof.
apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; auto.
Qed.

End section_EV_bind.
