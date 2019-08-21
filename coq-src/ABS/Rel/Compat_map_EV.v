Require Import Rel.Definitions.
Require Import Lang.BindingsFacts.
Require Import Wf_natnat.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Section section_EV_map_aux.

Hint Extern 1 => match goal with
| [ x : ?V |- ∃ _ : ?V, _ ] => exists x ; crush
end.

Hint Extern 0 => match goal with
| [ |- ?n ⊨ ?X ⇔ ?X ] => apply auto_contr_id
| [ |- ?n ⊨ ?X ≈ᵢ ?X ] => repeat iintro ; apply auto_contr_id
| [ |- Acc lt' (_, _) ] => try lt'_solve
end.

Fixpoint
  EV_map_𝓥_aux
  n EV EV' HV
  (Ξ : XEnv EV HV)
  (f : EV → EV')
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig)
  (Hδ₁ : ∀ α : EV, δ₁ α = δ₁' (f α))
  (Hδ₂ : ∀ α : EV, δ₂ α = δ₂' (f α))
  (Hδ : n ⊨ ∀ᵢ α : EV, δ α ≈ᵢ δ' (f α))
  (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig)
  (ξ₁ ξ₂ : list var)
  (v₁ v₂ : val0) (T : ty EV HV ∅)
  (W : Acc lt' (n, size_ty T))
  {struct W} :
  (n ⊨
    𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
    𝓥⟦ (EV_map_XEnv f Ξ) ⊢ EV_map_ty f T ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂)
with
  EV_map_𝓾_aux
  n EV EV' HV
  (Ξ : XEnv EV HV)
  (f : EV → EV')
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig)
  (Hδ₁ : ∀ α : EV, δ₁ α = δ₁' (f α))
  (Hδ₂ : ∀ α : EV, δ₂ α = δ₂' (f α))
  (Hδ : n ⊨ ∀ᵢ α : EV, δ α ≈ᵢ δ' (f α))
  (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig)
  (ξ₁ ξ₂ : list var)
  (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) l₁ l₂ (ε : ef EV HV ∅)
  (W : Acc lt' (n, 0))
  {struct W} :
  (n ⊨
    𝓾⟦ Ξ ⊢ ε ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓾⟦ (EV_map_XEnv f Ξ) ⊢ EV_map_ef f ε ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂)
with
  EV_map_𝓤_aux
  n EV EV' HV
  (Ξ : XEnv EV HV)
  (f : EV → EV')
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig)
  (Hδ₁ : ∀ α : EV, δ₁ α = δ₁' (f α))
  (Hδ₂ : ∀ α : EV, δ₂ α = δ₂' (f α))
  (Hδ : n ⊨ ∀ᵢ α : EV, δ α ≈ᵢ δ' (f α))
  (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig)
  (ξ₁ ξ₂ : list var)
  (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) l₁ l₂ (𝓔 : eff EV HV ∅)
  (W : Acc lt' (n, size_eff 𝓔))
  {struct W} :
  (n ⊨
    𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓤⟦ (EV_map_XEnv f Ξ) ⊢ EV_map_eff f 𝓔 ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂)
.

Proof.
{
destruct T eqn:HT.
+ crush.
+ simpl 𝓥_Fun ; auto_contr.
  - apply EV_map_𝓥_aux ; auto.
  - apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; auto.
+ simpl 𝓥_Fun ; auto_contr.
  replace (EV_shift_XEnv (EV_map_XEnv f Ξ))
    with (EV_map_XEnv (map_inc f) (EV_shift_XEnv Ξ))
    by (repeat erewrite EV_map_map_XEnv ; crush).
  apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; [ |auto].
  repeat iintro ; apply EV_map_𝓥_aux ; [auto|auto| |auto].
  iintro α ; destruct α ; simpl ; repeat iintro ; [auto|].
  iespecialize Hδ ; apply Hδ.
+ simpl 𝓥_Fun ; auto_contr.
  replace (HV_shift_XEnv (EV_map_XEnv f Ξ))
    with (EV_map_XEnv f (HV_shift_XEnv Ξ))
    by (erewrite EV_HV_map_XEnv ; crush).
  apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; auto.
}

{
destruct ε as [ α | [ p | [ | X ] ] ] ; simpl.
+ iespecialize Hδ ; apply Hδ.
+ auto_contr.
+ auto.
+ auto_contr.
  isplit ; iintro' H.
  - idestruct H as T H ; idestruct H as 𝓔 H ; idestruct H as HX H.
    ielim_prop HX ; eapply binds_EV_map in HX.
    repeat ieexists ; repeat isplit ; [ eauto | ].
    later_shift.
    erewrite <- I_iff_elim_M ; [ apply H | ].
    apply 𝓗_Fun'_nonexpansive ; repeat iintro ; [auto| ].
    apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro.
    { erewrite <- 𝓥_roll_unroll_iff ; auto. }
    { erewrite <- 𝓤_roll_unroll_iff ; auto. }
  - idestruct H as T' H ; idestruct H as 𝓔' H ; idestruct H as HX H.
    ielim_prop HX ; apply binds_EV_map_inv in HX.
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
destruct 𝓔 ; simpl.
+ auto.
+ auto_contr ; auto.
}

Qed.

End section_EV_map_aux.


Section section_EV_map.
Context (n : nat).
Context (EV EV' HV : Set).
Context (Ξ : XEnv EV HV).
Context (f : EV → EV').
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig).
Context (Hδ₁ : ∀ α : EV, δ₁ α = δ₁' (f α)).
Context (Hδ₂ : ∀ α : EV, δ₂ α = δ₂' (f α)).
Context (Hδ : n ⊨ ∀ᵢ α : EV, δ α ≈ᵢ δ' (f α)).
Context (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig).

Hint Resolve lt'_wf.

Lemma EV_map_𝓥 T ξ₁ ξ₂ v₁ v₂ :
n ⊨
  𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
  𝓥⟦ (EV_map_XEnv f Ξ) ⊢ EV_map_ty f T ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂.
Proof.
apply EV_map_𝓥_aux ; auto.
Qed.

Lemma EV_map_𝓤 𝓔 ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ :
n ⊨
  𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ ⇔
  𝓤⟦ (EV_map_XEnv f Ξ) ⊢ EV_map_eff f 𝓔 ⟧ δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂.
Proof.
apply EV_map_𝓤_aux ; auto.
Qed.

Hint Resolve EV_map_𝓥 EV_map_𝓤.

Lemma EV_map_𝓣 T 𝓔 ξ₁ ξ₂ t₁ t₂ :
n ⊨
  𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
  𝓣⟦ (EV_map_XEnv f Ξ) ⊢ (EV_map_ty f T) # (EV_map_eff f 𝓔) ⟧
  δ₁' δ₂' δ' ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂.
Proof.
apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; auto.
Qed.

End section_EV_map.
