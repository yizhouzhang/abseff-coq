Require Import Rel.Definitions.
Require Import LibReflect LibList.
Require Import Util.Wf_natnat.
Require Import Lang.Static.
Require Import Lang.BindingsFacts.
Require Import Lang.StaticFacts.
Set Implicit Arguments.

Implicit Types EV HV : Set.

Section section_X_weaken_aux.

Local Hint Extern 1 => match goal with
| [ |- ?n ⊨ ?X ≈ᵢ ?X ] => repeat iintro ; apply auto_contr_id
| [ |- ?n ⊨ ?X ⇔ ?X ] => apply auto_contr_id
| [ |- Acc lt' (_, _) ] => try lt'_solve
end.

Fixpoint
  X_weaken_𝓾_aux
  (n : nat)
  (EV HV : Set)
  (Ξ Ξ' : XEnv EV HV)
  (Wf_ΞΞ' : wf_XEnv (Ξ & Ξ'))
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig)
  (ξ₁ ξ₂ : list var)
  (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) l₁ l₂ (ε : ef EV HV ∅)
  (Wf_ε : wf_ef Ξ ε)
  (W : Acc lt' (n, 0))
  {struct W} :
  (n ⊨
    𝓾⟦ Ξ ⊢ ε ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓾⟦ (Ξ & Ξ') ⊢ ε ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂)

with
  X_weaken_𝓤_aux
  (n : nat)
  (EV HV : Set)
  (Ξ Ξ' : XEnv EV HV)
  (Wf_ΞΞ' : wf_XEnv (Ξ & Ξ'))
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig)
  (ξ₁ ξ₂ : list var)
  (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) l₁ l₂ (𝓔 : eff EV HV ∅)
  (Wf_𝓔 : wf_eff Ξ 𝓔)
  (W : Acc lt' (n, size_eff 𝓔))
  {struct W} :
  (n ⊨
    𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓤⟦ (Ξ & Ξ') ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂)

with
  X_weaken_𝓥_aux
  (n : nat)
  (EV HV : Set)
  (Ξ Ξ' : XEnv EV HV)
  (Wf_ΞΞ' : wf_XEnv (Ξ & Ξ'))
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig)
  (ξ₁ ξ₂ : list var)
  (v₁ v₂ : val0) (T : ty EV HV ∅)
  (Wf_T : wf_ty Ξ T)
  (W : Acc lt' (n, size_ty T))
  {struct W} :
  (n ⊨
    𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
    𝓥⟦ (Ξ & Ξ') ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂)
.

Proof.

{
destruct ε as [ α | [ p | [ | X ] ] ] ; simpl.
+ auto_contr.
+ auto_contr.
+ auto_contr.
+ inversion Wf_ε as [ | ? [ ? HX | ] ] ; subst.
  repeat (apply auto_contr_exists ; intro).
  apply auto_contr_conj ; [ apply auto_contr_id | ].
  apply auto_contr_conj ; [ apply auto_contr_id | ].
  apply auto_contr_conj ; [ apply auto_contr_id | ].
  apply auto_contr_conj ; [ | apply auto_contr_id ].
  repeat (apply auto_contr_exists ; intro).
  apply auto_contr_conj ; [ apply auto_contr_id | ].
  repeat (apply auto_contr_exists ; intro).
  isplit ; iintro' H.
  - idestruct H as BindsX H ; isplit.
    * clear - BindsX HX Wf_ΞΞ'.
      iintro_prop ; ielim_prop BindsX.
      apply binds_concat_left ; [ apply BindsX | ].
      clear - Wf_ΞΞ' HX.
      apply wf_XEnv_ok in Wf_ΞΞ'.
      eapply ok_concat_indom_l ; eauto.
    * later_shift.
      ielim_prop BindsX.
      apply wf_XEnv_concat_inv_l in Wf_ΞΞ' as Wf_Ξ.
      specialize (binds_wf Wf_Ξ BindsX) as Wf_T𝓔.
      erewrite <- I_iff_elim_M ; [ apply H | clear H ].
      apply 𝓗_Fun'_nonexpansive ; repeat iintro ; [auto|].
      eapply I_iff_transitive ; [ | apply fold_𝓥𝓤_in_𝓣 ].
      eapply I_iff_transitive ; [ apply I_iff_symmetric ; apply fold_𝓥𝓤_in_𝓣 | ].
      apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; crush.
  - idestruct H as BindsX H.
    assert (binds X (x8, x9) Ξ) as BindsX'.
    { clear - BindsX HX Wf_ΞΞ'.
      ielim_prop BindsX.
      eapply binds_concat_left_inv ; [ apply BindsX | ].
      apply wf_XEnv_ok in Wf_ΞΞ'.
      eapply ok_concat_indom_l ; eauto.
    }
    isplit ; [crush|].
    later_shift.
    apply wf_XEnv_concat_inv_l in Wf_ΞΞ' as Wf_Ξ.
    specialize (binds_wf Wf_Ξ BindsX') as Wf_T𝓔.
    erewrite I_iff_elim_M ; [ apply H | clear H ].
    apply 𝓗_Fun'_nonexpansive ; repeat iintro ; [auto|].
    eapply I_iff_transitive ; [ | apply fold_𝓥𝓤_in_𝓣 ].
    eapply I_iff_transitive ; [ apply I_iff_symmetric ; apply fold_𝓥𝓤_in_𝓣 | ].
    apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; crush.
}

{
destruct 𝓔 ; simpl ; [auto|].
inversion Wf_𝓔 ; auto_contr ; auto.
}

{
destruct T ; simpl.
+ crush.
+ inversion Wf_T.
  auto_contr.
  - apply X_weaken_𝓥_aux ; auto.
  - apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; crush.
+ inversion Wf_T.
  auto_contr.
  apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; [|auto].
  rewrite EV_map_XEnv_concat.
  apply X_weaken_𝓥_aux ; [|crush|crush].
  rewrite <- EV_map_XEnv_concat.
  apply EV_map_wf_XEnv ; assumption.
+ inversion Wf_T.
  auto_contr.
  apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; [|auto].
  rewrite HV_map_XEnv_concat.
  apply X_weaken_𝓥_aux ; [|crush|crush].
  rewrite <- HV_map_XEnv_concat.
  apply HV_map_wf_XEnv ; assumption.
}

Qed.

End section_X_weaken_aux.


Section section_X_weaken.

Context (n : nat).
Context (EV HV : Set).
Context (Ξ Ξ' : XEnv EV HV).
Context (Wf_ΞΞ' : wf_XEnv (Ξ & Ξ')).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig).

Hint Resolve lt'_wf.

Lemma X_weaken_𝓥 T (Wf_T : wf_ty Ξ T) ξ₁ ξ₂ v₁ v₂ :
n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
    𝓥⟦ (Ξ & Ξ') ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂.
Proof.
apply X_weaken_𝓥_aux ; auto.
Qed.

Lemma X_weaken_𝓤 𝓔 (Wf_𝓔 : wf_eff Ξ 𝓔) ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ :
n ⊨ 𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ⇔
    𝓤⟦ (Ξ & Ξ') ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂.
Proof.
apply X_weaken_𝓤_aux ; auto.
Qed.

Hint Resolve X_weaken_𝓥 X_weaken_𝓤.

Lemma X_weaken_𝓣 T (Wf_T : wf_ty Ξ T) 𝓔 (Wf_𝓔 : wf_eff Ξ 𝓔) ξ₁ ξ₂ t₁ t₂ :
n ⊨ 𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
    𝓣⟦ (Ξ & Ξ') ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂.
Proof.
apply 𝓣_Fun_Fix'_nonexpansive ; repeat iintro ; auto.
Qed.

End section_X_weaken.
