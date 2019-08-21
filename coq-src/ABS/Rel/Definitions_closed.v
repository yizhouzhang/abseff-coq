Require Import IxFree.Lib.
Require Import ABS.Util.Postfix.
Require Import ABS.Lang.Syntax.
Require Import ABS.Lang.Bindings.
Require Import ABS.Lang.Operational.
Set Implicit Arguments.

Require Export Util.Postfix Lang.Syntax Lang.Bindings Lang.Operational IxFree.Lib.

Implicit Types EV HV V L : Set.

Definition 𝓞_Sig : list Type :=
  [ (list var : Type) ; (list var : Type) ; (tm0 : Type) ; (tm0 : Type) ].
Definition 𝓣_Sig : list Type :=
  [ (list var : Type) ; (list var : Type) ; (tm0 : Type) ; (tm0 : Type) ].
Definition 𝓥_Sig : list Type :=
  [ (list var : Type) ; (list var : Type) ; (val0 : Type) ; (val0 : Type) ].
Definition 𝓤_Sig : list Type :=
  [ (list var : Type) ; (list var : Type) ; (tm0 : Type) ; (tm0 : Type) ;
    IRel 𝓣_Sig ; (vars : Type) ; (vars : Type) ].
Definition ty_𝓥_Sig : Set → Set → list Type :=
  λ EV HV, ([
    (XEnv EV HV : Type) ;
    (EV → eff0 : Type) ; (EV → eff0 : Type) ;
    (EV → IRel 𝓤_Sig : Type) ;
    (HV → hd0 : Type) ; (HV → hd0 : Type) ;
    (HV → IRel 𝓣_Sig : Type) ;
    (ty EV HV ∅ : Type)
  ] ++ 𝓥_Sig) % list.
Definition eff_𝓤_Sig : Set → Set → list Type :=
  λ EV HV, ([
    (XEnv EV HV : Type) ;
    (EV → eff0 : Type) ; (EV → eff0 : Type) ;
    (EV → IRel 𝓤_Sig : Type) ;
    (HV → hd0 : Type) ; (HV → hd0 : Type) ;
    (HV → IRel 𝓣_Sig : Type) ;
    (eff EV HV ∅ : Type)
  ] ++ 𝓤_Sig) % list.

Notation subst_ty δ ρ T := (
  HV_bind_ty ρ (EV_bind_ty (HV_open_eff ∘ δ) T)
).

Notation subst_ef δ ρ ε := (
  HV_bind_ef ρ (EV_bind_ef (HV_open_eff ∘ δ) ε)
).

Notation subst_eff δ ρ 𝓔 := (
  HV_bind_eff ρ (EV_bind_eff (HV_open_eff ∘ δ) 𝓔)
).

Notation subst_hd δ ρ γ h := (
  V_bind_hd γ (
    HV_bind_hd (V_open_hd ∘ ρ) (
      EV_bind_hd (HV_open_eff ∘ δ) h
    )
  )
).

Notation subst_ktx δ ρ γ K := (
  V_bind_ktx γ (
    HV_bind_ktx (V_open_hd ∘ ρ) (
      EV_bind_ktx (HV_open_eff ∘ δ) K
    )
  )
).

Notation subst_tm δ ρ γ t := (
  V_bind_tm γ (
    HV_bind_tm (V_open_hd ∘ ρ) (
      EV_bind_tm (HV_open_eff ∘ δ) t
    )
  )
).

Notation subst_val δ ρ γ v := (
  V_bind_val γ (
    HV_bind_val (V_open_hd ∘ ρ) (
      EV_bind_val (HV_open_eff ∘ δ) v
    )
  )
).

(** * The [𝓞] relation *)

(** The [𝓞] relation, with a recursive binder *)
Definition 𝓞_Fun (𝓞 : IRel 𝓞_Sig) ξ₁ ξ₂ (t₁ t₂ : tm0) : IProp :=
  ((∃ (v₁ : val0), t₁ = v₁) ∧ ∃ ξ₂' (v₂ : val0), step_refl_tran ⟨ξ₂, t₂⟩ ⟨ξ₂', v₂⟩)ᵢ ∨ᵢ
  (∃ᵢ ξ₁' t₁', (step ⟨ξ₁, t₁⟩ ⟨ξ₁', t₁'⟩)ᵢ ∧ᵢ ▷ 𝓞 ξ₁' ξ₂ t₁' t₂).

Lemma 𝓞_Fun_contractive : contractive _ 𝓞_Fun.
Proof.
  unfold contractive.
  intros R₁ R₂.
  intro n.
  iintro H.
  simpl.
  iintro ξ₁ ; iintro ξ₂.
  iintro t₁ ; iintro t₂.
  unfold 𝓞_Fun.
  auto_contr.
  iespecialize H ; eassumption.
Qed.

(** The [𝓞] relation, with the recursive knot tied *)
Definition 𝓞 := I_fix _ 𝓞_Fun 𝓞_Fun_contractive.

(** Lemmas about rolling and unrolling the recursive [𝓞] definition *)
Lemma 𝓞_roll n ξ₁ ξ₂ t₁ t₂ : n ⊨ 𝓞_Fun 𝓞 ξ₁ ξ₂ t₁ t₂ → n ⊨ 𝓞 ξ₁ ξ₂ t₁ t₂.
Proof.
  intro H.
  apply (I_fix_roll 𝓞_Sig).
  apply H.
Qed.

Lemma 𝓞_unroll n ξ₁ ξ₂ t₁ t₂ : n ⊨ 𝓞 ξ₁ ξ₂ t₁ t₂ → n ⊨ 𝓞_Fun 𝓞 ξ₁ ξ₂ t₁ t₂.
Proof.
  intro H.
  apply (I_fix_unroll 𝓞_Sig).
  apply H.
Qed.


(** * The [𝓦], [𝓡], and [𝓣] relations (biorthogonality) *)

Section section_𝓣𝓡𝓦_Fun.

(** These relations are parameterized by a [𝓥] and a [𝓤] relation. *)

Context (𝓥 : IRel 𝓥_Sig) (𝓤 : IRel 𝓤_Sig).

(** Relations [𝓦], [𝓡], and [𝓣] are first defined as functors of [𝓣].
The fixpoint is then taken of the functors. *)

Context (𝓣 : IRel 𝓣_Sig).

(** The [𝓦] relation, expressed as a functor *)

Definition 𝓦_Fun ξ₁ ξ₂ (K₁ K₂ : ktx0) (t₁ t₂ : tm0) : IProp :=
  ∃ᵢ ψ l₁ l₂,
  𝓤 ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ∧ᵢ
  (∀ X, (X ∈ l₁ → tunnels X K₁) ∧ (X ∈ l₂ → tunnels X K₂))ᵢ ∧ᵢ
  ∀ᵢ ξ₁' ξ₂' t₁' t₂',
  (postfix ξ₁ ξ₁')ᵢ ⇒
  (postfix ξ₂ ξ₂')ᵢ ⇒
  ψ ξ₁' ξ₂' t₁' t₂' ⇒ ▷ 𝓣 ξ₁' ξ₂'(ktx_plug K₁ t₁') (ktx_plug K₂ t₂').

(** The [𝓡] relation, expressed as a functor *)

Definition 𝓡_v_Fun ξ₁ ξ₂ (R₁ R₂ : ktx0) : IProp :=
  ∀ᵢ ξ₁' ξ₂' v₁ v₂,
  (postfix ξ₁ ξ₁')ᵢ ⇒
  (postfix ξ₂ ξ₂')ᵢ ⇒
  𝓥 ξ₁' ξ₂' v₁ v₂ ⇒ 𝓞 ξ₁' ξ₂' (ktx_plug R₁ v₁) (ktx_plug R₂ v₂).

Definition 𝓡_w_Fun ξ₁ ξ₂ (R₁ R₂ : ktx0) : IProp :=
  ∀ᵢ ξ₁' ξ₂' (K₁ K₂ : ktx0) t₁ t₂,
  (postfix ξ₁ ξ₁')ᵢ ⇒
  (postfix ξ₂ ξ₂')ᵢ ⇒
  𝓦_Fun ξ₁' ξ₂' K₁ K₂ t₁ t₂ ⇒
  𝓞 ξ₁' ξ₂'
  (ktx_plug R₁ (ktx_plug K₁ t₁))
  (ktx_plug R₂ (ktx_plug K₂ t₂)).

Definition 𝓡_Fun ξ₁ ξ₂ (R₁ R₂ : ktx0) : IProp :=
  𝓡_v_Fun ξ₁ ξ₂ R₁ R₂ ∧ᵢ 𝓡_w_Fun ξ₁ ξ₂ R₁ R₂.

(** The [𝓣] relation, expressed as a functor *)

Definition 𝓣_Fun ξ₁ ξ₂ (t₁ t₂ : tm0) : IProp :=
  ∀ᵢ R₁ R₂, 𝓡_Fun ξ₁ ξ₂ R₁ R₂ ⇒ 𝓞 ξ₁ ξ₂ (ktx_plug R₁ t₁) (ktx_plug R₂ t₂).

End section_𝓣𝓡𝓦_Fun.


(** [𝓣_Fun] is contractive in [𝓣] *)
Lemma 𝓣_Fun_contractive (𝓥 : IRel 𝓥_Sig) (𝓤 : IRel 𝓤_Sig) :
  contractive _ (𝓣_Fun 𝓥 𝓤).
Proof.
  intros r₁ r₂ n.
  iintro H.
  iintro ξ₁ ; iintro ξ₂.
  iintro t₁ ; iintro t₂.
  unfold 𝓣_Fun ; auto_contr.
  unfold 𝓡_Fun ; auto_contr.
  unfold 𝓡_w_Fun ; auto_contr.
  unfold 𝓦_Fun ; auto_contr.
  iespecialize H ; eassumption.
Qed.

(** The [𝓣] relation, with the recursive knot tied *)

Definition 𝓣_Fun_Fix (𝓥 : IRel 𝓥_Sig) (𝓤 : IRel 𝓤_Sig) : IRel 𝓣_Sig :=
  I_fix _ (𝓣_Fun 𝓥 𝓤) (𝓣_Fun_contractive 𝓥 𝓤).

(** The [𝓦], [𝓡], and [𝓣] relations, with the fixpoint unrolled *)

Notation 𝓣_Fun_Fix' 𝓥 𝓤 := (𝓣_Fun 𝓥 𝓤 (𝓣_Fun_Fix 𝓥 𝓤)).
Notation 𝓡_Fun_Fix' 𝓥 𝓤 := (𝓡_Fun 𝓥 𝓤 (𝓣_Fun_Fix 𝓥 𝓤)).
Notation 𝓦_Fun_Fix' 𝓥 𝓤 := (𝓦_Fun 𝓤 (𝓣_Fun_Fix 𝓥 𝓤)).
Notation 𝓡_w_Fun_Fix' 𝓥 𝓤 := (𝓡_w_Fun 𝓤 (𝓣_Fun_Fix 𝓥 𝓤)).

(* [𝓣_Fun_Fix'] and [𝓣_Fun_Fix] are equivalent relations *)

Lemma 𝓣_roll n 𝓤 𝓥 ξ₁ ξ₂ t₁ t₂ :
  n ⊨ 𝓣_Fun_Fix' 𝓤 𝓥 ξ₁ ξ₂ t₁ t₂ → n ⊨ 𝓣_Fun_Fix 𝓤 𝓥 ξ₁ ξ₂ t₁ t₂.
Proof.
  intro H.
  apply (I_fix_roll 𝓣_Sig).
  apply H.
Qed.

Lemma 𝓣_unroll n 𝓤 𝓥 ξ₁ ξ₂ t₁ t₂ :
  n ⊨ 𝓣_Fun_Fix 𝓤 𝓥 ξ₁ ξ₂ t₁ t₂ → n ⊨ 𝓣_Fun_Fix' 𝓤 𝓥 ξ₁ ξ₂ t₁ t₂.
Proof.
  intro H.
  apply (I_fix_unroll 𝓣_Sig).
  apply H.
Qed.

Lemma 𝓣_equiv_roll n 𝓤1 𝓥1 𝓤2 𝓥2 ξ₁ ξ₂ t₁ t₂ :
  (n ⊨ 𝓣_Fun_Fix' 𝓥1 𝓤1 ξ₁ ξ₂ t₁ t₂ ⇔ 𝓣_Fun_Fix' 𝓥2 𝓤2 ξ₁ ξ₂ t₁ t₂) →
  (n ⊨ 𝓣_Fun_Fix 𝓥1 𝓤1 ξ₁ ξ₂ t₁ t₂ ⇔ 𝓣_Fun_Fix 𝓥2 𝓤2 ξ₁ ξ₂ t₁ t₂).
Proof.
  intro H.
  idestruct H as H12 H21.
  isplit ; iintro H ; apply 𝓣_roll ; apply 𝓣_unroll in H.
  + iapply H12 ; apply H.
  + iapply H21 ; apply H.
Qed.


(** * The [𝓚] relation on evaluation contexts *)

Section section_𝓚_Fun.

Context (𝓥a : IRel 𝓥_Sig) (𝓤a : IRel 𝓤_Sig).
Context (𝓥b : IRel 𝓥_Sig) (𝓤b : IRel 𝓤_Sig).

Definition 𝓚_Fun ξ₁ ξ₂ (K₁ K₂ : ktx0) : IProp :=
  ∀ᵢ ξ₁' ξ₂' t₁ t₂,
  (postfix ξ₁ ξ₁')ᵢ ⇒
  (postfix ξ₂ ξ₂')ᵢ ⇒
  𝓣_Fun_Fix' 𝓥a 𝓤a ξ₁' ξ₂' t₁ t₂ ⇒
  𝓣_Fun_Fix' 𝓥b 𝓤b ξ₁' ξ₂' (ktx_plug K₁ t₁) (ktx_plug K₂ t₂).

End section_𝓚_Fun.


Section section_𝓤_Fun.

Context (𝓥 : IRel_xx ty_𝓥_Sig).
Context (𝓤 : IRel_xx eff_𝓤_Sig).
Context (EV HV : Set).
Context (Ξ : XEnv EV HV).
Context (δ₁ δ₂ : EV → eff0).
Context (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : HV → hd0).
Context (ρ : HV → IRel 𝓣_Sig).

Definition 𝓗_Fun' 𝔽 φ ξ₁ ξ₂ (t₁ t₂ : tm ∅ ∅ (inc (inc ∅)) ∅) : IProp :=
  ∀ᵢ ξ₁' ξ₂',
  (postfix ξ₁ ξ₁')ᵢ ⇒
  (postfix ξ₂ ξ₂')ᵢ ⇒
  ∀ᵢ v₁ v₂ X₁ X₂ K₁ K₂,
  𝓥 empty ∅→ ∅→ ∅→ ∅→ ∅→ ∅→ (fst (Σ 𝔽)) ξ₁' ξ₂' v₁ v₂ ⇒
  ( ∀ᵢ ξ₁'' ξ₂'' u₁ u₂,
    (postfix ξ₁' ξ₁'')ᵢ ⇒
    (postfix ξ₂' ξ₂'')ᵢ ⇒
    𝓥 empty ∅→ ∅→ ∅→ ∅→ ∅→ ∅→ (snd (Σ 𝔽)) ξ₁'' ξ₂'' u₁ u₂ ⇒
    ▷ φ ξ₁'' ξ₂'' (⇩ X₁ (ktx_plug K₁ u₁)) (⇩ X₂ (ktx_plug K₂ u₂))
  ) ⇒
  φ ξ₁' ξ₂'
    (V2_subst_tm v₁ (val_fun (⇩ X₁ (ktx_plug (V_open_ktx K₁) (val_var VZ)))) t₁)
    (V2_subst_tm v₂ (val_fun (⇩ X₂ (ktx_plug (V_open_ktx K₂) (val_var VZ)))) t₂)
.

Definition 𝓗_Fun 𝔽 (ℓ : lbl HV ∅) ξ₁ ξ₂ (h₁ h₂ : hd0) : IProp :=
match ℓ with
| lbl_var p =>
  ∃ᵢ t₁ t₂ X₁ X₂,
  ( h₁ = hd_def 𝔽 (lid_f X₁) t₁ ∧
    h₂ = hd_def 𝔽 (lid_f X₂) t₂ )ᵢ
  ∧ᵢ
  ( lbl_hd (ρ₁ p) = lbl_id (lid_f X₁) ∧ lbl_hd (ρ₂ p) = lbl_id (lid_f X₂) )ᵢ
  ∧ᵢ
  ▷ 𝓗_Fun' 𝔽 (ρ p) ξ₁ ξ₂ t₁ t₂
| lbl_id (lid_f X) =>
  ∃ᵢ t₁ t₂,
  ( h₁ = hd_def 𝔽 (lid_f X) t₁ ∧
    h₂ = hd_def 𝔽 (lid_f X) t₂ )ᵢ
  ∧ᵢ
  ∃ᵢ T 𝓔,
  (binds X (T, 𝓔) Ξ)ᵢ
  ∧ᵢ
  ▷ 𝓗_Fun' 𝔽
    (𝓣_Fun_Fix' (𝓥 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T) (𝓤 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝓔))
    ξ₁ ξ₂ t₁ t₂
| lbl_id (lid_b _) => (False)ᵢ
end.

Fixpoint 𝓾_Fun
(ε : ef EV HV ∅)
ξ₁ ξ₂ (t₁ t₂ : tm0) (ψ : IRel 𝓣_Sig) (l₁ l₂ : vars) : IProp :=
match ε with
| ef_var α =>
    δ α ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂
| ef_lbl ℓ =>
    ∃ᵢ 𝔽 X₁ X₂ h₁ h₂ (v₁ v₂ : val0),
    ( HV_bind_lbl ρ₁ ℓ = lbl_id (lid_f X₁) ∧
      HV_bind_lbl ρ₂ ℓ = lbl_id (lid_f X₂) )ᵢ
    ∧ᵢ
    ( t₁ = tm_app (⇧ h₁) v₁ ∧ t₂ = tm_app (⇧ h₂) v₂ )ᵢ
    ∧ᵢ
    ( l₁ = \{ X₁ } ∧ l₂ = \{ X₂ } )ᵢ
    ∧ᵢ
    𝓗_Fun 𝔽 ℓ ξ₁ ξ₂ h₁ h₂
    ∧ᵢ
    ▷ 𝓥 empty ∅→ ∅→ ∅→ ∅→ ∅→ ∅→ (fst (Σ 𝔽)) ξ₁ ξ₂ v₁ v₂
    ∧ᵢ
    ∀ᵢ ξ₁' ξ₂' t₁' t₂',
    (▷ ∃ᵢ (u₁ u₂ : val0), (t₁' = u₁ ∧ t₂' = u₂)ᵢ ∧ᵢ
       𝓥 empty ∅→ ∅→ ∅→ ∅→ ∅→ ∅→ (snd (Σ 𝔽)) ξ₁' ξ₂' u₁ u₂)
    ⇔ ψ ξ₁' ξ₂' t₁' t₂'
end.

Fixpoint 𝓤_Fun 𝓔 ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ : IProp :=
match 𝓔 with
| [] => (False)ᵢ
| ε :: 𝓔 => 𝓾_Fun ε ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ ∨ᵢ 𝓤_Fun 𝓔 ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂
end
.

End section_𝓤_Fun.


Section section_𝓥_Fun.

Context (𝓥 : IRel_xx ty_𝓥_Sig).
Context (𝓤 : IRel_xx eff_𝓤_Sig).

Definition closed_φ ξ₁ ξ₂ (φ : IRel 𝓤_Sig) : IProp :=
∀ᵢ ξ₁' ξ₂' s₁ s₂ ψ Xs₁ Xs₂,
φ ξ₁' ξ₂' s₁ s₂ ψ Xs₁ Xs₂ ⇒
(Xs₁ \c from_list ξ₁ ∧ Xs₂ \c from_list ξ₂)ᵢ.

Fixpoint 𝓥_Fun
  EV HV (Ξ : XEnv EV HV)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig)
  (T : ty EV HV ∅) ξ₁ ξ₂ (v₁ v₂ : val0) {struct T} : IProp :=
match T with
| 𝟙 =>
  (v₁ = val_unit ∧ v₂ = val_unit)ᵢ
| ty_fun T₁ T₂ 𝓔 =>
  ∀ᵢ ξ₁' ξ₂',
  (postfix ξ₁ ξ₁')ᵢ ⇒
  (postfix ξ₂ ξ₂')ᵢ ⇒
  ∀ᵢ u₁ u₂,
  𝓥_Fun Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T₁ ξ₁' ξ₂' u₁ u₂ ⇒
  𝓣_Fun_Fix'
    (𝓥_Fun Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T₂)
    (𝓤_Fun 𝓥 𝓤 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝓔)
    ξ₁' ξ₂'
    (tm_app v₁ u₁)
    (tm_app v₂ u₂)
| ty_efun T₀ =>
  ∀ᵢ ξ₁' ξ₂',
  (postfix ξ₁ ξ₁')ᵢ ⇒
  (postfix ξ₂ ξ₂')ᵢ ⇒
  ∀ᵢ 𝓔₁ 𝓔₂ (φ : IRel 𝓤_Sig),
  closed_φ ξ₁' ξ₂' φ ⇒
  let δ₁' := env_ext δ₁ 𝓔₁ in
  let δ₂' := env_ext δ₂ 𝓔₂ in
  let δ' := env_ext δ φ in
  𝓣_Fun_Fix'
    (𝓥_Fun (EV_shift_XEnv Ξ) δ₁' δ₂' δ' ρ₁ ρ₂ ρ T₀)
    (𝓤_Fun 𝓥 𝓤 empty ∅→ ∅→ ∅→ ∅→ ∅→ ∅→ [])
    ξ₁' ξ₂'
    (tm_eapp v₁ 𝓔₁)
    (tm_eapp v₂ 𝓔₂)
| ty_hfun 𝔽 T₀ =>
  ∀ᵢ ξ₁' ξ₂',
  (postfix ξ₁ ξ₁')ᵢ ⇒
  (postfix ξ₂ ξ₂')ᵢ ⇒
  ∀ᵢ r₁ r₂ X₁ X₂ φ,
  (X₁ ∈ from_list ξ₁' ∧ X₂ ∈ from_list ξ₂')ᵢ ⇒
  ▷ 𝓗_Fun' 𝓥 𝔽 φ ξ₁' ξ₂' r₁ r₂ ⇒
  let ρ₁' := env_ext ρ₁ (hd_def 𝔽 (lid_f X₁) r₁) in
  let ρ₂' := env_ext ρ₂ (hd_def 𝔽 (lid_f X₂) r₂) in
  let ρ' := env_ext ρ φ in
  𝓣_Fun_Fix'
    (𝓥_Fun (HV_shift_XEnv Ξ) δ₁ δ₂ δ ρ₁' ρ₂' ρ' T₀)
    (𝓤_Fun 𝓥 𝓤 empty ∅→ ∅→ ∅→ ∅→ ∅→ ∅→ [])
    ξ₁' ξ₂'
    (tm_happ v₁ (hd_def 𝔽 (lid_f X₁) r₁))
    (tm_happ v₂ (hd_def 𝔽 (lid_f X₂) r₂))
end.

End section_𝓥_Fun.


(** [𝓣_Fun_Fix'] is nonexpansive in [𝓥] and [𝓤] *)

Section section_𝓣_Fun_Fix'_nonexpansive.
Context (𝓥₁ 𝓥₂ : IRel 𝓥_Sig).
Context (𝓤₁ 𝓤₂ : IRel 𝓤_Sig).

Lemma 𝓣_Fun_Fix'_nonexpansive_aux :
  ∀ n,
  n ⊨ 𝓥₁ ≈ᵢ 𝓥₂ →
  n ⊨ 𝓤₁ ≈ᵢ 𝓤₂ →
  n ⊨ ∀ᵢ ξ₁ ξ₂ t₁ t₂,
      𝓣_Fun_Fix' 𝓥₁ 𝓤₁ ξ₁ ξ₂ t₁ t₂ ⇔ 𝓣_Fun_Fix' 𝓥₂ 𝓤₂ ξ₁ ξ₂ t₁ t₂.
Proof.
  intros n H𝓥 H𝓤.
  loeb_induction LöbIH.
  iintro ξ₁ ; iintro ξ₂.
  iintro t₁ ; iintro t₂.
  unfold 𝓣_Fun.
  unfold 𝓡_Fun, 𝓡_v_Fun, 𝓡_w_Fun.
  unfold 𝓦_Fun.
  auto_contr.
  - iespecialize H𝓥 ; eassumption.
  - iespecialize H𝓤 ; eassumption.
  - iespecialize LöbIH.
    idestruct LöbIH as IH1 IH2.
    isplit ; iintro H.
    * apply (I_fix_roll 𝓣_Sig).
      iapply IH1.
      apply (I_fix_unroll 𝓣_Sig) in H.
      apply H.
    * apply (I_fix_roll 𝓣_Sig).
      iapply IH2.
      apply (I_fix_unroll 𝓣_Sig) in H.
      apply H.
Qed.

Lemma 𝓣_Fun_Fix'_nonexpansive :
  ∀ n ξ₁ ξ₂ t₁ t₂,
  n ⊨ 𝓥₁ ≈ᵢ 𝓥₂ →
  n ⊨ 𝓤₁ ≈ᵢ 𝓤₂ →
  n ⊨ 𝓣_Fun_Fix' 𝓥₁ 𝓤₁ ξ₁ ξ₂ t₁ t₂ ⇔ 𝓣_Fun_Fix' 𝓥₂ 𝓤₂ ξ₁ ξ₂ t₁ t₂.
Proof.
  intros n ξ₁ ξ₂ t₁ t₂ H𝓥 H𝓤.
  specialize (𝓣_Fun_Fix'_nonexpansive_aux H𝓥 H𝓤) as H.
  iespecialize H; exact H.
Qed.

End section_𝓣_Fun_Fix'_nonexpansive.


Section section_𝓚_Fun_nonexpansive.

Context (𝓥a1 𝓥a2 𝓥b1 𝓥b2 : IRel 𝓥_Sig).
Context (𝓤a1 𝓤a2 𝓤b1 𝓤b2 : IRel 𝓤_Sig).

Lemma 𝓚_Fun_nonexpansive n ξ₁ ξ₂ K₁ K₂ :
  n ⊨ 𝓥a1 ≈ᵢ 𝓥a2 →
  n ⊨ 𝓤a1 ≈ᵢ 𝓤a2 →
  n ⊨ 𝓥b1 ≈ᵢ 𝓥b2 →
  n ⊨ 𝓤b1 ≈ᵢ 𝓤b2 →
  n ⊨ 𝓚_Fun 𝓥a1 𝓤a1 𝓥b1 𝓤b1 ξ₁ ξ₂ K₁ K₂ ⇔
      𝓚_Fun 𝓥a2 𝓤a2 𝓥b2 𝓤b2 ξ₁ ξ₂ K₁ K₂.
Proof.
  intros H𝓥a H𝓤a H𝓥b H𝓤b.
  unfold 𝓚_Fun.
  auto_contr.
  + apply 𝓣_Fun_Fix'_nonexpansive ; assumption.
  + apply 𝓣_Fun_Fix'_nonexpansive ; assumption.
Qed.

End section_𝓚_Fun_nonexpansive.


Section section_𝓤_Fun_contractive.

Context (𝓥1 𝓥2 : IRel_xx ty_𝓥_Sig).
Context (𝓤1 𝓤2 : IRel_xx eff_𝓤_Sig).
Context (EV HV : Set).
Context (Ξ : XEnv EV HV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig).

Lemma 𝓗_Fun'_nonexpansive n 𝔽 (φ1 φ2 : IRel 𝓣_Sig) ξ₁ ξ₂ t₁ t₂ :
  n ⊨ I_rel_xx_equiv _ 𝓥1 𝓥2 →
  n ⊨ I_rel_equiv _ φ1 φ2 →
  n ⊨ 𝓗_Fun' 𝓥1 𝔽 φ1 ξ₁ ξ₂ t₁ t₂ ⇔
      𝓗_Fun' 𝓥2 𝔽 φ2 ξ₁ ξ₂ t₁ t₂.
Proof.
  intros H𝓥 Hφ.
  unfold 𝓗_Fun'.
  auto_contr.
  + iespecialize H𝓥 ; eassumption.
  + iespecialize H𝓥 ; eassumption.
  + iespecialize Hφ ; eassumption.
  + iespecialize Hφ ; eassumption.
Qed.

Lemma 𝓗_Fun_contractive n 𝔽 ℓ ξ₁ ξ₂ h₁ h₂ :
  n ⊨ ▷ I_rel_xx_equiv _ 𝓥1 𝓥2 →
  n ⊨ ▷ I_rel_xx_equiv _ 𝓤1 𝓤2 →
  n ⊨ 𝓗_Fun 𝓥1 𝓤1 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝔽 ℓ ξ₁ ξ₂ h₁ h₂ ⇔
      𝓗_Fun 𝓥2 𝓤2 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝔽 ℓ ξ₁ ξ₂ h₁ h₂.
Proof.
Proof.
intros H𝓥 H𝓤.
destruct ℓ as [ p | [ | X ] ] ; simpl.
+ auto_contr.
  apply 𝓗_Fun'_nonexpansive.
  - apply H𝓥.
  - repeat iintro ; apply auto_contr_id.
+ auto_contr.
+ auto_contr.
  apply 𝓗_Fun'_nonexpansive.
  - apply H𝓥.
  - repeat iintro ; apply 𝓣_Fun_Fix'_nonexpansive.
    * repeat iintro ; iespecialize H𝓥 ; apply H𝓥.
    * repeat iintro ; iespecialize H𝓤 ; apply H𝓤.
Qed.

Lemma 𝓾_Fun_contractive n ε ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂ :
  n ⊨ ▷ I_rel_xx_equiv _ 𝓥1 𝓥2 →
  n ⊨ ▷ I_rel_xx_equiv _ 𝓤1 𝓤2 →
  n ⊨ 𝓾_Fun 𝓥1 𝓤1 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ ε ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂ ⇔
      𝓾_Fun 𝓥2 𝓤2 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ ε ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂.
Proof.
intros H𝓥 H𝓤.
destruct ε ; simpl.
+ auto_contr.
+ auto_contr.
  - apply 𝓗_Fun_contractive ; auto.
  - iespecialize H𝓥 ; apply H𝓥.
  - iespecialize H𝓥 ; apply H𝓥.
Qed.

Fixpoint 𝓤_Fun_contractive
  n
  (𝓔 : eff EV HV ∅) ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂ {struct 𝓔} :
  n ⊨ ▷ I_rel_xx_equiv _ 𝓥1 𝓥2 →
  n ⊨ ▷ I_rel_xx_equiv _ 𝓤1 𝓤2 →
  n ⊨ 𝓤_Fun 𝓥1 𝓤1 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝓔 ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂ ⇔
      𝓤_Fun 𝓥2 𝓤2 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝓔 ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂.
Proof.
  intros H𝓥 H𝓤.
  destruct 𝓔 ; intros ; simpl.
  + auto_contr.
  + auto_contr.
    - apply 𝓾_Fun_contractive ; later_shift ; assumption.
    - apply 𝓤_Fun_contractive ; assumption.
Qed.

End section_𝓤_Fun_contractive.


Section section_𝓥_Fun_contractive.

Context (𝓥1 𝓥2 : IRel_xx ty_𝓥_Sig).
Context (𝓤1 𝓤2 : IRel_xx eff_𝓤_Sig).

Fixpoint 𝓥_Fun_contractive
    n
    EV HV (Ξ : XEnv EV HV)
    (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
    (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig)
    T ξ₁ ξ₂ v₁ v₂ {struct T} :
    n ⊨ ▷ I_rel_xx_equiv _ 𝓥1 𝓥2 →
    n ⊨ ▷ I_rel_xx_equiv _ 𝓤1 𝓤2 →
    n ⊨ 𝓥_Fun 𝓥1 𝓤1 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T ξ₁ ξ₂ v₁ v₂ ⇔
        𝓥_Fun 𝓥2 𝓤2 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T ξ₁ ξ₂ v₁ v₂.
Proof.
intros H𝓥 H𝓤.
destruct T ; simpl ; auto_contr.
+ apply 𝓥_Fun_contractive ; assumption.
+ apply 𝓣_Fun_Fix'_nonexpansive.
  - repeat iintro ; apply 𝓥_Fun_contractive ; assumption.
  - repeat iintro ; apply 𝓤_Fun_contractive ; assumption.
+ apply 𝓣_Fun_Fix'_nonexpansive.
  - repeat iintro ; apply 𝓥_Fun_contractive ; assumption.
  - repeat iintro ; auto_contr.
+ apply 𝓗_Fun'_nonexpansive.
  - repeat iintro ; iespecialize H𝓥 ; eassumption.
  - repeat iintro ; auto_contr.
+ apply 𝓣_Fun_Fix'_nonexpansive.
  - repeat iintro ; apply 𝓥_Fun_contractive ; assumption.
  - repeat iintro ; auto_contr.
Qed.

End section_𝓥_Fun_contractive.


Section section_𝓥_Fun_Fix.

Program Definition 𝓤_Fun_Fix1 (𝓥 : IRel_xx ty_𝓥_Sig) : IRel_xx eff_𝓤_Sig :=
  I_fix_xx _ (𝓤_Fun 𝓥) _.
Next Obligation.
Proof.
  intros r₁ r₂ n.
  repeat iintro.
  apply 𝓤_Fun_contractive.
  + iintro_later.
    apply I_rel_xx_equiv_reflexive.
  + assumption.
Qed.

Lemma 𝓤_Fun_Fix1_nonexpansive_aux
  𝓥1 𝓥2 n :
  n ⊨ I_rel_xx_equiv _ 𝓥1 𝓥2 →
  n ⊨ ∀ᵢ (EV HV : Set) (Ξ : XEnv EV HV)
         (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
         (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig)
         𝓔 ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂,
      𝓤_Fun_Fix1 𝓥1 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝓔 ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂ ⇔
      𝓤_Fun_Fix1 𝓥2 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝓔 ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂.
Proof.
  intro H.
  loeb_induction LöbIH.
  repeat iintro.
  unfold 𝓤_Fun_Fix1 ; isplit ; iintro H'.
  + eapply (I_fix_xx_roll eff_𝓤_Sig).
    eapply (I_fix_xx_unroll eff_𝓤_Sig) in H'.
    erewrite <- I_iff_elim_M ; [ apply H' | ].
    eapply 𝓤_Fun_contractive.
    - iintro_later ; apply H.
    - later_shift.
      repeat iintro.
      iespecialize LöbIH ; apply LöbIH.
  + eapply (I_fix_xx_roll eff_𝓤_Sig).
    eapply (I_fix_xx_unroll eff_𝓤_Sig) in H'.
    erewrite I_iff_elim_M ; [ apply H' | ].
    eapply 𝓤_Fun_contractive.
    - iintro_later ; apply H.
    - later_shift.
      repeat iintro.
      iespecialize LöbIH ; apply LöbIH.
Qed.

Corollary 𝓤_Fun_Fix1_nonexpansive
  𝓥1 𝓥2
  n
  (EV HV : Set) (Ξ : XEnv EV HV)
  (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig)
  (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig)
  𝓔 ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂ :
  n ⊨ I_rel_xx_equiv _ 𝓥1 𝓥2 →
  n ⊨ 𝓤_Fun_Fix1 𝓥1 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝓔 ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂ ⇔
      𝓤_Fun_Fix1 𝓥2 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝓔 ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂.
Proof.
  intro H.
  specialize (𝓤_Fun_Fix1_nonexpansive_aux H) as H'.
  iespecialize H' ; apply H'.
Qed.

Program Definition 𝓥_Fun_Fix : IRel_xx ty_𝓥_Sig :=
  I_fix_xx _ (λ 𝓥, 𝓥_Fun 𝓥 (𝓤_Fun_Fix1 𝓥)) _.
Next Obligation.
Proof.
  intros r₁ r₂ n.
  repeat iintro.
  apply 𝓥_Fun_contractive.
  + assumption.
  + later_shift.
    repeat iintro.
    apply 𝓤_Fun_Fix1_nonexpansive ; assumption.
Qed.


Definition 𝓤_Fun_Fix : IRel_xx eff_𝓤_Sig := 𝓤_Fun_Fix1 𝓥_Fun_Fix.

End section_𝓥_Fun_Fix.


Notation "'𝓥⟦' Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓥_Fun (𝓥_Fun_Fix) (𝓤_Fun_Fix) Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T)
(at level 25, Ξ at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓤⟦' Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓤_Fun (𝓥_Fun_Fix) (𝓤_Fun_Fix) Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝓔)
(at level 25, Ξ at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).


Section section_𝓥𝓤_roll_unroll.

Context (EV HV : Set).
Context (Ξ : XEnv EV HV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig).
Context (T : ty EV HV ∅) (v₁ v₂ : val0).
Context (𝓔 : eff EV HV ∅).
Context (ξ₁ ξ₂ : list var) (s₁ s₂ : tm0) (ψ : IRel 𝓣_Sig) (l₁ l₂ : vars).

Lemma 𝓥_roll n :
  n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ →
  n ⊨ 𝓥_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T ξ₁ ξ₂ v₁ v₂.
Proof.
  intro H.
  apply (I_fix_xx_roll _ (λ 𝓥, 𝓥_Fun 𝓥 (𝓤_Fun_Fix1 𝓥))).
  apply H.
Qed.

Lemma 𝓥_unroll n :
  n ⊨ 𝓥_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T ξ₁ ξ₂ v₁ v₂ →
  n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂.
Proof.
  intro H.
  apply (I_fix_xx_unroll _ (λ 𝓥, 𝓥_Fun 𝓥 (𝓤_Fun_Fix1 𝓥))).
  apply H.
Qed.

Corollary 𝓥_roll_unroll n :
  n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
      𝓥_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T ξ₁ ξ₂ v₁ v₂.
Proof.
  isplit ; iintro H ; [ apply 𝓥_roll | apply 𝓥_unroll ] ; assumption.
Qed.

Lemma 𝓤_roll n :
  n ⊨ 𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂ →
  n ⊨ 𝓤_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝓔 ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂.
Proof.
  intro H.
  apply (I_fix_xx_roll _ (𝓤_Fun (𝓥_Fun_Fix))).
  apply H.
Qed.

Lemma 𝓤_unroll n :
  n ⊨ 𝓤_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝓔 ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂ →
  n ⊨ 𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂.
Proof.
  intro H.
  apply (I_fix_xx_unroll _ (𝓤_Fun (𝓥_Fun_Fix))).
  apply H.
Qed.

Corollary 𝓤_roll_unroll n :
  n ⊨ 𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂ ⇔
      𝓤_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝓔 ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂.
Proof.
  isplit ; iintro H ; [ apply 𝓤_roll | apply 𝓤_unroll ] ; assumption.
Qed.

End section_𝓥𝓤_roll_unroll.


Notation "'𝓾⟦' Ξ ⊢ ε ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓾_Fun (𝓥_Fun_Fix) (𝓤_Fun_Fix) Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ ε)
(at level 25, Ξ at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓗⟦' Ξ ⊢ 𝔽 # ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓗_Fun (𝓥_Fun_Fix) (𝓤_Fun_Fix) Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝔽 ℓ)
(at level 25, Ξ at level 0, 𝔽 at level 0, ℓ at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓚⟦' Ξ ⊢ Ta # 𝓔a ⇢ Tb # 𝓔b ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓚_Fun
    (𝓥⟦ Ξ ⊢ Ta ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ) (𝓤⟦ Ξ ⊢ 𝓔a ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
    (𝓥⟦ Ξ ⊢ Tb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ) (𝓤⟦ Ξ ⊢ 𝓔b ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
  )
(at level 25, Ξ at level 0,
Ta at level 0, 𝓔a at level 0, Tb at level 0, 𝓔b at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓣⟦' Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓣_Fun_Fix'
    (𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
    (𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ))
(at level 25, Ξ at level 0, T at level 0, 𝓔 at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓡⟦' Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓡_Fun_Fix'
    (𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
    (𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ))
(at level 25, Ξ at level 0, T at level 0, 𝓔 at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓡v⟦' Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓡_v_Fun (𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ))
(at level 25, Ξ at level 0, T at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓡w⟦' Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓡_w_Fun_Fix'
    (𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
    (𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ))
(at level 25, Ξ at level 0, T at level 0, 𝓔 at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓦⟦' Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓦_Fun_Fix'
    (𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
    (𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ))
(at level 25, Ξ at level 0, T at level 0, 𝓔 at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).


Section section_𝓚v_𝓚w.
Context (EV HV : Set).
Context (Ξ : XEnv EV HV).
Context (ω : vars).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig).
Context (Ta : ty EV HV ∅) (𝓔a : eff EV HV ∅).
Context (Tb : ty EV HV ∅) (𝓔b : eff EV HV ∅).
Context (ξ₁ ξ₂ : list var) (K₁ K₂ : ktx0).

Definition 𝓚_v : IProp :=
  ∀ᵢ ξ₁' ξ₂' v₁ v₂,
  (postfix ξ₁ ξ₁')ᵢ ⇒
  (postfix ξ₂ ξ₂')ᵢ ⇒
  𝓥⟦ Ξ ⊢ Ta ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' v₁ v₂ ⇒
  𝓣⟦ Ξ ⊢ Tb # 𝓔b ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' (ktx_plug K₁ v₁) (ktx_plug K₂ v₂).

Definition 𝓚_w : IProp :=
  ∀ᵢ ξ₁' ξ₂' L₁ L₂ s₁ s₂,
  (postfix ξ₁ ξ₁')ᵢ ⇒
  (postfix ξ₂ ξ₂')ᵢ ⇒
  𝓦⟦ Ξ ⊢ Ta # 𝓔a ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' L₁ L₂ s₁ s₂ ⇒
  𝓣⟦ Ξ ⊢ Tb # 𝓔b ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
    ξ₁' ξ₂'
    (ktx_plug K₁ (ktx_plug L₁ s₁))
    (ktx_plug K₂ (ktx_plug L₂ s₂))
.

End section_𝓚v_𝓚w.

Notation "'𝓚v⟦' Ξ ⊢ Ta ⇢ Tb # 𝓔b ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓚_v Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ Ta Tb 𝓔b)
(at level 25, Ξ at level 0,
Ta at level 0, Tb at level 0, 𝓔b at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝓚w⟦' Ξ ⊢ Ta # 𝓔a ⇢ Tb # 𝓔b ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓚_w Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ Ta 𝓔a Tb 𝓔b)
(at level 25, Ξ at level 0,
Ta at level 0, 𝓔a at level 0, Tb at level 0, 𝓔b at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).


Section section_𝓣𝓛.
Context (EV HV : Set).
Context (Ξ : XEnv EV HV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig).

Context (ℓ : lbl HV ∅).

Definition 𝓣𝓛 : IRel 𝓣_Sig :=
  match ℓ with
  | lbl_var α => ρ α
  | lbl_id (lid_f X) =>
      match (get X Ξ) with
      | Some (T, 𝓔) => 𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
      | _ => λ _ _ _ _, (False)ᵢ
      end
  | _ => λ _ _ _ _, (False)ᵢ
  end.

End section_𝓣𝓛.

Notation "'𝓣𝓛⟦' Ξ ⊢ ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" :=
  (𝓣𝓛 Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ ℓ)
(at level 25, Ξ at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).
