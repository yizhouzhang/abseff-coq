Require Import Rel.Definitions_closed.
Require Import Lang.Static.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Section section_𝜩𝑷𝜞.
Context (EV HV V : Set).
Implicit Type (Ξ : XEnv EV HV).
Implicit Type (P : HV → F).
Implicit Type (Γ : V → ty EV HV ∅).
Implicit Type (ω : vars).
Implicit Type (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Implicit Type (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig).
Implicit Type (γ₁ γ₂ : V → val0).

Definition 𝜞 Ξ Γ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ γ₁ γ₂ :=
∀ᵢ x, 𝓥⟦ Ξ ⊢ Γ x ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ (γ₁ x) (γ₂ x).

Definition 𝑷 P ξ₁ ξ₂ ρ₁ ρ₂ ρ :=
∀ᵢ p, ∃ᵢ r₁ r₂ X₁ X₂,
( ρ₁ p = hd_def (P p) (lid_f X₁) r₁ ∧
  ρ₂ p = hd_def (P p) (lid_f X₂) r₂ )ᵢ
∧ᵢ
▷ 𝓗_Fun' (𝓥_Fun_Fix) (P p) (ρ p) ξ₁ ξ₂ r₁ r₂.

Definition 𝜩 Ξ ξ₁ ξ₂ := dom Ξ \c from_list ξ₁ ∧ dom Ξ \c from_list ξ₂.

Definition closed_δ ξ₁ ξ₂ δ : IProp := ∀ᵢ α, closed_φ ξ₁ ξ₂ (δ α).

Definition closed_ρ ξ₁ ξ₂ ρ₁ ρ₂ : Prop :=
∀ p X,
(lbl_hd (ρ₁ p) = lbl_id (lid_f X) → X ∈ from_list ξ₁) ∧
(lbl_hd (ρ₂ p) = lbl_id (lid_f X) → X ∈ from_list ξ₂).

End section_𝜩𝑷𝜞.

Notation "'𝜞⟦' Ξ ⊢ Γ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ" := (𝜞 Ξ Γ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
(at level 25, Ξ at level 0, Γ at level 0,
δ₁ at level 0, δ₂ at level 0, δ at level 0,
ρ₁ at level 0, ρ₂ at level 0, ρ at level 0).

Notation "'𝑷⟦' ⊢ P ⟧" := (𝑷 P)
(at level 25, P at level 0).


Section section_EV_HV_V_open.
Context (EV HV V : Set).
Context (Ξ : XEnv EV HV).
Context (P : HV → F).
Context (Γ : V → ty EV HV ∅).

Definition 𝓣_EV_HV_V_open (T : ty EV HV ∅) (𝓔 : eff EV HV ∅) (t₁ t₂ : tm EV HV V ∅) : IProp :=
  ∀ᵢ ξ₁ ξ₂ δ₁ δ₂ δ ρ₁ ρ₂ ρ γ₁ γ₂,
  (𝜩 Ξ ξ₁ ξ₂)ᵢ ⇒
  closed_δ ξ₁ ξ₂ δ ⇒
  (closed_ρ ξ₁ ξ₂ ρ₁ ρ₂)ᵢ ⇒
  𝑷⟦ ⊢ P ⟧ ξ₁ ξ₂ ρ₁ ρ₂ ρ ⇒
  𝜞⟦ Ξ ⊢ Γ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ γ₁ γ₂ ⇒
  𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
    ξ₁ ξ₂
    (subst_tm δ₁ ρ₁ γ₁ t₁)
    (subst_tm δ₂ ρ₂ γ₂ t₂).

Definition 𝓥_EV_HV_V_open (T : ty EV HV ∅) v₁ v₂ : IProp :=
  ∀ᵢ ξ₁ ξ₂ δ₁ δ₂ δ ρ₁ ρ₂ ρ γ₁ γ₂,
  (𝜩 Ξ ξ₁ ξ₂)ᵢ ⇒
  closed_δ ξ₁ ξ₂ δ ⇒
  (closed_ρ ξ₁ ξ₂ ρ₁ ρ₂)ᵢ ⇒
  𝑷⟦ ⊢ P ⟧ ξ₁ ξ₂ ρ₁ ρ₂ ρ ⇒
  𝜞⟦ Ξ ⊢ Γ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ γ₁ γ₂ ⇒
  𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
    ξ₁ ξ₂
    (subst_val δ₁ ρ₁ γ₁ v₁)
    (subst_val δ₂ ρ₂ γ₂ v₂).

Definition 𝓗_EV_HV_V_open (𝔽 : F) (ℓ : lbl HV ∅) h₁ h₂ : IProp :=
  ∀ᵢ ξ₁ ξ₂ δ₁ δ₂ δ ρ₁ ρ₂ ρ γ₁ γ₂,
  (𝜩 Ξ ξ₁ ξ₂)ᵢ ⇒
  closed_δ ξ₁ ξ₂ δ ⇒
  (closed_ρ ξ₁ ξ₂ ρ₁ ρ₂)ᵢ ⇒
  𝑷⟦ ⊢ P ⟧ ξ₁ ξ₂ ρ₁ ρ₂ ρ ⇒
  𝜞⟦ Ξ ⊢ Γ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ γ₁ γ₂ ⇒
  𝓗⟦ Ξ ⊢ 𝔽 # ℓ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
    ξ₁ ξ₂
    (subst_hd δ₁ ρ₁ γ₁ h₁)
    (subst_hd δ₂ ρ₂ γ₂ h₂).

Definition 𝓚_EV_HV_V_open (Ta Tb : ty EV HV ∅) (𝓔a 𝓔b : eff EV HV ∅) K₁ K₂ : IProp :=
  ∀ᵢ ξ₁ ξ₂ δ₁ δ₂ δ ρ₁ ρ₂ ρ γ₁ γ₂,
  (𝜩 Ξ ξ₁ ξ₂)ᵢ ⇒
  closed_δ ξ₁ ξ₂ δ ⇒
  (closed_ρ ξ₁ ξ₂ ρ₁ ρ₂)ᵢ ⇒
  𝑷⟦ ⊢ P ⟧ ξ₁ ξ₂ ρ₁ ρ₂ ρ ⇒
  𝜞⟦ Ξ ⊢ Γ ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ γ₁ γ₂ ⇒
  𝓚⟦ Ξ ⊢ Ta # 𝓔a ⇢ Tb # 𝓔b ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
    ξ₁ ξ₂
    (subst_ktx δ₁ ρ₁ γ₁ K₁)
    (subst_ktx δ₂ ρ₂ γ₂ K₂).

End section_EV_HV_V_open.

Notation "⟦ Ξ P Γ ⊢ t₁ '≼ˡᵒᵍ' t₂ : T # 𝓔 ⟧" := (𝓣_EV_HV_V_open Ξ P Γ T 𝓔 t₁ t₂)
  (Ξ at level 0, P at level 0, Γ at level 0,
    t₁ at level 0, t₂ at level 0, T at level 0).

Notation "⟦ Ξ P Γ ⊢ v₁ '≼ˡᵒᵍᵥ' v₂ : T ⟧" := (𝓥_EV_HV_V_open Ξ P Γ T v₁ v₂)
  (Ξ at level 0, P at level 0, Γ at level 0,
    v₁ at level 0, v₂ at level 0).

Notation "⟦ Ξ P Γ ⊢ h₁ '≼ˡᵒᵍₕ' h₂ : 𝔽 # ℓ ⟧" := (𝓗_EV_HV_V_open Ξ P Γ 𝔽 ℓ h₁ h₂)
  (Ξ at level 0, P at level 0, Γ at level 0,
    h₁ at level 0, h₂ at level 0, 𝔽 at level 0).

Notation "⟦ Ξ P Γ ⊢ K₁ '≼ˡᵒᵍ' K₂ : Ta # 𝓔a ⇢ Tb # 𝓔b ⟧" :=
  (𝓚_EV_HV_V_open Ξ P Γ Ta Tb 𝓔a 𝓔b K₁ K₂)
  (Ξ at level 0, P at level 0, Γ at level 0,
    K₁ at level 0, K₂ at level 0, Ta at level 0, Tb at level 0).


Section section_EV_HV_V_L_open.
Context (EV HV V L : Set).
Context (Π : LEnv EV HV L).
Context (P : HV → F).
Context (Γ : V → ty EV HV L).

Definition 𝓣_EV_HV_V_L_open T 𝓔 t₁ t₂ : IProp :=
∀ᵢ Ξ f,
(XLEnv Ξ Π f)ᵢ ⇒
⟦ Ξ P (L_bind_ty f ∘ Γ) ⊢ (L_bind_tm f t₁) ≼ˡᵒᵍ (L_bind_tm f t₂) :
  (L_bind_ty f T) # (L_bind_eff f 𝓔) ⟧.

Definition 𝓥_EV_HV_V_L_open T v₁ v₂ : IProp :=
∀ᵢ Ξ f,
(XLEnv Ξ Π f)ᵢ ⇒
⟦ Ξ P (L_bind_ty f ∘ Γ) ⊢ (L_bind_val f v₁) ≼ˡᵒᵍᵥ (L_bind_val f v₂) :
  (L_bind_ty f T) ⟧.

Definition 𝓚_EV_HV_V_L_open Ta Tb 𝓔a 𝓔b K₁ K₂ : IProp :=
∀ᵢ Ξ f,
(XLEnv Ξ Π f)ᵢ ⇒
⟦ Ξ P (L_bind_ty f ∘ Γ) ⊢ (L_bind_ktx f K₁) ≼ˡᵒᵍ (L_bind_ktx f K₂) :
  (L_bind_ty f Ta) # (L_bind_eff f 𝓔a) ⇢ (L_bind_ty f Tb) # (L_bind_eff f 𝓔b) ⟧.

Definition 𝓗_EV_HV_V_L_open 𝔽 ℓ h₁ h₂ : IProp :=
∀ᵢ Ξ f,
(XLEnv Ξ Π f)ᵢ ⇒
⟦ Ξ P (L_bind_ty f ∘ Γ) ⊢ (L_bind_hd f h₁) ≼ˡᵒᵍₕ (L_bind_hd f h₂) : 𝔽 # (L_bind_lbl f ℓ) ⟧.

End section_EV_HV_V_L_open.

Notation "【 Π P Γ ⊢ t₁ '≼ˡᵒᵍ' t₂ : T # 𝓔 】" := (𝓣_EV_HV_V_L_open Π P Γ T 𝓔 t₁ t₂)
  (Π at level 0, P at level 0, Γ at level 0, t₁ at level 0, t₂ at level 0, T at level 0).

Notation "【 Π P Γ ⊢ v₁ '≼ˡᵒᵍᵥ' v₂ : T 】" := (𝓥_EV_HV_V_L_open Π P Γ T v₁ v₂)
  (Π at level 0, P at level 0, Γ at level 0, v₁ at level 0, v₂ at level 0).

(* Notation "【 Π P Γ ⊢ K₁ '≼ˡᵒᵍ' K₂ : Ta # 𝓔a ⇢ Tb # 𝓔b 】" :=
  (𝓚_EV_HV_V_L_open Π P Γ Ta Tb 𝓔a 𝓔b K₁ K₂)
  (Π at level 0, Γ at level 0, K₁ at level 0, K₂ at level 0, Ta at level 0, Tb at level 0).

Notation "【 Π P Γ ⊢ h₁ '≼ˡᵒᵍₕ' h₂ : 𝔽 # ℓ 】" := (𝓗_EV_HV_V_open Π P Γ 𝔽 ℓ h₁ h₂)
  (Π at level 0, P at level 0, Γ at level 0,
    h₁ at level 0, h₂ at level 0, 𝔽 at level 0). *)