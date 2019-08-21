Require Import Lang.Syntax Lang.Bindings.
Require Import Lang.BindingsFacts_map_0.
Require Import Lang.BindingsFacts_bind_0.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Section section_EV_bind_id.

Definition
  EV_bind_ef_id
  (EV HV L : Set) (f : EV → eff EV HV L) (Hf : ∀ α, f α = [ef_var α])
  (ε : ef EV HV L) :
  EV_bind_ef f ε = [ε]
.
Proof.
destruct ε ; crush.
Qed.

Hint Rewrite EV_bind_ef_id.

Fixpoint
  EV_bind_eff_id
  (EV HV L : Set) (f : EV → eff EV HV L) (Hf : ∀ α, f α = [ef_var α])
  (𝓔 : eff EV HV L) {struct 𝓔} :
  EV_bind_eff f 𝓔 = 𝓔
.
Proof.
destruct 𝓔 ; crush.
Qed.

Hint Rewrite EV_bind_eff_id.

Fixpoint
  EV_bind_ty_id
  (EV HV L : Set) (f : EV → eff EV HV L) (Hf : ∀ α, f α = [ef_var α])
  (T : ty EV HV L) {struct T} :
  EV_bind_ty f T = T.
Proof.
+ destruct T ; crush.
Qed.

Hint Rewrite EV_bind_ty_id.

Fixpoint
  EV_bind_hd_id
  (EV HV V L : Set) (f : EV → eff EV HV L) (Hf : ∀ α, f α = [ef_var α])
  (h : hd EV HV V L) {struct h} :
  EV_bind_hd f h = h
with
  EV_bind_val_id
  (EV HV V L : Set) (f : EV → eff EV HV L) (Hf : ∀ α, f α = [ef_var α])
  (v : val EV HV V L) {struct v} :
  EV_bind_val f v = v
with
  EV_bind_tm_id
  (EV HV V L : Set) (f : EV → eff EV HV L) (Hf : ∀ α, f α = [ef_var α])
  (t : tm EV HV V L) {struct t} :
  EV_bind_tm f t = t.
Proof.
+ destruct h ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

Hint Rewrite EV_bind_val_id EV_bind_tm_id.

Lemma EV_bind_XEnv_id
(EV HV : Set) (f : EV → eff EV HV ∅) (Hf : ∀ α, f α = [ef_var α])
(Ξ : XEnv EV HV) :
EV_bind_XEnv f Ξ = Ξ.
Proof.
induction Ξ as [ | Ξ X [T 𝓔] IHΞ ] using env_ind.
+ rewrite EV_bind_XEnv_empty.
  reflexivity.
+ rewrite EV_bind_XEnv_concat, EV_bind_XEnv_single.
  erewrite IHΞ, EV_bind_ty_id, EV_bind_eff_id ; crush.
Qed.

End section_EV_bind_id.


Section section_HV_bind_id.

Definition
  HV_bind_lbl_id
  (EV HV V L : Set) (f : HV → hd EV HV V L) (Hf : ∀ α, lbl_hd (f α) = lbl_var α)
  (ℓ : lbl HV L) :
  HV_bind_lbl f ℓ = ℓ
.
Proof.
destruct ℓ ; crush.
Qed.

Hint Rewrite HV_bind_lbl_id.

Fixpoint
  HV_bind_ef_id
  (EV HV V L : Set) (f : HV → hd EV HV V L) (Hf : ∀ α, lbl_hd (f α) = lbl_var α)
  (ε : ef EV HV L) :
  HV_bind_ef f ε = ε
.
Proof.
destruct ε ; crush.
Qed.

Hint Rewrite HV_bind_ef_id.

Fixpoint
  HV_bind_eff_id
  (EV HV V L : Set) (f : HV → hd EV HV V L) (Hf : ∀ α, lbl_hd (f α) = lbl_var α)
  (𝓔 : eff EV HV L) {struct 𝓔} :
  HV_bind_eff f 𝓔 = 𝓔
.
Proof.
destruct 𝓔 ; crush.
Qed.

Hint Rewrite HV_bind_eff_id lbl_EV_map_hd lbl_HV_map_hd.

Fixpoint
  HV_bind_ty_id
  (EV HV V L : Set) (f : HV → hd EV HV V L) (Hf : ∀ α, lbl_hd (f α) = lbl_var α)
  (T : ty EV HV L) {struct T} :
  HV_bind_ty f T = T.
Proof.
+ destruct T ; simpl ; crush.
Qed.

Hint Rewrite HV_bind_ty_id.

Fixpoint
  HV_bind_hd_id
  (EV HV V L : Set) (f : HV → hd EV HV V L) (Hf : ∀ α, f α = hd_var α)
  (h : hd EV HV V L) {struct h} :
  HV_bind_hd f h = h
with
  HV_bind_val_id
  (EV HV V L : Set) (f : HV → hd EV HV V L) (Hf : ∀ α, f α = hd_var α)
  (v : val EV HV V L) {struct v} :
  HV_bind_val f v = v
with
  HV_bind_tm_id
  (EV HV V L : Set) (f : HV → hd EV HV V L) (Hf : ∀ α, f α = hd_var α)
  (t : tm EV HV V L) {struct t} :
  HV_bind_tm f t = t.
Proof.
+ destruct h ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

Hint Rewrite HV_bind_val_id HV_bind_tm_id.

Lemma HV_bind_XEnv_id
(EV HV V : Set) (f : HV → hd EV HV V ∅) (Hf : ∀ α, lbl_hd (f α) = lbl_var α)
(Ξ : XEnv EV HV) :
HV_bind_XEnv f Ξ = Ξ.
Proof.
induction Ξ as [ | Ξ X [T 𝓔] IHΞ ] using env_ind.
+ rewrite HV_bind_XEnv_empty.
  reflexivity.
+ rewrite HV_bind_XEnv_concat, HV_bind_XEnv_single.
  erewrite IHΞ, HV_bind_ty_id, HV_bind_eff_id ; crush.
Qed.

End section_HV_bind_id.


Section section_L_bind_id.

Definition
  L_bind_lid_id
  (L : Set) (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  (ID : lid L) :
  L_bind_lid f ID = ID
.
Proof.
destruct ID ; crush.
Qed.

Hint Rewrite L_bind_lid_id.

Definition
  L_bind_lbl_id
  (HV L : Set) (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  (ℓ : lbl HV L) :
  L_bind_lbl f ℓ = ℓ
.
Proof.
destruct ℓ ; crush.
Qed.

Hint Rewrite L_bind_lbl_id.

Fixpoint
  L_bind_ef_id
  (EV HV L : Set) (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  (ε : ef EV HV L) :
  L_bind_ef f ε = ε
.
Proof.
destruct ε ; crush.
Qed.

Hint Rewrite L_bind_ef_id.

Fixpoint
  L_bind_eff_id
  (EV HV L : Set) (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  (𝓔 : eff EV HV L) {struct 𝓔} :
  L_bind_eff f 𝓔 = 𝓔
.
Proof.
destruct 𝓔 ; crush.
Qed.

Hint Rewrite L_bind_eff_id.

Fixpoint
  L_bind_ty_id
  (EV HV L : Set) (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  (T : ty EV HV L) {struct T} :
  L_bind_ty f T = T.
Proof.
+ destruct T ; crush.
Qed.

Hint Rewrite L_bind_ty_id.

Fixpoint
  L_bind_hd_id
  (EV HV V L : Set) (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  (h : hd EV HV V L) {struct h} :
  L_bind_hd f h = h
with
  L_bind_val_id
  (EV HV V L : Set) (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  (v : val EV HV V L) {struct v} :
  L_bind_val f v = v
with
  L_bind_tm_id
  (EV HV V L : Set) (f : L → lid L) (Hf : ∀ α, f α = lid_b α)
  (t : tm EV HV V L) {struct t} :
  L_bind_tm f t = t.
Proof.
+ destruct h ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

Hint Rewrite L_bind_val_id L_bind_tm_id.

End section_L_bind_id.


Section section_V_bind_id.

Fixpoint
  V_bind_hd_id
  (EV HV V L : Set) (f : V → val EV HV V L) (Hf : ∀ x, f x = val_var x)
  (h : hd EV HV V L) {struct h} :
  V_bind_hd f h = h
with
  V_bind_val_id
  (EV HV V L : Set) (f : V → val EV HV V L) (Hf : ∀ x, f x = val_var x)
  (v : val EV HV V L) {struct v} :
  V_bind_val f v = v
with
  V_bind_tm_id
  (EV HV V L : Set) (f : V → val EV HV V L) (Hf : ∀ x, f x = val_var x)
  (t : tm EV HV V L) {struct t} :
  V_bind_tm f t = t.
Proof.
+ destruct h ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

Hint Rewrite V_bind_val_id V_bind_tm_id V_bind_hd_id.

Fixpoint
  V_bind_ktx_id
  (EV HV V L : Set) (f : V → val EV HV V L) (Hf : ∀ x, f x = val_var x)
  (K : ktx EV HV V L) :
  V_bind_ktx f K = K.
Proof.
destruct K ; crush.
Qed.

End section_V_bind_id.
