Require Import Lang.Syntax Lang.Bindings_map Lang.BindingsFacts_map_0.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Section section_EV_map_id.

Definition
  EV_map_ef_id (EV HV L : Set) (f : EV → EV) (Hf : ∀ x, f x = x) (ε : ef EV HV L) :
  EV_map_ef f ε = ε.
Proof.
destruct ε ; crush.
Qed.

Hint Rewrite EV_map_ef_id.

Fixpoint
  EV_map_eff_id (EV HV L : Set) (f : EV → EV) (Hf : ∀ x, f x = x) (𝓔 : eff EV HV L) :
  EV_map_eff f 𝓔 = 𝓔.
Proof.
destruct 𝓔 ; crush.
Qed.

Hint Rewrite EV_map_eff_id.

Fixpoint
  EV_map_ty_id (EV HV L : Set) (f : EV → EV) (Hf : ∀ x, f x = x)
  (T : ty EV HV L) {struct T} :
  EV_map_ty f T = T
.
Proof.
destruct T ; crush.
Qed.

Hint Rewrite EV_map_ty_id.

Fixpoint
  EV_map_hd_id (EV HV V L : Set) (f : EV → EV) (Hf : ∀ x, f x = x)
  (h : hd EV HV V L) {struct h} :
  EV_map_hd f h = h
with
  EV_map_val_id (EV HV V L : Set) (f : EV → EV) (Hf : ∀ x, f x = x)
  (v : val EV HV V L) {struct v} :
  EV_map_val f v = v
with
  EV_map_tm_id (EV HV V L : Set) (f : EV → EV) (Hf : ∀ x, f x = x)
  (t : tm EV HV V L) {struct t} :
  EV_map_tm f t = t
.
Proof.
+ destruct h ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

Lemma EV_map_XEnv_id
(EV HV : Set) (f : EV → EV) (Hf : ∀ x, f x = x)
(Ξ : XEnv EV HV) :
EV_map_XEnv f Ξ = Ξ.
Proof.
induction Ξ as [ | Ξ X [T 𝓔] IHΞ ] using env_ind.
+ rewrite EV_map_XEnv_empty.
  reflexivity.
+ rewrite EV_map_XEnv_concat, EV_map_XEnv_single.
  erewrite IHΞ, EV_map_ty_id, EV_map_eff_id ; crush.
Qed.

End section_EV_map_id.


Section section_HV_map_id.

Definition
  HV_map_lbl_id (HV L : Set) (f : HV → HV) (Hf : ∀ x, f x = x)
  (ℓ : lbl HV L) :
  HV_map_lbl f ℓ = ℓ.
Proof.
destruct ℓ ; crush.
Qed.

Hint Rewrite HV_map_lbl_id.

Definition
  HV_map_ef_id (EV HV L : Set) (f : HV → HV) (Hf : ∀ x, f x = x)
  (ε : ef EV HV L) :
  HV_map_ef f ε = ε.
Proof.
destruct ε ; crush.
Qed.

Hint Rewrite HV_map_ef_id.

Fixpoint
  HV_map_eff_id (EV HV L : Set) (f : HV → HV) (Hf : ∀ x, f x = x)
  (𝓔 : eff EV HV L) :
  HV_map_eff f 𝓔 = 𝓔.
Proof.
destruct 𝓔 ; crush.
Qed.

Hint Rewrite HV_map_eff_id.

Fixpoint
  HV_map_ty_id (EV HV L : Set) (f : HV → HV) (Hf : ∀ x, f x = x)
  (T : ty EV HV L) {struct T} :
  HV_map_ty f T = T
.
Proof.
+ destruct T ; crush.
Qed.

Hint Rewrite HV_map_ty_id.

Fixpoint
  HV_map_hd_id (EV HV V L : Set) (f : HV → HV) (Hf : ∀ x, f x = x)
  (h : hd EV HV V L) {struct h} :
  HV_map_hd f h = h
with
  HV_map_val_id (EV HV V L : Set) (f : HV → HV) (Hf : ∀ x, f x = x)
  (v : val EV HV V L) {struct v} :
  HV_map_val f v = v
with
  HV_map_tm_id (EV HV V L : Set) (f : HV → HV) (Hf : ∀ x, f x = x)
  (t : tm EV HV V L) {struct t} :
  HV_map_tm f t = t
.
Proof.
+ destruct h ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

Lemma HV_map_XEnv_id
(EV HV : Set) (f : HV → HV) (Hf : ∀ x, f x = x)
(Ξ : XEnv EV HV) :
HV_map_XEnv f Ξ = Ξ.
Proof.
induction Ξ as [ | Ξ X [T 𝓔] IHΞ ] using env_ind.
+ rewrite HV_map_XEnv_empty.
  reflexivity.
+ rewrite HV_map_XEnv_concat, HV_map_XEnv_single.
  erewrite IHΞ, HV_map_ty_id, HV_map_eff_id ; crush.
Qed.

End section_HV_map_id.


Section section_L_map_id.

Definition
  L_map_lid_id (L : Set) (f : L → L) (Hf : ∀ x, f x = x)
  (ID : lid L) :
  L_map_lid f ID = ID.
Proof.
destruct ID ; crush.
Qed.

Hint Rewrite L_map_lid_id.

Definition
  L_map_lbl_id (HV L : Set) (f : L → L) (Hf : ∀ x, f x = x)
  (ℓ : lbl HV L) :
  L_map_lbl f ℓ = ℓ.
Proof.
destruct ℓ ; crush.
Qed.

Hint Rewrite L_map_lbl_id.

Definition
  L_map_ef_id (EV HV L : Set) (f : L → L) (Hf : ∀ x, f x = x)
  (ε : ef EV HV L) :
  L_map_ef f ε = ε.
Proof.
destruct ε ; crush.
Qed.

Hint Rewrite L_map_ef_id.

Fixpoint
  L_map_eff_id (EV HV L : Set) (f : L → L) (Hf : ∀ x, f x = x)
  (𝓔 : eff EV HV L) :
  L_map_eff f 𝓔 = 𝓔.
Proof.
destruct 𝓔 ; crush.
Qed.

Hint Rewrite L_map_eff_id.

Fixpoint
  L_map_ty_id (EV HV L : Set) (f : L → L) (Hf : ∀ x, f x = x)
  (T : ty EV HV L) {struct T} :
  L_map_ty f T = T
.
Proof.
+ destruct T ; crush.
Qed.

Hint Rewrite L_map_ty_id.

Fixpoint
  L_map_hd_id (EV HV V L : Set) (f : L → L) (Hf : ∀ x, f x = x)
  (h : hd EV HV V L) {struct h} :
  L_map_hd f h = h
with
  L_map_val_id (EV HV V L : Set) (f : L → L) (Hf : ∀ x, f x = x)
  (v : val EV HV V L) {struct v} :
  L_map_val f v = v
with
  L_map_tm_id (EV HV V L : Set) (f : L → L) (Hf : ∀ x, f x = x)
  (t : tm EV HV V L) {struct t} :
  L_map_tm f t = t
.
Proof.
+ destruct h ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

End section_L_map_id.


Fixpoint
  V_map_hd_id (EV HV V L : Set) (f : V → V) (Hf : ∀ x, f x = x)
  (h : hd EV HV V L) {struct h} :
  V_map_hd f h = h
with
  V_map_val_id (EV HV V L : Set) (f : V → V) (Hf : ∀ x, f x = x)
  (v : val EV HV V L) {struct v} :
  V_map_val f v = v
with
  V_map_tm_id (EV HV V L : Set) (f : V → V) (Hf : ∀ x, f x = x)
  (t : tm EV HV V L) {struct t} :
  V_map_tm f t = t
.
Proof.
+ destruct h ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

Fixpoint
  V_map_ktx_id (EV HV V L : Set) (f : V → V) (Hf : ∀ x, f x = x)
  (K : ktx EV HV V L) :
  V_map_ktx f K = K.
Proof.
destruct K ; simpl ;
repeat erewrite V_map_ktx_id ;
repeat erewrite V_map_val_id ;
repeat erewrite V_map_hd_id ;
repeat erewrite V_map_tm_id ;
crush.
Qed.
