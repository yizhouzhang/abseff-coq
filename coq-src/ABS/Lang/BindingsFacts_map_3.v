Require Import Lang.Syntax Lang.Bindings_map Lang.BindingsFacts_map_0.
Set Implicit Arguments.

Section section_EV_L_map.

Definition
  EV_L_map_ef (EV EV' HV L L' : Set) (f₁ : EV → EV') (f₂ : L → L')
  (ε : ef EV HV L) :
  EV_map_ef f₁ (L_map_ef f₂ ε) = L_map_ef f₂ (EV_map_ef f₁ ε)
.
Proof.
destruct ε ; crush.
Qed.

Hint Rewrite EV_L_map_ef.

Fixpoint
  EV_L_map_eff (EV EV' HV L L' : Set) (f₁ : EV → EV') (f₂ : L → L')
  (𝓔 : eff EV HV L) {struct 𝓔} :
  EV_map_eff f₁ (L_map_eff f₂ 𝓔) = L_map_eff f₂ (EV_map_eff f₁ 𝓔)
.
Proof.
destruct 𝓔 ; crush.
Qed.

Hint Rewrite EV_L_map_eff.

Fixpoint
  EV_L_map_ty (EV EV' HV L L' : Set) (f₁ : EV → EV') (f₂ : L → L')
  (T : ty EV HV L) {struct T} :
  EV_map_ty f₁ (L_map_ty f₂ T) = L_map_ty f₂ (EV_map_ty f₁ T)
.
Proof.
+ destruct T ; crush.
Qed.

Hint Rewrite EV_L_map_ty.

Fixpoint
  EV_L_map_hd (EV EV' HV V L L' : Set) (f₁ : EV → EV') (f₂ : L → L')
  (h : hd EV HV V L) {struct h} :
  EV_map_hd f₁ (L_map_hd f₂ h) = L_map_hd f₂ (EV_map_hd f₁ h)
with
  EV_L_map_val (EV EV' HV V L L' : Set) (f₁ : EV → EV') (f₂ : L → L')
  (v : val EV HV V L) {struct v} :
  EV_map_val f₁ (L_map_val f₂ v) = L_map_val f₂ (EV_map_val f₁ v)
with
  EV_L_map_tm (EV EV' HV V L L' : Set) (f₁ : EV → EV') (f₂ : L → L')
  (t : tm EV HV V L) {struct t} :
  EV_map_tm f₁ (L_map_tm f₂ t) = L_map_tm f₂ (EV_map_tm f₁ t)
.
Proof.
+ destruct h ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

End section_EV_L_map.


Section section_HV_L_map.

Definition
  HV_L_map_lbl (HV HV' L L' : Set) (f₁ : HV → HV') (f₂ : L → L')
  (ℓ : lbl HV L) :
  HV_map_lbl f₁ (L_map_lbl f₂ ℓ) = L_map_lbl f₂ (HV_map_lbl f₁ ℓ)
.
Proof.
destruct ℓ ; crush.
Qed.

Hint Rewrite HV_L_map_lbl.

Definition
  HV_L_map_ef (EV HV HV' L L' : Set) (f₁ : HV → HV') (f₂ : L → L')
  (ε : ef EV HV L) :
  HV_map_ef f₁ (L_map_ef f₂ ε) = L_map_ef f₂ (HV_map_ef f₁ ε)
.
Proof.
destruct ε ; crush.
Qed.

Hint Rewrite HV_L_map_ef.

Fixpoint
  HV_L_map_eff (EV HV HV' L L' : Set) (f₁ : HV → HV') (f₂ : L → L')
  (𝓔 : eff EV HV L) {struct 𝓔} :
  HV_map_eff f₁ (L_map_eff f₂ 𝓔) = L_map_eff f₂ (HV_map_eff f₁ 𝓔)
.
Proof.
destruct 𝓔 ; crush.
Qed.

Hint Rewrite HV_L_map_eff.

Fixpoint
  HV_L_map_ty (EV HV HV' L L' : Set) (f₁ : HV → HV') (f₂ : L → L')
  (T : ty EV HV L) {struct T} :
  HV_map_ty f₁ (L_map_ty f₂ T) = L_map_ty f₂ (HV_map_ty f₁ T)
.
Proof.
+ destruct T ; crush.
Qed.

Hint Rewrite HV_L_map_ty.

Fixpoint
  HV_L_map_hd (EV HV HV' V L L' : Set) (f₁ : HV → HV') (f₂ : L → L')
  (h : hd EV HV V L) {struct h} :
  HV_map_hd f₁ (L_map_hd f₂ h) = L_map_hd f₂ (HV_map_hd f₁ h)
with
  HV_L_map_val (EV HV HV' V L L' : Set) (f₁ : HV → HV') (f₂ : L → L')
  (v : val EV HV V L) {struct v} :
  HV_map_val f₁ (L_map_val f₂ v) = L_map_val f₂ (HV_map_val f₁ v)
with
  HV_L_map_tm (EV HV HV' V L L' : Set) (f₁ : HV → HV') (f₂ : L → L')
  (t : tm EV HV V L) {struct t} :
  HV_map_tm f₁ (L_map_tm f₂ t) = L_map_tm f₂ (HV_map_tm f₁ t)
.
Proof.
+ destruct h ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

End section_HV_L_map.


Section section_EV_HV_map.

Definition
  EV_HV_map_ef (EV EV' HV HV' L : Set) (f₁ : EV → EV') (f₂ : HV → HV')
  (ε : ef EV HV L) :
  EV_map_ef f₁ (HV_map_ef f₂ ε) = HV_map_ef f₂ (EV_map_ef f₁ ε)
.
Proof.
destruct ε ; crush.
Qed.

Hint Rewrite EV_HV_map_ef.

Fixpoint
  EV_HV_map_eff (EV EV' HV HV' L : Set) (f₁ : EV → EV') (f₂ : HV → HV')
  (𝓔 : eff EV HV L) {struct 𝓔} :
  EV_map_eff f₁ (HV_map_eff f₂ 𝓔) = HV_map_eff f₂ (EV_map_eff f₁ 𝓔)
.
Proof.
destruct 𝓔 ; crush.
Qed.

Hint Rewrite EV_HV_map_eff.

Fixpoint
  EV_HV_map_ty (EV EV' HV HV' L : Set) (f₁ : EV → EV') (f₂ : HV → HV')
  (T : ty EV HV L) {struct T} :
  EV_map_ty f₁ (HV_map_ty f₂ T) = HV_map_ty f₂ (EV_map_ty f₁ T)
.
Proof.
+ destruct T ; crush.
Qed.

Hint Rewrite EV_HV_map_ty.

Fixpoint
  EV_HV_map_hd (EV EV' HV HV' V L : Set) (f₁ : EV → EV') (f₂ : HV → HV')
  (h : hd EV HV V L) {struct h} :
  EV_map_hd f₁ (HV_map_hd f₂ h) = HV_map_hd f₂ (EV_map_hd f₁ h)
with
  EV_HV_map_val (EV EV' HV HV' V L : Set) (f₁ : EV → EV') (f₂ : HV → HV')
  (v : val EV HV V L) {struct v} :
  EV_map_val f₁ (HV_map_val f₂ v) = HV_map_val f₂ (EV_map_val f₁ v)
with
  EV_HV_map_tm (EV EV' HV HV' V L : Set) (f₁ : EV → EV') (f₂ : HV → HV')
  (t : tm EV HV V L) {struct t} :
  EV_map_tm f₁ (HV_map_tm f₂ t) = HV_map_tm f₂ (EV_map_tm f₁ t)
.
Proof.
+ destruct h ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

Lemma EV_HV_map_XEnv
(EV EV' HV HV' : Set) (f₁ : EV → EV') (f₂ : HV → HV')
(Ξ : XEnv EV HV) :
EV_map_XEnv f₁ (HV_map_XEnv f₂ Ξ) = HV_map_XEnv f₂ (EV_map_XEnv f₁ Ξ).
Proof.
induction Ξ as [ | ? ? [] ] using env_ind.
+ repeat rewrite EV_map_XEnv_empty, HV_map_XEnv_empty ; reflexivity.
+ repeat rewrite EV_map_XEnv_concat, HV_map_XEnv_concat,
    EV_map_XEnv_single, HV_map_XEnv_single.
  rewrite EV_HV_map_ty, EV_HV_map_eff, IHΞ.
  reflexivity.
Qed.

End section_EV_HV_map.


Fixpoint
  EV_V_map_hd (EV EV' HV V V' L : Set) (f₁ : EV → EV') (f₂ : V → V')
  (h : hd EV HV V L) {struct h} :
  EV_map_hd f₁ (V_map_hd f₂ h) = V_map_hd f₂ (EV_map_hd f₁ h)
with
  EV_V_map_val (EV EV' HV V V' L : Set) (f₁ : EV → EV') (f₂ : V → V')
  (v : val EV HV V L) {struct v} :
  EV_map_val f₁ (V_map_val f₂ v) = V_map_val f₂ (EV_map_val f₁ v)
with
  EV_V_map_tm (EV EV' HV V V' L : Set) (f₁ : EV → EV') (f₂ : V → V')
  (t : tm EV HV V L) {struct t} :
  EV_map_tm f₁ (V_map_tm f₂ t) = V_map_tm f₂ (EV_map_tm f₁ t)
.
Proof.
+ destruct h ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.


Fixpoint
  HV_V_map_hd (EV HV HV' V V' L : Set) (f₁ : HV → HV') (f₂ : V → V')
  (h : hd EV HV V L) {struct h} :
  HV_map_hd f₁ (V_map_hd f₂ h) = V_map_hd f₂ (HV_map_hd f₁ h)
with
  HV_V_map_val (EV HV HV' V V' L : Set) (f₁ : HV → HV') (f₂ : V → V')
  (v : val EV HV V L) {struct v} :
  HV_map_val f₁ (V_map_val f₂ v) = V_map_val f₂ (HV_map_val f₁ v)
with
  HV_V_map_tm (EV HV HV' V V' L : Set) (f₁ : HV → HV') (f₂ : V → V')
  (t : tm EV HV V L) {struct t} :
  HV_map_tm f₁ (V_map_tm f₂ t) = V_map_tm f₂ (HV_map_tm f₁ t)
.
Proof.
+ destruct h ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

Fixpoint
  V_L_map_hd (EV HV V V' L L' : Set) (f₁ : V → V') (f₂ : L → L')
  (h : hd EV HV V L) {struct h} :
  V_map_hd f₁ (L_map_hd f₂ h) = L_map_hd f₂ (V_map_hd f₁ h)
with
  V_L_map_val (EV HV V V' L L' : Set) (f₁ : V → V') (f₂ : L → L')
  (v : val EV HV V L) {struct v} :
  V_map_val f₁ (L_map_val f₂ v) = L_map_val f₂ (V_map_val f₁ v)
with
  V_L_map_tm (EV HV V V' L L' : Set) (f₁ : V → V') (f₂ : L → L')
  (t : tm EV HV V L) {struct t} :
  V_map_tm f₁ (L_map_tm f₂ t) = L_map_tm f₂ (V_map_tm f₁ t)
.
Proof.
+ destruct h ; crush.
+ destruct v ; crush.
+ destruct t ; crush.
Qed.

Fixpoint
  V_L_map_ktx (EV HV V V' L L' : Set) (f₁ : V → V') (f₂ : L → L')
  (K : ktx EV HV V L) {struct K} :
  V_map_ktx f₁ (L_map_ktx f₂ K) = L_map_ktx f₂ (V_map_ktx f₁ K).
Proof.
destruct K ; simpl ;
repeat rewrite V_L_map_ktx ;
repeat rewrite V_L_map_tm ;
repeat rewrite V_L_map_val ;
repeat rewrite V_L_map_hd ;
crush.
Qed.
