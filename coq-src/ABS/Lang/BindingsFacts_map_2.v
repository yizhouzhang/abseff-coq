Require Import Lang.Syntax Lang.Bindings_map Lang.BindingsFacts_map_0.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Section section_EV_map_map.

Definition
  EV_map_map_ef (EV1 EV2 EV3 HV L : Set)
  (f₁ : EV1 → EV2) (f₂ : EV2 → EV3) (g : EV1 → EV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (ε : ef EV1 HV L) :
  EV_map_ef f₂ (EV_map_ef f₁ ε) = EV_map_ef g ε
.
Proof.
destruct ε ; simpl ;
crush.
Qed.

Fixpoint
  EV_map_map_eff (EV1 EV2 EV3 HV L : Set)
  (f₁ : EV1 → EV2) (f₂ : EV2 → EV3) (g : EV1 → EV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (𝓔 : eff EV1 HV L) :
  EV_map_eff f₂ (EV_map_eff f₁ 𝓔) = EV_map_eff g 𝓔
.
Proof.
destruct 𝓔 ; simpl ;
repeat erewrite EV_map_map_ef ;
repeat erewrite EV_map_map_eff ;
crush.
Qed.

Fixpoint
  EV_map_map_ty (EV1 EV2 EV3 HV L : Set)
  (f₁ : EV1 → EV2) (f₂ : EV2 → EV3) (g : EV1 → EV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (T : ty EV1 HV L) {struct T} :
  EV_map_ty f₂ (EV_map_ty f₁ T) = EV_map_ty g T.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EV_map_map_ty ;
  repeat erewrite EV_map_map_eff ;
  crush.
Qed.


Fixpoint
  EV_map_map_hd (EV1 EV2 EV3 HV V L : Set)
  (f₁ : EV1 → EV2) (f₂ : EV2 → EV3) (g : EV1 → EV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (h : hd EV1 HV V L) {struct h} :
  EV_map_hd f₂ (EV_map_hd f₁ h) = EV_map_hd g h
with
  EV_map_map_val (EV1 EV2 EV3 HV V L : Set)
  (f₁ : EV1 → EV2) (f₂ : EV2 → EV3) (g : EV1 → EV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (v : val EV1 HV V L) {struct v} :
  EV_map_val f₂ (EV_map_val f₁ v) = EV_map_val g v
with
  EV_map_map_tm (EV1 EV2 EV3 HV V L : Set)
  (f₁ : EV1 → EV2) (f₂ : EV2 → EV3) (g : EV1 → EV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (t : tm EV1 HV V L) {struct t} :
  EV_map_tm f₂ (EV_map_tm f₁ t) = EV_map_tm g t.
Proof.
+ destruct h ; simpl ;
  repeat erewrite EV_map_map_hd ;
  repeat erewrite EV_map_map_tm ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite EV_map_map_hd ;
  repeat erewrite EV_map_map_ty ;
  repeat erewrite EV_map_map_tm ;
  repeat erewrite EV_map_map_eff ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite EV_map_map_ty ;
  repeat erewrite EV_map_map_eff ;
  repeat erewrite EV_map_map_val ;
  repeat erewrite EV_map_map_tm ;
  repeat erewrite EV_map_map_hd ;
  crush.
Qed.

Lemma EV_map_map_XEnv
(EV1 EV2 EV3 HV : Set)
(f₁ : EV1 → EV2) (f₂ : EV2 → EV3) (g : EV1 → EV3)
(Hf : ∀ x, f₂ (f₁ x) = g x)
(Ξ : XEnv EV1 HV) :
EV_map_XEnv f₂ (EV_map_XEnv f₁ Ξ) = EV_map_XEnv g Ξ.
Proof.
induction Ξ as [ | ? ? [] ] using env_ind.
+ repeat rewrite EV_map_XEnv_empty ; reflexivity.
+ repeat rewrite EV_map_XEnv_concat, EV_map_XEnv_single.
  erewrite EV_map_map_ty, EV_map_map_eff, IHΞ ; crush.
Qed.

End section_EV_map_map.


Section section_HV_map_map.

Definition
  HV_map_map_lbl (HV1 HV2 HV3 L : Set)
  (f₁ : HV1 → HV2) (f₂ : HV2 → HV3) (g : HV1 → HV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (ℓ : lbl HV1 L) :
  HV_map_lbl f₂ (HV_map_lbl f₁ ℓ) = HV_map_lbl g ℓ
.
Proof.
destruct ℓ ; simpl ;
crush.
Qed.

Definition
  HV_map_map_ef (EV HV1 HV2 HV3 L : Set)
  (f₁ : HV1 → HV2) (f₂ : HV2 → HV3) (g : HV1 → HV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (ε : ef EV HV1 L) :
  HV_map_ef f₂ (HV_map_ef f₁ ε) = HV_map_ef g ε
.
Proof.
destruct ε ; simpl ;
repeat erewrite HV_map_map_lbl ;
crush.
Qed.

Fixpoint
  HV_map_map_eff (EV HV1 HV2 HV3 L : Set)
  (f₁ : HV1 → HV2) (f₂ : HV2 → HV3) (g : HV1 → HV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (𝓔 : eff EV HV1 L) :
  HV_map_eff f₂ (HV_map_eff f₁ 𝓔) = HV_map_eff g 𝓔
.
Proof.
destruct 𝓔 ; simpl ;
repeat erewrite HV_map_map_ef ;
repeat erewrite HV_map_map_eff ;
crush.
Qed.

Fixpoint
  HV_map_map_ty (EV HV1 HV2 HV3 L : Set)
  (f₁ : HV1 → HV2) (f₂ : HV2 → HV3) (g : HV1 → HV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (T : ty EV HV1 L) {struct T} :
  HV_map_ty f₂ (HV_map_ty f₁ T) = HV_map_ty g T.
Proof.
+ destruct T ; simpl ;
  repeat erewrite HV_map_map_ty ;
  repeat erewrite HV_map_map_eff ;
  repeat erewrite HV_map_map_lbl ;
  crush.
Qed.


Fixpoint
  HV_map_map_hd (EV HV1 HV2 HV3 V L : Set)
  (f₁ : HV1 → HV2) (f₂ : HV2 → HV3) (g : HV1 → HV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (h : hd EV HV1 V L) {struct h} :
  HV_map_hd f₂ (HV_map_hd f₁ h) = HV_map_hd g h
with
  HV_map_map_val (EV HV1 HV2 HV3 V L : Set)
  (f₁ : HV1 → HV2) (f₂ : HV2 → HV3) (g : HV1 → HV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (v : val EV HV1 V L) {struct v} :
  HV_map_val f₂ (HV_map_val f₁ v) = HV_map_val g v
with
  HV_map_map_tm (EV HV1 HV2 HV3 V L : Set)
  (f₁ : HV1 → HV2) (f₂ : HV2 → HV3) (g : HV1 → HV3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (t : tm EV HV1 V L) {struct t} :
  HV_map_tm f₂ (HV_map_tm f₁ t) = HV_map_tm g t.
Proof.
+ destruct h ; simpl ;
  repeat erewrite HV_map_map_hd ;
  repeat erewrite HV_map_map_tm ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite HV_map_map_hd ;
  repeat erewrite HV_map_map_ty ;
  repeat erewrite HV_map_map_tm ;
  repeat erewrite HV_map_map_eff ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite HV_map_map_ty ;
  repeat erewrite HV_map_map_eff ;
  repeat erewrite HV_map_map_val ;
  repeat erewrite HV_map_map_tm ;
  repeat erewrite HV_map_map_hd ;
  crush.
Qed.

Lemma HV_map_map_XEnv
(EV HV1 HV2 HV3 : Set)
(f₁ : HV1 → HV2) (f₂ : HV2 → HV3) (g : HV1 → HV3)
(Hf : ∀ x, f₂ (f₁ x) = g x)
(Ξ : XEnv EV HV1) :
HV_map_XEnv f₂ (HV_map_XEnv f₁ Ξ) = HV_map_XEnv g Ξ.
Proof.
induction Ξ as [ | ? ? [] ] using env_ind.
+ repeat rewrite HV_map_XEnv_empty ; reflexivity.
+ repeat rewrite HV_map_XEnv_concat, HV_map_XEnv_single.
  erewrite HV_map_map_ty, HV_map_map_eff, IHΞ ; crush.
Qed.

End section_HV_map_map.


Section section_L_map_map.

Definition
  L_map_map_lid (L1 L2 L3 : Set)
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (id : lid L1) :
  L_map_lid f₂ (L_map_lid f₁ id) = L_map_lid g id
.
Proof.
destruct id ; simpl ; crush.
Qed.

Definition
  L_map_map_lbl (HV L1 L2 L3 : Set)
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (ℓ : lbl HV L1) :
  L_map_lbl f₂ (L_map_lbl f₁ ℓ) = L_map_lbl g ℓ
.
Proof.
destruct ℓ ; simpl ;
repeat erewrite L_map_map_lid ;
crush.
Qed.

Definition
  L_map_map_ef (EV HV L1 L2 L3 : Set)
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (ε : ef EV HV L1) :
  L_map_ef f₂ (L_map_ef f₁ ε) = L_map_ef g ε
.
Proof.
destruct ε ; simpl ;
repeat erewrite L_map_map_lbl ;
crush.
Qed.

Fixpoint
  L_map_map_eff (EV HV L1 L2 L3 : Set)
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (𝓔 : eff EV HV L1) :
  L_map_eff f₂ (L_map_eff f₁ 𝓔) = L_map_eff g 𝓔
.
Proof.
destruct 𝓔 ; simpl ;
repeat erewrite L_map_map_ef ;
repeat erewrite L_map_map_eff ;
crush.
Qed.

Fixpoint
  L_map_map_ty (EV HV L1 L2 L3 : Set)
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (T : ty EV HV L1) {struct T} :
  L_map_ty f₂ (L_map_ty f₁ T) = L_map_ty g T.
Proof.
+ destruct T ; simpl ;
  repeat erewrite L_map_map_ty ;
  repeat erewrite L_map_map_eff ;
  repeat erewrite L_map_map_lbl ;
  crush.
Qed.

Fixpoint
  L_map_map_hd (EV HV V L1 L2 L3 : Set)
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (h : hd EV HV V L1) {struct h} :
  L_map_hd f₂ (L_map_hd f₁ h) = L_map_hd g h
with
  L_map_map_val (EV HV V L1 L2 L3 : Set)
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (v : val EV HV V L1) {struct v} :
  L_map_val f₂ (L_map_val f₁ v) = L_map_val g v
with
  L_map_map_tm (EV HV V L1 L2 L3 : Set)
  (f₁ : L1 → L2) (f₂ : L2 → L3) (g : L1 → L3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (t : tm EV HV V L1) {struct t} :
  L_map_tm f₂ (L_map_tm f₁ t) = L_map_tm g t.
Proof.
+ destruct h ; simpl ;
  repeat erewrite L_map_map_hd ;
  repeat erewrite L_map_map_tm ;
  repeat erewrite L_map_map_lid ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite L_map_map_hd ;
  repeat erewrite L_map_map_lid ;
  repeat erewrite L_map_map_ty ;
  repeat erewrite L_map_map_eff ;
  repeat erewrite L_map_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite L_map_map_ty ;
  repeat erewrite L_map_map_eff ;
  repeat erewrite L_map_map_val ;
  repeat erewrite L_map_map_tm ;
  repeat erewrite L_map_map_hd ;
  crush.
Qed.

End section_L_map_map.


Fixpoint
  V_map_map_hd (EV HV V1 V2 V3 L : Set)
  (f₁ : V1 → V2) (f₂ : V2 → V3) (g : V1 → V3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (h : hd EV HV V1 L) {struct h} :
  V_map_hd f₂ (V_map_hd f₁ h) = V_map_hd g h
with
  V_map_map_val (EV HV V1 V2 V3 L : Set)
  (f₁ : V1 → V2) (f₂ : V2 → V3) (g : V1 → V3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (v : val EV HV V1 L) {struct v} :
  V_map_val f₂ (V_map_val f₁ v) = V_map_val g v
with
  V_map_map_tm (EV HV V1 V2 V3 L : Set)
  (f₁ : V1 → V2) (f₂ : V2 → V3) (g : V1 → V3)
  (Hf : ∀ x, f₂ (f₁ x) = g x)
  (t : tm EV HV V1 L) {struct t} :
  V_map_tm f₂ (V_map_tm f₁ t) = V_map_tm g t.
Proof.
+ destruct h ; simpl ;
  repeat erewrite V_map_map_hd ;
  repeat erewrite V_map_map_tm ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite V_map_map_hd ;
  repeat erewrite V_map_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite V_map_map_ty ;
  repeat erewrite V_map_map_eff ;
  repeat erewrite V_map_map_val ;
  repeat erewrite V_map_map_tm ;
  repeat erewrite V_map_map_hd ;
  crush.
Qed.
