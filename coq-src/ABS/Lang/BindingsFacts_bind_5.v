Require Import Lang.Syntax Lang.Bindings.
Require Import Lang.BindingsFacts_map_0.
Require Import Lang.BindingsFacts_map_1.
Require Import Lang.BindingsFacts_bind_0.
Require Import Lang.BindingsFacts_bind_2.
Require Import Lang.BindingsFacts_bind_3.
Require Import Lang.BindingsFacts_bind_4.
Set Implicit Arguments.

Section section_EV_bind_bind.

Local Fact EV_bind_bind_aux1 (EV₁ EV₂ EV₃ HV L : Set)
  (f₁ : EV₁ → eff EV₂ HV L) (f₂ : EV₂ → eff EV₃ HV L)
  (g : EV₁ → eff EV₃ HV L)
  (Hfg : ∀ α, EV_bind_eff f₂ (f₁ α) = g α) :
  ∀ α : inc EV₁, EV_bind_eff (EV_lift_inc f₂) (EV_lift_inc f₁ α) = EV_lift_inc g α.
Proof.
  destruct α ; simpl ; [ crush | ].
  rewrite <- Hfg.
  repeat erewrite EV_bind_map_eff ; crush.
Qed.

Local Fact EV_bind_bind_aux2 (EV₁ EV₂ EV₃ HV L : Set)
  (f₁ : EV₁ → eff EV₂ HV L) (f₂ : EV₂ → eff EV₃ HV L)
  (g : EV₁ → eff EV₃ HV L)
  (Hfg : ∀ α, EV_bind_eff f₂ (f₁ α) = g α) :
  ∀ α : EV₁,
  EV_bind_eff (HV_shift_eff ∘ f₂) ((HV_shift_eff ∘ f₁) α) = (HV_shift_eff ∘ g) α.
Proof.
  intro ; unfold compose.
  rewrite <- Hfg.
  erewrite EV_bind_HV_map_eff ; crush.
Qed.

Local Fact EV_bind_bind_aux3 (EV₁ EV₂ EV₃ HV L : Set)
  (f₁ : EV₁ → eff EV₂ HV L) (f₂ : EV₂ → eff EV₃ HV L)
  (g : EV₁ → eff EV₃ HV L)
  (Hfg : ∀ α, EV_bind_eff f₂ (f₁ α) = g α) :
  ∀ α : EV₁,
  EV_bind_eff (L_shift_eff ∘ f₂) ((L_shift_eff ∘ f₁) α) = (L_shift_eff ∘ g) α.
Proof.
  intro ; unfold compose ; rewrite <- Hfg.
  erewrite EV_bind_L_map_eff ; crush.
Qed.

Hint Resolve EV_bind_bind_aux1 EV_bind_bind_aux2 EV_bind_bind_aux3.

Fixpoint
  EV_bind_bind_ef (EV₁ EV₂ EV₃ HV L : Set)
  (f₁ : EV₁ → eff EV₂ HV L) (f₂ : EV₂ → eff EV₃ HV L)
  (g : EV₁ → eff EV₃ HV L)
  (Hfg : ∀ α, EV_bind_eff f₂ (f₁ α) = g α)
  (ε : ef EV₁ HV L) :
  EV_bind_eff f₂ (EV_bind_ef f₁ ε) = EV_bind_ef g ε
.
Proof.
+ destruct ε ; simpl ;
  repeat erewrite EV_bind_bind_lbl ;
  crush.
Qed.

Fixpoint
  EV_bind_bind_eff (EV₁ EV₂ EV₃ HV L : Set)
  (f₁ : EV₁ → eff EV₂ HV L) (f₂ : EV₂ → eff EV₃ HV L)
  (g : EV₁ → eff EV₃ HV L)
  (Hfg : ∀ α, EV_bind_eff f₂ (f₁ α) = g α)
  (𝓔 : eff EV₁ HV L) {struct 𝓔} :
  EV_bind_eff f₂ (EV_bind_eff f₁ 𝓔) = EV_bind_eff g 𝓔
.
Proof.
+ destruct 𝓔 ; simpl ; [ crush | ].
  rewrite <- EV_bind_eff_app.
  erewrite EV_bind_bind_ef, EV_bind_bind_eff ; crush.
Qed.

Fixpoint
  EV_bind_bind_ty (EV₁ EV₂ EV₃ HV L : Set)
  (f₁ : EV₁ → eff EV₂ HV L) (f₂ : EV₂ → eff EV₃ HV L)
  (g : EV₁ → eff EV₃ HV L)
  (Hfg : ∀ α, EV_bind_eff f₂ (f₁ α) = g α)
  (T : ty EV₁ HV L) {struct T} :
  EV_bind_ty f₂ (EV_bind_ty f₁ T) = EV_bind_ty g T.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EV_bind_bind_ty ;
  repeat erewrite EV_bind_bind_eff ;
  crush.
Qed.

Fixpoint
  EV_bind_bind_hd (EV₁ EV₂ EV₃ HV V L : Set)
  (f₁ : EV₁ → eff EV₂ HV L) (f₂ : EV₂ → eff EV₃ HV L)
  (g : EV₁ → eff EV₃ HV L)
  (Hf : ∀ α, EV_bind_eff f₂ (f₁ α) = g α)
  (h : hd EV₁ HV V L) {struct h} :
  EV_bind_hd f₂ (EV_bind_hd f₁ h) = EV_bind_hd g h
with
  EV_bind_bind_tm (EV₁ EV₂ EV₃ HV V L : Set)
  (f₁ : EV₁ → eff EV₂ HV L) (f₂ : EV₂ → eff EV₃ HV L)
  (g : EV₁ → eff EV₃ HV L)
  (Hf : ∀ α, EV_bind_eff f₂ (f₁ α) = g α)
  (t : tm EV₁ HV V L) {struct t} :
  EV_bind_tm f₂ (EV_bind_tm f₁ t) = EV_bind_tm g t
with
  EV_bind_bind_val (EV₁ EV₂ EV₃ HV V L : Set)
  (f₁ : EV₁ → eff EV₂ HV L) (f₂ : EV₂ → eff EV₃ HV L)
  (g : EV₁ → eff EV₃ HV L)
  (Hf : ∀ α, EV_bind_eff f₂ (f₁ α) = g α)
  (v : val EV₁ HV V L) {struct v} :
  EV_bind_val f₂ (EV_bind_val f₁ v) = EV_bind_val g v.
Proof.
+ destruct h ; simpl ;
  repeat erewrite EV_bind_bind_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite EV_bind_bind_ty ;
  repeat erewrite EV_bind_bind_eff ;
  repeat erewrite EV_bind_bind_hd ;
  repeat erewrite EV_bind_bind_val ;
  repeat erewrite EV_bind_bind_tm ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite EV_bind_bind_tm ;
  repeat erewrite EV_bind_bind_hd ;
  crush.
Qed.

End section_EV_bind_bind.


Section section_HV_bind_bind.

Local Fact HV_bind_bind_aux1
  (EV HV₁ HV₂ HV₃ V L : Set)
  (f₁ : HV₁ → hd EV HV₂ V L) (f₂ : HV₂ → hd EV HV₃ V L)
  (g : HV₁ → hd EV HV₃ V L)
  (Hfg : ∀ p, HV_bind_hd f₂ (f₁ p) = g p) :
  ∀ p : inc HV₁, HV_bind_hd (HV_lift_inc f₂) (HV_lift_inc f₁ p) = HV_lift_inc g p.
Proof.
  destruct p ; simpl ; [ trivial | ].
  rewrite <- Hfg.
  erewrite HV_bind_map_hd ; crush.
Qed.

Local Fact HV_bind_bind_aux2
  (EV HV₁ HV₂ HV₃ V L : Set)
  (f₁ : HV₁ → hd EV HV₂ V L) (f₂ : HV₂ → hd EV HV₃ V L)
  (g : HV₁ → hd EV HV₃ V L)
  (Hfg : ∀ p, HV_bind_hd f₂ (f₁ p) = g p) :
  ∀ p : HV₁,
  HV_bind_hd (L_shift_hd ∘ f₂) ((L_shift_hd ∘ f₁) p) = (L_shift_hd ∘ g) p.
Proof.
  intro ; unfold compose ; rewrite <- Hfg.
  erewrite HV_bind_L_map_hd ; crush.
Qed.

Hint Resolve HV_bind_bind_aux1 HV_bind_bind_aux2.
Hint Rewrite lbl_HV_map_hd lbl_EV_map_hd.

Definition
  HV_bind_bind_lbl
  (EV HV₁ HV₂ HV₃ V V' L : Set)
  (f₁ : HV₁ → hd EV HV₂ V L) (f₂ : HV₂ → hd EV HV₃ V' L)
  (g : HV₁ → hd EV HV₃ V' L)
  (Hfg : ∀ p, HV_bind_lbl f₂ (lbl_hd (f₁ p)) = lbl_hd (g p))
  (ℓ : lbl HV₁ L) :
  HV_bind_lbl f₂ (HV_bind_lbl f₁ ℓ) = HV_bind_lbl g ℓ
.
Proof.
  destruct ℓ ; crush.
Qed.

Definition
  HV_bind_bind_ef
  (EV HV₁ HV₂ HV₃ V V' L : Set)
  (f₁ : HV₁ → hd EV HV₂ V L) (f₂ : HV₂ → hd EV HV₃ V' L)
  (g : HV₁ → hd EV HV₃ V' L)
  (Hfg : ∀ p, HV_bind_lbl f₂ (lbl_hd (f₁ p)) = lbl_hd (g p))
  (ε : ef EV HV₁ L) :
  HV_bind_ef f₂ (HV_bind_ef f₁ ε) = HV_bind_ef g ε
.
Proof.
  destruct ε ; simpl ;
  repeat erewrite HV_bind_bind_lbl ;
  crush.
Qed.

Fixpoint
  HV_bind_bind_eff
  (EV HV₁ HV₂ HV₃ V V' L : Set)
  (f₁ : HV₁ → hd EV HV₂ V L) (f₂ : HV₂ → hd EV HV₃ V' L)
  (g : HV₁ → hd EV HV₃ V' L)
  (Hfg : ∀ p, HV_bind_lbl f₂ (lbl_hd (f₁ p)) = lbl_hd (g p))
  (𝓔 : eff EV HV₁ L) {struct 𝓔} :
  HV_bind_eff f₂ (HV_bind_eff f₁ 𝓔) = HV_bind_eff g 𝓔
.
Proof.
  destruct 𝓔 ; simpl ;
  repeat erewrite HV_bind_bind_ef ;
  repeat erewrite HV_bind_bind_eff ;
  crush.
Qed.

Fixpoint
  HV_bind_bind_ty
  (EV HV₁ HV₂ HV₃ V V' L : Set)
  (f₁ : HV₁ → hd EV HV₂ V L) (f₂ : HV₂ → hd EV HV₃ V' L)
  (g : HV₁ → hd EV HV₃ V' L)
  (Hfg : ∀ p, HV_bind_lbl f₂ (lbl_hd (f₁ p)) = lbl_hd (g p))
  (T : ty EV HV₁ L) {struct T} :
  HV_bind_ty f₂ (HV_bind_ty f₁ T) = HV_bind_ty g T.
Proof.
+ destruct T ; simpl ;
  repeat erewrite HV_bind_bind_ty ;
  repeat erewrite HV_bind_bind_eff ;
  try reflexivity ;
  try assumption.
  { intro ; unfold compose.
    repeat rewrite lbl_EV_map_hd.
    rewrite <- Hfg.
    clear ; destruct (lbl_hd (f₁ p)) ; crush.
  }
  { intro x ; destruct x ; simpl ; [ crush | ].
    repeat rewrite lbl_HV_map_hd.
    rewrite <- Hfg.
    erewrite HV_bind_map_lbl ; crush.
  }
Qed.

Fixpoint
  HV_bind_bind_hd
  (EV HV₁ HV₂ HV₃ V L : Set)
  (f₁ : HV₁ → hd EV HV₂ V L) (f₂ : HV₂ → hd EV HV₃ V L)
  (g : HV₁ → hd EV HV₃ V L)
  (Hfg : ∀ p, HV_bind_hd f₂ (f₁ p) = g p)
  (h : hd EV HV₁ V L) {struct h} :
  HV_bind_hd f₂ (HV_bind_hd f₁ h) = HV_bind_hd g h
with
  HV_bind_bind_tm
  (EV HV₁ HV₂ HV₃ V L : Set)
  (f₁ : HV₁ → hd EV HV₂ V L) (f₂ : HV₂ → hd EV HV₃ V L)
  (g : HV₁ → hd EV HV₃ V L)
  (Hfg : ∀ p, HV_bind_hd f₂ (f₁ p) = g p)
  (t : tm EV HV₁ V L) {struct t} :
  HV_bind_tm f₂ (HV_bind_tm f₁ t) = HV_bind_tm g t
with
  HV_bind_bind_val
  (EV HV₁ HV₂ HV₃ V L : Set)
  (f₁ : HV₁ → hd EV HV₂ V L) (f₂ : HV₂ → hd EV HV₃ V L)
  (g : HV₁ → hd EV HV₃ V L)
  (Hfg : ∀ p, HV_bind_hd f₂ (f₁ p) = g p)
  (v : val EV HV₁ V L) {struct v} :
  HV_bind_val f₂ (HV_bind_val f₁ v) = HV_bind_val g v.
Proof.
+ destruct h ; simpl ;
  repeat erewrite HV_bind_bind_tm ;
  try reflexivity.
  { crush. }
  { intro ; unfold compose ; repeat erewrite HV_bind_V_map_hd ; crush. }
+ destruct t ; simpl ;
  repeat erewrite HV_bind_bind_ty ;
  repeat erewrite HV_bind_bind_eff ;
  repeat erewrite HV_bind_bind_hd ;
  repeat erewrite HV_bind_bind_val ;
  repeat erewrite HV_bind_bind_tm ;
  try reflexivity ;
  try assumption.
  { intro ; rewrite <- Hfg.
    erewrite lbl_HV_bind_hd ; crush.
  }
  { intro ; unfold compose ; erewrite HV_bind_V_map_hd ; crush. }
  { crush. }
+ destruct v ; simpl ;
  repeat erewrite HV_bind_bind_tm ;
  repeat erewrite HV_bind_bind_hd ;
  try reflexivity ;
  try assumption.
  { intro ; unfold compose ; erewrite HV_bind_V_map_hd ; crush. }
  { intro ; unfold compose ; erewrite HV_bind_EV_map_hd ; crush. }
  { intro x ; destruct x ; simpl ; [ crush | ].
    erewrite HV_bind_map_hd ; crush. }
Qed.

End section_HV_bind_bind.


Section section_V_bind_bind.

Local Fact V_bind_bind_aux1 (EV HV V₁ V₂ V₃ L : Set)
  (f₁ : V₁ → val EV HV V₂ L) (f₂ : V₂ → val EV HV V₃ L)
  (g : V₁ → val EV HV V₃ L)
  (Hf : ∀ x, V_bind_val f₂ (f₁ x) = g x) :
  ∀ x : inc V₁, V_bind_val (V_lift_inc f₂) (V_lift_inc f₁ x) = V_lift_inc g x.
Proof.
  destruct x ; simpl ; [ crush | ].
  rewrite <- Hf.
  erewrite V_bind_map_val ; crush.
Qed.

Local Fact V_bind_bind_aux2 (EV HV V₁ V₂ V₃ L : Set)
  (f₁ : V₁ → val EV HV V₂ L) (f₂ : V₂ → val EV HV V₃ L)
  (g : V₁ → val EV HV V₃ L)
  (Hf : ∀ x, V_bind_val f₂ (f₁ x) = g x) :
  ∀ x : V₁,
  V_bind_val (L_shift_val ∘ f₂) ((L_shift_val ∘ f₁) x) = (L_shift_val ∘ g) x.
Proof.
  intro ; unfold compose ; rewrite <- Hf.
  erewrite V_bind_L_map_val ; crush.
Qed.

Hint Resolve V_bind_bind_aux1 V_bind_bind_aux2.

Fixpoint
  V_bind_bind_hd (EV HV V₁ V₂ V₃ L : Set)
  (f₁ : V₁ → val EV HV V₂ L) (f₂ : V₂ → val EV HV V₃ L)
  (g : V₁ → val EV HV V₃ L)
  (Hf : ∀ x, V_bind_val f₂ (f₁ x) = g x)
  (h : hd EV HV V₁ L) {struct h} :
  V_bind_hd f₂ (V_bind_hd f₁ h) = V_bind_hd g h
with
  V_bind_bind_tm (EV HV V₁ V₂ V₃ L : Set)
  (f₁ : V₁ → val EV HV V₂ L) (f₂ : V₂ → val EV HV V₃ L)
  (g : V₁ → val EV HV V₃ L)
  (Hf : ∀ x, V_bind_val f₂ (f₁ x) = g x)
  (t : tm EV HV V₁ L) {struct t} :
  V_bind_tm f₂ (V_bind_tm f₁ t) = V_bind_tm g t
with
  V_bind_bind_val (EV HV V₁ V₂ V₃ L : Set)
  (f₁ : V₁ → val EV HV V₂ L) (f₂ : V₂ → val EV HV V₃ L)
  (g : V₁ → val EV HV V₃ L)
  (Hf : ∀ x, V_bind_val f₂ (f₁ x) = g x)
  (v : val EV HV V₁ L) {struct v} :
  V_bind_val f₂ (V_bind_val f₁ v) = V_bind_val g v.
Proof.
+ destruct h ; simpl ;
  repeat erewrite V_bind_bind_tm ;
  try reflexivity.
  { intro x ; destruct x as [ | x] ; simpl ; [ crush | ].
    destruct x ; simpl ; [ crush | ].
    repeat erewrite V_bind_map_val ; crush.
    simpl ; crush. }
+ destruct t ; simpl ;
  repeat erewrite V_bind_bind_ty ;
  repeat erewrite V_bind_bind_eff ;
  repeat erewrite V_bind_bind_hd ;
  repeat erewrite V_bind_bind_val ;
  repeat erewrite V_bind_bind_tm ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite V_bind_bind_hd ;
  repeat erewrite V_bind_bind_tm ;
  try reflexivity ;
  try assumption.
  { crush. }
  { intro x ; destruct x ; simpl ; [ crush | ].
    erewrite V_bind_map_val ; crush. }
  { intro ; unfold compose ; erewrite V_bind_EV_map_val ; crush. }
  { intro ; unfold compose ; erewrite V_bind_HV_map_val ; crush. }
Qed.

End section_V_bind_bind.


Section section_L_bind_bind.

Definition
  L_bind_bind_lid
  (L₁ L₂ L₃ : Set)
  (f₁ : L₁ → lid L₂) (f₂ : L₂ → lid L₃)
  (g : L₁ → lid L₃)
  (Q : ∀ α, L_bind_lid f₂ (f₁ α) = g α)
  (i : lid L₁) :
  L_bind_lid f₂ (L_bind_lid f₁ i) = L_bind_lid g i
.
Proof.
  destruct i ; simpl ; crush.
Qed.

Definition
  L_bind_bind_lbl
  (HV L₁ L₂ L₃ : Set)
  (f₁ : L₁ → lid L₂) (f₂ : L₂ → lid L₃)
  (g : L₁ → lid L₃)
  (Q : ∀ α, L_bind_lid f₂ (f₁ α) = g α)
  (ℓ : lbl HV L₁) :
  L_bind_lbl f₂ (L_bind_lbl f₁ ℓ) = L_bind_lbl g ℓ
.
Proof.
  destruct ℓ ; simpl ; [ crush | ].
  erewrite L_bind_bind_lid ; crush.
Qed.

Definition
  L_bind_bind_ef
  (EV HV V L₁ L₂ L₃ : Set)
  (f₁ : L₁ → lid L₂) (f₂ : L₂ → lid L₃)
  (g : L₁ → lid L₃)
  (Q : ∀ α, L_bind_lid f₂ (f₁ α) = g α)
  (ε : ef EV HV L₁) :
  L_bind_ef f₂ (L_bind_ef f₁ ε) = L_bind_ef g ε
.
Proof.
  destruct ε ; simpl ;
  repeat erewrite L_bind_bind_lbl ;
  crush.
Qed.

Fixpoint
  L_bind_bind_eff
  (EV HV V L₁ L₂ L₃ : Set)
  (f₁ : L₁ → lid L₂) (f₂ : L₂ → lid L₃)
  (g : L₁ → lid L₃)
  (Q : ∀ α, L_bind_lid f₂ (f₁ α) = g α)
  (𝓔 : eff EV HV L₁) {struct 𝓔} :
  L_bind_eff f₂ (L_bind_eff f₁ 𝓔) = L_bind_eff g 𝓔
.
Proof.
  destruct 𝓔 ; simpl ;
  repeat erewrite L_bind_bind_ef ;
  repeat erewrite L_bind_bind_eff ;
  crush.
Qed.

Fixpoint
  L_bind_bind_ty
  (EV HV V L₁ L₂ L₃ : Set)
  (f₁ : L₁ → lid L₂) (f₂ : L₂ → lid L₃)
  (g : L₁ → lid L₃)
  (Q : ∀ α, L_bind_lid f₂ (f₁ α) = g α)
  (T : ty EV HV L₁) {struct T} :
  L_bind_ty f₂ (L_bind_ty f₁ T) = L_bind_ty g T.
Proof.
+ destruct T ; simpl ;
  repeat erewrite L_bind_bind_ty ;
  repeat erewrite L_bind_bind_eff ;
  crush.
Qed.

Fixpoint
  L_bind_bind_hd
  (EV HV V L₁ L₂ L₃ : Set)
  (f₁ : L₁ → lid L₂) (f₂ : L₂ → lid L₃)
  (g : L₁ → lid L₃)
  (Q : ∀ α, L_bind_lid f₂ (f₁ α) = g α)
  (h : hd EV HV V L₁) {struct h} :
  L_bind_hd f₂ (L_bind_hd f₁ h) = L_bind_hd g h
with
  L_bind_bind_tm
  (EV HV V L₁ L₂ L₃ : Set)
  (f₁ : L₁ → lid L₂) (f₂ : L₂ → lid L₃)
  (g : L₁ → lid L₃)
  (Q : ∀ α, L_bind_lid f₂ (f₁ α) = g α)
  (t : tm EV HV V L₁) {struct t} :
  L_bind_tm f₂ (L_bind_tm f₁ t) = L_bind_tm g t
with
  L_bind_bind_val
  (EV HV V L₁ L₂ L₃ : Set)
  (f₁ : L₁ → lid L₂) (f₂ : L₂ → lid L₃)
  (g : L₁ → lid L₃)
  (Q : ∀ α, L_bind_lid f₂ (f₁ α) = g α)
  (v : val EV HV V L₁) {struct v} :
  L_bind_val f₂ (L_bind_val f₁ v) = L_bind_val g v.
Proof.
+ destruct h ; simpl ;
  repeat erewrite L_bind_bind_tm ;
  repeat erewrite L_bind_bind_lid ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite L_bind_bind_ty ;
  repeat erewrite L_bind_bind_eff ;
  repeat erewrite L_bind_bind_hd ;
  repeat erewrite L_bind_bind_val ;
  repeat erewrite L_bind_bind_tm ;
  try reflexivity ;
  try assumption.
  { intro x ; destruct x ; simpl ; [ crush | ].
    erewrite L_bind_map_lid ; crush. }
+ destruct v ; simpl ;
  repeat erewrite L_bind_bind_tm ;
  repeat erewrite L_bind_bind_hd ;
  crush.
Qed.

End section_L_bind_bind.
