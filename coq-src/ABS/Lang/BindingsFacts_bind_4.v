Require Import Lang.Syntax Lang.Bindings.
Require Import Lang.BindingsFacts_map_0.
Require Import Lang.BindingsFacts_map_1.
Require Import Lang.BindingsFacts_bind_0.
Require Import Lang.BindingsFacts_bind_2.
Require Import Lang.BindingsFacts_bind_3.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Section section_app.
Hint Rewrite app_assoc.

Lemma EV_bind_eff_app (EV EV' HV L : Set)
  (f : EV → eff EV' HV L) (𝓔₁ 𝓔₂ : eff EV HV L) :
  EV_bind_eff f 𝓔₁ ++ EV_bind_eff f 𝓔₂ = EV_bind_eff f (𝓔₁ ++ 𝓔₂).
Proof.
  induction 𝓔₁ ; crush.
Qed.

Lemma HV_bind_eff_app (EV HV HV' V L : Set)
  (f : HV → hd EV HV' V L) (𝓔₁ 𝓔₂ : eff EV HV L) :
  HV_bind_eff f 𝓔₁ ++ HV_bind_eff f 𝓔₂ = HV_bind_eff f (𝓔₁ ++ 𝓔₂).
Proof.
  induction 𝓔₁ ; crush.
Qed.

Lemma L_bind_eff_app (EV HV L L' : Set)
  (f : L → lid L') (𝓔₁ 𝓔₂ : eff EV HV L) :
  L_bind_eff f 𝓔₁ ++ L_bind_eff f 𝓔₂ = L_bind_eff f (𝓔₁ ++ 𝓔₂).
Proof.
  induction 𝓔₁ ; crush.
Qed.

End section_app.


Section section_EV_HV_bind.

Hint Rewrite lbl_EV_map_hd lbl_HV_map_hd lbl_V_map_hd lbl_L_map_hd.

Local Fact EV_HV_bind_val_aux1
  (EV EV' HV HV' V L : Set)
  (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV' L)
  (P : ∀ x, EV_bind_hd g₂ (f₁ x) = f₂ x) :
∀ x : HV, EV_bind_hd g₂ ((V_shift_hd ∘ f₁) x) = (V_shift_hd ∘ f₂) x.
Proof.
intro ; unfold compose ; erewrite EV_bind_V_map_hd ; crush.
Qed.

Local Fact EV_HV_bind_val_aux2
  (EV EV' HV HV' V L : Set)
  (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV' L)
  (Q : ∀ x, HV_bind_eff f₂ (g₁ x) = g₂ x) :
∀ x : EV, HV_bind_eff (V_shift_hd ∘ f₂) (g₁ x) = g₂ x.
Proof.
intro ; unfold compose ; erewrite HV_bind_xx_map_eff ; crush.
Qed.

Local Fact EV_HV_bind_val_aux3
  (EV EV' HV HV' V L : Set)
  (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV' L)
  (P : ∀ x, EV_bind_hd g₂ (f₁ x) = f₂ x) :
∀ x : HV, EV_bind_hd (L_shift_eff ∘ g₂) ((L_shift_hd ∘ f₁) x) = (L_shift_hd ∘ f₂) x.
Proof.
intro ; unfold compose ; erewrite EV_bind_L_map_hd ; crush.
Qed.

Local Fact EV_HV_bind_val_aux4
  (EV EV' HV HV' V L : Set)
  (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV' L)
  (Q : ∀ x, HV_bind_eff f₂ (g₁ x) = g₂ x) :
∀ x : EV, HV_bind_eff (L_shift_hd ∘ f₂) ((L_shift_eff ∘ g₁) x) = (L_shift_eff ∘ g₂) x.
Proof.
intro ; unfold compose ; erewrite HV_bind_L_map_eff ; crush.
Qed.

Local Fact EV_HV_bind_val_aux5
  (EV EV' HV HV' V L : Set)
  (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV' L)
  (P : ∀ x, EV_bind_hd g₂ (f₁ x) = f₂ x) :
∀ x : HV, EV_bind_hd (EV_lift_inc g₂) ((EV_shift_hd ∘ f₁) x) = (EV_shift_hd ∘ f₂) x.
Proof.
intro ; unfold compose ; erewrite EV_bind_map_hd ; crush.
Qed.

Local Fact EV_HV_bind_val_aux6
  (EV EV' HV HV' V L : Set)
  (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV' L)
  (Q : ∀ x, HV_bind_eff f₂ (g₁ x) = g₂ x) :
∀ x : inc EV, HV_bind_eff (EV_shift_hd ∘ f₂) (EV_lift_inc g₁ x) = EV_lift_inc g₂ x.
Proof.
destruct x ; simpl ; [ crush | ].
unfold compose ; erewrite HV_bind_EV_map_eff ; crush.
Qed.

Local Fact EV_HV_bind_val_aux7
  (EV EV' HV HV' V L : Set)
  (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV' L)
  (P : ∀ x, EV_bind_hd g₂ (f₁ x) = f₂ x) :
∀ x : inc HV, EV_bind_hd (HV_shift_eff ∘ g₂) (HV_lift_inc f₁ x) = HV_lift_inc f₂ x.
Proof.
destruct x ; simpl ; [ crush | ].
unfold compose ; erewrite EV_bind_HV_map_hd ; crush.
Qed.

Local Fact EV_HV_bind_val_aux8
  (EV EV' HV HV' V L : Set)
  (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV' L)
  (Q : ∀ x, HV_bind_eff f₂ (g₁ x) = g₂ x) :
∀ x : EV, HV_bind_eff (HV_lift_inc f₂) ((HV_shift_eff ∘ g₁) x) = (HV_shift_eff ∘ g₂) x.
Proof.
intro ; unfold compose ; erewrite HV_bind_map_eff ; crush.
Qed.

Hint Rewrite <- HV_bind_eff_app.

Definition
  EV_HV_bind_ef
  (EV EV' HV HV' V L : Set)
  (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV' L)
  (P : ∀ x, lbl_hd (EV_bind_hd g₂ (f₁ x)) = lbl_hd (f₂ x))
  (Q : ∀ x, HV_bind_eff f₂ (g₁ x) = g₂ x)
  (ε : ef EV HV L) :
  EV_bind_ef g₂ (HV_bind_ef f₁ ε) = HV_bind_eff f₂ (EV_bind_ef g₁ ε)
.
Proof.
destruct ε ; simpl ; [ crush | ].
erewrite HV_bind_xx_map_lbl with (f₂ := f₂) ; try reflexivity.
intro ; erewrite <- lbl_EV_bind_hd ; crush.
Qed.

Fixpoint
  EV_HV_bind_eff
  (EV EV' HV HV' V L : Set)
  (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV' L)
  (P : ∀ x, lbl_hd (EV_bind_hd g₂ (f₁ x)) = lbl_hd (f₂ x))
  (Q : ∀ x, HV_bind_eff f₂ (g₁ x) = g₂ x)
  (𝓔 : eff EV HV L) {struct 𝓔} :
  EV_bind_eff g₂ (HV_bind_eff f₁ 𝓔) = HV_bind_eff f₂ (EV_bind_eff g₁ 𝓔)
.
Proof.
destruct 𝓔 ; simpl ;
repeat erewrite EV_HV_bind_ef ;
repeat erewrite EV_HV_bind_eff ;
crush.
Qed.

Fixpoint
  EV_HV_bind_ty
  (EV EV' HV HV' V L : Set)
  (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV' L)
  (P : ∀ x, lbl_hd (EV_bind_hd g₂ (f₁ x)) = lbl_hd (f₂ x))
  (Q : ∀ x, HV_bind_eff f₂ (g₁ x) = g₂ x)
  (T : ty EV HV L) {struct T} :
  EV_bind_ty g₂ (HV_bind_ty f₁ T) = HV_bind_ty f₂ (EV_bind_ty g₁ T)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EV_HV_bind_ty ;
  repeat erewrite EV_HV_bind_eff ;
  repeat erewrite EV_HV_bind_ms ;
  try reflexivity ;
  try assumption.
  { intro ; unfold compose ; erewrite EV_bind_map_hd ; crush. }
  { intro x ; destruct x ; simpl ; [ crush | ].
    unfold compose ; erewrite HV_bind_EV_map_eff ; crush. }
  { intro x ; destruct x ; simpl ; [ crush | ].
    unfold compose ; erewrite EV_bind_HV_map_hd ; crush. }
  { intro ; unfold compose ; erewrite HV_bind_map_eff ; crush. }
Qed.

Fixpoint
  EV_HV_bind_hd
  (EV EV' HV HV' V L : Set)
  (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV' L)
  (P : ∀ x, EV_bind_hd g₂ (f₁ x) = f₂ x)
  (Q : ∀ x, HV_bind_eff f₂ (g₁ x) = g₂ x)
  (h : hd EV HV V L) {struct h} :
  EV_bind_hd g₂ (HV_bind_hd f₁ h) = HV_bind_hd f₂ (EV_bind_hd g₁ h)
with
  EV_HV_bind_tm
  (EV EV' HV HV' V L : Set)
  (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV' L)
  (P : ∀ x, EV_bind_hd g₂ (f₁ x) = f₂ x)
  (Q : ∀ x, HV_bind_eff f₂ (g₁ x) = g₂ x)
  (t : tm EV HV V L) {struct t} :
  EV_bind_tm g₂ (HV_bind_tm f₁ t) = HV_bind_tm f₂ (EV_bind_tm g₁ t)
with
  EV_HV_bind_val
  (EV EV' HV HV' V L : Set)
  (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV' L)
  (P : ∀ x, EV_bind_hd g₂ (f₁ x) = f₂ x)
  (Q : ∀ x, HV_bind_eff f₂ (g₁ x) = g₂ x)
  (v : val EV HV V L) {struct v} :
  EV_bind_val g₂ (HV_bind_val f₁ v) = HV_bind_val f₂ (EV_bind_val g₁ v).
Proof.
+ destruct h ; simpl ;
  repeat erewrite EV_HV_bind_tm ;
  try reflexivity.
  { crush. }
  { intro ; unfold compose ; rewrite <- P.
    repeat erewrite EV_bind_V_map_hd ; crush. }
  { intro ; unfold compose ; rewrite <- Q.
    erewrite HV_bind_xx_map_eff ; crush. }
+ destruct t ; simpl ;
  repeat erewrite EV_HV_bind_ty ;
  repeat erewrite EV_HV_bind_eff ;
  repeat erewrite EV_HV_bind_hd ;
  repeat erewrite EV_HV_bind_val ;
  repeat erewrite EV_HV_bind_tm ;
  try reflexivity ;
  try (apply EV_HV_bind_val_aux1 ; crush) ;
  try (apply EV_HV_bind_val_aux2 ; crush) ;
  try (apply EV_HV_bind_val_aux3 ; crush) ;
  try (apply EV_HV_bind_val_aux4 ; crush) ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite EV_HV_bind_tm ;
  repeat erewrite EV_HV_bind_hd ;
  try reflexivity ;
  try (apply EV_HV_bind_val_aux1 ; crush) ;
  try (apply EV_HV_bind_val_aux2 ; crush) ;
  try (apply EV_HV_bind_val_aux5 ; crush) ;
  try (apply EV_HV_bind_val_aux6 ; crush) ;
  try (apply EV_HV_bind_val_aux7 ; crush) ;
  try (apply EV_HV_bind_val_aux8 ; crush) ;
  crush.
Qed.

Lemma
  EV_HV_bind_XEnv
  EV EV' HV HV' V
  (f₁ : HV → hd EV HV' V ∅) (f₂ : HV → hd EV' HV' V ∅)
  (g₁ : EV → eff EV' HV ∅) (g₂ : EV → eff EV' HV' ∅)
  (P : ∀ x, lbl_hd (EV_bind_hd g₂ (f₁ x)) = lbl_hd (f₂ x))
  (Q : ∀ x, HV_bind_eff f₂ (g₁ x) = g₂ x)
  (Ξ : XEnv EV HV) :
  EV_bind_XEnv g₂ (HV_bind_XEnv f₁ Ξ) = HV_bind_XEnv f₂ (EV_bind_XEnv g₁ Ξ)
.
Proof.
induction Ξ as [ | ? ? [] ] using env_ind.
+ repeat (rewrite HV_bind_XEnv_empty || rewrite EV_bind_XEnv_empty).
  reflexivity.
+ repeat rewrite
    EV_bind_XEnv_concat, HV_bind_XEnv_concat,
    EV_bind_XEnv_single, HV_bind_XEnv_single.
  erewrite EV_HV_bind_ty, EV_HV_bind_eff, IHΞ ; crush.
Qed.

End section_EV_HV_bind.


Section section_EV_V_bind.

Local Fact EV_V_bind_aux1 (EV EV' HV V V' L : Set)
  (f₁ : V → val EV' HV V' L) (f₂ : V → val EV HV V' L)
  (g : EV → eff EV' HV L)
  (H : ∀ x, EV_bind_val g (f₂ x) = f₁ x) :
  ∀ x : inc V, EV_bind_val g (V_lift_inc f₂ x) = V_lift_inc f₁ x.
Proof.
  destruct x ; simpl ; [ crush | ].
  rewrite <- H.
  rewrite EV_bind_V_map_val ; crush.
Qed.

Local Fact EV_V_bind_aux2 (EV EV' HV V V' L : Set)
  (f₁ : V → val EV' HV V' L) (f₂ : V → val EV HV V' L)
  (g : EV → eff EV' HV L)
  (H : ∀ x, EV_bind_val g (f₂ x) = f₁ x) :
  ∀ x : V,
  EV_bind_val (L_shift_eff ∘ g) ((L_shift_val ∘ f₂) x) = (L_shift_val ∘ f₁) x.
Proof.
  intro ; unfold compose ; rewrite <- H.
  erewrite EV_bind_L_map_val ; crush.
Qed.

Local Fact EV_V_bind_aux3 (EV EV' HV V V' L : Set)
  (f₁ : V → val EV' HV V' L) (f₂ : V → val EV HV V' L)
  (g : EV → eff EV' HV L)
  (H : ∀ x, EV_bind_val g (f₂ x) = f₁ x) :
  ∀ x : V,
  EV_bind_val (EV_lift_inc g) ((EV_shift_val ∘ f₂) x) = (EV_shift_val ∘ f₁) x.
Proof.
intro ; unfold compose ; erewrite EV_bind_map_val ; crush.
Qed.

Local Fact EV_V_bind_aux4 (EV EV' HV V V' L : Set)
  (f₁ : V → val EV' HV V' L) (f₂ : V → val EV HV V' L)
  (g : EV → eff EV' HV L)
  (H : ∀ x, EV_bind_val g (f₂ x) = f₁ x) :
  ∀ x : V,
  EV_bind_val (HV_shift_eff ∘ g) ((HV_shift_val ∘ f₂) x) = (HV_shift_val ∘ f₁) x.
Proof.
intro ; unfold compose ; erewrite EV_bind_HV_map_val ; crush.
Qed.

Hint Resolve EV_V_bind_aux1 EV_V_bind_aux2 EV_V_bind_aux3 EV_V_bind_aux4.

Fixpoint
  EV_V_bind_hd (EV EV' HV V V' L : Set)
  (f₁ : V → val EV' HV V' L) (f₂ : V → val EV HV V' L)
  (g : EV → eff EV' HV L)
  (H : ∀ x, EV_bind_val g (f₂ x) = f₁ x)
  (h : hd EV HV V L) {struct h} :
  V_bind_hd f₁ (EV_bind_hd g h) = EV_bind_hd g (V_bind_hd f₂ h)
with
  EV_V_bind_tm (EV EV' HV V V' L : Set)
  (f₁ : V → val EV' HV V' L) (f₂ : V → val EV HV V' L)
  (g : EV → eff EV' HV L)
  (H : ∀ x, EV_bind_val g (f₂ x) = f₁ x)
  (t : tm EV HV V L) {struct t} :
  V_bind_tm f₁ (EV_bind_tm g t) = EV_bind_tm g (V_bind_tm f₂ t)
with
  EV_V_bind_val (EV EV' HV V V' L : Set)
  (f₁ : V → val EV' HV V' L) (f₂ : V → val EV HV V' L)
  (g : EV → eff EV' HV L)
  (H : ∀ x, EV_bind_val g (f₂ x) = f₁ x)
  (v : val EV HV V L) {struct v} :
  V_bind_val f₁ (EV_bind_val g v) = EV_bind_val g (V_bind_val f₂ v).
Proof.
+ destruct h ; simpl ;
  repeat erewrite EV_V_bind_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite EV_V_bind_val ;
  repeat erewrite EV_V_bind_hd ;
  repeat erewrite EV_V_bind_tm ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite EV_V_bind_hd ;
  repeat erewrite EV_V_bind_tm ;
  crush.
Qed.

End section_EV_V_bind.


Section section_HV_V_bind.

Hint Rewrite lbl_V_bind_hd.

Fixpoint
  HV_V_bind_hd (EV HV HV' V V' L : Set)
  (f₁ : V → val EV HV V' L) (f₂ : V → val EV HV' V' L)
  (g₁ : HV → hd EV HV' V L) (g₂ : HV → hd EV HV' V' L)
  (G : ∀ x, V_bind_hd f₂ (g₁ x) = g₂ x)
  (H : ∀ x, HV_bind_val g₂ (f₁ x) = f₂ x)
  (h : hd EV HV V L) {struct h} :
  V_bind_hd f₂ (HV_bind_hd g₁ h) = HV_bind_hd g₂ (V_bind_hd f₁ h)
with
  HV_V_bind_tm (EV HV HV' V V' L : Set)
  (f₁ : V → val EV HV V' L) (f₂ : V → val EV HV' V' L)
  (g₁ : HV → hd EV HV' V L) (g₂ : HV → hd EV HV' V' L)
  (G : ∀ x, V_bind_hd f₂ (g₁ x) = g₂ x)
  (H : ∀ x, HV_bind_val g₂ (f₁ x) = f₂ x)
  (t : tm EV HV V L) {struct t} :
  V_bind_tm f₂ (HV_bind_tm g₁ t) = HV_bind_tm g₂ (V_bind_tm f₁ t)
with
  HV_V_bind_val (EV HV HV' V V' L : Set)
  (f₁ : V → val EV HV V' L) (f₂ : V → val EV HV' V' L)
  (g₁ : HV → hd EV HV' V L) (g₂ : HV → hd EV HV' V' L)
  (G : ∀ x, V_bind_hd f₂ (g₁ x) = g₂ x)
  (H : ∀ x, HV_bind_val g₂ (f₁ x) = f₂ x)
  (v : val EV HV V L) {struct v} :
  V_bind_val f₂ (HV_bind_val g₁ v) = HV_bind_val g₂ (V_bind_val f₁ v).
Proof.
+ destruct h ; simpl ;
  repeat erewrite HV_V_bind_tm ;
  try reflexivity.
  { crush. }
  { intro ; unfold compose.
    repeat erewrite V_bind_map_hd ; crush.
    simpl ; crush. }
  { destruct x as [ | x ] ; simpl ; [ crush | ].
    destruct x as [ | x ] ; simpl ; [ crush | ].
    repeat erewrite HV_bind_V_map_val ; crush. }
+ destruct t ; simpl ;
  repeat erewrite HV_V_bind_hd ;
  repeat erewrite HV_V_bind_val ;
  repeat erewrite HV_V_bind_tm ;
  repeat erewrite HV_bind_xx_map_ty with (f₂ := g₂) ;
  repeat erewrite HV_bind_xx_map_eff with (f₂ := g₂) ;
  try reflexivity ;
  try assumption.
  { intro ; rewrite <- G ; crush. }
  { intro ; unfold compose ; erewrite V_bind_map_hd ; crush. }
  { destruct x ; simpl ; [ crush | ].
    unfold compose ; erewrite HV_bind_V_map_val ; crush. }
  { intro ; unfold compose ; erewrite V_bind_L_map_hd ; crush. }
  { intro ; unfold compose ; erewrite HV_bind_L_map_val ; crush. }
+ destruct v ; simpl ;
  repeat erewrite HV_V_bind_hd ;
  repeat erewrite HV_V_bind_tm ;
  try reflexivity ;
  try assumption.
  { crush. }
  { intro ; unfold compose ; erewrite V_bind_map_hd ; crush. }
  { destruct x ; simpl ; [ crush | ].
    unfold compose ; erewrite HV_bind_V_map_val ; crush. }
  { intro ; unfold compose ; erewrite V_bind_EV_map_hd ; crush. }
  { intro ; unfold compose ; erewrite HV_bind_EV_map_val ; crush. }
  { destruct x ; simpl ; [ crush | ].
    unfold compose ; erewrite V_bind_HV_map_hd ; crush. }
  { intro ; unfold compose ; erewrite HV_bind_map_val ; crush. }
Qed.

End section_HV_V_bind.


Section section_EV_L_bind.

Local Fact EV_L_bind_aux1
  (EV EV' HV L L' : Set)
  (f : L → lid L')
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV L')
  (Q : ∀ x, L_bind_eff f (g₁ x) = g₂ x) :
  ∀ x : inc EV, L_bind_eff f (EV_lift_inc g₁ x) = EV_lift_inc g₂ x.
Proof.
  intro x ; destruct x ; simpl ; [ crush | ].
  unfold compose.
  erewrite L_bind_EV_map_eff ; crush.
Qed.

Local Fact EV_L_bind_aux2
  (EV EV' HV L L' : Set)
  (f : L → lid L')
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV L')
  (Q : ∀ x, L_bind_eff f (g₁ x) = g₂ x) :
  ∀ x : EV, L_bind_eff f ((HV_shift_eff ∘ g₁) x) = (HV_shift_eff ∘ g₂) x.
Proof.
  intro ; unfold compose.
  erewrite L_bind_HV_map_eff ; crush.
Qed.

Local Fact EV_L_bind_aux3
  (EV EV' HV L L' : Set)
  (f : L → lid L')
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV L')
  (Q : ∀ x, L_bind_eff f (g₁ x) = g₂ x) :
  ∀ x : EV, L_bind_eff (L_lift_inc f) ((L_shift_eff ∘ g₁) x) = (L_shift_eff ∘ g₂) x.
Proof.
  intro ; unfold compose.
  erewrite L_bind_map_eff ; crush.
Qed.

Hint Resolve EV_L_bind_aux1 EV_L_bind_aux2 EV_L_bind_aux3.

Hint Rewrite <- L_bind_eff_app.

Definition
  EV_L_bind_ef
  (EV EV' HV L L' : Set)
  (f : L → lid L')
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV L')
  (Q : ∀ x, L_bind_eff f (g₁ x) = g₂ x)
  (ε : ef EV HV L) :
  EV_bind_ef g₂ (L_bind_ef f ε) = L_bind_eff f (EV_bind_ef g₁ ε)
.
Proof.
destruct ε ; simpl ; crush.
Qed.

Fixpoint
  EV_L_bind_eff
  (EV EV' HV L L' : Set)
  (f : L → lid L')
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV L')
  (Q : ∀ x, L_bind_eff f (g₁ x) = g₂ x)
  (𝓔 : eff EV HV L) {struct 𝓔} :
  EV_bind_eff g₂ (L_bind_eff f 𝓔) = L_bind_eff f (EV_bind_eff g₁ 𝓔)
.
Proof.
destruct 𝓔 ; simpl ;
repeat erewrite EV_L_bind_ef ;
repeat erewrite EV_L_bind_eff ;
crush.
Qed.

Fixpoint
  EV_L_bind_ty
  (EV EV' HV L L' : Set)
  (f : L → lid L')
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV L')
  (Q : ∀ x, L_bind_eff f (g₁ x) = g₂ x)
  (T : ty EV HV L) {struct T} :
  EV_bind_ty g₂ (L_bind_ty f T) = L_bind_ty f (EV_bind_ty g₁ T)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EV_L_bind_ty ;
  repeat erewrite EV_L_bind_eff ;
  repeat erewrite EV_L_bind_ms ;
  crush.
Qed.

Fixpoint
  EV_L_bind_hd
  (EV EV' HV V L L' : Set)
  (f : L → lid L')
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV L')
  (Q : ∀ x, L_bind_eff f (g₁ x) = g₂ x)
  (h : hd EV HV V L) {struct h} :
  EV_bind_hd g₂ (L_bind_hd f h) = L_bind_hd f (EV_bind_hd g₁ h)
with
  EV_L_bind_tm
  (EV EV' HV V L L' : Set)
  (f : L → lid L')
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV L')
  (Q : ∀ x, L_bind_eff f (g₁ x) = g₂ x)
  (t : tm EV HV V L) {struct t} :
  EV_bind_tm g₂ (L_bind_tm f t) = L_bind_tm f (EV_bind_tm g₁ t)
with
  EV_L_bind_val
  (EV EV' HV V L L' : Set)
  (f : L → lid L')
  (g₁ : EV → eff EV' HV L) (g₂ : EV → eff EV' HV L')
  (Q : ∀ x, L_bind_eff f (g₁ x) = g₂ x)
  (v : val EV HV V L) {struct v} :
  EV_bind_val g₂ (L_bind_val f v) = L_bind_val f (EV_bind_val g₁ v).
Proof.
+ destruct h ; simpl ;
  repeat erewrite EV_L_bind_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite EV_L_bind_ty ;
  repeat erewrite EV_L_bind_eff ;
  repeat erewrite EV_L_bind_hd ;
  repeat erewrite EV_L_bind_val ;
  repeat erewrite EV_L_bind_tm ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite EV_L_bind_hd ;
  repeat erewrite EV_L_bind_tm ;
  crush.
Qed.

End section_EV_L_bind.


Section section_HV_L_bind.

Hint Rewrite <- L_bind_eff_app.
Hint Rewrite lbl_L_bind_hd lbl_EV_map_hd.

Definition
  HV_L_bind_lbl
  (EV HV HV' V L L' : Set)
  (f : L → lid L')
  (g₁ : HV → hd EV HV' V L) (g₂ : HV → hd EV HV' V L')
  (Q : ∀ x, lbl_hd (L_bind_hd f (g₁ x)) = lbl_hd (g₂ x))
  (ℓ : lbl HV L) :
  HV_bind_lbl g₂ (L_bind_lbl f ℓ) = L_bind_lbl f (HV_bind_lbl g₁ ℓ)
.
Proof.
destruct ℓ ; simpl ; [ | crush ].
rewrite <- Q ; crush.
Qed.

Definition
  HV_L_bind_ef
  (EV HV HV' V L L' : Set)
  (f : L → lid L')
  (g₁ : HV → hd EV HV' V L) (g₂ : HV → hd EV HV' V L')
  (Q : ∀ x, lbl_hd (L_bind_hd f (g₁ x)) = lbl_hd (g₂ x))
  (ε : ef EV HV L) :
  HV_bind_ef g₂ (L_bind_ef f ε) = L_bind_ef f (HV_bind_ef g₁ ε)
.
Proof.
destruct ε ; simpl ;
repeat erewrite HV_L_bind_lbl ;
crush.
Qed.

Fixpoint
  HV_L_bind_eff
  (EV HV HV' V L L' : Set)
  (f : L → lid L')
  (g₁ : HV → hd EV HV' V L) (g₂ : HV → hd EV HV' V L')
  (Q : ∀ x, lbl_hd (L_bind_hd f (g₁ x)) = lbl_hd (g₂ x))
  (𝓔 : eff EV HV L) {struct 𝓔} :
  HV_bind_eff g₂ (L_bind_eff f 𝓔) = L_bind_eff f (HV_bind_eff g₁ 𝓔)
.
Proof.
destruct 𝓔 ; simpl ;
repeat erewrite HV_L_bind_ef ;
repeat erewrite HV_L_bind_eff ;
crush.
Qed.

Fixpoint
  HV_L_bind_ty
  (EV HV HV' V L L' : Set)
  (f : L → lid L')
  (g₁ : HV → hd EV HV' V L) (g₂ : HV → hd EV HV' V L')
  (Q : ∀ x, lbl_hd (L_bind_hd f (g₁ x)) = lbl_hd (g₂ x))
  (T : ty EV HV L) {struct T} :
  HV_bind_ty g₂ (L_bind_ty f T) = L_bind_ty f (HV_bind_ty g₁ T)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite HV_L_bind_ty ;
  repeat erewrite HV_L_bind_eff ;
  try reflexivity.
  { crush. }
  { crush. }
  { crush. }
  { intro ; unfold compose ; erewrite L_bind_EV_map_hd.
    repeat rewrite lbl_EV_map_hd ; crush. }
  { destruct x ; simpl ; [ crush | ].
    rewrite L_bind_HV_map_hd.
    repeat rewrite lbl_HV_map_hd.
    crush.
  }
Qed.

Fixpoint
  HV_L_bind_hd
  (EV HV HV' V L L' : Set)
  (f : L → lid L')
  (g₁ : HV → hd EV HV' V L) (g₂ : HV → hd EV HV' V L')
  (Q : ∀ x, L_bind_hd f (g₁ x) = g₂ x)
  (h : hd EV HV V L) {struct h} :
  HV_bind_hd g₂ (L_bind_hd f h) = L_bind_hd f (HV_bind_hd g₁ h)
with
  HV_L_bind_tm
  (EV HV HV' V L L' : Set)
  (f : L → lid L')
  (g₁ : HV → hd EV HV' V L) (g₂ : HV → hd EV HV' V L')
  (Q : ∀ x, L_bind_hd f (g₁ x) = g₂ x)
  (t : tm EV HV V L) {struct t} :
  HV_bind_tm g₂ (L_bind_tm f t) = L_bind_tm f (HV_bind_tm g₁ t)
with
  HV_L_bind_val
  (EV HV HV' V L L' : Set)
  (f : L → lid L')
  (g₁ : HV → hd EV HV' V L) (g₂ : HV → hd EV HV' V L')
  (Q : ∀ x, L_bind_hd f (g₁ x) = g₂ x)
  (v : val EV HV V L) {struct v} :
  HV_bind_val g₂ (L_bind_val f v) = L_bind_val f (HV_bind_val g₁ v).
Proof.
+ destruct h ; simpl ;
  repeat erewrite HV_L_bind_tm ;
  try reflexivity.
  { crush. }
  { intro ; unfold compose ; rewrite <- Q.
    repeat erewrite L_bind_V_map_hd ; crush.
  }
+ destruct t ; simpl ;
  repeat erewrite HV_L_bind_ty ;
  repeat erewrite HV_L_bind_eff ;
  repeat erewrite HV_L_bind_hd ;
  repeat erewrite HV_L_bind_val ;
  repeat erewrite HV_L_bind_tm ;
  try reflexivity ;
  try assumption.
  { crush. }
  { intro ; unfold compose ; rewrite L_bind_V_map_hd ; crush. }
  { intro ; unfold compose ; erewrite L_bind_map_hd ; crush. }
+ destruct v ; simpl ;
  repeat erewrite HV_L_bind_hd ;
  repeat erewrite HV_L_bind_tm ;
  try reflexivity ;
  try assumption.
  { intro ; unfold compose ; rewrite L_bind_V_map_hd ; crush. }
  { intro ; unfold compose ; rewrite L_bind_EV_map_hd ; crush. }
  { destruct x ; simpl ; [ crush | ].
    rewrite L_bind_HV_map_hd ; crush. }
Qed.

End section_HV_L_bind.


Section section_V_L_bind.

Local Fact V_L_bind_aux1
  (EV HV V V' L L' : Set)
  (f : L → lid L')
  (g₁ : V → val EV HV V' L) (g₂ : V → val EV HV V' L')
  (Q : ∀ x, L_bind_val f (g₁ x) = g₂ x) :
  ∀ x : inc V, L_bind_val f (V_lift_inc g₁ x) = V_lift_inc g₂ x.
Proof.
  intro x ; destruct x ; simpl ; [ crush | ].
  unfold compose.
  erewrite L_bind_V_map_val ; crush.
Qed.

Local Fact V_L_bind_aux2
  (EV HV V V' L L' : Set)
  (f : L → lid L')
  (g₁ : V → val EV HV V' L) (g₂ : V → val EV HV V' L')
  (Q : ∀ x, L_bind_val f (g₁ x) = g₂ x) :
  ∀ x : V, L_bind_val f ((EV_shift_val ∘ g₁) x) = (EV_shift_val ∘ g₂) x.
Proof.
  intro ; unfold compose.
  erewrite L_bind_EV_map_val ; crush.
Qed.

Local Fact V_L_bind_aux3
  (EV HV V V' L L' : Set)
  (f : L → lid L')
  (g₁ : V → val EV HV V' L) (g₂ : V → val EV HV V' L')
  (Q : ∀ x, L_bind_val f (g₁ x) = g₂ x) :
  ∀ x : V, L_bind_val f ((HV_shift_val ∘ g₁) x) = (HV_shift_val ∘ g₂) x.
Proof.
  intro ; unfold compose.
  erewrite L_bind_HV_map_val ; crush.
Qed.

Local Fact V_L_bind_aux4
  (EV HV V V' L L' : Set)
  (f : L → lid L')
  (g₁ : V → val EV HV V' L) (g₂ : V → val EV HV V' L')
  (Q : ∀ x, L_bind_val f (g₁ x) = g₂ x) :
  ∀ x : V, L_bind_val (L_lift_inc f) ((L_shift_val ∘ g₁) x) = (L_shift_val ∘ g₂) x.
Proof.
  intro ; unfold compose.
  erewrite <- Q, L_bind_map_val ; reflexivity.
Qed.

Hint Resolve V_L_bind_aux1 V_L_bind_aux2 V_L_bind_aux3 V_L_bind_aux4.

Fixpoint
  V_L_bind_hd
  (EV HV V V' L L' : Set)
  (f : L → lid L')
  (g₁ : V → val EV HV V' L) (g₂ : V → val EV HV V' L')
  (Q : ∀ x, L_bind_val f (g₁ x) = g₂ x)
  (h : hd EV HV V L) {struct h} :
  V_bind_hd g₂ (L_bind_hd f h) = L_bind_hd f (V_bind_hd g₁ h)
with
  V_L_bind_tm
  (EV HV V V' L L' : Set)
  (f : L → lid L')
  (g₁ : V → val EV HV V' L) (g₂ : V → val EV HV V' L')
  (Q : ∀ x, L_bind_val f (g₁ x) = g₂ x)
  (t : tm EV HV V L) {struct t} :
  V_bind_tm g₂ (L_bind_tm f t) = L_bind_tm f (V_bind_tm g₁ t)
with
  V_L_bind_val
  (EV HV V V' L L' : Set)
  (f : L → lid L')
  (g₁ : V → val EV HV V' L) (g₂ : V → val EV HV V' L')
  (Q : ∀ x, L_bind_val f (g₁ x) = g₂ x)
  (v : val EV HV V L) {struct v} :
  V_bind_val g₂ (L_bind_val f v) = L_bind_val f (V_bind_val g₁ v).
Proof.
+ destruct h ; simpl ;
  repeat erewrite V_L_bind_tm ; crush.
+ destruct t ; simpl ;
  repeat erewrite V_L_bind_ty ;
  repeat erewrite V_L_bind_eff ;
  repeat erewrite V_L_bind_hd ;
  repeat erewrite V_L_bind_val ;
  repeat erewrite V_L_bind_tm ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite V_L_bind_hd ;
  repeat erewrite V_L_bind_tm ;
  crush.
Qed.

End section_V_L_bind.
