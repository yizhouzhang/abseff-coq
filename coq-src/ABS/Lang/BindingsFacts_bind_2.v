Require Import Lang.Syntax Lang.Bindings.
Require Import Lang.BindingsFacts_map.
Require Import Lang.BindingsFacts_bind_0.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Section section_EV_bind_map.

Hint Rewrite <- EV_map_eff_app.

Local Fact EV_bind_map_aux1
  (EV₁ EV₂₁ EV₂₂ EV₃ HV L : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff EV₃ HV L)
  (g₁ : EV₁ → eff EV₂₂ HV L) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x)) :
  ∀ x : inc EV₁,
  EV_lift_inc f₂ (map_inc f₁ x) = EV_map_eff (map_inc g₂) (EV_lift_inc g₁ x).
Proof.
  destruct x ; simpl ; [ crush | ].
  rewrite Hfg.
  repeat erewrite EV_map_map_eff ; crush.
Qed.

Local Fact EV_bind_map_aux2
  (EV₁ EV₂₁ EV₂₂ EV₃ HV L : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff EV₃ HV L)
  (g₁ : EV₁ → eff EV₂₂ HV L) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x)) :
  ∀ x : EV₁, (HV_shift_eff ∘ f₂) (f₁ x) = EV_map_eff g₂ ((HV_shift_eff ∘ g₁) x).
Proof.
  intro ; unfold compose.
  rewrite EV_HV_map_eff.
  crush.
Qed.

Local Fact EV_bind_map_aux3
  (EV₁ EV₂₁ EV₂₂ EV₃ HV L : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff EV₃ HV L)
  (g₁ : EV₁ → eff EV₂₂ HV L) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x)) :
  ∀ x : EV₁, (L_shift_eff ∘ f₂) (f₁ x) = EV_map_eff g₂ ((L_shift_eff ∘ g₁) x).
Proof.
  intro ; unfold compose.
  rewrite EV_L_map_eff.
  crush.
Qed.

Hint Resolve EV_bind_map_aux1 EV_bind_map_aux2 EV_bind_map_aux3.

Definition
  EV_bind_map_ef
  (EV₁ EV₂₁ EV₂₂ EV₃ HV L : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff EV₃ HV L)
  (g₁ : EV₁ → eff EV₂₂ HV L) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x))
  (ε : ef EV₁ HV L) :
  EV_bind_ef f₂ (EV_map_ef f₁ ε) = EV_map_eff g₂ (EV_bind_ef g₁ ε)
.
Proof.
destruct ε ; simpl ;
crush.
Qed.

Fixpoint
  EV_bind_map_eff
  (EV₁ EV₂₁ EV₂₂ EV₃ HV L : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff EV₃ HV L)
  (g₁ : EV₁ → eff EV₂₂ HV L) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x))
  (𝓔 : eff EV₁ HV L) {struct 𝓔} :
  EV_bind_eff f₂ (EV_map_eff f₁ 𝓔) = EV_map_eff g₂ (EV_bind_eff g₁ 𝓔)
.
Proof.
destruct 𝓔 ; simpl ;
repeat erewrite EV_bind_map_ef ;
repeat erewrite EV_bind_map_eff ;
crush.
Qed.

Fixpoint
  EV_bind_map_ty
  (EV₁ EV₂₁ EV₂₂ EV₃ HV L : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff EV₃ HV L)
  (g₁ : EV₁ → eff EV₂₂ HV L) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x))
  (T : ty EV₁ HV L) {struct T} :
  EV_bind_ty f₂ (EV_map_ty f₁ T) = EV_map_ty g₂ (EV_bind_ty g₁ T).
Proof.
+ destruct T ; simpl ;
  repeat erewrite EV_bind_map_ty ;
  repeat erewrite EV_bind_map_eff ;
  crush.
Qed.

Fixpoint
  EV_bind_map_hd
  (EV₁ EV₂₁ EV₂₂ EV₃ HV V L : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff EV₃ HV L)
  (g₁ : EV₁ → eff EV₂₂ HV L) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x))
  (h : hd EV₁ HV V L) {struct h} :
  EV_bind_hd f₂ (EV_map_hd f₁ h) = EV_map_hd g₂ (EV_bind_hd g₁ h)
with
  EV_bind_map_val
  (EV₁ EV₂₁ EV₂₂ EV₃ HV V L : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff EV₃ HV L)
  (g₁ : EV₁ → eff EV₂₂ HV L) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x))
  (v : val EV₁ HV V L) {struct v} :
  EV_bind_val f₂ (EV_map_val f₁ v) = EV_map_val g₂ (EV_bind_val g₁ v)
with
  EV_bind_map_tm
  (EV₁ EV₂₁ EV₂₂ EV₃ HV V L : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff EV₃ HV L)
  (g₁ : EV₁ → eff EV₂₂ HV L) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x))
  (t : tm EV₁ HV V L) {struct t} :
  EV_bind_tm f₂ (EV_map_tm f₁ t) = EV_map_tm g₂ (EV_bind_tm g₁ t).
Proof.
+ destruct h ; simpl ;
  repeat erewrite EV_bind_map_tm ;
  repeat erewrite EV_bind_map_hd ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite EV_bind_map_hd ;
  repeat erewrite EV_bind_map_tm ;
  repeat erewrite EV_bind_map_ty ;
  repeat erewrite EV_bind_map_eff ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite EV_bind_map_ty ;
  repeat erewrite EV_bind_map_eff ;
  repeat erewrite EV_bind_map_val ;
  repeat erewrite EV_bind_map_tm ;
  repeat erewrite EV_bind_map_hd ;
  crush.
Qed.

Lemma  EV_bind_map_XEnv
  (EV₁ EV₂₁ EV₂₂ EV₃ HV : Set)
  (f₁ : EV₁ → EV₂₁) (f₂ : EV₂₁ → eff EV₃ HV ∅)
  (g₁ : EV₁ → eff EV₂₂ HV ∅) (g₂ : EV₂₂ → EV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = EV_map_eff g₂ (g₁ x))
  (Ξ : XEnv EV₁ HV) :
  EV_bind_XEnv f₂ (EV_map_XEnv f₁ Ξ) = EV_map_XEnv g₂ (EV_bind_XEnv g₁ Ξ).
Proof.
induction Ξ as [ | Ξ X [T 𝓔] IHΞ ] using env_ind.
+ repeat (rewrite EV_map_XEnv_empty || rewrite EV_bind_XEnv_empty).
  reflexivity.
+ rewrite EV_map_XEnv_concat, EV_bind_XEnv_concat.
  rewrite EV_map_XEnv_single, EV_bind_XEnv_single.
  rewrite EV_bind_XEnv_concat, EV_map_XEnv_concat.
  rewrite EV_bind_XEnv_single, EV_map_XEnv_single.
  erewrite IHΞ, EV_bind_map_ty, EV_bind_map_eff ; crush.
Qed.

End section_EV_bind_map.


Section section_HV_bind_map.

Hint Rewrite <- HV_map_eff_app.
Hint Rewrite lbl_EV_map_hd lbl_HV_map_hd.

Local Fact HV_bind_map_aux1
  (EV HV₁ HV₂₁ HV₂₂ HV₃ V V' L : Set)
  (f₁ : HV₁ → HV₂₁) (f₂ : HV₂₁ → hd EV HV₃ V L)
  (g₁ : HV₁ → hd EV HV₂₂ V' L) (g₂ : HV₂₂ → HV₃)
  (Hfg : ∀ x : HV₁, lbl_hd (f₂ (f₁ x)) = lbl_hd (HV_map_hd g₂ (g₁ x))) :
  ∀ x : inc HV₁,
  lbl_hd (HV_lift_inc f₂ (map_inc f₁ x)) =
  HV_map_lbl (map_inc g₂) (lbl_hd (HV_lift_inc g₁ x)).
Proof.
  intro x ; destruct x ; simpl ; crush.
  erewrite HV_map_map_lbl ; crush.
  erewrite HV_map_map_lbl ; crush.
Qed.

Local Fact HV_bind_map_aux2
  (EV HV₁ HV₂₁ HV₂₂ HV₃ V L : Set)
  (f₁ : HV₁ → HV₂₁) (f₂ : HV₂₁ → hd EV HV₃ V L)
  (g₁ : HV₁ → hd EV HV₂₂ V L) (g₂ : HV₂₂ → HV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = HV_map_hd g₂ (g₁ x)) :
  ∀ x : HV₁,
  (L_shift_hd ∘ f₂) (f₁ x) = HV_map_hd g₂ ((L_shift_hd ∘ g₁) x).
Proof.
  intro ; unfold compose ; rewrite Hfg.
  rewrite HV_L_map_hd ; crush.
Qed.

Local Fact HV_bind_map_aux3
  (EV HV₁ HV₂₁ HV₂₂ HV₃ V L : Set)
  (f₁ : HV₁ → HV₂₁) (f₂ : HV₂₁ → hd EV HV₃ V L)
  (g₁ : HV₁ → hd EV HV₂₂ V L) (g₂ : HV₂₂ → HV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = HV_map_hd g₂ (g₁ x)) :
∀ x : HV₁,
(V_shift_hd ∘ V_shift_hd ∘ f₂) (f₁ x) =
HV_map_hd g₂ ((V_shift_hd ∘ V_shift_hd ∘ g₁) x).
Proof.
intro ; unfold compose ; rewrite Hfg.
repeat erewrite V_map_map_hd ;
try erewrite HV_V_map_hd ;
crush.
Qed.

Local Fact HV_bind_map_aux4
  (EV HV₁ HV₂₁ HV₂₂ HV₃ V L : Set)
  (f₁ : HV₁ → HV₂₁) (f₂ : HV₂₁ → hd EV HV₃ V L)
  (g₁ : HV₁ → hd EV HV₂₂ V L) (g₂ : HV₂₂ → HV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = HV_map_hd g₂ (g₁ x)) :
  ∀ x : inc HV₁,
  HV_lift_inc f₂ (map_inc f₁ x) = HV_map_hd (map_inc g₂) (HV_lift_inc g₁ x).
Proof.
  destruct x ; simpl ; [ crush | ].
  rewrite Hfg.
  repeat erewrite HV_map_map_hd ; crush.
Qed.

Local Fact HV_bind_map_aux5
  (EV HV₁ HV₂₁ HV₂₂ HV₃ V L : Set)
  (f₁ : HV₁ → HV₂₁) (f₂ : HV₂₁ → hd EV HV₃ V L)
  (g₁ : HV₁ → hd EV HV₂₂ V L) (g₂ : HV₂₂ → HV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = HV_map_hd g₂ (g₁ x)) :
∀ x : HV₁, (V_shift_hd ∘ f₂) (f₁ x) = HV_map_hd g₂ ((V_shift_hd ∘ g₁) x).
Proof.
  intro ; unfold compose ; rewrite Hfg.
  rewrite HV_V_map_hd ; crush.
Qed.

Local Fact HV_bind_map_aux6
  (EV HV₁ HV₂₁ HV₂₂ HV₃ V L : Set)
  (f₁ : HV₁ → HV₂₁) (f₂ : HV₂₁ → hd EV HV₃ V L)
  (g₁ : HV₁ → hd EV HV₂₂ V L) (g₂ : HV₂₂ → HV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = HV_map_hd g₂ (g₁ x)) :
∀ x : HV₁, (EV_shift_hd ∘ f₂) (f₁ x) = HV_map_hd g₂ ((EV_shift_hd ∘ g₁) x).
Proof.
  intro ; unfold compose ; rewrite Hfg.
  rewrite EV_HV_map_hd ; crush.
Qed.

Hint Resolve HV_bind_map_aux1 HV_bind_map_aux2 HV_bind_map_aux3
  HV_bind_map_aux4 HV_bind_map_aux5 HV_bind_map_aux6.

Definition
  HV_bind_map_lbl
  (EV HV₁ HV₂₁ HV₂₂ HV₃ V V' L : Set)
  (f₁ : HV₁ → HV₂₁) (f₂ : HV₂₁ → hd EV HV₃ V L)
  (g₁ : HV₁ → hd EV HV₂₂ V' L) (g₂ : HV₂₂ → HV₃)
  (Hfg : ∀ x, lbl_hd (f₂ (f₁ x)) = HV_map_lbl g₂ (lbl_hd (g₁ x)))
  (ℓ : lbl HV₁ L) :
  HV_bind_lbl f₂ (HV_map_lbl f₁ ℓ) = HV_map_lbl g₂ (HV_bind_lbl g₁ ℓ)
.
Proof.
destruct ℓ ; simpl ; crush.
Qed.

Definition
  HV_bind_map_ef
  (EV HV₁ HV₂₁ HV₂₂ HV₃ V V' L : Set)
  (f₁ : HV₁ → HV₂₁) (f₂ : HV₂₁ → hd EV HV₃ V L)
  (g₁ : HV₁ → hd EV HV₂₂ V' L) (g₂ : HV₂₂ → HV₃)
  (Hfg : ∀ x, lbl_hd (f₂ (f₁ x)) = HV_map_lbl g₂ (lbl_hd (g₁ x)))
  (ε : ef EV HV₁ L) :
  HV_bind_ef f₂ (HV_map_ef f₁ ε) = HV_map_ef g₂ (HV_bind_ef g₁ ε)
.
Proof.
+ destruct ε ; simpl ;
  repeat erewrite HV_bind_map_lbl ;
  crush.
Qed.

Fixpoint
  HV_bind_map_eff
  (EV HV₁ HV₂₁ HV₂₂ HV₃ V V' L : Set)
  (f₁ : HV₁ → HV₂₁) (f₂ : HV₂₁ → hd EV HV₃ V L)
  (g₁ : HV₁ → hd EV HV₂₂ V' L) (g₂ : HV₂₂ → HV₃)
  (Hfg : ∀ x, lbl_hd (f₂ (f₁ x)) = HV_map_lbl g₂ (lbl_hd (g₁ x)))
  (𝓔 : eff EV HV₁ L) {struct 𝓔} :
  HV_bind_eff f₂ (HV_map_eff f₁ 𝓔) = HV_map_eff g₂ (HV_bind_eff g₁ 𝓔)
.
Proof.
+ destruct 𝓔 ; simpl ;
  repeat erewrite HV_bind_map_ef ;
  repeat erewrite HV_bind_map_eff ;
  crush.
Qed.

Fixpoint
  HV_bind_map_ty
  (EV HV₁ HV₂₁ HV₂₂ HV₃ V V' L : Set)
  (f₁ : HV₁ → HV₂₁) (f₂ : HV₂₁ → hd EV HV₃ V L)
  (g₁ : HV₁ → hd EV HV₂₂ V' L) (g₂ : HV₂₂ → HV₃)
  (Hfg : ∀ x, lbl_hd (f₂ (f₁ x)) = HV_map_lbl g₂ (lbl_hd (g₁ x)))
  (T : ty EV HV₁ L) {struct T} :
  HV_bind_ty f₂ (HV_map_ty f₁ T) = HV_map_ty g₂ (HV_bind_ty g₁ T).
Proof.
+ destruct T ; simpl ;
  repeat erewrite HV_bind_map_ty ;
  repeat erewrite HV_bind_map_eff ;
  repeat erewrite HV_bind_map_lbl ;
  crush.
Qed.

Fixpoint
  HV_bind_map_hd
  (EV HV₁ HV₂₁ HV₂₂ HV₃ V L : Set)
  (f₁ : HV₁ → HV₂₁) (f₂ : HV₂₁ → hd EV HV₃ V L)
  (g₁ : HV₁ → hd EV HV₂₂ V L) (g₂ : HV₂₂ → HV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = HV_map_hd g₂ (g₁ x))
  (h : hd EV HV₁ V L) {struct h} :
  HV_bind_hd f₂ (HV_map_hd f₁ h) = HV_map_hd g₂ (HV_bind_hd g₁ h)
with
  HV_bind_map_val
  (EV HV₁ HV₂₁ HV₂₂ HV₃ V L : Set)
  (f₁ : HV₁ → HV₂₁) (f₂ : HV₂₁ → hd EV HV₃ V L)
  (g₁ : HV₁ → hd EV HV₂₂ V L) (g₂ : HV₂₂ → HV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = HV_map_hd g₂ (g₁ x))
  (v : val EV HV₁ V L) {struct v} :
  HV_bind_val f₂ (HV_map_val f₁ v) = HV_map_val g₂ (HV_bind_val g₁ v)
with
  HV_bind_map_tm
  (EV HV₁ HV₂₁ HV₂₂ HV₃ V L : Set)
  (f₁ : HV₁ → HV₂₁) (f₂ : HV₂₁ → hd EV HV₃ V L)
  (g₁ : HV₁ → hd EV HV₂₂ V L) (g₂ : HV₂₂ → HV₃)
  (Hfg : ∀ x, f₂ (f₁ x) = HV_map_hd g₂ (g₁ x))
  (t : tm EV HV₁ V L) {struct t} :
  HV_bind_tm f₂ (HV_map_tm f₁ t) = HV_map_tm g₂ (HV_bind_tm g₁ t).
Proof.
+ destruct h ; simpl ;
  repeat erewrite HV_bind_map_tm ;
  repeat erewrite HV_bind_map_hd ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite HV_bind_map_hd ;
  repeat erewrite HV_bind_map_ty ;
  repeat erewrite HV_bind_map_eff ;
  repeat erewrite HV_bind_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite HV_bind_map_ty ;
  repeat erewrite HV_bind_map_eff ;
  repeat erewrite HV_bind_map_hd ;
  repeat erewrite HV_bind_map_val ;
  repeat erewrite HV_bind_map_tm ;
  crush.
Qed.

Lemma HV_bind_map_XEnv
  (EV HV₁ HV₂₁ HV₂₂ HV₃ V V' : Set)
  (f₁ : HV₁ → HV₂₁) (f₂ : HV₂₁ → hd EV HV₃ V _)
  (g₁ : HV₁ → hd EV HV₂₂ V' _) (g₂ : HV₂₂ → HV₃)
  (Hfg : ∀ x, lbl_hd (f₂ (f₁ x)) = HV_map_lbl g₂ (lbl_hd (g₁ x)))
  (Ξ : XEnv EV HV₁) :
  HV_bind_XEnv f₂ (HV_map_XEnv f₁ Ξ) = HV_map_XEnv g₂ (HV_bind_XEnv g₁ Ξ).
Proof.
induction Ξ as [ | Ξ X [T 𝓔] IHΞ ] using env_ind.
+ repeat (rewrite HV_map_XEnv_empty || rewrite HV_bind_XEnv_empty).
  reflexivity.
+ rewrite HV_map_XEnv_concat, HV_bind_XEnv_concat.
  rewrite HV_map_XEnv_single, HV_bind_XEnv_single.
  rewrite HV_bind_XEnv_concat, HV_map_XEnv_concat.
  rewrite HV_bind_XEnv_single, HV_map_XEnv_single.
  erewrite IHΞ, HV_bind_map_ty, HV_bind_map_eff ; crush.
Qed.

End section_HV_bind_map.


Section section_L_bind_map.

Hint Rewrite <- L_map_eff_app.

Local Fact L_bind_map_aux1
  (L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x)) :
  ∀ x : inc L₁,
  L_lift_inc f₂ (map_inc f₁ x) = L_map_lid (map_inc g₂) (L_lift_inc g₁ x).
Proof.
  destruct x ; simpl ; [ crush | ].
  rewrite Hfg.
  repeat erewrite L_map_map_lid ; crush.
Qed.

Hint Resolve L_bind_map_aux1.

Definition
  L_bind_map_lid
  (L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  (ID : lid L₁) :
  L_bind_lid f₂ (L_map_lid f₁ ID) = L_map_lid g₂ (L_bind_lid g₁ ID)
.
Proof.
destruct ID ; simpl ;
crush.
Qed.

Definition
  L_bind_map_lbl
  (HV L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  (ℓ : lbl HV L₁) :
  L_bind_lbl f₂ (L_map_lbl f₁ ℓ) = L_map_lbl g₂ (L_bind_lbl g₁ ℓ)
.
Proof.
destruct ℓ ; simpl ;
repeat erewrite L_bind_map_lid ;
crush.
Qed.

Definition
  L_bind_map_ef
  (EV HV L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  (ε : ef EV HV L₁) :
  L_bind_ef f₂ (L_map_ef f₁ ε) = L_map_ef g₂ (L_bind_ef g₁ ε)
.
Proof.
+ destruct ε ; simpl ;
  repeat erewrite L_bind_map_lbl ;
  crush.
Qed.

Fixpoint
  L_bind_map_eff
  (EV HV L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  (𝓔 : eff EV HV L₁) {struct 𝓔} :
  L_bind_eff f₂ (L_map_eff f₁ 𝓔) = L_map_eff g₂ (L_bind_eff g₁ 𝓔)
.
Proof.
+ destruct 𝓔 ; simpl ;
  repeat erewrite L_bind_map_ef ;
  repeat erewrite L_bind_map_eff ;
  crush.
Qed.

Fixpoint
  L_bind_map_ty
  (EV HV L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  (T : ty EV HV L₁) {struct T} :
  L_bind_ty f₂ (L_map_ty f₁ T) = L_map_ty g₂ (L_bind_ty g₁ T).
Proof.
+ destruct T ; simpl ;
  repeat erewrite L_bind_map_ty ;
  repeat erewrite L_bind_map_eff ;
  crush.
Qed.

Fixpoint
  L_bind_map_hd
  (EV HV V L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  (h : hd EV HV V L₁) {struct h} :
  L_bind_hd f₂ (L_map_hd f₁ h) = L_map_hd g₂ (L_bind_hd g₁ h)
with
  L_bind_map_val
  (EV HV V L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  (v : val EV HV V L₁) {struct v} :
  L_bind_val f₂ (L_map_val f₁ v) = L_map_val g₂ (L_bind_val g₁ v)
with
  L_bind_map_tm
  (EV HV V L₁ L₂₁ L₂₂ L₃ : Set)
  (f₁ : L₁ → L₂₁) (f₂ : L₂₁ → lid L₃)
  (g₁ : L₁ → lid L₂₂) (g₂ : L₂₂ → L₃)
  (Hfg : ∀ x, f₂ (f₁ x) = L_map_lid g₂ (g₁ x))
  (t : tm EV HV V L₁) {struct t} :
  L_bind_tm f₂ (L_map_tm f₁ t) = L_map_tm g₂ (L_bind_tm g₁ t).
Proof.
+ destruct h ; simpl ;
  repeat erewrite L_bind_map_tm ;
  repeat erewrite L_bind_map_hd ;
  repeat erewrite L_bind_map_lid ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite L_bind_map_hd ;
  repeat erewrite L_bind_map_tm ;
  repeat erewrite L_bind_map_ty ;
  repeat erewrite L_bind_map_eff ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite L_bind_map_ty ;
  repeat erewrite L_bind_map_eff ;
  repeat erewrite L_bind_map_hd ;
  repeat erewrite L_bind_map_val ;
  repeat erewrite L_bind_map_tm ;
  crush.
Qed.

End section_L_bind_map.


Section section_V_bind_map.

Local Fact
  V_bind_map_aux1
  (EV HV V₁ V₂₁ V₂₂ V₃ L : Set)
  (f₁ : V₁ → V₂₁) (f₂ : V₂₁ → val EV HV V₃ L)
  (g₁ : V₁ → val EV HV V₂₂ L) (g₂ : V₂₂ → V₃)
  (Hfg : ∀ x, f₂ (f₁ x) = V_map_val g₂ (g₁ x)) :
  ∀ x : inc (inc V₁),
  V_lift_inc (V_lift_inc f₂) (map_inc (map_inc f₁) x) =
  V_map_val (map_inc (map_inc g₂)) (V_lift_inc (V_lift_inc g₁) x).
Proof.
destruct x as [ | x ] ; simpl ; [ crush |
  destruct x as [ | x ] ; simpl ; [ crush | ]
].
repeat erewrite V_map_map_val ; crush.
erewrite V_map_map_val ; crush.
Qed.

Local Fact
  V_bind_map_aux2
  (EV HV V₁ V₂₁ V₂₂ V₃ L : Set)
  (f₁ : V₁ → V₂₁) (f₂ : V₂₁ → val EV HV V₃ L)
  (g₁ : V₁ → val EV HV V₂₂ L) (g₂ : V₂₂ → V₃)
  (Hfg : ∀ x, f₂ (f₁ x) = V_map_val g₂ (g₁ x)) :
  ∀ x : inc V₁,
  V_lift_inc f₂ (map_inc f₁ x) =
  V_map_val (map_inc g₂) (V_lift_inc g₁ x).
Proof.
destruct x as [ | x ] ; simpl ; [ crush | ].
rewrite Hfg.
repeat erewrite V_map_map_val ; crush.
Qed.

Local Fact
  V_bind_map_aux3
  (EV HV V₁ V₂₁ V₂₂ V₃ L : Set)
  (f₁ : V₁ → V₂₁) (f₂ : V₂₁ → val EV HV V₃ L)
  (g₁ : V₁ → val EV HV V₂₂ L) (g₂ : V₂₂ → V₃)
  (Hfg : ∀ x, f₂ (f₁ x) = V_map_val g₂ (g₁ x)) :
  ∀ x : V₁, (EV_shift_val ∘ f₂) (f₁ x) = V_map_val g₂ ((EV_shift_val ∘ g₁) x).
Proof.
intro ; unfold compose ; rewrite Hfg.
rewrite EV_V_map_val ; crush.
Qed.

Local Fact
  V_bind_map_aux4
  (EV HV V₁ V₂₁ V₂₂ V₃ L : Set)
  (f₁ : V₁ → V₂₁) (f₂ : V₂₁ → val EV HV V₃ L)
  (g₁ : V₁ → val EV HV V₂₂ L) (g₂ : V₂₂ → V₃)
  (Hfg : ∀ x, f₂ (f₁ x) = V_map_val g₂ (g₁ x)) :
  ∀ x : V₁, (HV_shift_val ∘ f₂) (f₁ x) = V_map_val g₂ ((HV_shift_val ∘ g₁) x).
Proof.
intro ; unfold compose ; rewrite Hfg.
rewrite HV_V_map_val ; crush.
Qed.

Local Fact
  V_bind_map_aux5
  (EV HV V₁ V₂₁ V₂₂ V₃ L : Set)
  (f₁ : V₁ → V₂₁) (f₂ : V₂₁ → val EV HV V₃ L)
  (g₁ : V₁ → val EV HV V₂₂ L) (g₂ : V₂₂ → V₃)
  (Hfg : ∀ x, f₂ (f₁ x) = V_map_val g₂ (g₁ x)) :
  ∀ x : V₁, (L_shift_val ∘ f₂) (f₁ x) = V_map_val g₂ ((L_shift_val ∘ g₁) x).
Proof.
intro ; unfold compose ; rewrite Hfg.
rewrite V_L_map_val ; crush.
Qed.

Hint Resolve V_bind_map_aux1 V_bind_map_aux2
  V_bind_map_aux3 V_bind_map_aux4 V_bind_map_aux5.

Fixpoint
  V_bind_map_hd
  (EV HV V₁ V₂₁ V₂₂ V₃ L : Set)
  (f₁ : V₁ → V₂₁) (f₂ : V₂₁ → val EV HV V₃ L)
  (g₁ : V₁ → val EV HV V₂₂ L) (g₂ : V₂₂ → V₃)
  (Hfg : ∀ x, f₂ (f₁ x) = V_map_val g₂ (g₁ x))
  (h : hd EV HV V₁ L) {struct h} :
  V_bind_hd f₂ (V_map_hd f₁ h) = V_map_hd g₂ (V_bind_hd g₁ h)
with
  V_bind_map_val
  (EV HV V₁ V₂₁ V₂₂ V₃ L : Set)
  (f₁ : V₁ → V₂₁) (f₂ : V₂₁ → val EV HV V₃ L)
  (g₁ : V₁ → val EV HV V₂₂ L) (g₂ : V₂₂ → V₃)
  (Hfg : ∀ x, f₂ (f₁ x) = V_map_val g₂ (g₁ x))
  (v : val EV HV V₁ L) {struct v} :
  V_bind_val f₂ (V_map_val f₁ v) = V_map_val g₂ (V_bind_val g₁ v)
with
  V_bind_map_tm
  (EV HV V₁ V₂₁ V₂₂ V₃ L : Set)
  (f₁ : V₁ → V₂₁) (f₂ : V₂₁ → val EV HV V₃ L)
  (g₁ : V₁ → val EV HV V₂₂ L) (g₂ : V₂₂ → V₃)
  (Hfg : ∀ x, f₂ (f₁ x) = V_map_val g₂ (g₁ x))
  (t : tm EV HV V₁ L) {struct t} :
  V_bind_tm f₂ (V_map_tm f₁ t) = V_map_tm g₂ (V_bind_tm g₁ t).
Proof.
+ destruct h ; simpl ;
  repeat erewrite V_bind_map_tm ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite V_bind_map_hd ;
  repeat erewrite V_bind_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite V_bind_map_val ;
  repeat erewrite V_bind_map_tm ;
  repeat erewrite V_bind_map_hd ;
  crush.
Qed.

Fixpoint
  V_bind_map_ktx
  (EV HV V₁ V₂₁ V₂₂ V₃ L : Set)
  (f₁ : V₁ → V₂₁) (f₂ : V₂₁ → val EV HV V₃ L)
  (g₁ : V₁ → val EV HV V₂₂ L) (g₂ : V₂₂ → V₃)
  (Hfg : ∀ x, f₂ (f₁ x) = V_map_val g₂ (g₁ x))
  (K : ktx EV HV V₁ L) {struct K} :
  V_bind_ktx f₂ (V_map_ktx f₁ K) = V_map_ktx g₂ (V_bind_ktx g₁ K).
Proof.
destruct K ; simpl ;
repeat erewrite V_bind_map_ktx ;
repeat erewrite V_bind_map_val ;
repeat erewrite V_bind_map_tm ;
repeat erewrite V_bind_map_hd ;
crush.
Qed.

End section_V_bind_map.
