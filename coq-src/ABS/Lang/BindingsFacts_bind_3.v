Require Import Lang.Syntax Lang.Bindings.
Require Import Lang.BindingsFacts_map.
Require Import Lang.BindingsFacts_bind_0.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Section section_EV_bind_V_map.

Fixpoint
  EV_bind_V_map_hd (EV EV' HV V V' L : Set)
  (g : V → V') (f : EV → eff EV' HV L)
  (h : hd EV HV V L) {struct h} :
  EV_bind_hd f (V_map_hd g h) = V_map_hd g (EV_bind_hd f h)
with
  EV_bind_V_map_tm (EV EV' HV V V' L : Set)
  (g : V → V') (f : EV → eff EV' HV L)
  (t : tm EV HV V L) {struct t} :
  EV_bind_tm f (V_map_tm g t) = V_map_tm g (EV_bind_tm f t)
with
  EV_bind_V_map_val (EV EV' HV V V' L : Set)
  (g : V → V') (f : EV → eff EV' HV L)
  (v : val EV HV V L) {struct v} :
  EV_bind_val f (V_map_val g v) = V_map_val g (EV_bind_val f v).
Proof.
+ destruct h ; crush.
+ destruct t ; crush.
+ destruct v ; crush.
Qed.

Hint Rewrite EV_bind_V_map_tm EV_bind_V_map_val.

End section_EV_bind_V_map.


Section section_HV_bind_xx_map.

Definition
HV_bind_xx_map_lbl EV EV' HV HV' V V' L
(f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V' L)
(H : ∀ x, lbl_hd (f₁ x) = lbl_hd (f₂ x))
(l : lbl HV L) :
HV_bind_lbl f₁ l = HV_bind_lbl f₂ l.
Proof.
destruct l ; simpl ; crush.
Qed.

Definition
HV_bind_xx_map_ef EV HV HV' V V' L
(f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V' L)
(H : ∀ x, lbl_hd (f₁ x) = lbl_hd (f₂ x))
(ε : ef EV HV L) :
HV_bind_ef f₁ ε = HV_bind_ef f₂ ε.
Proof.
destruct ε ; simpl ; [ crush | ].
erewrite HV_bind_xx_map_lbl ; crush.
Qed.

Fixpoint
HV_bind_xx_map_eff EV HV HV' V V' L
(f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V' L)
(H : ∀ x, lbl_hd (f₁ x) = lbl_hd (f₂ x))
(ε : eff EV HV L) :
HV_bind_eff f₁ ε = HV_bind_eff f₂ ε.
Proof.
destruct ε ; simpl ;
try erewrite HV_bind_xx_map_ef ;
try erewrite HV_bind_xx_map_eff ;
crush.
Qed.

Hint Rewrite lbl_EV_map_hd lbl_HV_map_hd.

Fixpoint
HV_bind_xx_map_ty EV HV HV' V V' L
(f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V' L)
(H : ∀ x, lbl_hd (f₁ x) = lbl_hd (f₂ x))
(T : ty EV HV L) :
HV_bind_ty f₁ T = HV_bind_ty f₂ T.
Proof.
destruct T ; simpl.
+ crush.
+ erewrite HV_bind_xx_map_ty with (f₁ := f₁) (f₂ := f₂) ; [ | crush ].
  erewrite HV_bind_xx_map_ty with (f₁ := f₁) (f₂ := f₂) ; [ | crush ].
  erewrite HV_bind_xx_map_eff ; crush.
+ erewrite HV_bind_xx_map_ty ; crush.
+ erewrite HV_bind_xx_map_ty ; crush.
Qed.

End section_HV_bind_xx_map.


Section section_HV_bind_V_map.

Local Fact
  HV_bind_V_map_aux1 (EV HV HV' V V' L : Set)
  (g : V → V') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V' L)
  (H : ∀ x, V_map_hd g (f₁ x) = f₂ x) :
∀ x : HV,
V_map_hd (map_inc (map_inc g)) ((V_shift_hd ∘ V_shift_hd ∘ f₁) x) =
(V_shift_hd ∘ V_shift_hd ∘ f₂) x.
Proof.
intro x ; unfold compose ; rewrite <- H.
repeat erewrite V_map_map_hd ; crush.
repeat erewrite V_map_map_hd ; crush.
Qed.

Local Fact
  HV_bind_V_map_aux2 (EV HV HV' V V' L : Set)
  (g : V → V') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V' L)
  (H : ∀ x, V_map_hd g (f₁ x) = f₂ x) :
∀ x : HV, V_map_hd (map_inc g) ((V_shift_hd ∘ f₁) x) = (V_shift_hd ∘ f₂) x.
Proof.
intro x ; unfold compose ; rewrite <- H.
repeat erewrite V_map_map_hd ; crush.
Qed.

Local Fact
  HV_bind_V_map_aux3 (EV HV HV' V V' L : Set)
  (g : V → V') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V' L)
  (H : ∀ x, V_map_hd g (f₁ x) = f₂ x) :
∀ x : HV, V_map_hd g ((L_shift_hd ∘ f₁) x) = (L_shift_hd ∘ f₂) x.
Proof.
intro x ; unfold compose ; rewrite <- H.
erewrite V_L_map_hd ; crush.
Qed.

Local Fact
  HV_bind_V_map_aux4 (EV HV HV' V V' L : Set)
  (g : V → V') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V' L)
  (H : ∀ x, V_map_hd g (f₁ x) = f₂ x) :
∀ x : HV, V_map_hd g ((EV_shift_hd ∘ f₁) x) = (EV_shift_hd ∘ f₂) x.
Proof.
intro ; unfold compose ; rewrite <- H.
erewrite EV_V_map_hd ; crush.
Qed.

Local Fact
  HV_bind_V_map_aux5 (EV HV HV' V V' L : Set)
  (g : V → V') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V' L)
  (H : ∀ x, V_map_hd g (f₁ x) = f₂ x) :
∀ x : inc HV, V_map_hd g (HV_lift_inc f₁ x) = HV_lift_inc f₂ x.
Proof.
destruct x as [ | x ] ; simpl ; [ crush | ].
rewrite <- HV_V_map_hd ; crush.
Qed.

Hint Resolve HV_bind_V_map_aux1 HV_bind_V_map_aux2 HV_bind_V_map_aux3
  HV_bind_V_map_aux4 HV_bind_V_map_aux5.

Hint Extern 1 => match goal with
| [ H : ∀ x, V_map_hd ?g (?f₁ x) = ?f₂ x |- lbl_hd (?f₁ _) = lbl_hd (?f₂ _) ] =>
  erewrite <- lbl_V_map_hd ; rewrite H
end.

Fixpoint
  HV_bind_V_map_hd (EV HV HV' V V' L : Set)
  (g : V → V') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V' L)
  (H : ∀ x, V_map_hd g (f₁ x) = f₂ x)
  (h : hd EV HV V L) {struct h} :
  HV_bind_hd f₂ (V_map_hd g h) = V_map_hd g (HV_bind_hd f₁ h)
with
  HV_bind_V_map_tm (EV HV HV' V V' L : Set)
  (g : V → V') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V' L)
  (H : ∀ x, V_map_hd g (f₁ x) = f₂ x)
  (t : tm EV HV V L) {struct t} :
  HV_bind_tm f₂ (V_map_tm g t) = V_map_tm g (HV_bind_tm f₁ t)
with
  HV_bind_V_map_val (EV HV HV' V V' L : Set)
  (g : V → V') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V' L)
  (H : ∀ x, V_map_hd g (f₁ x) = f₂ x)
  (v : val EV HV V L) {struct v} :
  HV_bind_val f₂ (V_map_val g v) = V_map_val g (HV_bind_val f₁ v).
Proof.
+ destruct h ; simpl ;
  repeat erewrite HV_bind_V_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite HV_bind_V_map_tm ;
  repeat erewrite HV_bind_V_map_hd ;
  repeat erewrite HV_bind_V_map_val ;
  repeat erewrite HV_bind_xx_map_ty with (f₁ := f₁) (f₂ := f₂) ;
  repeat erewrite HV_bind_xx_map_eff with (f₁ := f₁) (f₂ := f₂) ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite HV_bind_V_map_tm ;
  repeat erewrite HV_bind_V_map_hd ;
  crush.
Qed.

Hint Rewrite HV_bind_V_map_tm HV_bind_V_map_val.

End section_HV_bind_V_map.


Section section_L_bind_V_map.

Fixpoint
  L_bind_V_map_hd (EV HV V V' L L' : Set)
  (g : V → V') (f : L → lid L')
  (h : hd EV HV V L) {struct h} :
  L_bind_hd f (V_map_hd g h) = V_map_hd g (L_bind_hd f h)
with
  L_bind_V_map_tm (EV HV V V' L L' : Set)
  (g : V → V') (f : L → lid L')
  (t : tm EV HV V L) {struct t} :
  L_bind_tm f (V_map_tm g t) = V_map_tm g (L_bind_tm f t)
with
  L_bind_V_map_val (EV HV V V' L L' : Set)
  (g : V → V') (f : L → lid L')
  (v : val EV HV V L) {struct v} :
  L_bind_val f (V_map_val g v) = V_map_val g (L_bind_val f v).
Proof.
+ destruct h ; crush.
+ destruct t ; crush.
+ destruct v ; crush.
Qed.

Hint Rewrite L_bind_V_map_tm L_bind_V_map_val.

End section_L_bind_V_map.


Section section_EV_bind_HV_map.

Local Fact EV_bind_HV_map_aux1 (EV EV' HV HV' L : Set)
  (g : HV → HV') (f₁ : EV → eff EV' HV' L) (f₂ : EV → eff EV' HV L)
  (Hf : ∀ x, f₁ x = HV_map_eff g (f₂ x)) :
  ∀ x : inc EV, EV_lift_inc f₁ x = HV_map_eff g (EV_lift_inc f₂ x).
Proof.
  destruct x ; simpl ; [ crush | ].
  rewrite Hf, EV_HV_map_eff ; crush.
Qed.

Local Fact EV_bind_HV_map_aux2 (EV EV' HV HV' L : Set)
  (g : HV → HV') (f₁ : EV → eff EV' HV' L) (f₂ : EV → eff EV' HV L)
  (Hf : ∀ x, f₁ x = HV_map_eff g (f₂ x)) :
  ∀ x : EV, (HV_shift_eff ∘ f₁) x = HV_map_eff (map_inc g) ((HV_shift_eff ∘ f₂) x).
Proof.
  intro ; unfold compose.
  rewrite Hf.
  repeat erewrite HV_map_map_eff ; crush.
Qed.

Local Fact EV_bind_HV_map_aux3 (EV EV' HV HV' L : Set)
  (g : HV → HV') (f₁ : EV → eff EV' HV' L) (f₂ : EV → eff EV' HV L)
  (Hf : ∀ x, f₁ x = HV_map_eff g (f₂ x)) :
  ∀ x : EV, (L_shift_eff ∘ f₁) x = HV_map_eff g ((L_shift_eff ∘ f₂) x).
Proof.
  intro ; unfold compose.
  rewrite Hf.
  repeat erewrite HV_L_map_eff ; crush.
Qed.

Hint Resolve EV_bind_HV_map_aux1 EV_bind_HV_map_aux2 EV_bind_HV_map_aux3.

Definition
  EV_bind_HV_map_ef (EV EV' HV HV' L : Set)
  (g : HV → HV') (f₁ : EV → eff EV' HV' L) (f₂ : EV → eff EV' HV L)
  (Hf : ∀ x, f₁ x = HV_map_eff g (f₂ x))
  (ε : ef EV HV L) :
  EV_bind_ef f₁ (HV_map_ef g ε) = HV_map_eff g (EV_bind_ef f₂ ε)
.
Proof.
destruct ε ; simpl ; crush.
Qed.

Fixpoint
  EV_bind_HV_map_eff (EV EV' HV HV' L : Set)
  (g : HV → HV') (f₁ : EV → eff EV' HV' L) (f₂ : EV → eff EV' HV L)
  (Hf : ∀ x, f₁ x = HV_map_eff g (f₂ x))
  (𝓔 : eff EV HV L) {struct 𝓔} :
  EV_bind_eff f₁ (HV_map_eff g 𝓔) = HV_map_eff g (EV_bind_eff f₂ 𝓔)
.
Proof.
destruct 𝓔 ; simpl ; [ crush | ].
rewrite <- HV_map_eff_app.
erewrite EV_bind_HV_map_ef, EV_bind_HV_map_eff ; crush.
Qed.

Fixpoint
  EV_bind_HV_map_ty (EV EV' HV HV' L : Set)
  (g : HV → HV') (f₁ : EV → eff EV' HV' L) (f₂ : EV → eff EV' HV L)
  (Hf : ∀ x, f₁ x = HV_map_eff g (f₂ x))
  (T : ty EV HV L) {struct T} :
  EV_bind_ty f₁ (HV_map_ty g T) = HV_map_ty g (EV_bind_ty f₂ T)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EV_bind_HV_map_ty ;
  repeat erewrite EV_bind_HV_map_eff ;
  repeat erewrite EV_bind_HV_map_lbl ;
  crush.
Qed.

Fixpoint
  EV_bind_HV_map_hd (EV EV' HV HV' V L : Set)
  (g : HV → HV') (f₁ : EV → eff EV' HV' L) (f₂ : EV → eff EV' HV L)
  (Hf : ∀ x, f₁ x = HV_map_eff g (f₂ x))
  (h : hd EV HV V L) {struct h} :
  EV_bind_hd f₁ (HV_map_hd g h) = HV_map_hd g (EV_bind_hd f₂ h)
with
  EV_bind_HV_map_tm (EV EV' HV HV' V L : Set)
  (g : HV → HV') (f₁ : EV → eff EV' HV' L) (f₂ : EV → eff EV' HV L)
  (Hf : ∀ x, f₁ x = HV_map_eff g (f₂ x))
  (t : tm EV HV V L) {struct t} :
  EV_bind_tm f₁ (HV_map_tm g t) = HV_map_tm g (EV_bind_tm f₂ t)
with
  EV_bind_HV_map_val (EV EV' HV HV' V L : Set)
  (g : HV → HV') (f₁ : EV → eff EV' HV' L) (f₂ : EV → eff EV' HV L)
  (Hf : ∀ x, f₁ x = HV_map_eff g (f₂ x))
  (v : val EV HV V L) {struct v} :
  EV_bind_val f₁ (HV_map_val g v) = HV_map_val g (EV_bind_val f₂ v).
Proof.
+ destruct h ; simpl ;
  repeat erewrite EV_bind_HV_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite EV_bind_HV_map_tm ;
  repeat erewrite EV_bind_HV_map_hd ;
  repeat erewrite EV_bind_HV_map_val ;
  repeat erewrite EV_bind_HV_map_ty ;
  repeat erewrite EV_bind_HV_map_eff ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite EV_bind_HV_map_tm ;
  repeat erewrite EV_bind_HV_map_hd ;
  crush.
Qed.

Lemma EV_bind_HV_map_XEnv
(EV EV' HV HV' : Set)
(g : HV → HV') (f₁ : EV → eff EV' HV' ∅) (f₂ : EV → eff EV' HV ∅)
(Hf : ∀ x, f₁ x = HV_map_eff g (f₂ x)) (Ξ : XEnv EV HV) :
EV_bind_XEnv f₁ (HV_map_XEnv g Ξ) = HV_map_XEnv g (EV_bind_XEnv f₂ Ξ).
Proof.
induction Ξ as [ | ? ? [] ] using env_ind.
+ repeat (rewrite HV_map_XEnv_empty || rewrite EV_bind_XEnv_empty).
  reflexivity.
+ repeat rewrite EV_bind_XEnv_concat, HV_map_XEnv_concat,
    EV_bind_XEnv_single, HV_map_XEnv_single.
  erewrite EV_bind_HV_map_ty, EV_bind_HV_map_eff, IHΞ ; crush.
Qed.

End section_EV_bind_HV_map.


Section section_HV_bind_EV_map.

Definition
  HV_bind_EV_map_ef (EV EV' HV HV' V L : Set)
  (g : EV → EV') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (H : ∀ x, lbl_hd (f₁ x) = lbl_hd (f₂ x))
  (ε : ef EV HV L) :
  HV_bind_ef f₂ (EV_map_ef g ε) = EV_map_ef g (HV_bind_ef f₁ ε)
.
Proof.
destruct ε ; simpl ; [ crush | ].
erewrite HV_bind_xx_map_lbl with (f₁ := f₁) (f₂ := f₂) ;
crush.
Qed.

Fixpoint
  HV_bind_EV_map_eff (EV EV' HV HV' V L : Set)
  (g : EV → EV') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (H : ∀ x, lbl_hd (f₁ x) = lbl_hd (f₂ x))
  (𝓔 : eff EV HV L) {struct 𝓔} :
  HV_bind_eff f₂ (EV_map_eff g 𝓔) = EV_map_eff g (HV_bind_eff f₁ 𝓔)
.
Proof.
destruct 𝓔 ; simpl ; [ crush | ].
repeat erewrite HV_bind_EV_map_ef ;
repeat erewrite HV_bind_EV_map_eff ;
crush.
Qed.

Hint Rewrite lbl_EV_map_hd lbl_HV_map_hd.

Fixpoint
  HV_bind_EV_map_ty (EV EV' HV HV' V L : Set)
  (g : EV → EV') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (H : ∀ x, lbl_hd (f₁ x) = lbl_hd (f₂ x))
  (T : ty EV HV L) {struct T} :
  HV_bind_ty f₂ (EV_map_ty g T) = EV_map_ty g (HV_bind_ty f₁ T)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite HV_bind_EV_map_ty ;
  repeat erewrite HV_bind_EV_map_eff ;
  crush.
Qed.

Local Fact HV_bind_EV_map_aux1
  (EV EV' HV HV' V L : Set)
  (g : EV → EV') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (H : ∀ x, EV_map_hd g (f₁ x) = f₂ x) :
  ∀ x : HV,
  EV_map_hd g ((V_shift_hd ∘ V_shift_hd ∘ f₁) x) = (V_shift_hd ∘ V_shift_hd ∘ f₂) x.
Proof.
intro ; unfold compose ; rewrite <- H.
repeat erewrite V_map_map_hd ;
repeat erewrite EV_V_map_hd ;
crush.
Qed.

Local Fact HV_bind_EV_map_aux2
  (EV EV' HV HV' V L : Set)
  (g : EV → EV') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (H : ∀ x, EV_map_hd g (f₁ x) = f₂ x) :
  ∀ x : HV, EV_map_hd g ((V_shift_hd ∘ f₁) x) = (V_shift_hd ∘ f₂) x.
Proof.
intro ; unfold compose ; rewrite <- H ; rewrite EV_V_map_hd ; crush.
Qed.

Local Fact HV_bind_EV_map_aux3
  (EV EV' HV HV' V L : Set)
  (g : EV → EV') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (H : ∀ x, EV_map_hd g (f₁ x) = f₂ x) :
∀ x : HV, EV_map_hd g ((L_shift_hd ∘ f₁) x) = (L_shift_hd ∘ f₂) x.
Proof.
intro ; unfold compose ; rewrite <- H ; rewrite EV_L_map_hd ; crush.
Qed.

Local Fact HV_bind_EV_map_aux4
  (EV EV' HV HV' V L : Set)
  (g : EV → EV') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (H : ∀ x, EV_map_hd g (f₁ x) = f₂ x) :
∀ x : HV, EV_map_hd g ((V_shift_hd ∘ f₁) x) = (V_shift_hd ∘ f₂) x.
Proof.
intro ; unfold compose ; rewrite EV_V_map_hd ; crush.
Qed.

Local Fact HV_bind_EV_map_aux5
  (EV EV' HV HV' V L : Set)
  (g : EV → EV') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (H : ∀ x, EV_map_hd g (f₁ x) = f₂ x) :
∀ x : HV, EV_map_hd (map_inc g) ((EV_shift_hd ∘ f₁) x) = (EV_shift_hd ∘ f₂) x.
Proof.
intro ; unfold compose ; rewrite <- H.
repeat erewrite EV_map_map_hd ; crush.
Qed.

Local Fact HV_bind_EV_map_aux6
  (EV EV' HV HV' V L : Set)
  (g : EV → EV') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (H : ∀ x, EV_map_hd g (f₁ x) = f₂ x) :
∀ x : inc HV, EV_map_hd g (HV_lift_inc f₁ x) = HV_lift_inc f₂ x.
Proof.
destruct x ; simpl ; [ crush | ].
rewrite EV_HV_map_hd ; crush.
Qed.

Hint Resolve HV_bind_EV_map_aux1 HV_bind_EV_map_aux2 HV_bind_EV_map_aux3
  HV_bind_EV_map_aux4 HV_bind_EV_map_aux5 HV_bind_EV_map_aux6.

Hint Extern 1 => match goal with
| [ H : ∀ x, EV_map_hd ?g (?f₁ x) = ?f₂ x |- lbl_hd (?f₁ _) = lbl_hd (?f₂ _) ] =>
  erewrite <- lbl_EV_map_hd ; rewrite H
end.

Fixpoint
  HV_bind_EV_map_hd (EV EV' HV HV' V L : Set)
  (g : EV → EV') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (H : ∀ x, EV_map_hd g (f₁ x) = f₂ x)
  (h : hd EV HV V L) {struct h} :
  HV_bind_hd f₂ (EV_map_hd g h) = EV_map_hd g (HV_bind_hd f₁ h)
with
  HV_bind_EV_map_tm (EV EV' HV HV' V L : Set)
  (g : EV → EV') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (H : ∀ x, EV_map_hd g (f₁ x) = f₂ x)
  (t : tm EV HV V L) {struct t} :
  HV_bind_tm f₂ (EV_map_tm g t) = EV_map_tm g (HV_bind_tm f₁ t)
with
  HV_bind_EV_map_val (EV EV' HV HV' V L : Set)
  (g : EV → EV') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV' HV' V L)
  (H : ∀ x, EV_map_hd g (f₁ x) = f₂ x)
  (v : val EV HV V L) {struct v} :
  HV_bind_val f₂ (EV_map_val g v) = EV_map_val g (HV_bind_val f₁ v).
Proof.
+ destruct h ; simpl ;
  repeat erewrite HV_bind_EV_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite HV_bind_EV_map_tm ;
  repeat erewrite HV_bind_EV_map_hd ;
  repeat erewrite HV_bind_EV_map_val ;
  repeat erewrite HV_bind_EV_map_ty ;
  repeat erewrite HV_bind_EV_map_eff ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite HV_bind_EV_map_tm ;
  repeat erewrite HV_bind_EV_map_hd ;
  crush.
Qed.

Lemma HV_bind_EV_map_XEnv
(EV EV' HV HV' V : Set)
(g : EV → EV') (f₁ : HV → hd EV HV' V _) (f₂ : HV → hd EV' HV' V _)
(H : ∀ x, lbl_hd (f₁ x) = lbl_hd (f₂ x))
(Ξ : XEnv EV HV) :
EV_map_XEnv g (HV_bind_XEnv f₁ Ξ) = HV_bind_XEnv f₂ (EV_map_XEnv g Ξ).
Proof.
induction Ξ as [ | ? ? [] ] using env_ind.
+ repeat rewrite EV_map_XEnv_empty, HV_bind_XEnv_empty.
  reflexivity.
+ repeat rewrite
    EV_map_XEnv_concat, HV_bind_XEnv_concat,
    EV_map_XEnv_single, HV_bind_XEnv_single.
  erewrite HV_bind_EV_map_ty, HV_bind_EV_map_eff, IHΞ ;
  crush.
Qed.

End section_HV_bind_EV_map.


Section section_EV_bind_L_map.

Local Fact EV_bind_L_map_aux1
  (EV EV' HV L L' : Set)
  (g : L → L') (f₁ : EV → eff EV' HV L) (f₂ : EV → eff EV' HV L')
  (H : ∀ x, L_map_eff g (f₁ x) = f₂ x) :
  ∀ x : inc EV, L_map_eff g (EV_lift_inc f₁ x) = EV_lift_inc f₂ x.
Proof.
  destruct x ; simpl ; [ crush | ].
  rewrite <- H.
  erewrite EV_L_map_eff ; crush.
Qed.

Local Fact EV_bind_L_map_aux2
  (EV EV' HV L L' : Set)
  (g : L → L') (f₁ : EV → eff EV' HV L) (f₂ : EV → eff EV' HV L')
  (H : ∀ x, L_map_eff g (f₁ x) = f₂ x) :
  ∀ x : EV, L_map_eff g ((HV_shift_eff ∘ f₁) x) = (HV_shift_eff ∘ f₂) x.
Proof.
  intro ; unfold compose ; rewrite <- H.
  erewrite HV_L_map_eff ; crush.
Qed.

Local Fact EV_bind_L_map_aux3
  (EV EV' HV L L' : Set)
  (g : L → L') (f₁ : EV → eff EV' HV L) (f₂ : EV → eff EV' HV L')
  (H : ∀ x, L_map_eff g (f₁ x) = f₂ x) :
  ∀ x : EV, L_map_eff (map_inc g) ((L_shift_eff ∘ f₁) x) = (L_shift_eff ∘ f₂) x.
Proof.
  intro ; unfold compose ; rewrite <- H.
  repeat erewrite L_map_map_eff ; crush.
Qed.

Hint Resolve EV_bind_L_map_aux1 EV_bind_L_map_aux2 EV_bind_L_map_aux3.

Definition
  EV_bind_L_map_ef (EV EV' HV L L' : Set)
  (g : L → L') (f₁ : EV → eff EV' HV L) (f₂ : EV → eff EV' HV L')
  (H : ∀ x, L_map_eff g (f₁ x) = f₂ x)
  (ε : ef EV HV L) :
  EV_bind_ef f₂ (L_map_ef g ε) = L_map_eff g (EV_bind_ef f₁ ε)
.
Proof.
destruct ε ; simpl ; crush.
Qed.

Hint Resolve L_map_eff_app.

Fixpoint
  EV_bind_L_map_eff (EV EV' HV L L' : Set)
  (g : L → L') (f₁ : EV → eff EV' HV L) (f₂ : EV → eff EV' HV L')
  (H : ∀ x, L_map_eff g (f₁ x) = f₂ x)
  (𝓔 : eff EV HV L) {struct 𝓔} :
  EV_bind_eff f₂ (L_map_eff g 𝓔) = L_map_eff g (EV_bind_eff f₁ 𝓔)
.
Proof.
destruct 𝓔 ; simpl ;
repeat erewrite EV_bind_L_map_ef ;
repeat erewrite EV_bind_L_map_eff ;
crush.
Qed.

Fixpoint
  EV_bind_L_map_ty (EV EV' HV L L' : Set)
  (g : L → L') (f₁ : EV → eff EV' HV L) (f₂ : EV → eff EV' HV L')
  (H : ∀ x, L_map_eff g (f₁ x) = f₂ x)
  (T : ty EV HV L) {struct T} :
  EV_bind_ty f₂ (L_map_ty g T) = L_map_ty g (EV_bind_ty f₁ T)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite EV_bind_L_map_ty ;
  repeat erewrite EV_bind_L_map_eff ;
  crush.
Qed.

Fixpoint
  EV_bind_L_map_hd (EV EV' HV V L L' : Set)
  (g : L → L') (f₁ : EV → eff EV' HV L) (f₂ : EV → eff EV' HV L')
  (H : ∀ x, L_map_eff g (f₁ x) = f₂ x)
  (h : hd EV HV V L) {struct h} :
  EV_bind_hd f₂ (L_map_hd g h) = L_map_hd g (EV_bind_hd f₁ h)
with
  EV_bind_L_map_tm (EV EV' HV V L L' : Set)
  (g : L → L') (f₁ : EV → eff EV' HV L) (f₂ : EV → eff EV' HV L')
  (H : ∀ x, L_map_eff g (f₁ x) = f₂ x)
  (t : tm EV HV V L) {struct t} :
  EV_bind_tm f₂ (L_map_tm g t) = L_map_tm g (EV_bind_tm f₁ t)
with
  EV_bind_L_map_val (EV EV' HV V L L' : Set)
  (g : L → L') (f₁ : EV → eff EV' HV L) (f₂ : EV → eff EV' HV L')
  (H : ∀ x, L_map_eff g (f₁ x) = f₂ x)
  (v : val EV HV V L) {struct v} :
  EV_bind_val f₂ (L_map_val g v) = L_map_val g (EV_bind_val f₁ v).
Proof.
+ destruct h ; simpl ;
  repeat erewrite EV_bind_L_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite EV_bind_L_map_ty ;
  repeat erewrite EV_bind_L_map_eff ;
  repeat erewrite EV_bind_L_map_tm ;
  repeat erewrite EV_bind_L_map_hd ;
  repeat erewrite EV_bind_L_map_val ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite EV_bind_L_map_tm ;
  repeat erewrite EV_bind_L_map_hd ;
  crush.
Qed.

End section_EV_bind_L_map.


Section section_HV_bind_L_map.

Hint Rewrite lbl_L_map_hd.

Definition
  HV_bind_L_map_lbl (EV HV HV' V L L' : Set)
  (g : L → L') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V L')
  (H : ∀ x, lbl_hd (L_map_hd g (f₁ x)) = lbl_hd (f₂ x))
  (ℓ : lbl HV L) :
  HV_bind_lbl f₂ (L_map_lbl g ℓ) = L_map_lbl g (HV_bind_lbl f₁ ℓ)
.
Proof.
destruct ℓ ; simpl ; [ | crush ].
rewrite <- H ; crush.
Qed.

Definition
  HV_bind_L_map_ef (EV HV HV' V L L' : Set)
  (g : L → L') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V L')
  (H : ∀ x, lbl_hd (L_map_hd g (f₁ x)) = lbl_hd (f₂ x))
  (ε : ef EV HV L) :
  HV_bind_ef f₂ (L_map_ef g ε) = L_map_ef g (HV_bind_ef f₁ ε)
.
Proof.
destruct ε ; simpl ; [ crush | ].
erewrite HV_bind_L_map_lbl ; crush.
Qed.

Fixpoint
  HV_bind_L_map_eff (EV HV HV' V L L' : Set)
  (g : L → L') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V L')
  (H : ∀ x, lbl_hd (L_map_hd g (f₁ x)) = lbl_hd (f₂ x))
  (𝓔 : eff EV HV L) {struct 𝓔} :
  HV_bind_eff f₂ (L_map_eff g 𝓔) = L_map_eff g (HV_bind_eff f₁ 𝓔)
.
Proof.
destruct 𝓔 ; simpl ;
repeat erewrite HV_bind_L_map_ef ;
repeat erewrite HV_bind_L_map_eff ;
crush.
Qed.

Local Fact HV_bind_L_map_aux1
  (EV HV HV' V L L' : Set)
  (g : L → L') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V L')
  (H : ∀ x, lbl_hd (L_map_hd g (f₁ x)) = lbl_hd (f₂ x)) :
∀ x : HV,
lbl_hd (L_map_hd g ((EV_shift_hd ∘ f₁) x)) = lbl_hd ((EV_shift_hd ∘ f₂) x).
Proof.
intro ; unfold compose.
rewrite <- EV_L_map_hd.
repeat rewrite lbl_EV_map_hd.
crush.
Qed.

Local Fact HV_bind_L_map_aux2
  (EV HV HV' V L L' : Set)
  (g : L → L') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V L')
  (H : ∀ x, lbl_hd (L_map_hd g (f₁ x)) = lbl_hd (f₂ x)) :
∀ x : inc HV,
lbl_hd (L_map_hd g (HV_lift_inc f₁ x)) = lbl_hd (HV_lift_inc f₂ x).
Proof.
destruct x ; simpl ; [ crush | ].
rewrite <- HV_L_map_hd.
repeat rewrite lbl_HV_map_hd.
crush.
Qed.

Hint Resolve HV_bind_L_map_aux1 HV_bind_L_map_aux2.

Fixpoint
  HV_bind_L_map_ty (EV HV HV' V L L' : Set)
  (g : L → L') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V L')
  (H : ∀ x, lbl_hd (L_map_hd g (f₁ x)) = lbl_hd (f₂ x))
  (T : ty EV HV L) {struct T} :
  HV_bind_ty f₂ (L_map_ty g T) = L_map_ty g (HV_bind_ty f₁ T)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite HV_bind_L_map_ty ;
  repeat erewrite HV_bind_L_map_eff ;
  crush.
Qed.

Local Fact HV_bind_L_map_aux3
  (EV HV HV' V L L' : Set)
  (g : L → L') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V L')
  (H : ∀ x, L_map_hd g (f₁ x) = f₂ x) :
  ∀ x : inc HV, L_map_hd g (HV_lift_inc f₁ x) = HV_lift_inc f₂ x.
Proof.
  destruct x ; simpl ; [ crush | ].
  rewrite <- HV_L_map_hd ; crush.
Qed.

Local Fact HV_bind_L_map_aux4
  (EV HV HV' V L L' : Set)
  (g : L → L') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V L')
  (H : ∀ x, L_map_hd g (f₁ x) = f₂ x) :
  ∀ x : HV, L_map_hd (map_inc g) ((L_shift_hd ∘ f₁) x) = (L_shift_hd ∘ f₂) x.
Proof.
  intro ; unfold compose.
  rewrite <- H.
  repeat erewrite L_map_map_hd ; crush.
Qed.

Local Fact HV_bind_L_map_aux5
  (EV HV HV' V L L' : Set)
  (g : L → L') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V L')
  (H : ∀ x, L_map_hd g (f₁ x) = f₂ x) :
  ∀ x : HV,
  L_map_hd g ((V_shift_hd ∘ V_shift_hd ∘ f₁) x) = (V_shift_hd ∘ V_shift_hd ∘ f₂) x.
Proof.
intro ; unfold compose ; rewrite <- H.
repeat erewrite V_map_map_hd ;
repeat rewrite V_L_map_hd ;
crush.
Qed.

Local Fact HV_bind_L_map_aux6
  (EV HV HV' V L L' : Set)
  (g : L → L') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V L')
  (H : ∀ x, L_map_hd g (f₁ x) = f₂ x) :
∀ x : HV, L_map_hd g ((V_shift_hd ∘ f₁) x) = (V_shift_hd ∘ f₂) x.
Proof.
intro ; unfold compose ; rewrite <- H.
rewrite V_L_map_hd ; crush.
Qed.

Local Fact HV_bind_L_map_aux7
  (EV HV HV' V L L' : Set)
  (g : L → L') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V L')
  (H : ∀ x, L_map_hd g (f₁ x) = f₂ x) :
∀ x : HV, L_map_hd (map_inc g) ((L_shift_hd ∘ f₁) x) = (L_shift_hd ∘ f₂) x.
Proof.
intro ; unfold compose ; rewrite <- H.
repeat erewrite L_map_map_hd ; crush.
Qed.

Local Fact HV_bind_L_map_aux8
  (EV HV HV' V L L' : Set)
  (g : L → L') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V L')
  (H : ∀ x, L_map_hd g (f₁ x) = f₂ x) :
∀ x : HV,
L_map_hd g ((EV_shift_hd ∘ f₁) x) = (EV_shift_hd ∘ f₂) x.
Proof.
intro ; unfold compose.
rewrite <- EV_L_map_hd.
crush.
Qed.

Hint Resolve HV_bind_L_map_aux3 HV_bind_L_map_aux4 HV_bind_L_map_aux5
  HV_bind_L_map_aux6 HV_bind_L_map_aux7 HV_bind_L_map_aux8.

Fixpoint
  HV_bind_L_map_hd (EV HV HV' V L L' : Set)
  (g : L → L') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V L')
  (H : ∀ x, L_map_hd g (f₁ x) = f₂ x)
  (h : hd EV HV V L) {struct h} :
  HV_bind_hd f₂ (L_map_hd g h) = L_map_hd g (HV_bind_hd f₁ h)
with
  HV_bind_L_map_tm (EV HV HV' V L L' : Set)
  (g : L → L') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V L')
  (H : ∀ x, L_map_hd g (f₁ x) = f₂ x)
  (t : tm EV HV V L) {struct t} :
  HV_bind_tm f₂ (L_map_tm g t) = L_map_tm g (HV_bind_tm f₁ t)
with
  HV_bind_L_map_val (EV HV HV' V L L' : Set)
  (g : L → L') (f₁ : HV → hd EV HV' V L) (f₂ : HV → hd EV HV' V L')
  (H : ∀ x, L_map_hd g (f₁ x) = f₂ x)
  (v : val EV HV V L) {struct v} :
  HV_bind_val f₂ (L_map_val g v) = L_map_val g (HV_bind_val f₁ v).
Proof.
+ destruct h ; simpl ;
  repeat erewrite HV_bind_L_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite HV_bind_L_map_tm ;
  repeat erewrite HV_bind_L_map_hd ;
  repeat erewrite HV_bind_L_map_val ;
  repeat erewrite HV_bind_L_map_ty ;
  repeat erewrite HV_bind_L_map_eff ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite HV_bind_L_map_tm ;
  repeat erewrite HV_bind_L_map_hd ;
  crush.
Qed.

End section_HV_bind_L_map.


Section section_V_bind_EV_map.

Local Fact V_bind_EV_map_aux1 (EV EV' HV V V' L : Set)
  (g : EV → EV') (f₁ : V → val EV' HV V' L) (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = EV_map_val g (f₂ x)) :
  ∀ x : inc V, V_lift_inc f₁ x = EV_map_val g (V_lift_inc f₂ x).
Proof.
  destruct x ; simpl ; [ crush | ].
  rewrite Hf, EV_V_map_val ; crush.
Qed.

Local Fact V_bind_EV_map_aux2 (EV EV' HV V V' L : Set)
  (g : EV → EV') (f₁ : V → val EV' HV V' L) (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = EV_map_val g (f₂ x)) :
∀ x : inc (inc V),
V_lift_inc (V_lift_inc f₁) x = EV_map_val g (V_lift_inc (V_lift_inc f₂) x).
Proof.
destruct x ; simpl ; [ crush | ].  
rewrite EV_V_map_val.
erewrite V_bind_EV_map_aux1 ; crush.
Qed.

Local Fact V_bind_EV_map_aux3 (EV EV' HV V V' L : Set)
  (g : EV → EV') (f₁ : V → val EV' HV V' L) (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = EV_map_val g (f₂ x)) :
∀ x : V, (L_shift_val ∘ f₁) x = EV_map_val g ((L_shift_val ∘ f₂) x).
Proof.
intro ; unfold compose ; rewrite Hf.
rewrite EV_L_map_val ; crush.
Qed.

Local Fact V_bind_EV_map_aux4 (EV EV' HV V V' L : Set)
  (g : EV → EV') (f₁ : V → val EV' HV V' L) (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = EV_map_val g (f₂ x)) :
∀ x : V, (EV_shift_val ∘ f₁) x = EV_map_val (map_inc g) ((EV_shift_val ∘ f₂) x).
Proof.
intro ; unfold compose ; rewrite Hf.
repeat erewrite EV_map_map_val ; crush.
Qed.

Local Fact V_bind_EV_map_aux5 (EV EV' HV V V' L : Set)
  (g : EV → EV') (f₁ : V → val EV' HV V' L) (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = EV_map_val g (f₂ x)) :
∀ x : V, (HV_shift_val ∘ f₁) x = EV_map_val g ((HV_shift_val ∘ f₂) x).
Proof.
intro ; unfold compose ; rewrite Hf.
rewrite EV_HV_map_val ; crush.
Qed.

Hint Resolve V_bind_EV_map_aux1 V_bind_EV_map_aux2 V_bind_EV_map_aux3
  V_bind_EV_map_aux4 V_bind_EV_map_aux5.

Fixpoint
  V_bind_EV_map_hd (EV EV' HV V V' L : Set)
  (g : EV → EV') (f₁ : V → val EV' HV V' L) (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = EV_map_val g (f₂ x))
  (h : hd EV HV V L) {struct h} :
  V_bind_hd f₁ (EV_map_hd g h) = EV_map_hd g (V_bind_hd f₂ h)
with
  V_bind_EV_map_tm (EV EV' HV V V' L : Set)
  (g : EV → EV') (f₁ : V → val EV' HV V' L) (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = EV_map_val g (f₂ x))
  (t : tm EV HV V L) {struct t} :
  V_bind_tm f₁ (EV_map_tm g t) = EV_map_tm g (V_bind_tm f₂ t)
with
  V_bind_EV_map_val (EV EV' HV V V' L : Set)
  (g : EV → EV') (f₁ : V → val EV' HV V' L) (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = EV_map_val g (f₂ x))
  (v : val EV HV V L) {struct v} :
  V_bind_val f₁ (EV_map_val g v) = EV_map_val g (V_bind_val f₂ v).
Proof.
+ destruct h ; simpl ;
  repeat erewrite V_bind_EV_map_tm ; 
  crush.
+ destruct t ; simpl ;
  repeat erewrite V_bind_EV_map_tm ; 
  repeat erewrite V_bind_EV_map_val ; 
  repeat erewrite V_bind_EV_map_hd ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite V_bind_EV_map_tm ; 
  repeat erewrite V_bind_EV_map_hd ;
  crush.
Qed.

End section_V_bind_EV_map.


Section section_V_bind_HV_map.

Local Fact V_bind_HV_map_aux1 (EV HV HV' V V' L : Set)
  (g : HV → HV') (f₁ : V → val EV HV' V' L) (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = HV_map_val g (f₂ x)) :
  ∀ x : inc V, V_lift_inc f₁ x = HV_map_val g (V_lift_inc f₂ x).
Proof.
  destruct x ; simpl ; [ trivial | ].
  rewrite Hf.
  rewrite HV_V_map_val ; trivial.
Qed.

Local Fact V_bind_HV_map_aux2 (EV HV HV' V V' L : Set)
  (g : HV → HV') (f₁ : V → val EV HV' V' L) (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = HV_map_val g (f₂ x)) :
∀ x : inc (inc V),
V_lift_inc (V_lift_inc f₁) x = HV_map_val g (V_lift_inc (V_lift_inc f₂) x).
Proof.
destruct x ; simpl ; [ crush | ].
rewrite HV_V_map_val.
erewrite V_bind_HV_map_aux1 ; crush.
Qed.

Local Fact V_bind_HV_map_aux3 (EV HV HV' V V' L : Set)
  (g : HV → HV') (f₁ : V → val EV HV' V' L) (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = HV_map_val g (f₂ x)) :
∀ x : V, (L_shift_val ∘ f₁) x = HV_map_val g ((L_shift_val ∘ f₂) x).
Proof.
intro ; unfold compose.
rewrite HV_L_map_val ; crush.
Qed.

Local Fact V_bind_HV_map_aux4 (EV HV HV' V V' L : Set)
  (g : HV → HV') (f₁ : V → val EV HV' V' L) (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = HV_map_val g (f₂ x)) :
∀ x : V, (EV_shift_val ∘ f₁) x = HV_map_val g ((EV_shift_val ∘ f₂) x).
Proof.
intro ; unfold compose ; rewrite <- EV_HV_map_val ; crush.
Qed.

Local Fact V_bind_HV_map_aux5 (EV HV HV' V V' L : Set)
  (g : HV → HV') (f₁ : V → val EV HV' V' L) (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = HV_map_val g (f₂ x)) :
∀ x : V, (HV_shift_val ∘ f₁) x = HV_map_val (map_inc g) ((HV_shift_val ∘ f₂) x).
Proof.
intro ; unfold compose ; rewrite Hf.
repeat erewrite HV_map_map_val ; crush.
Qed.

Hint Resolve V_bind_HV_map_aux1 V_bind_HV_map_aux2 V_bind_HV_map_aux3
  V_bind_HV_map_aux4 V_bind_HV_map_aux5.

Fixpoint
  V_bind_HV_map_hd (EV HV HV' V V' L : Set)
  (g : HV → HV') (f₁ : V → val EV HV' V' L) (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = HV_map_val g (f₂ x))
  (h : hd EV HV V L) {struct h} :
  V_bind_hd f₁ (HV_map_hd g h) = HV_map_hd g (V_bind_hd f₂ h)
with
  V_bind_HV_map_tm (EV HV HV' V V' L : Set)
  (g : HV → HV') (f₁ : V → val EV HV' V' L) (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = HV_map_val g (f₂ x))
  (t : tm EV HV V L) {struct t} :
  V_bind_tm f₁ (HV_map_tm g t) = HV_map_tm g (V_bind_tm f₂ t)
with
  V_bind_HV_map_val (EV HV HV' V V' L : Set)
  (g : HV → HV') (f₁ : V → val EV HV' V' L) (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = HV_map_val g (f₂ x))
  (v : val EV HV V L) {struct v} :
  V_bind_val f₁ (HV_map_val g v) = HV_map_val g (V_bind_val f₂ v).
Proof.
+ destruct h ; simpl ;
  repeat erewrite V_bind_HV_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite V_bind_HV_map_val ;
  repeat erewrite V_bind_HV_map_tm ;
  repeat erewrite V_bind_HV_map_hd ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite V_bind_HV_map_tm ;
  repeat erewrite V_bind_HV_map_hd ;
  crush.
Qed.

End section_V_bind_HV_map.


Section section_V_bind_L_map.

Local Fact V_bind_L_map_aux1
  (EV HV V V' L L' : Set)
  (g : L → L') (f₁ : V → val EV HV V' L') (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = L_map_val g (f₂ x)) :
  ∀ x : inc V, V_lift_inc f₁ x = L_map_val g (V_lift_inc f₂ x).
Proof.
  destruct x ; simpl ; [ crush | ].
  rewrite Hf, V_L_map_val ; crush.
Qed.

Local Fact V_bind_L_map_aux2
  (EV HV V V' L L' : Set)
  (g : L → L') (f₁ : V → val EV HV V' L') (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = L_map_val g (f₂ x)) :
∀ x : V, (L_shift_val ∘ f₁) x = L_map_val (map_inc g) ((L_shift_val ∘ f₂) x).
Proof.
intro ; unfold compose ; rewrite Hf.
repeat erewrite L_map_map_val ; crush.
Qed.

Local Fact V_bind_L_map_aux3
  (EV HV V V' L L' : Set)
  (g : L → L') (f₁ : V → val EV HV V' L') (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = L_map_val g (f₂ x)) :
∀ x : V, (EV_shift_val ∘ f₁) x = L_map_val g ((EV_shift_val ∘ f₂) x).
Proof.
intro ; unfold compose ; rewrite <- EV_L_map_val ; crush.
Qed.

Local Fact V_bind_L_map_aux4
  (EV HV V V' L L' : Set)
  (g : L → L') (f₁ : V → val EV HV V' L') (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = L_map_val g (f₂ x)) :
∀ x : V, (HV_shift_val ∘ f₁) x = L_map_val g ((HV_shift_val ∘ f₂) x).
Proof.
intro ; unfold compose ; rewrite <- HV_L_map_val ; crush.
Qed.

Hint Resolve V_bind_L_map_aux1 V_bind_L_map_aux2 V_bind_L_map_aux3 V_bind_L_map_aux4.

Fixpoint
  V_bind_L_map_hd (EV HV V V' L L' : Set)
  (g : L → L') (f₁ : V → val EV HV V' L') (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = L_map_val g (f₂ x))
  (h : hd EV HV V L) {struct h} :
  V_bind_hd f₁ (L_map_hd g h) = L_map_hd g (V_bind_hd f₂ h)
with
  V_bind_L_map_tm (EV HV V V' L L' : Set)
  (g : L → L') (f₁ : V → val EV HV V' L') (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = L_map_val g (f₂ x))
  (t : tm EV HV V L) {struct t} :
  V_bind_tm f₁ (L_map_tm g t) = L_map_tm g (V_bind_tm f₂ t)
with
  V_bind_L_map_val (EV HV V V' L L' : Set)
  (g : L → L') (f₁ : V → val EV HV V' L') (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = L_map_val g (f₂ x))
  (v : val EV HV V L) {struct v} :
  V_bind_val f₁ (L_map_val g v) = L_map_val g (V_bind_val f₂ v).
Proof.
+ destruct h ; simpl ;
  repeat erewrite V_bind_L_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite V_bind_L_map_val ;
  repeat erewrite V_bind_L_map_tm ;
  repeat erewrite V_bind_L_map_hd ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite V_bind_L_map_tm ;
  repeat erewrite V_bind_L_map_hd ;
  crush.
Qed.

Fixpoint
  V_bind_L_map_ktx EV HV V V' L L'
  (g : L → L') (f₁ : V → val EV HV V' L') (f₂ : V → val EV HV V' L)
  (Hf : ∀ x, f₁ x = L_map_val g (f₂ x))
  (K : ktx EV HV V L) {struct K} :
  V_bind_ktx f₁ (L_map_ktx g K) = L_map_ktx g (V_bind_ktx f₂ K).
Proof.
destruct K ; simpl ;
repeat erewrite V_bind_L_map_ktx ;
repeat erewrite V_bind_L_map_val ;
repeat erewrite V_bind_L_map_tm ;
repeat erewrite V_bind_L_map_hd ;
crush.
Qed.

End section_V_bind_L_map.


Section section_L_bind_EV_map.

Definition
  L_bind_EV_map_ef (EV EV' HV L L' : Set)
  (g : EV → EV') (f : L → lid L')
  (ε : ef EV HV L) :
  L_bind_ef f (EV_map_ef g ε) = EV_map_ef g (L_bind_ef f ε)
.
Proof.
destruct ε ; simpl ; crush.
Qed.

Hint Rewrite L_bind_EV_map_ef.

Fixpoint
  L_bind_EV_map_eff (EV EV' HV L L' : Set)
  (g : EV → EV') (f : L → lid L')
  (𝓔 : eff EV HV L) {struct 𝓔} :
  L_bind_eff f (EV_map_eff g 𝓔) = EV_map_eff g (L_bind_eff f 𝓔)
.
Proof.
destruct 𝓔 ; simpl ; crush.
Qed.

Hint Rewrite L_bind_EV_map_eff.

Fixpoint
  L_bind_EV_map_ty (EV EV' HV L L' : Set)
  (g : EV → EV') (f : L → lid L')
  (T : ty EV HV L) {struct T} :
  L_bind_ty f (EV_map_ty g T) = EV_map_ty g (L_bind_ty f T)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite L_bind_EV_map_ty ;
  repeat erewrite L_bind_EV_map_eff ;
  crush.
Qed.

Fixpoint
  L_bind_EV_map_hd (EV EV' HV V L L' : Set)
  (g : EV → EV') (f : L → lid L')
  (h : hd EV HV V L) {struct h} :
  L_bind_hd f (EV_map_hd g h) = EV_map_hd g (L_bind_hd f h)
with
  L_bind_EV_map_tm (EV EV' HV V L L' : Set)
  (g : EV → EV') (f : L → lid L')
  (t : tm EV HV V L) {struct t} :
  L_bind_tm f (EV_map_tm g t) = EV_map_tm g (L_bind_tm f t)
with
  L_bind_EV_map_val (EV EV' HV V L L' : Set)
  (g : EV → EV') (f : L → lid L')
  (v : val EV HV V L) {struct v} :
  L_bind_val f (EV_map_val g v) = EV_map_val g (L_bind_val f v).
Proof.
+ destruct h ; simpl ;
  repeat erewrite L_bind_EV_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite L_bind_EV_map_ty ;
  repeat erewrite L_bind_EV_map_eff ;
  repeat erewrite L_bind_EV_map_val ;
  repeat erewrite L_bind_EV_map_tm ;
  repeat erewrite L_bind_EV_map_hd ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite L_bind_EV_map_tm ;
  repeat erewrite L_bind_EV_map_hd ;
  crush.
Qed.

End section_L_bind_EV_map.


Section section_L_bind_HV_map.

Definition
  L_bind_HV_map_lbl (EV HV HV' L L' : Set)
  (g : HV → HV') (f : L → lid L')
  (ℓ : lbl HV L) :
  L_bind_lbl f (HV_map_lbl g ℓ) = HV_map_lbl g (L_bind_lbl f ℓ)
.
Proof.
destruct ℓ ; simpl ; crush.
Qed.

Hint Rewrite L_bind_HV_map_lbl.

Definition
  L_bind_HV_map_ef (EV HV HV' L L' : Set)
  (g : HV → HV') (f : L → lid L')
  (ε : ef EV HV L) :
  L_bind_ef f (HV_map_ef g ε) = HV_map_ef g (L_bind_ef f ε)
.
Proof.
destruct ε ; simpl ; crush.
Qed.

Hint Rewrite L_bind_HV_map_ef.

Fixpoint
  L_bind_HV_map_eff (EV HV HV' L L' : Set)
  (g : HV → HV') (f : L → lid L')
  (𝓔 : eff EV HV L) {struct 𝓔} :
  L_bind_eff f (HV_map_eff g 𝓔) = HV_map_eff g (L_bind_eff f 𝓔)
.
Proof.
destruct 𝓔 ; simpl ; crush.
Qed.

Hint Rewrite L_bind_HV_map_eff.

Fixpoint
  L_bind_HV_map_ty (EV HV HV' L L' : Set)
  (g : HV → HV') (f : L → lid L')
  (T : ty EV HV L) {struct T} :
  L_bind_ty f (HV_map_ty g T) = HV_map_ty g (L_bind_ty f T)
.
Proof.
+ destruct T ; simpl ;
  repeat erewrite L_bind_HV_map_ty ;
  repeat erewrite L_bind_HV_map_eff ;
  crush.
Qed.

Fixpoint
  L_bind_HV_map_hd (EV HV HV' V L L' : Set)
  (g : HV → HV') (f : L → lid L')
  (h : hd EV HV V L) {struct h} :
  L_bind_hd f (HV_map_hd g h) = HV_map_hd g (L_bind_hd f h)
with
  L_bind_HV_map_tm (EV HV HV' V L L' : Set)
  (g : HV → HV') (f : L → lid L')
  (t : tm EV HV V L) {struct t} :
  L_bind_tm f (HV_map_tm g t) = HV_map_tm g (L_bind_tm f t)
with
  L_bind_HV_map_val (EV HV HV' V L L' : Set)
  (g : HV → HV') (f : L → lid L')
  (v : val EV HV V L) {struct v} :
  L_bind_val f (HV_map_val g v) = HV_map_val g (L_bind_val f v).
Proof.
+ destruct h ; simpl ;
  repeat erewrite L_bind_HV_map_tm ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite L_bind_HV_map_ty ;
  repeat erewrite L_bind_HV_map_eff ;
  repeat erewrite L_bind_HV_map_val ;
  repeat erewrite L_bind_HV_map_tm ;
  repeat erewrite L_bind_HV_map_hd ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite L_bind_HV_map_tm ;
  repeat erewrite L_bind_HV_map_hd ;
  crush.
Qed.

End section_L_bind_HV_map.
