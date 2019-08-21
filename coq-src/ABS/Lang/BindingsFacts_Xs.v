Require Import ABS.Lang.Syntax.
Require Import ABS.Lang.Bindings.
Require Import ABS.Lang.Operational.
Require Import BindingsFacts_map_0.
Require Import ABS.Util.Subset.

Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Lemma Xs_eff_app EV HV L (𝓔 𝓔' : eff EV HV L) :
Xs_eff (𝓔 ++ 𝓔') = Xs_eff 𝓔 \u Xs_eff 𝓔'.
Proof.
induction 𝓔 ; simpl.
+ rewrite union_empty_l ; auto.
+ rewrite IH𝓔, union_assoc ; auto.
Qed.

Section section_Xs_map_and_bind.

Lemma
L_map_lid_Xs
L L' (f : L → L')
(ι : lid L) :
Xs_lid (L_map_lid f ι) = Xs_lid ι.
Proof.
destruct ι ; crush.
Qed.

Hint Rewrite L_map_lid_Xs.

Lemma
L_map_lbl_Xs
HV L L' (f : L → L')
(ℓ : lbl HV L) :
Xs_lbl (L_map_lbl f ℓ) = Xs_lbl ℓ.
Proof.
destruct ℓ ; crush.
Qed.

Hint Rewrite L_map_lbl_Xs.

Lemma
L_map_ef_Xs
EV HV L L' (f : L → L')
(ε : ef EV HV L) :
Xs_ef (L_map_ef f ε) = Xs_ef ε.
Proof.
destruct ε ; crush.
Qed.

Hint Rewrite L_map_ef_Xs.

Lemma
L_map_eff_Xs
EV HV L L' (f : L → L')
(𝓔 : eff EV HV L) :
Xs_eff (L_map_eff f 𝓔) = Xs_eff 𝓔.
Proof.
induction 𝓔 ; crush.
Qed.

Hint Rewrite L_map_eff_Xs.

Fixpoint
L_map_ty_Xs
EV HV L L' (f : L → L')
(T : ty EV HV L) :
Xs_ty (L_map_ty f T) = Xs_ty T
.
Proof.
destruct T ; crush.
Qed.

Hint Rewrite L_map_ty_Xs.

Fixpoint
L_map_hd_Xs
EV HV V L L' (f : L → L')
(h : hd EV HV V L) :
Xs_hd (L_map_hd f h) = Xs_hd h
with
L_map_tm_Xs
EV HV V L L' (f : L → L')
(t : tm EV HV V L) :
Xs_tm (L_map_tm f t) = Xs_tm t
with
L_map_val_Xs
EV HV V L L' (f : L → L')
(v : val EV HV V L) :
Xs_val (L_map_val f v) = Xs_val v
.
Proof.
+ destruct h ; crush.
+ destruct t ; crush.
+ destruct v ; crush.
Qed.

Hint Rewrite L_map_hd_Xs.
Hint Rewrite L_map_tm_Xs.
Hint Rewrite L_map_val_Xs.

Lemma
HV_map_lbl_Xs
HV L HV' (f : HV → HV')
(ℓ : lbl HV L) :
Xs_lbl (HV_map_lbl f ℓ) = Xs_lbl ℓ.
Proof.
destruct ℓ ; crush.
Qed.

Hint Rewrite HV_map_lbl_Xs.

Lemma
HV_map_ef_Xs
EV HV L HV' (f : HV → HV')
(ε : ef EV HV L) :
Xs_ef (HV_map_ef f ε) = Xs_ef ε.
Proof.
destruct ε ; crush.
Qed.

Hint Rewrite HV_map_ef_Xs.

Lemma
HV_map_eff_Xs
EV HV L HV' (f : HV → HV')
(𝓔 : eff EV HV L) :
Xs_eff (HV_map_eff f 𝓔) = Xs_eff 𝓔.
Proof.
induction 𝓔 ; crush.
Qed.

Hint Rewrite HV_map_eff_Xs.

Fixpoint
HV_map_ty_Xs
EV HV L HV' (f : HV → HV')
(T : ty EV HV L) :
Xs_ty (HV_map_ty f T) = Xs_ty T
.
Proof.
destruct T ; crush.
Qed.

Hint Rewrite HV_map_ty_Xs.

Fixpoint
HV_map_hd_Xs
EV HV V L HV' (f : HV → HV')
(h : hd EV HV V L) :
Xs_hd (HV_map_hd f h) = Xs_hd h
with
HV_map_tm_Xs
EV HV V L HV' (f : HV → HV')
(t : tm EV HV V L) :
Xs_tm (HV_map_tm f t) = Xs_tm t
with
HV_map_val_Xs
EV HV V L HV' (f : HV → HV')
(v : val EV HV V L) :
Xs_val (HV_map_val f v) = Xs_val v
.
Proof.
+ destruct h ; crush.
+ destruct t ; crush.
+ destruct v ; crush.
Qed.

Hint Rewrite HV_map_hd_Xs.
Hint Rewrite HV_map_tm_Xs.
Hint Rewrite HV_map_val_Xs.

Lemma
EV_map_ef_Xs
EV HV L EV' (f : EV → EV')
(ε : ef EV HV L) :
Xs_ef (EV_map_ef f ε) = Xs_ef ε.
Proof.
destruct ε ; crush.
Qed.

Hint Rewrite EV_map_ef_Xs.

Lemma
EV_map_eff_Xs
EV HV L EV' (f : EV → EV')
(𝓔 : eff EV HV L) :
Xs_eff (EV_map_eff f 𝓔) = Xs_eff 𝓔.
Proof.
induction 𝓔 ; crush.
Qed.

Hint Rewrite EV_map_eff_Xs.

Fixpoint
EV_map_ty_Xs
EV HV L EV' (f : EV → EV')
(T : ty EV HV L) :
Xs_ty (EV_map_ty f T) = Xs_ty T
.
Proof.
destruct T ; crush.
Qed.

Hint Rewrite EV_map_ty_Xs.

Fixpoint
EV_map_hd_Xs
EV HV V L EV' (f : EV → EV')
(h : hd EV HV V L) :
Xs_hd (EV_map_hd f h) = Xs_hd h
with
EV_map_tm_Xs
EV HV V L EV' (f : EV → EV')
(t : tm EV HV V L) :
Xs_tm (EV_map_tm f t) = Xs_tm t
with
EV_map_val_Xs
EV HV V L EV' (f : EV → EV')
(v : val EV HV V L) :
Xs_val (EV_map_val f v) = Xs_val v
.
Proof.
+ destruct h ; crush.
+ destruct t ; crush.
+ destruct v ; crush.
Qed.

Hint Rewrite EV_map_hd_Xs.
Hint Rewrite EV_map_tm_Xs.
Hint Rewrite EV_map_val_Xs.

Fixpoint
V_map_hd_Xs
EV HV V L V' (f : V → V')
(h : hd EV HV V L) :
Xs_hd (V_map_hd f h) = Xs_hd h
with
V_map_tm_Xs
EV HV V L V' (f : V → V')
(t : tm EV HV V L) :
Xs_tm (V_map_tm f t) = Xs_tm t
with
V_map_val_Xs
EV HV V L V' (f : V → V')
(v : val EV HV V L) :
Xs_val (V_map_val f v) = Xs_val v
.
Proof.
+ destruct h ; crush.
+ destruct t ; crush.
+ destruct v ; crush.
Qed.

Hint Rewrite V_map_hd_Xs.
Hint Rewrite V_map_tm_Xs.
Hint Rewrite V_map_val_Xs.

Fixpoint
V_map_ktx_Xs
EV HV V L V' (f : V → V')
(K : ktx EV HV V L) :
Xs_ktx (V_map_ktx f K) = Xs_ktx K.
Proof.
destruct K ; crush.
Qed.

Hint Resolve subset_empty_l.
Hint Resolve subset_union_l subset_union_r.
Hint Resolve subset_refl.

Lemma
L_bind_lid_Xs
L L'
B (f : L → lid L') (Q : ∀ x, Xs_lid (f x) \c B)
(ι : lid L) :
Xs_lid (L_bind_lid f ι) \c Xs_lid ι \u B.
Proof.
destruct ι ; simpl ; auto.
Qed.

Lemma
L_bind_lbl_Xs
HV L L'
B (f : L → lid L') (Q : ∀ x, Xs_lid (f x) \c B)
(ℓ : lbl HV L) :
Xs_lbl (L_bind_lbl f ℓ) \c Xs_lbl ℓ \u B.
Proof.
destruct ℓ ; simpl.
+ auto.
+ eapply subset_trans ; [ apply L_bind_lid_Xs ; auto | auto ].
Qed.

Lemma
L_bind_ef_Xs
EV HV L L'
B (f : L → lid L') (Q : ∀ x, Xs_lid (f x) \c B)
(ε : ef EV HV L) :
Xs_ef (L_bind_ef f ε) \c Xs_ef ε \u B.
Proof.
destruct ε ; simpl.
+ auto.
+ eapply subset_trans ; [ apply L_bind_lbl_Xs ; auto | auto ].
Qed.

Lemma
L_bind_eff_Xs
EV HV L L'
B (f : L → lid L') (Q : ∀ x, Xs_lid (f x) \c B)
(𝓔 : eff EV HV L) :
Xs_eff (L_bind_eff f 𝓔) \c Xs_eff 𝓔 \u B.
Proof.
induction 𝓔 ; simpl.
+ auto.
+ apply union_subset.
  - eapply subset_trans ; [ apply L_bind_ef_Xs ; auto | ].
    auto using union_subset.
  - rewrite <- union_assoc ; auto.
Qed.

Hint Resolve union_subset.

Fixpoint
L_bind_ty_Xs
EV HV L L'
B (f : L → lid L') (Q : ∀ x, Xs_lid (f x) \c B)
(T : ty EV HV L) :
Xs_ty (L_bind_ty f T) \c Xs_ty T \u B
.
Proof.
destruct T ; simpl.
- auto.
- repeat apply union_subset.
  * eapply subset_trans ; [ apply L_bind_ty_Xs with (B := B) ; auto | auto ].
  * eapply subset_trans ; [ apply L_bind_ty_Xs with (B := B) ; auto | auto ].
  * eapply subset_trans ; [ apply L_bind_eff_Xs with (B := B) ; auto | auto ].
- eapply subset_trans ; [ apply L_bind_ty_Xs with (B := B) ; auto | auto ].
- eapply subset_trans ; [ apply L_bind_ty_Xs with (B := B) ; auto | auto ].
Qed.

Fixpoint
L_bind_hd_Xs
EV HV V L L'
B (f : L → lid L') (Q : ∀ x, Xs_lid (f x) \c B)
(h : hd EV HV V L) :
Xs_hd (L_bind_hd f h) \c Xs_hd h \u B
with
L_bind_val_Xs
EV HV V L L'
B (f : L → lid L') (Q : ∀ x, Xs_lid (f x) \c B)
(v : val EV HV V L) :
Xs_val (L_bind_val f v) \c Xs_val v \u B
with
L_bind_tm_Xs
EV HV V L L'
B (f : L → lid L') (Q : ∀ x, Xs_lid (f x) \c B)
(t : tm EV HV V L) :
Xs_tm (L_bind_tm f t) \c Xs_tm t \u B
.
Proof.
+ destruct h ; simpl.
  - auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_lid_Xs with (B := B) ; auto | auto ].
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | auto ].
+ destruct v ; simpl.
  - auto.
  - auto.
  - eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply L_bind_hd_Xs with (B := B) ; auto | auto ].
+ destruct t ; simpl.
  - eapply subset_trans ; [ apply L_bind_val_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | auto ].
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | auto ].
    * eapply subset_trans ; [ apply L_bind_eff_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | auto ].
    * eapply subset_trans ; [ apply L_bind_hd_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | auto ].
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply L_bind_tm_Xs with (B := B) ; auto | auto ].
    * auto.
Qed.

Lemma
HV_bind_lbl_Xs
EV HV V L HV'
B (f : HV → hd EV HV' V L) (Q : ∀ x, Xs_lbl (lbl_hd (f x)) \c B)
(ℓ : lbl HV L) :
Xs_lbl (HV_bind_lbl f ℓ) \c Xs_lbl ℓ \u B.
Proof.
destruct ℓ ; simpl ; auto.
Qed.

Lemma
HV_bind_ef_Xs
EV HV V L HV'
B (f : HV → hd EV HV' V L) (Q : ∀ x, Xs_lbl (lbl_hd (f x)) \c B)
(ε : ef EV HV L) :
Xs_ef (HV_bind_ef f ε) \c Xs_ef ε \u B.
Proof.
destruct ε ; simpl.
+ auto.
+ eapply subset_trans ; [ apply HV_bind_lbl_Xs ; auto | auto ].
Qed.

Lemma
HV_bind_eff_Xs
EV HV V L HV'
B (f : HV → hd EV HV' V L) (Q : ∀ x, Xs_lbl (lbl_hd (f x)) \c B)
(𝓔 : eff EV HV L) :
Xs_eff (HV_bind_eff f 𝓔) \c Xs_eff 𝓔 \u B.
Proof.
induction 𝓔 ; simpl.
+ auto.
+ apply union_subset.
  - eapply subset_trans ; [ apply HV_bind_ef_Xs ; auto | ].
    auto using union_subset.
  - rewrite <- union_assoc ; auto.
Qed.

Hint Rewrite lbl_EV_map_hd lbl_HV_map_hd.

Fixpoint
HV_bind_ty_Xs
EV HV V L HV'
B (f : HV → hd EV HV' V L) (Q : ∀ x, Xs_lbl (lbl_hd (f x)) \c B)
(T : ty EV HV L) :
Xs_ty (HV_bind_ty f T) \c Xs_ty T \u B
.
Proof.
destruct T ; simpl.
- auto.
- repeat apply union_subset.
  * eapply subset_trans ; [ apply HV_bind_ty_Xs with (B := B) ; auto | auto ].
  * eapply subset_trans ; [ apply HV_bind_ty_Xs with (B := B) ; auto | auto ].
  * eapply subset_trans ; [ apply HV_bind_eff_Xs with (B := B) ; auto | auto ].
- eapply subset_trans ; [ apply HV_bind_ty_Xs with (B := B) ; auto | auto ].
- eapply subset_trans ; [ apply HV_bind_ty_Xs with (B := B) ; auto | auto ].
Qed.

Lemma Xs_lbl_hd EV HV V L (h : hd EV HV V L) B :
Xs_hd h \c B → Xs_lbl (lbl_hd h) \c B.
Proof.
destruct h ; eauto using union_subset_inv_l.
Qed.

Hint Resolve Xs_lbl_hd.

Fixpoint
HV_bind_hd_Xs
EV HV V L HV'
B (f : HV → hd EV HV' V L) (Q : ∀ x, Xs_hd (f x) \c B)
(h : hd EV HV V L) :
Xs_hd (HV_bind_hd f h) \c Xs_hd h \u B
with
HV_bind_val_Xs
EV HV V L HV'
B (f : HV → hd EV HV' V L) (Q : ∀ x, Xs_hd (f x) \c B)
(v : val EV HV V L) :
Xs_val (HV_bind_val f v) \c Xs_val v \u B
with
HV_bind_tm_Xs
EV HV V L HV'
B (f : HV → hd EV HV' V L) (Q : ∀ x, Xs_hd (f x) \c B)
(t : tm EV HV V L) :
Xs_tm (HV_bind_tm f t) \c Xs_tm t \u B
.
Proof.
+ destruct h ; simpl.
  - auto.
  - apply union_subset.
    * auto.
    * eapply subset_trans ; [ apply HV_bind_tm_Xs with (B := B) ; auto | auto ].
+ destruct v ; simpl.
  - auto.
  - auto.
  - eapply subset_trans ; [ apply HV_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply HV_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply HV_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply HV_bind_hd_Xs with (B := B) ; auto | auto ].
+ destruct t ; simpl.
  - eapply subset_trans ; [ apply HV_bind_val_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply HV_bind_tm_Xs with (B := B) ; auto | auto ].
    * eapply subset_trans ; [ apply HV_bind_tm_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply HV_bind_tm_Xs with (B := B) ; auto | auto ].
    * eapply subset_trans ; [ apply HV_bind_eff_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply HV_bind_tm_Xs with (B := B) ; auto | auto ].
    * eapply subset_trans ; [ apply HV_bind_hd_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply HV_bind_tm_Xs with (B := B) ; auto | auto ].
    * eapply subset_trans ; [ apply HV_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply HV_bind_tm_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply HV_bind_tm_Xs with (B := B) ; auto | auto ].
    * auto.
Qed.

Lemma
EV_bind_ef_Xs
EV HV L EV'
B (f : EV → eff EV' HV L) (Q : ∀ x, Xs_eff (f x) \c B)
ε :
Xs_eff (EV_bind_ef f ε) \c Xs_ef ε \u B.
Proof.
destruct ε ; simpl.
+ auto.
+ apply union_subset ; auto.
Qed.

Lemma
EV_bind_eff_Xs
EV HV L EV'
B (f : EV → eff EV' HV L) (Q : ∀ x, Xs_eff (f x) \c B)
𝓔 :
Xs_eff (EV_bind_eff f 𝓔) \c Xs_eff 𝓔 \u B.
Proof.
induction 𝓔 ; simpl.
+ auto.
+ rewrite Xs_eff_app.
  apply union_subset.
  - eapply subset_trans ; [ apply EV_bind_ef_Xs ; auto | ].
    auto using union_subset.
  - rewrite <- union_assoc ; auto.
Qed.

Fixpoint
EV_bind_ty_Xs
EV HV L EV'
B (f : EV → eff EV' HV L) (Q : ∀ x, Xs_eff (f x) \c B)
T :
Xs_ty (EV_bind_ty f T) \c Xs_ty T \u B
.
Proof.
destruct T ; simpl.
  - auto.
  - repeat apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_ty_Xs with (B := B) ; auto | auto ].
    * eapply subset_trans ; [ apply EV_bind_ty_Xs with (B := B) ; auto | auto ].
    * eapply subset_trans ; [ apply EV_bind_eff_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply EV_bind_ty_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply EV_bind_ty_Xs with (B := B) ; auto | auto ].
Qed.

Fixpoint
EV_bind_hd_Xs
EV HV V L EV'
B (f : EV → eff EV' HV L) (Q : ∀ x, Xs_eff (f x) \c B)
(h : hd EV HV V L) :
Xs_hd (EV_bind_hd f h) \c Xs_hd h \u B
with
EV_bind_val_Xs
EV HV V L EV'
B (f : EV → eff EV' HV L) (Q : ∀ x, Xs_eff (f x) \c B)
(v : val EV HV V L) :
Xs_val (EV_bind_val f v) \c Xs_val v \u B
with
EV_bind_tm_Xs
EV HV V L EV'
B (f : EV → eff EV' HV L) (Q : ∀ x, Xs_eff (f x) \c B)
(t : tm EV HV V L) :
Xs_tm (EV_bind_tm f t) \c Xs_tm t \u B
.
Proof.
+ destruct h ; simpl.
  - auto.
  - apply union_subset.
    * auto.
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | auto ].
+ destruct v ; simpl.
  - auto.
  - auto.
  - eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply EV_bind_hd_Xs with (B := B) ; auto | auto ].
+ destruct t ; simpl.
  - eapply subset_trans ; [ apply EV_bind_val_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | auto ].
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | auto ].
    * eapply subset_trans ; [ apply EV_bind_eff_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | auto ].
    * eapply subset_trans ; [ apply EV_bind_hd_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | auto ].
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply EV_bind_tm_Xs with (B := B) ; auto | auto ].
    * auto.
Qed.

Fixpoint
V_bind_hd_Xs
EV HV V L V'
B (f : V → val EV HV V' L) (Q : ∀ x, Xs_val (f x) \c B)
h :
Xs_hd (V_bind_hd f h) \c Xs_hd h \u B
with
V_bind_val_Xs
EV HV V L V'
B (f : V → val EV HV V' L) (Q : ∀ x, Xs_val (f x) \c B)
v :
Xs_val (V_bind_val f v) \c Xs_val v \u B
with
V_bind_tm_Xs
EV HV V L V'
B (f : V → val EV HV V' L) (Q : ∀ x, Xs_val (f x) \c B)
t :
Xs_tm (V_bind_tm f t) \c Xs_tm t \u B
.
Proof.
+ destruct h ; simpl.
  - auto.
  - apply union_subset.
    * auto.
    * eapply subset_trans ; [ apply V_bind_tm_Xs with (B := B) ; auto | auto ].
+ destruct v ; simpl.
  - auto.
  - auto.
  - eapply subset_trans ; [ apply V_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply V_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply V_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply V_bind_hd_Xs with (B := B) ; auto | auto ].
+ destruct t ; simpl.
  - auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply V_bind_tm_Xs with (B := B) ; auto | auto ].
    * eapply subset_trans ; [ apply V_bind_tm_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply V_bind_tm_Xs with (B := B) ; auto | auto ].
    * auto.
  - apply union_subset.
    * eapply subset_trans ; [ apply V_bind_tm_Xs with (B := B) ; auto | auto ].
    * eapply subset_trans ; [ apply V_bind_hd_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply V_bind_tm_Xs with (B := B) ; auto | auto ].
    * eapply subset_trans ; [ apply V_bind_tm_Xs with (B := B) ; auto | auto ].
  - eapply subset_trans ; [ apply V_bind_tm_Xs with (B := B) ; auto | auto ].
  - apply union_subset.
    * eapply subset_trans ; [ apply V_bind_tm_Xs with (B := B) ; auto | auto ].
    * auto.
Qed.

End section_Xs_map_and_bind.

Section section_Xs_ktx_plug.

Hint Rewrite union_empty_l.

Lemma Xs_ktx_plug EV HV V L (K : ktx EV HV V L) t :
Xs_tm (ktx_plug K t) = Xs_ktx K \u Xs_tm t.
Proof.
induction K ; simpl.
+ crush.
+ rewrite IHK.
  rewrite <- union_assoc, (union_comm (Xs_tm t)).
  rewrite union_assoc.
  crush.
+ rewrite IHK.
  rewrite <- union_assoc, (union_comm (Xs_tm t)).
  rewrite union_assoc.
  crush.
+ rewrite IHK.
  rewrite <- union_assoc, (union_comm (Xs_tm t)).
  rewrite union_assoc.
  crush.
+ rewrite IHK.
  rewrite <- union_assoc, (union_comm (Xs_tm t)).
  rewrite union_assoc.
  crush.
+ rewrite IHK.
  rewrite <- union_assoc, (union_comm (Xs_tm t)).
  rewrite union_assoc.
  crush.
+ rewrite IHK.
  rewrite union_assoc, (union_comm _ (Xs_ktx K)).
  crush.
Qed.

End section_Xs_ktx_plug.
