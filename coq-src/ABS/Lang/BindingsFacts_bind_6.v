Require Import Lang.Syntax Lang.Bindings Lang.Operational.
Require Import BindingsFacts_map.

Implicit Types EV HV V L : Set.

Section section_HV_bind_eq.

Lemma HV_bind_lbl_eq
EV HV HV' V1 V2 L (f : HV → hd EV HV' V1 L) (g : HV → hd EV HV' V2 L)
(Q : ∀ p, lbl_hd (f p) = lbl_hd (g p))
(ℓ : lbl HV L) :
HV_bind_lbl f ℓ = HV_bind_lbl g ℓ.
Proof.
destruct ℓ ; crush.
Qed.

Lemma HV_bind_ef_eq
EV HV HV' V1 V2 L (f : HV → hd EV HV' V1 L) (g : HV → hd EV HV' V2 L)
(Q : ∀ p, lbl_hd (f p) = lbl_hd (g p))
(ε : ef EV HV L) :
HV_bind_ef f ε = HV_bind_ef g ε.
Proof.
destruct ε ; simpl.
+ crush.
+ erewrite HV_bind_lbl_eq ; crush.
Qed.

Fixpoint HV_bind_eff_eq
EV HV HV' V1 V2 L (f : HV → hd EV HV' V1 L) (g : HV → hd EV HV' V2 L)
(Q : ∀ p, lbl_hd (f p) = lbl_hd (g p))
(𝓔 : eff EV HV L) :
HV_bind_eff f 𝓔 = HV_bind_eff g 𝓔.
Proof.
destruct 𝓔 ; simpl.
+ crush.
+ erewrite HV_bind_ef_eq, HV_bind_eff_eq ; crush.
Qed.

Hint Rewrite lbl_EV_map_hd lbl_HV_map_hd.

Fixpoint HV_bind_ty_eq
EV HV HV' V1 V2 L (f : HV → hd EV HV' V1 L) (g : HV → hd EV HV' V2 L)
(Q : ∀ p, lbl_hd (f p) = lbl_hd (g p))
(T : ty EV HV L) :
HV_bind_ty f T = HV_bind_ty g T.
Proof.
destruct T ; simpl.
+ crush.
+ repeat erewrite HV_bind_ty_eq with (f := f) (g := g) ;
  repeat erewrite HV_bind_eff_eq with (f := f) (g := g) ;
  crush.
+ erewrite HV_bind_ty_eq ; crush.
+ erewrite HV_bind_ty_eq ; crush.
Qed.

Fixpoint
HV_bind_hd_eq
EV HV HV' V L (f g : HV → hd EV HV' V L)
(Q : ∀ p, f p = g p)
(h : hd EV HV V L) :
HV_bind_hd f h = HV_bind_hd g h
with
HV_bind_val_eq
EV HV HV' V L (f g : HV → hd EV HV' V L)
(Q : ∀ p, f p = g p)
(v : val EV HV V L) :
HV_bind_val f v = HV_bind_val g v
with
HV_bind_tm_eq
EV HV HV' V L (f g : HV → hd EV HV' V L)
(Q : ∀ p, f p = g p)
(t : tm EV HV V L) :
HV_bind_tm f t = HV_bind_tm g t.
Proof.
+ destruct h ; simpl.
  - crush.
  - erewrite HV_bind_tm_eq ; crush.
+ destruct v ; simpl.
  - crush.
  - crush.
  - erewrite HV_bind_tm_eq ; crush.
  - erewrite HV_bind_tm_eq ; crush.
  - erewrite HV_bind_tm_eq ; crush.
  - erewrite HV_bind_hd_eq ; crush.
+ destruct t ; simpl.
  - erewrite HV_bind_val_eq ; crush.
  - repeat erewrite HV_bind_tm_eq with (f := f) (g := g) ; crush.
  - erewrite HV_bind_tm_eq, HV_bind_eff_eq ; crush.
  - erewrite HV_bind_tm_eq, HV_bind_hd_eq ; crush.
  - erewrite
      HV_bind_tm_eq with (f := f),
      HV_bind_tm_eq with (f := V_shift_hd ∘ f) ;
    crush.
  - erewrite HV_bind_tm_eq ; crush.
  - erewrite HV_bind_tm_eq ; crush.
Qed.

End section_HV_bind_eq.


Section section_EV_bind_eq.

Lemma EV_bind_ef_eq
EV EV' HV L (f g : EV → eff EV' HV L)
(Q : ∀ α, f α = g α)
(ε : ef EV HV L) :
EV_bind_ef f ε = EV_bind_ef g ε.
Proof.
destruct ε ; simpl ; crush.
Qed.

Fixpoint EV_bind_eff_eq
EV EV' HV L (f g : EV → eff EV' HV L)
(Q : ∀ α, f α = g α)
(𝓔 : eff EV HV L) :
EV_bind_eff f 𝓔 = EV_bind_eff g 𝓔.
Proof.
destruct 𝓔 ; simpl.
+ crush.
+ erewrite EV_bind_ef_eq, EV_bind_eff_eq ; crush.
Qed.

Hint Rewrite lbl_EV_map_hd lbl_HV_map_hd.

Fixpoint EV_bind_ty_eq
EV EV' HV L (f g : EV → eff EV' HV L)
(Q : ∀ α, f α = g α)
(T : ty EV HV L) :
EV_bind_ty f T = EV_bind_ty g T.
Proof.
destruct T ; simpl.
+ crush.
+ repeat erewrite EV_bind_ty_eq with (f := f) (g := g) ;
  repeat erewrite EV_bind_eff_eq with (f := f) (g := g) ;
  crush.
+ erewrite EV_bind_ty_eq ; crush.
+ erewrite EV_bind_ty_eq ; crush.
Qed.

Fixpoint
EV_bind_hd_eq
EV EV' HV V L (f g : EV → eff EV' HV L)
(Q : ∀ α, f α = g α)
(h : hd EV HV V L) :
EV_bind_hd f h = EV_bind_hd g h
with
EV_bind_val_eq
EV EV' HV V L (f g : EV → eff EV' HV L)
(Q : ∀ α, f α = g α)
(v : val EV HV V L) :
EV_bind_val f v = EV_bind_val g v
with
EV_bind_tm_eq
EV EV' HV V L (f g : EV → eff EV' HV L)
(Q : ∀ α, f α = g α)
(t : tm EV HV V L) :
EV_bind_tm f t = EV_bind_tm g t.
Proof.
+ destruct h ; simpl.
  - crush.
  - erewrite EV_bind_tm_eq ; crush.
+ destruct v ; simpl.
  - crush.
  - crush.
  - erewrite EV_bind_tm_eq ; crush.
  - erewrite EV_bind_tm_eq ; crush.
  - erewrite EV_bind_tm_eq ; crush.
  - erewrite EV_bind_hd_eq ; crush.
+ destruct t ; simpl.
  - erewrite EV_bind_val_eq ; crush.
  - repeat erewrite EV_bind_tm_eq with (f := f) (g := g) ; crush.
  - erewrite EV_bind_tm_eq, EV_bind_eff_eq ; crush.
  - erewrite EV_bind_tm_eq, EV_bind_hd_eq ; crush.
  - repeat erewrite EV_bind_tm_eq with (f := f) (g := g) ; crush.
  - erewrite EV_bind_tm_eq ; crush.
  - erewrite EV_bind_tm_eq ; crush.
Qed.

End section_EV_bind_eq.


Section section_V_bind_eq.

Fixpoint
V_bind_hd_eq
EV HV V V' L (f g : V → val EV HV V' L) (Q : ∀ x, f x = g x)
(h : hd EV HV V L) :
V_bind_hd f h = V_bind_hd g h
with
V_bind_tm_eq
EV HV V V' L (f g : V → val EV HV V' L) (Q : ∀ x, f x = g x)
(t : tm EV HV V L) :
V_bind_tm f t = V_bind_tm g t
with
V_bind_val_eq
EV HV V V' L (f g : V → val EV HV V' L) (Q : ∀ x, f x = g x)
(v : val EV HV V L) :
V_bind_val f v = V_bind_val g v.
Proof.
+ destruct h ; simpl ;
  repeat erewrite V_bind_tm_eq with (g := V_lift_inc (V_lift_inc g)) ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite V_bind_tm_eq with (f := f) (g := g) ;
  repeat erewrite V_bind_tm_eq with (g := V_lift_inc g) ;
  repeat erewrite V_bind_tm_eq with (g := L_shift_val ∘ g) ;
  repeat erewrite V_bind_hd_eq with (g := g) ;
  repeat erewrite V_bind_val_eq with (g := g) ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite V_bind_tm_eq with (g := V_lift_inc g) ;
  repeat erewrite V_bind_tm_eq with (g := EV_shift_val ∘ g) ;
  repeat erewrite V_bind_tm_eq with (g := HV_shift_val ∘ g) ;
  repeat erewrite V_bind_tm_eq with (g := g) ;
  repeat erewrite V_bind_hd_eq with (g := g) ;
  crush.
Qed.

End section_V_bind_eq.
