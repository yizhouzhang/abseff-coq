Require Import Lang.Syntax Lang.Bindings_map.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Section section_L_map_eq.

Definition L_map_lid_eq
L L' (f g : L → L') (Q : ∀ x, f x = g x)
(i : lid L) :
(L_map_lid f i) = (L_map_lid g i).
Proof.
destruct i ; crush.
Qed.

Definition L_map_lbl_eq
HV L L' (f g : L → L') (Q : ∀ x, f x = g x)
(ℓ : lbl HV L) :
(L_map_lbl f ℓ) = (L_map_lbl g ℓ).
Proof.
destruct ℓ ; simpl ;
repeat erewrite L_map_lid_eq with (g := g) ;
crush.
Qed.

Definition L_map_ef_eq
EV HV L L' (f g : L → L') (Q : ∀ x, f x = g x)
(ε : ef EV HV L) :
(L_map_ef f ε) = (L_map_ef g ε).
Proof.
destruct ε ; simpl ;
repeat erewrite L_map_lbl_eq with (g := g) ;
crush.
Qed.

Fixpoint L_map_eff_eq
EV HV L L' (f g : L → L') (Q : ∀ x, f x = g x)
(𝓔 : eff EV HV L) :
(L_map_eff f 𝓔) = (L_map_eff g 𝓔).
Proof.
destruct 𝓔 ; simpl ;
repeat erewrite L_map_ef_eq with (g := g) ;
repeat erewrite L_map_eff_eq with (g := g) ;
crush.
Qed.

Fixpoint L_map_ty_eq
EV HV L L' (f g : L → L') (Q : ∀ x, f x = g x)
(T : ty EV HV L) :
(L_map_ty f T) = (L_map_ty g T).
Proof.
destruct T ; simpl ;
repeat erewrite L_map_eff_eq with (g := g) ;
repeat erewrite L_map_ty_eq with (f := f) (g := g) ;
crush.
Qed.

Fixpoint
L_map_hd_eq
EV HV V L L' (f g : L → L') (Q : ∀ x, f x = g x)
(h : hd EV HV V L) :
(L_map_hd f h) = (L_map_hd g h)
with
L_map_tm_eq
EV HV V L L' (f g : L → L') (Q : ∀ x, f x = g x)
(t : tm EV HV V L) :
(L_map_tm f t) = (L_map_tm g t)
with
L_map_val_eq
EV HV V L L' (f g : L → L') (Q : ∀ x, f x = g x)
(v : val EV HV V L) :
(L_map_val f v) = (L_map_val g v).
Proof.
+ destruct h ; simpl ;
  repeat erewrite L_map_tm_eq with (g := g) ;
  repeat erewrite L_map_lid_eq with (g := g) ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite L_map_eff_eq with (g := g) ;
  repeat erewrite L_map_ty_eq with (g := g) ;
  repeat erewrite L_map_tm_eq with (f := f) (g := g) ;
  repeat erewrite L_map_tm_eq with (g := map_inc g) ;
  repeat erewrite L_map_hd_eq with (g := g) ;
  repeat erewrite L_map_val_eq with (g := g) ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite L_map_tm_eq with (g := g) ;
  repeat erewrite L_map_hd_eq with (g := g) ;
  crush.
Qed.

End section_L_map_eq.


Section section_V_map_eq.

Fixpoint
V_map_hd_eq
EV HV V V' L (f g : V → V') (Q : ∀ x, f x = g x)
(h : hd EV HV V L) :
(V_map_hd f h) = (V_map_hd g h)
with
V_map_tm_eq
EV HV V V' L (f g : V → V') (Q : ∀ x, f x = g x)
(t : tm EV HV V L) :
(V_map_tm f t) = (V_map_tm g t)
with
V_map_val_eq
EV HV V V' L (f g : V → V') (Q : ∀ x, f x = g x)
(v : val EV HV V L) :
(V_map_val f v) = (V_map_val g v).
Proof.
+ destruct h ; simpl ;
  repeat erewrite V_map_tm_eq with (g := map_inc (map_inc g)) ;
  crush.
+ destruct t ; simpl ;
  repeat erewrite V_map_tm_eq with (f := f)(g := g) ;
  repeat erewrite V_map_tm_eq with (f := map_inc f) (g := map_inc g) ;
  repeat erewrite V_map_hd_eq with (g := g) ;
  repeat erewrite V_map_val_eq with (g := g) ;
  crush.
+ destruct v ; simpl ;
  repeat erewrite V_map_tm_eq with (g := map_inc g) ;
  repeat erewrite V_map_tm_eq with (g := g) ;
  repeat erewrite V_map_hd_eq with (g := g) ;
  crush.
Qed.

End section_V_map_eq.
