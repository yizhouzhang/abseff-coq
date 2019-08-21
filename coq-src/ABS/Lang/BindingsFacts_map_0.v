Require Import FinFun.
Require Import Lang.Syntax Lang.Bindings_map.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Section section_L_map_inj.

Hint Extern 0 => match goal with
| [ Inj : Injective ?f , Heq : ?f _ = ?f _ |- _ ] =>
  let H := fresh "H" in apply Inj in Heq as H ; rewrite H in *
end.

Lemma L_map_lid_inj
L L' (f : L → L') (Inj : Injective f)
(i i' : lid L)
(H : L_map_lid f i = L_map_lid f i') :
i = i'.
Proof.
destruct i, i' ; simpl in * ; inversion H ; crush.
Qed.

Lemma L_map_lbl_inj
HV L L' (f : L → L') (Inj : Injective f)
(l l' : lbl HV L)
(H : L_map_lbl f l = L_map_lbl f l') :
l = l'.
Proof.
destruct l, l' ; inversion H ; clear H ;
repeat match goal with
| [ H : L_map_lid ?f _ = L_map_lid ?f _ |- _ ] =>
  apply L_map_lid_inj in H ; subst ; clear H
end ;
crush.
Qed.

Lemma L_map_ef_inj
EV HV L L' (f : L → L') (Inj : Injective f)
(ε ε' : ef EV HV L)
(H : L_map_ef f ε = L_map_ef f ε') :
ε = ε'.
Proof.
destruct ε, ε' ; inversion H ; clear H;
repeat match goal with
| [ H : L_map_lbl ?f _ = L_map_lbl ?f _ |- _ ] =>
  apply L_map_lbl_inj in H ; subst ; clear H
end ;
crush.
Qed.

Fixpoint L_map_eff_inj
EV HV L L' (f : L → L') (Inj : Injective f)
(𝓔 𝓔' : eff EV HV L)
(H : L_map_eff f 𝓔 = L_map_eff f 𝓔') :
𝓔 = 𝓔'.
Proof.
destruct 𝓔, 𝓔' ; inversion H ; clear H ;
repeat match goal with
| [ H : L_map_ef ?f _ = L_map_ef ?f _ |- _ ] =>
  apply L_map_ef_inj in H ; subst ; clear H
| [ H : L_map_eff ?f _ = L_map_eff ?f _ |- _ ] =>
  apply L_map_eff_inj in H ; subst ; clear H
end ;
crush.
Qed.

Fixpoint L_map_ty_inj
EV HV L L' (f : L → L') (Inj : Injective f)
(T T' : ty EV HV L)
(H : L_map_ty f T = L_map_ty f T') :
T = T'.
Proof.
destruct T, T' ; inversion H ; clear H ;
repeat match goal with
| [ H : L_map_ty ?f _ = L_map_ty ?f _ |- _ ] =>
  apply L_map_ty_inj in H ; subst ; clear H
| [ H : L_map_eff ?f _ = L_map_eff ?f _ |- _ ] =>
  apply L_map_eff_inj in H ; subst ; clear H
end ;
crush.
Qed.

Hint Resolve map_inc_is_injective.

Fixpoint
L_map_hd_inj
EV HV V L L' (f : L → L') (Inj : Injective f)
(h h' : hd EV HV V L)
(H : L_map_hd f h = L_map_hd f h') :
h = h'
with
L_map_tm_inj
EV HV V L L' (f : L → L') (Inj : Injective f)
(t t' : tm EV HV V L)
(H : L_map_tm f t = L_map_tm f t') :
t = t'
with
L_map_val_inj
EV HV V L L' (f : L → L') (Inj : Injective f)
(v v' : val EV HV V L)
(H : L_map_val f v = L_map_val f v') :
v = v'.
Proof.
+ destruct h, h' ; inversion H ; clear H ;
  repeat match goal with
  | [ H : L_map_tm ?f _ = L_map_tm ?f _ |- _ ] =>
    apply L_map_tm_inj in H ; subst ; clear H
  | [ H : L_map_lid ?f _ = L_map_lid ?f _ |- _ ] =>
    apply L_map_lid_inj in H ; subst ; clear H
  end ;
  crush.
+ destruct t, t' ; inversion H ; clear H ;
  repeat match goal with
  | [ H : L_map_tm ?f _ = L_map_tm ?f _ |- _ ] =>
    apply L_map_tm_inj in H ; subst ; clear H
  | [ H : L_map_hd ?f _ = L_map_hd ?f _ |- _ ] =>
    apply L_map_hd_inj in H ; subst ; clear H
  | [ H : L_map_val ?f _ = L_map_val ?f _ |- _ ] =>
    apply L_map_val_inj in H ; subst ; clear H
  | [ H : L_map_ty ?f _ = L_map_ty ?f _ |- _ ] =>
    apply L_map_ty_inj in H ; subst ; clear H
  | [ H : L_map_eff ?f _ = L_map_eff ?f _ |- _ ] =>
    apply L_map_eff_inj in H ; subst ; clear H
  end ;
  crush.
+ destruct v, v' ; inversion H ; clear H ;
  repeat match goal with
  | [ H : L_map_tm ?f _ = L_map_tm ?f _ |- _ ] =>
    apply L_map_tm_inj in H ; subst ; clear H
  | [ H : L_map_hd ?f _ = L_map_hd ?f _ |- _ ] =>
    apply L_map_hd_inj in H ; subst ; clear H
  end ;
  crush.
Qed.

End section_L_map_inj.


Lemma lbl_EV_map_hd EV EV' HV V L
  (f : EV → EV') (h : hd EV HV V L) :
  lbl_hd (EV_map_hd f h) = lbl_hd h.
Proof.
  induction h ; crush.
Qed.

Lemma lbl_V_map_hd EV HV V V' L
  (f : V → V') (h : hd EV HV V L) :
  lbl_hd (V_map_hd f h) = lbl_hd h.
Proof.
  induction h ; crush.
Qed.

Lemma lbl_HV_map_hd EV HV HV' V L
  (f : HV → HV') (h : hd EV HV V L) :
  lbl_hd (HV_map_hd f h) = HV_map_lbl f (lbl_hd h).
Proof.
  induction h ; crush.
Qed.

Lemma lbl_L_map_hd EV HV V L L'
  (f : L → L') (h : hd EV HV V L) :
  lbl_hd (L_map_hd f h) = L_map_lbl f (lbl_hd h).
Proof.
  induction h ; crush.
Qed.

Lemma EV_map_eff_app EV EV' HV L
  (f : EV → EV') (𝓔₁ 𝓔₂ : eff EV HV L) :
  EV_map_eff f 𝓔₁ ++ EV_map_eff f 𝓔₂ = EV_map_eff f (𝓔₁ ++ 𝓔₂).
Proof.
  induction 𝓔₁ ; crush.
Qed.

Lemma HV_map_eff_app (EV HV HV' L : Set)
  (f : HV → HV') (𝓔₁ 𝓔₂ : eff EV HV L) :
  HV_map_eff f 𝓔₁ ++ HV_map_eff f 𝓔₂ = HV_map_eff f (𝓔₁ ++ 𝓔₂).
Proof.
  induction 𝓔₁ ; crush.
Qed.

Lemma L_map_eff_app (EV HV L L' : Set)
  (f : L → L') (𝓔₁ 𝓔₂ : eff EV HV L) :
  L_map_eff f 𝓔₁ ++ L_map_eff f 𝓔₂ = L_map_eff f (𝓔₁ ++ 𝓔₂).
Proof.
  induction 𝓔₁ ; crush.
Qed.

Lemma EV_map_XEnv_empty
EV EV' HV (f : EV → EV') :
EV_map_XEnv f empty = (empty : XEnv EV' HV).
Proof.
apply map_empty.
Qed.

Lemma HV_map_XEnv_empty
EV HV HV' (f : HV → HV') :
HV_map_XEnv f empty = (empty : XEnv EV HV').
Proof.
apply map_empty.
Qed.

Lemma EV_map_XEnv_single
EV EV' HV (f : EV → EV') X (T : ty EV HV ∅) (𝓔 : eff EV HV ∅) :
EV_map_XEnv f (X ~ (T, 𝓔)) = X ~ (EV_map_ty f T, EV_map_eff f 𝓔).
Proof.
apply map_single.
Qed.

Lemma HV_map_XEnv_single
EV HV HV' (f : HV → HV') X (T : ty EV HV ∅) (𝓔 : eff EV HV ∅) :
HV_map_XEnv f (X ~ (T, 𝓔)) = X ~ (HV_map_ty f T, HV_map_eff f 𝓔).
Proof.
apply map_single.
Qed.

Lemma EV_map_XEnv_concat
EV EV' HV (f : EV → EV') (Ξ Ξ' : XEnv EV HV) :
EV_map_XEnv f (Ξ & Ξ') =
(EV_map_XEnv f Ξ) & (EV_map_XEnv f Ξ').
Proof.
apply map_concat.
Qed.

Lemma HV_map_XEnv_concat
EV HV HV' (f : HV → HV') (Ξ Ξ' : XEnv EV HV) :
HV_map_XEnv f (Ξ & Ξ') =
(HV_map_XEnv f Ξ) & (HV_map_XEnv f Ξ').
Proof.
apply map_concat.
Qed.

Lemma EV_map_XEnv_dom
EV EV' HV (f : EV → EV') (Ξ : XEnv EV HV) :
dom (EV_map_XEnv f Ξ) = dom Ξ.
Proof.
induction Ξ as [ | ? ? [? ?] IHΞ ] using env_ind.
+ rewrite EV_map_XEnv_empty.
  repeat rewrite dom_empty.
  reflexivity.
+ rewrite EV_map_XEnv_concat, EV_map_XEnv_single.
  repeat rewrite dom_concat, dom_single.
  rewrite IHΞ.
  reflexivity.
Qed.

Lemma HV_map_XEnv_dom
EV HV HV' (f : HV → HV') (Ξ : XEnv EV HV) :
dom (HV_map_XEnv f Ξ) = dom Ξ.
Proof.
induction Ξ as [ | ? ? [? ?] IHΞ ] using env_ind.
+ rewrite HV_map_XEnv_empty.
  repeat rewrite dom_empty.
  reflexivity.
+ rewrite HV_map_XEnv_concat, HV_map_XEnv_single.
  repeat rewrite dom_concat, dom_single.
  rewrite IHΞ.
  reflexivity.
Qed.


Section section_binds_EV_map.
Context (EV EV' HV : Set).
Context (f : EV → EV').
Context (X : var).

Lemma binds_EV_map T 𝓔 (Ξ : XEnv EV HV) :
binds X (T, 𝓔) Ξ →
binds X (EV_map_ty f T, EV_map_eff f 𝓔) (EV_map_XEnv f Ξ).
Proof.
intro Hbinds.
induction Ξ as [ | Ξ' X' [ T' 𝓔' ] IHΞ' ] using env_ind.
+ apply binds_empty_inv in Hbinds ; crush.
+ apply binds_concat_inv in Hbinds.
  rewrite EV_map_XEnv_concat, EV_map_XEnv_single.
  destruct Hbinds as [ Hbinds | Hbinds ].
  - apply binds_single_inv in Hbinds ; crush.
  - destruct Hbinds as [ FrX Hbinds ] ; auto.
Qed.

Lemma binds_EV_map_inv
(T' : ty EV' HV ∅) (𝓔' : eff EV' HV ∅) (Ξ : XEnv EV HV) :
binds X (T', 𝓔') (EV_map_XEnv f Ξ) →
∃ T 𝓔,
T' = EV_map_ty f T ∧ 𝓔' = EV_map_eff f 𝓔 ∧ binds X (T, 𝓔) Ξ.
Proof.
intro Hbinds'.
induction Ξ as [ | Ξ Y [ T 𝓔 ] IHΞ ] using env_ind.
+ rewrite EV_map_XEnv_empty in Hbinds'.
  apply binds_empty_inv in Hbinds' ; crush.
+ rewrite EV_map_XEnv_concat, EV_map_XEnv_single in Hbinds'.
  apply binds_concat_inv in Hbinds'.
  destruct Hbinds' as [ Hbinds' | Hbinds' ].
  - apply binds_single_inv in Hbinds'.
    destruct Hbinds' as [ [] Heq ].
    inversion Heq ; subst.
    eauto.
  - destruct Hbinds' as [ FrX Hbinds' ].
    specialize (IHΞ Hbinds').
    destruct IHΞ as [T'' [𝓔'' [? [? ?]]]].
    repeat eexists ; eauto.
Qed.

End section_binds_EV_map.


Section section_binds_HV_map.
Context (EV HV HV' : Set).
Context (f : HV → HV').
Context (X : var).

Lemma binds_HV_map T 𝓔 (Ξ : XEnv EV HV) :
binds X (T, 𝓔) Ξ →
binds X (HV_map_ty f T, HV_map_eff f 𝓔) (HV_map_XEnv f Ξ).
Proof.
intro Hbinds.
induction Ξ as [ | Ξ' X' [ T' 𝓔' ] IHΞ' ] using env_ind.
+ apply binds_empty_inv in Hbinds ; crush.
+ apply binds_concat_inv in Hbinds.
  rewrite HV_map_XEnv_concat, HV_map_XEnv_single.
  destruct Hbinds as [ Hbinds | Hbinds ].
  - apply binds_single_inv in Hbinds ; crush.
  - destruct Hbinds as [ FrX Hbinds ] ; auto.
Qed.

Lemma binds_HV_map_inv
(T' : ty EV HV' ∅) (𝓔' : eff EV HV' ∅) (Ξ : XEnv EV HV) :
binds X (T', 𝓔') (HV_map_XEnv f Ξ) →
∃ T 𝓔,
T' = HV_map_ty f T ∧ 𝓔' = HV_map_eff f 𝓔 ∧ binds X (T, 𝓔) Ξ.
Proof.
intro Hbinds'.
induction Ξ as [ | Ξ Y [ T 𝓔 ] IHΞ ] using env_ind.
+ rewrite HV_map_XEnv_empty in Hbinds'.
  apply binds_empty_inv in Hbinds' ; crush.
+ rewrite HV_map_XEnv_concat, HV_map_XEnv_single in Hbinds'.
  apply binds_concat_inv in Hbinds'.
  destruct Hbinds' as [ Hbinds' | Hbinds' ].
  - apply binds_single_inv in Hbinds'.
    destruct Hbinds' as [ [] Heq ].
    inversion Heq ; subst.
    eauto.
  - destruct Hbinds' as [ FrX Hbinds' ].
    specialize (IHΞ Hbinds').
    destruct IHΞ as [T'' [𝓔'' [? [? ?]]]].
    repeat eexists ; eauto.
Qed.

End section_binds_HV_map.

