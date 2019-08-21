Require Import Lang.Syntax Lang.Bindings FinFun.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Section section_L_bind_inj.

Local Fact disjoint_same_inv A (x : A) : disjoint \{x} \{x} → False.
Proof.
unfold disjoint ; rewrite inter_same ; intro H.
erewrite <- in_empty.
rewrite <- H.
rewrite in_singleton ; reflexivity.
Qed.

Lemma L_bind_lid_inj
L L' (f : L → lid L')
(Inj : Injective f)
(i1 i2 : lid L)
(Q1 : ∀ α, disjoint (Xs_lid (f α)) (Xs_lid i1))
(Q2 : ∀ α, disjoint (Xs_lid (f α)) (Xs_lid i2))
(H : L_bind_lid f i1 = L_bind_lid f i2) :
i1 = i2.
Proof.
destruct i1 as [ α1 | X1 ], i2 as [ α2 | X2 ] ; simpl in *.
+ specialize (Inj α1 α2 H) ; congruence.
+ exfalso.
  specialize (Q2 α1) ; rewrite H in Q2 ; simpl in Q2.
  apply disjoint_same_inv in Q2 ; auto.
+ exfalso.
  specialize (Q1 α2) ; rewrite <- H in Q1 ; simpl in Q1.
  apply disjoint_same_inv in Q1 ; auto.
+ crush.
Qed.

Lemma L_bind_lbl_inj
HV L L' (f : L → lid L')
(Inj : Injective f)
(l1 l2 : lbl HV L)
(Q1 : ∀ α, disjoint (Xs_lid (f α)) (Xs_lbl l1))
(Q2 : ∀ α, disjoint (Xs_lid (f α)) (Xs_lbl l2))
(H : L_bind_lbl f l1 = L_bind_lbl f l2) :
l1 = l2.
Proof.
destruct l1, l2 ; simpl in * ; try inversion H ; clear H ;
repeat match goal with
| [ H : L_bind_lid ?f _ = L_bind_lid ?f _ |- _ ] =>
  apply L_bind_lid_inj in H ; subst ; clear H
end ;
crush.
Qed.

Lemma L_bind_ef_inj
EV HV L L' (f : L → lid L')
(Inj : Injective f)
(ε1 ε2 : ef EV HV L)
(Q1 : ∀ α, disjoint (Xs_lid (f α)) (Xs_ef ε1))
(Q2 : ∀ α, disjoint (Xs_lid (f α)) (Xs_ef ε2))
(H : L_bind_ef f ε1 = L_bind_ef f ε2) :
ε1 = ε2.
Proof.
destruct ε1, ε2 ; simpl in * ; try inversion H ; clear H ;
repeat match goal with
| [ H : L_bind_lbl ?f _ = L_bind_lbl ?f _ |- _ ] =>
  apply L_bind_lbl_inj in H ; subst ; clear H
end ;
crush.
Qed.

End section_L_bind_inj.

Lemma lbl_EV_bind_hd
EV EV' HV V L (f : EV → eff EV' HV L)
(h : hd EV HV V L) :
lbl_hd (EV_bind_hd f h) = lbl_hd h.
Proof.
induction h ; crush.
Qed.

Lemma lbl_L_bind_hd EV HV V L L'
  (f : L → lid L') (h : hd EV HV V L) :
  lbl_hd (L_bind_hd f h) = L_bind_lbl f (lbl_hd h).
Proof.
  induction h ; crush.
Qed.

Lemma lbl_V_bind_hd EV HV V V' L
  (f : V → val EV HV V' L) (h : hd EV HV V L) :
  lbl_hd (V_bind_hd f h) = lbl_hd h.
Proof.
  induction h ; crush.
Qed.

Lemma lbl_HV_bind_hd EV EV' HV HV' V V' L
  (f : HV → hd EV HV' V L) (g : HV → hd EV' HV' V' L)
  (Q : ∀ p, lbl_hd (f p) = lbl_hd (g p))
  (h : hd EV' HV V' L) :
  lbl_hd (HV_bind_hd g h) = HV_bind_lbl f (lbl_hd h).
Proof.
  induction h ; crush.
Qed.

Lemma EV_bind_XEnv_empty
EV EV' HV (f : EV → eff EV' HV ∅) :
EV_bind_XEnv f empty = empty.
Proof.
apply map_empty.
Qed.

Lemma EV_bind_XEnv_single
EV EV' HV (f : EV → eff EV' HV ∅) X (T : ty EV HV ∅) (𝓔 : eff EV HV ∅) :
EV_bind_XEnv f (X ~ (T, 𝓔)) = X ~ (EV_bind_ty f T, EV_bind_eff f 𝓔).
Proof.
apply map_single.
Qed.

Lemma EV_bind_XEnv_concat
EV EV' HV (f : EV → eff EV' HV ∅) (Ξ Ξ' : XEnv EV HV) :
EV_bind_XEnv f (Ξ & Ξ') =
(EV_bind_XEnv f Ξ) & (EV_bind_XEnv f Ξ').
Proof.
apply map_concat.
Qed.

Lemma EV_bind_XEnv_dom
EV EV' HV (f : EV → eff EV' HV ∅) (Ξ : XEnv EV HV) :
dom (EV_bind_XEnv f Ξ) = dom Ξ.
Proof.
induction Ξ as [ | ? ? [? ?] IHΞ ] using env_ind.
+ rewrite EV_bind_XEnv_empty.
  repeat rewrite dom_empty.
  reflexivity.
+ rewrite EV_bind_XEnv_concat, EV_bind_XEnv_single.
  repeat rewrite dom_concat, dom_single.
  rewrite IHΞ.
  reflexivity.
Qed.

Lemma HV_bind_XEnv_empty
EV HV HV' V (f : HV → hd EV HV' V ∅) :
HV_bind_XEnv f (empty : XEnv EV HV) = empty.
Proof.
apply map_empty.
Qed.

Lemma HV_bind_XEnv_single
EV HV HV' V (f : HV → hd EV HV' V ∅) X (T : ty EV HV ∅) (𝓔 : eff EV HV ∅) :
HV_bind_XEnv f (X ~ (T, 𝓔)) = X ~ (HV_bind_ty f T, HV_bind_eff f 𝓔).
Proof.
apply map_single.
Qed.

Lemma HV_bind_XEnv_concat
EV HV HV' V (f : HV → hd EV HV' V ∅) (Ξ Ξ' : XEnv EV HV) :
HV_bind_XEnv f (Ξ & Ξ') =
(HV_bind_XEnv f Ξ) & (HV_bind_XEnv f Ξ').
Proof.
apply map_concat.
Qed.

Lemma HV_bind_XEnv_dom
EV HV HV' V (f : HV → hd EV HV' V ∅) (Ξ : XEnv EV HV) :
dom (HV_bind_XEnv f Ξ) = dom Ξ.
Proof.
induction Ξ as [ | ? ? [? ?] IHΞ ] using env_ind.
+ rewrite HV_bind_XEnv_empty.
  repeat rewrite dom_empty.
  reflexivity.
+ rewrite HV_bind_XEnv_concat, HV_bind_XEnv_single.
  repeat rewrite dom_concat, dom_single.
  rewrite IHΞ.
  reflexivity.
Qed.


Section section_binds_EV_bind.
Context (EV EV' HV : Set).
Context (f : EV → eff EV' HV ∅).
Context (X : var).

Lemma binds_EV_bind T 𝓔 (Ξ : XEnv EV HV) :
binds X (T, 𝓔) Ξ →
binds X (EV_bind_ty f T, EV_bind_eff f 𝓔) (EV_bind_XEnv f Ξ).
Proof.
intro Hbinds.
induction Ξ as [ | Ξ' X' [ T' 𝓔' ] IHΞ' ] using env_ind.
+ apply binds_empty_inv in Hbinds ; crush.
+ apply binds_concat_inv in Hbinds.
  rewrite EV_bind_XEnv_concat, EV_bind_XEnv_single.
  destruct Hbinds as [ Hbinds | Hbinds ].
  - apply binds_single_inv in Hbinds ; crush.
  - destruct Hbinds as [ FrX Hbinds ] ; auto.
Qed.

Lemma binds_EV_bind_inv
(T' : ty EV' HV ∅) (𝓔' : eff EV' HV ∅) (Ξ : XEnv EV HV) :
binds X (T', 𝓔') (EV_bind_XEnv f Ξ) →
∃ T 𝓔,
T' = EV_bind_ty f T ∧ 𝓔' = EV_bind_eff f 𝓔 ∧ binds X (T, 𝓔) Ξ.
Proof.
intro Hbinds'.
induction Ξ as [ | Ξ Y [ T 𝓔 ] IHΞ ] using env_ind.
+ rewrite EV_bind_XEnv_empty in Hbinds'.
  apply binds_empty_inv in Hbinds' ; crush.
+ rewrite EV_bind_XEnv_concat, EV_bind_XEnv_single in Hbinds'.
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

End section_binds_EV_bind.


Section section_binds_HV_bind.
Context (EV HV HV' V : Set).
Context (f : HV → hd EV HV' V ∅).
Context (X : var).

Lemma binds_HV_bind T 𝓔 (Ξ : XEnv EV HV) :
binds X (T, 𝓔) Ξ →
binds X (HV_bind_ty f T, HV_bind_eff f 𝓔) (HV_bind_XEnv f Ξ).
Proof.
intro Hbinds.
induction Ξ as [ | Ξ' X' [ T' 𝓔' ] IHΞ' ] using env_ind.
+ apply binds_empty_inv in Hbinds ; crush.
+ apply binds_concat_inv in Hbinds.
  rewrite HV_bind_XEnv_concat, HV_bind_XEnv_single.
  destruct Hbinds as [ Hbinds | Hbinds ].
  - apply binds_single_inv in Hbinds ; crush.
  - destruct Hbinds as [ FrX Hbinds ] ; auto.
Qed.

Lemma binds_HV_bind_inv
(T' : ty EV HV' ∅) (𝓔' : eff EV HV' ∅) (Ξ : XEnv EV HV) :
binds X (T', 𝓔') (HV_bind_XEnv f Ξ) →
∃ T 𝓔,
T' = HV_bind_ty f T ∧ 𝓔' = HV_bind_eff f 𝓔 ∧ binds X (T, 𝓔) Ξ.
Proof.
intro Hbinds'.
induction Ξ as [ | Ξ Y [ T 𝓔 ] IHΞ ] using env_ind.
+ rewrite HV_bind_XEnv_empty in Hbinds'.
  apply binds_empty_inv in Hbinds' ; crush.
+ rewrite HV_bind_XEnv_concat, HV_bind_XEnv_single in Hbinds'.
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

End section_binds_HV_bind.
