Require Import Lang.Syntax.
Require Import Lang.Bindings.
Require Import Lang.Static.
Require Import Lang.BindingsFacts.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Section section_weaken_wf.

Hint Rewrite dom_concat in_union.

Lemma weaken_wf_lbl
EV HV (Ξ Ξ' : XEnv EV HV) l :
wf_lbl Ξ l → wf_lbl (Ξ & Ξ') l.
Proof.
destruct 1 ; constructor ; crush.
Qed.

Hint Resolve weaken_wf_lbl.

Lemma weaken_wf_ef
EV HV (Ξ Ξ' : XEnv EV HV) e :
wf_ef Ξ e → wf_ef (Ξ & Ξ') e.
Proof.
destruct 1 ; constructor ; crush.
Qed.

Hint Resolve weaken_wf_ef.

Lemma weaken_wf_eff
EV HV (Ξ Ξ' : XEnv EV HV) E :
wf_eff Ξ E → wf_eff (Ξ & Ξ') E.
Proof.
induction 1 ; constructor ; crush.
Qed.

Hint Resolve weaken_wf_eff.
Hint Rewrite EV_map_XEnv_concat HV_map_XEnv_concat.

Lemma weaken_wf_ty
EV HV (Ξ Ξ' : XEnv EV HV) T :
wf_ty Ξ T → wf_ty (Ξ & Ξ') T.
Proof.
induction 1 ; constructor ; crush.
Qed.

Hint Resolve weaken_wf_ty.

Corollary weaken_wf_Γ
EV HV V (Ξ Ξ' : XEnv EV HV) (Γ : V → ty EV HV ∅) :
wf_Γ Ξ Γ → wf_Γ (Ξ & Ξ') Γ.
Proof.
intros_all ; crush.
Qed.

End section_weaken_wf.


Section section_EV_map_wf.

Hint Rewrite EV_map_XEnv_dom.

Lemma EV_map_wf_lbl EV EV' HV
(f : EV → EV') (Ξ : XEnv EV HV)
(ℓ : lbl HV ∅) :
wf_lbl Ξ ℓ → wf_lbl (EV_map_XEnv f Ξ) ℓ.
Proof.
destruct 1 ; constructor ; crush.
Qed.

Hint Resolve EV_map_wf_lbl.

Lemma EV_map_wf_ef EV EV' HV
(f : EV → EV') (Ξ : XEnv EV HV)
(ε : ef EV HV ∅) :
wf_ef Ξ ε → wf_ef (EV_map_XEnv f Ξ) (EV_map_ef f ε).
Proof.
destruct 1 ; constructor ; crush.
Qed.

Hint Resolve EV_map_wf_ef.

Lemma EV_map_wf_eff EV EV' HV
(f : EV → EV') (Ξ : XEnv EV HV)
(𝓔 : eff EV HV ∅) :
wf_eff Ξ 𝓔 → wf_eff (EV_map_XEnv f Ξ) (EV_map_eff f 𝓔).
Proof.
induction 1 ; constructor ; crush.
Qed.

Hint Resolve EV_map_wf_eff.

Fixpoint EV_map_wf_ty EV EV' HV
(f : EV → EV') (Ξ : XEnv EV HV)
(T : ty EV HV ∅)
(Q : wf_ty Ξ T) :
wf_ty (EV_map_XEnv f Ξ) (EV_map_ty f T).
Proof.
destruct Q ; simpl.
- constructor.
- constructor ; crush.
- constructor.
  eapply EV_map_wf_ty in Q.
  erewrite EV_map_map_XEnv in Q|-* ; [eauto|crush|crush].
- constructor.
  eapply EV_map_wf_ty in Q.
  erewrite <- EV_HV_map_XEnv ; eauto.
Qed.

Hint Resolve EV_map_wf_ty.
Hint Rewrite EV_map_XEnv_empty EV_map_XEnv_concat EV_map_XEnv_single.

Lemma EV_map_wf_XEnv EV EV' HV
(f : EV → EV') (Ξ : XEnv EV HV) :
wf_XEnv Ξ → wf_XEnv (EV_map_XEnv f Ξ).
Proof.
induction 1 ; crush ; constructor ; crush.
Qed.

Lemma EV_map_wf_Γ EV EV' HV V
(f : EV → EV') (Ξ : XEnv EV HV) (Γ : V → ty EV HV ∅) :
wf_Γ Ξ Γ → wf_Γ (EV_shift_XEnv Ξ) (EV_shift_ty ∘ Γ).
Proof.
intros_all; auto.
Qed.

End section_EV_map_wf.


Section section_HV_map_wf.

Hint Rewrite HV_map_XEnv_dom.

Lemma HV_map_wf_lbl EV HV HV'
(f : HV → HV') (Ξ : XEnv EV HV)
(ℓ : lbl HV ∅)
(Wf_ℓ : wf_lbl Ξ ℓ) :
wf_lbl (HV_map_XEnv f Ξ) (HV_map_lbl f ℓ).
Proof.
destruct Wf_ℓ ; constructor ; crush.
Qed.

Hint Resolve HV_map_wf_lbl.

Lemma HV_map_wf_ef EV HV HV'
(f : HV → HV') (Ξ : XEnv EV HV)
(ε : ef EV HV ∅)
(Wf_ε : wf_ef Ξ ε) :
wf_ef (HV_map_XEnv f Ξ) (HV_map_ef f ε).
Proof.
destruct Wf_ε ; constructor ; crush.
Qed.

Hint Resolve HV_map_wf_ef.

Fixpoint HV_map_wf_eff EV HV HV'
(f : HV → HV') (Ξ : XEnv EV HV)
(𝓔 : eff EV HV ∅)
(Wf_𝓔 : wf_eff Ξ 𝓔) :
wf_eff (HV_map_XEnv f Ξ) (HV_map_eff f 𝓔).
Proof.
destruct Wf_𝓔 ; simpl ; constructor ; crush.
Qed.

Hint Resolve HV_map_wf_eff.

Fixpoint HV_map_wf_ty EV HV HV'
(f : HV → HV') (Ξ : XEnv EV HV)
(T : ty EV HV ∅)
(Q : wf_ty Ξ T) :
wf_ty (HV_map_XEnv f Ξ) (HV_map_ty f T)
.
Proof.
destruct Q ; simpl.
+ constructor.
+ constructor ; crush.
+ constructor.
  eapply HV_map_wf_ty in Q.
  erewrite EV_HV_map_XEnv ; eauto.
+ constructor.
  eapply HV_map_wf_ty in Q.
  erewrite HV_map_map_XEnv in Q|-* ; [eauto|crush|crush].
Qed.

Hint Resolve HV_map_wf_ty.
Hint Rewrite HV_map_XEnv_empty HV_map_XEnv_concat HV_map_XEnv_single.

Lemma HV_map_wf_XEnv EV HV HV'
(f : HV → HV') (Ξ : XEnv EV HV) :
wf_XEnv Ξ → wf_XEnv (HV_map_XEnv f Ξ).
Proof.
induction 1 ; crush ; constructor ; crush.
Qed.

Lemma HV_map_wf_Γ EV HV HV' V
(f : HV → HV') (Ξ : XEnv EV HV) (Γ : V → ty EV HV ∅) :
wf_Γ Ξ Γ → wf_Γ (HV_shift_XEnv Ξ) (HV_shift_ty ∘ Γ).
Proof.
intros_all; auto.
Qed.

End section_HV_map_wf.


Lemma binds_wf EV HV (Ξ : XEnv EV HV) X T 𝓔 :
wf_XEnv Ξ → binds X (T, 𝓔) Ξ → wf_ty Ξ T ∧ wf_eff Ξ 𝓔.
Proof.
induction 1 as [ | ? ? ? ? ? IH ] ; simpl.
+ intro BindsX ; apply binds_empty_inv in BindsX ; contradict BindsX.
+ intro BindsX.
  apply binds_concat_inv in BindsX.
  destruct BindsX as [BindsX | BindsX].
  - apply binds_single_inv in BindsX.
    destruct BindsX as [ HX HT𝓔 ].
    apply eq_sym in HX ; apply eq_sym in HT𝓔.
    inversion HT𝓔 ; clear HT𝓔 ; subst.
    split ; [ apply weaken_wf_ty | apply weaken_wf_eff ] ; assumption.
  - destruct BindsX as [HX BindsX].
    specialize (IH BindsX).
    destruct IH.
    split ; [ apply weaken_wf_ty | apply weaken_wf_eff ] ; assumption.
Qed.
