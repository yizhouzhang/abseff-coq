Require Import Lang.Syntax.
Require Import Lang.Bindings.
Require Import Lang.Static.
Require Import Lang.BindingsFacts.
Require Import Lang.StaticFacts_1.
Require Import Lang.StaticFacts_2.
Require Import FunctionalExtensionality.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Section section_XLEnv_inv.

Hint Rewrite dom_concat dom_single in_union in_singleton.

Fixpoint XLEnv_inv_substituion_ok
EV HV L Ξ (Π : LEnv EV HV L) f
(H : XLEnv Ξ Π f) {struct H} :
∀ β, ∃ X, f β = lid_f X ∧ X ∈ dom Ξ.
Proof.
destruct H as [ | ? ? ? ? ? ? ? H ] ; intro β.
+ destruct β.
+ destruct β as [ | β ] ; simpl.
  - eexists ; crush.
  - destruct (f β) as [ | Y ] eqn:H' ; [ auto | ].
    exists ; split ; [ reflexivity | ].
    apply XLEnv_inv_substituion_ok with (β := β) in H ; destruct H as [?[??]].
    rewrite H' in H.
    crush.
Qed.

Fixpoint XLEnv_inv_wf_XEnv
EV HV L Ξ (Π : LEnv EV HV L) f
(H : XLEnv Ξ Π f) {struct H} :
wf_XEnv Ξ.
Proof.
destruct H as [ | ? ? ? ? ? ? ? H ] ; simpl.
+ constructor.
+ constructor ; eauto.
Qed.

End section_XLEnv_inv.


Section section_ok_wf.

Fixpoint LEnv_lookup_inv_binds
EV HV L Ξ (Π : LEnv EV HV L) f X β T E
(Lookup : LEnv_lookup β Π = (T, E))
(EQ_β : f β = lid_f X)
(H : XLEnv Ξ Π f) {struct H} :
binds X (L_bind_ty f T, L_bind_eff f E) Ξ.
Proof.
destruct H as [ | ??????? H] ; simpl ; [auto|].
destruct β as [|β] ; simpl in *.
+ inversion EQ_β ; inversion Lookup ; subst.
  unshelve erewrite L_bind_map_ty, L_bind_map_eff, L_map_ty_id, L_map_eff_id ; auto.
  - intro ; erewrite L_map_lid_id ; auto.
  - intro ; erewrite L_map_lid_id ; auto.
+ destruct (LEnv_lookup β Π) eqn:Lookup'.
  inversion Lookup ; subst.
  eapply LEnv_lookup_inv_binds in H ; try eassumption.
  apply get_some_inv in H as H'.
  apply binds_concat_left.
  - unshelve erewrite L_bind_map_ty, L_bind_map_eff, L_map_ty_id, L_map_eff_id ; eauto.
    * intro ; erewrite L_map_lid_id ; auto.
    * intro ; erewrite L_map_lid_id ; auto.
  - rewrite dom_single, notin_singleton.
    intro ; subst ; auto.
Qed.

Fixpoint HV_map_XLEnv
EV HV L HV' (f : HV → HV')
Ξ (Π : LEnv EV HV L) g
(H : XLEnv Ξ Π g) :
XLEnv (HV_map_XEnv f Ξ) (HV_map_LEnv f Π) g.
Proof.
destruct H as [ | ? ? ? ? ? ? ? H ] ; simpl.
+ rewrite HV_map_XEnv_empty ; constructor.
+ rewrite HV_map_XEnv_concat, HV_map_XEnv_single.
  rewrite <- L_bind_HV_map_ty, <- L_bind_HV_map_eff.
  constructor.
  - auto.
  - rewrite HV_map_XEnv_dom ; auto.
  - rewrite L_bind_HV_map_ty.
    apply HV_map_wf_ty ; auto.
  - rewrite L_bind_HV_map_eff.
    apply HV_map_wf_eff ; auto.
Qed.

Fixpoint EV_map_XLEnv
EV HV L EV' (f : EV → EV')
Ξ (Π : LEnv EV HV L) g
(H : XLEnv Ξ Π g) :
XLEnv (EV_map_XEnv f Ξ) (EV_map_LEnv f Π) g.
Proof.
destruct H as [ | ? ? ? ? ? ? ? H ] ; simpl.
+ rewrite EV_map_XEnv_empty ; constructor.
+ rewrite EV_map_XEnv_concat, EV_map_XEnv_single.
  rewrite <- L_bind_EV_map_ty, <- L_bind_EV_map_eff.
  constructor.
  - auto.
  - rewrite EV_map_XEnv_dom ; auto.
  - rewrite L_bind_EV_map_ty.
    apply EV_map_wf_ty ; auto.
  - rewrite L_bind_EV_map_eff.
    apply EV_map_wf_eff ; auto.
Qed.

Lemma L_bind_In
EV HV L L' (f : L → lid L') :
∀ e (E : eff EV HV L) (H : In e E),
In (L_bind_ef f e) (L_bind_eff f E).
Proof.
induction E ; crush.
Qed.

Hint Resolve L_bind_In.

Lemma L_bind_se
EV HV L L' (f : L → lid L') :
∀ (E1 E2 : eff EV HV L) (H : se E1 E2),
se (L_bind_eff f E1) (L_bind_eff f E2).
Proof.
induction E1 ; crush.
Qed.

Hint Resolve L_bind_se.

Fixpoint
subty_st
EV HV L (f : L → lid0)
(T1 T2 : ty EV HV L)
(H : subty T1 T2) :
st (L_bind_ty f T1) (L_bind_ty f T2)
.
Proof.
+ destruct H ; simpl.
  - constructor.
  - constructor ; eauto.
  - constructor ; eauto.
  - constructor ; eauto.
  - econstructor ; eauto.
Qed.

Hint Resolve subty_st.

Hint Constructors wf_lbl wf_ef wf_eff wf_ty.
Hint Constructors wf_hd wf_val wf_tm.

Lemma ok_wf_lbl
EV HV L (Π : LEnv EV HV L)
Ξ f (Q : XLEnv Ξ Π f)
(ℓ : lbl HV L) (H : ok_lbl Π ℓ) :
wf_lbl Ξ (L_bind_lbl f ℓ).
Proof.
destruct H ; simpl.
+ eapply XLEnv_inv_substituion_ok in Q ; crush.
+ crush.
Qed.

Hint Resolve ok_wf_lbl.

Lemma ok_wf_ef
EV HV L (Π : LEnv EV HV L)
Ξ f (Q : XLEnv Ξ Π f)
(ε : ef EV HV L) (H : ok_ef Π ε) :
wf_ef Ξ (L_bind_ef f ε).
Proof.
destruct H ; simpl ; eauto.
Qed.

Hint Resolve ok_wf_ef.

Lemma ok_wf_eff
EV HV L (Π : LEnv EV HV L)
Ξ f (Q : XLEnv Ξ Π f)
(𝓔 : eff EV HV L) (H : ok_eff Π 𝓔) :
wf_eff Ξ (L_bind_eff f 𝓔).
Proof.
induction H ; simpl ; eauto.
Qed.

Hint Resolve ok_wf_eff.
Hint Resolve EV_map_XLEnv HV_map_XLEnv.

Fixpoint
ok_wf_ty
EV HV L (Π : LEnv EV HV L)
Ξ f (Q : XLEnv Ξ Π f)
(T : ty EV HV L) (H : ok_ty Π T) :
wf_ty Ξ (L_bind_ty f T)
.
Proof.
destruct H ; simpl ; eauto.
Qed.

Hint Resolve ok_wf_ty.

Fixpoint
ok_wf_hd
EV HV V L (Π : LEnv EV HV L) (P : HV → F) (Γ : V → ty EV HV L)
Ξ f (Q : XLEnv Ξ Π f)
(h : hd EV HV V L) 𝔽 (H : ok_hd Π P Γ h 𝔽) :
wf_hd Ξ P ((L_bind_ty f) ∘ Γ) (L_bind_hd f h) 𝔽
with
ok_wf_val
EV HV V L (Π : LEnv EV HV L) (P : HV → F) (Γ : V → ty EV HV L)
Ξ f (Q : XLEnv Ξ Π f)
(v : val EV HV V L) T (H : ok_val Π P Γ v T) :
wf_val Ξ P ((L_bind_ty f) ∘ Γ) (L_bind_val f v) (L_bind_ty f T)
with
ok_wf_tm
EV HV V L (Π : LEnv EV HV L) (P : HV → F) (Γ : V → ty EV HV L)
Ξ f (Q : XLEnv Ξ Π f)
(t : tm EV HV V L) T E (H : ok_tm Π P Γ t T E) :
wf_tm Ξ P ((L_bind_ty f) ∘ Γ) (L_bind_tm f t) (L_bind_ty f T) (L_bind_eff f E)
.
Proof.
+ destruct H as [ | ?????? H' ] ; simpl.
  - constructor.
  - eapply ok_wf_tm in H' ; [|eauto].
    destruct (f β) as [|X] eqn:EQ_fβ ; simpl ; [auto|].
    econstructor ; [ eapply LEnv_lookup_inv_binds ; eauto |].
    match goal with
    | [ H : wf_tm ?Ξ ?P ?Γ ?t ?T ?E |- wf_tm ?Ξ ?P ?Γ' ?t ?T ?E ] =>
      replace Γ' with Γ ; [ exact H | ]
    end.
    extensionality x ; unfold compose.
    destruct x as [|[|x]] ; simpl.
    * unshelve erewrite L_bind_map_ty, L_bind_ty_id, L_map_ty_id ; eauto.
    * unshelve erewrite L_bind_map_ty, L_bind_ty_id, L_map_ty_id ; eauto.
    * auto.
+ destruct H as [ | | ? ? ? ? H' | ? ? H' | ? ? ? H' | ? ? H' ] ; simpl.
  - constructor.
  - constructor.
  - eapply ok_wf_tm in H' ; [|eauto].
    constructor ; [|eauto].
    match goal with
    | [ H : wf_tm ?Ξ ?P ?Γ ?t ?T ?E |- wf_tm ?Ξ ?P ?Γ' ?t ?T ?E ] =>
      replace Γ' with Γ ; [ exact H | ]
    end.
    extensionality x ; crush.
  - eapply ok_wf_tm in H' ; [|eauto].
    constructor.
    match goal with
    | [ H : wf_tm ?Ξ ?P ?Γ ?t ?T ?E |- wf_tm ?Ξ ?P ?Γ' ?t ?T ?E ] =>
      replace Γ' with Γ ; [ exact H | ]
    end.
    extensionality x ; unfold compose.
    rewrite L_bind_EV_map_ty ; auto.
  - eapply ok_wf_tm in H' ; [|eauto].
    constructor.
    match goal with
    | [ H : wf_tm ?Ξ ?P ?Γ ?t ?T ?E |- wf_tm ?Ξ ?P ?Γ' ?t ?T ?E ] =>
      replace Γ' with Γ ; [ exact H | ]
    end.
    extensionality x ; unfold compose.
    rewrite L_bind_HV_map_ty ; auto.
  - eapply ok_wf_hd in H' ; [|eauto].
    unshelve erewrite L_bind_map_ty, L_bind_ty_id, L_map_ty_id ; eauto.
    unshelve erewrite L_bind_map_ty, L_bind_ty_id, L_map_ty_id ; eauto.
    rewrite <- lbl_L_bind_hd.
    constructor ; auto.
+ destruct H as [ ?? H' | ????? H' H'' |  ?????? H' H'' |  ???? H' | ????? H' H'' |
  ? T E ??? H' | ????? H' ] ; simpl.
  - eapply ok_wf_val in H' ; [|eauto].
    constructor ; auto.
  - eapply ok_wf_tm in H' ; [|eauto].
    eapply ok_wf_tm in H'' ; [|eauto].
    econstructor ; eauto.
  - eapply ok_wf_tm in H' ; [|eauto].
    eapply ok_wf_tm in H'' ; [|eauto].
    eapply wf_tm_let.
    * eapply ok_wf_ty ; eauto.
    * auto.
    * match goal with
      | [ H : wf_tm ?Ξ ?P ?Γ ?t ?T ?E |- wf_tm ?Ξ ?P ?Γ' ?t ?T ?E ] =>
        replace Γ' with Γ ; [ exact H | ]
      end.
      extensionality x ; auto.
  - eapply ok_wf_tm in H' ; [|eauto].
    erewrite <- EV_L_bind_ty with (g₂ := EV_substfun _) ; [|crush].
    econstructor ; eauto.
  - eapply ok_wf_tm in H' ; [|eauto].
    eapply ok_wf_hd in H'' ; [|eauto].
    erewrite <- HV_L_bind_ty with (g₂ := HV_substfun _) ; [|crush].
    econstructor ; eauto.
  - econstructor ; [ eauto | eauto | ].
    intros X FrX.
    eapply ok_wf_tm
      with (Ξ := Ξ & X ~ (L_bind_ty f T, L_bind_eff f E)) (f := env_ext f (lid_f X))
      in H' ; [ | constructor ; eauto ].
    simpl L_bind_eff in H'.
    unshelve erewrite L_bind_map_ty, L_map_ty_id in H' ; eauto.
    unshelve erewrite L_bind_map_eff, L_map_eff_id in H' ; eauto.
    erewrite L_bind_bind_tm with (g := env_ext f (lid_f X)).
    match goal with
    | [ H : wf_tm ?Ξ ?P ?Γ ?t ?T ?E |- wf_tm ?Ξ ?P ?Γ' ?t ?T ?E ] =>
      replace Γ' with Γ ; [ exact H | ]
    end.
    { extensionality x ; unfold compose.
      unshelve erewrite L_bind_map_ty, L_map_ty_id ; eauto.
      intro ; erewrite L_map_lid_id ; eauto.
    }
    { intro α ; destruct α ; simpl ; [auto|].
      unshelve erewrite L_bind_map_lid, L_map_lid_id, L_bind_lid_id ; auto.
    }
    { intro ; erewrite L_map_lid_id ; auto. }
    { intro ; erewrite L_map_lid_id ; auto. }
  - econstructor ; eauto.
Qed.

End section_ok_wf.
