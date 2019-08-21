Require Import ABS.Rel.Definitions.
Require Import ABS.Rel.Adequacy.
Require Import ABS.Rel.Compat.
Require Import ABS.Rel.Parametricity.
Require Import ABS.Lang.BindingsFacts.
Require Import ABS.Lang.Static.
Require Import ABS.Lang.StaticFacts.
Require Import ABS.Lang.Context.
Require Import FunctionalExtensionality.

Implicit Types EV HV V L : Set.

Section section_congruence.

Hint Resolve ok_wf_lbl ok_wf_ty ok_wf_eff ok_wf_tm ok_wf_hd.
Hint Resolve XLEnv_inv_wf_XEnv.
Hint Resolve EV_map_XLEnv HV_map_XLEnv LEnv_lookup_inv_binds.
Hint Constructors ok_lbl.
Hint Unfold compose.

Fixpoint
congruence_tm n EV HV V L (t₁ t₂ : tm EV HV V L)
(Π : LEnv EV HV L) (P : HV → F) (Γ : V → ty EV HV L)
(T : ty EV HV L) (𝓔 : eff EV HV L) (T0 : ty0)
C (OK_C : ok_ctx C P Γ Π T 𝓔 T0) {struct OK_C} :
n ⊨ 【 Π P Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : T # 𝓔 】 →
n ⊨ 【 LEnv_empty ∅→ ∅→ ⊢ (ctx_plug C t₁) ≼ˡᵒᵍ (ctx_plug C t₂) : T0 # [] 】
.
Proof.
intro H.
destruct OK_C as [
  |
  |
  |
  ???? C s ??????? OK_C OK_s |
  ???? C s ??????? OK_C OK_s |
  ???? C ????? OK_C |
  ???? C P Γ Π 𝔽 T T'' OK_C |
  ???? C P Γ Π S T E T'' OK_C |
  ???? C E P Γ Π T ? T'' OK_C OK_E |
  ???? C h P Γ Π 𝔽 T 𝓔 T'' OK_C OK_h |
  ???? C t 𝔽 β P Γ Π T 𝓔 T' T'' h ? OK_C OK_t |
  ???? C s P Γ Π S T E T'' OK_C OK_s |
  ???? C t P Γ Π S T E T'' OK_C OK_t |
  ???? C P Γ Π T1 E1 T2 E2 T'' OK_C
] ; simpl ctx_plug.
+ apply H ; rewrite empty_def ; try rewrite keys_def ;
    try rewrite map_nil ; simpl ; shelve.
+ eapply congruence_tm ; try exact OK_C.
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ ; simpl.
  eapply compat_tm_down ; [intro;eauto|eauto|eauto|eauto|].
  intros X FrX.
  ispecialize H (Ξ & X ~ (L_bind_ty f T, L_bind_eff f E)).
  ispecialize H (env_ext f (lid_f X)).
  ispecialize H.
  { iintro_prop ; constructor ; eauto. }
  simpl in H.
  unshelve erewrite L_bind_map_ty, L_map_ty_id in H ; [eauto|eauto| |eauto|].
  unshelve erewrite L_bind_map_eff, L_map_eff_id in H ; [eauto|eauto| |eauto|].
  repeat erewrite L_bind_bind_tm with (g := env_ext f (lid_f X)).
  match goal with
  | [ H : ?n ⊨ ⟦ _ _ ?Γ ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ |- ?n ⊨ ⟦ _ _ ?Γ' ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ ] =>
    replace Γ' with Γ ; [ exact H | ]
  end.
  { extensionality x ; unfold compose.
    unshelve erewrite L_bind_map_ty, L_map_ty_id ; eauto.
    intro ; erewrite L_map_lid_id ; eauto.
  }
  { intro α ; destruct α ; simpl ; [auto|].
    unshelve erewrite L_bind_map_lid, L_map_lid_id, L_bind_lid_id ; auto.
  }
  { intro α ; destruct α ; simpl ; [auto|].
    unshelve erewrite L_bind_map_lid, L_map_lid_id, L_bind_lid_id ; auto.
  }
  { intro ; erewrite L_map_lid_id ; auto. }
  { intro ; erewrite L_map_lid_id ; auto. }
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl ; eapply compat_tm_val.
  repeat unshelve erewrite L_bind_map_ty, L_bind_ty_id, L_map_ty_id ;
    [auto|auto|auto|auto| |auto|auto|auto|auto|auto|auto].
  eapply compat_val_up ; [reflexivity|reflexivity|reflexivity|eauto|].
  destruct (f β) as [|X] eqn:EQ_fβ ; simpl ; [auto|].
  eapply compat_hd_def ; [eauto|eauto|].
  match goal with
  | [ H : ?n ⊨ ⟦ _ _ ?Γ ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ |- ?n ⊨ ⟦ _ _ ?Γ' ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ ] =>
    replace Γ' with Γ ; [ exact H | ]
  end.
  extensionality x ; unfold compose.
  destruct x as [|[|x]] ; simpl.
  - unshelve erewrite L_bind_map_ty, L_bind_ty_id, L_map_ty_id ; eauto.
  - unshelve erewrite L_bind_map_ty, L_bind_ty_id, L_map_ty_id ; eauto.
  - auto.
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl ; eapply compat_tm_let ; [|exact H].
  apply parametricity_tm_n ; [ eauto | intro ; eauto | ].
  eapply ok_wf_tm in OK_s ; [|eauto].
  match goal with
  | [ H : wf_tm ?Ξ ?P ?Γ ?t ?T ?E |- wf_tm ?Ξ ?P ?Γ' ?t ?T ?E ] =>
    replace Γ' with Γ ; [ exact H | ]
  end.
  extensionality x ; crush.
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl ; apply compat_tm_let with (S := L_bind_ty f S).
  { match goal with
    | [ H : ?n ⊨ ⟦ _ _ ?Γ ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ |- ?n ⊨ ⟦ _ _ ?Γ' ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ ] =>
      replace Γ' with Γ ; [ exact H | ]
    end.
    extensionality x ; crush.
  }
  apply parametricity_tm_n ; [ eauto | intro ; eauto | eauto ].
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl in H|-* ; apply compat_tm_val ; apply compat_val_efun.
  match goal with
  | [ H : ?n ⊨ ⟦ _ _ ?Γ ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ |- ?n ⊨ ⟦ _ _ ?Γ' ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ ] =>
    replace Γ' with Γ ; [ exact H | ]
  end.
  extensionality x ; unfold compose.
  rewrite L_bind_EV_map_ty ; auto.
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl in H|-* ; apply compat_tm_val ; apply compat_val_hfun.
  match goal with
  | [ H : ?n ⊨ ⟦ _ _ ?Γ ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ |- ?n ⊨ ⟦ _ _ ?Γ' ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ ] =>
    replace Γ' with Γ ; [ exact H | ]
  end.
  extensionality x ; unfold compose.
  rewrite L_bind_HV_map_ty ; auto.
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl in H|-* ; apply compat_tm_val ; apply compat_val_fun.
  match goal with
  | [ H : ?n ⊨ ⟦ _ _ ?Γ ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ |- ?n ⊨ ⟦ _ _ ?Γ' ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ ] =>
    replace Γ' with Γ ; [ exact H | ]
  end.
  extensionality x ; auto.
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl in H|-*.
  erewrite <- EV_L_bind_ty ; [ eapply compat_tm_eapp ; eauto | auto ].
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl in H|-*.
  erewrite <- HV_L_bind_ty with (g₂ := HV_substfun _) ; [|auto].
  eapply compat_tm_happ ; [reflexivity|reflexivity| |exact H|].
  - rewrite lbl_L_bind_hd.
    eapply ok_wf_lbl ; [ eauto | ].
    inversion OK_h ; crush.
  - eapply parametricity_hd_n ; [eauto|intro ; eauto|eauto].
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  destruct (f β) as [|X] eqn:EQ_fβ ; simpl ; [auto|].
  erewrite <- HV_L_bind_ty with (g₂ := HV_substfun _) ; [|auto].
  rewrite EQ_fβ.
  erewrite HV_bind_ty_eq
    with (g := HV_substfun (hd_def 𝔽 (lid_f X) (L_bind_tm f t₁))) ;
  [ | destruct p ; simpl ; [ rewrite lbl_L_bind_hd | ] ; crush ].
  match goal with
  | [ H : LEnv_lookup β _ = _ |- _ ] =>
    eapply LEnv_lookup_inv_binds in H as Binds ; eauto
  end.
  eapply compat_tm_happ ; [reflexivity|reflexivity| | |].
  - constructor.
    eauto using get_some_inv.
  - eapply parametricity_tm_n ; [eauto|intro ; eauto|].
    eapply ok_wf_tm in OK_t ; eauto.
  - eapply compat_hd_def ; [eauto|eauto|].
    match goal with
    | [ H : ?n ⊨ ⟦ _ _ ?Γ ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ |- ?n ⊨ ⟦ _ _ ?Γ' ⊢ _ ≼ˡᵒᵍ _ : _ # _ ⟧ ] =>
      replace Γ' with Γ ; [ exact H | ]
    end.
    extensionality x ; unfold compose.
    destruct x as [|[|x]] ; simpl ; [| |auto].
    * unshelve erewrite L_bind_map_ty, L_bind_ty_id, L_map_ty_id ; eauto.
    * unshelve erewrite L_bind_map_ty, L_bind_ty_id, L_map_ty_id ; eauto.
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl in H|-* ; eapply compat_tm_app ; [exact H|].
  eapply parametricity_tm_n ; [eauto|intro ; eauto|eauto].
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  simpl in H|-* ; eapply compat_tm_app ; [|exact H].
  eapply parametricity_tm_n ; [eauto|intro ; eauto|].
  eapply ok_wf_tm in OK_t ; eauto.
+ eapply congruence_tm ; [exact OK_C|].
  iintro Ξ ; iintro f ; iintro HΞΠ ; ielim_prop HΞΠ.
  iespecialize H ; ispecialize H ; [eauto|].
  eapply compat_sub with (𝓔 := L_bind_eff f E1) ; eauto using subty_st, L_bind_se.
Qed.

End section_congruence.

Section section_soundness.

Hint Rewrite dom_empty union_empty_l Xs_ctx_plug.

Theorem soundness EV HV V L (t₁ t₂ : tm EV HV V L) (Closed_t₁ : Xs_tm t₁ = \{})
(Π : LEnv EV HV L) (P : HV → F) (Γ : V → ty EV HV L)
(T : ty EV HV L) (𝓔 : eff EV HV L) :
⊨ 【 Π P Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : T # 𝓔 】 →
ctx_equiv t₁ t₂ Π P Γ T 𝓔.
Proof.
intro Ht.
intros C T0 OK_C Closed_C.
eapply adequacy ; [ | crush ].
intro n.
eapply congruence_tm with (n := n) in Ht as HCt ; [|exact OK_C].
iespecialize HCt.
ispecialize HCt ; [ iintro_prop ; constructor | ].
erewrite L_bind_tm_id, L_bind_tm_id, L_bind_ty_id, L_bind_eff_id in HCt ;
  [|auto|auto|auto|auto].
replace (L_bind_ty ∅→ ∘ ∅→) with (∅→ : ∅ → ty0) in HCt ; [|extensionality x ; auto].
exact HCt.
Qed.

End section_soundness.
