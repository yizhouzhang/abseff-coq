Require Import Rel.BasicFacts.
Require Import Rel.Compat.
Require Import Rel.Adequacy.
Require Import Lang.Static.
Require Import Lang.StaticFacts.
Require Import Lang.BindingsFacts.

Implicit Type EV HV V L : Set.

Section section_parametricity_n.

Local Fact wf_ext_Γ
EV HV V (Ξ : XEnv EV HV) (Γ : V → ty EV HV ∅) S :
wf_Γ Ξ Γ → wf_ty Ξ S → wf_Γ Ξ (env_ext Γ S).
Proof.
intros_all ; crush.
Qed.

Hint Resolve wf_ext_Γ wf_XEnv_cons weaken_wf_Γ weaken_wf_ty.
Hint Resolve EV_map_wf_XEnv EV_map_wf_ty EV_map_wf_Γ.
Hint Resolve HV_map_wf_XEnv HV_map_wf_ty HV_map_wf_Γ.
Hint Rewrite concat_empty_l EV_map_XEnv_empty HV_map_XEnv_empty.

Fixpoint
  parametricity_tm_n
  EV HV V (Ξ : XEnv EV HV) (P : HV → F) (Γ : V → ty EV HV ∅)
  (WF_Ξ : wf_XEnv Ξ) (WF_Γ : wf_Γ Ξ Γ)
  t T 𝓔 (WF_t : wf_tm Ξ P Γ t T 𝓔) n {struct WF_t} :
  n ⊨ ⟦ Ξ P Γ ⊢ t ≼ˡᵒᵍ t : T # 𝓔 ⟧
with
  parametricity_val_n
  EV HV V (Ξ : XEnv EV HV) (P : HV → F) (Γ : V → ty EV HV ∅)
  (WF_Ξ : wf_XEnv Ξ) (WF_Γ : wf_Γ Ξ Γ)
  v T (WF_v : wf_val Ξ P Γ v T) n {struct WF_v} :
  n ⊨ ⟦ Ξ P Γ ⊢ v ≼ˡᵒᵍᵥ v : T ⟧
with
  parametricity_hd_n
  EV HV V (Ξ : XEnv EV HV) (P : HV → F) (Γ : V → ty EV HV ∅)
  (WF_Ξ : wf_XEnv Ξ) (WF_Γ : wf_Γ Ξ Γ)
  h 𝔽 (WF_h : wf_hd Ξ P Γ h 𝔽) n {struct WF_h} :
  n ⊨ ⟦ Ξ P Γ ⊢ h ≼ˡᵒᵍₕ h : 𝔽 # lbl_hd h ⟧.
Proof.
+ destruct WF_t ; simpl.
  - apply compat_tm_val.
    eapply parametricity_val_n ; eauto.
  - eapply compat_tm_app.
    * eapply parametricity_tm_n ; eauto.
    * eapply parametricity_tm_n ; eauto.
  - eapply compat_tm_let.
    * eapply parametricity_tm_n ; eauto.
    * eapply parametricity_tm_n ; eauto.
  - eapply compat_tm_eapp.
    eapply parametricity_tm_n ; eauto.
  - eapply compat_tm_happ ; try reflexivity ; try eassumption.
    * clear - H.
      destruct h as [ | ? [ | X ] ? ] ; simpl ; [constructor|auto|].
      constructor.
      inversion H.
      eauto using get_some_inv.
    * eapply parametricity_tm_n ; eauto.
    * eapply parametricity_hd_n ; eauto.
  - eapply compat_tm_down with (B := B \u dom Ξ) ; try assumption.
    intros ; eapply parametricity_tm_n ; eauto.
  - eapply compat_sub ; try eassumption.
    eapply parametricity_tm_n ; eauto.
+ destruct WF_v ; simpl.
  - apply compat_val_unit.
  - apply compat_val_var.
  - apply compat_val_fun.
    eapply parametricity_tm_n ; eauto.
  - apply compat_val_efun.
    eapply parametricity_tm_n ; eauto.
  - apply compat_val_hfun.
    eapply parametricity_tm_n ; eauto.
  - eapply compat_val_up ; try reflexivity ; try assumption.
    eapply parametricity_hd_n ; eauto.
+ destruct WF_h ; simpl.
  - eapply compat_hd_var.
  - eapply compat_hd_def ; try eassumption.
    eapply parametricity_tm_n ; eauto.
    repeat apply wf_ext_Γ ; try assumption.
    { replace Ξ with (HV_open_XEnv (EV_open_XEnv empty) & Ξ) by crush.
      crush.
    }
    { constructor.
      - replace Ξ with (HV_open_XEnv (EV_open_XEnv empty) & Ξ) by crush.
        crush.
      - eapply binds_wf ; eauto.
      - eapply binds_wf ; eauto.
    }
Qed.

End section_parametricity_n.


Section section_parametricity.

Context (EV HV V : Set).
Context (Ξ : XEnv EV HV).
Context (P : HV → F).
Context (Γ : V → ty EV HV ∅).
Context (WF_Ξ : wf_XEnv Ξ).
Context (WF_Γ : wf_Γ Ξ Γ).

Hint Resolve parametricity_tm_n parametricity_val_n parametricity_hd_n.

Theorem parametricity_tm
t T 𝓔 (WF_t : wf_tm Ξ P Γ t T 𝓔) :
⊨ ⟦ Ξ P Γ ⊢ t ≼ˡᵒᵍ t : T # 𝓔 ⟧.
Proof.
intro ; auto.
Qed.

Theorem parametricity_val
v T (WF_v : wf_val Ξ P Γ v T) :
⊨ ⟦ Ξ P Γ ⊢ v ≼ˡᵒᵍᵥ v : T ⟧.
Proof.
intro ; auto.
Qed.

Theorem parametricity_hd
h 𝔽 (WF_h : wf_hd Ξ P Γ h 𝔽) :
⊨ ⟦ Ξ P Γ ⊢ h ≼ˡᵒᵍₕ h : 𝔽 # lbl_hd h ⟧.
Proof.
intro ; auto.
Qed.

End section_parametricity.
