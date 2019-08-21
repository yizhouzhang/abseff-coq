Require Import ABS.Lang.Syntax.
Require Import TLC.LibList.
Local Open Scope list_scope.
Set Implicit Arguments.

Section section_sim.

Context (Xs₁ Xs₂ : list var).

Definition var_sim X₁ X₂ : Prop :=
∃ n, Nth n Xs₁ X₁ ∧ Nth n Xs₂ X₂.

Inductive lid_sim L : lid L → lid L → Prop :=
| lid_f_sim : ∀ X₁ X₂, var_sim X₁ X₂ → lid_sim (lid_f X₁) (lid_f X₂)
| lid_b_sim : ∀ I, lid_sim (lid_b I) (lid_b I)
.

Inductive lbl_sim HV L : lbl HV L → lbl HV L → Prop :=
| lbl_var_sim : ∀ β, lbl_sim (lbl_var β) (lbl_var β)
| lbl_id_sim : ∀ ι₁ ι₂, lid_sim ι₁ ι₂ → lbl_sim (lbl_id ι₁) (lbl_id ι₂)
.

Inductive ef_sim EV HV L : ef EV HV L → ef EV HV L → Prop :=
| ef_var_sim : ∀ α, ef_sim (ef_var α) (ef_var α)
| ef_lbl_sim : ∀ ℓ₁ ℓ₂, lbl_sim ℓ₁ ℓ₂ → ef_sim (ef_lbl ℓ₁) (ef_lbl ℓ₂)
.

Inductive eff_sim EV HV L : eff EV HV L → eff EV HV L → Prop :=
| eff_nil_sim : eff_sim [] []
| eff_cons_sim :
  ∀ ε₁ 𝓔₁ ε₂ 𝓔₂, ef_sim ε₁ ε₂ → eff_sim 𝓔₁ 𝓔₂ →
  eff_sim (ε₁ :: 𝓔₁) (ε₂ :: 𝓔₂)
.

Inductive
ty_sim EV HV L : ty EV HV L → ty EV HV L → Prop :=
| ty_unit_sim : ty_sim 𝟙 𝟙
| ty_fun :
  ∀ S₁ T₁ E₁ S₂ T₂ E₂, ty_sim S₁ S₂ → ty_sim T₁ T₂ → eff_sim E₁ E₂ →
  ty_sim (ty_fun S₁ T₁ E₁) (ty_fun S₂ T₂ E₂)
| ty_efun : ∀ T₁ T₂, @ty_sim _ _ _ T₁ T₂ → ty_sim (ty_efun T₁) (ty_efun T₂)
| ty_hfun : ∀ 𝔽 T₁ T₂, @ty_sim _ _ _ T₁ T₂ → ty_sim (ty_hfun 𝔽 T₁) (ty_hfun 𝔽 T₂)
.

Inductive
hd_sim EV HV V L : hd EV HV V L → hd EV HV V L → Prop :=
| hd_var : ∀ p, hd_sim (hd_var p) (hd_var p)
| hd_def_sim :
  ∀ 𝔽 ι₁ ι₂ t₁ t₂, lid_sim ι₁ ι₂ → @tm_sim _ _ _ _ t₁ t₂ →
  hd_sim (hd_def 𝔽 ι₁ t₁) (hd_def 𝔽 ι₂ t₂)
with
val_sim EV HV V L : val EV HV V L → val EV HV V L → Prop :=
| val_unit_sim : val_sim val_unit val_unit
| val_var_sim : ∀ x, val_sim (val_var x) (val_var x)
| val_fun_sim : ∀ t₁ t₂, @tm_sim _ _ _ _ t₁ t₂ → val_sim (val_fun t₁) (val_fun t₂)
| val_efun_sim : ∀ t₁ t₂, @tm_sim _ _ _ _ t₁ t₂ → val_sim (val_efun t₁) (val_efun t₂)
| val_hfun_sim : ∀ t₁ t₂, @tm_sim _ _ _ _ t₁ t₂ → val_sim (val_hfun t₁) (val_hfun t₂)
| val_up_sim : ∀ h₁ h₂, @hd_sim _ _ _ _ h₁ h₂ → val_sim (val_up h₁) (val_up h₂)
with
tm_sim EV HV V L : tm EV HV V L → tm EV HV V L → Prop :=
| tm_val_sim : ∀ v₁ v₂, val_sim v₁ v₂ → tm_sim (tm_val v₁) (tm_val v₂)
| tm_Down_sim :
  ∀ t₁ t₂, @tm_sim _ _ _ _ t₁ t₂ → tm_sim (⬇ t₁) (⬇ t₂)
| tm_down_sim :
  ∀ X₁ t₁ X₂ t₂, var_sim X₁ X₂ → tm_sim t₁ t₂ → tm_sim (⇩ X₁ t₁) (⇩ X₂ t₂)
| tm_let_sim :
  ∀ t₁ s₁ t₂ s₂,
  tm_sim t₁ t₂ → @tm_sim _ _ _ _ s₁ s₂ →
  tm_sim (tm_let t₁ s₁) (tm_let t₂ s₂)
| tm_eapp_sim :
  ∀ t₁ 𝓔₁ t₂ 𝓔₂,
  tm_sim t₁ t₂ → eff_sim 𝓔₁ 𝓔₂ →
  tm_sim (tm_eapp t₁ 𝓔₁) (tm_eapp t₂ 𝓔₂)
| tm_happ_sim :
  ∀ t₁ h₁ t₂ h₂,
  tm_sim t₁ t₂ → hd_sim h₁ h₂ →
  tm_sim (tm_happ t₁ h₁) (tm_happ t₂ h₂)
| tm_app_sim :
  ∀ t₁ s₁ t₂ s₂,
  tm_sim t₁ t₂ → tm_sim s₁ s₂ →
  tm_sim (tm_app t₁ s₁) (tm_app t₂ s₂)
.

Inductive ktx_sim EV HV V L : ktx EV HV V L → ktx EV HV V L → Prop :=
| ktx_hole_sim : ktx_sim ktx_hole ktx_hole
| ktx_down_sim :
  ∀ K₁ K₂ X₁ X₂, ktx_sim K₁ K₂ → var_sim X₁ X₂ →
  ktx_sim (ktx_down K₁ X₁) (ktx_down K₂ X₂)
| ktx_let_sim :
  ∀ K₁ K₂ t₁ t₂,
  ktx_sim K₁ K₂ → @tm_sim _ _ _ _ t₁ t₂ →
  ktx_sim (ktx_let K₁ t₁) (ktx_let K₂ t₂)
| ktx_eapp_sim :
  ∀ K₁ K₂ 𝓔₁ 𝓔₂,
  ktx_sim K₁ K₂ → eff_sim 𝓔₁ 𝓔₂ →
  ktx_sim (ktx_eapp K₁ 𝓔₁) (ktx_eapp K₂ 𝓔₂)
| ktx_happ_sim :
  ∀ K₁ K₂ h₁ h₂,
  ktx_sim K₁ K₂ → hd_sim h₁ h₂ →
  ktx_sim (ktx_happ K₁ h₁) (ktx_happ K₂ h₂)
| ktx_app1_sim :
  ∀ K₁ K₂ t₁ t₂,
  ktx_sim K₁ K₂ → tm_sim t₁ t₂ →
  ktx_sim (ktx_app1 K₁ t₁) (ktx_app1 K₂ t₂)
| ktx_app2_sim :
  ∀ K₁ K₂ v₁ v₂,
  ktx_sim K₁ K₂ → val_sim v₁ v₂ →
  ktx_sim (ktx_app2 K₁ v₁) (ktx_app2 K₂ v₂)
.

Definition xEnv_sim EV HV V (Γ₁ Γ₂ : V → ty EV HV ∅) : Prop :=
∀ x, ty_sim (Γ₁ x) (Γ₂ x).

End section_sim.

Fixpoint XEnv_sim_aux (Xs₁ Xs₂ : list var) EV HV (Ξ₁ Ξ₂ : XEnv EV HV) : Prop :=
match Ξ₁, Ξ₂ with
| [], [] => True
| (X₁, (T₁, 𝓔₁)) :: Ξ₁, (X₂, (T₂, 𝓔₂)) :: Ξ₂ =>
  ty_sim Xs₁ Xs₂ T₁ T₂ ∧ eff_sim Xs₁ Xs₂ 𝓔₁ 𝓔₂ ∧
  XEnv_sim_aux (X₁ :: Xs₁) (X₂ :: Xs₂) Ξ₁ Ξ₂
| _, _ => False
end.

Definition XEnv_sim EV HV (Ξ₁ Ξ₂ : XEnv EV HV) : Prop :=
XEnv_sim_aux [] [] Ξ₁ Ξ₂.

