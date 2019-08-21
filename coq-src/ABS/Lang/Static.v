Require Import Lang.Syntax.
Require Import Lang.Bindings.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Notation se 𝓔₁ 𝓔₂ := (∀ ε, In ε 𝓔₁ → In ε 𝓔₂).

Inductive st EV HV : ty EV HV ∅ → ty EV HV ∅ → Prop :=
| st_unit : st 𝟙 𝟙
| st_fun  :
  ∀ T S₁ S₂ 𝓔₁ 𝓔₂,
  st S₁ S₂ → se 𝓔₁ 𝓔₂ →
  st (ty_fun T S₁ 𝓔₁) (ty_fun T S₂ 𝓔₂)
| st_efun :
  ∀ T₁ T₂,
  @st _ _ T₁ T₂ →
  st (ty_efun T₁) (ty_efun T₂)
| st_hfun :
  ∀ 𝔽 T₁ T₂,
  @st _ _ T₁ T₂ →
  st (ty_hfun 𝔽 T₁) (ty_hfun 𝔽 T₂)
| st_tran :
  ∀ T₁ T₂ T₃, st T₁ T₂ → st T₂ T₃ → st T₁ T₃.

Inductive wf_lbl EV HV (Ξ : XEnv EV HV) : lbl HV ∅ → Prop :=
| wf_lbl_id : ∀ X, X \in dom Ξ → wf_lbl Ξ (lbl_id (lid_f X))
| wf_lbl_var : ∀ p, wf_lbl Ξ (lbl_var p)
.

Inductive wf_ef EV HV (Ξ : XEnv EV HV) : ef EV HV ∅ → Prop :=
| wf_ef_var : ∀ α, wf_ef Ξ (ef_var α)
| wf_ef_lbl : ∀ ℓ, wf_lbl Ξ ℓ → wf_ef Ξ (ef_lbl ℓ)
.

Inductive wf_eff EV HV (Ξ : XEnv EV HV) : eff EV HV ∅ → Prop :=
| wf_eff_nil  : wf_eff Ξ []
| wf_eff_cons : ∀ ε 𝓔, wf_ef Ξ ε → wf_eff Ξ 𝓔 → wf_eff Ξ (ε :: 𝓔)
.

Inductive wf_ty EV HV (Ξ : XEnv EV HV) : ty EV HV ∅ → Prop :=
| wf_ty_unit : wf_ty Ξ 𝟙
| wf_ty_fun :
  ∀ S T 𝓔,
  wf_ty Ξ S → wf_ty Ξ T → wf_eff Ξ 𝓔 →
  wf_ty Ξ (ty_fun S T 𝓔)
| wf_ty_efun :
  ∀ T,
  wf_ty (EV := inc EV) (EV_shift_XEnv Ξ) T →
  wf_ty Ξ (ty_efun T)
| wf_ty_hfun :
  ∀ 𝔽 T,
  wf_ty (HV := inc HV) (HV_shift_XEnv Ξ) T →
  wf_ty Ξ (ty_hfun 𝔽 T)
.


Inductive
wf_hd EV HV V (Ξ : XEnv EV HV) (P : HV → F) (Γ : V → ty EV HV ∅) :
hd EV HV V ∅ → F → Prop :=

| wf_hd_var : ∀ p, wf_hd Ξ P Γ (hd_var p) (P p)

| wf_hd_def : ∀ 𝔽 X T 𝓔 t,
  binds X (T, 𝓔) Ξ →
  wf_tm (V := inc (inc V)) Ξ P (
    env_ext
      (env_ext Γ (HV_open_ty (EV_open_ty (fst (Σ 𝔽)))))
      (ty_fun (HV_open_ty (EV_open_ty (snd (Σ 𝔽)))) T 𝓔)
  ) t T 𝓔 →
  wf_hd Ξ P Γ (hd_def 𝔽 (lid_f X) t) 𝔽

with
wf_val EV HV V (Ξ : XEnv EV HV) (P : HV → F) (Γ : V → ty EV HV ∅) :
val EV HV V ∅ → ty EV HV ∅ → Prop :=

| wf_val_unit : wf_val Ξ P Γ val_unit 𝟙

| wf_val_var : ∀ x, wf_val Ξ P Γ (val_var x) (Γ x)

| wf_val_fun : ∀ t S T 𝓔,
  wf_tm (V := inc V) Ξ P (env_ext Γ S) t T 𝓔 →
  wf_ty Ξ S →
  wf_val Ξ P Γ (val_fun t) (ty_fun S T 𝓔)

| wf_val_efun : ∀ t T,
  wf_tm (EV := inc EV) (EV_shift_XEnv Ξ) P (EV_shift_ty ∘ Γ) t T [] →
  wf_val Ξ P Γ (val_efun t) (ty_efun T)

| wf_val_hfun : ∀ t 𝔽 T,
  wf_tm (HV := inc HV) (HV_shift_XEnv Ξ) (env_ext P 𝔽) (HV_shift_ty ∘ Γ) t T [] →
  wf_val Ξ P Γ (val_hfun t) (ty_hfun 𝔽 T)

| wf_val_up : ∀ h 𝔽,
  wf_hd Ξ P Γ h 𝔽 →
  wf_val Ξ P Γ (⇧ h) (
    ty_fun
    (HV_open_ty (EV_open_ty (fst (Σ 𝔽))))
    (HV_open_ty (EV_open_ty (snd (Σ 𝔽))))
    [ef_lbl (lbl_hd h)]
  )

with
wf_tm EV HV V (Ξ : XEnv EV HV) (P : HV → F) (Γ : V → ty EV HV ∅) :
tm EV HV V ∅ → ty EV HV ∅ → eff EV HV ∅ → Prop :=

| wf_tm_val :
  ∀ v T,
  wf_val Ξ P Γ v T → wf_tm Ξ P Γ v T []

| wf_tm_app :
  ∀ t s S T 𝓔,
  wf_tm Ξ P Γ t (ty_fun S T 𝓔) 𝓔 →
  wf_tm Ξ P Γ s S 𝓔 →
  wf_tm Ξ P Γ (tm_app t s) T 𝓔

| wf_tm_let :
  ∀ s t S T 𝓔,
  wf_ty Ξ S →
  wf_tm Ξ P Γ s S 𝓔 →
  wf_tm (V := inc V) Ξ P (env_ext Γ S) t T 𝓔 →
  wf_tm Ξ P Γ (tm_let s t) T 𝓔

| wf_tm_eapp :
  ∀ t 𝓔 T 𝓕,
  wf_tm Ξ P Γ t (ty_efun T) 𝓕 →
  wf_eff Ξ 𝓔 →
  wf_tm Ξ P Γ (tm_eapp t 𝓔) (EV_subst_ty 𝓔 T) 𝓕

| wf_tm_happ :
  ∀ t h 𝔽 T 𝓔,
  wf_tm Ξ P Γ t (ty_hfun 𝔽 T) 𝓔 →
  wf_hd Ξ P Γ h 𝔽 →
  wf_tm Ξ P Γ (tm_happ t h) (HV_subst_ty h T) 𝓔

| wf_tm_Down :
  ∀ t T 𝓔 (B : vars),
  wf_ty Ξ T →
  wf_eff Ξ 𝓔 →
  ( ∀ X, X ∉ B →
    wf_tm (Ξ & X ~ (T, 𝓔)) P Γ
    (L_subst_tm (lid_f X) t) T (ef_lbl (lbl_id (lid_f X)) :: 𝓔)
  ) →
  wf_tm Ξ P Γ (⬇ t) T 𝓔

| wf_tm_sub :
  ∀ t T1 T2 𝓔1 𝓔2,
  wf_tm Ξ P Γ t T1 𝓔1 →
  st T1 T2 → se 𝓔1 𝓔2 →
  wf_tm Ξ P Γ t T2 𝓔2
.

Inductive wf_XEnv EV HV : XEnv EV HV → Prop :=
| wf_XEnv_empty : wf_XEnv empty
| wf_XEnv_cons Ξ X T 𝓔 :
    wf_XEnv Ξ → X # Ξ → wf_ty Ξ T → wf_eff Ξ 𝓔 →
    wf_XEnv (Ξ & X ~ (T, 𝓔))
.

Definition wf_Γ EV HV V (Ξ : XEnv EV HV) (Γ : V → ty EV HV ∅) : Prop :=
∀ x, wf_ty Ξ (Γ x).

Inductive XLEnv EV LV :
∀ L, XEnv EV LV → LEnv EV LV L → (L → lid ∅) → Prop :=
| XLEnv_empty : XLEnv empty LEnv_empty ∅→
| XLEnv_push :
  ∀ L Ξ X T E (Π : LEnv EV LV L) (f : L → lid ∅),
  XLEnv Ξ Π f → X ∉ dom Ξ →
  wf_ty Ξ (L_bind_ty f T) → wf_eff Ξ (L_bind_eff f E) →
  XLEnv
    (Ξ & X ~ (L_bind_ty f T, L_bind_eff f E))
    (LEnv_push Π T E)
    (env_ext f (lid_f X))
.

Section section_ok.

(** Static semantics with label identifiers represented as de Bruijn indices *)

Inductive
subty EV LV L : ty EV LV L → ty EV LV L → Prop :=
  | subty_unit : subty 𝟙 𝟙
  | subty_efun : ∀ T1 T2, @subty _ _ _ T1 T2 → subty (ty_efun T1) (ty_efun T2)
  | subty_hfun : ∀ 𝔽 T1 T2, @subty _ _ _ T1 T2 → subty (ty_hfun 𝔽 T1) (ty_hfun 𝔽 T2)
  | subty_fun :
    ∀ T R1 R2 E1 E2, subty R1 R2 → se E1 E2 →
    subty (ty_fun T R1 E1) (ty_fun T R2 E2)
  | subty_tran :
    ∀ T1 T2 T3, subty T1 T2 → subty T2 T3 → subty T1 T3
.

Arguments subty_unit [EV LV L].

Inductive ok_lbl EV LV L (Π : LEnv EV LV L) : lbl LV L → Prop :=
| ok_lbl_id : ∀ β, ok_lbl Π (lbl_id (lid_b β))
| ok_lbl_var : ∀ p, ok_lbl Π (lbl_var p)
.

Inductive ok_ef EV LV L (Π : LEnv EV LV L) : ef EV LV L → Prop :=
| ok_ef_var : ∀ α, ok_ef Π (ef_var α)
| ok_ef_lbl : ∀ ℓ, ok_lbl Π ℓ → ok_ef Π (ef_lbl ℓ)
.

Inductive ok_eff EV LV L (Π : LEnv EV LV L) : eff EV LV L → Prop :=
| ok_eff_nil  : ok_eff Π []
| ok_eff_cons : ∀ ε 𝓔, ok_ef Π ε → ok_eff Π 𝓔 → ok_eff Π (ε :: 𝓔)
.

Inductive ok_ty EV HV L (Π : LEnv EV HV L) : ty EV HV L → Prop :=
| ok_ty_unit : ok_ty Π 𝟙
| ok_ty_fun :
  ∀ S T 𝓔,
  ok_ty Π S → ok_ty Π T → ok_eff Π 𝓔 →
  ok_ty Π (ty_fun S T 𝓔)
| ok_ty_efun :
  ∀ T,
  ok_ty (EV := inc EV) (EV_shift_LEnv Π) T →
  ok_ty Π (ty_efun T)
| ok_ty_hfun :
  ∀ 𝔽 T,
  ok_ty (HV := inc HV) (HV_shift_LEnv Π) T →
  ok_ty Π (ty_hfun 𝔽 T)
.

Fixpoint LEnv_lookup EV LV L (β : L) (Π : LEnv EV LV L) {struct Π} :
ty EV LV L * eff EV LV L.
Proof.
destruct Π as [ | L Π T E ].
+ destruct β.
+ destruct β as [ | β ].
  - exact (L_shift_ty T, L_shift_eff E).
  - exact (
      (λ p, match p with (T, E) => (L_shift_ty T, L_shift_eff E) end)
      (LEnv_lookup _ _ _ β Π)
    ).
Defined.

Inductive
ok_hd EV HV V L (Π : LEnv EV HV L) (P : HV → F) (Γ : V → ty EV HV L) :
hd EV HV V L → F → Prop :=

| ok_hd_var : ∀ p, ok_hd Π P Γ (hd_var p) (P p)

| ok_hd_def : ∀ 𝔽 β T 𝓔 t,
  LEnv_lookup β Π = (T, 𝓔) →
  ok_tm (V := inc (inc V)) Π P (
    env_ext
      (env_ext Γ (L_open_ty (HV_open_ty (EV_open_ty (fst (Σ 𝔽))))))
      (ty_fun (L_open_ty (HV_open_ty (EV_open_ty (snd (Σ 𝔽))))) T 𝓔)
  ) t T 𝓔 →
  ok_hd Π P Γ (hd_def 𝔽 (lid_b β) t) 𝔽

with
ok_val EV HV V L (Π : LEnv EV HV L) (P : HV → F) (Γ : V → ty EV HV L) :
val EV HV V L → ty EV HV L → Prop :=

| ok_val_unit : ok_val Π P Γ val_unit 𝟙

| ok_val_var : ∀ x, ok_val Π P Γ (val_var x) (Γ x)

| ok_val_fun : ∀ t S T 𝓔,
  ok_tm (V := inc V) Π P (env_ext Γ S) t T 𝓔 →
  ok_ty Π S →
  ok_val Π P Γ (val_fun t) (ty_fun S T 𝓔)

| ok_val_efun : ∀ t T,
  ok_tm (EV := inc EV) (EV_shift_LEnv Π) P (EV_shift_ty ∘ Γ) t T [] →
  ok_val Π P Γ (val_efun t) (ty_efun T)

| ok_val_hfun : ∀ t 𝔽 T,
  ok_tm (HV := inc HV) (HV_shift_LEnv Π) (env_ext P 𝔽) (HV_shift_ty ∘ Γ) t T [] →
  ok_val Π P Γ (val_hfun t) (ty_hfun 𝔽 T)

| ok_val_up : ∀ h 𝔽,
  ok_hd Π P Γ h 𝔽 →
  ok_val Π P Γ (⇧ h) (
    ty_fun
    (L_open_ty (HV_open_ty (EV_open_ty (fst (Σ 𝔽)))))
    (L_open_ty (HV_open_ty (EV_open_ty (snd (Σ 𝔽)))))
    [ef_lbl (lbl_hd h)]
  )

with
ok_tm EV HV V L (Π : LEnv EV HV L) (P : HV → F) (Γ : V → ty EV HV L) :
tm EV HV V L → ty EV HV L → eff EV HV L → Prop :=

| ok_tm_val :
  ∀ v T,
  ok_val Π P Γ v T → ok_tm Π P Γ v T []

| ok_tm_app :
  ∀ t s S T 𝓔,
  ok_tm Π P Γ t (ty_fun S T 𝓔) 𝓔 →
  ok_tm Π P Γ s S 𝓔 →
  ok_tm Π P Γ (tm_app t s) T 𝓔

| ok_tm_let :
  ∀ s t S T 𝓔,
  ok_ty Π S →
  ok_tm Π P Γ s S 𝓔 →
  ok_tm (V := inc V) Π P (env_ext Γ S) t T 𝓔 →
  ok_tm Π P Γ (tm_let s t) T 𝓔

| ok_tm_eapp :
  ∀ t 𝓔 T 𝓕,
  ok_tm Π P Γ t (ty_efun T) 𝓕 →
  ok_eff Π 𝓔 →
  ok_tm Π P Γ (tm_eapp t 𝓔) (EV_subst_ty 𝓔 T) 𝓕

| ok_tm_happ :
  ∀ t h 𝔽 T 𝓔,
  ok_tm Π P Γ t (ty_hfun 𝔽 T) 𝓔 →
  ok_hd Π P Γ h 𝔽 →
  ok_tm Π P Γ (tm_happ t h) (HV_subst_ty h T) 𝓔

| ok_tm_Down :
  ∀ t T 𝓔 (B : vars),
  ok_ty Π T →
  ok_eff Π 𝓔 →
  @ok_tm _ _ _ _ (LEnv_push Π T 𝓔) P (L_shift_ty ∘ Γ) t
    (L_shift_ty T) (ef_lbl (lbl_id (lid_b VZ)) :: (L_shift_eff 𝓔)) →
  ok_tm Π P Γ (⬇ t) T 𝓔

| ok_tm_sub :
  ∀ t T1 T2 𝓔1 𝓔2,
  ok_tm Π P Γ t T1 𝓔1 →
  subty T1 T2 → se 𝓔1 𝓔2 →
  ok_tm Π P Γ t T2 𝓔2
.

Definition ok_Γ EV LV V L (Π : LEnv EV LV L) (Γ : V → ty EV LV L) : Prop :=
∀ x, ok_ty Π (Γ x).

End section_ok.


Parameter Wf_Σ :
∀ 𝔽, wf_ty empty (fst (Σ 𝔽)) ∧ wf_ty empty (snd (Σ 𝔽)).

Hint Extern 0 => match goal with
| [ |- wf_ty empty (fst (Σ ?𝔽)) ] =>
  specialize (Wf_Σ 𝔽) ;
  let H := fresh in destruct 1 as [H _] ;
  apply H
| [ |- wf_ty empty (snd (Σ ?𝔽)) ] =>
  specialize (Wf_Σ 𝔽) ;
  let H := fresh in destruct 1 as [_ H] ;
  apply H
end.
