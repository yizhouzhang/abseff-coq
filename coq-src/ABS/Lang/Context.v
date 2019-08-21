Require Import Lang.Syntax.
Require Import Lang.Bindings.
Require Import Lang.Operational.
Require Import Lang.Static.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Inductive ctx : Set → Set → Set → Set → Type :=
| ctx_top   : ctx ∅ ∅ ∅ ∅
| ctx_Down  : ∀ EV HV V L, ctx EV HV V L → ctx EV HV V (inc L)
| ctx_up    : ∀ EV HV V L, ctx EV HV V L → F → L → ctx EV HV (inc (inc V)) L
| ctx_let1 : ∀ EV HV V L, ctx EV HV V L → tm EV HV (inc V) L → ctx EV HV V L
| ctx_let2 : ∀ EV HV V L, ctx EV HV V L → tm EV HV V L → ctx EV HV (inc V) L
| ctx_efun  : ∀ EV HV V L, ctx EV HV V L → ctx (inc EV) HV V L
| ctx_hfun  : ∀ EV HV V L, ctx EV HV V L → ctx EV (inc HV) V L
| ctx_fun   : ∀ EV HV V L, ctx EV HV V L → ctx EV HV (inc V) L
| ctx_eapp  : ∀ EV HV V L, ctx EV HV V L → eff EV HV L → ctx EV HV V L
| ctx_happ1 : ∀ EV HV V L, ctx EV HV V L → hd EV HV V L → ctx EV HV V L
| ctx_happ2 : ∀ EV HV V L, ctx EV HV V L → tm EV HV V L → F → L → ctx EV HV (inc (inc V)) L
| ctx_app1  : ∀ EV HV V L, ctx EV HV V L → tm EV HV V L → ctx EV HV V L
| ctx_app2  : ∀ EV HV V L, ctx EV HV V L → tm EV HV V L → ctx EV HV V L
.

Fixpoint
ctx_plug EV HV V L (C : ctx EV HV V L) (t : tm EV HV V L) {struct C} : tm0.
Proof.
destruct C as [ | ? ? ? ? C | ? ? ? ? C 𝔽 β | ? ? ? ? C r | ? ? ? ? C s |
  ? ? ? ? C | ? ? ? ? C | ? ? ? ? C |
  ? ? ? ? C E | ? ? ? ? C h | ? ? ? ? C f 𝔽 β | ? ? ? ? C s | ? ? ? ? C f ].
+ refine t.
+ refine (ctx_plug _ _ _ _ C (⬇ t)).
+ refine (ctx_plug _ _ _ _ C (⇧ (hd_def 𝔽 (lid_b β) t))).
+ refine (ctx_plug _ _ _ _ C (tm_let t r)).
+ refine (ctx_plug _ _ _ _ C (tm_let s t)).
+ refine (ctx_plug _ _ _ _ C (val_efun t)).
+ refine (ctx_plug _ _ _ _ C (val_hfun t)).
+ refine (ctx_plug _ _ _ _ C (val_fun t)).
+ refine (ctx_plug _ _ _ _ C (tm_eapp t E)).
+ refine (ctx_plug _ _ _ _ C (tm_happ t h)).
+ refine (ctx_plug _ _ _ _ C (tm_happ f (hd_def 𝔽 (lid_b β) t))).
+ refine (ctx_plug _ _ _ _ C (tm_app t s)).
+ refine (ctx_plug _ _ _ _ C (tm_app f t)).
Defined.

Fixpoint
Xs_ctx EV HV V L (C : ctx EV HV V L) {struct C} : vars.
Proof.
destruct C as [ | ? ? ? ? C | ? ? ? ? C 𝔽 β | ? ? ? ? C r | ? ? ? ? C s |
  ? ? ? ? C | ? ? ? ? C | ? ? ? ? C |
  ? ? ? ? C E | ? ? ? ? C h | ? ? ? ? C r 𝔽 β | ? ? ? ? C s | ? ? ? ? C f ].
+ refine \{}.
+ refine (Xs_ctx _ _ _ _ C).
+ refine (Xs_ctx _ _ _ _ C).
+ refine (Xs_ctx _ _ _ _ C \u Xs_tm r).
+ refine (Xs_ctx _ _ _ _ C \u Xs_tm s).
+ refine (Xs_ctx _ _ _ _ C).
+ refine (Xs_ctx _ _ _ _ C).
+ refine (Xs_ctx _ _ _ _ C).
+ refine (Xs_ctx _ _ _ _ C \u Xs_eff E).
+ refine (Xs_ctx _ _ _ _ C \u Xs_hd h).
+ refine (Xs_ctx _ _ _ _ C \u Xs_tm r).
+ refine (Xs_ctx _ _ _ _ C \u Xs_tm s).
+ refine (Xs_ctx _ _ _ _ C \u Xs_tm f).
Defined.

Section section_Xs_ctx_plug.
Hint Rewrite union_empty_l union_empty_r union_assoc.

Hint Extern 1 => match goal with
| [ |- ?A \u ?B \u ?C = (?A \u ?C) \u ?B ] => rewrite union_comm_assoc, union_comm
end.

Fixpoint
Xs_ctx_plug EV HV V L (C : ctx EV HV V L) t :
Xs_tm (ctx_plug C t) = Xs_ctx C \u Xs_tm t.
Proof.
destruct C ; simpl ; crush.
Qed.

End section_Xs_ctx_plug.

Inductive
ok_ctx :
∀ EV HV V L, ctx EV HV V L → (HV → F) → (V → ty EV HV L) → (LEnv EV HV L) →
ty EV HV L → eff EV HV L → ty0 → Type :=
| ok_ctx_top :
  ∀ T,
  ok_ctx ctx_top ∅→ ∅→ LEnv_empty T [] T
| ok_ctx_Down :
  ∀ EV HV V L (C : ctx EV HV V L) P Γ Π T E T',
  ok_ctx C P Γ Π T E T' →
  ok_ty Π T → ok_eff Π E →
  ok_Γ Π Γ →
  ok_ctx (ctx_Down C) P (compose L_shift_ty Γ) (LEnv_push Π T E)
    (L_shift_ty T) ((ef_lbl (lbl_id (lid_b VZ))) :: (L_shift_eff E)) T'
| ok_ctx_up :
  ∀ EV HV V L (C : ctx EV HV V L) 𝔽 β P Γ Π T E T'',
  ok_ctx C P Γ Π (
    ty_fun
    (L_open_ty (HV_open_ty (EV_open_ty (fst (Σ 𝔽)))))
    (L_open_ty (HV_open_ty (EV_open_ty (snd (Σ 𝔽)))))
    [ef_lbl (lbl_id (lid_b β))]
  ) [] T'' →
  LEnv_lookup β Π = (T, E) →
  ok_Γ Π Γ →
  ok_ctx (ctx_up C 𝔽 β) P (
    env_ext
      (env_ext Γ (L_open_ty (HV_open_ty (EV_open_ty (fst (Σ 𝔽))))))
      (ty_fun (L_open_ty (HV_open_ty (EV_open_ty (snd (Σ 𝔽))))) T E)
  ) Π T E T''
| ok_ctx_let1 :
  ∀ EV HV V L (C : ctx EV HV V L) t P Γ Π S E T T',
  ok_ctx C P Γ Π T E T' →
  ok_tm Π P (env_ext Γ S) t T E →
  ok_ty Π S →
  ok_Γ Π Γ →
  ok_ctx (ctx_let1 C t) P Γ Π S E T'
| ok_ctx_let2 :
  ∀ EV HV V L (C : ctx EV HV V L) s P Γ Π S E T T',
  ok_ctx C P Γ Π T E T' →
  ok_tm Π P Γ s S E →
  ok_Γ Π Γ →
  ok_ctx (ctx_let2 C s) P (env_ext Γ S) Π T E T'
| ok_ctx_efun :
  ∀ EV HV V L (C : ctx EV HV V L) P Γ Π T T'',
  ok_ctx C P Γ Π (ty_efun T) [] T'' →
  ok_Γ Π Γ →
  ok_ctx (ctx_efun C) P (EV_shift_ty ∘ Γ) (EV_shift_LEnv Π) T [] T''
| ok_ctx_hfun :
  ∀ EV HV V L (C : ctx EV HV V L) P Γ Π 𝔽 T T'',
  ok_ctx C P Γ Π (ty_hfun 𝔽 T) [] T'' →
  ok_Γ Π Γ →
  ok_ctx (ctx_hfun C) (env_ext P 𝔽) (HV_shift_ty ∘ Γ) (HV_shift_LEnv Π) T [] T''
| ok_ctx_fun :
  ∀ EV HV V L (C : ctx EV HV V L) P Γ Π S T E T'',
  ok_ctx C P Γ Π (ty_fun S T E) [] T'' →
  ok_Γ Π Γ →
  ok_ctx (ctx_fun C) P (env_ext Γ S) Π T E T''
| ok_ctx_eapp :
  ∀ EV HV V L (C : ctx EV HV V L) 𝓔₁ P Γ Π T 𝓔₂ T'',
  ok_ctx C P Γ Π (EV_subst_ty 𝓔₁ T) 𝓔₂ T'' →
  ok_eff Π 𝓔₁ →
  ok_Γ Π Γ →
  ok_ctx (ctx_eapp C 𝓔₁) P Γ Π (ty_efun T) 𝓔₂ T''
| ok_ctx_happ1 :
  ∀ EV HV V L (C : ctx EV HV V L) h P Γ Π 𝔽 T 𝓔 T'',
  ok_ctx C P Γ Π (HV_subst_ty h T) 𝓔 T'' →
  ok_hd Π P Γ h 𝔽 →
  ok_Γ Π Γ →
  ok_ctx (ctx_happ1 C h) P Γ Π (ty_hfun 𝔽 T) 𝓔 T''
| ok_ctx_happ2 :
  ∀ EV HV V L (C : ctx EV HV V L) t 𝔽 β P Γ Π T 𝓔 T' T'',
(*   ok_ctx C P Γ Π (HV_subst_ty (hd_def 𝔽 (lid_b β) val_unit : hd EV HV V L) T') 𝓔 T'' → *)
  ∀ (h : hd EV HV V L), lbl_hd h = lbl_id (lid_b β) → ok_ctx C P Γ Π (HV_subst_ty h T') 𝓔 T'' →
  ok_tm Π P Γ t (ty_hfun 𝔽 T') 𝓔 →
  LEnv_lookup β Π = (T, 𝓔) →
  ok_Γ Π Γ →
  ok_ctx (ctx_happ2 C t 𝔽 β) P (
    env_ext
      (env_ext Γ (L_open_ty (HV_open_ty (EV_open_ty (fst (Σ 𝔽))))))
      (ty_fun (L_open_ty (HV_open_ty (EV_open_ty (snd (Σ 𝔽))))) T 𝓔)
  ) Π T 𝓔 T''
| ok_ctx_app1 :
  ∀ EV HV V L (C : ctx EV HV V L) s P Γ Π S T E T'',
  ok_ctx C P Γ Π T E T'' →
  ok_tm Π P Γ s S E →
  ok_Γ Π Γ →
  ok_ctx (ctx_app1 C s) P Γ Π (ty_fun S T E) E T''
| ok_ctx_app2 :
  ∀ EV HV V L (C : ctx EV HV V L) t P Γ Π S T E T'',
  ok_ctx C P Γ Π T E T'' →
  ok_tm Π P Γ t (ty_fun S T E) E →
  ok_Γ Π Γ →
  ok_ctx (ctx_app2 C t) P Γ Π S E T''
| ok_ctx_sub :
  ∀ EV HV V L (C : ctx EV HV V L) P Γ Π T1 E1 T2 E2 T'',
  ok_ctx C P Γ Π T2 E2 T'' →
  subty T1 T2 → se E1 E2 →
  ok_Γ Π Γ →
  ok_ctx C P Γ Π T1 E1 T''
.

Definition ctx_equiv EV HV V L (t₁ t₂ : tm EV HV V L)
(Π : LEnv EV HV L) (P : HV → F) (Γ : V → ty EV HV L)
(T : ty EV HV L) (E : eff EV HV L) : Prop :=
∀ C T', ok_ctx C P Γ Π T E T' → Xs_ctx C = \{} →
∀ ξ₁ (v₁ : val0), step_refl_tran ⟨[], ctx_plug C t₁⟩ ⟨ξ₁, v₁⟩ →
∃ ξ₂ (v₂ : val0), step_refl_tran ⟨[], ctx_plug C t₂⟩ ⟨ξ₂, v₂⟩.
