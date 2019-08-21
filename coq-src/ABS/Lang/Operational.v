Require Import Utf8 List Wf Lia.
Import ListNotations.
Require Import CpdtTactics.
Require Import LibLN.
Require Import Lang.Syntax Lang.Bindings.
Local Set Implicit Arguments.

Section section_ktx.
Context (EV HV V L : Set).

(** Use [t] to fill in the hole of [ktx] *)
Fixpoint ktx_plug
(K : ktx EV HV V L) (t : tm EV HV V L) {struct K} :
tm EV HV V L.
Proof.
destruct K as [ | K X | K s | K 𝓔 | K h | K s | K v ].
+ refine t.
+ refine (⇩ X (ktx_plug K t)).
+ refine (tm_let (ktx_plug K t) s).
+ refine (tm_eapp (ktx_plug K t) 𝓔).
+ refine (tm_happ (ktx_plug K t) h).
+ refine (tm_app (ktx_plug K t) s).
+ refine (tm_app v (ktx_plug K t)).
Defined.

(** Compose [outer] and [inner] to form a new evaluation context. *)
Fixpoint ktx_comp
(outer : ktx EV HV V L) (inner : ktx EV HV V L) {struct outer} :
ktx EV HV V L :=
match outer with
| ktx_hole => inner
| ktx_down J X => ktx_down (ktx_comp J inner) X
| ktx_let J s => ktx_let (ktx_comp J inner) s
| ktx_eapp J 𝓔 => ktx_eapp (ktx_comp J inner) 𝓔
| ktx_happ J h => ktx_happ (ktx_comp J inner) h
| ktx_app1 J s => ktx_app1 (ktx_comp J inner) s
| ktx_app2 J v => ktx_app2 (ktx_comp J inner) v
end.

(** Return [True] iff [X] is not bound in [K]. *)
Fixpoint tunnels (X : var) (K : ktx EV HV V L) : Prop :=
match K with
| ktx_hole => True
| ktx_let J _ => tunnels X J
| ktx_eapp J _ => tunnels X J
| ktx_happ J _ => tunnels X J
| ktx_app1 J _ => tunnels X J
| ktx_app2 J _ => tunnels X J
| ktx_down J X' => tunnels X J ∧ ¬ X = X'
end.

End section_ktx.


Inductive config :=
| config_mk : list var → tm0 → config
.

Notation "⟨ ξ , t ⟩" := (config_mk ξ t) : core_scope.

Inductive step : config → config → Prop :=
| step_let :
  ∀ ξ (v : val0) t,
  step ⟨ξ, tm_let v t⟩ ⟨ξ, V_subst_tm v t⟩
| step_eapp :
  ∀ ξ t 𝓔,
  step ⟨ξ, tm_eapp (val_efun t) 𝓔⟩ ⟨ξ, EV_subst_tm 𝓔 t⟩
| step_happ :
  ∀ ξ t h,
  step ⟨ξ, tm_happ (val_hfun t) h⟩ ⟨ξ, HV_subst_tm h t⟩
| step_app :
  ∀ ξ t (v : val0),
  step ⟨ξ, tm_app (val_fun t) v⟩ ⟨ξ, V_subst_tm v t⟩
| step_Down :
  ∀ ξ t X,
  X ∉ from_list ξ → (* this arbitrariness about [X] allows non-determinism *) 
  step ⟨ξ, ⬇ t⟩ ⟨X :: ξ, ⇩ X (L_subst_tm (lid_f X) t)⟩
| step_down_val :
  ∀ ξ X (v : val0),
(*   X ∈ from_list ξ → *)
  step ⟨ξ, ⇩ X v⟩ ⟨ξ, v⟩
| step_down_up :
  ∀ ξ X K 𝔽 t (v : val0),
(*   X ∈ from_list ξ → *)
  tunnels X K →
  step
  ⟨ξ, ⇩ X (ktx_plug K (tm_app (⇧ (hd_def 𝔽 (lid_f X) t)) v))⟩
  ⟨ξ,
    let cont := val_fun (⇩ X (ktx_plug (V_open_ktx K) (val_var VZ))) in
    V2_subst_tm v cont t
  ⟩
| step_ktx_down :
  ∀ ξ₁ ξ₂ t₁ t₂ X,
  step ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
  step ⟨ξ₁, ⇩ X t₁⟩ ⟨ξ₂, ⇩ X t₂⟩
| step_ktx_let :
  ∀ ξ₁ ξ₂ t₁ t₂ s,
  step ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
  step ⟨ξ₁, tm_let t₁ s⟩ ⟨ξ₂, tm_let t₂ s⟩
| step_ktx_app1 :
  ∀ ξ₁ ξ₂ t₁ t₂ s,
  step ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
  step ⟨ξ₁, tm_app t₁ s⟩ ⟨ξ₂, tm_app t₂ s⟩
| step_ktx_app2 :
  ∀ ξ₁ ξ₂ (v : val0) t₁ t₂ ,
  step ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
  step ⟨ξ₁, tm_app v t₁⟩ ⟨ξ₂, tm_app v t₂⟩
| step_ktx_eapp :
  ∀ ξ₁ ξ₂ t₁ t₂ 𝓔,
  step ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
  step ⟨ξ₁, tm_eapp t₁ 𝓔⟩ ⟨ξ₂, tm_eapp t₂ 𝓔⟩
| step_ktx_happ :
  ∀ ξ₁ ξ₂ t₁ t₂ h,
  step ⟨ξ₁, t₁⟩ ⟨ξ₂, t₂⟩ →
  step ⟨ξ₁, tm_happ t₁ h⟩ ⟨ξ₂, tm_happ t₂ h⟩
.


(** The transitive closure of the reduction relation. *)
Definition step_tran := @Relation_Operators.clos_trans_1n _ step.

(** The reflexive and transitive closure of the reduction relation. *)
Definition step_refl_tran := @Relation_Operators.clos_refl_trans_1n _ step.

(** Reduction in a given number of steps. *)
Inductive step_n : nat → config → config → Prop :=
| step_n_O : ∀ c, step_n O c c
| step_n_S : ∀ n c₁ c₂ c₃,
    step c₁ c₂ →
    step_n n c₂ c₃ →
    step_n (S n) c₁ c₃
.