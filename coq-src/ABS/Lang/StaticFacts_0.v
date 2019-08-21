Require Import Lang.Syntax.
Require Import Lang.Bindings.
Require Import Lang.Static.
Require Import Lang.BindingsFacts.
Require Import Setoid.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

(** * Facts about the preorders on effects *)

Section section_eff_facts.
Context (EV HV L : Set).

Lemma se_transitive (𝓔₁ 𝓔₂ 𝓔₃ : eff EV HV L) : se 𝓔₁ 𝓔₂ → se 𝓔₂ 𝓔₃ → se 𝓔₁ 𝓔₃.
Proof.
auto.
Qed.

Lemma se_reflexive (𝓔 : eff EV HV L) : se 𝓔 𝓔.
Proof.
auto.
Qed.

Instance se_PreOrder : PreOrder (fun 𝓔₁ 𝓔₂ => se 𝓔₁ 𝓔₂) := {
  PreOrder_Reflexive  := @se_reflexive ;
  PreOrder_Transitive := @se_transitive ;
}.

Lemma se_nil (𝓔 : eff EV HV L) : se [] 𝓔.
Proof.
induction 𝓔 ; crush.
Qed.

Lemma se_cons_l (e : ef EV HV L) 𝓔1 𝓔2 : se (e :: 𝓔1) 𝓔2 -> se 𝓔1 𝓔2.
Proof.
crush.
Qed.

Lemma se_cons_r (e : ef EV HV L) 𝓔1 𝓔2 : se 𝓔1 𝓔2 -> se 𝓔1 (e :: 𝓔2).
Proof.
crush.
Qed.

Lemma se_app_l (𝓔1 𝓔2 : eff EV HV L) : se 𝓔1 (𝓔1 ++ 𝓔2).
Proof.
crush.
Qed.

Lemma se_app_r (𝓔1 𝓔2 : eff EV HV L) : se 𝓔2 (𝓔1 ++ 𝓔2).
Proof.
crush.
Qed.

Lemma se_app (𝓔1 𝓔2 E : eff EV HV L) : se 𝓔1 E -> se 𝓔2 E -> se (𝓔1 ++ 𝓔2) E.
Proof.
Hint Rewrite in_app_iff.
crush.
Qed.

End section_eff_facts.


(** * Facts about the preorders on types *)

Section section_ty_facts.

Hint Constructors st.
Hint Resolve se_reflexive.

Lemma st_transitive EV HV (T₁ T₂ T₃ : ty EV HV ∅) : st T₁ T₂ → st T₂ T₃ → st T₁ T₃.
Proof.
eauto.
Qed.

Fixpoint st_reflexive EV HV (T : ty EV HV ∅) : st T T.
Proof.
destruct T ; simpl.
+ apply st_unit.
+ apply st_fun ; auto.
+ apply st_efun ; eauto.
+ apply st_hfun ; auto.
Qed.

Instance st_PreOrder EV HV : PreOrder (@st EV HV) := {
  PreOrder_Reflexive  := @st_reflexive EV HV ;
  PreOrder_Transitive := @st_transitive EV HV ;
}.

End section_ty_facts.


Section section_wf_XEnv.

Hint Rewrite concat_empty_r concat_assoc.
Hint Rewrite notin_singleton notin_union dom_empty dom_concat dom_single.
Hint Extern 0 => match goal with
| [ H : empty = _ & _ ~ _ |- _ ] => apply empty_push_inv in H ; crush
| [ H : _ & _ ~ _ = _ & _ ~ _ |- _ ] => apply eq_push_inv in H ; crush
end.

Lemma ok_concat_indom_l EV HV (Ξ Ξ' : XEnv EV HV) :
ok (Ξ & Ξ') → ∀ X, X ∈ dom Ξ → X ∉ dom Ξ'.
Proof.
intros ok_ΞΞ' X HX.
induction Ξ' using env_ind ; [crush|].
rewrite concat_assoc in ok_ΞΞ'.
inversion ok_ΞΞ' ; crush.
Qed.

Lemma wf_XEnv_ok EV HV (Ξ : XEnv EV HV) :
wf_XEnv Ξ → ok Ξ.
Proof.
induction 1 ; constructor ; crush.
Qed.

Lemma wf_XEnv_concat_inv_l EV HV (Ξ Ξ' : XEnv EV HV) :
wf_XEnv (Ξ & Ξ') → wf_XEnv Ξ.
Proof.
induction Ξ' as [ | Ξ'' X [??] ] using env_ind ; [crush|].
rewrite concat_assoc.
inversion 1 ; crush.
Qed.

End section_wf_XEnv.
