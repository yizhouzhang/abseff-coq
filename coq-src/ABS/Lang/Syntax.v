Require Import Utf8 List Basics FinFun.
Import ListNotations.
Require Import CpdtTactics.
Require Import LibLN.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

(** * Syntax *)

(**
If [V] is the type of the representation of a variable, then [inc V]
is the type of the representation of the same variable after the free
variable environment is extended by one.
*)
Inductive inc (V : Set) : Set :=
| VZ : inc V
| VS : V → inc V
.
Arguments VZ [V].
Arguments VS [V].

Fixpoint incn (n : nat) V : Set :=
  match n with
  | O => V
  | S m => incn m (inc V)
  end
.

Lemma incSn n : ∀ L, incn n (inc L) = inc (incn n L).
induction n ; crush.
Defined.

Notation "∅" := Empty_set.

(** Introduce [n] more free variables *)
Fixpoint nVS (n : nat) V {struct n} : V → incn n V.
Proof.
destruct n as [ | n ] ; simpl.
+ refine (λ x, x).
+ intro x.
  pose (x' := VS (nVS n V x)).
  rewrite <- incSn in x'.
  refine x'.
Defined.

Lemma SnVS (n : nat) V (x : V) : nVS n (VS x) = nVS (S n) x.
Proof.
induction n ; crush.
Qed.

Definition empty_fun {T} : ∅ → T :=
  λ y, match y with end.

Notation "∅→" := empty_fun.

Lemma empty_fun_is_injective T : Injective (∅→ : ∅ → T).
Proof. intro x ; destruct x. Qed.

(** Extend a variable mapping. *)
Definition env_ext V (T : Type) (env : V → T) (t : T) :
    inc V → T :=
  λ y, match y with
  | VZ => t
  | VS x => env x
  end.

Parameter F : Set.

Inductive
(** label identifiers *)
lid L : Set :=
| lid_b : L → lid L
| lid_f : var → lid L
.

Inductive
(** labels *)
lbl HV L : Set :=
| lbl_var : HV → lbl HV L
| lbl_id : lid L → lbl HV L
.

Inductive
(** effects *)
ef EV HV L : Set :=
| ef_var : EV → ef EV HV L
| ef_lbl : lbl HV L → ef EV HV L
.

(** effect sequences *)
Notation eff EV HV L := (list (ef EV HV L)).

Inductive
ty EV HV L : Set :=
| ty_unit : ty EV HV L
| ty_fun  : ty EV HV L → ty EV HV L → eff EV HV L → ty EV HV L
| ty_efun : ty (inc EV) HV L → ty EV HV L
| ty_hfun : F → ty EV (inc HV) L → ty EV HV L
.

Inductive
(** handlers *)
hd (EV HV V L : Set) : Set :=
| hd_var : HV → hd EV HV V L
| hd_def : F → lid L → tm EV HV (inc (inc V)) L → hd EV HV V L
with
(** terms *)
tm (EV HV V L : Set) : Set :=
| tm_val  : val EV HV V L → tm EV HV V L
| tm_app  : tm EV HV V L → tm EV HV V L → tm EV HV V L
| tm_eapp : tm EV HV V L → eff EV HV L → tm EV HV V L
| tm_happ : tm EV HV V L → hd EV HV V L → tm EV HV V L
| tm_let  : tm EV HV V L → tm EV HV (inc V) L → tm EV HV V L
| tm_Down : tm EV HV V (inc L) → tm EV HV V L
| tm_down : var → tm EV HV V L → tm EV HV V L
with
(** values *)
val (EV HV V L : Set) : Set :=
| val_unit : val EV HV V L
| val_var  : V → val EV HV V L
| val_fun  : tm EV HV (inc V) L → val EV HV V L
| val_efun : tm (inc EV) HV V L → val EV HV V L
| val_hfun : tm EV (inc HV) V L → val EV HV V L
| val_up   : hd EV HV V L → val EV HV V L
.

Inductive
(** Evaluation contexts *)
ktx EV HV V L : Set :=
| ktx_hole : ktx EV HV V L
| ktx_down : ktx EV HV V L → var → ktx EV HV V L
| ktx_let  : ktx EV HV V L → tm EV HV (inc V) L → ktx EV HV V L
| ktx_eapp : ktx EV HV V L → eff EV HV L → ktx EV HV V L
| ktx_happ : ktx EV HV V L → hd EV HV V L → ktx EV HV V L
| ktx_app1 : ktx EV HV V L → tm EV HV V L → ktx EV HV V L
| ktx_app2 : ktx EV HV V L → val EV HV V L → ktx EV HV V L
.

(** label-identifier environments *)
Notation XEnv EV LV := (env (ty EV LV ∅ * eff EV LV ∅)).

Inductive LEnv EV LV : Set → Type :=
| LEnv_empty : LEnv EV LV ∅
| LEnv_push  : ∀ L, LEnv EV LV L → ty EV LV L → eff EV LV L → LEnv EV LV (inc L)
.

Arguments LEnv_empty [EV LV].

Arguments lid_f [L].
Arguments lbl_var [HV L].
Arguments lbl_id [HV L].
Arguments ef_var  [EV HV L].
Arguments ef_lbl  [EV HV L].
Arguments ty_unit [EV HV L].
Arguments hd_var  [EV HV V L].
Arguments val_unit [EV HV V L].
Arguments val_var  [EV HV V L].
Arguments ktx_hole [EV HV V L].

(** * Notations. *)

Notation "𝟙" := ty_unit.
Notation "⇧" := val_up.
Notation "⬇" := tm_Down.
Notation "⇩" := tm_down.
Notation "λₜ" := val_fun.
Notation "λₑ" := val_efun.
Notation "λₕ" := val_hfun. 

(** Syntactic objects that do not contain any kind of free variables. *)
Notation lid0 := (lid ∅).
Notation lbl0 := (lid ∅ ∅).
Notation ef0 := (ef ∅ ∅ ∅).
Notation eff0 := (eff ∅ ∅ ∅).
Notation ty0 := (ty ∅ ∅ ∅).
Notation tm0 := (tm ∅ ∅ ∅ ∅).
Notation val0 := (val ∅ ∅ ∅ ∅).
Notation hd0 := (hd ∅ ∅ ∅ ∅).
Notation ktx0 := (ktx ∅ ∅ ∅ ∅).

(** Allows the implicit coercion from a [val] object to [tm]. *)
Coercion tm_val : val >-> tm.

(** Convert a [hd] to [lbl]. *)
Definition lbl_hd EV HV V L (h : hd EV HV V L) : lbl HV L :=
match h with
| hd_var p => lbl_var p
| hd_def _ id _ => lbl_id id
end
.

Parameter (Σ : F → ty0 * ty0).

(** A well-founded measure of types and effects *)

Fixpoint size_eff EV HV L (E : eff EV HV L) : nat :=
match E with
| [] => 0
| ε :: E => 1 + size_eff E
end.

Fixpoint size_ty EV HV L (T : ty EV HV L) : nat :=
match T with
| ty_unit => 0
| ty_fun T R E => 1 + size_ty T + size_ty R + size_eff E
| ty_efun T => 1 + size_ty T
| ty_hfun _ T => 1 + size_ty T
end.


Notation "x ∈ E" := (mem x E) (at level 39) : fset_scope.
Notation "x ∉ E" := (notin x E) (at level 39) : fset_scope.

Require Export Utf8 List Basics.
Export ListNotations.
Require Export CpdtTactics.
Require Export LibLN.
Open Scope program_scope.

Hint Extern 1 => match goal with
| [ |- ∀ x : ∅, _ ] => let x := fresh "x" in (intro x ; destruct x)
| [ x : ∅ |- _ ] => destruct x
| [ x : inc ?V |- _ ] => destruct x ; simpl ; crush
| [ |- context[ _ ∘ _ ] ] => unfold compose ; crush
end.
