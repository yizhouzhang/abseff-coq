Require Import Lang.Syntax Lang.Bindings_map.
Require Import FinFun.
Set Implicit Arguments.

Implicit Types (EV HV V L : Set).

Section section_lift_inc.
Context (EV EV' HV HV' V V' L L' : Set).

(** If we have a substitution function of form [EV → eff EV' HV L],
then we can turn it into one of form [inc EV → eff (inc EV') HV L]. *)
Definition EV_lift_inc (f : EV → eff EV' HV L) :
    inc EV → eff (inc EV') HV L :=
  λ α, match α with
  | VZ   => [ ef_var VZ ]
  | VS β => EV_shift_eff (f β)
  end.

Definition HV_lift_inc (f : HV → hd EV HV' V L) :
    inc HV →  hd EV (inc HV') V L :=
  λ α, match α with
  | VZ   => hd_var VZ
  | VS β => HV_shift_hd (f β)
  end.

Definition L_lift_inc (f : L → lid L') :
    inc L → lid (inc L') :=
  λ α, match α with
  | VZ   => lid_b VZ
  | VS β => L_shift_lid (f β)
  end.

Definition V_lift_inc (f : V → val EV HV V' L) :
    inc V → val EV HV (inc V') L :=
  λ x, match x with
  | VZ   => val_var VZ
  | VS β => V_shift_val (f β)
  end.

End section_lift_inc.


(** Apply the substitution function [f : EV → eff EV' HV L] *)

Definition
EV_bind_ef
EV EV' HV L (f : EV → eff EV' HV L) (ε : ef EV HV L) :
eff EV' HV L :=
  match ε with
  | ef_var α => f α
  | ef_lbl ℓ => [ ef_lbl ℓ ]
  end
.

Fixpoint
EV_bind_eff
EV EV' HV L (f : EV → eff EV' HV L) (𝓔 : eff EV HV L) {struct 𝓔} :
eff EV' HV L :=
  match 𝓔 with
  | [] => []
  | ε :: 𝓔' => (EV_bind_ef f ε) ++ (EV_bind_eff f 𝓔')
  end
.

Fixpoint
EV_bind_ty
EV EV' HV L (f : EV → eff EV' HV L) (T : ty EV HV L) {struct T} : ty EV' HV L :=
  match T with
  | 𝟙 => ty_unit
  | ty_fun T R 𝓔 =>
    ty_fun (EV_bind_ty f T) (EV_bind_ty f R) (EV_bind_eff f 𝓔)
  | ty_efun T =>
    ty_efun (EV_bind_ty (EV_lift_inc f) T)
  | ty_hfun 𝔽 T =>
    ty_hfun 𝔽 (EV_bind_ty (HV_shift_eff ∘ f) T)
  end
.

Fixpoint
EV_bind_hd
EV EV' HV V L (f : EV → eff EV' HV L)
(h : hd EV HV V L) {struct h} : hd EV' HV V L :=
  match h with
  | hd_var p => hd_var p
  | hd_def 𝔽 i t => hd_def 𝔽 i (EV_bind_tm f t)
  end
with
EV_bind_val
EV EV' HV V L (f : EV → eff EV' HV L)
(v : val EV HV V L) {struct v} : val EV' HV V L :=
  match v with
  | val_unit => val_unit
  | val_var x => val_var x
  | val_fun t => val_fun (EV_bind_tm f t)
  | val_efun t => val_efun (EV_bind_tm (EV_lift_inc f) t)
  | val_hfun t => val_hfun (EV_bind_tm (HV_shift_eff ∘ f) t)
  | ⇧ h => ⇧ (EV_bind_hd f h)
  end
with
EV_bind_tm
EV EV' HV V L (f : EV → eff EV' HV L)
(t : tm EV HV V L) {struct t} : tm EV' HV V L :=
  match t with
  | tm_val v => EV_bind_val f v
  | ⬇ t => ⬇ (EV_bind_tm (L_shift_eff ∘ f) t)
  | ⇩ X t => ⇩ X (EV_bind_tm f t)
  | tm_let s t => tm_let (EV_bind_tm f s) (EV_bind_tm f t)
  | tm_app t s => tm_app (EV_bind_tm f t) (EV_bind_tm f s)
  | tm_eapp t 𝓔 => tm_eapp (EV_bind_tm f t) (EV_bind_eff f 𝓔)
  | tm_happ t h => tm_happ (EV_bind_tm f t) (EV_bind_hd f h)
  end
.

Fixpoint
EV_bind_ktx
EV EV' HV V L (f : EV → eff EV' HV L)
(K : ktx EV HV V L) {struct K} : ktx EV' HV V L :=
  match K with
  | ktx_hole => ktx_hole
  | ktx_down K X =>
      ktx_down (EV_bind_ktx f K) X
  | ktx_let K t =>
      ktx_let (EV_bind_ktx f K) (EV_bind_tm f t)
  | ktx_eapp K 𝓔 =>
      ktx_eapp (EV_bind_ktx f K) (EV_bind_eff f 𝓔)
  | ktx_happ K h =>
      ktx_happ (EV_bind_ktx f K) (EV_bind_hd f h)
  | ktx_app1 K t =>
      ktx_app1 (EV_bind_ktx f K) (EV_bind_tm f t)
  | ktx_app2 K v =>
      ktx_app2 (EV_bind_ktx f K) (EV_bind_val f v)
  end
.


(** Apply the substitution function [f : HV → hd EV HV' V L] *)

Definition
HV_bind_lbl
EV HV HV' V L (f : HV → hd EV HV' V L) (ℓ : lbl HV L) : lbl HV' L :=
  match ℓ with
  | lbl_var α => lbl_hd (f α)
  | lbl_id id => lbl_id id
  end
.

Definition
HV_bind_ef
EV HV HV' V L (f : HV → hd EV HV' V L) (ε : ef EV HV L) : ef EV HV' L :=
  match ε with
  | ef_var z => ef_var z
  | ef_lbl ℓ => ef_lbl (HV_bind_lbl f ℓ)
  end
.

Fixpoint
HV_bind_eff
EV HV HV' V L (f : HV → hd EV HV' V L) (𝓔 : eff EV HV L) {struct 𝓔} : eff EV HV' L :=
  match 𝓔 with
  | [] => []
  | ε :: 𝓔' => (HV_bind_ef f ε) :: (HV_bind_eff f 𝓔')
  end
.

Fixpoint
  HV_bind_ty
    EV HV HV' V L (f : HV → hd EV HV' V L) (T : ty EV HV L) {struct T} : ty EV HV' L :=
  match T with
  | 𝟙 => ty_unit
  | ty_fun T R 𝓔 =>
    ty_fun (HV_bind_ty f T) (HV_bind_ty f R) (HV_bind_eff f 𝓔)
  | ty_efun T =>
    ty_efun (HV_bind_ty (EV_shift_hd ∘ f) T)
  | ty_hfun 𝔽 T =>
    ty_hfun 𝔽 (HV_bind_ty (HV_lift_inc f) T)
  end
.

Fixpoint
  HV_bind_hd
    EV HV HV' V L (f : HV → hd EV HV' V L)
    (h : hd EV HV V L) {struct h} : hd EV HV' V L :=
  match h with
  | hd_var p => f p
  | hd_def 𝔽 i t => hd_def 𝔽 i (HV_bind_tm (V_shift_hd ∘ V_shift_hd ∘ f) t)
  end
with
  HV_bind_val
    EV HV HV' V L (f : HV → hd EV HV' V L)
    (v : val EV HV V L) {struct v} : val EV HV' V L :=
  match v with
  | val_unit => val_unit
  | val_var x => val_var x
  | val_fun t => val_fun (HV_bind_tm (V_shift_hd ∘ f) t)
  | val_efun t => val_efun (HV_bind_tm (EV_shift_hd ∘ f) t)
  | val_hfun t => val_hfun (HV_bind_tm (HV_lift_inc f) t)
  | ⇧ h => ⇧ (HV_bind_hd f h)
  end
with
  HV_bind_tm
    EV HV HV' V L (f : HV → hd EV HV' V L)
    (t : tm EV HV V L) {struct t} : tm EV HV' V L :=
  match t with
  | tm_val v =>
    HV_bind_val f v
  | ⬇ t => ⬇ (HV_bind_tm (L_shift_hd ∘ f) t)
  | ⇩ X t => ⇩ X (HV_bind_tm f t)
  | tm_let s t =>
    tm_let (HV_bind_tm f s) (HV_bind_tm (V_shift_hd ∘ f) t)
  | tm_app t s =>
    tm_app (HV_bind_tm f t) (HV_bind_tm f s)
  | tm_eapp t 𝓔 =>
    tm_eapp (HV_bind_tm f t) (HV_bind_eff f 𝓔)
  | tm_happ t h =>
    tm_happ (HV_bind_tm f t) (HV_bind_hd f h)
  end
.

Fixpoint
  HV_bind_ktx
    EV HV HV' V L (f : HV → hd EV HV' V L)
    (K : ktx EV HV V L) {struct K} : ktx EV HV' V L :=
  match K with
  | ktx_hole => ktx_hole
  | ktx_down K X =>
      ktx_down (HV_bind_ktx f K) X
  | ktx_let K t =>
      ktx_let (HV_bind_ktx f K) (HV_bind_tm (V_shift_hd ∘ f) t)
  | ktx_eapp K 𝓔 =>
      ktx_eapp (HV_bind_ktx f K) (HV_bind_eff f 𝓔)
  | ktx_happ K h =>
      ktx_happ (HV_bind_ktx f K) (HV_bind_hd f h)
  | ktx_app1 K t =>
      ktx_app1 (HV_bind_ktx f K) (HV_bind_tm f t)
  | ktx_app2 K v =>
      ktx_app2 (HV_bind_ktx f K) (HV_bind_val f v)
  end
.


(** Apply the substitution function [f : V → val EV HV V' L] *)

Fixpoint
  V_bind_hd
    EV HV V V' L (f : V → val EV HV V' L)
    (h : hd EV HV V L) {struct h} : hd EV HV V' L :=
  match h with
  | hd_var p => hd_var p
  | hd_def 𝔽 i t => hd_def 𝔽 i (V_bind_tm (V_lift_inc (V_lift_inc f)) t)
  end
with
  V_bind_val
    EV HV V V' L (f : V → val EV HV V' L)
    (v : val EV HV V L) {struct v} : val EV HV V' L :=
  match v with
  | val_unit => val_unit
  | val_var x => f x
  | val_fun t => val_fun (V_bind_tm (V_lift_inc f) t)
  | val_efun t => val_efun (V_bind_tm (EV_shift_val ∘ f) t)
  | val_hfun t => val_hfun (V_bind_tm (HV_shift_val ∘ f) t)
  | ⇧ h => ⇧ (V_bind_hd f h)
  end
with
  V_bind_tm
    EV HV V V' L (f : V → val EV HV V' L)
    (t : tm EV HV V L) {struct t} : tm EV HV V' L :=
  match t with
  | tm_val v => V_bind_val f v
  | ⬇ t => ⬇ (V_bind_tm (L_shift_val ∘ f) t)
  | ⇩ X t => ⇩ X (V_bind_tm f t)
  | tm_let s t => tm_let (V_bind_tm f s) (V_bind_tm (V_lift_inc f) t)
  | tm_app t s => tm_app (V_bind_tm f t) (V_bind_tm f s)
  | tm_eapp t 𝓔 => tm_eapp (V_bind_tm f t) 𝓔
  | tm_happ t h => tm_happ (V_bind_tm f t) (V_bind_hd f h)
  end
.

Fixpoint
  V_bind_ktx
    EV HV V V' L (f : V → val EV HV V' L)
    (K : ktx EV HV V L) {struct K} : ktx EV HV V' L :=
  match K with
  | ktx_hole => ktx_hole
  | ktx_down K X =>
      ktx_down (V_bind_ktx f K) X
  | ktx_let K t =>
      ktx_let (V_bind_ktx f K) (V_bind_tm (V_lift_inc f) t)
  | ktx_eapp K 𝓔 =>
      ktx_eapp (V_bind_ktx f K) 𝓔
  | ktx_happ K h =>
      ktx_happ (V_bind_ktx f K) (V_bind_hd f h)
  | ktx_app1 K t =>
      ktx_app1 (V_bind_ktx f K) (V_bind_tm f t)
  | ktx_app2 K v =>
      ktx_app2 (V_bind_ktx f K) (V_bind_val f v)
  end
.


(** Apply the substitution function [f : L → lid L'] *)

Definition
L_bind_lid
L L' (f : L → lid L') (ID : lid L) : lid L' :=
  match ID with
  | lid_b x => f x
  | lid_f X => lid_f X
  end
.

Definition
L_bind_lbl
HV L L' (f : L → lid L') (ℓ : lbl HV L) : lbl HV L' :=
  match ℓ with
  | lbl_var α => lbl_var α
  | lbl_id id => lbl_id (L_bind_lid f id)
  end
.

Definition
L_bind_ef
EV HV L L' (f : L → lid L') (ε : ef EV HV L) : ef EV HV L' :=
  match ε with
  | ef_var z => ef_var z
  | ef_lbl ℓ => ef_lbl (L_bind_lbl f ℓ)
  end
.

Fixpoint
L_bind_eff
EV HV L L' (f : L → lid L') (𝓔 : eff EV HV L) {struct 𝓔} : eff EV HV L' :=
  match 𝓔 with
  | [] => []
  | ε :: 𝓔' => (L_bind_ef f ε) :: (L_bind_eff f 𝓔')
  end
.

Fixpoint
  L_bind_ty
    EV HV L L' (f : L → lid L') (T : ty EV HV L) {struct T} : ty EV HV L' :=
  match T with
  | 𝟙 => ty_unit
  | ty_fun T R 𝓔 => ty_fun (L_bind_ty f T) (L_bind_ty f R) (L_bind_eff f 𝓔)
  | ty_efun T => ty_efun (L_bind_ty f T)
  | ty_hfun 𝔽 T => ty_hfun 𝔽 (L_bind_ty f T)
  end
.

Fixpoint
  L_bind_hd
    EV HV V L L' (f : L → lid L')
    (h : hd EV HV V L) {struct h} : hd EV HV V L' :=
  match h with
  | hd_var p => hd_var p
  | hd_def 𝔽 i t => hd_def 𝔽 (L_bind_lid f i) (L_bind_tm f t)
  end
with
  L_bind_val
    EV HV V L L' (f : L → lid L')
    (v : val EV HV V L) {struct v} : val EV HV V L' :=
  match v with
  | val_unit => val_unit
  | val_var x => val_var x
  | val_fun t => val_fun (L_bind_tm f t)
  | val_efun t => val_efun (L_bind_tm f t)
  | val_hfun t => val_hfun (L_bind_tm f t)
  | ⇧ h => ⇧ (L_bind_hd f h)
  end
with
  L_bind_tm
    EV HV V L L' (f : L → lid L')
    (t : tm EV HV V L) {struct t} : tm EV HV V L' :=
  match t with
  | tm_val v => L_bind_val f v
  | ⬇ t => ⬇ (L_bind_tm (L_lift_inc f) t)
  | ⇩ X t => ⇩ X (L_bind_tm f t)
  | tm_let s t => tm_let (L_bind_tm f s) (L_bind_tm f t)
  | tm_app t s => tm_app (L_bind_tm f t) (L_bind_tm f s)
  | tm_eapp t 𝓔 => tm_eapp (L_bind_tm f t) (L_bind_eff f 𝓔)
  | tm_happ t h => tm_happ (L_bind_tm f t) (L_bind_hd f h)
  end
.

Fixpoint
  L_bind_ktx
    EV HV V L L' (f : L → lid L')
    (K : ktx EV HV V L) {struct K} : ktx EV HV V L' :=
  match K with
  | ktx_hole => ktx_hole
  | ktx_down K X =>
      ktx_down (L_bind_ktx f K) X
  | ktx_let K t =>
      ktx_let (L_bind_ktx f K) (L_bind_tm f t)
  | ktx_eapp K 𝓔 =>
      ktx_eapp (L_bind_ktx f K) (L_bind_eff f 𝓔)
  | ktx_happ K h =>
      ktx_happ (L_bind_ktx f K) (L_bind_hd f h)
  | ktx_app1 K t =>
      ktx_app1 (L_bind_ktx f K) (L_bind_tm f t)
  | ktx_app2 K v =>
      ktx_app2 (L_bind_ktx f K) (L_bind_val f v)
  end
.

Definition EV_bind_XEnv EV EV' HV
(f : EV → eff EV' HV ∅) (Ξ : XEnv EV HV) : XEnv EV' HV :=
  map (λ x,
    match x with
      (T, 𝓔) => (EV_bind_ty f T, EV_bind_eff f 𝓔)
    end
  ) Ξ.

Definition HV_bind_XEnv EV HV HV' V
(f : HV → hd EV HV' V ∅) (Ξ : XEnv EV HV) : XEnv EV HV' :=
  map (λ x,
    match x with
      (T, 𝓔) => (HV_bind_ty f T, HV_bind_eff f 𝓔)
    end
  ) Ξ.


(** Construct substitution functions for one (or two) free variable(s). *)

Section section_substfun.
Context {EV HV V L : Set}.

Definition EV_substfun (𝓔 : eff EV HV L) : inc EV → eff EV HV L :=
  λ α, match α with
  | VZ   => 𝓔
  | VS β => [ ef_var β ]
  end.

Definition HV_substfun (h : hd EV HV V L) : inc HV → hd EV HV V L :=
  λ α, match α with
  | VZ   => h
  | VS β => hd_var β
  end.

Definition L_substfun (ID : lid L) : inc L → lid L :=
  λ α, match α with
  | VZ   => ID
  | VS β => lid_b β
  end.

Definition V_substfun (v : val EV HV V L) : inc V → val EV HV V L :=
  λ x, match x with
  | VZ   => v
  | VS y => val_var y
  end.

(** Innermost bound variable is substituted by [t2]. *)
Definition V2_substfun (t1 t2 : val EV HV V L) :
    inc (inc V) → val EV HV V L :=
  λ x, match x with
  | VZ        => t2
  | VS VZ     => t1
  | VS (VS y) => val_var y
  end.

Lemma L_substfun_lid_f_injective X : Injective (L_substfun (lid_f X)).
Proof.
intros x y H.
destruct x as [ | x ], y as [ | y ] ; simpl in H ; try inversion H ; crush.
Qed.

End section_substfun.

Notation EV_subst_ty 𝓔 := (EV_bind_ty (EV_substfun 𝓔)).
Notation EV_subst_ef 𝓔 := (EV_bind_ef (EV_substfun 𝓔)).
Notation EV_subst_eff 𝓔 := (EV_bind_eff (EV_substfun 𝓔)).
Notation EV_subst_hd 𝓔 := (EV_bind_hd (EV_substfun 𝓔)).
Notation EV_subst_val 𝓔 := (EV_bind_val (EV_substfun 𝓔)).
Notation EV_subst_tm 𝓔 := (EV_bind_tm (EV_substfun 𝓔)).
Notation EV_subst_ktx 𝓔 := (EV_bind_ktx (EV_substfun 𝓔)).
Notation EV_subst_XEnv 𝓔 := (EV_bind_XEnv (EV_substfun 𝓔)).

Notation HV_subst_ty h := (HV_bind_ty (HV_substfun h)).
Notation HV_subst_ef h := (HV_bind_ef (HV_substfun h)).
Notation HV_subst_eff h := (HV_bind_eff (HV_substfun h)).
Notation HV_subst_lbl h := (HV_bind_lbl (HV_substfun h)).
Notation HV_subst_hd h := (HV_bind_hd (HV_substfun h)).
Notation HV_subst_val h := (HV_bind_val (HV_substfun h)).
Notation HV_subst_tm h := (HV_bind_tm (HV_substfun h)).
Notation HV_subst_ktx h := (HV_bind_ktx (HV_substfun h)).
Notation HV_subst_XEnv h := (HV_bind_XEnv (HV_substfun h)).

Notation L_subst_lid ι := (L_bind_lid (L_substfun ι)).
Notation L_subst_ty ι := (L_bind_ty (L_substfun ι)).
Notation L_subst_ef ι := (L_bind_ef (L_substfun ι)).
Notation L_subst_eff ι := (L_bind_eff (L_substfun ι)).
Notation L_subst_lbl ι := (L_bind_lbl (L_substfun ι)).
Notation L_subst_hd ι := (L_bind_hd (L_substfun ι)).
Notation L_subst_val ι := (L_bind_val (L_substfun ι)).
Notation L_subst_ktx ι := (L_bind_ktx (L_substfun ι)).
Notation L_subst_tm ι := (L_bind_tm (L_substfun ι)).

Notation V_subst_hd v := (V_bind_hd (V_substfun v)).
Notation V_subst_val v := (V_bind_val (V_substfun v)).
Notation V_subst_tm v := (V_bind_tm (V_substfun v)).
Notation V2_subst_tm v u := (V_bind_tm (V2_substfun v u)).
Notation V_subst_ktx v := (V_bind_ktx (V_substfun v)).
