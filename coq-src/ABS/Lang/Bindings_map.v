Require Import FinFun.
Require Import Lang.Syntax.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Section section_map_inc.
Context (A B : Set).

(** If we can change the representation of a variable from [A] to [B],
then we can change the representation of a variable from [inc A] to
[inc B]. *)
Definition map_inc (f : A → B) : inc A → inc B :=
  λ v, match v with
  | VZ    => VZ
  | VS v' => VS (f v')
  end.

Fixpoint map_incn (f : A → B) n {struct n} : incn n A → incn n B.
Proof.
destruct n as [ | n ] ; simpl ; intro x.
+ refine (f x).
+ rewrite incSn in *.
  destruct x as [ | x].
  - refine VZ.
  - refine (VS (map_incn f n x)).
Defined.

Hint Extern 0 => match goal with
| [ Inj : Injective ?f, H : ?f _ = ?f _ |- _ ] =>
  apply Inj in H ; subst
end.

Lemma map_inc_is_injective (f : A → B) :
Injective f → Injective (map_inc f).
Proof.
intros_all ; crush.
Qed.

End section_map_inc.

(** Change the variable representation type [L] to [L']. *)

Definition
  L_map_lid
    L L' (f : L → L') (id : lid L) : lid L' :=
  match id with
  | lid_f X => lid_f X
  | lid_b N => lid_b (f N)
  end
.

Definition
  L_map_lbl
    HV L L' (f : L → L') (ℓ : lbl HV L) : lbl HV L' :=
  match ℓ with
  | lbl_var z => lbl_var z
  | lbl_id id => lbl_id (L_map_lid f id)
  end
.

Definition
  L_map_ef
    EV HV L L' (f : L → L') (ε : ef EV HV L) : ef EV HV L' :=
  match ε with
  | ef_var z => ef_var z 
  | ef_lbl ℓ => ef_lbl (L_map_lbl f ℓ)
  end
.

Fixpoint
  L_map_eff
    EV HV L L' (f : L → L') (𝓔 : eff EV HV L) {struct 𝓔} : eff EV HV L' :=
  match 𝓔 with
  | [] => []
  | ε :: 𝓔' => (L_map_ef f ε) :: (L_map_eff f 𝓔')
  end
.

Fixpoint
  L_map_ty
    EV HV L L' (f : L → L') (T : ty EV HV L) {struct T} : ty EV HV L' :=
  match T with
  | 𝟙 => ty_unit
  | ty_fun T R 𝓔 => ty_fun (L_map_ty f T) (L_map_ty f R) (L_map_eff f 𝓔)
  | ty_efun T => ty_efun (L_map_ty f T)
  | ty_hfun 𝔽 T => ty_hfun 𝔽 (L_map_ty f T)
  end
.

Fixpoint
  L_map_hd
    EV HV V L L' (f : L → L')
    (h : hd EV HV V L) {struct h} : hd EV HV V L' :=
  match h with
  | hd_var p => hd_var p
  | hd_def 𝔽 i t => hd_def 𝔽 (L_map_lid f i) (L_map_tm f t)
  end
with
  L_map_val
    EV HV V L L' (f : L → L')
    (v : val EV HV V L) {struct v} : val EV HV V L' :=
  match v with
  | val_unit => val_unit
  | val_var x => val_var x
  | val_fun t => val_fun (L_map_tm f t)
  | val_efun t => val_efun (L_map_tm f t)
  | val_hfun t => val_hfun (L_map_tm f t)
  | ⇧ h => ⇧ (L_map_hd f h)
  end
with
  L_map_tm
    EV HV V L L' (f : L → L')
    (t : tm EV HV V L) {struct t} : tm EV HV V L' :=
  match t with
  | tm_val v => L_map_val f v
  | ⬇ t => ⬇ (L_map_tm (map_inc f) t)
  | ⇩ X t => ⇩ X (L_map_tm f t)
  | tm_let s t => tm_let (L_map_tm f s) (L_map_tm f t)
  | tm_app t s => tm_app (L_map_tm f t) (L_map_tm f s)
  | tm_eapp t 𝓔 => tm_eapp (L_map_tm f t) (L_map_eff f 𝓔)
  | tm_happ t h => tm_happ (L_map_tm f t) (L_map_hd f h)
  end
.

Fixpoint
  L_map_ktx
    EV HV V L L' (f : L → L')
    (K : ktx EV HV V L) {struct K} : ktx EV HV V L' :=
  match K with
  | ktx_hole => ktx_hole
  | ktx_down K X =>
      ktx_down (L_map_ktx f K) X
  | ktx_let K t =>
      ktx_let (L_map_ktx f K) (L_map_tm f t)
  | ktx_eapp K 𝓔 =>
      ktx_eapp (L_map_ktx f K) (L_map_eff f 𝓔)
  | ktx_happ K h =>
      ktx_happ (L_map_ktx f K) (L_map_hd f h)
  | ktx_app1 K t =>
      ktx_app1 (L_map_ktx f K) (L_map_tm f t)
  | ktx_app2 K v =>
      ktx_app2 (L_map_ktx f K) (L_map_val f v)
  end
.


(** Change the variable representation type [HV] to [HV']. *)

Definition
  HV_map_lbl
    HV HV' L (f : HV → HV') (ℓ : lbl HV L) : lbl HV' L :=
  match ℓ with
  | lbl_var z => lbl_var (f z)
  | lbl_id lid => lbl_id lid
  end
.

Definition
  HV_map_ef
    EV HV HV' L (f : HV → HV') (ε : ef EV HV L) : ef EV HV' L :=
  match ε with
  | ef_var z => ef_var z 
  | ef_lbl ℓ => ef_lbl (HV_map_lbl f ℓ)
  end
.

Fixpoint
  HV_map_eff
    EV HV HV' L (f : HV → HV') (𝓔 : eff EV HV L) {struct 𝓔} : eff EV HV' L :=
  match 𝓔 with
  | [] => []
  | ε :: 𝓔' => (HV_map_ef f ε) :: (HV_map_eff f 𝓔')
  end
.

Fixpoint
  HV_map_ty
    EV HV HV' L (f : HV → HV') (T : ty EV HV L) {struct T} : ty EV HV' L :=
  match T with
  | 𝟙 => ty_unit
  | ty_fun T R 𝓔 => ty_fun (HV_map_ty f T) (HV_map_ty f R) (HV_map_eff f 𝓔)
  | ty_efun T => ty_efun (HV_map_ty f T)
  | ty_hfun 𝔽 T => ty_hfun 𝔽 (HV_map_ty (map_inc f) T)
  end
.

Fixpoint
  HV_map_hd
    EV HV HV' V L (f : HV → HV')
    (h : hd EV HV V L) {struct h} : hd EV HV' V L :=
  match h with
  | hd_var p => hd_var (f p)
  | hd_def 𝔽 i t => hd_def 𝔽 i (HV_map_tm f t)
  end
with
  HV_map_val
    EV HV HV' V L (f : HV → HV')
    (v : val EV HV V L) {struct v} : val EV HV' V L :=
  match v with
  | val_unit => val_unit
  | val_var x => val_var x
  | val_fun t => val_fun (HV_map_tm f t)
  | val_efun t => val_efun (HV_map_tm f t)
  | val_hfun t => val_hfun (HV_map_tm (map_inc f) t)
  | ⇧ h => ⇧ (HV_map_hd f h)
  end
with
  HV_map_tm
    EV HV HV' V L (f : HV → HV')
    (t : tm EV HV V L) {struct t} : tm EV HV' V L :=
  match t with
  | tm_val v => HV_map_val f v
  | ⬇ t => ⬇ (HV_map_tm f t)
  | ⇩ X t => ⇩ X (HV_map_tm f t)
  | tm_let s t => tm_let (HV_map_tm f s) (HV_map_tm f t)
  | tm_app t s => tm_app (HV_map_tm f t) (HV_map_tm f s)
  | tm_eapp t 𝓔 => tm_eapp (HV_map_tm f t) (HV_map_eff f 𝓔)
  | tm_happ t h => tm_happ (HV_map_tm f t) (HV_map_hd f h)
  end
.

Fixpoint
  HV_map_ktx
    EV HV HV' V L (f : HV → HV')
    (K : ktx EV HV V L) {struct K} : ktx EV HV' V L :=
  match K with
  | ktx_hole => ktx_hole
  | ktx_down K X => ktx_down (HV_map_ktx f K) X
  | ktx_let K t => ktx_let (HV_map_ktx f K) (HV_map_tm f t)
  | ktx_eapp K 𝓔 =>
      ktx_eapp (HV_map_ktx f K) (HV_map_eff f 𝓔)
  | ktx_happ K h =>
      ktx_happ (HV_map_ktx f K) (HV_map_hd f h)
  | ktx_app1 K t =>
      ktx_app1 (HV_map_ktx f K) (HV_map_tm f t)
  | ktx_app2 K v =>
      ktx_app2 (HV_map_ktx f K) (HV_map_val f v)
  end
.


Definition HV_map_XEnv EV HV HV'
(f : HV → HV') (Ξ : XEnv EV HV) : XEnv EV HV' :=
  map (λ x,
    match x with
      (T, 𝓔) => (HV_map_ty f T, HV_map_eff f 𝓔)
    end
  ) Ξ.

Fixpoint HV_map_LEnv EV HV L HV'
(f : HV → HV') (Π : LEnv EV HV L) : LEnv EV HV' L :=
match Π with
| LEnv_empty => LEnv_empty
| LEnv_push Π T E => LEnv_push (HV_map_LEnv f Π) (HV_map_ty f T) (HV_map_eff f E)
end.


(** Change the variable representation type [EV] to [EV']. *)

Definition
  EV_map_ef
    EV EV' HV L (f : EV → EV') (ε : ef EV HV L) : ef EV' HV L :=
  match ε with
  | ef_var α => ef_var (f α)
  | ef_lbl ℓ => ef_lbl ℓ
  end
.

Fixpoint
  EV_map_eff
    EV EV' HV L (f : EV → EV') (𝓔 : eff EV HV L) {struct 𝓔} : eff EV' HV L :=
  match 𝓔 with
  | [] => []
  | ε :: 𝓔' => (EV_map_ef f ε) :: (EV_map_eff f 𝓔')
  end
.

Fixpoint
  EV_map_ty
    EV EV' HV L (f : EV → EV') (T : ty EV HV L) {struct T} : ty EV' HV L :=
  match T with
  | 𝟙 => ty_unit
  | ty_fun T R 𝓔 => ty_fun (EV_map_ty f T) (EV_map_ty f R) (EV_map_eff f 𝓔)
  | ty_efun T => ty_efun (EV_map_ty (map_inc f) T)
  | ty_hfun 𝔽 T => ty_hfun 𝔽 (EV_map_ty f T)
  end
.

Fixpoint
  EV_map_hd
    EV EV' HV V L (f : EV → EV')
    (h : hd EV HV V L) {struct h} : hd EV' HV V L :=
  match h with
  | hd_var p => hd_var p
  | hd_def 𝔽 i t => hd_def 𝔽 i (EV_map_tm f t)
  end
with
  EV_map_val
    EV EV' HV V L (f : EV → EV')
    (v : val EV HV V L) {struct v} : val EV' HV V L :=
  match v with
  | val_unit => val_unit
  | val_var x => val_var x
  | val_fun t => val_fun (EV_map_tm f t)
  | val_efun t => val_efun (EV_map_tm (map_inc f) t)
  | val_hfun t => val_hfun (EV_map_tm f t)
  | ⇧ h => ⇧ (EV_map_hd f h)
  end
with
  EV_map_tm
    EV EV' HV V L (f : EV → EV')
    (t : tm EV HV V L) {struct t} : tm EV' HV V L :=
  match t with
  | tm_val v => EV_map_val f v
  | ⬇ t => ⬇ (EV_map_tm f t)
  | ⇩ X t => ⇩ X (EV_map_tm f t)
  | tm_let s t => tm_let (EV_map_tm f s) (EV_map_tm f t)
  | tm_app t s => tm_app (EV_map_tm f t) (EV_map_tm f s)
  | tm_eapp t 𝓔 => tm_eapp (EV_map_tm f t) (EV_map_eff f 𝓔)
  | tm_happ t h => tm_happ (EV_map_tm f t) (EV_map_hd f h)
  end
.

Fixpoint
  EV_map_ktx
    EV EV' HV V L (f : EV → EV')
    (K : ktx EV HV V L) {struct K} : ktx EV' HV V L :=
  match K with
  | ktx_hole => ktx_hole
  | ktx_down K X => ktx_down (EV_map_ktx f K) X
  | ktx_let K t => ktx_let (EV_map_ktx f K) (EV_map_tm f t)
  | ktx_eapp K 𝓔 =>
      ktx_eapp (EV_map_ktx f K) (EV_map_eff f 𝓔)
  | ktx_happ K h =>
      ktx_happ (EV_map_ktx f K) (EV_map_hd f h)
  | ktx_app1 K t =>
      ktx_app1 (EV_map_ktx f K) (EV_map_tm f t)
  | ktx_app2 K v =>
      ktx_app2 (EV_map_ktx f K) (EV_map_val f v)
  end
.

Definition EV_map_XEnv EV EV' HV
(f : EV → EV') (Ξ : XEnv EV HV) : XEnv EV' HV :=
  map (λ x,
    match x with
      (T, 𝓔) => (EV_map_ty f T, EV_map_eff f 𝓔)
    end
  ) Ξ.

Fixpoint EV_map_LEnv EV LV L EV'
(f : EV → EV') (Π : LEnv EV LV L) : LEnv EV' LV L :=
match Π with
| LEnv_empty => LEnv_empty
| LEnv_push Π T E => LEnv_push (EV_map_LEnv f Π) (EV_map_ty f T) (EV_map_eff f E)
end.


(** Change the variable representation type [V] to [V']. *)

Fixpoint
  V_map_hd
    EV HV V V' L (f : V → V')
    (h : hd EV HV V L) {struct h} : hd EV HV V' L :=
  match h with
  | hd_var p => hd_var p
  | hd_def 𝔽 i t => hd_def 𝔽 i (V_map_tm (map_inc (map_inc f)) t)
  end
with
  V_map_val
    EV HV V V' L (f : V → V')
    (v : val EV HV V L) {struct v} : val EV HV V' L :=
  match v with
  | val_unit => val_unit
  | val_var x => val_var (f x)
  | val_fun t => val_fun (V_map_tm (map_inc f) t)
  | val_efun t => val_efun (V_map_tm f t)
  | val_hfun t => val_hfun (V_map_tm f t)
  | ⇧ h => ⇧ (V_map_hd f h)
  end
with
  V_map_tm
    EV HV V V' L (f : V → V')
    (t : tm EV HV V L) {struct t} : tm EV HV V' L :=
  match t with
  | tm_val v => V_map_val f v
  | ⬇ t => ⬇ (V_map_tm f t)
  | ⇩ X t => ⇩ X (V_map_tm f t)
  | tm_let s t => tm_let (V_map_tm f s) (V_map_tm (map_inc f) t)
  | tm_app t s => tm_app (V_map_tm f t) (V_map_tm f s)
  | tm_eapp t 𝓔 => tm_eapp (V_map_tm f t) 𝓔
  | tm_happ t h => tm_happ (V_map_tm f t) (V_map_hd f h)
  end
.

Fixpoint
  V_map_ktx
    EV HV V V' L (f : V → V')
    (K : ktx EV HV V L) {struct K} : ktx EV HV V' L :=
  match K with
  | ktx_hole => ktx_hole
  | ktx_down K X =>
      ktx_down (V_map_ktx f K) X
  | ktx_let K t =>
      ktx_let (V_map_ktx f K) (V_map_tm (map_inc f) t)
  | ktx_eapp K 𝓔 =>
      ktx_eapp (V_map_ktx f K) 𝓔
  | ktx_happ K h =>
      ktx_happ (V_map_ktx f K) (V_map_hd f h)
  | ktx_app1 K t =>
      ktx_app1 (V_map_ktx f K) (V_map_tm f t)
  | ktx_app2 K v =>
      ktx_app2 (V_map_ktx f K) (V_map_val f v)
  end
.


(** A syntactic object can be used in a context that binds one more variable. *)

Notation L_shift_lid := (L_map_lid (@VS _)).
Notation L_shift_lbl := (L_map_lbl (@VS _)).
Notation L_shift_ef := (L_map_ef (@VS _)).
Notation L_shift_eff := (L_map_eff (@VS _)).
Notation L_shift_ty := (L_map_ty (@VS _)).
Notation L_shift_hd := (L_map_hd (@VS _)).
Notation L_shift_val := (L_map_val (@VS _)).
Notation L_shift_tm := (L_map_tm (@VS _)).
Notation L_shift_ktx := (L_map_ktx (@VS _)).

Notation HV_shift_lbl := (HV_map_lbl (@VS _)).
Notation HV_shift_ef := (HV_map_ef (@VS _)).
Notation HV_shift_eff := (HV_map_eff (@VS _)).
Notation HV_shift_ty := (HV_map_ty (@VS _)).
Notation HV_shift_hd := (HV_map_hd (@VS _)).
Notation HV_shift_val := (HV_map_val (@VS _)).
Notation HV_shift_tm := (HV_map_tm (@VS _)).
Notation HV_shift_ktx := (HV_map_ktx (@VS _)).
Notation HV_shift_XEnv := (HV_map_XEnv (@VS _)).
Notation HV_shift_LEnv := (HV_map_LEnv (@VS _)).

Notation EV_shift_ef := (EV_map_ef (@VS _)).
Notation EV_shift_eff := (EV_map_eff (@VS _)).
Notation EV_shift_ty := (EV_map_ty (@VS _)).
Notation EV_shift_hd := (EV_map_hd (@VS _)).
Notation EV_shift_val := (EV_map_val (@VS _)).
Notation EV_shift_tm := (EV_map_tm (@VS _)).
Notation EV_shift_ktx := (EV_map_ktx (@VS _)).
Notation EV_shift_XEnv := (EV_map_XEnv (@VS _)).
Notation EV_shift_LEnv := (EV_map_LEnv (@VS _)).

Notation V_shift_hd := (V_map_hd (@VS _)).
Notation V_shift_val := (V_map_val (@VS _)).
Notation V_shift_tm := (V_map_tm (@VS _)).
Notation V_shift_ktx := (V_map_ktx (@VS _)).

(** Syntactic objects that do not contain free variables can be used
in any context that binds free variables. *)

Notation L_open_lid := (L_map_lid ∅→).
Notation L_open_ty := (L_map_ty ∅→).
Notation L_open_ef := (L_map_ef ∅→).
Notation L_open_eff := (L_map_eff ∅→).
Notation L_open_lbl := (L_map_lbl ∅→).
Notation L_open_hd := (L_map_hd ∅→).
Notation L_open_val := (L_map_val ∅→).
Notation L_open_tm := (L_map_tm ∅→).
Notation L_open_ktx := (L_map_ktx ∅→).

Notation HV_open_ty := (HV_map_ty ∅→).
Notation HV_open_ef := (HV_map_ef ∅→).
Notation HV_open_eff := (HV_map_eff ∅→).
Notation HV_open_lbl := (HV_map_lbl ∅→).
Notation HV_open_hd := (HV_map_hd ∅→).
Notation HV_open_val := (HV_map_val ∅→).
Notation HV_open_tm := (HV_map_tm ∅→).
Notation HV_open_ktx := (HV_map_ktx ∅→).
Notation HV_open_XEnv := (HV_map_XEnv ∅→).
Notation HV_open_LEnv := (HV_map_LEnv ∅→).

Notation EV_open_ty := (EV_map_ty ∅→).
Notation EV_open_ef := (EV_map_ef ∅→).
Notation EV_open_eff := (EV_map_eff ∅→).
Notation EV_open_hd := (EV_map_hd ∅→).
Notation EV_open_val := (EV_map_val ∅→).
Notation EV_open_tm := (EV_map_tm ∅→).
Notation EV_open_ktx := (EV_map_ktx ∅→).
Notation EV_open_XEnv := (EV_map_XEnv ∅→).
Notation EV_open_LEnv := (EV_map_LEnv ∅→).

Notation V_open_hd := (V_map_hd ∅→).
Notation V_open_val := (V_map_val ∅→).
Notation V_open_tm := (V_map_tm ∅→).
Notation V_open_ktx := (V_map_ktx ∅→).
