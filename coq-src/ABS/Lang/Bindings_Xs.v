Require Import Lang.Syntax.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

(** Extract free label identifiers *)

Definition Xs_lid L (ι : lid L) :=
match ι with
| lid_f X => \{ X }
| _ => \{}
end.

Definition Xs_lbl HV L (ℓ : lbl HV L) :=
match ℓ with
| lbl_id ι => Xs_lid ι
| _ => \{}
end.

Definition Xs_ef EV HV L (ε : ef EV HV L ) :=
match ε with
| ef_lbl ℓ => Xs_lbl ℓ
| _ => \{}
end.

Fixpoint Xs_eff EV HV L (𝓔 : eff EV HV L) :=
match 𝓔 with
| ε :: 𝓔 => Xs_ef ε \u Xs_eff 𝓔
| _ => \{}
end.

Fixpoint
Xs_ty EV HV L (T : ty EV HV L) :=
  match T with
  | 𝟙 => \{}
  | ty_fun T R E => Xs_ty T \u Xs_ty R \u Xs_eff E
  | ty_efun T => Xs_ty T
  | ty_hfun 𝔽 T => Xs_ty T
  end
.

Fixpoint
  Xs_hd EV HV V L (m : hd EV HV V L) :=
  match m with
  | hd_var p => \{}
  | hd_def _ ι t => Xs_lid ι \u Xs_tm t
  end
with
  Xs_val EV HV V L (v : val EV HV V L) :=
  match v with
  | val_unit => \{}
  | val_var x => \{}
  | val_fun t => Xs_tm t
  | val_efun t => Xs_tm t
  | val_hfun t => Xs_tm t
  | val_up h => Xs_hd h
  end
with
  Xs_tm EV HV V L (t : tm EV HV V L) :=
  match t with
  | tm_val v => Xs_val v
  | ⬇ t => Xs_tm t
  | ⇩ X t => Xs_tm t \u \{X}
  | tm_let s t => Xs_tm s \u Xs_tm t
  | tm_eapp t 𝓔 => Xs_tm t \u Xs_eff 𝓔
  | tm_happ t h => Xs_tm t \u Xs_hd h
  | tm_app t s => Xs_tm t \u Xs_tm s
  end
.

Fixpoint Xs_ktx EV HV V L (K : ktx EV HV V L) :=
match K with
| ktx_hole => \{}
| ktx_let J t => Xs_ktx J \u Xs_tm t
| ktx_eapp J 𝓔 => Xs_ktx J \u Xs_eff 𝓔
| ktx_happ J h => Xs_ktx J \u Xs_hd h
| ktx_app1 J t => Xs_ktx J \u Xs_tm t
| ktx_app2 J v => Xs_ktx J \u Xs_val v
| ktx_down J X => Xs_ktx J \u \{X}
end.