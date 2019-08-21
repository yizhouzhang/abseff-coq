Require Import ABS.Lang.Syntax.
Require Import ABS.Lang.Bindings.
Require Import ABS.Lang.BindingsFacts.
Require Import ABS.Lang.Operational.
Require Import ABS.Lang.Sim.
Require Import ABS.Util.Postfix.
Require Import ABS.Util.FromList.
Require Import ABS.Util.Subset.
Require TLC.LibList.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Local Hint Constructors lid_sim lbl_sim ef_sim eff_sim ty_sim.
Local Hint Constructors hd_sim val_sim tm_sim ktx_sim.

(** [xx_sym] is reflexivie *)
Section section_sim_refl.

Import TLC.LibList.

Hint Rewrite in_singleton.
Hint Extern 1 => match goal with
| [ H : _ \u _ \c _ |- _ ] => apply union_subset_inv in H ; destruct H
| [ H : \{ ?a } \c ?A |- _ ] => assert (a ∈ A) ; [ specialize (H a) ; crush | ]
end.

Lemma var_sim_refl ξ X (H : X ∈ from_list ξ) :
var_sim ξ ξ X X.
Proof.
rewrite from_list_spec in H.
apply mem_Nth in H.
destruct H as [n ?].
exists n ; crush.
Qed.

Hint Resolve var_sim_refl.

Lemma lid_sim_refl L ξ (ι : lid L) (H : Xs_lid ι \c from_list ξ) :
lid_sim ξ ξ ι ι.
Proof.
destruct ι ; crush.
Qed.

Hint Resolve lid_sim_refl.

Lemma
lbl_sim_refl HV L ξ (ℓ : lbl HV L) (H : Xs_lbl ℓ \c from_list ξ) :
lbl_sim ξ ξ ℓ ℓ.
Proof.
destruct ℓ ; crush.
Qed.

Hint Resolve lbl_sim_refl.

Lemma
ef_sim_refl EV HV L ξ (ε : ef EV HV L) (H : Xs_ef ε \c from_list ξ) :
ef_sim ξ ξ ε ε.
Proof.
destruct ε ; crush.
Qed.

Hint Resolve ef_sim_refl.
Hint Extern 1 => match goal with
| [ H : _ \u _ \c _ |- _ ] => apply union_subset_inv in H ; destruct H
end.

Lemma
eff_sim_refl
EV HV L ξ (𝓔 : eff EV HV L) (H : Xs_eff 𝓔 \c from_list ξ) :
eff_sim ξ ξ 𝓔 𝓔.
Proof.
induction 𝓔 ; crush.
Qed.

Hint Resolve eff_sim_refl.

Fixpoint
ty_sim_refl
EV HV L ξ (T : ty EV HV L) (H : Xs_ty T \c from_list ξ) {struct T} :
ty_sim ξ ξ T T
.
Proof.
destruct T ; constructor ; crush.
Qed.

Hint Resolve ty_sim_refl.

Fixpoint
hd_sim_refl
EV HV V L ξ (m : hd EV HV V L) (H : Xs_hd m \c from_list ξ) {struct m} :
hd_sim ξ ξ m m
with
val_sim_refl
EV HV V L ξ (v : val EV HV V L) (H : Xs_val v \c from_list ξ) {struct v} :
val_sim ξ ξ v v
with
tm_sim_refl
EV HV V L ξ (t : tm EV HV V L) (H : Xs_tm t \c from_list ξ) {struct t} :
tm_sim ξ ξ t t
.
Proof.
+ destruct m ; constructor ; crush.
+ destruct v ; constructor ; crush.
+ destruct t ; constructor ; crush.
Qed.

End section_sim_refl.


(** [xx_sym] is symmetric *)
Section section_sim_sym.

Lemma var_sim_sym ξ ξ' (X X' : var) (H : var_sim ξ ξ' X X') :
var_sim ξ' ξ X' X.
Proof.
destruct H as [n ?].
exists n ; crush.
Qed.

Hint Resolve var_sim_sym.

Lemma lid_sim_sym L ξ ξ' (ι ι' : lid L) (H : lid_sim ξ ξ' ι ι') :
lid_sim ξ' ξ ι' ι.
Proof.
destruct H ; crush.
Qed.

Hint Resolve lid_sim_sym.

Lemma
lbl_sim_sym HV L ξ ξ' (ℓ ℓ' : lbl HV L) (H : lbl_sim ξ ξ' ℓ ℓ') :
lbl_sim ξ' ξ ℓ' ℓ.
Proof.
destruct H ; crush.
Qed.

Hint Resolve lbl_sim_sym.

Lemma
ef_sim_sym EV HV L ξ ξ' (ε ε' : ef EV HV L) (H : ef_sim ξ ξ' ε ε') :
ef_sim ξ' ξ ε' ε.
Proof.
destruct H ; crush.
Qed.

Hint Resolve ef_sim_sym.

Lemma
eff_sim_sym
EV HV L ξ ξ' (𝓔 𝓔' : eff EV HV L) (H : eff_sim ξ ξ' 𝓔 𝓔') :
eff_sim ξ' ξ 𝓔' 𝓔.
Proof.
induction H ; crush.
Qed.

Hint Resolve eff_sim_sym.

Fixpoint
ty_sim_sym
EV HV L ξ ξ' (T T' : ty EV HV L) (H : ty_sim ξ ξ' T T') :
ty_sim ξ' ξ T' T
.
Proof.
destruct H ; constructor ; crush.
Qed.

Hint Resolve ty_sim_sym.

Fixpoint
hd_sim_sym
EV HV V L ξ ξ' (m m' : hd EV HV V L) (H : hd_sim ξ ξ' m m') :
hd_sim ξ' ξ m' m
with
val_sim_sym
EV HV V L ξ ξ' (v v' : val EV HV V L) (H : val_sim ξ ξ' v v') :
val_sim ξ' ξ v' v
with
tm_sim_sym
EV HV V L ξ ξ' (t t' : tm EV HV V L) (H : tm_sim ξ ξ' t t') :
tm_sim ξ' ξ t' t
.
Proof.
+ destruct H ; constructor ; crush.
+ destruct H ; constructor ; crush.
+ destruct H ; constructor ; crush.
Qed.

End section_sim_sym.

Section section_sim_and_bindings.

Lemma
L_map_lid_sim
L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
(ι ι' : lid L) (H : lid_sim ξ ξ' ι ι') :
lid_sim ξ ξ' (L_map_lid f ι) (L_map_lid f' ι')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve L_map_lid_sim.

Lemma
L_map_lbl_sim
HV L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
(ℓ ℓ' : lbl HV L) (H : lbl_sim ξ ξ' ℓ ℓ') :
lbl_sim ξ ξ' (L_map_lbl f ℓ) (L_map_lbl f' ℓ')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve L_map_lbl_sim.

Lemma
L_map_ef_sim
EV HV L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
(ε ε' : ef EV HV L) (H : ef_sim ξ ξ' ε ε') :
ef_sim ξ ξ' (L_map_ef f ε) (L_map_ef f' ε')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve L_map_ef_sim.

Fixpoint
L_map_eff_sim
EV HV L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
(𝓔 𝓔' : eff EV HV L) (H : eff_sim ξ ξ' 𝓔 𝓔') :
eff_sim ξ ξ' (L_map_eff f 𝓔) (L_map_eff f' 𝓔')
.
Proof.
induction H ; simpl ; crush.
Qed.

Hint Resolve L_map_eff_sim.

Fixpoint
L_map_ty_sim
EV HV L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
(T T' : ty EV HV L) (H : ty_sim ξ ξ' T T') :
ty_sim ξ ξ' (L_map_ty f T) (L_map_ty f' T')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve L_map_ty_sim.

Fixpoint
L_map_hd_sim
EV HV V L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
(m m' : hd EV HV V L) (H : hd_sim ξ ξ' m m') :
hd_sim ξ ξ' (L_map_hd f m) (L_map_hd f' m')
with
L_map_val_sim
EV HV V L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
(v v' : val EV HV V L) (H : val_sim ξ ξ' v v') :
val_sim ξ ξ' (L_map_val f v) (L_map_val f' v')
with
L_map_tm_sim
EV HV V L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
(t t' : tm EV HV V L) (H : tm_sim ξ ξ' t t') :
tm_sim ξ ξ' (L_map_tm f t) (L_map_tm f' t')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Hint Resolve L_map_hd_sim L_map_val_sim L_map_tm_sim.

Fixpoint
L_map_ktx_sim
EV HV V L L'
ξ ξ' (f f' : L → L') (Q : ∀ α, f α = f' α)
(K K' : ktx EV HV V L) (H : ktx_sim ξ ξ' K K') :
ktx_sim ξ ξ' (L_map_ktx f K) (L_map_ktx f' K').
Proof.
destruct H ; simpl ; crush.
Qed.

Lemma
HV_map_lbl_sim
HV L HV'
ξ ξ' (f f' : HV → HV') (Q : ∀ α, f α = f' α)
(ℓ ℓ' : lbl HV L) (H : lbl_sim ξ ξ' ℓ ℓ') :
lbl_sim ξ ξ' (HV_map_lbl f ℓ) (HV_map_lbl f' ℓ')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve HV_map_lbl_sim.

Lemma
HV_map_ef_sim
EV HV L HV'
ξ ξ' (f f' : HV → HV') (Q : ∀ α, f α = f' α)
(ε ε' : ef EV HV L) (H : ef_sim ξ ξ' ε ε') :
ef_sim ξ ξ' (HV_map_ef f ε) (HV_map_ef f' ε')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve HV_map_ef_sim.

Fixpoint
HV_map_eff_sim
EV HV L HV'
ξ ξ' (f f' : HV → HV') (Q : ∀ α, f α = f' α)
(𝓔 𝓔' : eff EV HV L) (H : eff_sim ξ ξ' 𝓔 𝓔') :
eff_sim ξ ξ' (HV_map_eff f 𝓔) (HV_map_eff f' 𝓔')
.
Proof.
induction H ; simpl ; crush.
Qed.

Hint Resolve HV_map_eff_sim.

Fixpoint
HV_map_ty_sim
EV HV L HV'
ξ ξ' (f f' : HV → HV') (Q : ∀ α, f α = f' α)
(T T' : ty EV HV L) (H : ty_sim ξ ξ' T T') :
ty_sim ξ ξ' (HV_map_ty f T) (HV_map_ty f' T')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve HV_map_ty_sim.

Fixpoint
HV_map_hd_sim
EV HV V L HV'
ξ ξ' (f f' : HV → HV') (Q : ∀ α, f α = f' α)
(h h' : hd EV HV V L) (H : hd_sim ξ ξ' h h') :
hd_sim ξ ξ' (HV_map_hd f h) (HV_map_hd f' h')
with
HV_map_val_sim
EV HV V L HV'
ξ ξ' (f f' : HV → HV') (Q : ∀ α, f α = f' α)
(v v' : val EV HV V L) (H : val_sim ξ ξ' v v') :
val_sim ξ ξ' (HV_map_val f v) (HV_map_val f' v')
with
HV_map_tm_sim
EV HV V L HV'
ξ ξ' (f f' : HV → HV') (Q : ∀ α, f α = f' α)
(t t' : tm EV HV V L) (H : tm_sim ξ ξ' t t') :
tm_sim ξ ξ' (HV_map_tm f t) (HV_map_tm f' t')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Hint Resolve HV_map_hd_sim HV_map_val_sim HV_map_tm_sim.

Fixpoint
HV_map_ktx_sim
EV HV V L HV'
ξ ξ' (f f' : HV → HV') (Q : ∀ α, f α = f' α)
(K K' : ktx EV HV V L) (H : ktx_sim ξ ξ' K K') :
ktx_sim ξ ξ' (HV_map_ktx f K) (HV_map_ktx f' K').
Proof.
destruct H ; simpl ; crush.
Qed.

Lemma
EV_map_ef_sim
EV HV L EV'
ξ ξ' (f f' : EV → EV') (Q : ∀ α, f α = f' α)
(ε ε' : ef EV HV L) (H : ef_sim ξ ξ' ε ε') :
ef_sim ξ ξ' (EV_map_ef f ε) (EV_map_ef f' ε')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve EV_map_ef_sim.

Fixpoint
EV_map_eff_sim
EV HV L EV'
ξ ξ' (f f' : EV → EV') (Q : ∀ α, f α = f' α)
(𝓔 𝓔' : eff EV HV L) (H : eff_sim ξ ξ' 𝓔 𝓔') :
eff_sim ξ ξ' (EV_map_eff f 𝓔) (EV_map_eff f' 𝓔')
.
Proof.
induction H ; simpl ; crush.
Qed.

Hint Resolve EV_map_eff_sim.

Fixpoint
EV_map_ty_sim
EV HV L EV'
ξ ξ' (f f' : EV → EV') (Q : ∀ α, f α = f' α)
(T T' : ty EV HV L) (H : ty_sim ξ ξ' T T') :
ty_sim ξ ξ' (EV_map_ty f T) (EV_map_ty f' T')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve EV_map_ty_sim.

Fixpoint
EV_map_hd_sim
EV HV V L EV'
ξ ξ' (f f' : EV → EV') (Q : ∀ α, f α = f' α)
(h h' : hd EV HV V L) (H : hd_sim ξ ξ' h h') :
hd_sim ξ ξ' (EV_map_hd f h) (EV_map_hd f' h')
with
EV_map_val_sim
EV HV V L EV'
ξ ξ' (f f' : EV → EV') (Q : ∀ α, f α = f' α)
(v v' : val EV HV V L) (H : val_sim ξ ξ' v v') :
val_sim ξ ξ' (EV_map_val f v) (EV_map_val f' v')
with
EV_map_tm_sim
EV HV V L EV'
ξ ξ' (f f' : EV → EV') (Q : ∀ α, f α = f' α)
(t t' : tm EV HV V L) (H : tm_sim ξ ξ' t t') :
tm_sim ξ ξ' (EV_map_tm f t) (EV_map_tm f' t')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Hint Resolve EV_map_hd_sim EV_map_val_sim EV_map_tm_sim.

Fixpoint
EV_map_ktx_sim
EV HV V L EV'
ξ ξ' (f f' : EV → EV') (Q : ∀ α, f α = f' α)
(K K' : ktx EV HV V L) (H : ktx_sim ξ ξ' K K') :
ktx_sim ξ ξ' (EV_map_ktx f K) (EV_map_ktx f' K').
Proof.
destruct H ; simpl ; crush.
Qed.

Fixpoint
V_map_hd_sim
EV HV V L V'
ξ ξ' (f f' : V → V') (Q : ∀ α, f α = f' α)
(h h' : hd EV HV V L) (H : hd_sim ξ ξ' h h') :
hd_sim ξ ξ' (V_map_hd f h) (V_map_hd f' h')
with
V_map_val_sim
EV HV V L V'
ξ ξ' (f f' : V → V') (Q : ∀ α, f α = f' α)
(v v' : val EV HV V L) (H : val_sim ξ ξ' v v') :
val_sim ξ ξ' (V_map_val f v) (V_map_val f' v')
with
V_map_tm_sim
EV HV V L V'
ξ ξ' (f f' : V → V') (Q : ∀ α, f α = f' α)
(t t' : tm EV HV V L) (H : tm_sim ξ ξ' t t') :
tm_sim ξ ξ' (V_map_tm f t) (V_map_tm f' t')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Hint Resolve V_map_hd_sim V_map_val_sim V_map_tm_sim.

Fixpoint
V_map_ktx_sim
EV HV V L V'
ξ ξ' (f f' : V → V') (Q : ∀ α, f α = f' α)
(K K' : ktx EV HV V L) (H : ktx_sim ξ ξ' K K') :
ktx_sim ξ ξ' (V_map_ktx f K) (V_map_ktx f' K').
Proof.
destruct H ; simpl ; crush.
Qed.

Lemma
L_bind_lid_sim
L L'
ξ ξ' (f f' : L → lid L') (Q : ∀ x, lid_sim ξ ξ' (f x) (f' x))
(ι ι' : lid L) (H : lid_sim ξ ξ' ι ι') :
lid_sim ξ ξ' (L_bind_lid f ι) (L_bind_lid f' ι')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve L_bind_lid_sim.

Lemma
L_bind_lbl_sim
HV L L'
ξ ξ' (f f' : L → lid L') (Q : ∀ x, lid_sim ξ ξ' (f x) (f' x))
(ℓ ℓ' : lbl HV L) (H : lbl_sim ξ ξ' ℓ ℓ') :
lbl_sim ξ ξ' (L_bind_lbl f ℓ) (L_bind_lbl f' ℓ')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve L_bind_lbl_sim.

Lemma
L_bind_ef_sim
EV HV L L'
ξ ξ' (f f' : L → lid L') (Q : ∀ x, lid_sim ξ ξ' (f x) (f' x))
(ε ε' : ef EV HV L) (H : ef_sim ξ ξ' ε ε') :
ef_sim ξ ξ' (L_bind_ef f ε) (L_bind_ef f' ε')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve L_bind_ef_sim.

Lemma
L_bind_eff_sim
EV HV L L'
ξ ξ' (f f' : L → lid L') (Q : ∀ x, lid_sim ξ ξ' (f x) (f' x))
(𝓔 𝓔' : eff EV HV L) (H : eff_sim ξ ξ' 𝓔 𝓔') :
eff_sim ξ ξ' (L_bind_eff f 𝓔) (L_bind_eff f' 𝓔')
.
Proof.
induction H ; simpl ; crush.
Qed.

Hint Resolve L_bind_eff_sim.

Fixpoint
L_bind_ty_sim
EV HV L L'
ξ ξ' (f f' : L → lid L') (Q : ∀ x, lid_sim ξ ξ' (f x) (f' x))
(T T' : ty EV HV L) (H : ty_sim ξ ξ' T T') :
ty_sim ξ ξ' (L_bind_ty f T) (L_bind_ty f' T')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve L_bind_ty_sim.

Fixpoint
L_bind_hd_sim
EV HV V L L'
ξ ξ' (f f' : L → lid L') (Q : ∀ x, lid_sim ξ ξ' (f x) (f' x))
(h h' : hd EV HV V L) (H : hd_sim ξ ξ' h h') :
hd_sim ξ ξ' (L_bind_hd f h) (L_bind_hd f' h')
with
L_bind_val_sim
EV HV V L L'
ξ ξ' (f f' : L → lid L') (Q : ∀ x, lid_sim ξ ξ' (f x) (f' x))
(u u' : val EV HV V L) (H : val_sim ξ ξ' u u') :
val_sim ξ ξ' (L_bind_val f u) (L_bind_val f' u')
with
L_bind_tm_sim
EV HV V L L'
ξ ξ' (f f' : L → lid L') (Q : ∀ x, lid_sim ξ ξ' (f x) (f' x))
(t t' : tm EV HV V L) (H : tm_sim ξ ξ' t t') :
tm_sim ξ ξ' (L_bind_tm f t) (L_bind_tm f' t')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Lemma
HV_bind_lbl_sim
EV HV V L HV'
ξ ξ' (f f' : HV → hd EV HV' V L) (Q : ∀ x, lbl_sim ξ ξ' (lbl_hd (f x)) (lbl_hd (f' x)))
ℓ ℓ' (H : lbl_sim ξ ξ' ℓ ℓ') :
lbl_sim ξ ξ' (HV_bind_lbl f ℓ) (HV_bind_lbl f' ℓ')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve HV_bind_lbl_sim.

Lemma
HV_bind_ef_sim
EV HV V L HV'
ξ ξ' (f f' : HV → hd EV HV' V L) (Q : ∀ x, lbl_sim ξ ξ' (lbl_hd (f x)) (lbl_hd (f' x)))
(ε ε' : ef EV HV L) (H : ef_sim ξ ξ' ε ε') :
ef_sim ξ ξ' (HV_bind_ef f ε) (HV_bind_ef f' ε')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve HV_bind_ef_sim.

Lemma
HV_bind_eff_sim
EV HV V L HV'
ξ ξ' (f f' : HV → hd EV HV' V L) (Q : ∀ x, lbl_sim ξ ξ' (lbl_hd (f x)) (lbl_hd (f' x)))
(𝓔 𝓔' : eff EV HV L) (H : eff_sim ξ ξ' 𝓔 𝓔') :
eff_sim ξ ξ' (HV_bind_eff f 𝓔) (HV_bind_eff f' 𝓔')
.
Proof.
induction H ; simpl ; crush.
Qed.

Hint Resolve HV_bind_eff_sim.
Hint Rewrite lbl_EV_map_hd lbl_HV_map_hd.

Fixpoint
HV_bind_ty_sim
EV HV V L HV'
ξ ξ' (f f' : HV → hd EV HV' V L) (Q : ∀ x, lbl_sim ξ ξ' (lbl_hd (f x)) (lbl_hd (f' x)))
(T T' : ty EV HV L) (H : ty_sim ξ ξ' T T') :
ty_sim ξ ξ' (HV_bind_ty f T) (HV_bind_ty f' T')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve HV_bind_ty_sim.

Lemma lbl_hd_sim EV HV V L ξ ξ' (h h' : hd EV HV V L) :
hd_sim ξ ξ' h h' →
lbl_sim ξ ξ' (lbl_hd h) (lbl_hd h').
Proof.
destruct 1 ; crush.
Qed.

Hint Resolve lbl_hd_sim.

Fixpoint
HV_bind_hd_sim
EV HV V L HV'
ξ ξ' (f f' : HV → hd EV HV' V L) (Q : ∀ x, hd_sim ξ ξ' (f x) (f' x))
(m m' : hd EV HV V L) (H : hd_sim ξ ξ' m m') :
hd_sim ξ ξ' (HV_bind_hd f m) (HV_bind_hd f' m')
with
HV_bind_val_sim
EV HV V L HV'
ξ ξ' (f f' : HV → hd EV HV' V L) (Q : ∀ x, hd_sim ξ ξ' (f x) (f' x))
(u u' : val EV HV V L) (H : val_sim ξ ξ' u u') :
val_sim ξ ξ' (HV_bind_val f u) (HV_bind_val f' u')
with
HV_bind_tm_sim
EV HV V L HV'
ξ ξ' (f f' : HV → hd EV HV' V L) (Q : ∀ x, hd_sim ξ ξ' (f x) (f' x))
(t t' : tm EV HV V L) (H : tm_sim ξ ξ' t t') :
tm_sim ξ ξ' (HV_bind_tm f t) (HV_bind_tm f' t')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Lemma
EV_bind_ef_sim
EV HV L EV'
ξ ξ' (f f' : EV → eff EV' HV L) (Q : ∀ x, eff_sim ξ ξ' (f x) (f' x))
ε ε' (H : ef_sim ξ ξ' ε ε') :
eff_sim ξ ξ' (EV_bind_ef f ε) (EV_bind_ef f' ε')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve EV_bind_ef_sim.

Lemma eff_app_sim
EV HV L ξ ξ' :
∀ (𝓔₁ 𝓔₁' : eff EV HV L), eff_sim ξ ξ' 𝓔₁ 𝓔₁' →
∀ 𝓔₂ 𝓔₂', eff_sim ξ ξ' 𝓔₂ 𝓔₂' →
eff_sim ξ ξ' (𝓔₁ ++ 𝓔₂) (𝓔₁' ++ 𝓔₂').
Proof.
induction 1 ; intros ? ? H₂.
+ crush.
+ rewrite <- app_comm_cons ; crush.
Qed.

Hint Resolve eff_app_sim.

Lemma
EV_bind_eff_sim
EV HV L EV'
ξ ξ' (f f' : EV → eff EV' HV L) (Q : ∀ x, eff_sim ξ ξ' (f x) (f' x))
𝓔 𝓔' (H : eff_sim ξ ξ' 𝓔 𝓔') :
eff_sim ξ ξ' (EV_bind_eff f 𝓔) (EV_bind_eff f' 𝓔')
.
Proof.
induction H ; simpl ; crush.
Qed.

Hint Resolve EV_bind_eff_sim.

Fixpoint
EV_bind_ty_sim
EV HV L EV'
ξ ξ' (f f' : EV → eff EV' HV L) (Q : ∀ x, eff_sim ξ ξ' (f x) (f' x))
T T' (H : ty_sim ξ ξ' T T') :
ty_sim ξ ξ' (EV_bind_ty f T) (EV_bind_ty f' T')
.
Proof.
destruct H ; simpl ; crush.
Qed.

Hint Resolve EV_bind_ty_sim.

Fixpoint
EV_bind_hd_sim
EV HV V L EV'
ξ ξ' (f f' : EV → eff EV' HV L) (Q : ∀ x, eff_sim ξ ξ' (f x) (f' x))
(h h' : hd EV HV V L) (H : hd_sim ξ ξ' h h') :
hd_sim ξ ξ' (EV_bind_hd f h) (EV_bind_hd f' h')
with
EV_bind_val_sim
EV HV V L EV'
ξ ξ' (f f' : EV → eff EV' HV L) (Q : ∀ x, eff_sim ξ ξ' (f x) (f' x))
(u u' : val EV HV V L) (H : val_sim ξ ξ' u u') :
val_sim ξ ξ' (EV_bind_val f u) (EV_bind_val f' u')
with
EV_bind_tm_sim
EV HV V L EV'
ξ ξ' (f f' : EV → eff EV' HV L) (Q : ∀ x, eff_sim ξ ξ' (f x) (f' x))
(t t' : tm EV HV V L) (H : tm_sim ξ ξ' t t') :
tm_sim ξ ξ' (EV_bind_tm f t) (EV_bind_tm f' t')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

Fixpoint
V_bind_hd_sim
EV HV V L V'
ξ ξ' (f f' : V → val EV HV V' L) (Q : ∀ x, val_sim ξ ξ' (f x) (f' x))
m m' (H : hd_sim ξ ξ' m m') :
hd_sim ξ ξ' (V_bind_hd f m) (V_bind_hd f' m')
with
V_bind_val_sim
EV HV V L V'
ξ ξ' (f f' : V → val EV HV V' L) (Q : ∀ x, val_sim ξ ξ' (f x) (f' x))
u u' (H : val_sim ξ ξ' u u') :
val_sim ξ ξ' (V_bind_val f u) (V_bind_val f' u')
with
V_bind_tm_sim
EV HV V L V'
ξ ξ' (f f' : V → val EV HV V' L) (Q : ∀ x, val_sim ξ ξ' (f x) (f' x))
t t' (H : tm_sim ξ ξ' t t') :
tm_sim ξ ξ' (V_bind_tm f t) (V_bind_tm f' t')
.
Proof.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
+ destruct H ; simpl ; crush.
Qed.

End section_sim_and_bindings.


(** [xx_sim] is closed under world extension *)
Section section_sim_future.

Context (ξ₁ ξ₁' ξ₂ ξ₂' : list var).
Context (P : (ξ₂ = ξ₁ ∧ ξ₂' = ξ₁') ∨ (∃ X X', ξ₂ = X :: ξ₁ ∧ ξ₂' = X' :: ξ₁')).

Lemma var_sim_future
X X' (H : var_sim ξ₁ ξ₁' X X') : var_sim ξ₂ ξ₂' X X'.
Proof.
destruct P as [ [P₂ P₂'] | [? [? [P₂ P₂']]] ] ; rewrite P₂, P₂' in *.
+ auto.
+ destruct H as [ n [H H'] ].
  exists (S n) ; split ; constructor ; assumption.
Qed.

Hint Resolve var_sim_future.

Lemma lid_sim_future
L (ι ι' : lid L) (H : lid_sim ξ₁ ξ₁' ι ι') : lid_sim ξ₂ ξ₂' ι ι'.
Proof.
destruct H ;  auto.
Qed.

Hint Resolve lid_sim_future.

Lemma lbl_sim_future
HV L (ℓ ℓ' : lbl HV L) (H : lbl_sim ξ₁ ξ₁' ℓ ℓ') : lbl_sim ξ₂ ξ₂' ℓ ℓ'.
Proof.
destruct H ; auto.
Qed.

Hint Resolve lbl_sim_future.

Lemma ef_sim_future
EV HV L (ε ε' : ef EV HV L) (H : ef_sim ξ₁ ξ₁' ε ε') : ef_sim ξ₂ ξ₂' ε ε'.
Proof.
destruct H ; auto.
Qed.

Hint Resolve ef_sim_future.

Lemma eff_sim_future
EV HV L (𝓔 𝓔' : eff EV HV L) (H : eff_sim ξ₁ ξ₁' 𝓔 𝓔') : eff_sim ξ₂ ξ₂' 𝓔 𝓔'.
Proof.
induction H ; auto.
Qed.

Hint Resolve eff_sim_future.

Fixpoint
ty_sim_future
EV HV L (T T' : ty EV HV L) (H : ty_sim ξ₁ ξ₁' T T') {struct H} : ty_sim ξ₂ ξ₂' T T'.
Proof.
destruct H ; constructor ; auto.
Qed.

Hint Resolve ty_sim_future.

Fixpoint
hd_sim_future
EV HV V L (m m' : hd EV HV V L) (H : hd_sim ξ₁ ξ₁' m m') {struct H} : hd_sim ξ₂ ξ₂' m m'
with
val_sim_future
EV HV V L (v v' : val EV HV V L) (H : val_sim ξ₁ ξ₁' v v') {struct H} : val_sim ξ₂ ξ₂' v v'
with
tm_sim_future
EV HV V L (t t' : tm EV HV V L) (H : tm_sim ξ₁ ξ₁' t t') {struct H} : tm_sim ξ₂ ξ₂' t t'
.
Proof.
+ destruct H ; constructor ; auto.
+ destruct H ; constructor ; auto.
+ destruct H ; constructor ; auto.
Qed.

Hint Resolve hd_sim_future val_sim_future tm_sim_future.

Fixpoint
ktx_sim_future
EV HV V L (K K' : ktx EV HV V L) (H : ktx_sim ξ₁ ξ₁' K K') {struct H} : ktx_sim ξ₂ ξ₂' K K'.
Proof.
destruct H ; constructor ; auto.
Qed.

End section_sim_future.


Lemma eff_app_sim_inv_l ξ ξ' EV HV L : ∀ (E1 E2 E' : eff EV HV L),
eff_sim ξ ξ' (E1 ++ E2) E' →
∃ E1' E2', E' = E1' ++ E2' ∧ (eff_sim ξ ξ' E1 E1' ∧ eff_sim ξ ξ' E2 E2').
Proof.
induction E1 ; simpl ; intros ? ? H.
+ repeat eexists ; [ | constructor | exact H ].
  auto.
+ inversion H ; subst ; clear H.
  match goal with
  | [ H : eff_sim _ _ (E1 ++ _) _ |- _ ] =>
    apply IHE1 in H ; destruct H as [?[?[?[??]]]] ; subst
  end.
  repeat eexists ; auto using app_comm_cons.
Qed.
