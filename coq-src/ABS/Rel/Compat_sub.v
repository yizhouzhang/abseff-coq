Require Import Rel.Definitions.
Require Import Rel.BasicFacts.
Require Import Lang.Static.
Require Import Util.Subset.

Implicit Types EV HV V : Set.

Section section_ccompat_se.

Lemma ccompat_eff_In
EV HV (Ξ : XEnv EV HV) δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂
ε 𝓔 (Hε : In ε 𝓔) t₁ t₂ ψ l₁ l₂ n :
n ⊨ 𝓾⟦ Ξ ⊢ ε ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ →
n ⊨ 𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂.
Proof.
intro.
induction 𝓔 ; [ crush | ].
apply in_inv in Hε ; destruct Hε ; [ ileft | iright ] ; crush.
Qed.

Hint Extern 0 => match goal with
| [ x : ?V |- ∃ (x : ?V), _ ] => exists x
end.

Lemma ccompat_eff_In_inverse
EV HV (Ξ : XEnv EV HV) δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂
𝓔 t₁ t₂ ψ l₁ l₂ n :
n ⊨ 𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ →
∃ ε, In ε 𝓔 ∧ (n ⊨ 𝓾⟦ Ξ ⊢ ε ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂).
Proof.
intro Ht.
induction 𝓔 ; [ crush | ].
idestruct Ht as Ht Ht ; crush.
Qed.

Lemma ccompat_se
EV HV (Ξ : XEnv EV HV) δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂
𝓔 𝓔' (Q : se 𝓔 𝓔') t₁ t₂ ψ l₁ l₂ n :
n ⊨ 𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂ →
n ⊨ 𝓤⟦ Ξ ⊢ 𝓔' ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ l₁ l₂.
Proof.
intro H.
induction 𝓔 as [ | ε 𝓔 IH𝓔 ] ; simpl in * ; [ crush | ].
idestruct H as Hε H𝓔.
- destruct 𝓔' as [ | ε' 𝓔' ] ; simpl in *.
  * destruct (Q ε) ; auto.
  * destruct (Q ε) ; [ auto | subst | ].
    { ileft ; assumption. }
    { iright ; eapply ccompat_eff_In ; eauto. }
- crush.
Qed.

End section_ccompat_se.


Section section_ccompat_sub.

Lemma ccompat_st_hole
EV HV (Ξ : XEnv EV HV) δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂
T T' 𝓔 n :
( ∀ ξ₁ ξ₂ v₁ v₂ n,
  n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ →
  n ⊨ 𝓥⟦ Ξ ⊢ T' ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂
) →
n ⊨ 𝓚v⟦ Ξ ⊢ T ⇢ T' # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ ktx_hole ktx_hole.
Proof.
intros H.
iintro ξ₁' ; iintro ξ₂' ; iintro v₁ ; iintro v₂ ; iintro Hξ₁' ; iintro Hξ₂'.
simpl.
iintro Hv.
apply 𝓥_in_𝓣 ; auto.
Qed.

Hint Resolve postfix_trans postfix_refl.

Lemma ccompat_stse_hole
EV HV (Ξ : XEnv EV HV) δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ T T' 𝓔 𝓔' n :
( ∀ ξ₁ ξ₂ v₁ v₂ n,
  n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ →
  n ⊨ 𝓥⟦ Ξ ⊢ T' ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂
) →
se 𝓔 𝓔' →
n ⊨ 𝓚w⟦ Ξ ⊢ T # 𝓔 ⇢ T' # 𝓔' ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ ktx_hole ktx_hole.
Proof.
intros Hst Hse.
loeb_induction LöbIH.
iintro ξ₁' ; iintro ξ₂' ;
iintro K₁ ; iintro K₂ ; iintro t₁ ; iintro t₂ ;
iintro Hξ₁' ; iintro Hξ₂'.
simpl.
iintro HKt.
apply 𝓦_in_𝓣.
idestruct HKt as ψ HKt ; idestruct HKt as l₁ HKt ; idestruct HKt as l₂ HKt.
idestruct HKt as Ht HKt.
idestruct HKt as Xs_K₁K₂ Hψ.
iexists ψ ; iexists l₁ ; iexists l₂.
repeat isplit.
+ eapply ccompat_se ; eauto.
+ assumption.
+ iintro ξ₁'' ; iintro ξ₂'' ; iintro t₁' ; iintro t₂' ;
  iintro Hξ₁'' ; iintro Hξ₂'' ; iintro Ht'.
  iespecialize Hψ.
  ispecialize Hψ ; [eassumption | ].
  ispecialize Hψ ; [eassumption | ].
  ispecialize Hψ ; [ apply Ht' | ].
  later_shift.
  apply 𝓣_roll.
  apply 𝓣_unroll in Hψ.
  bind_hole.
  eapply plug.
  - apply ccompat_st_hole ; apply Hst.
  - apply LöbIH.
  - clear - Hξ₁' Hξ₁'' ; eauto .
  - clear - Hξ₂' Hξ₂'' ; eauto .
  - apply Hψ.
Qed.

Lemma ccompat_st
EV HV (Ξ : XEnv EV HV) δ₁ δ₂ δ ρ₁ ρ₂ ρ
T T' :
st T T' →
∀ ξ₁ ξ₂ v₁ v₂ n,
n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ →
n ⊨ 𝓥⟦ Ξ ⊢ T' ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂.
Proof.
induction 1 as [
  | ? ? S T1 T2 𝓔1 𝓔2 ? IHT |
  ? ? T1 T2 | ? ? ? T1 T2 |
] ; intros ξ₁ ξ₂ v₁ v₂ n Hv ; simpl in Hv |- *.
+ trivial.
+ iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
  iintro u₁ ; iintro u₂ ; iintro Hu.
  bind_hole.
  apply plug with (Ta := T1) (𝓔a := 𝓔1) (ξ₁ := ξ₁') (ξ₂ := ξ₂').
  - apply ccompat_st_hole ; auto.
  - apply ccompat_stse_hole ; auto.
  - crush.
  - crush.
  - ispecialize Hv ξ₁' ; ispecialize Hv ξ₂'.
    ispecialize Hv ; [ assumption | ].
    ispecialize Hv ; [ assumption | ].
    iespecialize Hv ; iapply Hv.
    apply Hu.
+ iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
  iintro 𝓔₁ ; iintro 𝓔₂ ; iintro φ ; iintro cl_φ.
  change (λ _ _ _ _ _ _ _, (False )ᵢ) with (
    𝓤⟦ (EV_shift_XEnv Ξ) ⊢ [] ⟧
    (env_ext δ₁ 𝓔₁) (env_ext δ₂ 𝓔₂) (env_ext δ φ) ρ₁ ρ₂ ρ
  ).
  bind_hole.
  apply plug with (Ta := T1) (𝓔a := []) (ξ₁ := ξ₁') (ξ₂ := ξ₂').
  - apply ccompat_st_hole ; auto.
  - apply ccompat_stse_hole ; auto.
  - crush.
  - crush.
  - ispecialize Hv ξ₁' ; ispecialize Hv ξ₂'.
    ispecialize Hv ; [ assumption | ].
    ispecialize Hv ; [ assumption | ].
    ispecialize Hv 𝓔₁ ; ispecialize Hv 𝓔₂ ; ispecialize Hv φ.
    ispecialize Hv ; [ exact cl_φ | ].
    apply Hv.
+ iintro ξ₁' ; iintro ξ₂' ; iintro Hξ₁' ; iintro Hξ₂' ;
  iintro r₁ ; iintro r₂ ; iintro X₁ ; iintro X₂ ; iintro η ;
  iintro HX₁X₂ ; iintro Hr.
  change (λ _ _ _ _ _ _ _, (False )ᵢ) with (
    𝓤⟦ (HV_shift_XEnv Ξ) ⊢ [] ⟧
    δ₁ δ₂ δ
    (env_ext ρ₁ (hd_def 𝔽 (lid_f X₁) r₁))
    (env_ext ρ₂ (hd_def 𝔽 (lid_f X₂) r₂))
    (env_ext ρ η)
  ).
  bind_hole.
  apply plug with (Ta := T1) (𝓔a := []) (ξ₁ := ξ₁') (ξ₂ := ξ₂').
  - apply ccompat_st_hole ; auto.
  - apply ccompat_stse_hole ; auto.
  - crush.
  - crush.
  - ispecialize Hv ξ₁' ; ispecialize Hv ξ₂'.
    ispecialize Hv ; [ assumption | ].
    ispecialize Hv ; [ assumption | ].
    iespecialize Hv.
    ispecialize Hv ; [ eassumption | ].
    ispecialize Hv ; [ apply Hr | ].
    apply Hv.
+ auto.
Qed.

Lemma ccompat_sub
EV HV (Ξ : XEnv EV HV) δ₁ δ₂ δ ρ₁ ρ₂ ρ
T T' 𝓔 𝓔' :
st T T' →
se 𝓔 𝓔' →
∀ ξ₁ ξ₂ t₁ t₂ n,
n ⊨ 𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ →
n ⊨ 𝓣⟦ Ξ ⊢ T' # 𝓔' ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂.
Proof.
intros HT H𝓔 ξ₁ ξ₂ t₁ t₂ n Ht.
bind_hole.
apply plug with (Ta := T) (𝓔a := 𝓔) (ξ₁ := ξ₁) (ξ₂ := ξ₂).
+ apply ccompat_st_hole.
  apply ccompat_st.
  assumption.
+ apply ccompat_stse_hole.
  - apply ccompat_st.
    assumption.
  - assumption.
+ auto.
+ auto.
+ assumption.
Qed.

End section_ccompat_sub.


Lemma compat_sub
EV HV V (Ξ : XEnv EV HV) P (Γ : V → ty EV HV ∅)
T T' 𝓔 𝓔' :
st T T' →
se 𝓔 𝓔' →
∀ t₁ t₂ n,
n ⊨ ⟦ Ξ P Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : T # 𝓔 ⟧ →
n ⊨ ⟦ Ξ P Γ ⊢ t₁ ≼ˡᵒᵍ t₂ : T' # 𝓔' ⟧.
Proof.
intros HT H𝓔 t₁ t₂ n Ht.
iintro ξ₁ ; iintro ξ₂ ;
iintro δ₁ ; iintro δ₂ ; iintro δ ;
iintro ρ₁ ; iintro ρ₂ ; iintro ρ ;
iintro γ₁ ; iintro γ₂.
iintro HΞ ; iintro cl_δ ; iintro cl_ρ ; iintro HP ; iintro HΓ.
eapply ccompat_sub.
+ apply HT.
+ apply H𝓔.
+ iespecialize Ht.
  repeat (ispecialize Ht ; [ eassumption | ]).
  exact Ht.
Qed.
