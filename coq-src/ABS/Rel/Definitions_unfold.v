Require Import Rel.Definitions_closed Rel.Definitions_open.
Set Implicit Arguments.

Section section_unfold.

Context (EV HV V : Set).
Context (Ξ : XEnv EV HV).
Context (δ₁ δ₂ : EV → eff0) (δ : EV → IRel 𝓤_Sig).
Context (ρ₁ ρ₂ : HV → hd0) (ρ : HV → IRel 𝓣_Sig).

Fact fold_𝓦 n T 𝓔 ξ₁ ξ₂ (K₁ K₂ : ktx0) s₁ s₂ ψ l₁ l₂ :
  (n ⊨ 𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂) →
  (∀ X, (X ∈ l₁ → tunnels X K₁) ∧ (X ∈ l₂ → tunnels X K₂)) →
  (n ⊨ ∀ᵢ ξ₁' ξ₂' s₁' s₂',
       (postfix ξ₁ ξ₁')ᵢ ⇒
       (postfix ξ₂ ξ₂')ᵢ ⇒
       ψ ξ₁' ξ₂' s₁' s₂' ⇒
       ▷ 𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
         ξ₁' ξ₂' (ktx_plug K₁ s₁') (ktx_plug K₂ s₂')
  ) →
  n ⊨ 𝓦⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂ s₁ s₂.
Proof.
  intros ? ? Hs.
  iexists ψ ; iexists l₁ ; iexists l₂.
  repeat isplit ; [ assumption | iintro_prop ; assumption | ].
  iintro ξ₁' ; iintro ξ₂' ; iintro s₁' ; iintro s₂';
  iintro Hξ₁' ; iintro Hξ₂'; iintro Hs'.
  iespecialize Hs.
  ispecialize Hs ; [ eassumption | ].
  ispecialize Hs ; [ eassumption | ].
  ispecialize Hs ; [ eassumption | ].
  later_shift.
  apply 𝓣_roll.
  assumption.
Qed.

Fact unfold_𝓦 n T 𝓔 ξ₁ ξ₂ (K₁ K₂ : ktx0) s₁ s₂ :
  n ⊨ 𝓦⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂ s₁ s₂ →
  ∃ ψ l₁ l₂,
  (n ⊨ 𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ s₁ s₂ ψ l₁ l₂) ∧
  (∀ X, (X ∈ l₁ → tunnels X K₁) ∧ (X ∈ l₂ → tunnels X K₂)) ∧
  (n ⊨ ∀ᵢ ξ₁' ξ₂' s₁' s₂',
       (postfix ξ₁ ξ₁')ᵢ ⇒
       (postfix ξ₂ ξ₂')ᵢ ⇒
       ψ ξ₁' ξ₂' s₁' s₂' ⇒
       ▷ 𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ
         ξ₁' ξ₂' (ktx_plug K₁ s₁') (ktx_plug K₂ s₂')
  ).
Proof.
  intro Hw.
  idestruct Hw as ψ Hw ; idestruct Hw as l₁ Hw ; idestruct Hw as l₂ Hw.
  idestruct Hw as Hs Hw ; idestruct Hw as HK Hψ.
  ielim_prop HK.
  eexists ; eexists ; eexists.
  split ; [ eassumption | ].
  split ; [ assumption | ].
  iintro ξ₁' ; iintro ξ₂' ; iintro s₁' ; iintro s₂' ;
  iintro Hξ₁' ; iintro Hξ₂' ; iintro Hs'.
  iespecialize Hψ.
  ispecialize Hψ ; [ eassumption | ].
  ispecialize Hψ ; [ eassumption | ].
  ispecialize Hψ ; [ eassumption | ].
  later_shift.
  apply 𝓣_unroll in Hψ.
  assumption.
Qed.

Fact unfold_𝓚 n Ta 𝓔a Tb 𝓔b ξ₁ ξ₂ (K₁ K₂ : ktx0) ξ₁' ξ₂' t₁ t₂ :
  postfix ξ₁ ξ₁' → postfix ξ₂ ξ₂' →
  n ⊨ 𝓚⟦ Ξ ⊢ Ta # 𝓔a ⇢ Tb # 𝓔b ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ K₁ K₂ →
  n ⊨ 𝓣⟦ Ξ ⊢ Ta # 𝓔a ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' t₁ t₂ →
  n ⊨ 𝓣⟦ Ξ ⊢ Tb # 𝓔b ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁' ξ₂' (ktx_plug K₁ t₁) (ktx_plug K₂ t₂).
Proof.
  intros Hξ₁' Hξ₂' HK Ht.
  iespecialize HK.
  ispecialize HK ; [ iintro_prop ; eassumption | ].
  ispecialize HK ; [ iintro_prop ; eassumption | ].
  iapply HK ; apply Ht.
Qed.

Fact fold_𝓥𝓤_in_𝓣 n T 𝓔 ξ₁ ξ₂ t₁ t₂ :
  n ⊨ 𝓣⟦ Ξ ⊢ T # 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ⇔
      𝓣_Fun_Fix'
      (𝓥_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T)
      (𝓤_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝓔)
      ξ₁ ξ₂ t₁ t₂.
Proof.
  apply 𝓣_Fun_Fix'_nonexpansive.
  + repeat iintro ; isplit ; iintro H.
    - apply 𝓥_roll ; assumption.
    - apply 𝓥_unroll ; assumption.
  + repeat iintro ; isplit ; iintro H.
    - apply 𝓤_roll ; assumption.
    - apply 𝓤_unroll ; assumption.
Qed.

Fact fold_𝓥𝓤a_in_𝓚 n T 𝓔 𝓥b 𝓤b ξ₁ ξ₂ K₁ K₂ :
  n ⊨ 𝓚_Fun
      (𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
      (𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
      𝓥b 𝓤b
      ξ₁ ξ₂ K₁ K₂ ⇔
      𝓚_Fun
      (𝓥_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T)
      (𝓤_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝓔)
      𝓥b 𝓤b
      ξ₁ ξ₂ K₁ K₂.
Proof.
  apply 𝓚_Fun_nonexpansive ; repeat iintro.
  + apply 𝓥_roll_unroll.
  + apply 𝓤_roll_unroll.
  + apply auto_contr_id.
  + apply auto_contr_id.
Qed.

Fact fold_𝓥𝓤_in_𝓚 n (Ta Tb : ty EV HV ∅) 𝓔a 𝓔b ξ₁ ξ₂ K₁ K₂ :
  n ⊨ 𝓚_Fun
      (𝓥⟦ Ξ ⊢ Ta ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
      (𝓤⟦ Ξ ⊢ 𝓔a ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
      (𝓥⟦ Ξ ⊢ Tb ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
      (𝓤⟦ Ξ ⊢ 𝓔b ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ)
      ξ₁ ξ₂ K₁ K₂ ⇔
      𝓚_Fun
      (𝓥_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ Ta)
      (𝓤_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝓔a)
      (𝓥_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ Tb)
      (𝓤_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝓔b)
      ξ₁ ξ₂ K₁ K₂.
Proof.
  apply 𝓚_Fun_nonexpansive ; repeat iintro.
  + apply 𝓥_roll_unroll.
  + apply 𝓤_roll_unroll.
  + apply 𝓥_roll_unroll.
  + apply 𝓤_roll_unroll.
Qed.

Context (EV' HV' V' : Set).
Context (Ξ' : XEnv EV' HV').
Context (δ₁' δ₂' : EV' → eff0) (δ' : EV' → IRel 𝓤_Sig).
Context (ρ₁' ρ₂' : HV' → hd0) (ρ' : HV' → IRel 𝓣_Sig).

Fact 𝓥_roll_unroll_iff n T T' ξ₁ ξ₂ v₁ v₂ :
(n ⊨ 𝓥⟦ Ξ ⊢ T ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ v₁ v₂ ⇔
     𝓥⟦ Ξ' ⊢ T' ⟧ δ₁' δ₂' δ' ρ₁' ρ₂' ρ' ξ₁ ξ₂ v₁ v₂) ↔
(n ⊨ 𝓥_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ T ξ₁ ξ₂ v₁ v₂ ⇔
     𝓥_Fun_Fix Ξ' δ₁' δ₂' δ' ρ₁' ρ₂' ρ' T' ξ₁ ξ₂ v₁ v₂).
Proof.
split ; intro H.
+ eapply I_iff_transitive ; [ | apply 𝓥_roll_unroll ].
  eapply I_iff_transitive ; [ | apply H ].
  apply I_iff_symmetric ; apply 𝓥_roll_unroll.
+ eapply I_iff_transitive ; [ apply 𝓥_roll_unroll | ].
  eapply I_iff_transitive ; [ apply H | ].
  apply I_iff_symmetric ; apply 𝓥_roll_unroll.
Qed.

Fact 𝓤_roll_unroll_iff n 𝓔 𝓔' ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ :
(n ⊨ 𝓤⟦ Ξ ⊢ 𝓔 ⟧ δ₁ δ₂ δ ρ₁ ρ₂ ρ ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ ⇔
     𝓤⟦ Ξ' ⊢ 𝓔' ⟧ δ₁' δ₂' δ' ρ₁' ρ₂' ρ' ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂) ↔
(n ⊨ 𝓤_Fun_Fix Ξ δ₁ δ₂ δ ρ₁ ρ₂ ρ 𝓔 ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂ ⇔
     𝓤_Fun_Fix Ξ' δ₁' δ₂' δ' ρ₁' ρ₂' ρ' 𝓔' ξ₁ ξ₂ t₁ t₂ ψ L₁ L₂).
Proof.
split ; intro H.
+ eapply I_iff_transitive ; [ | apply 𝓤_roll_unroll ].
  eapply I_iff_transitive ; [ | apply H ].
  apply I_iff_symmetric ; apply 𝓤_roll_unroll.
+ eapply I_iff_transitive ; [ apply 𝓤_roll_unroll | ].
  eapply I_iff_transitive ; [ apply H | ].
  apply I_iff_symmetric ; apply 𝓤_roll_unroll.
Qed.

End section_unfold.
