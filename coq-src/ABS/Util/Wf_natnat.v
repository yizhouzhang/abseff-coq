Require Import Utf8 Lia.
Local Set Implicit Arguments.

Definition lt' (p1 p2 : nat * nat) : Prop :=
  match p1, p2 with
  | (n1, m1), (n2, m2) => n1 < n2 ∨ n1 = n2 ∧ m1 < m2
  end.

Lemma lt'_wf_aux :
well_founded lt → forall x, Acc lt x → forall y, Acc lt y → Acc lt' (x, y).
Proof.
  intros Hlt x Hx.
  induction Hx as [x _ IHaccx].
  intros y Hy.
  induction Hy as [y _ IHaccy].
  constructor.
  intros (x', y').
  destruct 1 as [ | [] ]; subst ; auto.
Qed.

Lemma lt'_wf : well_founded lt'.
Proof.
  intros (x, y).
  apply lt'_wf_aux ; apply Wf_nat.lt_wf.
Qed.

Ltac lt'_left := simpl ; left ; lia.
Ltac lt'_right := simpl ; right ; split ; [ reflexivity | lia ].
Ltac lt'_solve :=
  match goal with
  | [ W : Acc lt' (?n2, 0) |- Acc lt' (?n1, ?m1) ] =>
    apply (Acc_inv W) ; lt'_left
  | [ W : Acc lt' (S ?n, ?m2) |- Acc lt' (?n, ?m1) ] =>
    apply (Acc_inv W) ; lt'_left
  | [ W : Acc lt' (?n, ?m2) |- Acc lt' (?n, ?m1) ] =>
    apply (Acc_inv W) ; lt'_right
  | [ W : Acc lt' (?n2, ?m2) |- Acc lt' (?n1, ?m1) ] =>
    (* general case *)
    apply (Acc_inv W) ;
    simpl;
    let L := fresh "H_le" in
    assert (n1 <= n2) as L ; [ lia | ] ;
    inversion L ; subst ; [ lt'_right | lt'_left ]
  end.
