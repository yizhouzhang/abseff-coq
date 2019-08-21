Require Import Utf8 List.
Local Set Implicit Arguments.
Local Open Scope list_scope.

Notation "'foreach' x 'in' l 'then' P" := (fold_right (λ x Q, P ∧ Q) True l)
(at level 0, x at level 0, l at level 0, P at level 0).

Lemma foreach_inv X (l : list X) (P : X → Prop) :
  foreach x in l then (P x) →
  ∀ y, In y l → P y.
Proof.
  intros H_fold x H_x.
  induction l as [ | x' l IHl] ; simpl in * ; [ contradict H_x | ].
  destruct H_fold.
  destruct H_x.
  + subst x' ; assumption.
  + apply IHl ; assumption.
Qed.

Lemma foreach_arrow X (l : list X) (P Q : X → Prop) :
  (∀ x, P x → Q x) →
  foreach x in l then (P x) →
  foreach x in l then (Q x).
Proof.
  intros H_arrow HP.
  induction l ; simpl in *.
  + trivial.
  + destruct HP.
    split ; auto.
Qed.