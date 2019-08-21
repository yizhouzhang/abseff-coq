Require Import Utf8.

(* [erequire H], when called on a hypothesis [H : forall x, Q x],
   specializes [H] to a new evar to be filled in later *)
Ltac erequire H :=
  match type of H with
  | ∀ _  : ?H1, _ =>
    let x := fresh in
    evar (x : H1); specialize (H x); subst x
  end.
