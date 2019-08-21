Require Export Definitions_closed.
Require Export Definitions_unfold.
Require Export Definitions_open.

Hint Extern 1 => match goal with
| [ |- _ ⊨ ∀ᵢ x : ∅, _ ] => let x := fresh "x" in (iintro x ; destruct x)
end.
