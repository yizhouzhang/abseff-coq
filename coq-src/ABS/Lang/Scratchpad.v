Require Import Util.Subset.
Require Import Lang.Syntax Lang.Bindings.
Require Import BindingsFacts_map_0.
Require Import BindingsFacts_Xs_0.
Require Import BindingsFacts_Xs_1.
Require Import BindingsFacts_Xs_2.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Local Hint Extern 0 => match goal with
| [ x : ?V |- ∃ (_ : ?V), _ ] => exists x
end.

