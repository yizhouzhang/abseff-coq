Require Import Lang.Syntax Lang.Bindings Lang.Operational.
Require Import BindingsFacts_map.

Implicit Types EV HV V L : Set.

Fixpoint V_bind_ktx_plug
EV HV V V' L (f : V → val EV HV V' L)
(K : ktx EV HV V L) (t : tm EV HV V L) {struct K} :
V_bind_tm f (ktx_plug K t) =
ktx_plug (V_bind_ktx f K) (V_bind_tm f t).
Proof.
destruct K ; simpl ; crush.
Qed.
