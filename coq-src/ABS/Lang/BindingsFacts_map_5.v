Require Import Lang.Syntax Lang.Operational Lang.Bindings_map.
Set Implicit Arguments.

Implicit Types EV HV V L : Set.

Fixpoint L_map_ktx_plug
EV HV V L L' (f : L → L')
(K : ktx EV HV V L) t {struct K} :
L_map_tm f (ktx_plug K t) =
ktx_plug (L_map_ktx f K) (L_map_tm f t).
Proof.
destruct K ; simpl ; crush.
Qed.
