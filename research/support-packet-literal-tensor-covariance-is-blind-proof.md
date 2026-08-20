---
rg: 2
id: support-packet-literal-tensor-covariance-is-blind-proof
kind: route
title: Compare the character supports of the allowed and forbidden spin packets
target: support-packet-literal-tensor-covariance-is-blind
requires: []
artifacts:
  - experiments/schur_packet_covariance_annihilator.py
---

Put `Delta=[V_+]-[V_-]` in the complex representation ring.  The character
map identifies its complexification with the algebra of class functions under
pointwise multiplication.  Thus `(LTC1)` is exactly

```text
chi_S(g) chi_Delta(g)=0
```

for every packet element `g` and every allowed simple `S`.

For a class-two packet sector with central character `k`, the character of an
irreducible spin representation vanishes unless the noncentral coordinate of
`g` belongs to the radical of the evaluated commutator form.  The forbidden
form at `k=101` is nondegenerate.  Hence `chi_(T_101)` is supported on the
centre of `B_sub`.  On every central element, however, every allowed spin
character is its nonzero dimension times a central phase.  Therefore

```text
chi_(T_101)(g) != 0  implies  chi_S(g) != 0
```

for every allowed `S`.  Equation `(LTC1)` forces `chi_Delta(g)=0` throughout
the support of `chi_(T_101)`, while the forbidden character itself vanishes
off that support.  Thus `chi_(T_101) chi_Delta=0` everywhere.  Injectivity of
the character map gives `(LTC2)`.

The experiment independently constructs all 38 irreducible characters and
the complete integral fusion table.  Over each of `F_2,F_3,F_5,F_101`, the
456 tensor equations from the allowed simples have rank 26, and adjoining all
forbidden tensor equations leaves rank 26.  It also checks `(LTC3)` element by
element.  Finally, as a falsification screen for a finite-Heisenberg
exactifier, it enumerates all 75,669 coefficients with at most six irreducible
summands supported on one central character: none is simultaneously
`alpha`-covariant, allowed-flat in commutant dimension, and forbidden-sensitive.
