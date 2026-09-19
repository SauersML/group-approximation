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

First take `gamma=delta=1` and put `Delta=[V_+]-[V_-]` in the complex
representation ring.  The character map identifies its complexification with
the algebra of class functions under pointwise multiplication.  Thus `(LTC1)`
is exactly

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

For the twisted statement, evaluate `(LTC1)` at a central element `z`.  Write
`h=gamma(z)z^(-1)` in the binary central coordinates.  The ratio between the
two source characters is

```text
chi_(S pullback gamma)(z)/chi_S(z)=(-1)^(k dot h),
```

where `k` is the central character of `S`; dimensions cancel.  If the two
coefficient values at `z` and `delta(z)` do not both vanish, `(LTC1)` says this
ratio is the same for `k=100,110,111`.  Their pairwise differences span the
`z_e,z_f` coordinate plane, so this is possible only when
`h=(a,0,0)`.  The common allowed ratio is then `(-1)^a`, which is also the
ratio for the forbidden character `101`.  If either coefficient value
vanishes, any one nonzero allowed central character forces the other to vanish
as well.  Hence the forbidden equality holds on the centre in all cases.  Off
the centre both forbidden characters vanish because automorphisms preserve
the centre.  This proves `(LTC2)` for arbitrary independent `gamma,delta`.

The experiment independently constructs all 38 irreducible characters and
the complete integral fusion table.  Over each of `F_2,F_3,F_5,F_101`, the
456 tensor equations from the allowed simples have rank 26, and adjoining all
forbidden tensor equations leaves rank 26.  It also checks `(LTC3)` element by
element.  It separately constructs all four linear packet automorphisms and
checks all 16 independently twisted covariance systems; their allowed ranks
are `26`, `36` or `42`, and forbidden equations never increase rank.  Finally,
as a falsification screen for a finite-Heisenberg
exactifier, it enumerates all 75,669 coefficients with at most six irreducible
summands supported on one central character: none is simultaneously
`alpha`-covariant, allowed-flat in commutant dimension, and forbidden-sensitive.
