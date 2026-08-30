---
rg: 2
id: stw93-singular-trace-needs-finite-central-cuntz-capacity
kind: claim
title: A trace-charged XCIII kernel element has a spectral cut of finite central Cuntz capacity
distinct_from:
  stw93-trace-kernel-quasitracial-invisibility: that open claim asks every quasitrace to kill the entire XCIII kernel; this theorem gives a necessary Cuntz-semigroup signature for any bounded trace which does not kill one positive kernel element.
  stw93-faithful-full-diagonal-retains-norm-kernel: that construction produces a norm-one kernel projection with infinite multiplicity escape; this theorem proves abstractly that such escape is exactly incompatible with detection by a bounded trace.
  stw93-central-commutator-lifting-is-trace-hinge: that criterion uses norm self-commutator generation; this criterion instead detects the same possible extra ordinary trace through finite Cuntz capacity of one spectral cut.
artifacts:
  - research/artifacts/stw93-faithful-diagonal-multiplicity-escape-audit-2026-08-30.md
---

Let `D` be a unital C*-algebra, let `h in D_+`, and define the central Cuntz
capacity

```text
cap_D(a)=sup{n in N: n[a]<=[1_D] in Cu(D)}.
```

If a normalized trace `q` on `D` satisfies `q(h)>0`, then there is an
`epsilon>0` such that

```text
cap_D((h-epsilon)_+)<infinity.                          (1)
```

Indeed one can choose `epsilon` with `q((h-epsilon)_+)>0`.  The associated
dimension function is then positive on `[(h-epsilon)_+]`; applying it to
`n[(h-epsilon)_+]<=[1]` gives a uniform upper bound on `n`.

Consequently, if every positive element `h` in the XCIII trace-kernel ideal

```text
I=J_tau intersect ((C*_r(F_2) tensor Z)_omega
                    intersect (C*_r(F_2) tensor Z)')
```

has infinite central Cuntz capacity after every nonzero spectral cut, then
every bounded trace on the central sequence algebra kills `I`.  Conversely,
any extra bounded trace furnishes a concrete positive `h in I` and a
spectral cut satisfying `(1)`.  Thus the ordinary-trace part of XCIII has an
exact finite-capacity obstruction: a negative witness must be centrally
finite at some positive spectral scale.
