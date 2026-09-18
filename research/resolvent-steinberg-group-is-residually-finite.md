---
rg: 2
id: resolvent-steinberg-group-is-residually-finite
kind: claim
title: For some prime l and some N >= 4, the finitely presented Kazhdan group St_N(R_l) is residually finite
distinct_from:
  z-localized-embeds-in-fp-kazhdan-steinberg-group: that shows St_N(R_l) is finitely presented and contains Z_(l); this asks for residual finiteness, which finishes z-localized-embeds-in-fp-rf-group.
  resolvent-presentation-ring-is-residually-finite: that is residual finiteness of the ring R_l, a necessary condition for this claim by steinberg-rf-forces-ring-rf; this also needs the kernel of St_N(R_l) -> E_N(R_l) to be detected by finite quotients.
---

**OPEN.** There are a prime `l` and `N >= 4` such that `St_N(R_l)` is residually
finite. Here `R_l` is the eight-relator ring of
`resolvent-ring-presentation-is-not-faithful-on-r-bar`.

**Use.** With `z-localized-embeds-in-fp-kazhdan-steinberg-group` this is exactly what
`z-localized-embeds-in-fp-rf-group` asks for, by route
`z-localized-fp-rf-via-rf-resolvent-steinberg-group`. It is enough to find some
finitely presented residually finite quotient of `St_N(R_l)` in which `x_12(θ(Z_(l)))`
survives, for example `E_N(R_l)` if the kernel of `St_N(R_l) -> E_N(R_l)` is finitely
normally generated and `R_l` is residually finite.

**Reduction.** By `steinberg-rf-forces-ring-rf`, every finite quotient of `St_N(R_l)`
factors through `St_N(F)` for a finite quotient ring `F` of `R_l`. So the claim holds
iff both of these hold:
1. `R_l` is residually finite (`resolvent-presentation-ring-is-residually-finite`);
2. every nontrivial element of `K = ker(St_N(R_l) -> E_N(R_l))` survives in
   `St_N(F)` for some finite quotient ring `F`.

**Calibration.**
- `St_N(R_l)` has property (T) and contains `Z_(l)`. A residually finite witness
  would be a finitely presented residually finite Kazhdan group containing `Z_(l)`.
- Kazhdan groups can be residually finite (`SL_3(Z)`) and can contain infinitely
  generated abelian subgroups. No conflict with O1: there is no divisible subgroup.

## Attempts

None yet (2026-09-17, lane gq-infinite-primes).
