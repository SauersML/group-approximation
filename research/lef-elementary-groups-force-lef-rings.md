---
rg: 2
id: lef-elementary-groups-force-lef-rings
kind: claim
title: If some elementary group of rank at least four over a ring is LEF, the ring is LEF
distinct_from:
  exactly-matricial-rings-are-lef-rings: that passes from exact matriciality of the ring to LEF of the ring; this passes from LEF of one elementary group of rank at least four to LEF of the ring
  cohn-elementary-group-is-not-lef: that runs the finitely presented Steinberg cover at one ring to prove non-LEF; this runs it at every ring and reads a finite level quotient ring off each finite model
artifacts:
  - research/artifacts/un-lef-converse-2026-09-13-part1.md
---

**ESTABLISHED (unreviewed; proof route `lef-elementary-groups-force-lef-rings-proof`, artifact §1).**

Let `R` be a unital associative ring and `N >= 4`. If `EL_N(R)` is LEF, then `R` is a LEF ring in the sense
of `lef-simple-rings-are-not-finitely-presented`: every finite window of sums and products embeds exactly and
injectively in a finite unital ring. No simplicity or finite generation is assumed.

**Mechanism.**
- Lift a window of `R` to the free ring `A` on its elements. `St_N(A)` is finitely presented
  (`steinberg-finite-presentation-and-kazhdan-theorem`).
- A finite partial model of a large enough ball of `EL_N(R)` satisfies every relator, so it extends to a
  homomorphism `rho : St_N(A) -> Q` into a finite group.
- The kernels `{a : rho(x_ij(a)) = 1}` coincide and form a two-sided ideal `K` of finite index. `A/K` is a
  finite ring, and injectivity on the ball makes the window embed exactly in `A/K`.

**Model tests.**
- `L_k(1,2)` is not directly finite, so it is not a LEF ring. So no `EL_N(L_k(1,2))`, `N >= 4`, is LEF,
  consistent with the non-MF paper and `cohn-elementary-group-is-not-lef`.
- Group rings `F_q[Gamma]` of amenable non-LEF `Gamma` have non-LEF `EL_n`, and they are not LEF rings. Consistent.

**Consequence.** With `lef-simple-rings-are-not-finitely-presented`: a finitely presented infinite simple ring
has no LEF elementary group of rank at least four.
