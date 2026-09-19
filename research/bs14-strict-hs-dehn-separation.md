---
rg: 2
id: bs14-strict-hs-dehn-separation
kind: claim
title: The parabolic skeleton BS(1,4) has linear HS length control but exponential Dehn function, the first strict separation
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  centralized-cyclic-distortion-hs-dehn-tracks-area: that exhibits a group where the HS-Dehn modulus EQUALS the Dehn function (abelian distortion with an off-sheet centralizer); this exhibits a group where the HS length control is exponentially SMALLER than the Dehn function, showing the two genuinely diverge.
  approximate-doubling-invariant-joint-measure-is-atomic: that is the joint far-sector measure statement; this is the length-control half, established, for the same BS(1,4) skeleton.
---

Let `BS(1,4) = <a, t | t a t^(-1) = a^4> = Z rtimes_4 Z[1/4]`.

1. **Exponential Dehn function.**  `Dehn_(BS(1,4))(l)` is exponential
   (Gersten: not polynomial for `BS(1,n)`, `|n| != 1`; Thurston: exponential
   lower bound), because the cyclic `<a>` is exponentially distorted
   (`t^(-n) a t^n = a^(4^n)`).

2. **Linear HS length control.**  `BS(1,4)` is Hilbert--Schmidt stable
   (Levit--Vigdorovich arXiv:2206.02268 Cor D(3): `BS(1,n)` is HS-stable, via
   dense periodic measures of the single ergodic solenoid automorphism), so
   by `hs-length-control-is-linear-under-stability` its length-control
   modulus is `Phi(l, t) <= l eps(t)`, LINEAR in `l`.

Hence

```text
Phi_(BS(1,4))(l, t) = O(l eps(t))   while   Dehn_(BS(1,4))(l) t = exp(Theta(l)) t,
```

a strict separation `F_G << Dehn_G` -- the first explicit one in the graph.

**Why it matters for the goal.**  `BS(1,4) = <u, h>` (with `u` the parabolic
and `h = diag(2, 1/2)`) is exactly the parabolic skeleton subgroup of
`SL_2(Z[1/2])`.  So the length-control the far sector needs -- linear (not
area/exponential) HS control of the congruence relator family -- is already
a theorem ON THE SKELETON.  The remaining far-sector content is precisely the
EXTENSION of this linear control from the abelian/parabolic skeleton to the
full congruence relators of `SL_2(Z[1/2])`, across the non-amenable
involution.  The one structural point in favour
(`centralized-cyclic-distortion-hs-dehn-tracks-area` cannot embed): the
centralizer of the parabolic `u` in `SL_2(Z[1/2])` is the abelian unipotent
group, so there is no off-sheet centralizer element to run the
area-tracking-defect witness; the skeleton's linear control is not obstructed
by that mechanism.

This is a publishable separation on its own (independent of the program): a
finitely presented group whose HS length-control modulus is linear while its
Dehn function is exponential.
