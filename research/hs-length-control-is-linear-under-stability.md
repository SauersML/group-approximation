---
rg: 2
id: hs-length-control-is-linear-under-stability
kind: claim
title: Hilbert-Schmidt stability makes the length-control modulus linear in length, whatever the Dehn function
artifacts:
  - research/artifacts/hs-dehn-modulus-length-control-2026-08-20.md
distinct_from:
  hs-dehn-modulus-bounded-by-dehn-function: that is the universal area/Dehn upper bound on trivial-word defect; this is the complementary stability upper bound, LINEAR in length, which beats the area bound exponentially whenever the Dehn function is superlinear.
  hyperlinear-computable-hs-dehn-modulus-solvable-word-problem: that turns computable length control into decidability; this identifies the source of length control (stability) and its length-linearity.
---

For a finitely presented `G = <S | R>` define the HS length-control modulus

```text
Phi_G(l, t) = sup { ||w(U)-1||_2 : w =_G 1, |w| <= l, Def_R(U) <= t },
```

the worst normalized-HS defect of a trivial word of length `<= l` over
approximate representations of relator defect `<= t`.

**Two bounds.**

1. **Area (universal).**  `Phi_G(l, t) <= Dehn_G(l) t`
   (`hs-dehn-modulus-bounded-by-dehn-function`).

2. **Stability (linear in length).**  If `G` is Hilbert--Schmidt stable
   with modulus `delta` (`Def_R(U) < delta(eps)` implies some exact
   representation `rho` with `max_s ||U_s - rho(s)||_2 <= eps`), then for a
   trivial word `w`, since `w(rho) = 1`,

```text
||w(U)-1||_2 = ||w(U) - w(rho)||_2 <= |w| max_s ||U_s - rho(s)||_2 <= |w| eps,
```

   so `Phi_G(l, t) <= l * eps(t)` with `eps(t) = inf{eps : delta(eps) > t}
   -> 0` as `t -> 0`.  The length dependence is **linear**, independent of
   the rate `eps(t)`.

**Consequence.**  When `Dehn_G` is superlinear (in particular exponential),
the stability bound is asymptotically far below the area bound in the length
variable: at fixed small `t`, `l eps(t)` versus `Dehn_G(l) t`.  So HS-stability
delivers exactly the length-linear control that the de la Salle far-sector
route (arXiv:2204.07084) needs -- the promotion of a microstate to an
averaged almost-representation of a finite quotient costs the length of the
quotient relations, not their area, precisely when the relevant subgroup is
stable.

This is the mechanism behind `bs14-strict-hs-dehn-separation`: the parabolic
skeleton `BS(1,4) = <u, h>` of `SL_2(Z[1/2])` is HS-stable but has exponential
Dehn function, so its trivial words have linear-in-length HS control despite
exponential area.
