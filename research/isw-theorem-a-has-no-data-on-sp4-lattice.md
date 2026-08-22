---
rg: 2
id: isw-theorem-a-has-no-data-on-sp4-lattice
kind: claim
title: Ioana--Spaas--Wiersma Theorem A admits no input data on the symplectic lattice for any subgroup
distinct_from:
  sp4-metaplectic-class-pointwise-coboundary-limit: that kills the constant-class version of the attack (one fixed class, changing representatives) for every group; this kills ALL versions at Sp_4(Z) — including sequences of distinct classes — and uniformly in the subgroup Lambda.
  isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals: that forbids rerunning Theorem A inside a maximal parabolic (relative to its radical); this forbids running it on the full lattice Sp_4(Z) relative to ANY subgroup, which is the form a refutation of the LLP hole would need.
  sp2g-z-full-c-star-algebra-has-llp: that is the lifting hole itself; this hardens its refutation side by proving the only published scalar-cohomological LLP-failure mechanism cannot apply to it.
---

**THEOREM.**  Let `Gamma = Sp_4(Z)` and let `Lambda <= Gamma` be ANY
subgroup.  There is no sequence `c_n in Z^2(Gamma,T)` satisfying the
three hypotheses of Ioana--Spaas--Wiersma Theorem A (arXiv:2006.01874,
p. 2, source-verified 2026-08-21):

```text
(1) c_n|_Lambda is not a 2-coboundary, for every n;
(2) c_n(g,h) -> 1 for every g,h in Gamma;
(3) each c_n is the exact cocycle of a finite-dimensional
    projective unitary representation of Gamma.               (NA1)
```

Consequently ISW Theorem A can never show that `C^*(Sp_4(Z))` fails the
LLP — not through the Siegel pair, not through the Klingen pair, not
through the Klingen center, not through `Lambda = Gamma` itself.

**Relative property (T) was never the issue.**  Theorem A also assumes
`(Gamma,Lambda)` has relative property (T) in the Kazhdan--Margulis
sense (any unitary representation of `Gamma` with almost invariant
vectors has a nonzero `Lambda`-invariant vector; ISW p. 2).  Since
`Sp_4(Z)` has property (T) (ISW Example 1.3(i), p. 4, records property
(T) for `Sp_{2n}(R)`, `n >= 2`, citing BdHV Remark 3.5.5; lattices
inherit it, classically), EVERY pair `(Sp_4(Z),Lambda)` has relative
property (T).  So the hypothesis that looked like the bottleneck is
free, and the entire content of the mechanism at `Sp_4(Z)` was the
cocycle supply `(NA1)` — which this theorem removes.

**What it answers.**  The extension question of the lifting lane — do
the NPS/theta classes of the Klingen (or Siegel) sub-pair extend to
classes of `Sp_4(Z)` realized by finite-dimensional projective
representations with classes tending to the trivial class? — is
answered NO wholesale: by `sp4-fd-projective-multiplier-is-finite`
there are only finitely many finite-dimensionally realizable classes
of `Sp_4(Z)` in total, while the ISW mechanism (their `Z^2 x| SL_2(Z)`
construction, Section 3.2, p. 11, uses the infinitely many distinct
classes `exp(2 pi i (xt-yz)/k)`) requires infinitely many.

**What survives.**  This fence closes the scalar Theorem A surface
only.  The remaining ISW-side mouth at `Sp_4(Z)` is their
operator-valued Theorem C (p. 3): cocycles in `Z^2(Gamma,L^0(X,T))`
over a p.m.p. action with `||c_n(g,h) - 1||_2 -> 0`, non-coboundary
restrictions, plus — for LLP rather than LP — `R^omega`-embeddability
of every twisted crossed product `L^infty(X) x|_{sigma,c_n} Gamma`.
No such data is recorded for `Sp_4(Z)` in either direction.
