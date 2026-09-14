---
rg: 2
id: arithmetic-normal-subgroup-congruence-openness-proof
kind: route
title: Strong approximation, quasisimplicity mod p, Frattini lifting and a Lie-algebra ideal argument
target: normal-subgroups-of-arithmetic-lattices-are-congruence-open
requires: []
---

**Imported standard inputs (not re-read in this pass):**
- (SA) Kneser--Platonov strong approximation: `Γ̄` is open in `G(Ô)`, so
  `Γ̄ ⊇ ∏_{𝔭 ∉ S} G(O_𝔭)` for a finite set `S`.
- (QS) For almost all `𝔭`, `G(O/𝔭)` is perfect and simple modulo its center.
- (FR) For almost all `𝔭`, `G(O_𝔭)` is topologically perfect, and a closed
  subgroup surjecting onto `G(O/𝔭)` is all of `G(O_𝔭)`.
- (LIE) Closed subgroups of compact `p`-adic analytic groups are analytic.

*(a) Almost all primes.*  `Z(G)(O)` is finite and `Γ` is torsion-free, so any
`1 != a in M` is non-central.  The entries of `a - z` over central `z` give
nonzero ideals, so `a` stays non-central mod `𝔭` for almost all `𝔭`.  The image
of `M` is normal in `Γ/Γ(𝔭) = G(O/𝔭)` and not central, so by (QS) it is
everything; by (FR) the closure of `M` maps onto `G(O_𝔭)`.

*(b) The tail product.*  Let `N = closure(M)` and let `T` be the set of good
primes from (a) not in `S`.  For `𝔭 in T` and `x in G(O_𝔭)`,
`[m, x] in N` for all `m in N`, and the `𝔭`-components of `m` range over
`G(O_𝔭)`.  So `N ⊇ [G(O_𝔭), G(O_𝔭)] = G(O_𝔭)`, hence `N ⊇ ∏_{𝔭 in T} G(O_𝔭)`.

*(c) Finitely many primes.*  `N = π(N) × ∏_T` with `π` the projection to the
finite product over the remaining primes.  `M` injects into each `G(O_𝔭)`, so
`π(N)` has infinite image in each factor; by (LIE) its Lie algebra `I` is an
ideal of `⊕ 𝔤(k_𝔭)` projecting nonzero onto every simple summand `𝔤_𝔭`, and
`I ⊇ [I, 𝔤_𝔭] = 𝔤_𝔭`.  So `I` is everything, `π(N)` is open, and `N` is open.
`QED`
