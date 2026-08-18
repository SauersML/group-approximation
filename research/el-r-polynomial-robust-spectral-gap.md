---
rg: 2
id: el-r-polynomial-robust-spectral-gap
kind: claim
title: Robust asymptotic spectral gap (or character rigidity) for the elementary group over the polynomial ring
distinct_from:
  kt-centralizer-normalization-hs: that is the normalization/(CCR) question about commutants in ultraproducts; this is a representation-theoretic property of the single group Γ = EL_r(𝔽_q[x₁…x_d]) which, if established, would close that question's residue via published intertwiner-transport machinery.
  leavitt-steinberg-hs-stable: that is normalized-HS stability of the Steinberg cover of the Leavitt unit group (the other fork); this is a strictly weaker-flavored robustness property of a different group, and Becker–Lubotzky FORBIDS full HS-stability for this Γ, so the two must not be conflated.
artifacts:
  - research/kt-centralizer-normalization-hs.md
---

**Question (OPEN).**  Does `Γ = EL_r(𝔽_q[x₁…x_d])` (`r ≥ 3`, Kazhdan)
have robust asymptotic spectral gap — Dogon–Vigdorovich `(T;FD)^rob`,
arXiv:2506.20843: finite-dimensional ASYMPTOTIC representations have
uniform spectral gap — or character rigidity?

**Why this is the named target.**  The 2026-08-18 literature sweep
(verification ledger in `kt-centralizer-normalization-hs`, addendum h)
found exactly one transportable proof mechanism for the (AC)/(CCR)
residue, and it is NOT the sofic side's: Dogon–Vigdorovich's
intertwiner transport (2506.20843 Lem 3.1 — exact intertwiners from
generator-closeness — and Prop 3.3, its asymptotic version) plus
de la Salle's quantitative spectral-gap Poincaré inequality
(2204.07084, Lem 2.2, which runs through conditional expectations
onto relative commutants).  Establishing `(T;FD)^rob` or character
rigidity for this Γ would close (AC), completing
`kt-centralizer-normalization-hs` and with it the rigidity route to a
non-hyperlinear group.  Nobody has attempted it: Γ is not a lattice,
so Bekka-type character rigidity (math/0609102), Peterson's methods,
and the 2507.21862 higher-rank results do not reach it, and the
literature contains NOTHING on HS-type stability of `EL_n`/Steinberg
groups over polynomial rings (searches return only K-theoretic false
friends).

**Hard fence (Becker–Lubotzky, arXiv:1809.00632).**  Γ is infinite,
residually finite (hence sofic, hence hyperlinear) and Kazhdan, so Γ
is provably NOT stable in normalized HS, and (having infinitely many
finite-index subgroups) fails their Thm 1.4 criterion as well.
Asymptotic representations far from every genuine one are GUARANTEED
to exist for Γ.  Consequences: (i) never route (AC) through
HS-stability of Γ — foreclosed; (ii) the liftable case of (AC) is
true but vacuous — the entire content is non-liftable approximate
representations; (iii) `(T;FD)^rob` asks for spectral gap OF the
far-from-genuine representations, not their absence — the two
properties are compatible on their face, BUT:

**Unresolved consistency check (flagged, do not skip).**
Dogon–Vigdorovich's equivalence (their Thm 1.6, for irreducible
higher-rank lattices) includes *hyperfinite* HS-stability.  If
`(T;FD)^rob` implied ORDINARY HS-stability for a residually finite
(T) group, Becker–Lubotzky would refute `(T;FD)^rob` for Γ outright
and this route would collapse.  The sweep did not verify DV's
definition of hyperfinite HS-stability; whether the implication holds
for non-lattices is the first thing any campaign on this claim must
settle — a definition-reading task, hours not months.

**Counterexample side.**  The only known engine manufacturing
asymptotic HS-representations provably far from genuine ones with
controlled structure is Ioana's (2108.09589), whose property (τ)
asymmetry across commuting factors is blocked when a factor has (T)
(de la Salle 2204.07084 Thm 0.1).  Γ is Kazhdan.  No applicable
counterexample mechanism is in the literature.

**Adjacent reduction, recorded.**  Alekseev–Thom Open Problem 6.2(b)
(arXiv:2608.05362, §6, posted 2026-08-05) with a conjugation-coherence
strengthening would convert (AC) into a finite-dimensional statement:
with lifts `g_{s,n}` of `σ(s)` defining `A_n^Γ` and a lift `h_n` of
`σ(t)`, the conjugates `h_n g_{s,n} h_n^*` lift Λ's generators, so
(AC) becomes `∏_𝒰 h_n A_n^Γ h_n^* = ∏_𝒰 A_n^Γ` — exactly where the
congruence collapse lives.  The gap between 6.2(b) as stated and the
coherent-lift version is a uniqueness question, not a new theory.
