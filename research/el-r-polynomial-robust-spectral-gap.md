---
rg: 2
id: el-r-polynomial-robust-spectral-gap
kind: claim
title: Robust asymptotic spectral gap for the elementary group over the polynomial ring
distinct_from:
  kt-centralizer-normalization-hs: that is the normalization/(CCR) question about commutants in ultraproducts; this is a representation-theoretic property of the single group Γ = EL_r(𝔽_q[x₁…x_d]), now closed by citation, which discharges that question's uniformity gap but not (AC) proper.
  leavitt-steinberg-hs-stable: that is normalized-HS stability of the Steinberg cover (the other fork); this property is strictly weaker than stability — Becker–Lubotzky FORBIDS HS-stability for this Γ while (T) grants robustness for free, and Dogon–Vigdorovich print an explicit separation (𝔽₂×𝔽₂ is hyperfinitely HS-stable but not HS-stable).
artifacts:
  - research/kt-centralizer-normalization-hs.md
---

**Established (by citation — route
`el-r-polynomial-robust-spectral-gap-citation`).**
`Γ = EL_r(𝔽_q[x₁…x_d])` (`r ≥ 3`) has Dogon–Vigdorovich property
`(T;FD)_rob` (arXiv:2506.20843v2, Def 7.5 / Prop 7.6): its
finite-dimensional `‖·‖₂`-almost representations have uniform
approximate spectral gap for the generator Laplacian `Δ_S`.

The point that makes this a citation and not a campaign: **property
(T) implies `(T;FD)_rob` unconditionally** — DV Corollary 7.7,

```text
(T) ⟹ (T;W*)_rob ⟺ (T;W*) ⟹ (T;CE) ⟺ (T;FD)_rob ⟹ (T;FD) ⟹ (τ),
```

whose derivation lives entirely in their §7 with **no lattice input**
(the lattice/charmenability machinery is confined to §8/Thm 1.6 and is
neither available nor needed for Γ).  Γ has (T) by
Ershov–Jaikin-Zapirain (the program's recorded Kazhdan input for the
Kun–Thom pair), so the property holds outright.  Character rigidity —
the first sweep's guess at the needed hypothesis — is NOT needed; that
guess is superseded.

**What it discharges downstream.**  The approximate-Kazhdan uniformity
gap of `kt-centralizer-normalization-hs` (audit item 5 /
addendum 18f): `Ad π_n = π_n ⊗ π̄_n` lands in `U(M_{d_n²})`, is a
`‖·‖₂`-almost representation when `π_n` is, and `(T;FD)_rob` applies to
it directly — the `π ⊗ π̄` application template is in print (DV
Lem 8.2).  It does NOT touch (AC) proper
(`approximate-collapse-for-kt-compressor`), which is now the route's
sole open requirement.

**Fences and residuals.**

- *Cite the right formulation:* Def 7.5 says "finitely presented" but
  Prop 7.6/Cor 7.7 (and Bader's Thm 7.10) need only a finitely
  generated group with finite symmetric generating set — cite those.
- *Full (T) is load-bearing:* DV Rem 7.8 — `(T;FD)` does NOT imply
  `(T;FD)_rob` in general; it is full (T) that buys robustness.  Never
  weaken the citation to `(T;FD)`.
- *Effective constants are asserted, not proved:* the quantitative
  operator-norm form is Bader's Thm 7.10 (Ozawa characterization +
  spectral mapping); DV Rem 7.11 asserts the Hilbert–Schmidt effective
  version without proof.  Any downstream argument needing explicit
  constants must extract them or make do with the qualitative form —
  the one open sub-item left here.
- *Consistency with Becker–Lubotzky resolved:* `(T;FD)_rob` does not
  imply HS-stability — DV print the `𝔽₂ × 𝔽₂` separation, and the
  hyperfinite weakening is on the INPUT class (only asymptotic
  representations with hyperfinite limiting algebra need correcting;
  corrections are honest finite-dimensional representations), not on
  the output.  Becker–Lubotzky's far-from-genuine representations are
  globally-far by irreducibility, not spectral-gap-violating, so they
  do not obstruct robustness.

Trust surface: DV 2506.20843v2 read from PDF by the sweep agent
(Defs 7.2/7.4/7.5/7.9, Prop 7.6, Cor 7.7 — chain independently
re-derived from Prop 7.6 — Thms 6.2/7.10, Rems 7.8/7.11, Lem 8.2);
Ershov–Jaikin-Zapirain (T) as already recorded by the program.
