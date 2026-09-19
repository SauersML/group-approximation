---
rg: 2
id: fd-invisibility-of-compression
kind: claim
title: The compression is invisible to every finite-dimensional representation
distinct_from:
  char-p-root-torsion-collapse: that establishes the congruence-type factorization with a central relative-K1 modulo clause; this shows the clause never mattered for the group images — ρ(Λ) EQUALS ρ(E) outright, central classes included — by an elementary additivity argument on top of that node's kernel structure.
  twisted-tower-central-character-criterion: that posed (CC) as the decisive two-sided question of the coordinate regime; this ANSWERS it — NO, vacuously — and empties the twisted-tower counterexample channel without any character theory.
  ccr-for-coordinate-collapsing-models: that proves (CCR) under the image-collapse hypothesis; this proves the hypothesis is automatic for every genuine finite-dimensional representation of G, closing the coordinate regime unconditionally.
artifacts:
  - research/char-p-root-torsion-collapse.md
---

**Theorem.**  Let `G = EL_r(R) ⋊ SL_d(ℤ)`, `R = 𝔽_q[x₁^{±1}…x_d^{±1}]`,
`r ≥ 3`, char `p`, and `Λ = tΓt⁻¹ = EL_r(S_Λ)` the compressed copy
(`S_Λ` the polynomial subalgebra on the monomials `x^{Av}`, `v ∈ ℕ^d`,
`A ∈ SL_d(ℤ)`).  For EVERY finite-dimensional unitary representation
`ρ` of `G`:

```text
ρ(Λ) = ρ(E)      (E = EL_r(R), as subgroups of U(n)).
```

In particular `ρ(Λ)' = ρ(E)' ⊆ ρ(Γ)'` — the compression is invisible
to all of FD.

**Proof (three steps, two already landed).**
1. By `char-p-root-torsion-collapse` steps 1–2 (root-subgroup
   torsion), `e_ij(J) ⊆ ker ρ` for a finite-codimension ideal
   `J ⊆ R`.
2. `S_Λ + J = R`: in the finite ring `R/J` each `x̄_i` is a unit of
   finite order; with `m` their lcm, monomial images depend on
   exponents mod `m`, and `{Av mod m : v ∈ ℕ^d} = (ℤ/m)^d` because
   `A` is invertible mod `m` (`det A = 1`) and `ℕ^d ↠ (ℤ/m)^d`.  So
   the image of `S_Λ` contains every monomial image and is a
   subalgebra: it is all of `R/J`.
3. Every elementary generator factors: `r = s + j` with `s ∈ S_Λ`,
   `j ∈ J`, and `e_ij(r) = e_ij(s)·e_ij(j)` (same-slot additivity),
   so `ρ(e_ij(r)) = ρ(e_ij(s)) ∈ ρ(Λ)`.  The generators of `E` land
   in `ρ(Λ)`, hence `ρ(E) ⊆ ρ(Λ) ⊆ ρ(E)`.  ∎

No K-theory, no stability theory, no Mennicke centrality, no
character theory — additivity of elementary matrices does all the
work once the kernel swallows `e_ij(J)`.

**What it closes.**

1. **(CC) is answered: NO, vacuously.**  `π(Λ) = Ē` in every
   congruence-type quotient arising from a finite-dimensional
   representation — the compressed copy's image contains every
   central relative-`K₁` class (indeed everything), so no pair of
   irreps can be separated by central characters yet agree on
   `π(Λ)`.  The twisted-tower counterexample channel of
   `twisted-tower-central-character-criterion` is EMPTY; the
   `2.8 × 10⁹`-scale computation is unnecessary; the verified `SK₁`
   nonvanishing remains true but is no longer load-bearing (it
   measures a mismatch of elementary subgroups, not of images).
2. **The modulo clause of `char-p-root-torsion-collapse` is
   harmless:** the central piece lies inside `ρ(Λ)` itself, so every
   `x ∈ ρ(Λ)'` commutes with it automatically.
3. **The coordinate regime of (CCR) is FULLY CLOSED,
   unconditionally:** every coordinatewise ultraproduct of genuine
   finite-dimensional representations of `G` satisfies the collapse
   hypothesis of `ccr-for-coordinate-collapsing-models`
   (`π_n(Γ) ⊆ π_n(E) = π_n(Λ)`), hence (CCR).  No chain hypothesis,
   no `SK₁` hypothesis, no exceptions.
4. **The residue of `kt-centralizer-normalization-hs` is exactly
   `approximate-collapse-for-kt-compressor`, and its enemy is now
   fully characterized:** a counterexample must be an approximate
   representation violating an identity (`ρ(Λ) = ρ(E)`) that holds
   for EVERY genuine finite-dimensional representation — not
   generically, not modulo anything: identically.

Fence: infinite-dimensional representations distinguish `Λ` from `E`
(quasi-regular `ℓ²(E/Λ)`), so this is strictly a finite-dimensional
rigidity phenomenon — which is precisely the shape the
matrix-ultraproduct question consumes.

Scope sharpening (2026-08-18 flexible-side pass): this is a
`G`-phenomenon, NOT a `Γ`-phenomenon.  Inside `Γ = EL_r(P)` alone the
collapse genuinely FAILS: the m-adic quotients `EL_r(P/m^k)`
separate `π(Λ) ⊊ π(Γ)` (proved — witness `e_ij(x̄_{i₀})` for a
coordinate ray outside the compression cone; see the flexible-side
vanguard section of `approximate-collapse-for-kt-compressor`).  The
Laurent-unit step (`x̄_i` invertible in `R/J`) is load-bearing: over
`P/m^k` the variables are nilpotent and the unit trick cannot start.
Those separating `Γ`-representations never extend to genuine
representations of `G` — which is this theorem restated — and that
non-extendability is what any (CCR) proof must exploit.
