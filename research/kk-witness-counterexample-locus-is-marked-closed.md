---
rg: 2
id: kk-witness-counterexample-locus-is-marked-closed
kind: claim
title: For each spectral witness the Kadison--Kaplansky counterexamples form an effectively closed set of marked groups, so the conjecture is a Pi^0_2 short-torsion statement and holds generically on the closure of torsion-free KK groups
artifacts:
  - experiments/kk-marked-compactness-2026-09-17/one_generator_torsion_bound.py
  - experiments/kk-marked-compactness-2026-09-17/one_generator_torsion_bound.out
distinct_from:
  local-approximation-properties-are-marked-closed: that shows the failure locus of soficity-type properties is OPEN (finite obstructions), which yields finitely presented counterexamples; here the failure locus of Kadison--Kaplansky for a fixed witness is CLOSED (a spectral gap is an infinite-moment condition), which reverses the transfer - no finitely presented counterexample follows, but the KK locus is G_delta, generic limits inherit it, and compactness bounds the torsion.
  reduced-projection-iff-gapped-spectral-measure: that turns a projection into a gapped spectral measure inside one group; this studies how the gapped-measure condition varies over the space of marked groups.
  kadison-kaplansky-torsion-free: that is the root; this gives an equivalent arithmetic (Pi^0_2) short-torsion form of it and a genericity theorem, without deciding it.
  generic-limit-of-subshift-sl-models-is-simple-kazhdan: that is a Baire argument for simplicity and property (T) on a family of Kazhdan limits; this is a Baire argument for absence of reduced projections on arbitrary closed families of marked groups.
---

**ESTABLISHED** by `kk-witness-counterexample-locus-is-marked-closed-proof`.

**Setting.** `F = F_d` is free on `s_1, ..., s_d`, and `M_d ⊆ 2^F` is the compact space of
normal subgroups `N ⊴ F` (marked groups `G_N = F/N`). A **witness** is a tuple
`ω = (a, c, ε, δ)` with `a = a*` in `Q[i][F]` and rationals `c`, `ε > 0`, `0 < δ ≤ 1/2`.
Put

```text
P_ω = { N in M_d : spec(λ_N(a)) ∩ (c-ε, c+ε) = ∅  and  μ_{a,N}((-∞, c)) ∈ [δ, 1-δ] },
```

where `λ_N: C[F] -> C*_r(G_N)` and `μ_{a,N}` is the spectral measure of `λ_N(a)` for the
canonical trace. `TF_d ⊆ M_d` is the set of torsion-free marked groups.

**Theorem A (topology).**
1. `N ↦ ‖λ_N(x)‖` is lower semicontinuous on `M_d` for every `x ∈ C[F]`.
2. Every `P_ω` is closed in `M_d`, and in fact a `Π^0_1` class in `2^F`.
3. `C*_r(G_N)` has a projection other than `0, 1` iff `N ∈ ∪_ω P_ω`. So the **KK locus**
   (marked groups whose reduced C\*-algebra has no nontrivial projection) is a `G_δ` subset of
   `M_d`, and `TF_d` is closed.
4. **Radius.** If `G_N` has no nontrivial projection, then for every `ω` there is `r = r(N, ω)`
   such that every marked group agreeing with `G_N` on words of length `≤ r` lies outside
   `P_ω`. If `G_N` has solvable word problem, `r(N, ω)` is computable from `(N, ω)`.
5. **Genericity.** If `Y ⊆ M_d` is closed and the KK groups are dense in `Y`, the KK groups
   form a dense `G_δ` of `Y`. Example: `Y` = the closure of the torsion-free hyperbolic
   `d`-marked groups; its generic member is a torsion-free group with only trivial projections.
6. **Fast limits.** Let `G(0) -> G(1) -> ...` be epimorphisms of `d`-marked groups with no
   nontrivial reduced projections, and enumerate the witnesses `ω_1, ω_2, ...`. If the
   injectivity radius `r_i` of `G(i-1) -> G(i)` satisfies `r_i ≥ r_{i-1}` and
   `r_i ≥ max_{k ≤ i} r(N_{i-1}, ω_k)`, then the direct limit has no nontrivial reduced projection.

**Theorem B (arithmetic form of the root).** The following are equivalent.
- (KK) `kadison-kaplansky-torsion-free`.
- (ST) **Gapped projections force short torsion.** For every `d` and every witness `ω` there is
  `N_ω` such that every `d`-marked group `G` in which `P_ω` holds contains an element `w ≠ 1`
  of word length `≤ N_ω` with `w^m = 1` for some `1 ≤ m ≤ N_ω`.

Moreover, for each `(d, ω)` the statement "no torsion-free `d`-marked group lies in `P_ω`" is
`Σ^0_1` (it has a finite certificate: finitely many cylinders covering `2^F`), so (KK) is a
`Π^0_2` sentence of arithmetic. If (KK) fails, it fails on a torsion-free finitely generated
group whose word problem has **low** Turing degree (Jockusch--Soare low basis theorem applied to
the nonempty `Π^0_1` class `P_ω ∩ TF_d`).

**Calibration (d = 1, proved).** A `1`-marked group is `Z` or `Z/n`. For
`a = Σ a_k s^k` with `L = Σ |k||a_k|`, every witness `ω = (a, c, ε, δ)` has
`N_ω ≤ ⌊π L / ε⌋`: a gap of half-width `ε` with spectrum on both sides forces `s^n = 1` with
`n ≤ π L / ε`. The script `experiments/kk-marked-compactness-2026-09-17/one_generator_torsion_bound.py`
checks the inequality `n · ε_max(n) ≤ π L` on 300 random Laurent polynomials for `n ≤ 400`.

**What this does and does not give.**
- It is the reverse of the soficity picture (`local-approximation-properties-are-marked-closed`):
  a KK counterexample is *not* inherited by finitely presented covers, because the gap is a
  closed condition. Genericity and fast limits inherit KK instead.
- Isolated points of `TF_d` get nothing from item 5. Example: `Γ(3) ⊴ SL_3(Z)` is finitely
  presented and, by the Margulis normal subgroup theorem, every proper quotient is finite and
  nontrivial, hence has torsion; so a small cylinder around `Γ(3)` meets `TF_d` only in `Γ(3)`.
- Theorem A.6 is applied in `kazhdan-torsion-free-tarski-monster-satisfies-kk` to obtain
  torsion-free Kazhdan Tarski monsters with only trivial projections.
