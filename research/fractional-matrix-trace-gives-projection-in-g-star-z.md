---
rg: 2
id: fractional-matrix-trace-gives-projection-in-g-star-z
kind: claim
title: A matrix projection of non-integer trace over G gives a projection of fractional trace in C*_r(G * Z), so Kadison--Kaplansky is equivalent to the torsion-free trace conjecture
distinct_from:
  reduced-projection-iff-gapped-spectral-measure: that turns a projection of C*_r(G) into a gapped spectral measure of one group-ring element; this turns a matrix projection over G into a 1x1 projection over the torsion-free overgroup G * Z.
  assembly-image-traces-are-integral-for-torsion-free-groups: that makes traces integral on the assembly image; this shows that integrality of the trace on all of K_0 is exactly what the Kadison--Kaplansky root asserts, once the group may change.
  non-dihedral-free-products-are-completely-selfless: that is the regularity input (strict comparison); this consumes it to realize fractional K_0 traces by projections.
---

**ESTABLISHED** by `fractional-matrix-trace-gives-projection-in-g-star-z-proof`.

Notation: `τ` is the canonical trace, and for a projection `p ∈ M_n(C*_r Γ)`,
`τ_*(p) = sum_i τ(p_ii)`.

**Theorem.** Let `G` be a nontrivial countable group and `Γ = G * Z`.

1. **Scalarization.** Let `p ∈ M_n(C*_r Γ)` be a projection with `τ_*(p) ∉ Z`, for
   instance a projection of `M_n(C*_r G) ⊆ M_n(C*_r Γ)`. Put `k = floor(τ_*(p))`. Then
   `C*_r(Γ)` contains a projection `e` with `τ(e) = τ_*(p) - k ∈ (0,1)`, and
   `p ~ 1_k ⊕ e` (Murray--von Neumann).
2. **Torsion.** If `G` is torsion-free, so is `Γ`.
3. **Selfless hosts.** Item 1 holds with `Γ` replaced by any countable group `H` for which
   `(C*_r H, τ)` is selfless. Example: every torsion-free acylindrically hyperbolic `H`,
   by `ozawa-php-groups-completely-selfless` (torsion-free groups have trivial finite radical).

**Corollary A (equivalence of roots).** The following are equivalent.
- (KK) For every countable torsion-free group `Γ`, `C*_r(Γ)` has no projection other than `0`
  and `1`. This is `kadison-kaplansky-torsion-free`.
- (TR) For every countable torsion-free group `Γ`, `τ_*(K_0(C*_r Γ)) ⊆ Z`: every projection
  in every `M_n(C*_r Γ)` has integer trace.

(TR) ⇒ (KK) is the classical argument: `τ` is faithful, so a projection `e ≠ 0, 1` has
`τ(e) ∈ (0,1)`. (KK) ⇒ (TR) is items 1 and 2: a matrix projection of non-integer trace over
`Γ` gives a nontrivial projection over the torsion-free group `Γ * Z`.

**Corollary B (per group).** For torsion-free `G`: if `C*_r(G * Z)` has no nontrivial
projection, then `τ_*(K_0(C*_r G)) ⊆ Z`. For a torsion-free acylindrically hyperbolic `H`,
`C*_r(H)` has no nontrivial projection iff `τ_*(K_0(C*_r H)) ⊆ Z`.

**Corollary C (matrix witnesses are root witnesses).** Let `G` be torsion-free and
`a ∈ M_n(C[G])` self-adjoint with `c ∉ spec(a)`, and put `P = χ_(-∞,c)(a) ∈ M_n(C*_r G)`.
If `τ_*(P) ∉ Z`, then `kadison-kaplansky-torsion-free` fails on `G * Z`. Two instances:
- **Gapped Atiyah failures.** If `A ∈ M_n(C[G])`, `0` is isolated in `spec(A^*A)`, and
  `dim_vN ker A ∉ Z`, then `P = χ_{0}(A^*A)` qualifies. So a counterexample to Strong Atiyah
  over a torsion-free group whose kernel is spectrally isolated is a Kadison--Kaplansky
  counterexample on `G * Z`.
- **Lattice transfer.** On the complex of `complex-with-irrational-and-torsion-free-lattices`,
  a gap of the combinatorial Laplacian at `0` makes its kernel projection over the
  torsion-free lattice a projection of irrational trace, hence a root counterexample.
  Neither instance is known to exist.

**Credit and novelty.**
- The mechanism is Dykema--Rørdam, *Projections in free product C\*-algebras*, GAFA 8
  (1998) 1--16, abstract: under the Avitzour conditions and nuclearity of both factors, the
  positive cone of `K_0` of the reduced free product is `{g : g = 0 or K_0(φ)(g) > 0}`. That
  covers only amenable `G`, where Baum--Connes holds anyway.
- Nuclearity is removed by Flores--Klisse--Ó Cobhthaigh--Pagliero (arXiv:2510.24675v3,
  Theorem A) together with Robert (arXiv:2309.14188v3, Theorem 3.1), both already imported.
- Novelty unverified: two web searches on 2026-09-12 found no statement of Corollary A. Treat
  it as packaging of known theorems with a new consequence for this graph.
