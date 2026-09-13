---
rg: 2
id: fractional-matrix-trace-gives-projection-in-g-star-z-proof
kind: route
title: Strict comparison in the selfless algebra C*_r(G * Z) peels integer units off a matrix projection and compresses the remainder into the unit
target: fractional-matrix-trace-gives-projection-in-g-star-z
requires:
  - non-dihedral-free-products-are-completely-selfless
  - robert-tracial-selfless-regularity
  - amalgam-torsion-permanence-needs-no-cyclic-reduction
  - ozawa-php-groups-completely-selfless
---

Let `A` be a unital C\*-algebra with faithful tracial state `τ`, extended to `A ⊗ K` as
`τ ⊗ Tr`, and write `τ_*` for it on projections of `M_n(A)`.

**Step 0: the input.** For `G ≠ 1`, `(C*_r(G * Z), τ)` is completely selfless by
`non-dihedral-free-products-are-completely-selfless`: `G` is nontrivial, and `Z` is not `C_2`.
Complete selflessness implies selflessness, so Robert's Theorem 3.1(ii)
(`robert-tracial-selfless-regularity`) applies. Robert's definition (arXiv:2309.14188v3, §3),
verbatim: *"We say that A has the property of strict comparison of positive elements by ρ if
for any two positive elements a, b ∈ A ⊗ K, d_ρ(a) < d_ρ(b) ⇒ a ≾ b, where
d_ρ(c) := lim_n ρ(c^(1/n)) and ≾ denotes the Cuntz comparison relation."* Theorem 3.1(ii),
verbatim: *"If ρ is a trace (necessarily faithful), then A has stable rank one and strict
comparison of positive elements by ρ, and ρ is the unique 2-quasitracial state on A."*
Both were read from the arXiv PDF on 2026-09-12. For item 3 of the claim, the same input comes
from `ozawa-php-groups-completely-selfless`.

**Step 1: dimension of a projection.** For a projection `q ∈ M_m(A)`, `q^(1/n) = q`, so
`d_τ(q) = τ_*(q)`.

**Step 2: Cuntz subequivalence of projections is Murray--von Neumann subequivalence.** Let
`p, q` be projections of `M_m(A)` with `p ≾ q`. Pick `r_j ∈ A ⊗ K` with `r_j q r_j^* → p`.
Approximating one `r_j` by a finite matrix gives `r ∈ M_N(A)`, `N >= m`, with
`||r q r^* - p|| < 1/2`. Put `y = p r q`. Then

```text
||y y^* - p|| = ||p (r q r^* - p) p|| < 1/2,
```

so `y y^*` is invertible in the corner `p M_N(A) p`. Let `h = (y y^*)^(-1/2)`, inverted in that
corner, and `z = h y`. Then `z z^* = h y y^* h = p`, so `z` is a partial isometry and `z^* z` is
a projection. Since `y = y q`, also `z = z q`, so `z^* z = q z^* z q <= q`. Hence
`p ~ z^* z <= q`, and `τ_*(p) = τ_*(z^* z)` by the trace property.

**Step 3: peel and compress.** Let `p ∈ M_n(A)` be a projection with `t = τ_*(p) ∉ Z`. Then
`t > 0`; put `k = floor(t)` and `s = t - k ∈ (0,1)`.
- *Peel.* If `k >= 1`, view `1_k` and `p` in `M_N(A)`, `N = max(n,k)`. Then
  `d_τ(1_k) = k < t = d_τ(p)`, so strict comparison and Step 2 give `1_k ~ f <= p`. Put
  `q = p - f`: a projection of `M_n(A)`, since `f = p f p`, with `τ_*(q) = s`. If `k = 0`, put
  `q = p`.
- *Compress.* `d_τ(q) = s < 1 = d_τ(1_1)`, where `1_1 = 1 ⊕ 0 ⊕ ... ⊕ 0`. So `q ~ e <= 1_1`.
  A projection below `1_1` lives in the `(1,1)` corner, which is `A`. So `e ∈ A` is a
  projection with `τ(e) = s ∈ (0,1)`, in particular `e ≠ 0, 1`.
- *Decomposition.* `p = f + q` with `f ~ 1_k` and `q ~ e`, and `f ⊥ q`. So `p ~ 1_k ⊕ e`.

With `A = C*_r(G * Z)` this is item 1. The canonical inclusion `C*_r(G) ⊆ C*_r(G * Z)`
preserves the canonical trace, so projections of `M_n(C*_r G)` are covered. Item 3 is the same
argument with `A = C*_r(H)`.

**Step 4: torsion.** A free product is the amalgamated free product over the trivial group, so
`amalgam-torsion-permanence-needs-no-cyclic-reduction` makes `G * Z` torsion-free when `G` is.
The classical form: an element of finite order in a free product is conjugate into a factor
(Magnus--Karrass--Solitar, *Combinatorial Group Theory*, Cor. 4.1.4; not re-read here). This is
item 2.

**Corollaries.**
- *A, (TR) ⇒ (KK).* For a projection `e ∈ C*_r(Γ)` other than `0, 1`, both `e` and `1 - e` are
  nonzero positive, and `τ` is faithful, so `τ(e) ∈ (0,1)`, which is not an integer.
- *A, (KK) ⇒ (TR).* If some `M_n(C*_r Γ)`, with `Γ` torsion-free, holds a projection of
  non-integer trace, items 1 and 2 give a nontrivial projection in `C*_r(Γ * Z)`, and
  `Γ * Z` is countable and torsion-free. Classes of `K_0` are differences of projection
  classes, so integrality on projections is integrality on `K_0`. Idempotents need no separate
  case, since every idempotent of `M_n(C*_r Γ)` is similar to a projection with the same trace.
- *B.* Items 1 and 3, read contrapositively.
- *C.* `P = χ_(-∞,c)(a)` is a continuous function of `a` on its spectrum, so `P ∈ M_n(C*_r G)`;
  apply item 1. For the Atiyah instance: when `0` is isolated in `spec(A^*A)`, `χ_{0}(A^*A)` is
  a continuous function of `A^*A` on its spectrum, and its trace is `dim_vN ker A`. For the
  lattice instance, the kernel projection of `Δ_k` has trace `r · b_k^(2)(X;G)` over the
  torsion-free lattice, as recorded on `complex-with-irrational-and-torsion-free-lattices`.
