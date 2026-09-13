---
rg: 2
id: density-random-groups-no-finite-quotients-below-exp-k
kind: claim
title: A random group with k random relators has no nontrivial finite quotient of order below exp(c k)
distinct_from:
  density-random-groups-no-small-nondegenerate-almost-reps: that bounds unitary almost-representations of dimension up to about (2n-1)^(dℓ/2) through an operator-norm net; this bounds exact finite quotients, needs no net, and reaches order exp(c k), doubly exponential in the length at positive density
  random-relators-kill-small-simple-quotients-of-kazhdan-groups: that uses property (T) mixing to kill alternating quotients up to order λ^(-L) with boundedly many random-walk relators; this uses a letter swap, needs no (T), and trades relator count for quotient order
  hyperbolic-group-without-finite-quotients: that asks for no nontrivial finite quotient at all; this excludes quotients below a threshold only, and above it the first moment is infinite
artifacts:
  - research/artifacts/solve-hyperbolic-rf-2026-09-13.md
---

**ESTABLISHED** (direct proof; not independently reviewed; no novelty claimed).

**Setting.** Fix `m >= 2` and `L >= 3`. Let `A` be the `2m` letters `a_i^{±1}` and
`C_L` the number of cyclically reduced words of length `L` in `F_m`. The relator
set `R` is either a uniform `k`-element subset of these words or `k` independent
uniform choices. Put `Λ = F_m/<<R>>` and `κ_m = (m−1)/(2m(2m−1)^3)`.

**THEOREM.**

1. **One homomorphism.** Let `φ: F_m -> Q` be a homomorphism to any group whose
   values on `A` are not all equal. Then `P[R ⊆ ker φ] <= (1 − κ_m)^k`. If the
   values on `A` are all equal, `φ` is trivial or the length-parity map onto `Z/2`.
2. **Simple quotients.** Consider the normal subgroups `N ⊇ <<R>>` of `F_m` with
   `F_m/N` nontrivial simple of order at most `M`, excluding the length-parity
   kernel. Granting `finite-simple-groups-at-most-two-per-order`, their expected
   number is at most `2 M^(m+1) (1 − κ_m)^k`.
3. **Odd length.** For `L` odd,
   `P[Λ has a nontrivial finite quotient of order <= M] <= 2 M^(m+1) (1 − κ_m)^k`.
   Without the order-coincidence import this probability is still at most
   `M^((m−1)M + 2) (1 − κ_m)^k`.
4. **Density.** Let `k = ⌊(2m−1)^(dL)⌋` with `d > 0` and `L` odd, and put
   `M_L = ⌊exp(κ_m k / (2(m+1)))⌋`. With probability at least
   `1 − 2 exp(−κ_m k/2)`, `Λ` has no nontrivial finite quotient of order at most `M_L`.

   Combine this with `density-random-group-hyperbolic-kazhdan-with-positive-b2`,
   taking `d ∈ (1/3, 1/2)` and letting `L → ∞` through odd multiples of 3. With
   probability tending to 1:
   - `Λ` is infinite, torsion-free, hyperbolic and Kazhdan;
   - it has a finite aspherical presentation complex and `b_2 >= 1`;
   - every nontrivial finite quotient has order greater than
     `exp(κ_m ⌊(2m−1)^(dL)⌋ / (2(m+1)))`.

For even `L`, part 2 still says that every nontrivial simple quotient of order at
most `M` is the length-parity quotient, with the same probability bound.

**Scale.** At positive density the threshold is doubly exponential in `L`. The
thresholds already on main are singly exponential:
- `λ^(-L)` for boundedly many relators in a Kazhdan host;
- dimension about `(2m−1)^(dL/2)` for almost-representations.

**What it does not do.** It says nothing above the threshold, and the method cannot
be pushed past it. `density-random-simple-quotient-first-moment-diverges` shows that
the unconditioned expected number of simple quotients is infinite at every large
length. After conditioning on hyperbolicity, a finite expectation would already
answer Gromov's question.

Proof: `density-random-no-quotients-below-exp-k-letter-swap-proof`. Exact checks of
the counting identities, of the window bound, and of part 1 on small permutation
groups are in the artifact.
