---
rg: 2
id: katsura-one-vertex-actions-are-odometers-proof
kind: route
title: The Katsura cocycle gives sigma^m(j xi) = j sigma^n(xi); coprimality makes every level orbit full; the baker map conjugates a^m to a^n; the odometer lemma finishes
target: katsura-one-vertex-actions-are-odometers
requires:
  - odometer-generators-carry-no-nonsolvable-baumslag-solitar
---

**Standard inputs (not re-read):**
- `σ_k` is a well-defined action of `Z` by homeomorphisms. This is Exel-Pardo's construction from the Katsura data,
  since `(σ, φ)` with `φ(k, j) = ⌊(kn+j)/m⌋` satisfies the self-similarity cocycle identities.
- A level-transitive automorphism of the `m`-ary rooted tree is conjugate in the tree's automorphism group to the
  adding machine.

**Item 1.** For `k = m` the Euclidean division gives `mn + j = n·m + j`, so `σ_m(jξ) = j σ_n(ξ)`. That is,
`σ^m(jξ) = j σ^n(ξ)`. Induct on `|w|`:
`σ^{m^{k+1}}(j w ξ) = (σ^m)^{m^k}(j w ξ) = j (σ^n)^{m^k}(w ξ) = j (σ^{m^k})^n (w ξ) = j w σ^{n^{k+1}}(ξ)`,
using the case `|w| = k` for the last step.

**Item 2.** Induct on the level `k` to show that `<σ>` acts transitively on the `m^k` words of length `k`.
- `k = 1`: `σ` acts on the first letter by `j ↦ j + n mod m`, a single `m`-cycle because `gcd(m,n) = 1`.
- Step: assume transitivity on level `k`. Then the stabilizer in `<σ>` of a word `w` of length `k` contains
  `σ^{m^k}`, and the orbit-stabilizer count forces equality once `σ` has infinite order. Infinite order holds because
  the level-`k` orbit sizes `m^k` are unbounded. By item 1, `σ^{m^k}` acts on the children `wj` by `j ↦ j + n^{k+1}
  mod m`, a single `m`-cycle. So `<σ>` is transitive on level `k+1`.

Level-transitivity then gives the conjugacy to the adding machine by the standard input.

**Item 3.** For `(jξ, y)`: `b a^m b^-1 (ξ, j y) = b(σ^m(jξ), y) = b(j σ^n(ξ), y) = (σ^n(ξ), j y) = a^n (ξ, j y)`.

**Item 4.** By item 2, `a = σ × id` is conjugate to `(+1) × id` on `Z_m × C_m`. Here `n Z_m = Z_m` because `n` is
coprime to `m`. So item 4 of `odometer-generators-carry-no-nonsolvable-baumslag-solitar` applies to any `t` with
`t a^m t^-1 = a^n`. ∎
