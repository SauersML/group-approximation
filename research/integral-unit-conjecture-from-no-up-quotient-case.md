---
rg: 2
id: integral-unit-conjecture-from-no-up-quotient-case
kind: route
title: Higman's conjecture from its case on finitely generated groups with no nontrivial unique-product quotient
target: integral-unit-conjecture-torsion-free
requires:
  - integral-units-trivial-on-groups-without-up-quotients
  - connell-group-ring-primality
artifacts:
  - research/artifacts/up-quotient-unit-reduction-2026-09-16.md
---

Call `K` *UP-null* if every homomorphism from `K` to a group with unique
products (UP) is trivial. Assume every unit of `Z[K]` is `+-k` whenever `K` is
finitely generated, torsion-free and UP-null. Let `G` be torsion-free. Full
proofs of the lemmas are in the artifact, Sections 2 to 4.

**Components.** For `phi: K -> M` and `x in Z[K]`, let `x_(q)` be the part of
`x` supported on `phi^-1(q)`. Then `(xy)_(q)` is the sum of `x_(a) y_(b)` over
the expressions `q = ab` with `a in phi(supp x)` and `b in phi(supp y)`. At a
unique product, `(xy)_(q) = x_(a) y_(b)`.

**Strojnowski.** If `M` has UP and `|A||B| >= 2`, then `(A, B)` has two
distinct unique products. The artifact gives the full proof, Lemma 2.

**Step 1: `Z[G]` has no zero divisors.** Suppose not, and take `xy = 0` with
`x, y != 0` and `|supp x| + |supp y|` minimal. Translate to `x' = g^-1 x` and
`y' = y h^-1` with `1` in both supports, and put
`K = <supp x' ∪ supp y'>`.
- **`K` is UP-null.** If `phi: K -> M` is nontrivial with `M` UP, then one of
  the images of the supports has at least two elements. A unique product
  `q = ab` gives `0 = (x'y')_(q) = x'_(a) y'_(b)`, a zero divisor pair of
  smaller total support, which is a contradiction.
- **`Z[K]` has a nontrivial unit.** By `connell-group-ring-primality`, the rational
  group ring `Q[K]` is prime, since `K` is torsion-free. So `gamma = y' k x' != 0` for some
  `k in K`. Also `gamma^2 = 0`, so `1 + gamma` is a unit of `Z[K]`. It is not
  `+-h`: for `h = 1` the square of `gamma` would be a nonzero constant, and for
  `h != 1` the coefficient of `1` in `gamma^2` would be `1`.
- `K` is finitely generated, torsion-free and UP-null, so this contradicts the
  hypothesis.

**Step 2: units.** Let `uv = vu = 1`, choose `g in supp u`, and put
`u' = g^-1 u`, `v' = v g` and `K = <supp u' ∪ supp v'>`.
- **`K` is UP-null.** Let `phi: K -> M` with `M` UP, `A = phi(supp u')` and
  `B = phi(supp v')`, so `1 in A`.
  - If `|A||B| >= 2`, Strojnowski gives a unique product `q = ab != 1`. Then
    `u'_(a) v'_(b) = (u'v')_(q) = 0`, a zero divisor, contradicting Step 1.
  - If `|A| = |B| = 1`, then `A = {1}` and `u'v' = 1` forces `B = {1}`. So
    `phi` kills a generating set of `K`.
- `u'` is a unit of `Z[K]`, so by the hypothesis `u' = +-k` and
  `u = +-gk`.

So every unit of `Z[G]` is trivial. QED

The converse holds trivially, so the required claim is equivalent to the
target. The reduction proves no new case: a torsion-free group with no
nontrivial UP-null subgroup already has unique products (artifact,
Proposition 5.2).
