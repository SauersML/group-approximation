---
rg: 2
id: thompson-t-copies-of-t-have-trivial-centralizer-proof
kind: route
title: A commuting element has no fixed point, so its rotation number is rational (torsion clash) or irrational (A becomes rotations)
target: thompson-t-copies-of-t-have-trivial-centralizer
requires:
  - thompson-t-centralizers-of-orbit-free-subgroups-act-freely
  - finite-subgroups-of-thompson-t-are-cyclic
---

**Imported facts.**

- (S) `T` is simple (Cannon–Floyd–Parry, *Introductory notes on Richard
  Thompson's groups*, Enseign. Math. 42 (1996), Theorem 5.8). In particular
  `T` is perfect, has trivial center, and has no proper subgroup of finite
  index.
- (R) For every `q ≥ 2`, `T` has an element of order `q`. Proof: cut
  `S^1` at the `q` points `0 = p_0 < p_1 < … < p_{q−1}` with
  `p_i = 1 − 2^{−i}` for `i ≤ q − 1` (all dyadic), and let `t` send the arc
  `[p_i, p_{i+1}]` onto `[p_{i+1}, p_{i+2}]` (indices mod `q`, `p_q = 1 ≡ 0`)
  by the affine map between these dyadic intervals. Their lengths are powers of
  2, so each piece has slope a power of 2 and dyadic breakpoints. So `t ∈ T`
  and `t^q = 1`, `t ≠ 1`.
- (P) Poincaré's theorem (e.g. Navas, *Groups of circle diffeomorphisms*,
  §1.1): if `f ∈ Homeo+(S^1)` has irrational rotation number `α`, then `f` has
  a unique minimal closed invariant set `K`, and there is a continuous,
  monotone, degree-one surjection `h : S^1 → S^1` with `h f = R_α h`. The
  fibres of `h` are the closures of the components of `S^1 \ K` and the single
  points of `K` not in such closures. (`K` is `S^1` or a Cantor set, so
  distinct components of `S^1 \ K` have disjoint closures.) Also (P′): the rotation number of `f^q`
  is `q` times that of `f`, and `f` has a fixed point iff its rotation number
  is `0`.
- (F) Every nontrivial finite-order element of `Homeo+(S^1)` acts without
  fixed points (step "Free action" of
  `finite-subgroups-of-thompson-t-are-cyclic-proof`).

**Step 0: `A` has no finite orbit.** Suppose `x` has a finite `A`-orbit. Its
stabilizer has finite index in `A ≅ T`. By (S) it is all of `A`, so `A`
fixes `x`. By (R) `A` has a nontrivial element of finite order, and by (F) it
cannot fix `x`. Contradiction.

**Step 1: nontrivial elements of `C_T(A)` have no fixed point.** This is
`thompson-t-centralizers-of-orbit-free-subgroups-act-freely` applied with
Step 0.

Now let `c ∈ C_T(A)`, `c ≠ 1`, and let `ρ = rot(c) ∈ R/Z`. By Step 1 and (P′),
`ρ ≠ 0`.

**Step 2: `ρ` is not rational.** Suppose `ρ = p/q` in lowest terms; `q ≥ 2` because `ρ ≠ 0`. Then
`rot(c^q) = 0`, so `c^q` has a fixed point by (P′). It also commutes with
`A`, so `c^q = 1` by Step 1. Let `n ≥ 2` be the order of `c` and pick
`t ∈ A` of order `n` (it exists by (R), since `A ≅ T`). Now `<c> ∩ A` is
central in `A`, because `c` commutes with `A`. By (S) it is trivial. So
`<c, t> = <c> × <t> ≅ Z/n × Z/n`, a finite subgroup of `T` that is not
cyclic. This contradicts `finite-subgroups-of-thompson-t-are-cyclic`.

**Step 3: `ρ` is not irrational.** Suppose `ρ = α` is irrational, and take `K`
and `h` from (P) for `f = c`.

- *`A` preserves `K`.* For `a ∈ A`, `a(K)` is closed, nonempty and
  `c`-invariant (`c a K = a c K = a K`), and it is minimal because `a` is a
  homeomorphism conjugating the `c`-dynamics on `K` to itself. By uniqueness,
  `a(K) = K`.
- *`A` descends.* Since `a` preserves `K`, it permutes the components of
  `S^1 \ K` and hence the fibres of `h` described in (P). So there is a unique
  bijection `ā` of `S^1` with `h a = ā h`. It is continuous because `h` is a
  closed quotient map, so it is a homeomorphism, and `a ↦ ā` is a homomorphism
  `A → Homeo+(S^1)`.
- *The image is rotations.* From `h c = R_α h` and `a c = c a`, we get
  `ā R_α h = ā h c = h a c = h c a = R_α h a = R_α ā h`. Since `h` is onto,
  `ā` commutes with `R_α`, hence with every `R_{kα}`, `k ∈ Z`. These angles
  are dense and `ā` is continuous, so `ā(x + β) = ā(x) + β` for all `β`. So
  `ā = R_{ā(0)}` is a rotation. Thus `a ↦ ā` is a homomorphism from `A` to the
  abelian group `SO(2)`. By (S) `A` is perfect, so `ā = 1` for all `a`.
- *`A` fixes a point.* Take any fibre `h^{−1}(y)`. Each `a ∈ A` maps it into
  `h^{−1}(ā y) = h^{−1}(y)`, so it preserves it. The fibre is a point or a
  closed arc. In the second case its endpoints are preserved setwise by an
  orientation-preserving homeomorphism, so they are fixed. Either way `A` has
  a fixed point, which contradicts Step 0.

Steps 2 and 3 exhaust the nonzero rotation numbers. So `C_T(A) = 1`. ∎

**Remark.** Step 3 can be skipped by quoting that every element of `T` has
rational rotation number (Ghys–Sergiescu 1987). The argument above avoids that
theorem. The piecewise-linear structure of `T` is used only through
`thompson-t-centralizers-of-orbit-free-subgroups-act-freely` (in Step 1).
