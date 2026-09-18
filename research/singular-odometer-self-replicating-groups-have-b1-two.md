---
rg: 2
id: singular-odometer-self-replicating-groups-have-b1-two
kind: claim
title: Tree automorphisms that move points along odometer orbits off finitely many singular points carry a regularized flux pair (A, B) that no relation can kill, and a sub-tree copy shifts A by B; so every self-replicating candidate in this class with a nonzero-slope element has b_1 >= 2 and is not finitely presented, and an FP_(d-1) one has zero flux throughout
artifacts:
  - experiments/odometer-flux-index-2026-09-17/flux_index.py
  - experiments/odometer-flux-index-2026-09-17/flux_index.out
distinct_from:
  m11-linear-activity-group-b1-two-not-finitely-presented: that proves b_1(R) = 2 for one group R = <M_11, a, b, c> by descending relations to stable words, a word-by-word argument; this defines two characters on the whole ambient group O_d by integrating the displacement, so they survive every relation of every subgroup at once, and it recovers that b_1 = 2 as one instance.
  odometer-prefix-groups-have-fg-index-kernels: that is the index character on groups of prefix tables with odometer leaves, whose displacement is continuous everywhere; this allows finitely many singular points, where the displacement is unbounded, and adds the slope B, which is zero on that class.
  fully-self-replicating-fp-infinity-groups-are-acyclic: that bounds b_1 for finitely presented R = R wr_X P with root image in Alt(X); this produces the characters that bound is applied to, for every candidate in O_d at once.
  self-wreathing-groups-have-full-sigma-invariants: that shows characters cannot test finiteness through Sigma invariants; this uses only how many independent characters there are.
---

**ESTABLISHED (unreviewed).** Proof: `singular-odometer-self-replicating-groups-have-b1-two-proof`.
Items 1-4 are elementary and self-contained. Item 5 imports item 3 of
`fully-self-replicating-fp-infinity-groups-are-acyclic`. The script checks item 1 and the M_11
values numerically.

**Setting.** Let `d ≥ 2`. Identify `X` with the digits `{0, …, d−1}` by a bijection `σ`, and
identify `X^ω` with the `d`-adic integers `ℤ_d`, reading the first letter as the least
significant digit. Let `μ` be Haar measure and `C_K(q)` the level-`K` cylinder containing `q`,
which has measure `d^{−K}`. Automorphisms act on the right. For `g ∈ Aut(X*)` put
`t_g(x) = x^g − x ∈ ℤ_d`. Let `S_g` be the set of points that have no neighbourhood on which
`t_g` is constant with value in `ℤ`. Define `𝒪_d = 𝒪_d^σ` to be the set of `g` such that:

- **(O1)** `S_g` is finite;
- **(O2)** the **truncated flux** `D_K(g) = ∫_{ℤ_d ∖ ∪_{q ∈ S_g} C_K(q)} t_g dμ` satisfies
  `D_K(g) = A(g) + K·B(g) + o(1)` as `K → ∞`, for real numbers `A(g)` (the **index**) and
  `B(g)` (the **slope**).

The integral is a finite sum, since `t_g` is locally constant and integer-valued on a compact
set. Examples:
- the odometer `x ↦ x + 1`;
- every finitary automorphism;
- every element of the topological full group of the odometer (`S_g = ∅`);
- linear-activity elements such as the `c` of `m11-linear-activity-self-replicating-group`, whose
  singular set is `{−1}`.

**Theorem.**

1. **Near-additivity.** For `g, h ∈ 𝒪_d` there are `K_0` and a rational `E(g, h)` with
   `D_K(gh) = D_K(g) + D_K(h) + E(g, h)·d^{−K}` for all `K ≥ K_0`. Also
   `D_K(g^{−1}) = −D_K(g)` for all `K`. Hence `𝒪_d` is a subgroup of `Aut(X*)` and
   `(A, B) : 𝒪_d → ℝ²` is a homomorphism. The slope `B` depends only on the germs of `g` at
   `S_g`; the index `A` does not.
2. **Values.**
   - Every finitary element has `A = B = 0`.
   - Every element of the odometer's topological full group has `B = 0`, and `A` is its mean
     displacement `∫ t_g dμ`. The odometer itself has `A = 1`.
3. **Sub-tree copies.** Let `g@x` act as `g` below the vertex `x ∈ X` and trivially elsewhere.
   If `g ∈ 𝒪_d`, then `g@x ∈ 𝒪_d`, with `A(g@x) = A(g) − B(g)` and `B(g@x) = B(g)`.
4. **Rank.** Let `R ≤ 𝒪_d` be finitely generated with `R@x ⊆ R` for some `x`. If `B(g) ≠ 0`
   for some `g ∈ R`, then `(A, B)(g)` and `(A, B)(g@x)` are independent, since their
   determinant is `B(g)²`. So `b_1(R) ≥ 2`. If `(A, B)` is not identically `0` on `R`, then
   `b_1(R) ≥ 1`.
5. **The class dies on the Tits route.** Let `R ≤ 𝒪_d` be fully self-replicating with root
   image a transitive `P ≤ Alt(X)` (conditions (S), (B) of `fully-self-replicating-tree-groups-give-fg-tits-hosts`,
   with `P` in place of `A_d`).
   - (a) If `d ≥ 4` and `R` is finitely presented, then `B ≡ 0` on `R`.
   - (b) If `d = 3` and `R` is finitely presented, then `A ≡ B ≡ 0` on `R`.
   - (c) If `R` is of type `FP_{d−1}`, then `A ≡ B ≡ 0` on `R`. In particular `R` contains no
     element of nonzero index: no odometer, no `𝒪_d`-conjugate of one, and no sub-tree copy of
     one.
6. **Instance.** For `R = ⟨M_11, a, b, c⟩`, with the digit map `letter k ↦ k − 2`,
   `letter 1 ↦ 10`, we get `R ≤ 𝒪_11` and `(A, B) = (e_a, e_c)` on the generators:
   - `D_K(a) = 1`;
   - `D_K(c) = K`;
   - `D_K(b) = D_K(m) = 0` for `m ∈ M_11`.

   This is a second, relation-free proof of `b_1(R) = 2`, as in
   `m11-linear-activity-group-b1-two-not-finitely-presented`.

**The class this kills.** Every Tits-route candidate that is built from the odometer and places
its states inside `𝒪_d` is excluded, whatever its relations, as soon as:
- **(i)** some element has nonzero slope, in which case it is not finitely presented; or
- **(ii)** some element has nonzero index, in which case it is not `FP_{d−1}`, and not
  `FP_∞`-acyclic as the Tits route expects.

The invariant is the pair `(A, B)`. Every member dies at the same step, the acyclicity count of
`fully-self-replicating-fp-infinity-groups-are-acyclic` item 3. In particular, redesigning the
stable section-cycles, as proposed under "What the next candidate needs" in
`m11-linear-activity-group-b1-two-not-finitely-presented`, cannot help. `(A, B)` is defined on
the ambient group `𝒪_d`, so no relation of any subgroup can carry flux.

**What survives.**
- For finite presentation: candidates in `𝒪_d` whose singular germs all have slope zero, for
  example a variant of `c` with sections `a` at digit `0` and `a^{−1}` at digit `1`, and which may
  still contain the odometer.
- For `FP_{d−1}`: candidates with `A ≡ B ≡ 0`.
- Candidates outside `𝒪_d` for every digit identification `σ`, that is, groups not contained in
  the singular extension of any odometer's orbit relation.

**Remark on germs.** `B` is a sum of local germ contributions, which is why the germ route of
the M_11 node sees `e_c`. `A` integrates the displacement over the whole space, so a finite sum
over germs cannot recover it. That is the gap recorded in the M_11 node's remark, closed here
by regularizing at the singular points instead of summing germs.
