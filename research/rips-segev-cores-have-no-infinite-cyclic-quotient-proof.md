---
rg: 2
id: rips-segev-cores-have-no-infinite-cyclic-quotient-proof
kind: route
title: Fiber a zero product over a unique-product quotient, then kill every rational character with two positive relations of opposite exponent sign
target: rips-segev-cores-have-no-infinite-cyclic-quotient
requires: [rips-segev-core-large-gap-two-layer-elements-are-regular, rips-segev-port-data-cannot-exclude-balanced-divisors]
---

**Conventions.**  As in `rips-segev-core-large-gap-two-layer-elements-are-regular-proof`.
- `F = <a> * <b>`, `Gamma` a generalized Rips--Segev graph whose reduced labelling satisfies `Gr'_*(1/8)`, and
  `K = F / <<R>>` the core group.  `K` is torsion-free (Steenbock, Theorem "tf").
- A *positive relation* is `b a^{n_1} b a^{n_2} ... b a^{n_L} = 1` in `K`, with `L >= 1`.
- `S = {1, a, b, ab}`.

---

## Part 1. The fiber criterion

**Lemma 1.1.**  Let `G` be a group and `g != h` in `G` with `g^{-1} h` of infinite order.  Then for `c, d != 0`
in `k`, the element `c g + d h` is a non-zero-divisor in `k[G]`.

*Proof.*  `c g + d h = g (c + d t)` with `t = g^{-1} h`.  `g` is a unit.  `k[G]` is a free left and right
`k[<t>]`-module on coset representatives, and `k[<t>] = k[t^{±1}]` is a domain, so `c + d t` is regular. ∎

**Lemma 1.2 (fiber criterion).**  Let `G` be a group and `H_0 = <a, b> <= G`.  Suppose:
- the quotients `s^{-1} s'` for `s != s'` in `S`, namely `a, b, ab, a^{-1} b, b^{-1} a b`, have infinite order;
- there is a homomorphism `pi : H_0 -> Q` onto a nontrivial group `Q` with the unique product property.

Then every nonzero `beta in k[G]` with `supp beta ⊆ S` is a non-zero-divisor in `k[G]`.

*Proof.*
- *Reduction to `H_0`.*  Write `G = ⊔_j t_j H_0` (left cosets) and `α = sum_j t_j α_j` with `α_j in k[H_0]`.
  Then `α β = sum_j t_j (α_j β)`, with the summands supported in distinct cosets.  So `α β = 0` forces every
  `α_j β = 0`.  Right cosets handle `β α = 0` the same way.  It suffices to work in `k[H_0]`.
- *Fibers of `beta`.*  `pi` is nontrivial and `H_0 = <a, b>`, so `pi(a) != 1` or `pi(b) != 1`.  The fibers of
  `pi` on `S` have at most two points:
  - If `pi(a) = pi(b) = 1` then `pi` is trivial, excluded.
  - A fiber with three points `s, s', s''` needs two of the relations `pi(a) = 1`, `pi(b) = 1`, `pi(ab) = 1`,
    `pi(a) = pi(b)`, `pi(a) = pi(ab)` (that is `pi(b) = 1`), `pi(b) = pi(ab)` (that is `pi(a) = 1`).  Any two of
    them force `pi(a) = pi(b) = 1`.
- *Unique product.*  Suppose `α β = 0` with `0 != α in k[H_0]`.  Put `X = pi(supp α)` and `Y = pi(supp β)`, both
  nonempty and finite.  By the unique product property there are `x in X`, `y in Y` such that `xy` has exactly
  one expression as a product in `X · Y`.  Write `α_x`, `β_y` for the parts of `α`, `β` supported on
  `pi^{-1}(x)`, `pi^{-1}(y)`.  The part of `α β` on `pi^{-1}(xy)` is `α_x β_y`, so `α_x β_y = 0`.
- *Contradiction.*  `α_x != 0`, and `β_y` is a nonzero element supported on one or two points of `S`.  A monomial
  is a unit, and a two-point sub-sum is regular by Lemma 1.1.  So `α_x β_y != 0`.

The case `β α = 0` is identical with `y x`. ∎

**In `K`.**  The hypotheses on orders hold in `K`, and hence in every generalized Rips--Segev group, into which `K`
embeds (`rips-segev-groups-embed-every-torsion-free-group`).
- `K` is torsion-free (Theorem "tf") and has no unique products (Steenbock's main theorem, with `G_1 = <a>`,
  `G_2 = <b>`; see `rips-segev-groups-embed-every-torsion-free-group`).  Cyclic groups have unique products, so
  `K = <a, b>` is not cyclic.
- Hence `a != 1`, `b notin <a>` (so `b`, `ab`, `a^{-1} b` are nontrivial), and `b^{-1} a b != 1`.  Being
  nontrivial in a torsion-free group, all five have infinite order.

So: **if `K` had a nontrivial quotient with the unique product property, every element of `k[K]` (and of
`k[G(Gamma)]`) supported on `{1, a, b, ab}` would be regular**, balanced or not, of any rank.  The natural such
quotients are `Z` and, more generally, torsion-free abelian and locally indicable groups.  Part 2 rules them out.

---

## Part 2. No rational character

**Lemma 2.1.**  Let `phi : K -> Q` be a homomorphism to the additive rationals, `p = phi(a)`, `q = phi(b)`.  For
every positive relation `b a^{n_1} ... b a^{n_L} = 1`,

    L q + p (n_1 + ... + n_L) = 0.

*Proof.*  Apply `phi`. ∎

**Lemma 2.2.**  `b^L != 1` in `K` for `L >= 1`.  So in every positive relation the exponents `n_k` are not all
zero.

*Proof.*  `K` is torsion-free and `b != 1` (paragraph "In `K`" above). ∎

**Theorem 2.3.**  Suppose `K` has positive relations `P_1` and `P_2` whose exponent means `m_1 = (1/L_1) sum n_k`
and `m_2` differ.  Then `Hom(K, Q) = 0`.

*Proof.*  Lemma 2.1 gives `q = - p m_1` and `q = - p m_2`.  So `p (m_1 - m_2) = 0`, hence `p = 0`, hence `q = 0`.
Since `a, b` generate `K`, `phi = 0`. ∎

**Corollary 2.4 (endpoint hypothesis).**  Suppose every line endpoint position `0, C_i` of `Gamma` is both a source
and a target of `b`-edges.  Then `Hom(K, Q) = 0`.

*Proof.*
- By Part 1 of `rips-segev-port-data-cannot-exclude-balanced-divisors-proof`, the image of `Gamma` in `K` is a
  port configuration with offsets `(d_+, d_-) = (0, 0)`.
- The walk lemma (Lemma 2 of `rips-segev-core-large-gap-two-layer-elements-are-regular-proof`), clauses (i) and
  (iii), gives a positive relation `P_1` with all `n_k >= 0` and a positive relation `P_2` with all `n_k <= 0`.
- By Lemma 2.2 neither has all exponents zero, so `m_1 > 0 > m_2`.  Apply Theorem 2.3. ∎

**Corollary 2.5 (Steenbock's explicit graphs).**  For Steenbock's explicit families, directly: by Part 2 of
`rips-segev-port-data-cannot-exclude-balanced-divisors-proof`, the cycles of `x_2`-edges give positive relations
with all exponents `>= 99900` and the cycles of `x_1`-edges give positive relations with all exponents `<= -10`.
So `m_1 >= 99900 > -10 >= m_2`, and `Hom(K, Q) = 0`.  (They also satisfy the endpoint hypothesis.) ∎

**Consequences.**
- `H_1(K; Z) = K^{ab}` is a finitely generated abelian group with `Hom(K^{ab}, Q) = 0`, hence finite.
- `K` has no nontrivial homomorphism to a torsion-free abelian group: the image would be a nontrivial finitely
  generated torsion-free abelian group, which maps onto `Z`.
- `K` has no nontrivial homomorphism to a locally indicable group (the image is nontrivial and finitely generated,
  so it maps onto `Z`), nor to a bi-orderable group (bi-orderable groups are locally indicable).
- In a generalized Rips--Segev group `G(Gamma) = G_1 *_{<a>} K *_{<b>} G_2`, every homomorphism to a torsion-free
  abelian group kills `K`, hence `a` and `b`.  So Lemma 1.2 cannot be fed by a character of `G(Gamma)` either.

---

## Part 3. Calibration

- *`Gamma` without cycles.*  Then `K = F_2`, which has no positive relations, and `Hom(F_2, Q) = Q^2`.  Lemma 1.2
  with `pi : F_2 -> Z^2` reproduces the regularity of all elements on `{1,a,b,ab}` in `k[F_2]`.  Consistent.
- *Positive relations of one mean only.*  In `Z = <a, b | b a^{-1}>` the relation `b a^{-1} = 1` is positive with
  mean `-1`, and `phi(a) = phi(b) = 1` is a nonzero character.  So one positive relation, or several with equal
  means, does not suffice: Theorem 2.3 needs two different means.
- *Torsion.*  In `Z × Z/2 = <a> × <b | b^2>` the element `1 + b` is a zero divisor on `S`.  The criterion does not
  apply: Lemma 1.1 fails for `t = b` of order two.  Consistent.

---

## Part 4. What is killed, exactly

The class killed is: **"regularity of witness-support elements in `k[K]` by grading along a character, an abelian
quotient, or a locally indicable or bi-orderable quotient"**, and more broadly every reduction of the Kaplansky
problem for `K` to the kernel of a map `K -> Z`.
- It dies at Theorem 2.3: the endpoint structure of `Gamma` forces positive relations of both exponent signs.
- The one surviving form of the fiber criterion needs a nontrivial unique-product quotient `Q` of `K` with
  `Q^{ab}` finite.  None is known; torsion-free hyperbolic unique-product quotients in the sense of Delzant would
  qualify.
