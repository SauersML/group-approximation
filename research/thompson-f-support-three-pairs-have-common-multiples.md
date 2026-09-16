---
rg: 2
id: thompson-f-support-three-pairs-have-common-multiples
kind: claim
title: In K[F], two nonzero elements whose supports have right translates with union of size at most three have a common right multiple, and no set of at most three monomials doubles
distinct_from:
  thompson-f-twisted-binomial-pairs-have-common-multiples: that settles pairs with at most two terms on each side; this settles every pair whose translated supports fit in three points, including a binomial against a trinomial and two trinomials with translated supports, and it obtains the two-term case by counting instead of comaximality.
  thompson-f-binomial-pairs-have-common-multiples: that uses Lyndon's relation sequence for 1 - h against binomials; this uses non-doubling of three-element sets and a dimension count, for all coefficients.
  thompson-f-every-twisted-binomial-is-ore-with-every-element: that asks 1 + lambda g against every nonzero b and is open; this settles, for every g ≠ 1 including multi-bump g, the trinomials b whose support contains a pair w, g w.
  thompson-f-amenable-iff-group-ring-is-ore: that is the equivalence of amenability with the Ore condition for all pairs; this proves the Ore condition unconditionally for pairs with small joint support.
  thompson-f-nonamenable-iff-some-monomial-set-doubles: that reduces non-amenability to doubling of some monomial set; this shows such a set has at least four elements.
artifacts:
  - research/artifacts/three-element-doubling-sets-2026-09-16.md
---

Let `K` be any field, `R = K[F]`, and `M` the positive monoid of Thompson's group `F`.

1. **Joint support three.** Let `a, b ∈ R` be nonzero. If `|supp(a) h_1 ∪ supp(b) h_2| <= 3` for some
   `h_1, h_2 ∈ F`, then `a R ∩ b R ≠ 0`. If `|h_1 supp(a) ∪ h_2 supp(b)| <= 3`, then `R a ∩ R b ≠ 0`.
2. **Cases** (all coefficients nonzero, otherwise arbitrary):
   - two elements with at most two terms each (a new proof of item 2 of
     `thompson-f-twisted-binomial-pairs-have-common-multiples`);
   - `a` with `supp a = {u, v}` against `b` with `supp b = {w_1, w_2, w_3}`, whenever
     `v u^-1 = w_j w_i^-1` for some `i ≠ j`. For such pairs this is exactly the hypothesis of item 1.
     Example: `1 + lambda g` against `mu + nu g + rho k`, for every `g ≠ 1` and `k ∉ {1, g}`, on
     both sides;
   - two trinomials with `supp b = (supp a) h` for some `h ∈ F`.
3. **Monomial sets.** Every `S ⊆ M` with `|S| <= 3` has a finite nonempty `Y ⊆ M` with
   `|S Y| < 2|Y|`. So `S` does not double in the sense of
   `thompson-f-nonamenable-iff-some-monomial-set-doubles`.

**Relation to the root.** By `thompson-f-amenable-iff-group-ring-is-ore`, `F` is not amenable iff some
pair `(a, b)` has `a R ∩ b R = 0`. Item 1 says every such pair has
`|supp(a) h_1 ∪ supp(b) h_2| >= 4` for all `h_1, h_2`. By item 3, every doubling set of monomials has
at least four elements. Item 3 of `three-element-doubling-sets-are-free-bases` shows that the bound
four cannot be improved using only the absence of free subgroups.

**Scope.**
- Item 1 holds in `K[G]` for every group `G` without non-abelian free subgroups whose group ring has
  no zero divisors; the only inputs about `F` are `thompson-f-has-no-free-subgroups` and
  `thompson-f-is-bi-orderable`.
- The multiplier comes from a kernel vector of `(u, v) -> a u - b v` on `K^Y ⊕ K^Y`, where `Y` is a
  non-doubling witness for the joint support. So the proof bounds the support of `u, v` by `|Y|`,
  but gives no explicit bound on `|Y|`.
- Pairs with joint support of size four are open in general; generic pairs in `P_(2,2)` have joint
  support nine.
- Systems of three or more elements are not covered, even with joint support three. Guba's `Q_k`
  (`k + 1` linear forms in `x_0, x_1, x_2`; see `thompson-f-rescaled-x0-binomials-have-common-multiples`,
  item 5) is such a system. The dimension count for `a_0 u_0 = ... = a_k u_k` needs
  `|S Y| < (1 + 1/k) |Y|`, and non-doubling gives only `|S Y| < 2|Y|`. So this claim does not touch
  the open candidate `Q_4`.
- Novelty is not claimed; this is a short consequence of item 2 of
  `three-element-doubling-sets-are-free-bases`.

Proof route: `thompson-f-support-three-pairs-have-common-multiples-proof`.
