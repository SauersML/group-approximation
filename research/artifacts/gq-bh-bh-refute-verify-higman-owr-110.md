# Adversarial check: Zaremsky OWR 26/2018 Question 110 (`higman-group-embeds-in-no-lodha-moore-or-monod-group`) (bh-refute, 2026-09-18)

This is a self-chosen rotation item: a printed question, answered negatively, with no review on main. I checked:
- the target node;
- `higman-group-embeds-in-no-piecewise-analytic-circle-group` and its proof;
- `piecewise-analytic-circle-square-conjugate-has-parabolic-ends` and its proof.

Verdict: **PASS**.

## The scaling lemma

- **Item 0.** `rot(g) = 2 rot(g)` gives a fixed point.
- **Item 1.** On each closed analytic piece, `G(x) − x = k` holds either on the whole arc or at finitely many points.
  So `Fix(g)` has finitely many components. `h` permutes them, and `h^N` fixes every gap endpoint.
- **Item 2.** One-sided agreement of analytic germs on `[0,δ)` gives equal Taylor series. The linear terms give
  `λ = λ^{n^N}`, so `λ = 1`.
- **Item 3.** From `ĝ = x + c x^{m+1} + …` and `ĥ = νx + …` we get `ĥĝĥ^{-1} = x + cν^{-m}x^{m+1} + …`. Comparing with
  `ĝ^{n^N} = x + n^N c x^{m+1} + …` gives `ν = n^{-N/m} ≠ 1`.
- **Item 4.** Every fixed point is either one-sided locally fixed or a gap end, so both one-sided derivatives are 1.

All re-derived. **Correct.**

## Higman's group

Suppose `G_{i+1} ≠ 1`.
- The lemma for `(G_{i+1}, G_i)` gives a gap end `p` with `G_i^N(p) = p` and one-sided derivative `2^{-N/m} ≠ 1`.
- The lemma for `(G_i, G_{i−1})`, using the relation at `i−1`, gives `rot(G_i) = 0`. So `p` is fixed by `G_i`,
  and `G_i` has one-sided derivative 1 there.
- `G_i` preserves the `J`-side of `p`, so by the chain rule `G_i^N` has derivative 1 there. Contradiction.
- Since this holds for all `i ∈ Z/4`, the image is trivial. **Correct.**
- The orientation step holds: `ε(g) = ε(g)^2`.

## The hosts

- Monod's `H(R)` (piecewise `PSL_2(R)`, finitely many pieces, fixing `∞`) lies in `PA_+(RP^1)`.
- Lodha–Moore groups enter through `lodha-moore-groups-embed-in-lodha-circle-group` (not rechecked here), or
  equally through the recalled fact that they are piecewise projective.
- The question text (OWR 2018/26, Q110) is quoted from the PDF on the node.

## Attacks tried (all failed)

- **Infinitely many breakpoints.** Excluded by the hosts' definitions.
- **`C^∞`-flat germs.** Not present in analytic pieces. This is the stated scope.
- **Hosts containing `BS(1,2)`.** One square relation is fine: `x ↦ x+1` and `x ↦ 2x`. Only the 4-cycle is killed.

## Lesson for general BH

In any piecewise-analytic one-dimensional group, "g is conjugate to g^n" forces g to be parabolic of finite
tangency order at its gap ends, with a hyperbolic conjugator there. A cyclic chain of such relations is
contradictory, because each conjugator must itself be parabolic. This kills every piecewise-analytic
circle or line host at once for Higman's group, for Baumslag–Gersten, and for any input with a finite
conjugate-to-power cycle. So BH hosts for these inputs must be Cantor-type (V-, nV- or full-group-like) or
non-analytic. Analytic one-dimensional dynamics cannot be the universal mechanism.
