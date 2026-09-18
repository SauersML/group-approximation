---
rg: 2
id: rational-function-field-crossed-products-have-the-rank-condition
kind: claim
title: Every skew group ring of any group over a rational function field in finitely many variables over a prime field has the rank condition, and is stably finite when the action is faithful
distinct_from:
  field-crossed-product-rank-condition-survival-cases: that needs an amenable quotient, algebraic coefficients, or an invariant measure on complex points; this needs no hypothesis on the group or the action and uses finite-field points, where birational maps are bijections off a thin set, instead of an invariant measure.
  virtually-hughes-free-field-crossed-products-are-stably-finite: that restricts the group (virtually locally indicable and similar) and allows any field; this allows any group, including Kazhdan groups, and restricts the field to finitely generated rational function fields with trivial cocycle.
  sofic-lamplighter-bernoulli-crossed-products-have-rank-models: that builds rank models for Bernoulli-type lamplighter crossed products from sofic approximations of the base group; this needs no approximation of the group, because the finite model comes from reducing the field modulo p.
---

**ESTABLISHED (unreviewed)** by [[rational-function-field-crossed-products-rank-condition-proof]].

Let `k` be `Q` or `F_p`, let `K = k(x_1, ..., x_n)` with `n >= 0`, let `G` be any group, and let `σ: G -> Aut(K)` be
any action. Write `K ⋊ G` for the skew group ring (trivial cocycle), `(a u_g)(b u_h) = a σ_g(b) u_{gh}`.

**Theorem 1 (rank condition).** If `A ∈ M_{d×r}(K ⋊ G)`, `B ∈ M_{r×d}(K ⋊ G)` and `AB = I_d`, then `r >= d`.

**Theorem 2 (stable finiteness).** If `σ` is faithful, then `AB = I_d` implies `BA = I_d` in `M_d(K ⋊ G)`.

**Local form of Theorem 1.** The same conclusion holds for `K' ⋊ G`, with `K'` any field, if for every finite
`E ⊂ K'` and finite `T ⊂ G` there is a subfield `K_0 ⊇ E` of the form `k(x_1, ..., x_n)` with `σ_g(K_0) ⊆ K_0`
for all `g ∈ T`.

**Mechanism.** Reduce modulo `p` and let `G` act by partial substitution on `F_q^n`. The model is exact at every
point where one fixed nonzero polynomial `D` does not vanish. So the rank defect of `AB = I_d` is at most
`d · deg(D) · q^{n-1}`, against `(d-r) q^n` (Schwartz–Zippel).

**Consequences for `some-field-crossed-product-fails-the-rank-condition`.**
- **Named next test case dies.** `Q(x,y) ⋊ SL_3(Z)` by projective substitutions satisfies the rank condition and
  is stably finite, as does every subgroup of the Cremona group `Bir(P^n_k)` acting on `k(x_1..x_n)`.
- **Survival regime (c) extended.** In regime (c) the invariant measure on complex points is not needed for
  rational function fields.
- **What a witness still needs.** At least one of the following:
  1. a nontrivial cocycle `α` that is not a coboundary on the finite models, as in the ternary Leavitt route,
     where `n = 0` and the obstruction is exactly the twist;
  2. coefficient orbits under finitely many `σ_g` that lie in no finitely generated rational subfield, as in
     Bernoulli shift fields `F_p(x_g)`;
  3. a non-rational finitely generated field. Here the same proof goes through once Lang–Weil point counts are
     imported (recorded under Remarks in the route, not established here).
