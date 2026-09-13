---
rg: 2
id: artin-k4-mixed-dead-character-is-outside-sigma1
kind: claim
title: "Test case for the Sigma^1-conjecture: the dead character (1,1,-1,-1) of the four-vertex Artin group K with cross labels 4,4,4,6 lies outside Sigma^1"
---

`K`, `χ` as in `artin-k4-dead-cut-admits-no-nonzero-dead-edge-ring`:
`A_K = <u1, u2, v1, v2 | [u1,u2], [v1,v2], (u1v1)^2 = (v1u1)^2, (u2v1)^2 = (v1u2)^2,
(u2v2)^2 = (v2u2)^2, (u1v2)^3 = (v2u1)^3>`, with `χ = (1, 1, -1, -1)`.

**Claim.** `[χ] ∉ Σ^1(A_K)`, i.e. `ker χ` is not finitely generated.

The Σ¹-conjecture predicts this. A proof that `ker χ` IS finitely generated would
refute the conjecture. `A_K` is 2-dimensional (no spherical triangle), so it satisfies
the `K(π,1)`-conjecture.

## Attempts

- Dead-edge rings and finite abelian twists: impossible,
  `artin-k4-dead-cut-admits-no-nonzero-dead-edge-ring`.
- Quotients through which `χ` factors (Almeida's Lemma 2.14 moves; killing `u1u2^{-1}`,
  `u1v1` or `u2v2`) all give characters that are in `Σ^1`. Identifying `u1 = u2` merges
  the cross labels `4, 6` at `v2` into `gcd = 2`. Killing `u2v2` makes `u2` central with
  `χ(u2) != 0`. So no known quotient obstruction applies.
- Reidemeister–Schreier with `τ = u1`, `g = u2 u1^{-1}`, `x1 = u1v1`, `x3 = u2v2`: `g` is
  `τ`-invariant; `[v1,v2] = 1` solves `x3` at each level in terms of lower data and `x1`
  at that level; but `x1` at level `i+1` is tied to lower levels only by quadratic
  relations (`x1_{i+1}^2 = x1_i^2`, `(g x1_{i+1})^2 = (x1 g)^2`-type). This suggests that
  `ker χ` is infinitely generated, as for the dihedral group `<x, u | [u, x^2]>`. It is
  not a proof.
- Open next: a module witness (artifact §4, Remark ii). It needs a left
  `R((t))`-module `M` and `λ != 0` with `S_2(ρ(u_i v_j)) (t ρ(u_i) - 1) λ = 0` on the three
  label-4 edges and `S_3(ρ(u1 v2)) (t ρ(u1) - 1) λ = 0`. A common eigenvector of `ρ(u1)`
  and `ρ(u2)` cannot work (checked), so `λ` has to mix the eigenspaces of the commuting
  pair `ρ(u1), ρ(u2)`.
