---
rg: 2
id: artin-k4-mixed-dead-character-is-outside-sigma1
kind: claim
title: "Test case for the Sigma^1-conjecture: the dead character (1,1,-1,-1) of the four-vertex Artin group K with cross labels 4,4,4,6 lies outside Sigma^1"
refuted_by: [artin-k4-odd-family-dead-characters-lie-in-sigma1]
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
- Locally finite shift quotients `ψ : A_K -> L ⋊ Z` (with `χ` the `Z`-coordinate; an
  infinite image of `ker χ` inside a locally finite `L` would prove the claim).
  - `L = ⊕_Z F` fails. `[u1, u2] = 1` with `ψ(u1) = a s`, `ψ(u2) = b s` reads
    `a_j b_{j-1} = b_j a_{j-1}` componentwise, and induction from the left gives
    `a = b`. Then `(xv)^2 = (vx)^2` and `(xv)^3 = (vx)^3` force `ψ(u1)`, `ψ(v2)` to
    commute, so `ψ` factors through the collapsed triangle, whose character is in
    `Σ^1`, and the image of `ker χ` is finite.
  - `L = FSym(Z)` with `p_j = (j j+1)` in the Reidemeister–Schreier coordinates of
    the dead-edge quotient `(u1v1)^2 = (u2v1)^2 = (u2v2)^2 = (u1v2)^3 = 1`, `g^2 = 1`
    fails. The needed order-3 elements `q_j` must commute with `p_j p_{j+1}` at every
    level, and the exponents cannot be matched along the chain.
- Open next: a module witness (artifact §4, Remark ii). It needs a left
  `R((t))`-module `M` and `λ != 0` with `S_2(ρ(u_i v_j)) (t ρ(u_i) - 1) λ = 0` on the three
  label-4 edges and `S_3(ρ(u1 v2)) (t ρ(u1) - 1) λ = 0`. A common eigenvector of `ρ(u1)`
  and `ρ(u2)` cannot work (checked), so `λ` has to mix the eigenspaces of the commuting
  pair `ρ(u1), ρ(u2)`.
- **2026-09-19 (swarm-0917-w15-z-break): REFUTED.**
  - The claim is false: `ker χ` is finitely generated. See
    `artin-k4-odd-family-dead-characters-lie-in-sigma1`.
  - The Novikov homology reduces to the left ideal
    `L = Σ N S_k(u_i v_j)(u_i - 1)`, using the two label-2 edges.
  - `L` contains a unit because `x^2 = S_3(x) - S_2(u1v1) + u1u2^{-1}(S_2(u2v1) - S_2(u2v2))`
    with `x = u1v2`.
  - The same identity with `T = Σ_{j<m} x^{2j}` works for every odd cross label
    `2q = 4m + 2`.
  - The case `q = 3` was found first by swarm-0917-w14-z-break (unlanded
    `artin-k4-mixed-dead-character-lies-in-sigma1`, a different identity). This lane
    refereed that route line by line and found no gap.
  - This also explains why every witness search above came back empty.
