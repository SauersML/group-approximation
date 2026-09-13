---
rg: 2
id: un-ladder-rf-rigidity-is-free-mf-rigidity-proof
kind: route
title: Perfectness plus simplicity of the central quotient give no finite quotients and no residually finite targets
target: un-ladder-rf-rigidity-is-free-mf-rigidity-is-dynamical
requires: []
artifacts:
  - research/artifacts/un-open-7-coarse-geometry-2026-09-13.md
---

Complete direct proof. Let `R` be unital, `n >= 3`, `G = EL_n(R)`, `Z = Z(G)`, and
assume `S = G/Z` is infinite and simple.

**1. `G` is perfect.** For pairwise distinct indices `i, j, l` (available since
`n >= 3`) the Steinberg commutator relation gives
`e_ij(r) = [e_il(r), e_lj(1)]`. The `e_ij(r)` generate `G` by definition, so
`G = [G, G]`.

**2. `G` has no nontrivial finite quotient.** Let `φ: G -> F` with `F` finite and
`K = ker φ`. The image `KZ/Z` is normal in `S`, so by simplicity it is trivial or `S`.

- If `KZ/Z = 1` then `K <= Z`, so `Z/K` is normal in `G/K` with quotient `G/Z = S`.
  Thus `S` is a quotient of the finite group `G/K ≅ φ(G)`, contradicting `S` infinite.
- Otherwise `KZ = G`, so `G/K = KZ/K ≅ Z/(Z ∩ K)` by the second isomorphism theorem,
  which is abelian. By step 1 `G` is perfect, so its abelian quotients are trivial and
  `φ(G) = 1`.

**3. Every homomorphism from `S` to a residually finite group is trivial.** Let
`φ: S -> H` with `H` residually finite. Since `S` is simple, `ker φ` is `S` (and `φ` is
trivial, as claimed) or trivial. Suppose it is trivial, so `S` embeds in `H`. Residual
finiteness passes to subgroups, so `S` is residually finite. Choose `s ≠ 1` in `S`; there
is `ψ: S -> F` with `F` finite and `ψ(s) ≠ 1`. Then `ker ψ` is a proper normal subgroup
of `S`, hence trivial by simplicity, so `S` embeds in the finite group `F`. This
contradicts `S` infinite. Hence `φ` is trivial.

**Model tests.**
- `S = PSL_2(F_p)` (finite simple) fails the hypothesis "infinite" and indeed has
  faithful finite and linear representations, so the hypothesis is load-bearing.
- `S = Z` is infinite but not simple as required (it is abelian, not perfect), and it is
  residually finite; again the hypotheses are load-bearing.
- `G = EL_3(LC(X,F_q) ⋊ Z)` (Pestov, measure side) and
  `G = EL_N(LC(∂F_d,k) ⋊ F_d)` (paradox side) both satisfy the hypotheses, which is the
  point: item 3 does not separate them.
