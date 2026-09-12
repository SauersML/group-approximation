---
rg: 2
id: diagonal-leavitt-models-have-external-commutant-excess
kind: claim
title: Diagonal Leavitt embeddings retain an extra commutant at distance one in every finite tracial extension
distinct_from:
  leavitt-root-fixed-projections-equal-the-global-fixed-projection: That identifies left fixed projections and character weights inside the represented group algebra; this concerns conjugation-invariant operators in an external tracial algebra and preserves the regular character throughout.
  frozen-leavitt-curvature-has-no-small-invariant-hull: That obstructs reducing containment of a sparse relator error in exact finite-factor models; this is an exact commutant obstruction in a tensor-square group algebra and in every further finite extension.
artifacts:
  - research/artifacts/leavitt-diagonal-external-commutant-obstruction-2026-09-08.md
---

Let `H=L_(F_2)(1,2)^x=GL_4(R)`, with native subgroups

```text
L={diag(g,1):g in EL_3(R)},
K={diag(I_3,k):k in R^x}.
```

Put `N=L(H)`, `A=L(L)`, `B=L(K)`, and let
`Delta:N -> M=N tensor N` be the diagonal embedding
`Delta(lambda_g)=lambda_g tensor lambda_g`. Then

```text
Delta(A)' intersect M = B tensor B,
Delta(N)' intersect M = C.
```

For every `k in K\{1}`, set `x=lambda_k tensor I`. In every finite
tracial extension `Q` of `M`, define

```text
D_Q=Delta(B) join (Delta(N)' intersect Q).
```

The unitary `x` commutes with `Delta(A)`, but

```text
E_(D_Q)(x)=0,       dist_2(x,D_Q)=1.
```

If `H` is hyperlinear, this example occurs inside a matrix tracial
ultraproduct, and hence inside the hyperfinite factor's tracial
ultrapower. Tensor-square microstates realize `M` and preserve the
frozen `C_3` and `C_2^3` profiles, while increasing every HS word
defect by at most a factor two.

Thus a universal external identification, or a zero-error quantitative
replacement, of the left commutant by the native right algebra and
the whole-group ambient commutant is incompatible with the existence
of an embedding. This does not exclude selecting a special embedding,
and does not prove nonhyperlinearity.
