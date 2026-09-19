---
rg: 2
id: saturated-group-hs-relator-defect-gap
kind: claim
title: A dimension-free normalized-HS relator defect gap for the saturated group
distinct_from:
  full-mf-radical-linear-relator-inequality: that is the established operator-norm inequality; this asks for the normalized Hilbert--Schmidt analogue, which the operator-norm statement does not give and which the sofic firewall shows cannot follow from full MF radical alone.
  full-mf-radical-hyperlinear-models-force-relator-outliers: that derives the forced spectral geometry of a hypothetical microstate sequence and stops there; this asks for the positive constant that such a sequence would violate.
  effective-transport-modulus: that asks for explicit operator-norm numbers on the literal group's displayed relators; this asks for a normalized Hilbert--Schmidt constant for the saturated group and does not ask for it to be computable.
artifacts:
  - research/artifacts/hs-defect-gap-and-padding-2026-09-07.md
  - non_mf_groups_exist.tex
---

Let `Q=<S|R>` be the finite presentation of
`defect-saturation-full-mf-radical`, and in normalized Hilbert--Schmidt norm
put

```text
D_2(U) = max_(s in S) ||U_s - I||_2,
d_2(U) = max_(r in R) ||r(U) - I||_2.
```

OPEN.  Prove that there is `eta>0`, independent of dimension, with

```text
D_2(U) >= 1  ==>  d_2(U) >= eta                        (HSG)
```

for every `d` and every `U in U(d)^S`.

## Attempts

**The operator-norm certificate is not enough.**
`full-mf-radical-linear-relator-inequality` gives `D_infty <= C d_infty`.
Combining `||a||_2<=||a||_op` and `||a||_op<=sqrt d ||a||_2` turns it into a
dimension floor, `d >= 1/(C^2 d_2(U)^2)` whenever `D_2(U)>=1`, and no more;
this is `hyperlinear-models-need-quadratic-dimension`.  Microstate
dimensions are unconstrained, so the floor is consistent with hyperlinearity.

**The compression proof does not transfer.**  For
`A_d=diag(-1,1,...,1)` one has `||A_d-I||_2=2/sqrt d -> 0` while
`||Ad(A_d)-id||` on `(M_d,||.||_2)` equals `2`, by testing on `E_12`.  So
Hilbert--Schmidt-small relator error does not make the conjugation operators
operator-norm close to the identity, which is what the Kazhdan projection
step needs, and the finite-corona argument cannot be repeated.

**No hypothesis-free version exists.**  `simple-sofic-total-mf-radical` gives
a countable simple sofic, so hyperlinear, group with total MF radical.  Any
proof of `(HSG)` must use structure of `Q` beyond `Res_MF(Q)=Q`.

**Localizing near the trivial tuple does not help.**  By
`padding-makes-local-hs-rigidity-global`, a dimension-free linear rigidity
estimate in any neighbourhood of the trivial tuple already implies the global
inequality `D_2 <= C d_2`, which contains `(HSG)` with `eta=1/C`.

**The literature needs an extra hypothesis.**  Dogon--Vigdorovich,
arXiv:2506.20843v2, Theorem 4.1, obtain non-hyperlinear groups only after
assuming Hilbert--Schmidt stability of the lattice; see
`dv-s-arithmetic-hs-stable-nonhyperlinear-extension`.
