---
rg: 2
id: corona-finite-index-radical-heredity-proof
kind: route
title: Induce a corona representation to a block-monomial one and read the corner
target: corona-finite-index-radical-heredity
requires: []
artifacts:
  - GroupApproximation/Sofic/InducedCoronaMF.lean
  - GroupApproximation/Sofic/AmplifiedBlockNorms.lean
---

## Why sufficient

Fix left-coset representatives `r_1 = 1, ..., r_m` for `H` in `G`.  Each
`g in G` determines a permutation `sigma_g` of the indices and elements
`h_{g,i} in H` by `g r_i = r_{sigma_g(i)} h_{g,i}`, with the cocycle identity
`h_{g1 g2, i} = h_{g1, sigma_{g2}(i)} h_{g2, i}`.

Given `Theta : H -> U(Q_d)`, let `Ind Theta(g)` be the block matrix whose only
nonzero block in column `i` is `Theta(h_{g,i})` in row `sigma_g(i)`.  Every
row and column carries exactly one unitary block, so each `Ind Theta(g)` is
unitary; the cocycle identity makes `Ind Theta` multiplicative.  For fixed
`m`, a sequence of `m x m` block matrices is null in operator norm exactly
when each of its finitely many block-entry sequences is, so
`M_m(Q_d)` is again a norm matrix corona (dimensions `m d_n`) and
`Ind Theta` is an honest corona representation of `G`.

For `h in H` we have `sigma_h(1) = 1` and `h_{h,1} = h`, so the `(1,1)`-block
of `Ind Theta(h)` is exactly `Theta(h)`.  Hence if
`x in H intersect Rad_MF(G)` then `Ind Theta(x) = 1`, so reading the corner
gives `Theta(x) = 1`; as `Theta` was arbitrary, `x in Rad_MF(H)`.  The reverse
inclusion is the restriction of an ambient corona representation to `H`.

Both directions are kernel-level in
`InducedCoronaMF.corona_invisible_of_finiteIndex` and
`InducedCoronaMF.corona_invisible_restrict`, built on the block-pattern norm
estimates of `AmplifiedBlockNorms.lean`.  The induced family there is built on
the *lifts*, so the amplification isomorphism is never needed as a separate
step.

Replacing unitary blocks by invertible blocks over an arbitrary field, or by
`U(d)` blocks, gives the same argument for `Rad_lin` and `Rad_fd`; for the
finite residual, a finite quotient of `H` has its kernel's normal core of
finite index in `G`, which separates the same element.

## Priority

The *permanence* half — MF passes to and from finite-index subgroups — is
already recorded in the MF literature and should not be presented as new; the
faithfulness half is `InducedCoronaMF.isOperatorMF_of_finiteIndex_subgroup`.
What is added here is the **exact radical identity**, which is strictly more
than permanence: it pins the invisible subgroup of every finite-index
subgroup, not merely the truth value of MF.
