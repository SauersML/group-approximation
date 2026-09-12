---
rg: 2
id: sl3-double-swap-involution-is-outlier-carried
kind: claim
title: At a prime at least 11 the swap involution of the arithmetic double lives only on lattice outliers
distinct_from:
  arithmetic-double-swap-extension-is-binary-coset-wreath: that identifies the swap extension E with the binary coset wreath, exhibits the fold mark w = [h,s], and ends by observing that excluding its canonical microstates is exactly the original problem; this runs the large-prime sector machinery on the swap involution and proves the exclusion holds UNCONDITIONALLY on the whole Lambda-exact face, confining the problem to uniform lattice outliers.
  homogeneous-quotient-ce-forces-sl3-outlier-at-large-primes: that isolates the outlier obstruction for Connes embeddings of the homogeneous-quotient crossed product, whose microstates carry the K-orbit cell structure; this isolates the same obstruction for canonical microstates of the double-swap group E_p, a finitely presented GROUP witness, where the carried structure is one balanced central involution instead of a cell family.
  odd-congruence-lambda-exact-sector-collapses: that is the coprime-sector collapse consumed here as an input; this is its application to the swap involution of E_p together with the depth-free and robustness theorems, producing the outlier confinement of a specific finitely presented group's canonical microstates.
---

Fix a prime `p >= 11`, `Lambda = SL_3(Z)`, `Gamma = SL_3(Z[1/p])`,
`h = diag(p, 1, 1/p)`, and the double-swap group of
`arithmetic-double-swap-extension-is-binary-coset-wreath` instantiated at
this pair:

```text
E_p = < Gamma, s | s^2 = 1, [s, lambda] = 1 (lambda in Lambda) >
    = Gamma *_Lambda (Lambda x C_2),
```

finitely presented (`Gamma` is finitely presented, `Lambda` finitely
generated).  Write `w = h s h^(-1) s`, the fold mark; `w != e` and the
canonical (regular) character of `E_p` has `delta(w) = 0`.

**THEOREM (established here; proof in
`sl3-double-swap-outlier-confinement-proof`).**  Let `phi_n : E_p ->
U(d_n)` be any hyperlinear approximation of `E_p` (canonical character).
Then the restrictions `phi_n|_Lambda` are, along the ultrafilter, uniform
outliers of `SL_3(Z)`: they stay at distance bounded below (normalized HS,
flexibly, on a fixed generating set) from EVERY genuine finite-dimensional
unitary representation of `SL_3(Z)`.  Equivalently: the swap involution
cannot ride on the `Lambda`-exact face -- if the lattice restriction of a
canonical `E_p`-microstate sequence were asymptotically genuine, the
coprime-sector collapse (after the depth-free emptying of the p-divisible
sector and the robustness absorption) would force the involution into the
commutant of the whole of `pi(Gamma)`, giving the fold mark trace `1`
against its canonical value `0`.

**What this changes.**  The double-swap node closed with: excluding the
canonical microstates of `E` is exactly the original non-hyperlinearity
problem.  At `p >= 11` that is no longer the full truth: the exclusion is
now proved on the entire `Lambda`-exact face with NO stability input, so
what remains of the original problem is exactly its outlier sector.  The
group `E_p` (equivalently the double `D_p = Gamma *_Lambda Gamma`, by the
swap identification) is non-hyperlinear if and only if no uniform lattice
outlier carries the balanced free involution -- the open leaf
`sl3-outliers-carry-no-balanced-free-involution`, which is implied by
`sl3-z-weakly-ucp-stable`. It asks for a more restricted exclusion than
stability; no converse or strict separation has been proved.

## Attempts

- **Does the confinement extend to small primes?**  Not with the present
  inputs: the depth-free constant `a_p = min(4c_p - 3, 1/3)` is positive
  only for `p >= 11`, and at `p in {2, 3, 5, 7}` the p-divisible
  `Lambda`-exact sector is only confined to ultra-deep towers
  (`lambda-exact-p-divisible-sector-is-ultra-deep-or-negligible`), so at
  small primes the involution may also ride deep towers, and the honest
  statement is "outlier or ultra-deep".  The `k`-fold-twist extension
  note on the depth-free node is the recorded route to `p = 5, 7`.
