---
rg: 2
id: matricially-stable-groups-have-central-eigencorners-proof
kind: route
title: Lift the corona representation to exact representations, where the central element is exactly central, and take shrinking spectral projections along a subsequence
target: matricially-stable-groups-have-central-eigencorners
requires:
  - dadarlat-matricial-stability-obstruction
---

Notation as in the target.  The quotient map is `(x_n) -> [x_n]`.  In `Q`,
`||[x_n]|| = limsup_n ||x_n||`.

**Step 1 (exact lifts).**  Enumerate `H = {h_1, h_2, ...}`.  By (L1) of
`central-eigencorners-die-over-full-radical-quotients-proof`, each
`Theta(h)` has a unitary lift `(phi_n(h))_n`.  Choose one for each `h`, with
`phi_n(e) = 1`.  Since `Theta` is a homomorphism, for all `g, h`

```text
||phi_n(g) phi_n(h) - phi_n(gh)|| -> 0,
```

so `(phi_n)` is an asymptotic homomorphism `H -> U(k_n)`.  By matricial
stability, in the sense recorded verbatim in
`dadarlat-matricial-stability-obstruction` (not necessarily separating,
pointwise in operator norm), there are homomorphisms `psi_n : H -> U(k_n)`
with `||psi_n(h) - phi_n(h)|| -> 0` for every `h`.  Hence
`Theta(h) = [psi_n(h)]` for all `h`.

**Step 2 (exact centrality).**  Put `U_n = psi_n(c)`.  Since `c` is central
and `psi_n` is a homomorphism, `U_n` commutes with `psi_n(H)`.  So every
spectral projection `1_S(U_n)`, for `S` a Borel subset of the circle, lies
in `psi_n(H)'`.  Put `u = Theta(c) = [U_n]`.

**Step 3 (the spectrum of `u` is seen along a subsequence).**  Let
`lambda in sp(u)`.  We claim `liminf_n dist(lambda, sp(U_n)) = 0`.
Suppose instead that `dist(lambda, sp(U_n)) >= d > 0` for all `n >= n_0`.
The `U_n` are normal, so `||(U_n - lambda)^(-1)|| <= 1/d` for those `n`.
Then `[(U_n - lambda)^(-1)]` (with `0` for `n < n_0`) is a bounded element of
`Q` that inverts `u - lambda`.  This is a contradiction.

So there are `n_1 < n_2 < ...` and points `mu_j in sp(U_(n_j))` with
`|mu_j - lambda| < 1/j`.

**Step 4 (the corner).**  For `n = n_j` let `E_n = 1_(S_j)(U_n)`, where
`S_j` is the open disc of radius `2/j` about `lambda`.  For other `n` let
`E_n = 0`.
- `E_(n_j) != 0`, since `mu_j in S_j ∩ sp(U_(n_j))`.  So `||E_(n_j)|| = 1`
  for all `j`, and `P = [E_n]` is a nonzero projection in `Q`.
- By Step 2, `E_n psi_n(h) = psi_n(h) E_n` for all `n` and `h`.  So `P`
  commutes with every `Theta(h) = [psi_n(h)]`, that is, `P in B`.
- By the spectral theorem, `||(U_(n_j) - lambda) E_(n_j)|| <= 2/j -> 0`.  So
  `(u - lambda) P = [(U_n - lambda) E_n] = 0`, that is, `u P = lambda P`.

**Step 5 (`lambda != 1` is available).**  If `u != 1`, then `sp(u)` is not
`{1}`, since a unitary with spectrum `{1}` is `1`.  So some
`lambda in sp(u)` has `lambda != 1`, and Step 4 applies to it.

The only input beyond elementary spectral theory is the lifting of Step 1.
