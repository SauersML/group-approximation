---
rg: 2
id: binary-leavitt-minimal-almost-periodicity-proof
kind: route
title: Kill one Thompson swap and use characteristic-two normal generation
target: binary-leavitt-unit-group-is-minimally-almost-periodic
requires:
  - leavitt-gl-equals-el-and-perfect-unit-group
  - leavitt-cylinder-swaps-generate-thompson-in-el
  - thompson-v-has-no-nontrivial-fd-unitary-representation
  - char-two-basis-swap-normally-generates-elementary-group
---

Let `rho:Q -> U(d)` be a finite-dimensional unitary representation, where
`Q=L_(F_2)(1,2)^x`.

By `leavitt-gl-equals-el-and-perfect-unit-group` and the prefix-code
self-similarity, choose a complete code `C` with at least three leaves and
identify `Q` with `E_C(L) ~= E_n(L)`, `n>=3`.  Under this identification the
basis transposition `tau_12` is the cylinder swap of the first two leaves.
By `leavitt-cylinder-swaps-generate-thompson-in-el` it belongs to the embedded
copy of Thompson's `V`.

The restriction of `rho` to that `V` is trivial by
`thompson-v-has-no-nontrivial-fd-unitary-representation`; hence
`rho(tau_12)=1`.  Therefore the kernel of `rho` contains the normal closure of
`tau_12`.  The characteristic-two calculation
`char-two-basis-swap-normally-generates-elementary-group` identifies that
normal closure with all of `E_n(L)`.  Thus `ker(rho)=Q`, so `rho` is trivial.
