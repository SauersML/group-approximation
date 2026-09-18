---
rg: 2
id: finite-index-odometer-near-shift-groups-pass-the-germ-gate
kind: claim
title: A fixed-base enumeration whose near shift group has finite index in the odometer Nekrashevych group gives a finitely presented shell germ group, and every fixed-base enumeration of a non-virtually-cyclic input must stretch
distinct_from:
  odometer-prefix-groups-have-fg-index-kernels: that proves B = V_(h,r)(<a>) is F_infinity with a finitely generated index kernel; this feeds those two facts into the shell germ gate, for every near shift group of finite index in B.
  fixed-base-shell-inputs-embed-in-odometer-rn-groups: that shows a fixed-base input embeds in B and has only finite Kazhdan subgroups; this identifies which fixed-base enumerations pass the germ gate outright, and proves they must use pieces of slope other than 1.
  fp-window-group-makes-shell-germ-group-fp: that reduces the gate to finite presentation of the window group; this gives a second sufficient condition, internal to B, that needs no window computation at all.
  a5-arithmetic-shell-envelope-is-not-finitely-presented: that kills one explicit fixed-base enumeration of A_5*A_5, whose near shift group acts on a tree and contains Z^infinity; this says what a successful fixed-base enumeration must do instead, namely generate a finite-index subgroup of B.
artifacts: []
---

**ESTABLISHED** by `finite-index-odometer-near-shift-groups-germ-gate-proof` (lane proof,
elementary given the cited nodes, not independently reviewed; no novelty claimed).

## Setting

Fix `h >= 2`, `r >= 1` and `B = V_(h,r)(<a>)`, acting faithfully on `N` by near
permutations as in `odometer-prefix-groups-have-fg-index-kernels`, with near index
`chi : B -> Z`. The cofinite shift `s : n -> n+1` is an element of `B` with `chi(s) = 1`:
on `n = r q + i` it moves root `i` to root `i+1` for `i < r-1`, and on root `r-1` it is
the odometer followed by the root change to `0`. Let `P` be infinite with finite
generating set `S`, and `nu` an enumeration satisfying the fixed-base hypothesis of
`fixed-base-shell-inputs-embed-in-odometer-rn-groups`: every `lambda_g`, `g in S`, lies in
`B` near infinity. Then `R_nu = <lambda(P), s>` is a subgroup of `B`.

## Statement

1. **Finite index passes the gate.** If `[B : R_nu] < infinity`, then `R_nu` is of type
   `F_infinity`, `ker(eta)` is finitely generated for the near index `eta = chi|R_nu`, the
   finite-window condition of `shell-ascending-gate-is-a-finite-window-inclusion` holds,
   and the shell germ group `Q_nu` and the fiber product `F_nu` are finitely presented.
2. **Stretching is forced.** If every `lambda_g`, `g in S`, has bounded displacement on
   `N` (`|lambda_g(n) - n| <= C` for all `n`), then `P` is virtually cyclic. Elements of
   `B` all of whose prefix-table pieces have slope 1 (input and output prefixes of equal
   length) have bounded displacement. So a fixed-base enumeration of an input that is not
   virtually cyclic uses, for some generator, a piece that changes prefix length.

## What this leaves as the target

A first positive germ-gate example for an input that is not virtually cyclic can be
sought entirely inside `B`: an input `P`, typically virtually free (fixed-base inputs have
no infinite Kazhdan subgroup), together with a free transitive action of `P` on `N` by
elements of `B`, such that `lambda(P)` and the shift generate a finite-index subgroup of
`B`. The explicit arithmetic enumeration of `A_5*A_5`
(`a5-free-product-has-simple-arithmetic-shell-envelope`) is fixed-base but its near shift
group acts on a tree and is not finitely presented, so it generates an
infinite-index subgroup. A successful enumeration has to break that level structure.

## Scope

- Item 1 is sufficient, not necessary.
- Nothing is claimed about finite presentation of the envelope `E_nu` itself.
- No enumeration with `[B : R_nu]` finite is exhibited here.
