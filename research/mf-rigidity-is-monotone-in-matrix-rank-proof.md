---
rg: 2
id: mf-rigidity-is-monotone-in-matrix-rank-proof
kind: route
title: Proof that the MF ranks form a down-set and the MF-rigid ranks an up-set
target: mf-rigidity-is-monotone-in-matrix-rank
requires: []
artifacts:
  - research/artifacts/un-open-2-mf-spectrum-2026-09-13.md
---

Write `i: EL_N(R) -> EL_M(R)` for the top-left corner map `A |-> diag(A, I_(M-N))`, an injective group
homomorphism carrying `e_ij(r)` to `e_ij(r)`.

**Down-set.** `i` embeds `EL_N(R)` into `EL_M(R)`, and MF passes to subgroups (manuscript
`non_mf_groups_exist.tex` l.1080: "that group is not MF, and MF passes to subgroups"). So `EL_M(R)` MF
implies `EL_N(R)` MF.

**Normal generation.** For `a != b` in `{1,...,M}` put `w_ab = e_ab(1) e_ba(-1) e_ab(1) in EL_M(R)`. A
direct computation gives that `w_ab` acts on the `(a,b)` coordinate plane by `(x_a, x_b) |-> (-x_b, x_a)`
and as the identity elsewhere, so conjugation by `w_ab` sends `e_ij(r)` to `e_(i')(j')(±r)` where `i', j'`
are `i, j` with `a` and `b` interchanged. Transpositions generate the symmetric group on `{1,...,M}`, so
for every `i != j` there is a product `P` of such `w_ab` with `P e_12(r) P^(-1) = e_ij(±r)`. Since `r |-> -r`
is a bijection of `R`, the set of `EL_M(R)`-conjugates of `{ e_12(r) : r in R }` contains every `e_ij(r)`
with `i != j`, and these generate `EL_M(R)`. Because `N >= 2` we have `e_12(r) in i(EL_N(R))`, so the normal
closure of `i(EL_N(R))` in `EL_M(R)` is `EL_M(R)`.

**Up-set.** Let `phi: EL_M(R) -> H` be a homomorphism with `H` an MF group. Then `phi . i` is a
homomorphism from `EL_N(R)` to an MF group, hence trivial when `EL_N(R)` is MF-rigid, so
`i(EL_N(R)) <= ker phi`. As `ker phi` is normal in `EL_M(R)` it contains the normal closure of
`i(EL_N(R))`, which is `EL_M(R)`. So `phi` is trivial, and `EL_M(R)` is MF-rigid.

**Exclusivity.** If `EL_N(R)` were both MF and MF-rigid, the identity `EL_N(R) -> EL_N(R)` would be a
homomorphism into an MF group, hence trivial, so `EL_N(R) = 1`. But `e_12(1) != I` because `1 != 0` in `R`.

**Corollary.** The two monotonicity statements make `{N : EL_N(R) MF}` a down-set and
`{N : EL_N(R) MF-rigid}` an up-set, so they are the intervals `[2, mf(R)]` and `[rig(R), infinity)`, and
exclusivity gives `mf(R) < rig(R)`. A rank in the open interval between them is one where `EL_N(R)` is not
MF and not MF-rigid, so some nontrivial homomorphism to an MF group exists; its image is a subgroup of an
MF group and hence is itself a nontrivial MF quotient of `EL_N(R)`.

No hypothesis on `R` beyond `1 != 0` is used, and no property of MF groups beyond closure under subgroups.
