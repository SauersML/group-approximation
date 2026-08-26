---
rg: 2
id: intertwiner-retention-is-equivalent-to-hyperlinearity
kind: claim
title: Retained intertwiner sectors exist for some exact pairs exactly when the simple Leavitt quotient is hyperlinear, and by property (T) a retained sector must show its trace defect on a Kazhdan generating set
distinct_from:
  intertwiner-retention-makes-leavitt-quotient-hyperlinear: that is the implication from a retained sector to hyperlinearity; this adds the converse for freely chosen pairs (conjugation model), locating the whole content of the program in the Shulman pairs, and the (T) constraint that the defect is generator-visible.
  leavitt-presentation-double-positive-rank-retention: that is the open existence statement for the Shulman pairs; this explains why it is exactly a norm-to-trace transfer and sharpens what any solution must look like.
artifacts:
  - research/artifacts/hyperlinear-nonsofic-attack-notebook-2026-08-26.md
---

Notation of `intertwiner-retention-makes-leavitt-quotient-hyperlinear`:
`Q = F/K = EL_4(L_(F_2)(1,2))`, exact pairs `u_n, v_n : F -> U(d_n)`,
`Pi_n(f) = u_n(f) (x) conj(v_n(f))` on `HS(C^(d_n)) = C^(d_n) (x) conj(C^(d_n))`,
sectors `W_n` with projections `P_n`, rank `r_n`, normalized norm
`||.||_(2,r_n)`.

**Theorem.**
1. (Equivalence for free pairs.)  `Q` is hyperlinear iff there exist exact
   pairs `(u_n, v_n)` and sectors `W_n` satisfying (IR1)--(IR3).  For the
   converse direction take canonical microstates `sigma_n : Q -> U(d_n)`,
   let `u_n = v_n` be the exact representation of `F` sending a free basis
   to the `sigma_n`-images of its generators, and `W_n = HS(C^(d_n))`: then
   `Pi_n = Ad u_n`, (IR1) is exact, and
   `||(Pi_n(f) - 1)||_(2, d_n^2)^2 = 2 - 2 |tr u_n(f)|^2`, which tends to `0`
   for `f in K` and to `2` for `f notin K`.
2. (Where the content is.)  Hence the criterion carries no information
   beyond the choice of pairs.  The pairs supplied unconditionally by
   `leavitt-presentation-double-forces-restriction-instability` converge on
   `K` in **operator norm** and separate `f_0` in operator norm; the
   conjugation pairs of (1) converge on `K` only in normalized Hilbert--Schmidt
   norm.  `leavitt-presentation-double-positive-rank-retention` is therefore
   exactly the problem of extracting a positive-normalized-rank sector from
   operator-norm data -- the same shape as `mf-implies-hyperlinear` and its
   rank-profile obstruction, specialized to intertwiner spaces.
3. (Generator visibility.)  Let `S` be a finite generating set of `Q` with
   Kazhdan constant `kappa > 0`, lifted to `F`.  For any sectors satisfying
   (IR1)--(IR2), the sector characters
   `phi_n(f) = r_n^(-1) Tr(P_n Pi_n(f) P_n)` are positive-definite on `F`
   and asymptotically `K`-bi-invariant, and if
   `max_(s in S) ||(Pi_n(s) - 1) P_n||_(2,r_n) -> 0` then
   `||(Pi_n(f) - 1) P_n||_(2,r_n) -> 0` for every `f in F`.  Consequently
   (IR3) can only hold if
   `liminf_n max_(s in S) ||(Pi_n(s) - 1) P_n||_(2,r_n) > 0`: a retained
   sector displays its defect on the Kazhdan generators, and `f_0` in (IR3)
   may be taken to be a lift of a generator.

**Consequence for the search.**  Any construction of a retained sector must
start from operator-norm separation at the generators themselves
(`leavitt-presentation-double-forces-restriction-instability` gives it at
any chosen `f_0`, in particular at each generator lift) and must convert it
into a trace-visible defect at those same generators; sectors on which the
generators become almost trivial are worthless however `f_0` behaves.
