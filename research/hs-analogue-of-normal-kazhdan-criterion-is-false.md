---
rg: 2
id: hs-analogue-of-normal-kazhdan-criterion-is-false
kind: claim
title: The normalized Hilbert--Schmidt analogue of the normal-Kazhdan compression criterion is false
distinct_from:
  hs-invisibility-inflation-no-go: that shows a criterion whose conclusion is Hilbert--Schmidt invisibility can never prove non-MF, by inflating any corona representation; this shows the criterion's group hypotheses do not obstruct Hilbert--Schmidt asymptotic representations at all, by exhibiting sofic models that keep the witness at distance root two.
  hyperlinear-killed-normal-kazhdan-mf-transfer: that assumes a tracial kill of the defect in the shadow of every operator-norm almost representation and concludes MF-radical membership; this shows that the tracial kill is not a consequence of the group hypotheses, since a genuine Hilbert--Schmidt asymptotic representation need not kill the defect.
  sofic-non-mf-witness: that is soficity and non-MF of the group W; this uses W's sofic models as a counterexample to a proposed two-norm criterion and asserts nothing new about W.
  binary-leavitt-unit-group-hyperlinear: that asks whether the Leavitt unit group is hyperlinear; this says that the compression criterion's hypotheses cannot decide any such question and says nothing about that group.
artifacts:
  - research/artifacts/finite-rank-compression-defect-dichotomy-2026-09-09.md
  - non_mf_groups_exist.tex
---

**ESTABLISHED.**  The manuscript's criterion (`normal-kazhdan-defect-non-mf`)
reads: if `L <= G` is Kazhdan, `K <| G` is Kazhdan, and `K <= D_G(L)`,
then every operator-norm asymptotic representation `(V_n)` of `G`
satisfies `||V_n(k) - 1|| -> 0` for `k in K`.  Consider the statement
obtained by replacing operator norm by normalized Hilbert--Schmidt norm
in both hypothesis and conclusion:

> (HS) if `||V_n(gh) - V_n(g) V_n(h)||_2 -> 0` for all `g, h in G`, then
> `||V_n(k) - 1||_2 -> 0` for all `k in K`.

**(HS) is false**, even when `K` is central of order two.  Witness: the
manuscript's group `W = Cl(X) x| V` with `L = Gamma = Z^3 x| SL_3(Z)`
(Kazhdan) and `K = <epsilon>`, `epsilon` the central involution of
`Cl(X)`.  Then `epsilon in D_W(Gamma)`, `K` is central, finite, hence
normal and Kazhdan, and `W` is sofic (`sofic-non-mf-witness`).  The
permutation matrices of a sofic approximation form a normalized-HS
asymptotic representation of `W`, and

```text
||V_n(epsilon) - 1||_2 -> sqrt 2 .                                     (HS1)
```

So the group-theoretic hypotheses of the criterion, compression plus a
normal Kazhdan subgroup of the defect, do not obstruct approximation in
normalized Hilbert--Schmidt norm; in particular they yield no soficity or
hyperlinearity obstruction for any group.  A two-norm obstruction must
add information beyond these hypotheses.

**Where operator norm enters.**  The criterion's first step, the
manuscript's Corollary on Hilbert--Schmidt collapse of the defect, uses
that conjugation by `V_n(u)` is an operator-norm asymptotic
representation on the coordinate spaces `(M_(d_n), ||.||_2)`; that is
what transports the Kazhdan projection of `V_n(L)` under the compressor.
Two-norm multiplicativity gives no such control:

```text
||diag(-1,1,..,1) - I||_2 = 2 / sqrt d -> 0,
||Ad(diag(-1,1,..,1)) - 1||_(B(M_d, ||.||_2)) = 2,                     (HS2)
```

the lower bound on the unit vector `sqrt d E_12`.  A concrete two-norm
asymptotic representation of `C_2` with this defect is
`V_d(a) = diag(i,1,..,1)`.

**What it does not say.**  It does not say `H = L_(F_2)(1,2)^x` is
hyperlinear or not, and it does not weaken `normal-kazhdan-defect-non-mf`
or `hyperlinear-killed-normal-kazhdan-mf-transfer`, whose hypotheses are
about operator-norm almost representations.  It is also consistent with
`hs-invisibility-inflation-no-go`: that node says two-norm invisibility
can never *prove* non-MF, this one says two-norm invisibility does not
even *follow* from the group hypotheses.

**Manuscript.**  The remark following the soficity proof of `W` in
`non_mf_groups_exist.tex` (commit `4e3024d36`) records `(HS1)` and the
consequence that no sofic or hyperlinear version of the criterion follows
from its hypotheses.

Derivation: `hs-analogue-of-normal-kazhdan-criterion-is-false-proof`.
