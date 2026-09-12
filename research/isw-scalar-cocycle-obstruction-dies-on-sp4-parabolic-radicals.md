---
rg: 2
id: isw-scalar-cocycle-obstruction-dies-on-sp4-parabolic-radicals
kind: claim
title: The scalar Ioana--Spaas--Wiersma cocycle mechanism cannot extend to either Sp4 parabolic radical
distinct_from:
  sp4-maximal-parabolics-contain-no-isw-affine-subgroup: that excludes the already-proved affine example as a subgroup; this audits a direct rerun of ISW Theorem A on the larger parabolic groups.
  sp2g-z-full-c-star-algebra-has-llp: this is a fence on one proof mechanism, not a proof of LLP for Sp4(Z).
---

Let `N_S = Sym^2(Z^2)` be the Siegel radical and `N_K = H_3(Z)` the
Klingen radical.  For either arithmetic semidirect product `P_i` in
`(SPF2)`, every scalar class in `H^2(P_i,T)` restricts to a Levi-invariant
class in `H^2(N_i,T)`.  The invariant subgroup is finite:

```text
H^2(N_S,T)^SL_2(Z) is finite,
H^2(N_K,T)^SL_2(Z) is finite.                            (ISC1)
```

Consequently there is no sequence `c_n in Z^2(P_i,T)` which converges
pointwise to `1` while every restriction `c_n|N_i` remains a
non-coboundary.  Thus the sequence required by Ioana--Spaas--Wiersma
Theorem A cannot exist for the relative pair `(P_i,N_i)`, even if one grants
relative property `(T)`.

This pinpoints why the standard alternating-area proof for
`Z^2 rtimes SL_2(Z)` does not transplant.  On the Siegel radical the
module is `Sym^2(Z^2)`, whose alternating square has no rational invariant
line.  On the Klingen radical the alternating area class of the abelianized
`Z^2` is already the coboundary defining the Heisenberg central extension.

The conclusion is limited to scalar cocycles and ISW Theorem A.  Their
operator-valued Theorem C can evade `(ISC1)`; applying it would require an
ergodic coefficient action, nontrivial operator-valued restriction classes,
and Connes-embeddability of every associated twisted crossed product.  None
of these data is constructed by the published parabolic argument.
