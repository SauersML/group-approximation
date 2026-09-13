---
rg: 2
id: toeplitz-ring-has-infinite-middle-mf-regime-proof
kind: route
title: Proof that the Toeplitz-Jacobson algebra has an infinite middle MF regime
target: toeplitz-ring-has-infinite-middle-mf-regime
requires:
  - mf-rigidity-is-monotone-in-matrix-rank
artifacts:
  - research/artifacts/un-open-2-mf-spectrum-2026-09-13.md
---

Two facts come from `non_mf_groups_exist.tex` on main; lane `un-calibration` isolated this example as row 11
of its table.

- Tex l.1122-1125, verbatim: "The Toeplitz--Jacobson algebra $J=\F_2\langle s,t\mid ts=1\rangle$ has
  $1-st\ne0$ of order two, while $J/J(1-st)J\cong\F_2[z,z^{-1}]\ne0$, so $1-st$ is not full ...
  Proposition~\ref{prop:torsion-defect-ring} shows that $\EL_n(J)$ is not MF for $n\ge4$".
- Tex l.1143-1148, verbatim: "the quotient $\EL_n(\F_2[z,z^{-1}])$ is residually finite, so MF, and
  \[ \Rad_{\mathrm{MF}}(\EL_n(J))=\EL_n(J,JeJ)\cong\bigcup_N\mathrm{SL}_N(\F_2) \qquad(n\ge4)".

**`mf(J) <= 3`.** By the first quotation `EL_4(J)` is not MF, so `4 > mf(J)` by
`mf-rigidity-is-monotone-in-matrix-rank`, that is `mf(J) <= 3`.

**`rig(J) = infinity`.** It suffices that no `EL_N(J)`, `N >= 2`, is MF-rigid. The ring surjection
`J -> J/JeJ = F_2[z, z^(-1)]` induces a group surjection `EL_N(J) -> EL_N(F_2[z, z^(-1)])` for every
`N >= 2`. The target is nontrivial, since `F_2[z, z^(-1)] != 0` gives `e_12(1) != I` there, and it is a
finitely generated linear group over a finitely generated commutative ring, hence residually finite by
Malcev's theorem, hence MF. For `n >= 4` the second quotation states this residual finiteness and the
resulting proper MF radical directly. So for every `N >= 2` the group `EL_N(J)` admits a nontrivial
homomorphism to an MF group, and is not MF-rigid.

**Conclusion.** `mf(J) <= 3 < infinity = rig(J)`, so by the three-regime corollary of
`mf-rigidity-is-monotone-in-matrix-rank` every rank `N >= 4` lies strictly between the thresholds: `EL_N(J)`
is not MF and has a nontrivial MF quotient.

Malcev's theorem is recalled rather than imported from a source. For the ranks `n >= 4` this is not needed,
since the manuscript states the residual finiteness of `EL_n(F_2[z,z^{-1}])` itself; only the ranks `N = 2`
and `N = 3` of the `rig(J) = infinity` statement rest on the recalled form, and they are not used in the
conclusion, which concerns `N >= 4`.
