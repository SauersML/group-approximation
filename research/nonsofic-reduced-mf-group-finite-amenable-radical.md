---
rg: 2
id: nonsofic-reduced-mf-group-finite-amenable-radical
kind: claim
title: Some nonsofic group has MF reduced C-star algebra and finite amenable radical
distinct_from:
  kt-double-reduced-cstar-is-mf: that is one instance, the q=2 Kun--Thom double, whose amenable radical is trivial; this allows any nonsofic group with finite amenable radical, where the reduced trace need not be unique.
  hyperlinear-nonsofic-group: that is the Pestov 3.4 separation target; this is a sufficient operator-norm input for it, through reduced-mf-finite-amenable-radical-is-hyperlinear.
---

**OPEN.**  Exhibit a countable nonsofic group `G` such that `C*_r(G)` embeds
into a norm matrix corona and `R_a(G)` is finite.

By `reduced-mf-finite-amenable-radical-is-hyperlinear` such a group is
hyperlinear and nonsofic.  This is therefore the reduced-norm form of the
MF-versus-soficity separation, lifted one level above the settled operator-MF
separation `weak-mf-does-not-imply-sofic`.

## Attempts

* **Kun--Thom double.**  Live, recorded at `kt-double-reduced-cstar-is-mf`
  together with its quantitative constraints (KRC1)--(KRC3).  Reduced MF passes
  to reduced algebras of subgroups, so it already needs `C*_r(G)` MF for
  `G = EL_r(F_2[x^(+-1)]) rtimes SL_d(Z)`, hence `C*_r(SL_d(Z))` MF for some
  `d >= 3`.  Magee--de la Salle (arXiv:2312.03220, C. R. Math. 362 (2024)
  903--910) prove that every finite-dimensional unitary representation of
  `SL_4(Z)` has a nonzero `SL_2(Z)`-invariant vector.  So for `d >= 4` no
  sequence of genuine representations can supply the vertex models; approximate
  models are not excluded, and the case `d = 3` is untouched by that argument.
* **Kazhdan gate, all criteria.**  By `reduced-mf-kazhdan-subgroup-gate`, any
  group produced by Kun--Thom Theorem A or the expander-matching criterion
  first needs an infinite Kazhdan group with MF reduced algebra
  (`infinite-kazhdan-group-with-mf-reduced-cstar`, open, with no known example).
  Changing the nonsofic group within these mechanisms cannot avoid it.
* **Fournier-Facio group.**  Dead: every norm-corona representation is trivial
  (`fournier-facio-asymptotic-representations-trivial`).
* **Leavitt unit groups.**  Dead: the binary Leavitt unit group and all its
  matrix ranks have full MF radical (`binary-leavitt-all-ranks-full-mf-radical`),
  and reduced MF implies operator MF.
* **Commuting-lamp and Clifford Kun--Thom extensions.**  Dead: not operator MF
  (the corresponding rows of `nonsofic-mechanism-mf-classification`).
* **Genuine-representation models of any kind.**  Dead:
  `pure-mf-conventions-imply-sofic`.
* **Descending from the full group C-star algebra.**  Dead for every group
  carrying a strict Kazhdan compressor
  (`maximal-group-cstar-infinite-under-strict-compression`).  Every nontrivial
  application of the known nonsoficity criteria carries one.  An infranormal
  subgroup normalized by all of its compressors is normal.  In the
  expander-matching criterion, a nonstrict `t_1` forces `J <= Gamma cap J = 1`.
