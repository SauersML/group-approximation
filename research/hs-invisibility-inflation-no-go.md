---
rg: 2
id: hs-invisibility-inflation-no-go
kind: claim
title: Hilbert--Schmidt invisibility alone never obstructs MF
distinct_from:
  trace-blindness-sharpness: that claim concerns which weak-MF data a trace can see in the free-lamp models; this one is the universal inflation construction showing that normalized-HS invisibility of the whole group is compatible with a faithful corona representation.
  finite-quotient-blindness: that claim is about exact finite-dimensional representations; this one is about the normalized Hilbert--Schmidt seminorm of a corona representation.
artifacts:
  - non_mf_groups_exist.tex
---

If a countable group `H` has a faithful corona representation on dimensions
`(m_n)`, then for any `N_n` with `m_n / (m_n + N_n) -> 0` it has a faithful
corona representation on dimensions `d_n = m_n + N_n` in which **every**
element is invisible in normalized Hilbert--Schmidt norm:
`‖Theta(h) - 1‖_2 = 0` for all `h in H`, while
`‖Theta(h) - 1‖_op` is unchanged.

Consequences.

- No criterion whose conclusion is `‖Theta(x) - 1‖_2 = 0` for some
  `x != 1`, in every corona representation, can prove non-MF-ness — however
  strong the group-theoretic hypotheses on `x` and on `H`.  Kazhdan
  transport must therefore always be followed by a **renormalization of the
  trace on a corner** cut by a projection commuting with the image.  Three
  sources of such a projection are known: averaging over a finite normal
  subgroup, the spectral projection of a finite-order central mark
  (`corona-corner-detection-criterion`), and the Kazhdan fixed-space
  projection of a normal property-(T) subgroup, which is invariant precisely
  because the subgroup is normal (`normal-kazhdan-defect-non-mf`).  Only the
  third avoids torsion.
- This is the precise asymmetry with soficity.  A sofic approximation
  measures its multiplicativity defect and its separation in the same
  Hamming metric, so a nontrivial invisible element contradicts soficity
  outright, with no torsion, corner, or spectral input.  MF measures the
  defect in operator norm and separation in operator norm, while transport
  concludes only in the (strictly weaker) normalized Hilbert--Schmidt norm.
  Hence a torsion-free nonsoficity construction carries no formal
  information for this problem: whatever torsion the nonsofic
  constructions use, it is not used to cross a metric gap, because on the
  sofic side there is none to cross.
