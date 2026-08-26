---
rg: 2
id: kt-remainder-corner-characters-are-infinite-index-induced
kind: claim
title: Above the stable range, the remainder corner of any Kun--Thom model carries a compression-fixed mixture of characters induced from finite-dimensional representations of infinite-index non-central normal subgroups
distinct_from:
  kt-polynomial-hyperfinite-stability-misses-regular-wreath: that uses the Lavi--Levit classification to show the amenable characters of the polynomial elementary group are finite-dimensional and hence that it is hyperfinitely HS-stable; this uses the same classification on the non-amenable side, to identify the extremal components of the third corner of a model as infinite-index induced characters.
  kt-compression-fixed-tracial-states-are-atomic-or-regular: that is the open classification of compression-fixed tracial states; this reduces it, above the stable range, to the exclusion of compression-fixed mixtures of infinite-index induced characters, and records the two-line proof that such characters are weakly mixing and non-tempered.
  tempered-gamma-part-of-a-model-is-compressor-invariant: that constructs the three-corner decomposition for arbitrary pairs; this identifies the characters living on the third corner for the Kun--Thom subgroup by citation.
---

Let `R_+ = F_q[x_1, ..., x_d]`, `Gamma = EL_r(R_+)` with

```text
r > sr(R_+),   e.g.  r >= d + 2   (Bass: sr(R_+) <= dim R_+ + 1 = d + 1),
```

so that with `d = 3` one may take `r >= 5`; Kun--Thom's Theorem E allows any
`r, d >= 3`, so this is still a Kun--Thom pair.  Let `pi : G -> U(N)` be any
model of the pair (`G = EL_r(R) x| SL_d(Z)`), `1 = e (+) f (+) g` the
three-corner decomposition of
`finite-dimensional-gamma-part-of-a-model-is-compression-blind` and
`tempered-gamma-part-of-a-model-is-compressor-invariant`, and
`chi_g = tau(pi(.) g)/tau(g)` the character of `Gamma` on the remainder
corner `g = 1 - e - f` (assumed nonzero).

**Theorem.**  In the unique decomposition `chi_g = int chi_omega dmu(omega)`
into extremal characters, `mu`-almost every component has the form

```text
chi_omega = Ind_(N_omega)^Gamma sigma_omega,    chi_omega = 0 off N_omega,
```

with `N_omega` a normal subgroup of `Gamma` of **infinite index**, not
central, hence (Vaserstein's sandwich) containing `E_r(R_+, I_omega)` for a
nonzero ideal `I_omega` of infinite colength, and `sigma_omega` a
finite-dimensional representation of `N_omega`.  Each such component is
weakly mixing (no finite-dimensional subrepresentation) and non-tempered,
as the corner requires.  Moreover `chi_g` is fixed by every compression map
`phi_A^*` (`model-characters-of-compressed-pairs-are-compression-invariant`).

**Input.**  N. Lavi and A. Levit, *Characters of the group EL_d(R) for a
commutative Noetherian ring R*, arXiv:2007.15547: for `d > sr(R)` every
character of `EL_d(R)` is induced from a finite-dimensional representation
(of a normal subgroup, off which it vanishes -- the reading source-audited
in `kun-thom-hyperfinite-character-firewall-proof`, where their Corollary
1.3 is applied to amenable characters).  Cited at statement level; not
re-read in this session.

**What it changes.**  Above the stable range the open classification
`kt-compression-fixed-tracial-states-are-atomic-or-regular` is exactly the
statement that **no compression-fixed tracial state of `Gamma` is a
mixture of infinite-index induced characters**.  Two mechanisms are
available and both are recorded as untried: (i) substitution-invariance --
the support normal subgroups `N_omega` must be permuted by the compression
maps, and no substitution-invariant ideal of infinite colength has been
found; (ii) the finite-core constraint on the kernel of a criterion-form
model.  Either would empty the third corner for `r >= 5` and make the
abstract and canonical formulations of hyperlinearity of `W`, `E`, `D`
coincide.
