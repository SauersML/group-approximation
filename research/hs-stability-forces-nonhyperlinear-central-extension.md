---
rg: 2
id: hs-stability-forces-nonhyperlinear-central-extension
kind: claim
title: Hilbert-Schmidt stability plus property (T;FD) makes a finite central extension non-hyperlinear
artifacts:
  - research/artifacts/two-paper-ingestion-2026-08-19.md
distinct_from:
  mf-hyperlinear-of-finite-normal-quotient: that transports hyperlinearity along a finite normal quotient in the MF lane; this is the opposite direction, producing a finite central extension that fails hyperlinearity from a stability hypothesis on the base.
  finite-central-extension-rf-iff-virtually-splits: that characterizes residual finiteness of a finite central extension; this concerns hyperlinearity and consumes Hilbert-Schmidt stability, not residual finiteness.
  gohla-thom-stable-base-nonsofic-extension: that produces a nonsofic extension of a stable base in the permutation setting; this is the unitary/Hilbert-Schmidt statement and its conclusion is non-hyperlinearity of a finite central extension.
---

**Established by citation.**  Dogon--Vigdorovich, arXiv:2506.20843v2,
Theorem 1.1 (`thm:main-non-hyperlinear` in the source):

> Let `Gamma` be a group with property (T;FD).  Assume `Gamma` has a central
> extension of the form
>
> ```text
> 1 --> Z --> Gamma~ --> Gamma --> 1
> ```
>
> where `Gamma~` is a group with finite abelianization.  If `Gamma` is
> Hilbert--Schmidt stable, then there exists `N in N` such that the finite
> central extension
>
> ```text
> 1 --> Z/N --> Gamma~/(N.Z) --> Gamma --> 1
> ```
>
> is not hyperlinear.

Property (T;FD) is Lubotzky--Zimmer's: finite dimensional `Gamma`-representations
have uniform spectral gap.  It is strictly weaker than property (T), and the
theorem is stated for it precisely so that it reaches lattices without (T).

**Why this node exists.**  This is the theorem that converts a stability
result into a non-hyperlinear group, and the graph did not have it: the
`iwahori-*` lane attacks the stability side, while the conversion lived only as
prose inside `iwahori-sector-closure`.  It also generalizes the property (T)
version of Dogon (arXiv:2211.10492) that earlier lanes referred to informally.

**Shape of the argument, recorded because it constrains reuse.**  Assuming
`Gamma~` hyperlinear yields *asymptotically projective representations* of
`Gamma` (their Definition 4.6) -- deformations of the regular representation
arising from the central extension.  Hilbert--Schmidt stability is then used to
*upgrade* (T;FD) into a rigidity statement for asymptotically projective
representations (their Prop 3.4 and Thm 4.9), via a Connes-type lemma
(Lem 4.1).  The deformation and the rigidity contradict each other.  So the
hypothesis is consumed as rigidity for almost representations, not as an
approximation property of `Gamma` itself; a lane that only produces
approximations of `Gamma` does not feed this theorem.

**Transcription note (source re-checked 2026-08-21, arXiv HTML of v2).**
In Dogon--Vigdorovich's convention "Hilbert--Schmidt stable" already means
the FLEXIBLE notion: their Definition 1.2 reads "A group `Gamma` is
Hilbert--Schmidt stable if for every asymptotic representation
`pi_n : Gamma -> U(d_n)` there exists a sequence `D_n >= d_n` and a sequence
of honest representations `rho_n : Gamma -> U(D_n)` such that
`d_2(pi_n, rho_n) -> 0`; if `D_n` can be chosen to be `d_n` we say `Gamma`
is strictly Hilbert--Schmidt stable."  So the hypothesis of the theorem
above is flexible stability (which is what the abstract says for
`SL_2(Z[1/p])`), and the strict notion is only the special case.  The
theorem is numbered 1.3 in the current HTML rendering and carried the
label `thm:main-non-hyperlinear` in the submitted source; the statement
is identical.
