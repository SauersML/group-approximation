---
rg: 2
id: fournier-facio-group-matricially-stable
kind: claim
title: Matricial stability of the Fournier-Facio torsion-free group
distinct_from:
  map-matricial-stability-non-mf: that claim is the established implication from stability plus minimal almost periodicity; this one is the stability hypothesis itself, for one specific group.
  leavitt-steinberg-hs-stable: that is a stability question for the Steinberg group over a Leavitt-type ring in the Hilbert--Schmidt setting; this is operator-norm matricial stability for the published torsion-free group.
  torsion-free-countable-non-mf: that claim asserts a torsion-free group is not MF; this one asserts a stability property and says nothing about MF on its own.
  fournier-facio-torsion-free-skeleton: that claim records the group's construction and compression core; this one is an analytic property of the same group, derived from that record rather than contained in it.
  torsion-free-finitely-presented-non-mf: that root is the non-MF existence statement; this is one analytic prerequisite of one route into it.
  torsion-free-higman-embedding: that claim is a combinatorial embedding theorem; this one is an operator-norm approximation property of a fixed group.
---

The Fournier-Facio group `G` of `fournier-facio-torsion-free-skeleton` is
matricially stable: every asymptotic homomorphism `G -> U(k_n)` is
pointwise-norm close to a sequence of genuine homomorphisms.

## Established form (2026-08-17)

ESTABLISHED, and in a strictly stronger form than stated: every
operator-norm asymptotic representation of `G` is **asymptotically
trivial**, so the correcting homomorphisms may always be taken to be the
trivial homomorphism.  The route is
`fournier-facio-stability-from-total-corona-triviality`; it does not attack
the stability question on its own terms at all.  It observes that an
asymptotic homomorphism is a representation in the norm matrix corona, that
`defect-normally-generates-torsion-free-quotient` makes the compression
defect the whole group, and that `normal-kazhdan-defect-non-mf` then kills
every corona representation elementwise.  What remains of an asymptotic
representation after that is a sequence converging pointwise to `1`.

Two consequences of the shape of the proof, both worth carrying:

- **The stability is degenerate.**  `G` is stable because it has no
  nontrivial finite-dimensional approximation of any kind, not because
  approximate representations of `G` can be repaired.  Reading this claim as
  evidence that `G` resembles the uniformly stable higher-rank lattices
  inverts what it says.
- **It is downstream of the obstruction, not independent of it.**  The route
  `torsion-free-non-mf-from-matricial-stability` was recorded as a fallback
  should `normal-kazhdan-defect-non-mf` turn out to have a gap.  It is no
  longer one: its analytic prerequisite is now proved *from* that
  obstruction.

## Literature, now read in the other direction

The material below was assembled while the claim was open, as evidence for
and against.  With the claim established it is no longer evidence; it is a
consistency check, and it passes.

- **Dadarlat, arXiv:2007.12655, Corollary 1.3** — a countable **linear**
  group with `H^{2k}(G;Q) != 0` for some `k >= 1` is not weakly matricially
  stable.  No conflict: `G` is not linear.  It contains an infinite finitely
  presented simple group, so it is not residually finite
  (`fournier-facio-group-finite-dimensional-shadow`), and a finitely
  generated linear group is residually finite by Malcev.
- **Dadarlat, Theorem 1.2** — for weakly quasidiagonal groups admitting a
  `gamma`-element, stability forces `H^{2k}(G;Q) = 0` in every nonzero even
  degree.  This used to be a place to hunt for a refutation; it is now a
  *checkable consequence* instead, conditional on `G` lying in that class.
  The hypothesis is exactly what is unexamined: `G` is not MF, so no corona
  representation of it is faithful, which is already incompatible with
  quasidiagonality — whether Dadarlat's *weak* quasidiagonality survives
  that is a separate question nobody here has looked at.  Flagged as
  transcription-dependent: the statement above is a summary, not a reading
  of the primary text, and nothing in this repository depends on it.
- **Glebsky--Lubotzky--Monod--Rangarajan, arXiv:2301.00476** — uniform
  stability of higher-rank lattices with respect to submultiplicative norms.
  Still a different property, and still not what is proved here: that is a
  uniform statement about defect-controlled families, this is pointwise
  convergence of every asymptotic representation to the trivial one.
- **Coarse geometry.**  Whether `G` is uniformly embeddable in Hilbert
  space, hence whether it admits a `gamma`-element, remains unexamined.  It
  is no longer on the critical path of anything, but it is the input the
  bullet above needs.
