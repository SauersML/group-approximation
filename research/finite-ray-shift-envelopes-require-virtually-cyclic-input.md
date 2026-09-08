---
rg: 2
id: finite-ray-shift-envelopes-require-virtually-cyclic-input
kind: claim
title: An infinite input admits a finite-ray realization of its shift envelope exactly when it is virtually cyclic
artifacts:
  - research/artifacts/boone-higman-finite-ray-compiler-boundary-2026-09-08.md
---

Let P be an infinite finitely generated group and let E_m denote the
eventually m-periodic permutation group of the positive natural numbers.
The following are equivalent:

1. P is virtually cyclic.
2. Some bijection nu:P->N and some finite m satisfy E_nu(P)<=E_m.
3. Some E_nu(P) is conjugate, as a permutation group, to a subgroup of
   some E_m.

More generally, any infinite subgroup of E_m with a free orbit in its
natural action is virtually cyclic. Here a free orbit means that every
point in that orbit has trivial stabilizer.

Thus no enumeration of Z^2, or any other non-virtually-cyclic input, can
extend the cyclic compiler by fitting its regular action and E_2 into a
finite-ray Houghton extension. The assertion concerns the specified
permutation action, including changes of labeling by conjugacy. It does
not exclude arbitrary abstract embeddings into E_m.

Containment in E_m is not asserted to make E_nu(P) finitely presented:
finite presentation is not inherited by arbitrary subgroups. The
index-twelve argument for the cyclic example supplied that extra step.
The general infinite-input compiler remains open.

