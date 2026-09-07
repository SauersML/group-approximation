---
rg: 2
id: semisimple-packet-multiplicity-collapse-proof
kind: route
title: Correct covariance on each fixed orbit algebra and normalize its displacement cocycle
target: semisimple-packet-multiplicity-collapse
requires: []
artifacts:
  - research/artifacts/locally-finite-dimensional-compression-2026-09-07.md
  - non_mf_groups_exist.tex
---

Apply the locally finite-dimensional orbit theorem in the linked complete
proof to a=pi(k). The hypotheses in the target give exact
finite-dimensionality of every orbit window and invariance under the
compressed Kazhdan subgroup.

The proof lifts growing finite-dimensional algebras and, separately for
each fixed pair h,g, averages and polar-corrects the conjugating unitary
on C*(1,a,a_g). With c_n(g)=rho_n(a_g-a) it obtains

    c_n(hg)-c_n(h) = W_n(h,g)c_n(g)W_n(h,g)^*,
    ||W_n(h,g)-V_n(h)|| -> 0.

Normalize by k_n=max_(s in S)||c_n(s)||_HS. Exact local covariance gives
||c_n(g)||_HS <= |g|_S k_n eventually and

    ||c_n(hg)-c_n(h)-Ad(V_n(h))c_n(g)||_HS / k_n
        <= 2 ||W_n(h,g)-V_n(h)|| |g|_S -> 0.

The resulting nonzero cocycle vanishes on the compressed subgroup.
Delorme--Guichardet makes it a coboundary. Finiteness of the adjoint
norm matrix corona identifies the two Kazhdan fixed spaces, forcing
the coboundary to vanish. This contradiction proves the target.

Only fixed-pair convergence is used. No uniform estimate over the
growing window and no coherence between different corrected unitaries
is needed. Finite order of pi(k) is unnecessary.

This is a complete paper proof; it is not a new Lean certificate.
