---
rg: 2
id: almost-all-one-relator-groups-bh-proof
kind: route
title: Sapir--Spakulova embed generic one-relator groups in ascending HNN extensions of finitely generated free groups, and those embed in simple groups of type F_infinity
target: almost-all-one-relator-groups-satisfy-boone-higman
requires:
  - ascending-hnn-of-free-groups-satisfy-boone-higman
artifacts:
  - research/artifacts/gq-bh-bh-free-05-ascending-hnn.md
---

**Import, read at source.** Sapir--Špakulová, arXiv:0809.4693v2, TeX e-print fetched via MSI
on 2026-09-18 (SHA-256 `1fabe7cbff7930e2d730c37e16112564eb6b9db92ef99d89fd752aadb09d88ae`,
at `$GQ/src/bh-free-05/`). Verbatim:
- `thm3`: "A random $k$-generator $1$-relator group, $k\geq 3$, can be embedded into an
  ascending HNN extension of a finitely generated free group with probability $1$."
- Their definition (line 138): "an ascending HNN extension of a free group ... is a group of
  the form HNN$_\phi(F_k)=\langle x_1,...,x_k,t\mid x_1^t=\phi(x_1),...\rangle$ where
  $\phi$ is an injective homomorphism of $F_k$". So the base is finitely generated.
- `thm1`, `lm4`: the explicit embedding criteria (SS1), (SS2) of the target claim.
- `lm0` (Brown, Theorem 4.4, quoted): "$G$ is an ascending HNN extension of a free group if
  and only if one of the two supporting lines of $w$ parallel to the vector $(m,n)$
  intersects $w$ in one simple vertex or one simple edge." Brown's paper itself was not read.
- The models NR, CR and IC are defined in their §1. `lem2` and `lem3` show that the limits
  agree across the models.

**Derivation.** If `G` embeds in `F*_φ` with `F` finitely generated free and `φ`
injective, then `ascending-hnn-of-free-groups-satisfy-boone-higman` embeds `F*_φ`, hence `G`, in a simple group of type `F_∞` and in a
type (A) group. So the event "BH+" contains the event "embeds in an ascending HNN extension of
a finitely generated free group". The first event's probabilities therefore have `lim inf` at
least the limit `1` given by `thm3`. Parts 2 and 3 are the same composition, applied to
single groups and to subgroups. ∎
