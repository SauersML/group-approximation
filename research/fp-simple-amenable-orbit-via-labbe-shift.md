---
rg: 2
id: fp-simple-amenable-orbit-via-labbe-shift
kind: route
title: A finitely presented derived full group of Labbé's Wang shift is an amenable-orbit realization
target: fp-simple-group-in-amenable-orbit-full-group
requires:
  - minimal-aperiodic-wang-shift-exists
  - minimal-z2-subshift-derived-full-groups-are-fg-simple
  - labbe-shift-derived-full-group-is-finitely-presented
---

1. **The action.** `Omega_U` is a minimal aperiodic Wang shift
   (`minimal-aperiodic-wang-shift-exists`), so `Z^2` acts freely on it by
   homeomorphisms. `Z^2` is amenable, so a `Z^2`-invariant Borel probability
   measure `mu` exists (Markov--Kakutani), and by minimality its support, a
   nonempty closed invariant set, is all of `Omega_U`.
2. **The group.** `S = D([[Z^2 ~ Omega_U]])` is finitely generated, infinite and
   simple (`minimal-z2-subshift-derived-full-groups-are-fg-simple`). Its elements
   have continuous, hence finite-range, cocycles, so `S ≤ W(Z^2 ~ Omega_U)`.
3. **Nontrivial.** A nontrivial element moves a nonempty open set, which has
   positive measure by full support.
4. **Finite presentation** is `labbe-shift-derived-full-group-is-finitely-presented`.

So `S` witnesses `fp-simple-group-in-amenable-orbit-full-group`. Combined with
`hyperlinear-fp-simple-via-amenable-orbit-full-group`, the root
`hyperlinear-fp-infinite-simple-group` now waits on exactly one open claim,
`labbe-shift-derived-full-group-is-finitely-presented`, and the witness would be
sofic. Amenability of `S` is not needed.
