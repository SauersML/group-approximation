---
rg: 2
id: subshift-track-injections-lower-rokhlin-entropy-proof
kind: route
title: Transfer the Bernoulli measure along the injection, mark each window independently, and code each track at its markers
target: subshift-track-injections-lower-rokhlin-entropy
requires: []
artifacts:
  - research/artifacts/quantitative-surjunctivity-rokhlin-markers-2026-09-12.md
  - research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md
---

Complete direct proof, Section 1 of the first artifact.

- **Amplify.** `k` copies of `Phi` form an injection of the same shape, with `nk` tracks, the same `m` windows and
  deficit `k Sigma`. So `k = 1` suffices.
- **Transfer.** `Phi` is a homeomorphism onto its image, so `nu = Phi_* uniform` is isomorphic to the Bernoulli shift
  and essentially free. On a conull invariant set of free points every track lies in its subshift.
- **Markers.** Translate each missing pattern so that `1 in W_i`. For each distinct window `W`, Steps 2 and 3 of
  Section 1 of the second artifact give a Borel set `C_W` with `nu(C_W) >= 1/|W W^-1|` and disjoint blocks
  `w^-1 . C_W`, `w in W`.
- **Code.** For each window the partition records, for the tracks with that window, their `W`-patterns at markers, a
  blank at the other block points, and their time-zero coordinates elsewhere. The free track is read directly. The
  join is generating. At markers each track avoids its missing pattern, so the entropy is at most
  `m log 3 + n log b + j' log|D| - Sigma`.

Independently re-derived 2026-09-12 by w4-vf-positive-b: PASS (Section 11.1 of
`research/artifacts/gk-vf-positive-b-verification-2026-09-12.md`).
- **Re-derived:**
  - the normalization;
  - the transfer of freeness;
  - the marker construction: independence, maximality, `s >= 1/|W W^-1|` and disjoint blocks;
  - the generating argument, `(w.y)_i(w) = y_i(1)`;
  - the entropy identity `s|T| log(b^|W| - 1) + (1 - |W| s)|T| log b = |T|(log b - s eta_W)`.
