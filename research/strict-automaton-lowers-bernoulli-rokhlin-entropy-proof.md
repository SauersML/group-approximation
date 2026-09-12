---
rg: 2
id: strict-automaton-lowers-bernoulli-rokhlin-entropy-proof
kind: route
title: Amplify the alphabet, code each Omega-block at an independent marker, and read the rest directly
target: strict-automaton-lowers-bernoulli-rokhlin-entropy
requires: []
artifacts:
  - research/artifacts/gottschalk-rokhlin-entropy-route-2026-09-12.md
  - research/artifacts/gk-verify-pos-permanence-chain-2026-09-12.md
---

Complete direct proof, Section 1 of the artifact.

* **Amplify.** Take `k` independent copies. The product misses `[p]` in every copy
  at every position and is isomorphic to `(A^k)^G`.
* **Markers.** A separating family of Borel sets gives a Borel marker set `C` with
  `S.C cap C` empty and `C union S.C` conull, where `S = Omega Omega^-1 \ {1}`.
  So `lambda(C) >= 1/D`, and the blocks `Omega^-1 . c` are pairwise disjoint.
* **Code.** The partition records the `k`-copy `Omega`-pattern at markers, a blank
  on the other block points, and the coordinate elsewhere. It is generating, with
  entropy at most `log 3 + k log q - k delta/D`.

Amplification is essential. The marker cost `log 3` is fixed while the saving
grows with `k`, so the proof never needs almost perfect tilings, which may not
exist.

Independently re-derived 2026-09-12 by gk-verify-pos: PASS (Section 14 of the
verification artifact). One normalization was added to the artifact: translate
the null pattern so that `1 in Omega`. This leaves `delta` and `D` unchanged and
gives `C ⊆ B`, which the entropy count uses.
