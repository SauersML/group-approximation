---
rg: 2
id: torus-transfer-contains-li-gottschalk-proof
kind: route
title: At hosts already known to be torus-surjunctive the hypothesis of C3 is true, so C3 there is surjunctivity itself
target: torus-transfer-contains-li-gottschalk
requires:
  - locally-indicable-groups-are-torus-surjunctive
  - torus-degree-regularity-lifts-through-li-kernels
artifacts:
  - research/artifacts/torus-transfer-li-hosts-2026-09-19.md
---

A complete proof, given in artifact Sections 1, 2 and 4.

* **Localization.** For `G in 𝒞`, the hypothesis of C3 at `G` is true, so the implication has the
  truth value of its conclusion.
* **Containment.** Two established nodes place the hosts in `𝒞`:
  - locally indicable groups, by `locally-indicable-groups-are-torus-surjunctive` item (c);
  - admissible-by-(RF or locally RPP) groups, by `torus-degree-regularity-lifts-through-li-kernels`
    item 4.
* **Mechanism kill.** A strict torus automaton over `H in 𝒞` contradicts `TS(H)`.
  - The listed host operations preserve local indicability, because LI is extension-closed
    (artifact Section 4, two-line proof), or land in item 4 of the descent node.
  - The support condition on the output degree matrix is item (a) of
    `locally-indicable-groups-are-torus-surjunctive`, together with
    `torus-degree-regular-on-prime-power-residual-support`.
