---
rg: 2
id: single-finitely-presented-mf-radical-computer-proof
kind: route
title: Gate the fixed Boone halting word with the literal MF-invisible mark
target: single-finitely-presented-mf-radical-computer
requires: [faithful-radical-commutator-gate, modular-machine-with-noncomputable-halting, boone-commutator-criterion-for-halting, boone-final-group-finitely-presented, marked-mf-radical-seed-gives-proof-triggered-compiler]
artifacts:
  - GroupApproximation/Computability/MFRadicalComputer.lean
  - GroupApproximation/Endpoint/ChosenNonMFAudit.lean
---

Choose the fixed modular machine whose configuration-halting predicate is not
computable, and let `B` be its coded finitely presented Boone group.  Let `E,w`
be Cairn's literal premise-free MF seed.  In the one fixed carrier

```text
U_MF = E * B
```

define `r_p=[w,v_p]`, where `v_p` is the explicit Boone element.  The faithful
gate says `r_p=1` exactly when `v_p=1`; Boone correctness says this is exactly
halting.  Functorial invisibility of `w` kills every `r_p` in every MF target.
If identity on the family were computable, fixed-machine configuration
halting would be computable.  Free-product finite-presentation permanence and
the non-MF left factor close the carrier package.
