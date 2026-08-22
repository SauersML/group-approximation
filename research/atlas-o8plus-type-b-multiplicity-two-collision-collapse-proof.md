---
rg: 2
id: atlas-o8plus-type-b-multiplicity-two-collision-collapse-proof
kind: route
title: Exhaust the eighty Boolean coordinates of the Type-B double module
target: atlas-o8plus-type-b-multiplicity-two-collision-collapse
requires:
  - atlas-o8plus-canonical-moved-module-completion-fails
artifacts:
  - experiments/atlas_a4_q1920_o8plus_typeb_m2_boolean.sage
  - experiments/atlas_a4_q1920_o8plus_typeb_m2_cnf_audit.sage
  - research/artifacts/atlas-a4-o8plus-type-b-multiplicity-two-cnf.json
---

The exact module calculation gives

```text
End_A(H^2) ~= M_8(F2) x M_4(F2).
```

Thus an arbitrary A-central operator on `H^2` has exactly eighty Boolean
coordinates.  Substitution in the three displayed collision identities gives
592 distinct source ANF equations: 80 quadratic, 256 cubic, and 256 quartic.
The separately expanded source has 1,541,964 monomial occurrences, so the
verifier avoids an exponentially redundant normal-form CNF.

Instead it constructs the three 16-by-16 matrix words directly as a Boolean
circuit.  Each F2 scalar product is an AND gate and each sum is an XOR chain.
For every generated gate the verifier exhausts its complete local truth table
and checks that the three-clause AND encoding or four-clause XOR encoding is
equivalent to the intended gate.  One final clause excludes the known identity
coordinate vector.  Therefore the resulting CNF is satisfiable exactly when a
nonidentity A-central collision operator exists.  Any returned assignment is
also substituted into the independently expanded 592-equation source ANF.

CryptoMiniSat 5.14.7 returns UNSAT for both markings.  The exact circuit data
are

```text
marking 1: 19,377 auxiliaries, 70,178 clauses,
           SHA256 c6609062671b9ebfc640a3c3834dae8e9c0725b3952f0792b26fd52ff75bea4b;
marking 2: 19,011 auxiliaries, 68,872 clauses,
           SHA256 776602abb9230f2e325662ea50c89d3e6eeec9cbd9732326e1b52d0d14d71a5d.
```

Consequently the identity is the only solution in either eighty-dimensional
Boolean coefficient space, proving the claim.  This finite SAT exhaustion is
not used as evidence for any multiplicity above two.
