---
rg: 2
id: zpc-readable-control-freezing-to-lcs
kind: claim
title: A perfect ZPC-IRS tailored gap has a readable fiber with a perfect commuting LCS solution
distinct_from:
  perfect-zpc-irs-quantum-gap-game: that established theorem supplies a finite tailored game with perfect ZPC-IRS completeness and a quantum gap; this is the remaining passage from its measurable classical control to one fixed linear branch.
  finite-linear-commutation-system-to-lcs: that exact compiler starts after a frozen operator solution is already available; this is the hard existence of a frozen branch.
  phase-safe-toric-gap-game-exists: that asks directly for a toric game witness; this uses the stronger semilinear structure now known to exist and asks only to eliminate the readable control.
  every-perfect-zpc-gap-witness-has-a-frozen-branch: that universal formulation is false by finite magic-square padding; this is the surviving joint-selection claim for one specially chosen unpadded witness.
artifacts:
  - research/artifacts/perfect-zpc-irs-gap-2026-08-18.md
  - notes/NONHYPERLINEAR_CHARACTER_REYNOLDS_INTEGRATION_2026-08-24.md
---

**OPEN JOINT-SELECTION CLAIM.**  One can choose the existential witness `G`
and a value-one ZPC-IRS strategy in `perfect-zpc-irs-quantum-gap-game` so that

```text
omega_ZIRS(G)=1,
omega*(G)<1.
```

For a global assignment `r` to all readable variables, substitute `r` into
every controlled-linear constraint selected on every edge.  This leaves a
finite family `E_r` of affine `F_2` equations in the unreadable variables.
Let `C` contain the unreadable pairs belonging to one question, and use
`finite-linear-commutation-system-to-lcs` to form the ordinary binary LCS

```text
L(G,r)=L(S_L,E_r,C),
```

with the original equation rows and the commutation-ancilla rows.

for some global readable assignment `r`, `L(G,r)` has a perfect
commuting-operator strategy.  This is an existential assertion about a
specially selected witness, not the false universal assertion that every
perfect ZPC gap witness freezes.

Once this holds, the quantum gap is automatic on that branch: if `L(G,r)` had
a perfect finite-dimensional strategy, restrict its operator solution to the
original unreadable variables and combine it with the deterministic readable
answers `r`.  The resulting tailored strategy satisfies every selected linear
constraint and would be perfect for `G`, contradicting `omega*(G)<1`.

## Attempts

- **The abstract value/ZPC hypotheses do not suffice.**
  `perfect-zpc-gap-padding-can-destroy-all-frozen-branches` appends a finite
  signed-Pauli magic-square selector to any perfect ZPC gap witness.  The gap
  and perfect strategy survive, but each selector value pins one member of an
  anticommuting pair to a central scalar and hence forces `J=1`.  Therefore a
  proof must select an unpadded witness using special TailoredMIP structure;
  it cannot be a theorem about an arbitrary game satisfying the two value
  inequalities.

- **Ucp compression to an arbitrary readable atom does not descend.**
  Compressing the IRS representation to a positive readable atom does send
  every selected equation word to its required scalar.  However,
  `scalar-relator-compression-does-not-kill-normal-ideal` gives an exact
  `2 x 2` counterexample to the tempting multiplicative-domain argument:
  scalar compression of each named relator does not kill its conjugates or
  the two-sided normal ideal.  Descent is valid only when every conjugate
  relation also holds on the atom, equivalently on the entire unreadable
  orbit of the fibre.  Thus ucp compression reformulates rather than removes
  the remote-bit/invariant-fibre obstruction.

- **Orbitwise equation-menu coherence is sufficient and weaker than fibre
  invariance.**  The exact repair does not require unreadable generators to
  preserve every readable bit.  It is enough that one positive readable atom
  and all its unreadable translates satisfy the same finite frozen relator
  menu.  `orbitwise-scalar-relators-give-quotient-representation` then
  restricts the ambient action to the cyclic orbit hull and produces a
  genuine quotient representation with `J=-1`.  This decomposes the present
  claim through the smaller open target
  `zpc-frozen-equation-menu-has-positive-orbitwise-class`.

- **Invariant readable atom.**  By `zpc-readable-variables-global-boolean-field`,
  all readable variables have joint spectral atoms `p_r`.  It is enough to
  find one positive-trace atom that is invariant under every unreadable
  variable.  The normalized corner then gives exact unreadable involutions;
  edge ZPC gives every commutation needed by the frozen equation rows, and
  perfect game value gives their affine relations.
- **Remote-bit cocycle.**  On `Y=X/<J>`, an unreadable generator acts on the
  global readable field by changing only coordinates not protected by its
  incident edges.  Package these changes as an `F_2^(S_R)`-valued measurable
  cocycle.  Edge ZPC kills a prescribed coordinate set for each generator.
  Prove, for the TailoredMIP gap witness, that this locally vanishing cocycle
  has a positive invariant fiber or can be cohomologically trivialized on a
  positive corner.
- **Dependency-hypergraph gluing.**  Inspect the fixed TailoredMIP verifier's
  readable dependency hypergraph.  If its local readable marginals have a
  running-intersection/chordal refinement, use measurable junction-tree
  gluing to turn the edge-local invariant algebras into one global invariant
  readable algebra.
- **Counterexample search before theorem proving.**  Enumerate tiny tailored
  controlled-linear games with finite ZPC permutation actions and test whether
  every readable branch is operator-inconsistent.  A counterexample would
  show that the TailoredMIP witness's special verifier structure, rather than
  abstract ZPC, must be used.

The obstruction is deliberately explicit: unreadable variables commute with
readable bits at their own and neighboring questions, but may move remote
readable bits.  No other perfect-completeness or approximation theorem is
missing on this route.

The actual BCV perfect-completeness construction does not silently supply the
missing invariant fiber.  By
`bcv-halt-readable-finite-orbit-does-not-transfer-to-gap-irs`, every HALT-side
finite signed-permutation strategy does have a finite readable translate
orbit, but the perfect gap IRS is extracted on a NONHALT instance and is not
one of those strategies.  Moreover, in BCV Question Reduction the unreadable
Pauli-X packet transitively permutes the readable `SamZ` atoms, so no nonzero
readable atom is invariant even in the canonical finite completeness
strategy.  Finite orbit and invariant fiber are therefore distinct resources;
the former is on the wrong branch and the latter already fails in the native
Pauli layer.
