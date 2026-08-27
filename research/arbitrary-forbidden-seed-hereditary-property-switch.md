---
rg: 2
id: arbitrary-forbidden-seed-hereditary-property-switch
kind: claim
title: One finite forbidden seed forces second-level hardness for every hereditary property
artifacts:
  - GroupApproximation/Computability/HereditaryPropertySwitchCompleteness.lean
  - GroupApproximation/Computability/ParametricRecursiveSwitchPresentation.lean
  - GroupApproximation/Computability/ParametricFinInfSwitch.lean
distinct_from:
  exact-literal-e-fin-inf-switch: that hard-wires the literal non-MF group as the seed; this is uniform in an arbitrary finite-presentation code and draws the consequence for every hereditary property at once.
  fixed-mark-query-enumerated-second-level-complete: that classifies one homomorphism-and-mark query about the literal seed; this classifies every hereditary property restricted to the switch family of an arbitrary seed.
  second-level-rice-theorem-for-local-approximation-properties: that adds the marked-group cover, the two-generator bridge and the finite-presentation Markov consequences; this is the countably generated switch and its pointwise identification with INF and FIN.
---

ESTABLISHED (route `arbitrary-forbidden-seed-hereditary-property-switch-proof`;
the semantic core is machine-checked in
`Computability/ParametricFinInfSwitch`).

**Parametric switch.**  There is a jointly computable map

```text
switchCode : FinitePresentationCode x ProgramCode -> EnumeratedPresentationCode
```

such that, writing `E_d = Carrier(d)` and `G(d,c)` for the group presented by
`switchCode(d,c)`,

```text
InfiniteDomain(c)  ==>  G(d,c) ~= 1,
FiniteDomain(c)    ==>  G(d,c) ~= E_d.                                  (S1)
```

The construction copies the relators of `d` at every stage of a ray, joins
adjacent copies generator by generator at a false event and kills a copy at a
true event; no property of the group `E_d` enters.

**Abstract property theorem.**  Let `P` be a property of groups that is
hereditary (passes to subgroups), holds for the trivial group and fails for
`E_d`.  Then on the switch family

```text
P(G(d,c))  iff  InfiniteDomain(c),                                     (P2)
```

so `c |-> P(G(d,c))` is `Pi^0_2`-complete and its complement
`Sigma^0_2`-complete, and for enumerated-presentation codes `q`

```text
Pi02Hard (q |-> P(Carrier q)),     Sigma02Hard (q |-> not P(Carrier q)).  (P5)
```

The same reductions hold under any isomorphism-invariant promise satisfied by
`1` and by `E_d`, since (S1) leaves only those two isomorphism types.

**Scope.**  The output is an enumerated (countably generated recursive)
presentation.  Nothing is claimed about finite-presentation codes; that
boundary is crossed only by a separate compiler.  The two-generator and
fixed-ambient sharpenings, and the finite-presentation Markov consequences,
are drawn in [[second-level-rice-theorem-for-local-approximation-properties]].
