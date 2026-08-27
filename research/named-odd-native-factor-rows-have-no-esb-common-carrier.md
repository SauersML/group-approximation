---
rg: 2
id: named-odd-native-factor-rows-have-no-esb-common-carrier
kind: claim
title: The authenticated odd native-factor rows have no common Hecke carrier for ESB
artifacts:
  - research/named-odd-native-factor-carrier-audit-proof.md
invalidates:
  - named-odd-native-factor-row-supplies-esb-bridge
distinct_from:
  primitive-native-hecke-relators-have-no-odd-mixed-occurrence: that audits only primitive relations and predates the derived order-seven and endpoint braid rows; this audits all odd rows currently authenticated in the direct EL moving packet and asks whether their other factors share the full Hecke carrier.
  cross-row-native-diamond-cube-retains-common-c2-gauge: that fences the first two-row commutator cube by a central dressing; this explains why the remaining odd rows do not remove that dressing on a common source-to-target occurrence.
  el20-six-moving-coefficient-square-bridges: that permits a new longer ordinary coefficient word; this is a finite-menu occurrence audit and not an exhaustive assertion about every consequence of EL20.
---

**ESTABLISHED CURRENT-PACKET OCCURRENCE AUDIT.**  In the ordinary EL20
relation menu currently attached to the two moving native rows, the
relations with odd incidence in exactly one member of

```text
{J_1,J_2,B_2,B_3}                                    (ONF1)
```

fall into three classes:

1. the literal Whitehead definitions `J_i=X_iY_iX_i`;
2. commutator factorizations of a Hecke arm, for example
   `B_2=[x_89(s_00),x_94(t_1)]`, and its next-prefix analogue;
3. the endpoint Coxeter rows `(J_iW)^3=1`.

None is an authenticated ungauged full-Gram row on the fixed Hecke carrier.

For class 1, `J_i` is the known full-Gram transport from `Q` to the next
Singer cut, but its chart typing is

```text
N_(i,k) tensor D_(i,k),                              (ONF2)
```

not `N_(i,k) tensor 1`.  The odd factors `X_i,Y_i` are precisely the
nonnormal coefficient occurrences whose simultaneous chart transport
absorbs `D_(i,k)`; the definition is internal to that moving chart and
does not compare it with the fixed Hecke frame.

For class 2, the output `B_2` or `B_3` does reduce `Q`, and the B2/B3 Pauli
rows give the sharp four-sector decomposition there.  The two input arms
of the commutator factorization are not authenticated as operators on that
same carrier.  The first complete factorization, native triangle, and
order-seven word still have the exact marked `GL_7(F_2)` model of
`native-a1-b2-hecke-triangle-has-gl7-model`.  Even adjoining the fine
idempotent, both native Morita factors, and both two-sided absorption rows
has the exact marked `GL_10(F_2)` model of
`fine-idempotent-biaction-return-has-gl10-model`.  Hence the odd output
syntax does not decode the input commutator as a same-carrier reservoir
commutator or make its output ungauged.

For class 3, the braid is a genuine global odd occurrence and synchronizes
the `J_i` gauges with the endpoint gauge.  But the endpoint word is not
typed as an ungauged map on `Q`; the complete full-moving packet even has an
exact profile with `QWQ=0`.  The row therefore identifies moving gauges but
does not supply the source/range Grams of a parallel edge.

The remaining named relations do not add a fourth class.  The order-seven
word `(J_iB_(i+1)A_i)^7` is odd in both `J_i` and `B_(i+1)` and permits the
paired factor dressing before its product is formed.  The `J_1--J_2` braid
is odd in both Whiteheads and identifies only their common gauge.  The
cross-row native-arm commutators contain neither Whitehead and see the
Hecke arms only through even commutator incidence; their common `C_2`
escape is recorded separately.

Thus the B2/B3 theorem changes the support column of the audit, but not the
occurrence column: it supplies a common quarter source `F<=Q`, while no
odd row places all of its factors on `F` with one fixed source and target
chart.  There is therefore no already-proved word which can be substituted
for the six bridges in `(ESB1)--(ESB3)`.

This is the sharp finite-menu conclusion.  It does not rule out a longer
derived EL20 word.  Such a word must couple one of the class-2 Pauli-typed
outputs to its nonnormal input arms on the same moving carrier, or attach
an endpoint/class-1 factor to an independently returned fixed-Hecke chart.

No Property T, Kazhdan input, trace assumption, new computation, literature
theorem, or Lean compilation is used.

DERIVATION
named-odd-native-factor-carrier-audit-proof
