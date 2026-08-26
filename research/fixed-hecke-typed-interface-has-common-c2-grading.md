---
rg: 2
id: fixed-hecke-typed-interface-has-common-c2-grading
kind: claim
title: The complete currently typed Hecke-carrier interface has a common C2 grading
artifacts:
  - research/fixed-hecke-typed-common-c2-grading-proof.md
distinct_from:
  cross-row-native-diamond-cube-retains-common-c2-gauge: that exhibits the common sign on the first two-row diamond cube; this proves that every algebraic consequence of all currently authenticated same-carrier rows, including the endpoint Whitehead braids, retains one common grading.
  named-odd-native-factor-rows-have-no-esb-common-carrier: that audits the odd global rows and proves that none is typed on the fixed Hecke carrier; this identifies the resulting carrier-local relation closure and proves it cannot manufacture an odd row by derivation.
  six-ungauged-moving-squares-lock-seven-gauges: that kills the moving gauges after an independently ungauged bridge is supplied; this proves that the existing typed interface cannot derive such a bridge.
---

**ESTABLISHED CARRIER-LOCAL PARITY FENCE.**  Form the abstract occurrence
interface consisting of every relation currently authenticated on one fixed
signed-Hecke carrier (or between its explicitly named moving charts):

1. the two native factorizations and seventh-power rows

```text
T_1=J_1B_2A_1,              T_2=J_2B_3A_2,
T_1^7=T_2^7=1;
```

2. the `J_1--J_2` braid and the endpoint Whitehead braids involving `W`;
3. the B2/B3 Pauli sign-flip conjugacies;
4. the rowwise native-arm diamonds, their cross-row commutators, and all
   conjugacy/naturality rows obtained from them on the named carriers; and
5. the positive external-return rows whose factors have actually been typed
   on those carriers.

This entire interface has a quotient onto `C_2=<c>` under the carrier gauge
grading

```text
J_1,J_2,B_2,B_3,W |-> c,                              (HCG1)
every other named occurrence |-> 1.                   (HCG2)
```

Equivalently, tensoring the five displayed occurrences by one common central
involution preserves every currently authenticated same-carrier row.  The
statement is closed under arbitrary products, substitutions, conjugations,
and consequences of those rows; it is not merely a finite list of failed
candidate words.

The endpoint occurrence `W` in `(HCG1)` is load-bearing.  If `W` were already
authenticated as ungauged on the fixed Hecke carrier, either endpoint braid
would kill the common sign.  What is established instead is only that the
three endpoint gauges are synchronized; `QWQ` may even vanish.  Therefore
one may not set the `W` gauge to one while using its global braid as a
carrier-local relation.

Consequently no algebraic recombination of the current typed interface can
produce an `(ESB2)` bridge whose label action has odd carrier grade and whose
reservoir action is the identity.  Any successful proof of
`el20-six-moving-coefficient-square-bridges` must add at least one new
same-carrier relation of odd grade, or independently authenticate one of
`J_1,J_2,B_2,B_3,W` as ungauged.  The globally valid Whitehead definitions
and odd arm factorizations do not contradict this conclusion: by
`named-odd-native-factor-rows-have-no-esb-common-carrier`, their other
factors are not typed on the required common carrier.

This is a semantic fence on the currently authenticated occurrence
interface, not a quotient of the full elementary group.  It therefore does
not refute the moving-cut compiler; it proves that a genuinely new
carrier-authentication input is necessary.  No Property `(T)`, Kazhdan
input, trace assumption, computation, literature theorem, or Lean
compilation is used.

DERIVATION
fixed-hecke-typed-common-c2-grading-proof
