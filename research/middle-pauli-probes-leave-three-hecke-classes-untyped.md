---
rg: 2
id: middle-pauli-probes-leave-three-hecke-classes-untyped
kind: claim
title: Literal middle-Pauli probes leave three signed-Hecke detector classes untyped
artifacts:
  - experiments/signed_hecke_literal_pauli_probe_audit.py
  - experiments/signed_hecke_literal_pauli_probe_audit.sbatch
  - experiments/signed_hecke_middle_pauli_probe_audit.py
  - experiments/signed-hecke-literal-pauli-probe-results.json
distinct_from:
  signed-hecke-detectors-are-uniformly-mark-saturated-but-untyped: that finds the 31 positive classes requiring external probes; this tests the complete literal 48-word middle-Pauli menu against those classes with faithful Leavitt coefficients and isolates the three surviving endpoint obstructions.
  paid-t00-reynolds-cut-is-whitehead-reducing: that uses the same 48 conjugators to localize paid mass on a Whitehead-reducing cut; this asks whether they source-type the external root extraction and proves that they do not.
  eight-external-returns-have-no-whitehead-gauge-lock: that leaves arbitrary multiplicity gauge on the eight constant external normalizers; this gives the earlier obstruction, before an external root return is even reached, for the literal middle-index probe menu.
---

**ESTABLISHED LITERAL-MENU FENCE.**  Retain the `31` positive-character
`L_0` conjugacy classes from
`signed-hecke-detectors-are-uniformly-mark-saturated-but-untyped` whose
internal normal closures contain no elementary root.  Let

```text
Y_m=x_(k_m,3)(b_m),        X_m=x_(1,k_m)(a_m),
(k_1,k_2,k_3)=(7,8,9),
M_Y=<Y_1,Y_2,Y_3,J_1,J_2>,
M_X=<X_1,X_2,X_3,J_1,J_2>.                            (MPF1)
```

Here `J_1,J_2` are the two literal prefix Whiteheads, not bare coordinate
permutations.  Their involution and braid relations and the Pauli
translation relations give

```text
|M_Y|=|M_X|=8*6=48.                                  (MPF2)
```

The faithful binary-prefix Leavitt audit gives three different answers,
which must not be conflated.

First, only two words of `M_Y` normalize the actual signed pair
`(L_0,lambda_0)`:

```text
M_Y intersect Norm(L_0,lambda_0)={1,Y_1}.             (MPF3)
```

Both commute with `L_0`.  Hence no one of the `31` fenced positive classes
has a nontrivial **source-preserving** first commutator with the literal
paid menu.

Second, the full menu has `24` explicitly conjugated signed-source types.
Every fenced class has some nonzero commutator with a word of `M_Y`.  Thus
the menu does name a finite moving source for mere noncommutation.  This is
not root extraction: only `16` of the `31` classes have an elementary first
commutator, and allowing a second probe from `M_Y` still covers only those
same `16` classes.

Third, allow the stronger mixed probe: first use any word of the paid dual
menu `M_Y`, then any word of the full primal menu `M_X`.  This extracts a
nonzero elementary root for `28` of the `31` classes.  Exactly three classes
remain.  In the actor coordinate order `(2,4,5,6,7,8,9)`, deterministic
representatives are

```text
(65,74,4,8,16,32,64),
(73, 2,4,8,16,32,64),
(73,74,4,8,16,32,64).                                (MPF4)
```

Equivalently, their nonidentity entries are respectively

```text
E_(2,9)+E_(4,6)+E_(4,9),
E_(2,6)+E_(2,9),
E_(2,6)+E_(2,9)+E_(4,6)+E_(4,9).                     (MPF5)
```

The endpoint obstruction is literal: every dual-menu ejection from these
classes lands at actor targets `2` or `4`, while every available primal
Pauli return leg has source in `{7,8,9}`.  Permuting the three middle
indices and multiplying several primal translations cannot create a
composable return.  The exact calculation consequently gives the same
three misses for one `X_m` return and for all `48` words of `M_X`.

Adding the currently named roots

```text
S_57=x_57(s_1),             A_1=x_47(s_1t_0)          (MPF6)
```

does not repair this endpoint mismatch: neither supplies a leg sourced at
`2` or `4`.  The exact expanded single-leg audit leaves the count `3` and
the representatives `(MPF4)` unchanged.

Consequently the paid `48`-word menu does not give a finite typed extraction
cover of the external detector classes.  It can transport `Q` to one of a
finite list of named conjugate source projections, but noncommutation on
that moving source does not identify an elementary return or its
multiplicity gauge.  The enumeration itself supplies no relation between
the multiplicity charts of those conjugate sources.  In any of the `28`
index-compatible branches subsequently routed through one of the eight
constant external normalizers, that missing datum is exactly the finite
representation-profile freedom exhibited by
`eight-external-returns-have-no-whitehead-gauge-lock`; on the three classes
`(MPF4)`, the literal probe does not even reach that stage.

This is an exact finite-menu obstruction, not a claim that no longer mixed
word can work.  In fact
`five-return-legs-cover-hecke-detectors-not-source-gauge` adds the
two incident legs `x_12(s_1),x_14(s_1)` and closes the elementary-root count
for all `31` classes.  That extension also proves the remaining boundary:
the current Whitehead does not transport the endpoint coefficient and no
useful probe preserves the signed source, so the moving-source multiplicity
action remains untyped.  No Property T, Kazhdan input, canonical trace,
literature theorem, local computation, or Lean compilation is used.

DERIVATION
signed-hecke-literal-pauli-probe-audit
