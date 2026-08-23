---
rg: 2
id: sync4-one-negative-abelian-corner-wordizes-arbitrary-pvm
kind: claim
title: A rational one-negative character corner wordizes every four-outcome PVM without rank balancing
distinct_from:
  sync4-coordinate-atom-normal-form: that computes the atom-reflection formula; this realizes all four reflections as literal group elements on one rational finite-group corner.
  hyperoctahedral-reflection-common-q-context-atlas: that first rationally balances arbitrary BCS traces and uses one irreducible signed-permutation block; this local corner permits arbitrary atom multiplicities.
  finite-cocycle-select-forces-one-common-lcu-gauge: that uses the one-negative orbit to synchronize a finite cocycle router; this uses only its commutative character corner to authenticate one PVM.
---

**ESTABLISHED.**  Let

```text
K=(C_2)^4=<r_0,r_1,r_2,r_3>
```

and, for a sign character `epsilon in {+1,-1}^4`, let

```text
p_epsilon=(1/16) product_(a=0)^3 (1+epsilon_a r_a)
```

be its rational minimal projection in `Q[K]`.  Let `Omega` be the four
characters having exactly one negative coordinate and put

```text
q=sum_(epsilon in Omega) p_epsilon.                     (S4C1)
```

Then `q` is a central rational projection with canonical trace `1/4`, and

```text
q Q[K] q = directSum_(a=0)^3 Q p_a.                    (S4C2)
```

Here `p_a` denotes the character which is negative exactly at `a`.  On this
corner,

```text
r_a q = q-2p_a.                                        (S4C3)
```

Consequently any four-outcome PVM `(E_0,...,E_3)` in any tracial algebra
gives a unital corner representation by

```text
p_a -> E_a,       r_a q -> 1-2E_a.                     (S4C4)
```

The atom ranks or traces may be arbitrary, including zero.  Conversely every
unital representation of `(S4C2)` produces a four-outcome PVM and literal
group-element atom reflections through `(S4C3)`.

This corrects the tempting use of the tautological irreducible representation
of `B_4=(C_2)^4 semidirect S_4`.  That representation also makes the
coordinate reflections literal, but adjoining the coordinate permutations
forces the four atom multiplicities to agree and therefore does not realize
an arbitrary perfect `SYNC_4` model.  The abelian rational corner retains the
wordization while avoiding that hidden completeness restriction.
