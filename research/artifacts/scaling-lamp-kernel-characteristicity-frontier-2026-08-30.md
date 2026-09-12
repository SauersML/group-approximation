# Scaling-family lamp-kernel characteristicity frontier

Date: 2026-08-30

Let `E_m` be the eight-generator scaling presentation and
`N_m=<<c_m>>`.  The selected quotient is completely understood:

```text
E_m/N_m ~= Z[1/m]^3 semidirect (SL_3(Z) x Z),
```

and its amenable-radical abelianization recovers `m`.  Thus the
pairwise-nonisomorphism root has one remaining group-theoretic gate:

```text
every isomorphism E_m -> E_n carries N_m onto N_n.
```

## Why the gate is not formal

The map `E_m -> E_m/N_m` is a displayed retraction, not an abstractly
canonical quotient.  Invariance under `Aut(E_m)` alone would also be
insufficient: the required assertion is functorial across isomorphisms
between different family members.

Ordinary abelianization does not select `N_m`.  The rotation relations kill
the base translations there, while the stable letter supplies the free
`Z` coordinate and the lamp supplies the same order-two coordinate at every
scale.  The exponent `m` is invisible.

Finite-quotient existence is not a shortcut.  Killing the whole base leaves
the common quotient

```text
<t,c | c^2=1> ~= Z * C_2,
```

independent of `m`, so unmarked finite targets can be reached through
scale-blind maps.

The established doubling block-amalgam theorem computes `N_2` internally,
but does not classify automorphisms of `E_2` or prove that this kernel is
intrinsic in the full semidirect product.  For composite `m`, the marked
orbital graph is additionally not a complete block.  A proof must supply an
intrinsic radical/normal-form characterization of `N_m` or a rigidity
theorem for the lamp-by-telescope decomposition.

## Exact payoff

Once the gate is proved, an isomorphism descends to the telescope quotients,
and

```text
|Tor(Rad_am(E_m/N_m)^ab)|=(m-1)^3
```

forces equality of scales.
