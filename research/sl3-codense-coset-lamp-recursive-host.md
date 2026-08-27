---
rg: 2
id: sl3-codense-coset-lamp-recursive-host
kind: claim
title: The SL3 codense coset action gives an explicit recursive expanding-character lamp host
distinct_from:
  sharply-two-transitive-augmentation-lamp-host-audit: that uses simplicity and sharp two-transitivity to exclude finite character orbits; this uses finite-quotient codensity of an arithmetic subgroup.
  sl3-pair-relative-commutant-route: that uses the same arithmetic pair in a centralizer HNN extension; this uses its coset permutation module and a two-point Pauli seed.
  property-t-must-upgrade-global-augmentation-rounding: that is the remaining normalized-HS same-basis interface; this proves the exact and recursive groupification facts only.
---

ESTABLISHED.

Put

```text
A=SL_3(Z[1/2]),        C=SL_3(Z),        X=A/C,
L=direct_sum_X C_2.
```

Choose `a in A-C`, write `x=C`, `y=aC`, and let

```text
m_0=delta_x+delta_y in L.                                  (SCL1)
```

Then:

1. `A` is finitely presented and has property `(T)`, while `C` is finitely
   generated;
2. every finite quotient `q:A->Q` satisfies `q(C)=q(A)`;
3. every character `chi in L^` with `chi(m_0)=-1` has infinite `A`-orbit;
4. the permutational lamp group `L rtimes A`, and its extension by

   ```text
   z^2=J^2=1,       J central,       [m_0,z]=J,             (SCL2)
   ```

   are finitely generated and recursively presented; and
5. in the marked extension, `J!=1`, while every exact finite-dimensional
   unitary representation kills `J`.

For clause 3, suppose `chi` has finite orbit and let `N` be the core of its
stabilizer.  Then `N` is finite-index normal and fixes `chi`.  Finite-quotient
codensity gives

```text
A=CN.                                                       (SCL3)
```

Normality of `N` and `(SCL3)` make `N` transitive on `A/C`: every coset
`gC` has a representative in `N`.  Hence the `N`-invariant binary coloring
`chi` is constant on `X`, so it evaluates trivially on the two-point lamp
`m_0`.  This proves clause 3.  Property `(T)` then gives one uniform Schreier
gap on all seed-visible character orbits.

For clause 4, apply `recursive-permutational-lamp-presentation`.  The
preimage of `C` in a finite presentation of `A` is recursively enumerable:
enumerate words in fixed generators of `C` and proofs that an `A`-word equals
one of them.  Thus no double-coset finiteness is required.  The infinitely
many `C`-double cosets obstruct the obvious finite permutational-wreath
presentation, but they do not obstruct this recursive presentation.

Clause 5 is `infinite-character-actor-kills-fd-mark` applied to clause 3.
Its character-translation model sends `J` to `-I`, proving nontriviality.
This completely removes the actor finite-presentation/effectivity issue from
the expanding-character route.  The remaining load-bearing theorem is the
finite-matrix global same-basis PVM/actor-word-energy decoder; no claim about
that analytic interface is made here.

For this particular two-point seed there is an even smaller endpoint.
`sl3-two-point-lamp-mark-is-single-rcc-scalar` observes that

```text
m_0=[c,h].
```

Therefore projective normalized-HS relative-commutant transfer from `C` to
the single generator `h` kills the mark directly: any scalar phase of
`[c,h]` disappears in its D8 commutator with `z`.  This is an alternative to
the full all-pairs/PVM route, not a consequence of additive rounding: the
exact infinite lamp model has `m_0!=1`.  Pure finite-orbital propagation
cannot supply uniform module exposure by
`finite-orbital-checksum-cannot-expose-sl3-coset-module`.
