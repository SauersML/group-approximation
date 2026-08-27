---
rg: 2
id: p3-denominator-steinberg-word-is-multiplicity-blind
kind: claim
title: The first p-three denominator-conjugated Steinberg word is multiplicity blind
distinct_from:
  mixed-steinberg-loops-admit-morita-rectangular-model: that realizes arbitrary pure Steinberg pastings with unequal coefficient reservoirs; this evaluates one literal denominator-conjugated SL3 word on an oscillator isotypic block and shows its multiplicity gauge cancels identically.
  denominator-transport-only-conjugates-p3-multiplicity-reservoirs: that leaves an arbitrary multiplicity unitary in every packet normalizer; this tests the first raw mixed-root relation that might have pinned that unitary and proves it does not.
  one-shared-root-does-not-align-heisenberg-packets: that gives two transverse regular Heisenberg packets sharing one literal root; this keeps one oscillator packet and shows a denominator-conjugated adjacent-root commutator cannot see its external commutant.
---

In `SL_3(Z[1/3])` put

```text
h=diag(3,1,1/3),       x_ij(r)=I+rE_ij.
```

The first literal relation mixing a denominator occurrence with two adjacent
roots is

```text
[h x_12(1) h^(-1), x_23(1)] x_13(-3)=1.               (DSB1)
```

Indeed `h x_12(1)h^(-1)=x_12(3)` and the Chevalley commutator formula gives
`[x_12(3),x_23(1)]=x_13(3)`.

On an oscillator isotypic carrier write the root radical as

```text
rho(x)=pi(x) tensor I_M,
rho(h)=W_h tensor V,                                   (DSB2)
```

where `W_h` is the prescribed oscillator intertwiner and `V` is the
multiplicity unitary from
`denominator-transport-only-conjugates-p3-multiplicity-reservoirs`.  Then

```text
rho(h x_12(1)h^(-1))
 = W_h pi(x_12(1)) W_h^* tensor I_M.                   (DSB3)
```

The factors `V,V^*` cancel before the commutator is formed.  Every remaining
factor in `(DSB1)` is in `pi(N) tensor I_M`, so `(DSB1)` is precisely the
oscillator Chevalley identity tensored with `I_M`.  It imposes no equation on
`V` or on `B(M)`.

This blindness has an exact trace witness.  Take `M=C^2`, let `V` be the
swap, and let `Q=I tensor diag(1,0)`.  Then all terms in `(DSB1)` are exact,
whereas

```text
||rho(h)Qrho(h)^*-Q||_2^2=1.                            (DSB4)
```

If the full finite parahoric/coweight table is retained, replace the single
swap by the inverse twisted-regular multiplicity functor from
`finite-native-p3-atlas-has-a-global-inverse-groupoid-gauge`.  The same
cancellation calculation remains exact for every denominator-conjugated
Chevalley triangle in the table.  Such triangles impose no constraint beyond
whatever the transition table already imposes on its multiplicity functor.

More generally, any word obtained by conjugating root-radical elements by
packet normalizers and then applying a root-group multiplication or
commutator identity is gauge-covariant: multiplicity factors cancel on each
conjugated root occurrence, and the word evaluates in the oscillator factor
alone.  Hence no dimension-independent estimate of the form

```text
||VQV^*-Q||_2^2 <= C * (denominator-Steinberg energy)   (DSB5)
```

can hold, for any finite `C`.

The remaining raw coordinate must therefore do more than evaluate a
Chevalley identity.  It must identify a transported multiplicity selector
with a separately named same-object selector, or decode a global building
PVM whose nonamenable covariance fixes the commutant gauge.  Pure root words,
even with denominator conjugations, remain inner/gauge-covariant.
