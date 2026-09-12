---
rg: 2
id: stw95-bernoulli-z-crossed-product-counterexample-proof
kind: route
title: Cross the Jiang-Su Bernoulli shift to expose an odd K-class
target: stw95-cu-z-tensor-counterexample
requires: []
---

Let

```text
C = tensor_(j in Z) Z
```

and let `beta` be the bilateral shift of the tensor coordinates.  Infinite
tensorial absorption identifies `C` with `Z`.

Here is a direct check of strong outerness, including the point that is easy to
hide in the phrase "Bernoulli shift".  In the unique-trace GNS representation,
the weak closure of `C` is the infinite tensor product finite factor `M`.  Fix
`n!=0` and suppose that the extension of `beta^n` were `Ad(U)`.  Given
`epsilon>0`, Kaplansky density gives a contraction `a` supported on finitely
many tensor coordinates with `||U-a||_2<epsilon`.  Choose a coordinate `j`
such that both `j` and `j+n` avoid that finite support, and choose a trace-zero
unitary `w` in the weak closure of the `j`th coordinate.  Then `a` commutes
with `w`, whereas

```text
beta^n(w) lies in coordinate j+n,
||beta^n(w)-w||_2^2 = 2.
```

The equality `beta^n(w)=UwU*`, together with the contraction approximation,
gives `||beta^n(w)-w||_2 <= 4 epsilon`; letting `epsilon` tend to zero is a
contradiction.  Thus every nonzero power is outer in the trace factor, exactly
the strong-outerness condition of Matui--Sato, Definition 2.5.

Set

```text
E = C crossed_product_beta Z.
```

This is an explicit separable unital simple nuclear UCT algebra.  These are
separate permanence inputs, not consequences of one omnibus theorem:

* pointwise outerness of a `Z`-action on a simple algebra gives simplicity of
  the reduced crossed product;
* amenability of `Z` and nuclearity of `C` give nuclearity and identify full
  and reduced crossed products;
* the Rosenberg--Schochet bootstrap/UCT class is closed under crossed products
  by `Z` (equivalently, use the Toeplitz extension underlying PV);
* Matui--Sato, Corollary 4.11 and Remark 4.12, apply because `Z` is elementary
  amenable, `C` is unital, simple, separable, nuclear, stably finite and
  Z-stable with one extremal trace, and the action is strongly outer.  Hence
  `E` is Z-stable.

It is monotracial as well.  If `sigma` is a trace on `E`, then its restriction
to `C` is the unique trace `tau`.  For the implementing unitary `u`, the
coefficient `a -> sigma(a u^n)` extends by Cauchy--Schwarz to an `L^2(C,tau)`
functional.  Its Riesz vector intertwines the identity representation with
the weak extension of `beta^n`.  For `n!=0`, factoriality and outerness force
that vector to be zero.  Thus every nonzero Fourier coefficient vanishes and
`sigma=tau conditional_expectation`.  This is also the standard
strong-outerness/unique-trace lemma for crossed products.

The shift acts trivially on K-theory.  Indeed,

```text
K_0(C)=Z[1_C],                 K_1(C)=0,
```

and every unital automorphism fixes `[1_C]`.  The Pimsner--Voiculescu
six-term exact sequence, whose boundary maps here are `id-beta_*=0`, gives

```text
K_0(E)=Z,                     K_1(E)=Z.
```

The trace pairing sends the positive generator of `K_0(E)` to `1`.  Since
`E` is simple, finite and Z-stable, it has stable rank one.  Thus
`V(E)=N_0`; nuclearity makes its unique trace its unique quasitrace.  The
simple pure Cuntz-semigroup formula now gives

```text
Cu(E)=N_0 disjoint_union (0,infinity]=Cu(Z).
```

For `F=E tensor_min E`, the UCT Kunneth sequence has no `Tor` terms and
gives

```text
K_0(F)
 = (K_0(E) tensor K_0(E)) direct_sum (K_1(E) tensor K_1(E))
 = Z^2.
```

The algebra `F` is again simple, finite and Z-stable, hence has stable rank
one.  Therefore the Grothendieck group of `Cu(F)_c=V(F)` is `Z^2`, while the
Grothendieck group of `Cu(Z)_c=N_0` is `Z`.  A Cu-isomorphism preserves
compact elements, and `Z` is not additively isomorphic to `Z^2`.  Hence
`Cu(F)!=Cu(Z)`.

For completeness, none of the hypotheses used in the last paragraph is
implicit: nuclearity of one simple factor gives simplicity of the minimal
tensor product; the product trace is faithful, so `F` is stably finite; and
Z-absorption passes to `E tensor_min E`.  Rordam's Theorem 6.7 then gives
stable rank one.  Brown--Perera--Toms' simple exact finite Z-stable Cuntz
semigroup computation gives the displayed `Cu(E)`, with the mixed order
determined by the trace pairing `n -> n`.  Hence it agrees with `Cu(Z)`, not
merely as a set or abstract additive monoid but as a Cu-semigroup.

## Imported results and exact scope

The direct argument above proves strong outerness and uniqueness of trace,
but still imports: countable tensorial absorption of the strongly
self-absorbing algebra `Z`; simplicity/nuclearity/UCT permanence for the
crossed product; Matui--Sato Corollary 4.11 plus Remark 4.12; the
Pimsner--Voiculescu six-term sequence; the UCT Kunneth sequence; Rordam
Theorem 6.7; and the Brown--Perera--Toms Cuntz-semigroup formula.  No one of
these operator-algebra statements is currently formalized in this repository.

This realizes the cross-`K_1` obstruction by a named dynamical construction,
without selecting an algebra only by an existence invariant.
