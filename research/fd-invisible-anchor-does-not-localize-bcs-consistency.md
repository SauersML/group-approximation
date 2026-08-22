---
rg: 2
id: fd-invisible-anchor-does-not-localize-bcs-consistency
kind: claim
title: Exact finite-dimensional invisibility does not supply even positive-density localized anchor consistency
distinct_from:
  exact-fd-invisibility-has-no-general-hs-robustification: that refutes global normalized-HS collapse; this strengthens the counterexample to a fixed positive-density reducing packet carrier and audits the BCS anchor substitution explicitly.
  bcs-commuting-square-transfer-collapses-britton-commutator: that identifies the missing matrix-only anchor row; this proves that identifying that row with an exactly finite-dimensional-invisible word does not provide it.
  canonical-iwahori-transfer-is-equivalent-to-full-transfer: that proves the analogous equivalence for the arithmetic Iwahori carrier; this gives a universal counterexample and the central-sign specialization.
---

**ESTABLISHED NO-GO.**  Exact finite-dimensional invisibility remains
insufficient even when the desired conclusion is required only on one fixed
positive-density reducing carrier.

Let `K` be the finitely presented sofic group and `c in K` the central
involution from `exact-fd-invisibility-has-no-general-hs-robustification`:

```text
pi(c)=1                                                   (FIA1)
```

for every finite-dimensional unitary representation `pi`, although `c!=1`.
Put

```text
Gamma=K times C_2,       C_2=<s | s^2=1>,
q=(1+s)/2 in C[Gamma].                                  (FIA2)
```

Then `Gamma` is finitely presented and sofic, `q` is a central projection,
and every exact finite-dimensional representation satisfies

```text
q(pi(c)-1)=0.                                            (FIA3)
```

Nevertheless canonical sofic microstates `(U_n)` of `Gamma` may be chosen
with the `C_2` factor exact, and their moments give

```text
tr(q(U_n)) -> 1/2,
||q(U_n)(c(U_n)-1)||_2^2 -> 1.                          (FIA4)
```

Indeed, in the regular trace,

```text
(c-1)^*(c-1)=2-c-c^*=2-2c,
tau(q)=1/2,             tau(qc)=0,                     (FIA5)
```

so the squared norm is `1`.  The carrier is not merely unnamed or weakly
controlled: it is a fixed group-algebra projection of mass `1/2`, central,
and hence reducing for every word.  Thus there is no general implication

```text
exact finite-dimensional invisibility of w
 + positive-density reducing carrier Q
 => ||Q(w(U)-1)||_2=o(1)                               (FIA6)
```

for normalized-HS approximate representations.

## Consequence for the BCS anchor substitution

One can formally replace the missing private/shared anchor equation

```text
c_0=b_0
```

by declaring its defect word `c_0 b_0^(-1)` equal to an exactly
finite-dimensional-invisible word `w`.  This makes the anchor equation true
in every honest finite-dimensional representation.  It does **not** make the
row small in canonical matrix microstates.  Equation `(FIA4)` already
refutes that inference after adjoining an independent finite anchor packet.
Therefore this substitution does not fill the matrix-only input in
`bcs-commuting-square-transfer-collapses-britton-commutator`; proving its
localized conclusion for the particular coupled presentation is new
normalized-HS stability/localization information.

There is a useful named/unnamed dichotomy.

* If `Q` is a fixed group-algebra carrier and `Q(w-1)!=0`, then forcing
  `||Q(U)(w(U)-1)||_2=o(1)` in canonical microstates is already a direct
  contradiction with the canonical trace.  Exact finite-dimensional
  invisibility contributes no proof of this forcing.
* If `Q_U` is model-dependent and unnamed, canonical moments do not control
  it.  Coupling `Q_U` to the invisible word is precisely the missing
  matrix-only localization theorem; `(FIA4)` shows it cannot follow from
  positive mass, reduction, and exact invisibility alone.

For a central invisible word there is also no gain from a finite covering
family.  If contractions `Q_1,...,Q_m` commute with `w` and

```text
sum_i Q_i Q_i^* >= kappa I,
```

then

```text
kappa ||w-1||_2^2
 <= sum_i ||(w-1)Q_i||_2^2.                            (FIA7)
```

Hence localized collapse on a bounded carrier cover implies the full global
approximate-invisibility statement.  For central marks, localization is
strictly weaker only when one has an isolated unnamed carrier with no such
coverage; producing and coupling exactly that carrier is the existing
compiler problem.

## The two advertised witnesses

For the binary Leavitt common-sign involution `J`, exact finite-dimensional
annihilation therefore supplies the wrong information.  After exactifying
the fixed order-two mark and writing

```text
e_-=(1-J)/2,            e_+=(1+J)/2,
```

one has identically

```text
||(J-1)e_-||_2^2=4 tau(e_-),       (J-1)e_+=0.         (FIA8)
```

Thus the anchor defect is maximal on the marked `J=-1` Heisenberg sector and
vanishes only on the unmarked trivial sector.  The dual-prefix dimension
pressure does not reverse `(FIA8)` in approximate representations; doing so
would be the open Leavitt HS coefficient decoder.

For the arithmetic HNN invisible commutator the word is not central, so
`(FIA7)` need not apply.  But the exact localized statement already appears
as `canonical-iwahori-projection-commutant-transfer`, and
`canonical-iwahori-transfer-is-equivalent-to-full-transfer` proves that
regular-tensor camouflage upgrades it back to the unrestricted transfer
modulus.  The positive-density arithmetic anchor is therefore not a weaker
escape either.

The only surviving possibility is candidate-specific coupling which fails
for `(FIA2)`: a genuinely matrix-only checksum tying an unnamed BCS carrier
to the invisible word.  That is the known stability/localization wall, not a
consequence of exact finite-dimensional invisibility.

