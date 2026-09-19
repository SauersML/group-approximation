# Problem LXXII: Morita-hereditary radical core audit (2026-08-30)

## Exact result

The purely-infinite-radical quotient can be localized beyond ideals.  If
`B` is weakly purely infinite and has no nonzero purely infinite ideal, then
every nonzero hereditary subalgebra `C subset B` is again weakly purely
infinite, non-purely-infinite, and has no nonzero purely infinite ideal.
Thus any LXXII counterexample produces a stable sigma-unital counterexample
with this property by taking `Her(b) tensor K` for any nonzero positive `b`.

This is a strict sharpening of the existing ideal-level statement.  A
hereditary subalgebra need not be an ideal, so the result rules out a good
Global-Glimm or purely infinite corner hidden inside a radical-free ideal.

## Morita step

The only new permanence input is standard strong Morita invariance of pure
infiniteness.  If `J` is a purely infinite ideal of a hereditary subalgebra
`C subset B`, then `J` is hereditary in `B` and is full in its generated
ambient ideal

```text
L=Ideal_B(J).
```

Hence `J` and `L` are strongly Morita equivalent, so `L` is a nonzero purely
infinite ideal of `B`, contradicting radical-freeness.  Notice that this does
not claim that `J` is itself an ideal of `B`; passing to `Ideal_B(J)` is the
essential step.

The same argument shows that zero purely infinite radical is invariant under
strong Morita equivalence: Rieffel correspondence matches ideals, the
corresponding ideals are Morita equivalent, and pure infiniteness is Morita
invariant.

## Local Cuntz certificate

Let `n` be a weak-pure exponent.  Every nonzero hereditary corner `C` is
non-purely-infinite, so some `x in Cu(C)` satisfies `x != infinity x`.  Since

```text
x=2x  implies  x=kx for all k  implies  x=infinity x,
```

one necessarily has

```text
x < 2x <= ... <= nx = infinity x.
```

Thus a radical-free counterexample is not merely globally defective.  Every
nonzero hereditary region contains a fresh non-idempotent Cuntz class even
though the same uniform finite multiple has already saturated that class.
This isolates the comparison-theoretic obstruction that any contradiction
argument must remove.

## Chain and quotient firewall

No nonzero hereditary subalgebra of the core can have a chain ideal lattice:
the established chain theorem would make that hereditary algebra purely
infinite.  In particular, every nonzero hereditary subalgebra has two
incomparable nonzero ideals.  Iterating gives an infinite strictly descending
sequence of nonzero radical-free ideals (and a recursively branching family
with incomparable siblings).  Thus a counterexample core has no minimal
nonzero ideal and no descending-chain condition at any nonzero hereditary
localization.

On the quotient side, the reduction deliberately stops short of claiming
that every quotient of `B` is radical-free.  If `0 != Q ideal B/I` is purely
infinite and `J` is its inverse image, then `I` cannot be zero and

```text
0 -> I -> J -> Q -> 0
```

has radical-free weakly-but-not-plain purely infinite terms `I` and `J`, but
a purely infinite quotient `Q`.  Equivalently, the remaining open seam is a
locally closed purely infinite patch whose lower boundary is itself
radical-free.  The hereditary theorem removes all open and Morita-local good
patches, but it does not remove such quotient-created patches.

## Scope boundary

This is an exact normal-form reduction, not a solution of Problem LXXII and
not a construction of a counterexample.  It reduces the search to stable
sigma-unital algebras and makes the obstruction hereditary under arbitrary
corners.  Nuclearity, exactness, and separability pass to hereditary
subalgebras and stabilization, so the reduction remains inside each of those
categories when assumed.
