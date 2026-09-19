---
rg: 2
id: stw72-localize-radical-through-hereditary-corners-proof
kind: route
title: Localize the purely infinite radical through full hereditary Morita equivalence
target: stw72-morita-hereditary-radical-core
requires:
  - stw72-purely-infinite-radical-reduction
---

Let `B=A/P_pi(A)` be the radical-free quotient supplied by the radical
reduction, and let `C subset B` be a nonzero hereditary subalgebra.  Weak pure
infiniteness passes to hereditary subalgebras, so `C` is weakly purely
infinite.  Concretely, the hereditary inclusion induces an order embedding
`Cu(C) -> Cu(B)` which preserves addition and increasing suprema; hence the
identity `nx=infinity x` in `Cu(B)` restricts, with the same `n`, to every
class in `Cu(C)`.

We first show that `C` has no nonzero purely infinite ideal.  Suppose that
`J ideal C` were nonzero and purely infinite.  Heredity is transitive, so `J`
is a hereditary subalgebra of `B`.  Let

```text
L=Ideal_B(J).
```

Then `J` is a full hereditary subalgebra of `L`.  Pure infiniteness is
invariant under strong Morita equivalence, hence `L` is purely infinite.
But `L` is a nonzero ideal of `B`, contradicting `P_pi(B)=0`.  Therefore

```text
P_pi(C)=0.
```

In particular `C` itself is not purely infinite.  Also, if `C` had the Global
Glimm Property, the equivalence

```text
weakly purely infinite + Global Glimm Property  iff  purely infinite
```

would again make `C` purely infinite.  Hence every nonzero hereditary
subalgebra of `B` fails the Global Glimm Property.  Applying the same argument
to a hereditary subalgebra of `C` proves the asserted Morita-hereditary
statement.

Now retain one exponent `n` witnessing weak pure infiniteness of `B`.  The
same exponent works in every hereditary `C`.  Since `C` is not purely
infinite, there is an `x in Cu(C)` with `x != infinity x`.  The equality
`x=2x` would imply inductively that `x=kx` for every positive integer `k`, and
then preservation of increasing suprema would give `x=infinity x`.  Thus
`x<2x`.  Weak pure infiniteness gives `nx=infinity x`, proving

```text
x < 2x <= ... <= nx = infinity x.
```

Finally choose `0 != b in B_+`.  The algebra `Her(b)` is sigma-unital, and the
preceding argument makes it weakly purely infinite, non-purely-infinite, and
radical-free.  Stabilization preserves weak pure infiniteness and pure
infiniteness.  Strong Morita equivalence identifies the ideal lattices of
`Her(b)` and `Her(b) tensor K`, and corresponding ideals are themselves
Morita equivalent; pure infiniteness of an ideal on one side is therefore
equivalent to pure infiniteness of its correspondent.  Consequently

```text
D=Her(b) tensor K
```

is stable, sigma-unital, weakly purely infinite, non-purely-infinite, and
radical-free.  The hereditary argument applied inside `D` gives the full
normal form.  Conversely, any algebra in this restricted class that is not
purely infinite is already a counterexample, so the reduction is an
equivalence and not merely a necessary condition.

For the quotient firewall, let `I ideal B` and let `0 != Q ideal B/I` be
purely infinite.  Write `J` for the inverse image of `Q`.  If `I=0`, then
`J=Q` would be a nonzero purely infinite ideal of `B`, impossible.  Thus
`I != 0`.  Both `I` and `J` are nonzero ideals of the radical-free weakly
purely infinite algebra `B`; hence both are weakly purely infinite, have zero
purely infinite radical, and are not purely infinite.  The defining exact
sequence is

```text
0 -> I -> J -> Q -> 0.
```

This proves that a good quotient layer can occur only over a genuinely bad
lower layer.  Extension permanence does not collapse this configuration,
because its ideal `I` is precisely the non-purely-infinite term.
