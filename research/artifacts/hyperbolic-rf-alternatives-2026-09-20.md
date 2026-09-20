# Hyperbolic residual finiteness: alternative-route attack, 20 September 2026

The root remains open. This pass produced two proved structural tests and
identified an overstatement in the arithmetic discussion. It did not
construct a counterexample or establish a persistent class. The detector-spectrum
and Sylow-detour proofs were independently reviewed, with a correction
requiring vertex injectivity for the moment corollary; the review is in
Section 5 of `hyperbolic-rf-stability-audit-2026-09-20.md`. The later
composition-factor obstruction, including its extension to every PSL2
simple group and every prime at least five, also passed independent
review. No Lean certification or new finite computation is claimed.

## What was attacked

I read the residual-finiteness root; persistent central-class and edge-twist
nodes and proofs; the Sp(2,1) simple-quotient obstruction node; the HC1
reflected-word node and its regularity gate; and the visible-central-extension
route to instability of GHB_2(7).

The edge-twist route had the most immediately testable mathematical claim:
several first kernels have `H^1(N;F_p)=0` and full three-dimensional moment
spaces. The question was whether these two observations provide independent
evidence for persistence. They do not under the recorded finite-quotient
data.

## Result 1: finite central detectors are lift discrepancies

[[hrf-alt-edge-twist-finite-detector-spectrum]] and its proof show the
following. Suppose the finite vertex groups are perfect and have
`H^2(A_v;F_p)=0`. Every finite quotient `f:Λ ->> Q` determines a linear map

```
D_f: Hom(H_2(Q;Z),F_p) -> ⊕_e Hom(E_e,F_p).
```

To compute it, choose a central extension of `Q` by `F_p`, lift each vertex
map uniquely, and compare the lifts on every edge. A twist has a finite
center-detecting quotient exactly when it belongs to the union of these
images over all finite quotients. The construction does not assume `Λ`
residually finite.

This yields a concrete finite search target: a finite quotient whose
Schur multiplier has `p`-torsion and whose unique vertex lifts exhibit a
specified nonzero edge discrepancy. Mere `p`-torsion in the multiplier is
necessary, not sufficient. Quotients must not be restricted to simple
ones without a new theorem: a finite perfect group can have a nontrivial
solvable radical, and its multiplier is not determined just by the
multipliers of its simple quotient groups.

There is also a direct first-level theorem. If `N=ker f` has
`H^1(N;F_p)=0` and `H^2(Q;F_p)=0`, every nonzero class in `H^2(Λ;F_p)`
survives restriction to `N`. The reason is that a splitting over `N`
would be unique, hence normal under the whole central extension. It
would descend to a central extension of `Q`; this splits by the second
vanishing assumption, forcing the original class to vanish.

For the table in [[hyperbolic-triangle-colimit-with-persistent-edge-twist]],
the cases with `p>=5` have `Q=PSL_2(q)` for

```
(q,p) = (19,5), (29,7), (29,5), (31,5), (27,7).
```

Here `H^2(Q;F_p)=0` can be checked without relying on a Schur multiplier
table. A Sylow `p`-subgroup `P` is cyclic and lies in a split or nonsplit
torus; a Weyl element in its normalizer acts by inversion. Restriction to
`P` is injective by transfer, and its image is invariant under this
inversion. But inversion acts by `-1` on the one-dimensional
`H^2(P;F_p)`. One sees the sign by presenting a central extension of a
cyclic group of order `m` with lifted generator `t` and relation
`t^m=z^a`: replacing the generator by its inverse sends `a` to `-a`.
Since `p` is odd, the invariant space is zero.

Thus, **conditional on the recorded first-homology computations**, the
full moment rank in every listed `p>=5` case is mathematically forced.
It is a useful consistency check, but not an additional indication that
the twists survive further covers. This pass did not rerun those computations.

The fixed-quotient distinction matters: a moment test at `Q` permits
wreath-product detectors, whose resulting quotient after removing the
central kernel can be larger than `Q`. Without `H^1(N;F_p)=0`, vanishing
of `H^2(Q;F_p)` alone does not force a full moment space. The new proof
states this boundary explicitly.

## Result 2: fixed-base pro-p towers are insufficient

[[hrf-alt-persistence-needs-sylow-detours]] proves that a class dies in
some finite cover iff it dies after a prime-to-`p`-index subgroup detour
followed by a tower of normal index-`p` subgroups. Take a normal core of a
vanishing subgroup, pass to a Sylow preimage of its finite quotient, and
use a composition series of the Sylow group.

The initial prime-to-`p` restriction is injective. Nevertheless it can
create first cohomology, enabling subsequent `p`-covers even when the
original group has no nontrivial finite `p`-quotient. The nonsplit
`SL_2(F_5) -> A_5` double cover gives a complete small calibration:
`H^1(A_5;F_2)=0`, but its nonzero extension class dies after the chain
`A_5 >= V_4 >= C_2 >= 1` with indices `15,2,2`.

Accordingly, "only p-covers matter" in the existing moment theorem
means exactly that a prime-to-`p` cover cannot itself change the moment
space. It does **not** reduce persistence to the pro-`p` completion of
one fixed first kernel. Every finite-index subgroup of a finitely
generated first kernel is another possible starting point.

This does not contradict (M5), which is correctly proved. It corrects
the stronger informal sentence that persistence only requires controlling
the pro-`p` part of the subgroup lattice of one `N`, if read as its
ordinary pro-`p` completion.

## Arithmetic correction

The existing persistent-degree-two node says that the congruence subgroup
property "fails badly for rank-one lattices." That is too broad and is
inconsistent with the separate open Sp(2,1) nodes. Hill's primary source
explicitly states infinitude of the rank-one congruence kernel as a
conjecture and derives it conditionally from universal hyperbolic residual
finiteness. A finite congruence kernel remains a conditional route, not
an already excluded hypothesis for every rank-one arithmetic family.

Suggested replacement for that paragraph:

> Hill constructs non-residually-finite finite extensions assuming a finite
> congruence kernel. For a cocompact arithmetic rank-one lattice this would
> produce a hyperbolic counterexample. The needed congruence-kernel input is
> not established for the quaternionic rank-one candidates used here; the
> Sp(2,1) nodes retain it as open. Failure of the congruence subgroup property
> in other rank-one families must not be substituted for a general theorem.

Source checked: Richard M. Hill, *Non-residually finite extensions of
arithmetic groups*, Research in Number Theory 5 (2019), Theorem 1,
Conjecture 1 and Corollary 1,
<https://link.springer.com/article/10.1007/s40993-018-0140-z>.

## Disposition of the other alternatives

The Sp(2,1) route still needs an arithmetic theorem controlling alternating
and unbounded-rank finite simple images. Matrix commutant internality by
itself is not such a theorem: the lattice is already residually finite,
and the relevant images need not stay in bounded matrix dimension.

The HC1 word `([b,a][b,c])^p` has an explicit nontriviality proof and known
families of images killing it. The current regularity gate already excludes
low-class `p`-groups, root-element Chevalley models, and the simplest
abelian-layer attempts. This pass found no universal finite-image argument
and no new detecting finite image. Treating those excluded families as a
classification would be invalid.

The primary Caprace–Conder–Kaluba–Witzel paper confirms that hyperbolic
Kazhdan generalized triangles can have finite simple quotients of
arbitrarily large rank, so neither property (T) nor the triangle format
removes this obstacle. Source: *Hyperbolic generalized triangle groups,
property (T) and finite simple quotients*,
<https://arxiv.org/abs/2011.09276>.

## Next mathematically distinct work

A bounded follow-up attack proved
[[hrf-alt-psl2-detectors-need-new-composition-factors]]. For the actual
`p=5,7` PSL2 seed groups in the recorded table, and more generally for
any prime `p>=5` and any `PSL_2(q)` vertices, a finite central detector
must, after quotienting by its detected central `C_p`, have either a
`C_p` composition factor or a non-PSL2 simple composition factor.
Arbitrary product images of PSL2 simple quotients are excluded.
The proof uses cyclic Sylow inversion in cross characteristic and
square-torus weights on commutator/power maps in defining characteristic,
followed by a direct
unique-splitting proof that simultaneous vanishing of `H^1,H^2` is
closed under finite extensions. This is an actionable finite search
filter beyond the single quotient; it does not decide persistence.

The follow-up read the actual seeded GAP driver and raw output in
`experiments/edge-twist-moments/run2.g` and `run2.out`. Those outputs do
not print the individual edge generators, so no particular new finite
quotient was reconstructed or tested in this pass. The obstruction is
uniform over every triangle with the displayed vertex groups and thus
does not depend on identifying one random triple or on rerunning its
homology computation. It does not apply directly to GHB7, whose vertex
groups are not perfect.

For a chosen perfect-vertex triangle, enumerate finite quotient maps with
`p`-torsion multipliers and actually compute `D_f`; a nonzero discrepancy
would kill the corresponding persistence candidate. For a persistence
proof, one must exclude all such detector maps or control index-`p`
descents after every relevant prime-to-`p` detour. No theorem doing either
has been supplied here. Repeating the already-forced first-level rank
calculation does not address that remaining problem.
