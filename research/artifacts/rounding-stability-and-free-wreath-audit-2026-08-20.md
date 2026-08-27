# Rounding, local stability, and free-wreath permanence -- source audit

Date: 2026-08-20

This audit records four user-supplied TeX archives and their exact impact on
the nonhyperlinear-group program.

## Amenable unitary microstates acquire literal sites

Burton--Chaudkhari--Juschenko--Muliarchyk, arXiv:2311.09202v2, Theorem 1.1
(`thm.sofic`) proves a quantitative same-dimension rounding theorem.  For an
amenable group `G`, a finite set `E`, and `epsilon>0`, sufficiently accurate
hyperlinear approximation data on a larger finite set `F` are `epsilon`-close
in normalized Hilbert--Schmidt norm on `E` to permutation matrices coming from
an `(E,epsilon)` sofic approximation.  The output acts on the same Hilbert
space.  The dependence is recursive, with a uniform description for
torsion-free groups.

This is the cleanest rigorous realization found so far of “manufacture sites
inside arbitrary unitary matrices.”  It is not a general hyperlinear-to-sofic
theorem: amenability and regular-trace separation are essential.  For the
finite-bi-index Clifford tape it can round an amenable stabilizer on each
fixed window, but it does not round the ambient action, produce one coherent
infinite coset family, or choose a number of sites larger than the current
matrix dimension inside that same model.

## Local stability makes the Kazhdan search strictly harder

Fournier-Facio--Gerasimova--Spaas, arXiv:2307.13155v2, Theorem 1.5 / `thm:T`,
proves that an infinite hyperlinear property-(T) group is not even locally
Hilbert--Schmidt stable.  This strictly strengthens the same-dimension
stability obstruction already recorded from Becker--Lubotzky.  Replacing
global stability by partial-homomorphism/local stability therefore cannot
rescue a hyperlinear Kazhdan ambient or stabilizer.

## Quantum free wreath products are another permanence trap

Fima--Troupel, arXiv:2504.00596v1, Theorem A(3) / Theorem `thmAtxt(2)`, studies
the generalized free wreath product

```text
G wreath_{*,beta,F} H
```

for an ergodic action of a compact quantum group `H` on a finite-dimensional
algebra.  The product is Kac exactly when `G` and `H` are Kac.  In the Kac
case, if the amalgamating dual quantum subgroup `F` is coamenable (equivalently
its finite von Neumann algebra is amenable in the theorem's formulation), the
discrete dual of the generalized free wreath product is hyperlinear exactly
when both input duals are hyperlinear.

This is not a theorem about every ordinary discrete-group quotient.  Its use
here is a narrow falsification test: changing a functorial Clifford halo into
a Kac generalized quantum free-wreath product with amenable amalgam does not
create nonhyperlinearity from hyperlinear ingredients.

## Dogon stability route

Dogon, arXiv:2211.10492v3, proves that flexible HS stability (indeed a weaker
ucp lifting property) for suitable property-(T) quotients makes specified
central extensions nonhyperlinear.  The supplied archive agrees with the
existing Cairn stability lane.  Dogon--Vigdorovich arXiv:2506.20843v2 already
generalizes and arithmeticizes that mechanism in the graph, so no duplicate
claim was added.  The live endpoint remains their concrete Iwahori
local-defect/global-distance question.

## Net effect

- amenability can produce literal permutation sites, but only on fixed
  windows and under regular-trace hyperlinear hypotheses;
- Kazhdan local stability cannot be used as a weaker escape hatch;
- both ordinary functorial haloes and Kac generalized quantum free wreaths
  preserve hyperlinearity under their published hypotheses.

The viable tape must therefore combine the amenable rounding insight with a
non-halo, non-free-wreath global return or holonomy relation.

## Additional supplied archives

Arzhantseva--Cherix, arXiv:2008.12954v1, develops general metric approximation
profiles, including hyperlinear profiles.  It reinforces the correct
quantifier lesson already represented by Slofstra's profile lane: arbitrarily
large finite dimension requirements do not refute hyperlinearity.  No new
claim is needed beyond `slofstra-subexponential-hyperlinear-profile` and the
same-model trigger nodes.

Brude--Sasyk, arXiv:1909.07800v5, proves permanence results for verbal products
and verbal wreath products.  For the present tape proposal its useful content
is subsumed by the newer and broader ordinary halo-product falsification node
`sofic-halo-products-preserve-hyperlinearity`; it does not provide the missing
non-halo return relation.  The archive is therefore recorded here without a
duplicative graph node.

Kahl--Schneider, arXiv:2504.10988v2, was already present as
`hyperlinear-near-representation-criterion`.  Direct source inspection upgrades
its audit: Theorem B is the precise iff, Theorem A is the
orthonormal-basis/probability-charge characterization of amenable
representations, and Theorem C supplies equivalent sphere and operator-state
forms.  This remains an exact reformulation of hyperlinearity, not an
independent solution of the wreath candidate.
