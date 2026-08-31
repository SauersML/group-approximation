---
rg: 2
id: finite-lamp-targets-glue-after-action-groupoid-completion
kind: claim
title: Finite lamp targets glue after action-groupoid completion, but site relation errors amplify
distinct_from:
  finite-schreier-holonomy-is-the-lamp-gauge-obstruction: that classifies gauges between supplied normalizer connections; this discards the supplied normalizers and constructs a new finite permutation transport once a finite action groupoid is given.
  moving-lamp-refinement-cocycle-has-diffuse-fibers: that proves spectral refinement and overlap covariance; this balances the refined atom multiplicities and identifies the separate finite-action-completion gate.
  finite-sheet-transport-networks-are-exactly-matricial: that realizes already supplied sheet bijections with arbitrary monodromy; this constructs a free finite groupoid carrier from rank capacities and quantifies both Fourier balancing and actor-relation loss.
  lamp-charts-recover-set-action: that turns a completed lamp chart system into a sofic set action; this proves the finite transport lemma and shows exactly why producing the required chart groupoid remains open.
artifacts:
  - notes/TRUE_RELATIVE_BURTON_KUN_THOM_REDUCTION.md
---

**ESTABLISHED FINITE GLUING; ACTION COMPLETION OPEN.**  Let `C` be a finite
groupoid and let `r_i` be a nonnegative integer capacity at every object.
For one connected component `O`, choose a root `o`, put
`H_O=Aut_C(o)`, and define

```text
k_O=|H_O| floor(min_(i in O) r_i / |H_O|).              (FTG1)
```

There are subsets `Y_i subset {i} times [r_i]`, each of size `k_O`, and
bijections `T_a:Y_i->Y_j` for every arrow `a:i->j`, such that

```text
T_(ba)=T_b T_a,       T_(a^(-1))=T_a^(-1),             (FTG2)
```

and every nonidentity isotropy arrow acts without fixed points.  The deleted
capacity is exactly

```text
L_O=sum_(i in O)(r_i-k_O).                              (FTG3)
```

If `T` is a spanning tree rooted at an object of minimum capacity, then

```text
L_O
 <=(|O|-1) sum_(e in T)|r_(t(e))-r_(s(e))|
   +|O|(|H_O|-1).                                      (FTG4)
```

Without the fixed-point-free requirement, the divisibility term disappears.
Thus, after the finite actor/cylinder groupoid has actually been completed,
rank balancing is the only transport cost.  There is no further Cech or
holonomy obstruction for a newly chosen target: use regular isotropy orbits
and transport their copy index along a spanning tree.

## Fourier cost of enlarging the lamp window

Let `B_S=(C_2)^S`, `m=|S|`, and let `P_chi` be the character
projections of a finite-dimensional lamp representation.  With
`p_chi=tau(P_chi)`, Fourier Parseval gives the exact identity

```text
sum_chi |p_chi-2^(-m)|^2
 =2^(-m) sum_(0!=b in B_S)|tau(rho(b))|^2.              (FTG5)
```

Consequently

```text
(1/2)sum_chi |p_chi-2^(-m)|
 <=(1/2)(sum_(0!=b in B_S)|tau(rho(b))|^2)^(1/2).       (FTG6)
```

If every tested nontrivial lamp trace has modulus at most `epsilon`, the
right side is at most
`(1/2)sqrt(2^m-1) epsilon`.  Replacing `E` by

```text
S=union_(g in F) gE
```

and adding `b=|S-E|` boundary sites therefore multiplies the worst-case
uniform-trace tolerance by the scale `2^(b/2)`.  For each fixed union this
can be paid by taking a sufficiently accurate microstate, but there is no
window-uniform estimate at fixed trace tolerance.

## Site-relation errors are not boundary-small

For `theta,eta in Sym(S)`, let `hat(theta),hat(eta)` be their canonical
permutations of the character cube `{+1,-1}^S`.  If `c(delta)` is the
number of cycles of `delta=theta^(-1)eta`, including fixed points, then

```text
d_H(hat(theta),hat(eta))
 =1-2^(c(delta)-|S|).                                   (FTG7)
```

Hence one wrong site relation already costs at least `1/2` of the regular
character block.  If the site defect has support `q`, the cost is at least
`1-2^(-q/2)`.  Passing from `E` to `union_(g in F)gE` does not dilute
a bad boundary completion: an asymptotic target assembled from regular
blocks must satisfy every tested site relation exactly on all but `o(1)`
of the blocks.

There is a sharp pairwise-gluing warning.  Suppose completed site
permutations for `s,h` send the required windows correctly and
`k=sh`.  If two unused boundary sites lie outside the prescribed target
window `kE`, compose the coherent completion for `k` with their
transposition.  All three generator covariances, all coarse restrictions to
the named windows, and all overlap refinements remain exact, but the actor
relation on the character cube has Hamming defect exactly `1/2`.
Therefore marginal character couplings do not determine a joint actor
coupling; multiplication cells must be imposed during target selection.

## A sufficient matrix observable, and its limit

[[phase-free-cartan-observables-force-joint-lamp-targets]]
gives a quantitative extractor once a common rank-one masa refining the lamp
PVMs is available.  Fourth-power collision mass near one rounds each actor
unitary to a monomial; phase-free diagonal conditional-expectation mass near
zero makes the underlying permutation asymptotically free.  Explicit bounds
then transfer actor products and cylinder covariance to Hamming distance.

These two statistics are not canonical scalar group moments.  They range
over the growing minimal projections of the chosen masa.  Producing such
masas uniformly from arbitrary crossed-product microstates would imply that
every Connes-embeddable p.m.p. action admitting the extraction is sofic.
For the Kun--Thom Bernoulli action this is exactly the desired contradiction,
not an independent finite-dimensional Ulam theorem.

[[canonical-regular-packets-leave-an-unbounded-cartan-reservoir]] rules out a
natural attempt to manufacture the missing masa.  In every canonical
regular-trace central sector, a finite nonabelian packet acts as a full fixed
matrix factor tensored with an unbounded multiplicity algebra.  Even an ideal
left/right packet leaves the external amplification, and no equivariant rule
from the packet tuple can select a rank-one masa.  An exact doubled bent-Walsh multiplicity involution has exact canonical
trace at every finite stage, collision tending to zero, and distance tending
to `sqrt(2)` from every monomial after sublinear padding.  The packet can rigidify coarse finite-factor atoms, but refining
them to rank one still requires growing actor-dependent data.

## Exact surviving direct-target seam

The theorem above deliberately abandons conjugating the supplied unitary
normalizers.  It says that **if** the matrix model yields a finite
approximately multiplicative action groupoid on the cylinder atoms, then
the remaining integer transport can be glued with the explicit losses
`(FTG4)--(FTG6)`.

Constructing that groupoid is the unsolved step.  Scalar canonical mixed
traces do not select it: for every nonidentity actor word `g` and lamp word
`a`, the canonical group trace of `a g` is zero.  Actor multiplication
must instead survive as a joint permutation constraint.

Nor can one replace the missing groupoid by exact finite quotients.  For the
Kun--Thom pair, `finite-quotient-blindness` and the marked two-point
obstruction show that exact finite actions collapse a required pair of coset
sites.  More generally, a strict compressor
`c Gamma c^(-1) proper-subset Gamma` puts elements of
`c^(-1)Gamma c minus Gamma` in the profinite closure of `Gamma`.
Thus a disjoint union of exact finite action blocks cannot supply the needed
pointed chart.

By [[lamp-charts-recover-set-action]], a compatible asymptotic cylinder
groupoid of the required kind would already prove the coordinate action
`G on G/Gamma` sofic.  Kun--Thom prove that action nonsofic.  The hoped-for
hyperlinear-to-sofic contradiction therefore still requires a new theorem
extracting this classical groupoid from a hypothetical matrix model.  The
finite balancing and overlap stages are now closed, but the direct target
construction and the nonhyperlinearity route remain OPEN.

DERIVATION
finite-lamp-target-groupoid-gluing-proof
