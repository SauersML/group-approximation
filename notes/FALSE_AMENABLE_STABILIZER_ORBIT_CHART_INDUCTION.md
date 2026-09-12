# Amenable stabilizers supply the real Schreier charts, but not scalar transversals

Date: 2026-08-12

## 1. Outcome

There is a genuine positive theorem behind the proposed induced-Schreier
experiment.  Gao--Patchell--Kunnawalkam Elayavalli prove that if a sofic
group `K` acts transitively on a graph and one vertex stabilizer `H` is
amenable, then the graph action is sofic.  Passing to the empty graph gives

`K sofic, H amenable  ==>  K curvearrowright K/H is a sofic set action.`
                                                               `(ASI1)`

This applies twice in the present FALSE construction:

1. the vertex group `G` is residually finite and
   `B=<h,c>~=BS(1,p+1)` is amenable, so `G curvearrowright G/B` is sofic;
2. the external group `L=SL_d(Z)` is residually finite and
   `H_0=<t,s>~=Z^2` is amenable, so `L curvearrowright L/H_0` is sofic.

Thus the absence of an actual finite orbit model is not the obstruction to
globalizing the local clock or paired Fourier cell.  The primary-source
proof gives exactly the finite orbit charts needed for induction.

It does **not**, however, construct one finite principal `H`-bundle with a
global transversal.  Its charts depend on the base state.  Consequently it
does not produce the three scalar quantities

`R_*/M`, `A_*/M`, `R_*A_*/M`                           `(ASI2)`

from `FALSE_INDUCED_WEYL_SEAM_MOMENT_CRITERION.md`.  In fact the primitive
scalar version of `(ASI2)` is impossible by
`FALSE_PROPERTY_T_PRIMITIVE_HOLONOMY_MOMENT_NO_GO.md`.

The useful conclusion is instead a chartwise paired-induction principle.
If the remaining Frobenius/Steinberg fiber assignment can be made functorial
on these orbit charts, then induction preserves its vanishing defects and
its marked Hilbert--Schmidt gap without dilution.  Hence finite base
transport is now available; the missing datum is precisely the
chart-functorial paired fiber map.

## 2. What the amenable-stabilizer proof actually provides

Fix finite sets

`F subset K`, `W subset K/H`,                               `(ASI3)`

and choose a section `sigma:K/H->K`.  The only stabilizer elements used on
this window are

`C_(F,W)={sigma(x)^(-1) g sigma(g^(-1)x):g in F,x in W}`
`        subset H`.                                        `(ASI4)`

This is a fixed finite subset of the amenable group `H`.  The proof of the
amenable-stabilizer theorem chooses a tiling of `H` whose shapes are almost
invariant under `(ASI4)`, a Folner set which is a union of those tiles, and
a sofic approximation

`varphi:K->Sym(Omega)`                                     `(ASI5)`

whose restriction to `H` agrees with left translation on the Folner set.
For a set `S subset Omega` of density greater than `1-epsilon`, it produces
injective orbit charts

`pi_u:W->V_fin`, `u in S`,                                `(ASI6)`

such that

`pi_(varphi(g)u)(x)=pi_u(g^(-1)x)`                        `(ASI7)`

whenever every term in the displayed finite window is defined and good.

The bounded set `(ASI4)` is important: every fixed local chart uses only
finitely many honest stabilizer transitions.  But the chart `pi_u` varies
with `u`.  There need not be a map from all of `Omega` to `K/H`, nor a
global `H`-valued Schreier cocycle on a finite principal bundle.  Replacing
the family `(pi_u)` by such a global object is exactly the unjustified step
in the old three-moment proposal.

This also explains why `(ASI1)` is compatible with the property-`(T)`
moment lower bound.  The latter applies to one primitive scalar cocycle on
one finite action.  The former permits the exceptional set and the local
coordinate chart to depend on the root `u` and on the tested window.

## 3. A no-dilution lemma for paired matrix charts

The following elementary estimate is the correct replacement for the
three scalar moments.

Let `Omega` be finite, let `varphi(k)` permute `Omega`, and let
`S subset Omega` satisfy

`|S|>(1-eta)|Omega|`.                                     `(ASI8)`

For each `u in S` and `i in {0,1}`, suppose a finite-dimensional fiber map

`P_(i,u):E->M_d`                                          `(ASI9)`

has been defined on the same finite algebraic window `E`.  Put identical
dummy blocks in the two sectors outside `S` and define block-diagonal maps

`P_i(a)=directSum_(u in Omega) P_(i,u)(a)`.              `(ASI10)`

Let `V_k` be the permutation unitary induced by `varphi(k)` on the block
index.  All Hilbert--Schmidt norms below are normalized.

**Lemma 1 (orbit-chart induction estimate).**  Suppose that on every block
for which `u,varphi(k)u in S`, the local covariance defect is at most
`delta`:

`||P_(i,varphi(k)u)(a)-P_(i,u)(k^(-1) a)||_2<=delta.`    `(ASI11)`

Then

`||V_k P_i(a)V_k^*-P_i(k a)||_2^2`
` <=delta^2+8 eta`.                                      `(ASI12)`

The same estimate holds for multiplication or any fixed finite relation:
average the squared local defect and charge at most `4` for every bad
block occurrence.

If, on the tested positive window `P`,

`max_(u in S)||P_(0,u)(a)-P_(1,u)(a)||_2<=delta`,        `(ASI13)`

then

`||P_0(a)-P_1(a)||_2^2<=delta^2+4 eta`.                 `(ASI14)`

Finally, if a marked label `m` satisfies

`||P_(0,u)(m)-P_(1,u)(m)||_2>=c`                       `(ASI15)`

for every `u in S`, then

`||P_0(m)-P_1(m)||_2^2>=(1-eta)c^2`.                  `(ASI16)`

**Proof.**  The square of the normalized Hilbert--Schmidt norm of a block
diagonal operator is the average of the squared normalized block norms.
On a good-to-good block use `(ASI11)`.  At most `2 eta|Omega|` blocks fail
because either the source or target is outside `S`, and the squared distance
between two contractions is at most `4`.  This gives `(ASI12)`.  Equations
`(ASI14)--(ASI16)` are the same average, with the identical dummy blocks
contributing zero.  A fixed product or relator is handled by the same
calculation after telescoping inside each good block.  End proof.

In particular, if `eta_n,delta_n->0`, a uniform local gap `c>0` survives
globalization.  There is no factor `1/|V_fin|` and no distinguished-fiber
dilution: the local marked block is repeated over a density tending to one
of the orbit-chart roots.

## 4. Application to the paired Fourier--Frobenius construction

The local long-chain theorem in
`FALSE_LONG_FROBENIUS_ELEMENTARY_COMPRESSOR.md` supplies, for the amenable
subgroup `H_0=<t,s>`, two finite fiber models with

1. exact square-zero tangent addition;
2. exact base elementary relations;
3. exact `Q_n` covariance;
4. agreement on an arbitrarily long positive compressor window; and
5. marked squared fold displacement exactly `2`.

By `(ASI1)`, the actual external action

`SL_d(Z) curvearrowright SL_d(Z)/<t,s>`                `(ASI17)`

has orbit charts `(ASI5)--(ASI7)`.  Lemma 1 shows that once the two local
Frobenius maps are assigned functorially to those charts, their external
covariance errors tend to zero and the fold energy remains `2-o(1)`.

What is still missing is not a finite Schreier action and not another clock
calculation.  It is the following compatibility statement:

> For every finite external orbit chart, transport the two long
> Fourier--Frobenius polarizations through the chart so that the transported
> tangent labels preserve the finite Steinberg multiplication table and the
> two transported maps agree on the positive polynomial window.

This is exactly the basepoint stabilizer/relative-holonomy condition in
`FALSE_EQUIVARIANT_FIBER_FUNCTOR_STABILIZER_REDUCTION.md`.  The sofic orbit
charts solve the permutation part of that condition; they do not solve the
matrix-valued relative holonomy.

## 5. Answer to the three-number question

No actual global transversals have been constructed for which all three
numbers in `(ASI2)` tend to zero.  More strongly, for the primitive scalar
clock such transversals do not exist.  Therefore the old scalar computation
should not be run.

What has now been constructed by the cited theorem is the correct real
finite Schreier **chart system** for the amenable stabilizers `B` and
`<t,s>`.  Its transition set on every fixed window is finite, and Lemma 1
proves that it will globalize any chart-functorial paired fiber solution
without losing the marked gap.  This is the surviving endgame for FALSE.

## Reference

David Gao, Gregory Patchell, and Srivatsav Kunnawalkam Elayavalli,
*Sofic actions on graphs*, arXiv:2408.15470, Theorem 2.20 and Lemma 2.18.

