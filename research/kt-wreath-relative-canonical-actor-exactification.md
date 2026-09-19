---
rg: 2
id: kt-wreath-relative-canonical-actor-exactification
kind: claim
title: Canonical Kun--Thom wreath microstates exactify on the actor leg
distinct_from:
  wreath-flexible-hs-stability: that asks flexible HS stability for every almost-representation of the full candidate; this asks only to exactify the actor restriction of canonical separating microstates of the Kun--Thom wreath
  invariant-cartan-completion: that reconstructs one globally invariant diagonal ultraproduct; this asks for no masa and no classicalization of the lamp algebra
  kt-centralizer-normalization-hs: that asks for relative-commutant normalization in every tracial ultraproduct representation of the actor; this asks only for finite-dimensional exactification along restrictions of canonical wreath microstates
  kazhdan-weak-ucp-stability-is-flexible-stability: that is a general equivalence for all hyperlinear approximations of a Kazhdan group; this is a strictly restricted approximation class selected by extension to the pinned wreath presentation
---

OPEN.  Fix the explicit Kun--Thom Theorem E pair `Gamma<G`, a strict
compressor `t Gamma t^(-1)<Gamma`, and

```text
W=(direct_sum_(G/Gamma) C_2) rtimes G.                  (KRE1)
```

Fix a finite generating set of `W` and an enumeration of its defining
relations.  Let `phi_n` be any canonical normalized-Hilbert--Schmidt
microstate sequence satisfying the first `n` relations.  Prove that, after
adding `o(d_n)` dimensions, the restriction `phi_n|G` is `o_2(1)` on the fixed actor
generators from a genuine finite-dimensional representation

```text
pi_n:G -> U(D_n),             D_n/d_n -> 1.             (KRE2)
```

This is the weakest stability statement currently sufficient for the pinned
Kun--Thom wreath endpoint.  It does not quantify over arbitrary
almost-representations of `G`, does not exactify the lamp generators, and does
not ask that the resulting actor representation be finite-image or monomial.

If `(KRE2)` holds, `W` is not hyperlinear.  Indeed, property `(T)` of
`Gamma` moves the base-lamp involution, which almost commutes with
`phi_n(Gamma)`, to an involution in `pi_n(Gamma)'` at `o_2(1)` cost.  Its
`t`-translate lies in `pi_n(t Gamma t^(-1))'`.  Finite-dimensional
commutant no-growth gives

```text
pi_n(t Gamma t^(-1))'=pi_n(Gamma)'.                    (KRE3)
```

Choose `gamma in Gamma\t Gamma t^(-1)`.  Equation `(KRE3)` makes the rounded
`tGamma` lamp asymptotically fixed by `gamma`, whereas the canonical wreath
trace makes the two distinct lamps at `tGamma` and `gamma tGamma` have
normalized `2`-distance `sqrt(2)`.  This is a contradiction.

For calibration, exactifying the whole canonical microstate would be much
stronger than necessary and would force residual finiteness directly: the
exact representations eventually separate every nonidentity word, and each
finitely generated linear image is residually finite.  The actor-only
statement above reaches the contradiction before any such global conclusion.

## Sharp one-compressor firewall

`kt-single-compressor-canonical-lamps-do-not-exactify-actor` proves that the
corresponding claim is false for every single positive strict compressor.
The restricted coset action is sofic, hence its binary wreath has canonical
permutation microstates satisfying all Bernoulli cylinder and mixed
lamp--actor traces; nevertheless their actor restrictions stay a uniform
distance from every genuine finite-dimensional representation after
negligible padding.  The proof is the same finite-dimensional commutant
collapse which would consume `(KRE2)`.

Therefore the only possible source of `(KRE2)` is simultaneous
multi-compressor compatibility.  Property `(T)`, one compression edge,
finite-packet exactification, and all local canonical lamp moments cannot
prove it.  This matches Kun--Thom's nonsoficity theorem: every individual
compressor action is sofic and the obstruction first appears when the full
compression semigroup is imposed.

`kt-two-positive-compressors-generate-full-obstruction` makes this frontier
literal with two named matrices.  For the `d=3` Theorem E pair, if `C` is the
cyclic coordinate permutation, then

```text
B=I+E_12,                    A=C B
```

are positive strict compressors and `<Gamma,A,B>=G`.  Each one-compressor
action is sofic, but their canonical permutation/lamp models admit no common
joint refinement; nonsoficity gives a fixed finite joint table with a
positive defect floor.  Thus two compressors are both necessary and already
globally sufficient on the **permutation** side.  Upgrading exactly this
two-compressor incompatibility from common permutation models to arbitrary
canonical unitary-HS microstates is `(KRE2)`; Pimsner--Popa growth does not do
so because both strict directions have infinite index in the exact Clifford
model and the index is not HS-continuous.

There is a further exact scope restriction.  By
`kt-two-compressor-lamp-orbit-is-a-sofic-regular-wreath`, the orbit of the
base coset under `<A,B>=SL_3(Z)` is the regular `SL_3(Z)`-set, and its binary
lamp semidirect product is residually finite.  Hence **all** `A,B`-orbit
cylinder PVMs, their joint covariance, actor multiplication, and canonical
mixed traces already have common permutation models and an invariant masa.
The finite family needed for `(KRE2)` must therefore include mixed
`Gamma`-stabilizer incidences on transported cylinders.  A common masa for
`A,B` alone cannot meet the known permutation defect; the missing transfer is
relative to the nonnormal Kazhdan subgroup, not a two-unitary normalizer
lemma.

The first mixed cylinder can also be named explicitly.
`kt-ab-marked-return-is-the-first-mixed-cylinder` takes
`r=e_12(x_1) in Gamma` and an `A,B` word `L` whose first exponent column is
`-(1,1,1)`.  Then
`h=LrL^(-1)=e_12((x_1x_2x_3)^(-1))`, and the two lamps at
`Gamma,hGamma` are exactly the marked pair whose finite two-point tables are
forbidden.  Hence no large cylinder packet is missing after a common
diagonal has been produced: two sites suffice.  What is missing is the
simultaneous diagonalization/classicalization of their multiplicity cocycle
using this mixed Gamma--compressor return; separate two-site covariance has
an exact finite boundary countermodel.

Even the visible Gamma root in that return is not enough by itself.
`kt-single-root-mixed-return-has-exact-finite-countermodels` reduces Laurent
exponents modulo `N` and wreathes the finite coset space by the cyclic subgroup
generated by `r`.  It satisfies the full actor table, `[a,r]=1`, and
`b=hah^(-1)` exactly while the two lamp projections retain squared
normalized-HS distance `1/2`.  Hence the sought transfer cannot be a
single-correlation inequality attached only to `r` and `h`; it must consume a
finite Kazhdan generating family of Gamma-stabilizer rows jointly with the
mixed lamp table.

That finite family can be fixed explicitly.  The elementary packet in
`kt-elementary-kazhdan-packet-rounds-base-lamp` consists of all constant root
elements `e_ij(c)` and the positive and negative variable roots
`e_ij(+-x_l)`.  Steinberg commutators generate all of `Gamma`, and its
Kazhdan constant gives the dimension-free estimate

```text
dist_2(P, Proj(pi(Gamma)'))
 <= (sqrt(2)/kappa_K) max_(s in K)||[P,pi(s)]||_2.
```

Together with actor closeness on `K union {h}`, this also rounds the second
lamp to `pi(h)P_0pi(h)^*` with an explicit linear error bound.  Hence the
stabilizer-rounding portion no longer requires an unspecified packet.  What
remains is exactly the KRE actor exactification and the subsequent control of
the action of `pi(h)` on the multiplicity commutant.

Already for a genuine representation of the Laurent elementary actor, that
subsequent control is automatic.  By
`kt-full-kazhdan-majorana-return-collapses-in-fd`, finite-dimensional
compression invisibility gives `pi(h) in pi(Gamma)`, and therefore

```text
||[X,pi(h)]||_2
 <= (2/kappa_K) max_(s in K)||[X,pi(s)]||_2.
```

In particular the full packet and the mixed return cannot support an exact
finite-dimensional Majorana pair.  This does not remove `(KRE2)`: the
finite-image inclusion has not been proved quantitatively for an approximate
actor.  It does show that there is no further exact multiplicity-algebra
obstruction after actor exactification; the live gap is precisely the
normalized-HS passage from approximate actor relations to this genuine-actor
inequality.

Moreover this passage cannot fail only on a negligible actor corner.
`kt-majorana-wall-certifies-macroscopic-actor-instability` gives the explicit
reverse estimate: vanishing packet and Majorana-row defects force a fixed
`K union {h}` distance `>=2/(8/kappa_K+4)` from every genuine actor.  The
same lower bound survives `o(d)` padding, and a positive lower bound survives
every bounded amplification ratio.  Thus a full-wall countermodel, if it
exists, is automatically a positive-density witness to source-specific
Laurent-actor instability; an unbounded amplification is the only remaining
way to dilute that witness during exactification.

Adding the entire external actor does not remove generic local instability.
`kt-full-actor-extension-is-locally-hs-unstable` applies the local-HS
instability theorem directly to the full residually finite Kazhdan group
`G`, using the generating set `K union {h,A,B}`.  It produces bad actor
microstates already satisfying both compressor directions and all semidirect
relations.  They extend through every binary wreath relation with a balanced
central lamp after a fixed doubling, but all lamp sites then coincide and
their distinct-site product trace is `1` rather than `0`.  Therefore the
genuine extra restriction in `(KRE2)` is exactly canonical positive-density
lamp separation; neither full actor extendability nor the abstract wreath
relations can be substituted for it.  Local instability is strict, so this
paragraph does not itself rule out flexible correction after the doubling.

For the canonical deleted-line instability witnesses that caveat is
decisive in the opposite direction.  `kt-deleted-line-instability-cannot-carry-majorana-wall`
adds back the single missing dimension, compares with the original genuine
actor representation, and obtains an explicit lower bound forcing the
returned anticommutator norm to `2`.  Thus the known local-instability
construction cannot satisfy the canonical two-site Majorana row.  Any
countermodel to `(KRE2)` must be a new macroscopic unstable sector, not the
standard codimension-one Kazhdan witness.

Gamma-only exactification does not bypass this gate through polar rounding.
`kt-kazhdan-polar-compressor-rounding-is-directional` applies property `(T)`
to the Hom representation for one strict compressor and obtains a partial
intertwiner on `1-o(1)` physical trace.  Its forward transport of a
`pi(Gamma)`-central lamp lies only in
`pi(alpha(Gamma))'`, exactly the stabilizer of `tGamma`; the adjoint controls
the backward, not the forward, lamp.  Extending the partial intertwiner to a
unitary requires matching the small complementary representation types, and
small physical trace does not control their commutant index.  Exact-Gamma
one-compressor telescope models realize this obstruction while retaining the
marked lamp separation.  Hence a terminal reduction still needs full actor
exactification or a multi-compressor mechanism that charges the unmatched
support types.

Nor does the pair `A,B` create a scalar free-boundary gap on the weighted
Gamma-irrep multiset.  `kt-two-compressor-irrep-flow-has-profinite-stationary-points`
uses residual finite quotients of the full actor.  In every such quotient the
two strict inclusions become automorphisms of the finite image of `Gamma`, so
its regular Plancherel vector is exactly stationary under both precomposition
flows while matching the canonical actor trace on any prescribed window.
For general irreducibles the flows can moreover branch under restriction.
The marked lamp lives in the multiplicity algebra `pi(Gamma)'`, which the
scalar Plancherel vector forgets.  Hence the remaining two-compressor estimate
must act on a named commutant projection and use its mixed-return trace; an
irrep-counting or free-semigroup boundary inequality alone is ruled out.

The first noncommuting pair is still insufficient at the covariance level.
`amenable-multi-compressors-have-a-joint-hs-telescope` treats the positive
transvections `u_13,u_32`, whose commutator is `u_12`.  Their positive
semigroup is Heisenberg and has explicit Følner boxes; a block telescope
satisfies both covariance rows, their Steinberg relation, and every fixed
local lamp/packet table with `O(L^(-1/2))` normalized-HS error.  Thus
“at least two” must not be read as a two-row theorem.  The remaining content
of `(KRE2)` must use global canonical lamp correlations across a
nonamenable generating family, or an equivalent recovery of the lamp
algebra; finite Heisenberg-window compatibility retains a joint cocycle
countermodel.

The smallest nonamenable positive family is another explicit pair.
`opposite-transvections-are-free-but-finite-lamp-windows-close` proves by
projective ping-pong that `u_12,u_21` generate a free positive monoid and
satisfy

```text
sum_(S in {u_12,u_21}) |FS triangle F| >= 2|F|.
```

This boundary would give a uniform HS floor if one fixed lamp test menu
decoded every wrong boundary match.  Canonical convergence separates each
fixed pair of lamps, not the model-dependent boundary words whose depths
diverge.  Indeed every bounded positive-cone lamp window has an exact finite
Bernoulli model from a congruence quotient.  Those models fail precisely on
the `Gamma`-moved-site correlations collapsed by normality of finite images
of `Gamma`.  Thus free-cone expansion alone is not `(KRE2)`; the missing
inequality must couple its boundary uniformly to the stabilizer lamp table.

`free-compressor-tree-has-constant-first-hit-mover-mass` performs that
finite-depth coupling exactly in the canonical wreath.  Dyadic prefix
cylinders on the free binary compressor tree give pairwise orthogonal leaf
exits, each fixed by its child stabilizer and moved by an element of its
parent stabilizer, with total squared mover displacement exactly `1/2` at
every depth.  Thus geometric first-hit dilution is not the obstruction.
The exits supply only `2^n` vectors in the `d^2`-dimensional adjoint space,
however, so at every fixed depth their normalized adjoint rank is at most
`2^n/d^2`.  Existing property-`(T)` no-growth therefore does not consume
them.  The remaining statement is a depth-uniform aggregate inequality
like `(FCT8)`, equivalently a common positive-density lamp/Cartan decoder;
congruence windows fail exactly the required `Gamma`-moved leaf row.

The apparent left-multiplication amplifier does not close this gap.
`fct8-left-lift-and-rotated-defect-firewall` shows that `L_(X_w)` has
normalized superoperator trace `tau(X_w)` and preserves the half-unit mover
mass, but commutes with the child adjoint representation only as an
**invariant-range projection**; its range is not pointwise fixed.  The
self-copy fixed-sector theorem therefore cannot consume it.  The rank-one
lift has pointwise-fixed range but returns to trace `1/d^2`, while an exact
permutation-block example shows that summing branchwise conjugates of one
sparse relator defect necessarily permits a `2^n` loss.  A successful
`(FCT8)` proof must exploit extra joint prefix-unitary/lamp structure.
