---
rg: 2
id: sl3-hnn-finite-window-central-dual-gap
kind: claim
title: A finite canonical window charges every stable-letter-central SL3 matrix-range separator
distinct_from:
  sl3-hnn-central-dual-gap-vanishes: that is the sequential matrix-ultraproduct formulation; this is its exactly equivalent finitary form, with one finite canonical trace window and one tolerance for each separator norm cutoff and target gap.
  sl3-large-prime-hnn-matrix-range-capture: that asks for primal distance of the selected lattice tuple to the ucp matrix range; this is the smaller dual inequality only for bounded separators approximately central under the selected stable letter.
---

Fix `p>=11` and a finite presentation

```text
G_p=<Gamma,t | [t,Lambda]=1>,
Lambda=SL_3(Z), Gamma=SL_3(Z[1/p]),
```

together with word representatives for a fixed symmetric generating set
`S` of `Lambda`.  For a unitary assignment `x` to the presentation
generators, write `ev_x(w)` for word evaluation, `X_s=ev_x(s)`,
`T=ev_x(t)`, and

```text
h_d(B)=sup_(Y in MR_d(Lambda,S))
       Re sum_(s in S) tr_d(B_s^*Y_s).
```

The **finite central-dual gap claim** is:

> For every `M<infinity` and `epsilon>0`, there are a finite set
> `W subset G_p\{1}` and `delta>0` such that, in every dimension `d`, every
> unitary presentation assignment `x` satisfying
>
> ```text
> max_(r in R)||ev_x(r)-I||_2 <= delta,
> max_(w in W)|tr_d(ev_x(w))| <= delta,                         (FDG1)
> ```
>
> and every tuple `B=(B_s)_(s in S)` satisfying
>
> ```text
> sum_s||B_s||_2^2=1,       max_s||B_s||_op<=M,
> sum_s||T B_s T^*-B_s||_2^2<=delta,                            (FDG2)
> ```
>
> obey
>
> ```text
> Re sum_s tr_d(B_s^*X_s)-h_d(B) <= epsilon.                    (FDG3)
> ```

This is OPEN, and is exactly equivalent to
`sl3-hnn-central-dual-gap-vanishes`.  The equivalence is proved in the two
routes `finite-window-central-dual-implies-sequential` and
`sequential-central-dual-implies-finite-window`.

The quantifier over `M` is essential.  The separator theorem supplies a
uniform bound once a positive primal distance is fixed, but no universal
bound covers separators for all possible gaps.  Conversely `(FDG1)` uses
only scalar canonical moments, not a matrix-valued lifting hypothesis.
Thus this is a genuinely finite matrix-range endpoint: proving one family
of dimension-free inequalities `(FDG3)` closes the large-prime HNN route,
while failure at some fixed `(M,epsilon)` diagonalizes to a canonical
outlier microstate sequence.

The existing firewalls remain visible in this form.  Reduced or full LLP
would prove a much stronger universal lifting assertion and is unavailable;
one-letter, two-letter, endpoint-amplification, and fixed-lamp-frame data are
Morita-neutral.  Any proof of `(FDG3)` must therefore use actor covariance on
a finite mixed Britton window.  If the coset action
`Gamma curvearrowright Gamma/Lambda` is sofic, its finite atlases violate
`(FDG3)` for some fixed `M,epsilon`.

## Attempts

- **The generator diagonal defeats word-orthogonality attacks.**
  `generator-diagonal-is-a-central-matrix-range-separator` sets
  `B_s=X_s/sqrt(|S|)`.  It is uniformly bounded, inherits the stable-letter
  centrality defect exactly, and has gap at least

  ```text
  dist_(2,S)(X,MR_d)^2/(2sqrt(|S|)).
  ```

  Its source pairing is the fixed identity contribution `sqrt(|S|)`, so no
  canonical trace window on nonidentity mixed Britton words can annihilate
  it.  This invalidates `sl3-fdg-via-canonical-word-orthogonality`.  A proof
  of `(FDG3)` must force the matrix-range support function upward -- in
  substance it must build the nearby ucp point -- even on the quantified
  actor-outlier stratum `(FDG-out)`.
- **The exact actor sector needs only one mixed word.**
  `one-britton-commutator-excludes-exact-arithmetic-actor-sector` takes
  `W={[t,h]}`.  Property `(T)` moves an approximately `Lambda`-central letter
  to the exact lattice commutant, finite-dimensional arithmetic co-density
  makes that the `Gamma`-commutant, and the trace of `[t,h]` is forced near
  one instead of its canonical value zero.  Hence every counterexample to
  `(FDG3)` is uniformly noncorrectable already at the actor level; bounded
  congruence depth and exact finite-action atlases are completely absent.
- **The same word gives the exact noncorrectability modulus.**
  `one-britton-moment-forces-uniform-actor-noncorrectability` keeps the
  distance `zeta` from the finite actor packet to every exact
  same-dimensional representation and proves

  ```text
  zeta >=
   [sqrt(2(1-delta_B))-(2sqrt(|S|)/kappa)delta_C]_+
   /(2+4sqrt(|S|)/kappa).
  ```

  Put

  ```text
  c_*=sqrt(2)/(2+4sqrt(|S|)/kappa).
  ```

  After shrinking `delta` and including `[t,h]` in `W`, every tuple admitted
  by `(FDG1)--(FDG2)` has `zeta>=c_*/2`.  Consequently the exact remaining
  finite inequality is `(FDG3)` restricted to the closed quantitative
  outlier stratum

  ```text
  dist_(2,S union {h})(actor, exact Gamma representations)>=c_*/2.  (FDG-out)
  ```

  This restriction is equivalent to the full finite-window claim: the
  one-Britton theorem puts every sufficiently accurate admissible tuple in
  `(FDG-out)`, while the converse restriction is immediate.  Thus what
  remains is an inequality charging the bounded separator on an already
  quantified actor outlier, not another proof that the actor is far from
  exact.
- **Uniform actor outliers can nevertheless be exactly UCP-captured.**
  `p-congruence-packet-is-ucp-exact-but-actor-nonextendable`
  gives a finite arithmetic packet with zero lattice-centrality defect,
  `tr([T,H])=0`, and actor distance at least `c_*`, but with its
  lattice tuple exactly in the UCP matrix range.  Hence `(FDG-out)` is not
  itself a matrix-order defect.  What distinguishes a genuine FDG packet
  from this countermodel is precisely the small defect in all relations of
  `Gamma`, especially denominator transport of the root `e_12(1)`.
- **One root transport still does not connect the two defects.**
  `balanced-denominator-transport-is-ucp-neutral`
  replaces the mod-`p` packet by a congruence actor of modulus coprime to
  `p` and twists the denominator matrix on a two-dimensional multiplicity
  factor.  It satisfies `h e_12(1) h^(-1)=e_12(p)` -- indeed every
  denominator-balanced arithmetic relation -- exactly, retains the uniform
  one-Britton actor-outlier bound, and still lies exactly in the lattice UCP
  matrix range.  Thus the full window must use an unbalanced arithmetic
  closure consequence which detects the denominator multiplicity; merely
  adjoining root conjugacy to `(FDG-out)` cannot charge a separator.
- **The first unbalanced closure word is explicit and sharp on product
  twists.**  `two-torus-closures-detect-denominator-multiplicity` writes
  `h` as the product of the `(1,2)` and `(2,3)` Steinberg torus words after
  replacing their negative roots by `h`-conjugates.  The resulting fixed
  relation has total `h`-exponent `-1`, and on
  `H=V tensor rho(h)` it evaluates exactly to `V^(-1) tensor I`.  It closes
  the pure multiplicity-twist counterpacket with constant one.  The precise
  surviving step is therefore to control an arbitrary outlier separator by
  such a product-normal-form multiplicity coordinate; the ordinary-word
  detector itself is no longer missing.
- **The entire ambient-extendable correction sector is now closed.**
  `unbalanced-torus-extracts-near-central-denominator-coordinate` replaces
  the displayed tensor factor by the intrinsic coordinate
  `H sigma(h)^*` relative to any exact ambient reference `sigma`.  The fixed
  overlap `C intersect hCh^(-1)` has the full image in every finite ambient
  representation, and its conjugacy relators Kazhdan-round that coordinate
  into the full lattice commutant.  The unbalanced word then charges every
  Wedderburn multiplicity block at once.  Consequently a genuine FDG packet
  is not merely far from exact actors as in `(FDG-out)`; its **lattice
  restriction** stays uniformly far from the restriction of every exact
  same-dimensional ambient actor.  The remaining finite inequality must
  charge this sharper ambient-extension outlier.  A dyadic lattice
  correction need not extend ambiently, so this does not yet supply the ucp
  comparison point required by `(FDG3)`.
- **The same word localizes every canonical Britton leak on two roots.**
  `unbalanced-torus-word-localizes-britton-leak` proves, for arbitrary
  approximate packets, that the sum of the commutation defects of
  `H^*TH` with `x_21(-1)` and `x_32(-1)` is at least `sqrt(2)-o(1)`.
  Thus at least one fixed negative simple root carries defect
  `1/sqrt(2)-o(1)`.  The unresolved separator step is now narrower: turn
  this explicit conjugate-letter root leak into payment by the
  `T`-central off-spectral matrix-range separator.
- **Leak energy and off-spectral mass do not couple formally.**
  `unbalanced-root-leak-does-not-charge-off-spectral-separators` gives an
  exact four-dimensional packet where the unbalanced word has zero defect,
  the one-Britton trace is zero, one named root has maximal commutator defect
  two, and a positive-gap separator is fully off the stable-letter spectral
  algebra on that same root coordinate.  This invalidates
  `sl3-fdg-via-unbalanced-root-leak-energy`: the two established estimates
  cannot be joined by a universal Hilbert--Schmidt energy inequality.  The
  packet violates an additional base relation, so FDG remains open; the
  surviving coupling must use further approximate `SL_3` relations to
  construct the ucp comparison point.
- **Universal lifting is unavailable.**  Replacing the selected finite
  window by LP of the lattice generator system would imply LLP of
  `C^*(SL_3(Z))`, contradicted by `sl3-generator-system-has-no-universal-lp`.
  The reduced algebra also has no LLP
  (`sl3-reduced-group-cstar-has-no-llp`).
- **Fixed frames are neutral.**  The one-letter, two-conjugate-letter,
  full-endpoint finite-actor, and fixed-lamp-frame constructions preserve an
  arbitrary pre-existing matrix-range gap exactly.  Consequently enlarging
  `W` by finitely many uncoupled base or lamp moments cannot prove `(FDG3)`.
  A viable window must test mixed Britton words with the same actor carrying
  both the lamp permutation and the lattice coordinates.
- **The exact finite-action atlas is excluded but approximate atlases remain.**
  Profinite co-density and the Kazhdan gap put every exact arithmetic atlas a
  fixed distance away, while a hypothetical sofic coset-action atlas would
  violate `(FDG3)`.  The unresolved finite inequality must therefore charge
  a noncorrectable approximate deck cocycle rather than another congruence
  representation.
