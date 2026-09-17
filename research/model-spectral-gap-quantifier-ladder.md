---
rg: 2
id: model-spectral-gap-quantifier-ladder
kind: claim
title: A representation-generic proof of the Kesten model spectral gap is a Kazhdan theorem, and the corona-quantified gap for the binary Leavitt group is implied by its endpoint
distinct_from:
  kesten-spectral-gap-replaces-kazhdan-projection-per-model: that isolates (MSG) as the only Kazhdan input of the transport and normal-subgroup proofs and calibrates its failure on one free-group block; this proves that (MSG) along every unitary representation of any ambient group G is equivalent to property (T) for L by induction from L to G. The ambient group therefore gives no leverage, and only matrix-origin arguments can remove (T).
  native-cross-gram-conclusions-fail-in-every-tracial-model: that shows the cross-Gram conclusion is false in tracial models, so its premises hold only vacuously; this concerns the spectral-gap substitute, whose conclusion is true in the regular representation, and locates the obstruction instead in the universal representation and in the corona quantifier.
  window-average-kazhdan-substitute-forces-trivial-corona-rep: that kills norm limits of Folner-window averages over an amenable root subgroup; this kills every argument that proves the isolated-eigenvalue substitute from the group relations of G and C-star functional calculus alone, for every finitely generated L.
  kesten-amenable-stabilizer-uniform-gap: that proves a uniform Kesten gap on coset spaces of amenable subgroups; this uses induced representations from L only to transport spectra into the universal representation of G.
---

**ESTABLISHED (written proof; not Lean-verified).**  This is an
obstruction to a class of approaches.  Notation follows
`kesten-spectral-gap-replaces-kazhdan-projection-per-model`.  Let `G` be
countable, let `L<=G` be finitely generated, let `S` be a finite
symmetric generating set of `L` with `e in S`, and let
`h_S=(1/|S|) sum_(s in S) u_s`.  For a unital C-star algebra `A` and a
homomorphism `rho:G->U(A)`, `(MSG)` on `L` says that `1` is not an
accumulation point of `sp(rho(h_S))`.

1. **Ladder rung 0 (all representations).**  The following are
   equivalent:
   - (a) every unitary representation `pi` of `G` on a Hilbert space
     satisfies `(MSG)` on `L`;
   - (b) the universal representation `rho_u:G->U(C*(G))` satisfies
     `(MSG)` on `L`;
   - (c) `L` has property `(T)`.

   Quantitatively, if `sp(rho_u(h_S))` misses `(1-c,1)`, then
   `(S, sqrt(2c))` is a Kazhdan pair for `L`.  Conversely, a Kazhdan pair
   `(S,kappa)` gives `c=kappa^2/(2|S|)` for every representation of `G`
   into every unital C-star algebra.  If `L` does not have `(T)`, then `1`
   is an accumulation point of `sp(rho_u(h_S))`.
2. **The class it kills.**  Consider arguments that derive `(MSG)` on `L`
   for a homomorphism `rho:G->U(A)` using only the relations of `G`, the
   C-star identities and functional calculus of `A`, and statements valid
   for every such `rho`.  With no property of `A` or of `rho` beyond
   being a unitary representation, every such argument applies to
   `rho_u`.  If `L` does not have `(T)`, the conclusion is false there,
   so the argument is wrong.  If `L` has `(T)`, the argument with its
   explicit constant is a proof of a Kazhdan pair for `L`.  It renames the
   Property `(T)` input instead of removing it, which the goal
   `property-t-free-manuscript-results` forbids.  Every member dies at
   the same step, the specialization to `Ind_L^G sigma` for an
   `L`-representation `sigma` with almost invariant vectors and no
   invariant vectors.  The invariant is the reducing copy of `sigma` on
   the sections supported on the coset `L`.  The ambient group `G` never
   helps: the conclusion of item 1 depends only on `L`, not on `G`.
3. **Ladder rung 1 (MF targets): the endpoint implies it.**  Let `G` have
   `Rad_MF(G)=G`, for example the endpoint
   `Delta=St_20(L_(F_2)(1,2))` of `property-t-free-leavitt-full-mf-radical`.
   Every homomorphism `G->U(A)` with `A` an MF algebra is trivial, so
   `(MSG)` holds for it with `sp={1}`.  Hence the hypotheses "`(MSG)`
   along every corona homomorphism of `G`" (the normal-subgroup
   substitute of the per-model lemma, item 3) and "`(MSG)` in the adjoint
   corona of every `delta_e`-profile model of `G`" (the transport input)
   both follow from the endpoint.  The second holds vacuously, because a
   group with full radical has no `delta_e`-profile model.  So as
   prerequisites they add no strictly weaker target.  The manuscript
   collapse consumes them through the transport theorem, so they are a
   reformulation of the endpoint, not a reduction of it.
4. **Diracization does not restrict the bad block.**  Suppose `G` has one
   `delta_e`-profile operator-norm model `(V'_n)`, and let `(W_n)` be any
   operator-norm model of `G`, with any trace profile.  Then some
   amplification `V''_n=V'_n tensor I_(k_n)` makes `V''_n (+) W_n` a
   `delta_e`-profile model.  Its adjoint corona homomorphism contains the
   adjoint corona homomorphism of `(W_n)` as a reducing corner.  Hence
   `(MSG)` on `L` for the adjoints of all `delta_e`-profile models implies
   `(MSG)` on `L` for the adjoint of every operator-norm model of `G`.
   The `delta_e` profile gives no spectral control.  Every model of `G`
   occurs as a `tau`-null block of vanishing normalized rank, which is the
   location of the free-group failure in the per-model lemma, item 4.

## Consequence for the Property-(T)-free program

`(MSG)` is the only Kazhdan input of the manuscript transport.  A
Property-`(T)`-free proof of it must therefore use a property of the
target or of the model that fails for `C*(G)`: matrix origin, stable
finiteness, a trace, or finite-dimensional correction.  It cannot use the
relations of `G` alone, however rich `G` is.  Together with item 4, the
spectral input has to be extracted from the operator-norm approximation of
an arbitrary model `W` of `G`.  This is the same difficulty as the
endpoint.  The rungs that remain undecided are arguments valid for all
representations into finite von Neumann algebras or into stably finite
C-star algebras.  The induced representation is not tracial, so item 1
does not reach them.

Proof route: `model-spectral-gap-quantifier-ladder-proof`.
