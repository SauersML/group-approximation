---
rg: 2
id: finite-orbit-indices-miss-twists-without-finite-quotients
kind: claim
title: Indices read from finite-orbit cluster type data cannot see realized twists from groups without finite quotients, where the Leavitt cover's relative defect lives
distinct_from:
  conjugation-invariant-sizes-miss-relative-defect: that shows sizes read from conjugacy invariants of realizer sets are exactly compressor invariant; this concerns data relative to sigma(Gamma), such as Kun--Thom cluster type distributions, and shows that their finiteness makes every index built from them factor through finite images of the realized twist group.
  realized-relative-twists-embed-in-outer-twist-group: that identifies the realized twist quotient as a stabilizer in the outer twist group; this bounds what any finite-orbit datum on that stabilizer can detect.
  relative-normalization-modulo-kazhdan-kernel: that is the open normalization statement; this rules out one form of size argument for it, a relative index bounded by finiteness of cluster types.
---

**ESTABLISHED.** Setting and notation as in
`realized-relative-twists-embed-in-outer-twist-group`: a rigid pair
`Gamma <= G`, `M <= Gamma` normal in `G`, a homomorphism `sigma : G -> S_U`,
the realized twist group `Q_s`, and the compressor endomorphisms `eps_t`.

A **finite-orbit datum** is a set `X` with an action of `Q_s` and a
`Q_s`-invariant mass function `mu : X -> [0, infinity)` with `sum_x mu(x) <= 1`.
Write `X_+ = {x : mu(x) > 0}`, `P` for the image of `Q_s` in `Sym(X_+)`, and
`pi : Q_s -> P`.

The intended example is the distribution of isomorphism types of
`Gamma_s`-components at a fixed perturbation scale, with realized twists acting
by precomposition, together with the same distribution for the compressed
subgroup `sigma(t Gamma t^-1)`. Precomposition by a realized twist sends the
type distribution of `sigma|_Gamma` to that of a conjugate representation, so
it preserves the masses. Kazhdan rigidity of the components is what gives
positive masses to finitely many types per mass scale.

1. **Finite orbits.** Every `Q_s`-orbit in `X_+` is finite. An orbit through `x`
   has at most `1/mu(x)` points.
2. **Blind on groups without finite quotients.** Every subgroup `A <= Q_s` with
   no nontrivial finite quotient acts trivially on `X_+`, so `pi(A) = 1`.
3. **What data-derived bounds constrain.** Call a quantity attached to a
   subgroup `B <= Q_s` *data-derived* if it is a function of `pi(B)` and `mu`.
   Orbit counts on `X_+`, masses of `B`-orbits, and indices of stabilizers in
   `P` are all of this form. A bound obtained from such quantities, for
   instance a Kun--Thom-type "integer index below 2" comparison of `pi(B)` with
   `pi(eps_t(B))`, constrains only `P`. It says nothing about `ker pi`, which
   contains every subgroup of `Q_s` without nontrivial finite quotients.
4. **The Leavitt cover.** Take the configuration of
   `leavitt-unit-group-carries-nontrivial-rigid-defect` lifted to
   `hyperbolic-kazhdan-cover-of-leavitt-unit-group`, with `M = N` and
   `Q = C_(R^x)(EL_alpha(R))` as in
   `relative-defect-iff-surjective-compressor-endomorphisms`.
   - `J = V_(1000)` commutes with `EL_alpha(R)`, so it lies in `Q`. It is
     isomorphic to Thompson's `V`, an infinite simple group
     (`thompson-v-finitely-presented-infinite-simple`), so it has no
     nontrivial finite quotient.
   - `A = <eps_u^k(J) : k >= 0>` has no nontrivial finite quotient and satisfies
     `eps_u(A) <= A`.
   - `A` contains the class `[z]` of a lift of the defect element `j`, and
     `[z]` is not in `eps_u(Q)`, hence not in `eps_u(A)`. So `eps_u` restricts
     to a strict self-embedding of `A`.
   - For any injective homomorphism `sigma` of a host containing the
     configuration, item 5 of
     `realized-relative-twists-embed-in-outer-twist-group` embeds `A` in `Q_s`
     compatibly with `eps_u`.

   On every finite-orbit datum, `A`, `eps_u(A)` and the trivial group therefore
   have the same image `1`. No data-derived index is strictly monotone along the
   strict self-embedding that carries the cover's relative defect.

Derivation: `finite-orbit-indices-miss-twists-proof`.

**This is an obstruction to a method, not evidence about soficity.** The proof
uses no property (T) and no soficity, and it holds in amenable hosts. Property
(T) of the components enters only as the source of the hypothesis
`sum mu <= 1` with finitely many positive-mass types per scale. That finiteness
forces item 1, and item 1 is exactly what makes these indices blind to twists
coming from groups such as Thompson's `V`.

**What survives.** A size that can register the cover's defect has to use
infinite-orbit data relative to `sigma(Gamma)`, on which `V` can act
nontrivially. One shape is the action of `Q_s` on the measure space of
`Gamma_s`-components, together with the compressor refinement factor from
`sigma(t Gamma t^-1)`-components to `Gamma_s`-components and its fibre counts.
Those are the ultraproduct forms of the finite-stage orbit and isotropy sizes of
Kun--Thom Theorem 4.1, with counting replaced by measure. None is constructed
here.
