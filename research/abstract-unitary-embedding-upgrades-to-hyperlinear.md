---
rg: 2
id: abstract-unitary-embedding-upgrades-to-hyperlinear
kind: claim
title: A countable group is hyperlinear iff it embeds abstractly in the unitary group of a Connes-embeddable algebra, and fixed-separation unitary models amplify to canonical ones
distinct_from:
  hyperlinear-near-representation-criterion: that is the Kahl--Schneider characterization through essentially free amenable near representations, a charge-type witness; this is the Radulescu characterization through plain group monomorphisms into a unitary group, with no trace, no character and no separation clause, plus its finite-model form.
  kt-double-hyperlinear-iff-mixed-word-trace-selection: that unpacks canonical microstates of one amalgam into four pointwise conditions on two vertex models; this removes the canonical-character clause from the definition of hyperlinearity for every countable group.
---

Let `G` be a countable group.  The following are equivalent.

1. `G` is hyperlinear: unitary models of every accuracy on every finite set,
   with normalized Hilbert--Schmidt separation `2 - epsilon` (the canonical
   character `delta_e`; `IsHyperlinear` in `Sofic/Hyperlinear.lean`).
2. For some `delta > 0`, `G` has unitary models of every accuracy on every
   finite set with separation only `delta` (`IsHyperlinearWeak G delta` in
   `Sofic/HyperlinearReduction.lean`).
3. `G` is isomorphic to a subgroup of `U(R^omega)`; equivalently, there is a
   tracial von Neumann algebra `(N, tau)` with a faithful normal trace that is
   Connes embeddable, and an injective group homomorphism `G -> U(N)`.  No
   condition whatsoever is imposed on `tau` restricted to the image: the
   character `tau(pi(g))` may be nonzero, even close to `1`, for every `g`.

The ultraproduct form `(1) <=> (3)` is Radulescu's theorem (F. Radulescu,
*The von Neumann algebra of the non-residually finite Baumslag group
`<a,b | a b^3 a^-1 = b^2>` embeds into `R^omega`*, Hot Topics in Operator
Theory, Theta 2008, arXiv:math/0004172; recorded as the definition-level
equivalence in Pestov's survey *Hyperlinear and sofic groups: a brief guide*,
Bull. Symb. Logic 14 (2008), Section 3 -- theorem numbers not re-verified
against the PDFs in this session, only the statements).  It is not in this
graph in that form: every consumer so far quotes the trace-preserving version
"`G` hyperlinear iff `L(G)` embeds in `R^omega`", which is the (1)-side only.

## Why the finite-model direction `(2) => (1)` needed a device

`Sofic/HyperlinearReduction.lean` proves only `(1) => (2)` and records why the
permutation amplification argument (`isSofic_iff_weak`) does not transfer
verbatim: tensor powers collapse phases -- `1` and `i.1` are unitaries at
maximal distance with equal fourth tensor powers (`tensorPow_phase_collapse`).
The repair is one line: first direct-sum every model unitary with the identity
of the same size, `v_g = u_g (+) 1`.  A unitary `u (+) 1` is scalar only when
`u = 1`, so for `g != h` the normalized trace `tr(v_h^* v_g) = (z+1)/2` with
`z = tr(u_h^* u_g)`, `|z| <= 1`, `Re z <= 1 - delta/2`, has modulus at most
`sqrt(1 - delta/4) < 1`, and tensor powers now drive every pairwise
separation to `2 - o(1)` at the cost of multiplying the multiplicativity
defect by the number of factors.  The proof route carries the estimates.

## What it buys

Hyperlinearity of a concrete group can be certified by an *abstract* unitary
embedding.  For the coset wreath `W = (+_(G/Gamma) C_2) x| G` this reads: `W`
is hyperlinear iff there are a Connes-embeddable tracial `(N,tau)`, a
homomorphism `pi : G -> U(N)` (not necessarily faithful, with any character),
and a projection `q in pi(Gamma)' cap N` whose conjugates
`q_x = pi(g) q pi(g)^*`, `x = g Gamma`, pairwise commute and are Boolean
independent (every finite cylinder `prod_(x in F) q_x^(eps_x) (1-q_x)^(1-eps_x)`
is nonzero).  Faithfulness on `G` and the canonical character are bought back
for free by tensoring with a regular-character model of `G` and applying the
upgrade; the Bernoulli values `2^(-|F|)` are never needed.  Equivalently: a
`G`-invariant probability measure on `{0,1}^(G/Gamma)` charging every cylinder,
together with a trace on the crossed product `C(Z) x|_full G` extending it whose
GNS algebra is Connes embeddable.  For the free-lamp group
`E = G *_Gamma (Gamma x K)` it reads: a faithful `pi` and a copy of `K` in
`pi(Gamma)' cap N` generating, with `pi(G)`, the amalgam.

The device is what makes `amenable-kazhdan-models-absorb-compression` bite: that
theorem constrains every unitary representation of a compressed Kazhdan pair,
and by this equivalence "every unitary representation" is the right class.
