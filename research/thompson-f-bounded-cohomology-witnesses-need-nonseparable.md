---
rg: 2
id: thompson-f-bounded-cohomology-witnesses-need-nonseparable
kind: claim
title: Every bounded-cohomology witness of non-amenability for Thompson's F generates a norm-non-separable weak*-closed coefficient module, and every l^1_0 permutation module of F has bounded cohomology R in degree one and zero above
distinct_from:
  thompson-f-finite-state-flows-cannot-prove-nonamenability: that kills transport flows read off a finite tree automaton; this kills cohomological witnesses whose coefficients are separable, by an ergodic argument with no combinatorics.
  thompson-f-moment-data-cannot-certify-nonamenability: that is about finitely many return probabilities; this is about bounded cocycles with values in Banach modules.
  thompson-f-end-rigid-schreier-graphs-are-amenable: that kills particular Schreier graphs; this computes the bounded cohomology of every l^1_0(F/H) and shows no separable dual module can carry the Johnson class of any F-set.
  amenable-normalish-kills-l2-betti-bounded-cohomology: that uses an amenable normalish subgroup and mixing coefficients; this uses Monod's lamplighter ergodicity and all separable dual coefficients.
---

**ESTABLISHED** through `thompson-f-bounded-cohomology-witnesses-need-nonseparable-proof`.
It is a direct proof on top of one import, Monod, *Lamplighters and the bounded cohomology of Thompson's
group*, arXiv:2112.13741, Theorems 1 and 2. It has not been independently reviewed. The vanishing theorem
is Monod's. What this node adds is the certificate-shape form, the `l^1_0` computation and the calibration.

**Setting.** A *dual Banach F-module* is `E = (E_*)^*` with the dual of an isometric `F`-action on the
Banach space `E_*`. Bounded cohomology `H^n_b(F; E)` uses bounded inhomogeneous cochains. A *bounded
cohomology witness* is a bounded cocycle `c : F^n → E`, `n >= 1`, whose class is nonzero. Such a witness
proves non-amenability, because amenable groups have `H^n_b(G; E) = 0` for every dual module
(Johnson). If `F` is not amenable, a witness exists for some `n >= 2` (Monod, ICM 2006, as recalled in
arXiv:2112.13741 §4.C).

**Theorem.**
1. *(Shape.)* Let `c` be a witness for `F` in degree `n >= 1`. Let `W_c` be the weak*-closed linear span of
   `{g · c(g_1, ..., g_n)}`. Then `W_c` is a dual `F`-submodule and it is **not norm-separable**. The
   norm-closed span `S_c` of the same countable set is separable and `F`-invariant, so it is never
   weak*-closed.
2. *(Killed modules.)* `H^n_b(F; E) = 0` for all `n >= 1` when `E` is any of the following:
   `l^p(X)` for a countable `F`-set `X` and `1 <= p < ∞` (for `p = 1` the predual is `c_0(X)`); `L^p(Y, μ)`,
   `1 < p < ∞`, with the isometric twisted Koopman action of a non-singular action on a standard space;
   a unitary representation on a separable Hilbert space; Schatten classes `S_p(H)`, `1 <= p < ∞`, of a
   separable `H` under conjugation by a unitary representation (for `p = 1` the predual is `K(H)`); any
   finite-dimensional isometric module.
3. *(The `l^1_0` computation.)* Let `X` be an `F`-set with no finite orbit. Then
   `H^1_b(F; l^1_0(X)) ≅ R`, spanned by the Johnson class `j_x(g) = δ_(g x) - δ_x`, and
   `H^n_b(F; l^1_0(X)) = 0` for every `n >= 2`. The class `j_x` dies in the bidual
   `l^1_0(X)^** = {ξ ∈ l^∞(X)^* : ξ(1) = 0}` exactly when `X` carries an `F`-invariant mean. No bounded
   equivariant map from `l^1_0(X)` into a separable dual module carries `j_x` to a nonzero class.

**What dies.** Non-amenability of `F` cannot be certified by:
- quasimorphisms, bounded Euler classes or any class with trivial real coefficients (Monod Theorem 1);
- bounded cocycles into `l^p` or `L^p` spaces, separable Hilbert spaces or trace-class operators;
- any cohomological argument that only ever uses a countable orbit of vectors inside a module where that
  orbit has separable weak*-closure;
- higher-degree classes on the permutation modules `l^1_0(F/H)`, for every subgroup `H` of infinite
  index. There the only class is the degree-one Johnson class. Detecting it means passing to the
  non-separable bidual, which is the invariant-mean question itself.

The step where the method fails is the ergodicity step. A separable dual module is second countable,
so the diagonal Bernoulli action of a co-amenable lamplighter inside `F'` forces equivariant
measurable maps to be constant.

**Calibration.** Degree one is universal: `H^1_b(G; E) = 0` for every group and every separable dual `E`
(Ryll-Nardzewski). So only the degree `>= 2` parts of items 1 and 2 are special to `F`. They are not
special to amenable groups. Monod's proof holds unchanged for the non-amenable piecewise-projective
groups `H(A)` of arXiv:1209.5229, so items 1–3 hold verbatim for a known non-amenable group. Separable
bounded cohomology therefore cannot separate amenable from non-amenable groups of this dynamical type,
in either direction. The separability gate is sharp: for `G ≀ Z` with `H^2_b(G) ≠ 0` Monod exhibits
`H^2_b(G ≀ Z; l^∞(Z)) ≠ 0`. Duality is needed too: `H^1_b(G; l^1_0(G)) ≠ 0` for every infinite `G`.

**Surviving shape.** A witness must use a module such as `l^∞(F/H)` or `l^1_0(F/H)^**`. By Shapiro's lemma
`H^n_b(F; l^∞(F/H)) ≅ H^n_b(H; R)`, so the most concrete survivor is a subgroup `H <= F` that is not
boundedly acyclic. Monod's Corollary 6 rules out every `H` with the compressible-support dynamics used
there, so `H` must fail it.

**Scope.** This proves neither answer. It kills one class of witnesses for `thompson-f-is-not-amenable`.
