---
rg: 2
id: cantor-integer-maps-central-growth-criterion
kind: claim
title: "For G = C(C,Z) ⋊ V, a cnd function is unbounded on the central direction <1_C> iff the off-centre part of its cocycle is not a coboundary; some cnd function is unbounded there iff some unitary representation of G has almost invariant vectors and no nonzero 1_C-invariant vector"
distinct_from:
  cantor-integer-maps-sup-norm-is-cnd-dominated: that asks for one cnd function dominating the sup norm on all of C(C,Z); this is the exact criterion for the much weaker necessary condition of growth along the single central direction <1_C>
  cantor-integer-maps-by-v-have-haagerup-property: that is Problem B(Z) itself; this proves that failure of relative property (T) for (G, <1_C>) is a necessary prerequisite, and characterizes that failure spectrally
  cantor-integer-maps-by-v-are-not-a-t-menable: that is the negative conjecture; this gives its weakest known sufficient condition in the relative-(T) family (relative (T) for the central cyclic subgroup) and a coboundary criterion to test it against
  brin-thompson-nv-fibre-elements-are-cubically-elliptic: that makes 1_C bounded in every commensurating (wall) action, a cubical statement; this treats every cnd function, where boundedness is not automatic, and reduces unboundedness to an almost-invariant-vector problem
  commensurating-loxodromics-split-their-centralizers: that is a character-splitting argument for commensurating actions; here the splitting is a spectral decomposition of an arbitrary affine isometric action along the central unitary pi(1_C)
---

**Setting.** `C = {0,1}^ω`, `A = C(C,Z)`, and `G = A ⋊ V` with `(h·f)(w) = f(h^{-1}w)`. The
element `z = 1_C` is central (constants are `V`-invariant), undistorted, of infinite order.
A cnd function on `G` is `ψ(g) = ‖b(g)‖²` for a cocycle `b` of a unitary representation `π`
on a Hilbert space `H`. Write `e(t) = exp(2πit)`.

**Theorem A (central coboundary splitting).** Let `H_1 = ker(π(z) − 1)` and, for `j ≥ 0`, let
`P_j` be the spectral projection of `π(z)` onto `{e(t) : 2^{-j-2} < |t| ≤ 2^{-j-1}}`. These
projections commute with `π(G)`, and `H = H_1 ⊕ ⊕_j P_jH`. Write `b_1`, `b_j` for the
components of `b`. Then:
1. `b_1(z) = 0`;
2. `b_j(g) = (π(g) − 1)ξ_j` for all `g ∈ G`, where `ξ_j = (π(z) − 1)^{-1} b_j(z) ∈ P_jH`;
3. with `S = Σ_j ‖ξ_j‖² ∈ [0, ∞]`, one has `2S ≤ sup_M ψ(z^M) ≤ 4S`.

In particular `ψ` is bounded on `<z>` iff `b` restricted to `H_1^⊥` is a coboundary.

**Theorem B (growth criterion).** The following are equivalent:
- (a) some cnd function on `G` is unbounded on `<1_C>`, i.e. the pair `(G, <1_C>)` does NOT
  have relative property (T);
- (b) some unitary representation of `G` has almost invariant vectors and no nonzero
  `π(1_C)`-invariant vector.

If (b) holds, the `A`-spectral laws `μ_k` (probability measures on the compact dual `Â`) of
the almost invariant unit vectors satisfy:
- `μ_k{χ : χ(1_C) = 1} = 0`;
- `sup_B |μ_k(v^{-1}B) − μ_k(B)| → 0` for every `v ∈ V`;
- `μ_k → δ_0` weakly.

**Consequences.**
- **A new necessary prerequisite.** Since `<1_C>` is undistorted and infinite, Problem B(Z)
  (`G` Haagerup), and hence Haagerup of `2V` and of every `nV` (`n ≥ 2`, as `G ≤ 2V ≤ nV`),
  forces (a) and (b).
- **A new sufficient condition for the negative conjecture.** Relative (T) for
  `(G, <1_C>)` implies that `2V` is not Haagerup. This is weaker than relative (T) for
  `(G, A)` (artifact §3(f)).
- **Where it sits.** It is the Hilbert-space analogue of the established cubical ellipticity
  of `1_C`.
