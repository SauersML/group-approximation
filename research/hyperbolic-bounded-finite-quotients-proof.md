---
rg: 2
id: hyperbolic-bounded-finite-quotients-proof
kind: route
title: A maximal finite image gives a minimal finite-index normal subgroup with no finite quotients
target: hyperbolic-bounded-finite-quotients-iff-quotientless-hyperbolic
requires: []
---

Let `Q` be finitely generated. Write `FI(Q)` for its finite-index normal
subgroups.

**Core lemma.** If `K <= Q` has finite index, its normal core
`core_Q(K) = ∩_{q in Q} q K q^{-1}` is the kernel of the action of `Q` on the
finite set `Q/K`, so it lies in `FI(Q)` and is contained in `K`.

**(1) ⇒ (3).** Suppose every `N in FI(Q)` has `|Q/N| <= B`. Choose `N_0 in FI(Q)`
with `|Q/N_0|` maximal.

- *Minimality.* For `N in FI(Q)`, `N_0 ∩ N in FI(Q)` and `Q/(N_0 ∩ N)` maps onto
  `Q/N_0`. Maximality forces `|Q/(N_0 ∩ N)| = |Q/N_0|`, so that surjection is a
  bijection, `N_0 ∩ N = N_0`, and `N_0 <= N`. By the core lemma every
  finite-index subgroup `K` contains `core_Q(K)`, hence contains `N_0`. So `N_0`
  is the intersection of all finite-index subgroups of `Q`.
- *No finite quotients.* Let `K <= N_0` have finite index in `N_0`. Then `K` has
  finite index in `Q`, so `N_0 <= core_Q(K) <= K`, and `K = N_0`. A nontrivial
  finite quotient of `N_0` would have a proper finite-index kernel, which is
  impossible.

Put `Δ = N_0`.

**(3) ⇒ (1).** Let `φ: Q ->> F` with `F` finite. Then `φ(Δ)` is a finite
quotient of `Δ`, hence trivial, so `φ` factors through `Q/Δ` and
`|F| <= |Q/Δ|`.

**(3) ⇒ (2).** For `N in FI(Q)`, `Δ/(Δ ∩ N) ≅ ΔN/N` is a finite quotient of `Δ`,
so `Δ <= N`. Thus `Q/Δ` is itself one of the finite quotients in the inverse
system defining `Q^`, and every other term is a quotient of it compatibly. So
`Q^ = Q/Δ`, which is finite.

**(2) ⇒ (1).** Every homomorphism `Q ->> F` onto a finite group extends
continuously to `Q^ ->> F`, so `|F| <= |Q^|`.

**The minimal subgroup and the maximal order.** In (1) ⇒ (3), `Δ` was shown to be
the intersection of all finite-index subgroups, and `|Q/Δ| = |Q/N_0|` is the
largest order of a finite quotient.

**Hyperbolic case.** Let `Q` be infinite and word-hyperbolic.
- `Δ` has finite index, so it is infinite.
- `Δ` acts properly and cocompactly by isometries on a Cayley graph of `Q` (the
  restriction of the action of `Q`). By the Švarc–Milnor lemma, `Δ` is finitely
  generated and quasi-isometric to `Q`.
- Hyperbolicity of geodesic metric spaces is a quasi-isometry invariant, so `Δ`
  is word-hyperbolic.

Both facts are standard (Švarc–Milnor lemma; quasi-isometry invariance of
hyperbolicity) and were not re-read at source here.

**Consequence.**
- (⇐) An infinite hyperbolic group without nontrivial finite quotients has
  finite quotients of bounded order, namely order `1`.
- (⇒) If an infinite hyperbolic `Q` has finite quotients of bounded order, then
  `Δ` from (3) is an infinite hyperbolic group without nontrivial finite
  quotients.

**Remark on infinite chains.** Suppose `Γ ->> G_1 ->> G_2 ->> …` are proper
quotients with increasing kernels `M_1 < M_2 < …`, each killing more finite
images. If the limit `Γ/∪M_i` were hyperbolic, it would be finitely presented,
so `∪M_i` would be finitely normally generated and contained in some `M_i`,
contradicting properness. So such a chain never has a hyperbolic limit, and a
hyperbolic witness needs one finitely normally generated `M`. `QED`
