---
rg: 2
id: subshift-crossed-product-rings-determine-flip-conjugacy
kind: claim
title: Open - does a ring isomorphism LC(X,F_2)⋊Z ≅ LC(Y,F_2)⋊Z force the infinite minimal subshifts X and Y to be flip conjugate?
distinct_from:
  subshift-el3-group-isomorphism-forces-flip-conjugacy: that asks it for the elementary groups G_X = EL_3(R_X); this is the ring question, equivalent to it by the two routes subshift-el3-flip-rigidity-from-ring-rigidity and subshift-ring-flip-rigidity-from-el3-flip-rigidity
  cartan-uniqueness-iff-orbit-cocycle-and-ring-rigidity: that proves (U) iff (D1) and (D2) at one X, with (D2) as one half of the equivalence; this is (D2) for every X as a standalone open question, with no Cartan hypothesis
  subshift-crossed-product-algebraic-cartans-are-conjugate: that asks Cartan uniqueness, which by cartan-uniqueness-iff-orbit-cocycle-and-ring-rigidity is this statement together with the orientation condition (D1); it implies this (route subshift-ring-flip-rigidity-from-cartan-uniqueness), and the converse would also need (D1)
  cantor-crossed-product-matrix-ring-iso-forces-soe: that proves the weaker conclusion, strong orbit equivalence, for arbitrary ring isomorphisms; this asks for flip conjugacy
  corner-matrix-ring-isos-force-flip-conjugacy: that proves flip conjugacy for ring isomorphisms built from diagonal-preserving corner maps; this asks it for every ring isomorphism
  subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity: that proves ring rigidity at X from Cartan uniqueness at X (its item 4); this is the ring rigidity statement itself, with no Cartan hypothesis
---

**OPEN.** Let `X ⊆ A^Z` and `Y ⊆ B^Z` be infinite minimal subshifts, `R_X = LC(X,F_2) ⋊_T Z` and `R_Y` likewise.
Flip conjugacy gives `R_X ≅ R_Y`. Question: does `R_X ≅ R_Y` as rings imply that `(X,T)` and `(Y,S)` are flip conjugate?

Remarks on the formulation.
- A ring isomorphism is automatically `F_2`-linear, because `F_2` is the prime field.
- An anti-isomorphism gives an isomorphism. The map `ι(Σ f_n u^n) = Σ u^(−n) f_n` is an involutive anti-automorphism of
  `R_Y`: `ι(f u^n · g u^m) = u^(−n−m) f α^n(g)` and `ι(g u^m) ι(f u^n) = u^(−m) g u^(−n) f = u^(−m−n) α^n(g) f`, with
  `α^n(g) = u^n g u^(−n)`, and these agree because `D_Y` is commutative. So `R_X ≅ R_Y^op` gives `R_X ≅ R_Y`.
- The question is equivalent to `subshift-el3-group-isomorphism-forces-flip-conjugacy`: routes
  `subshift-el3-flip-rigidity-from-ring-rigidity` (this one and standardness give the group statement) and
  `subshift-ring-flip-rigidity-from-el3-flip-rigidity` (the group statement gives this one). All remaining difficulty
  of the group question is ring-theoretic.

What is known.
- Strong orbit equivalence follows from `R_X ≅ R_Y` (`cantor-crossed-product-matrix-ring-iso-forces-soe`).
- A ring isomorphism mapping `D_X` onto `D_Y` gives flip conjugacy (`diagonal-preserving-isomorphisms-reconstruct-effective-groupoids`
  and `topological-full-groups-determine-flip-conjugacy`, assembled in `subshift-elementary-group-diagonal-iso-gives-flip-conjugacy`);
  so does one assembled from diagonal-preserving corner maps (`corner-matrix-ring-isos-force-flip-conjugacy`).
- Cartan uniqueness at `X` gives it at `X` (item 4 of `subshift-ring-cartan-uniqueness-iff-groupoid-model-rigidity`),
  so a yes to `subshift-crossed-product-algebraic-cartans-are-conjugate` gives a yes here
  (`subshift-ring-flip-rigidity-from-cartan-uniqueness`).

## Attempts

Details and the dead invariants are in `notes/subshift-el3-group-isomorphism-forces-fl-swarm-2026-09-16.md`.

- **Invariants of the ring: die at the unital ordered K_0.**
  - `HH_0(R_X) = K^0(X,T) ⊗ F_2` and `HH_1(R_X) = F_2`. The nonzero Z-degree parts vanish because the action is free.
    This uses the crossed-product decomposition of Hochschild homology (Feigin–Tsygan / Nistor), recalled from memory
    and not checked against a source.
  - The algebraic K-groups come from the twisted Bass–Heller–Swan sequence for `D_X[u, u^(−1); α]`, with
    `K_n(D_X) = C(X, K_n(F_2))`. This assumes the twisted Nil terms vanish for the regular coherent ring `D_X`, which was
    recalled from memory and not checked against a source. With Quillen's `K_*(F_2)` the sequence gives
    `K_(2i+1)(R_X) = K^0(X,T)/(2^(i+1) − 1)` for `i ≥ 1`, `K_1 = Z`, `K_2 = 0` and `K_(2i)(R_X) = Z/(2^i − 1)` for `i ≥ 2`.
    So they depend only on the group `K^0(X,T)`.
  - Growth is `≈ n·p_X(n)` (`subshift-ring-isomorphism-preserves-soe-class-and-growth`). It sees the complexity class,
    and nothing inside one strong orbit equivalence class of equal complexity growth.
- **Orbit modules: die at recognition.**
  - The orbit module `V_x = F_2^(Z)` is simple with `End = F_2` and linear growth.
  - The quotient `R_X / R_X(u − 1) ≅ D_X` is also simple with `End = F_2`. Its growth is of order `p_X(2n+1)`,
    linear for Sturmian `X`, and it has no joint `D_X`-eigenvector.
  - So "simple, `End = F_2`, linear growth" does not isolate the orbit modules. Even recognising them would give only a
    bijection of orbit sets, with no topology.
- **Automatic diagonal preservation for `*`-isomorphisms: dies over `F_2`.**
  - Over a kind subring of `C` (arXiv:2311.05694), `*`-isomorphisms of Steinberg algebras preserve the diagonal.
  - Two obstacles here. First, a ring or group isomorphism carries no involution data. Second, `F_2` is not kind:
    `J_4 − I` is a symmetric non-monomial involution in `M_4(F_2)`.
  - On a Rokhlin tower `U, TU, T^2U, T^3U` with matrix units `e_ij = u^i 1_U u^(−j)`, the element
    `w = Σ_{i≠j} e_ij + 1 − 1_W` satisfies `w* = w` and `w^2 = 1`. Then `Ad(w)` is a `*`-automorphism of `R_X` with
    `w 1_U w ∉ D_X`.
  - Exact check: `experiments/subshift-el3-group-isomorphism-forces-fl-2026-09-16/f2_not_kind_firewall.py`.
- **Semicrossed-product and `ℓ^1` rigidity: not applicable as stated.**
  - Hadwin–Hoover (1988), Davidson–Katsoulis (2008) and de Jeu–Svensson–Tomiyama (2012) were recalled from memory and
    not fetched in this attack, so treat them as unverified.
  - Those theorems recover the system from the positive part `⊕_{n≥0} D_X u^n` or from a norm. A ring isomorphism
    need not carry `⊕_{n≥0} D_X u^n` onto `⊕_{n≥0} D_Y u^{±n}`, and recognising that subring is at least as hard as
    this question.
- **Corners, towers, Kakutani moves: nothing new.** Isomorphisms assembled from diagonal-preserving corner and Morita
  pieces preserve the diagonal after composition (`corner-matrix-ring-isos-force-flip-conjugacy`). So a counterexample
  must be non-spatial on every clopen corner.
- **Counterexample by algebraic A𝕋 intertwining: blocked.**
  - The C*-proof that strong orbit equivalence gives `C(X)⋊Z ≅ C(Y)⋊Z` goes through A𝕋 building blocks
    `⊕ M_n(C(T))` and approximate intertwining. The exact algebraic analogue would write `R_X` as a directed union of
    subalgebras `⊕ M_(n_i)(F_2[t, t^(−1)])`.
  - Lemma, proved in the notes. First, `C_(R_X)(u) = F_2[u, u^(−1)]`, since the coefficients of a commuting element
    are `T`-invariant and hence constant. Second, some letter `a` has `T^n[a] ≠ [a]` for all `n ≠ 0`, or `X` is
    periodic. Third, `Σ c_n u^n` commutes with `1_[a]` only if `c_n = 0` for `n ≠ 0`.
  - Consequence: every subalgebra containing `u` and `1_[a]` has centre inside `F_2`. So `R_X` is not a directed union
    of subalgebras with infinite centre. By the ideal structure of `M_n(F_2[t, t^(−1)])`, it is not an inductive limit
    of finite sums of such blocks either.
  - A counterexample built by intertwining would need blocks with finite centre, and no such scheme is known.
- **Candidate pairs.**
  - Sturmian subshifts are dead as pairs among themselves: strong orbit equivalence among them is flip conjugacy.
  - Non-flip-conjugate proper orderings on one stationary Bratteli diagram share `K^0` and linear complexity. No
    invariant above separates their rings, and no construction of a non-spatial isomorphism is known.
- Bound: the arXiv API was searched on 2026-09-16 for ring isomorphisms of algebraic crossed products and Steinberg
  algebras without diagonal preservation. The search found no primary source that settles this question
  (swarm-subshift-el3-group-isomorphism, 2026-09-16).
