---
rg: 2
id: perfect-completeness-rich-2to1-tractable-skeletons-are-in-p
kind: claim
title: A reduction to Gap-2-to-1[1, delta] whose YES outputs carry a computable forcing-closure, certified merge or affine skeleton of mass above delta puts its source language in P, so right merges, affine-local wrappers and F_lin-stage starts cannot prove the perfect-completeness Rich 2-to-1 Conjecture
invalidates:
  - rich-2to1-perfect-completeness-via-tractable-skeletons
distinct_from:
  left-preserving-local-richness-wrappers-are-affine-ug-merges: that transfers imperfect-completeness hardness of a wrapper to the unique game U_W(G); this uses perfect completeness to make U_W(G) satisfiable and hence solvable, and adds two further skeleton types, forcing closures and affine encodings, that the wrapper theorem does not see.
  sd-rich-and-unique-games-sos-gaps-interconvert: that shows the right merge Psi(U) transfers values and SoS gaps at completeness 1 - eta; this shows the same merge is polynomial-time solvable at completeness 1, because one seed forces a whole component.
  low-label-threshold-rank-reductions-cannot-prove-ugc: that kills reductions through a spectral invariant of the output at any completeness; this kills through the combinatorial solvability of a skeleton and applies only at perfect completeness.
  unique-games-hard-at-completeness-one-half: that is a hardness theorem at completeness 1/2; this is an algorithmic obstruction at completeness 1 and is silent at every completeness below 1.
artifacts:
  - experiments/rich-2to1-perfect-completeness-2026-09-17/forcing_closure_check.py
---

**ESTABLISHED.** Fix `k >= 2`. A 2-to-1 game has left alphabet `[2k]` and right
alphabet `[k]`. Each edge `(u,v)` has weight `w_(uv) > 0` and a 2-to-1 map
`pi_(uv)`. Total weight is 1, and `mass` means total weight.

Let `R` be a polynomial-time reduction from a language `Lang` to games. It is
*perfect with soundness delta* if `x in Lang` gives `val(R(x)) = 1` and
`x notin Lang` gives `val(R(x)) <= delta`. Richness plays no role in the
algorithms, so every statement holds for rich outputs in particular.

**Lemma 0 (skeleton lemma).** Suppose a polynomial-time algorithm `A` sees `x`
and the full run of `R` on `x`, and outputs a labeling of `R(x)`. Suppose that
labeling has value `> delta` whenever `x in Lang`. Then `Lang in P`.

**Forcing closure.** Start from a partial labeling. Repeat two rules:

* a labelled left `u` labels every right neighbour `v` by `pi_(uv)(L_u)`;
* an unlabelled left `w` gets candidates
  `C_w = intersection over labelled neighbours v of pi_(wv)^(-1)(M_v)`. If
  `|C_w| = 1`, label `w`; if `C_w` is empty, report a conflict.

At the end, report a conflict if some edge with both ends labelled is violated.
`cl_L(S)` is the closure seeded by `L|S`.

For a satisfiable `G`, define `kappa_t(G)` as the sum, over connected components
`C`, of the maximum over satisfying `L` and seed sets `S` in `C` with `|S| <= t`
of the mass of the edges at labelled left vertices of `cl_L(S)`.

**Separation digraph `D(G)`.** Put an arc `u -> w` when the maps `pi_(wv)`, for
`v` in `N(u) ∩ N(w)`, jointly separate `[2k]`. That means the intersection of
their fibres is a partition into singletons. Two pairings with no common pair
already separate. `D(G)` does not depend on labels and is computable.

**Theorem.** Let `R` be perfect with soundness `delta`.

1. **(M1) Forcing closures.** If `kappa_t(R(x)) > delta` for every `x in Lang`
   and some constant `t`, then `Lang in P`. A label-free sufficient condition:
   choose at most `t` left vertices in each component. The left vertices they
   reach in `D(R(x))`, summed over all components, carry incident edge mass
   `> delta`.
2. **(M2) Right merges.** Let `U` be a unique game with alphabet `[2k]`. For each
   right `v` fix a family `Sigma_v` of 2-to-1 maps that separates `[2k]`. Two
   pairings with no common pair suffice; BKM's `Psi(U)` takes all of them. Let
   `Psi_Sigma(U)` have right vertices `(v, sigma)` for `sigma in Sigma_v`, with
   constraints `sigma o phi_(uv)`. Then:
   * `Psi_Sigma(U)` is satisfiable iff `U` is;
   * `D` contains every arc `u -> w` with a shared `U`-neighbour, so
     `kappa_1(Psi_Sigma(U)) = 1` when `U` is satisfiable.

   Any `R = Psi_Sigma o R'` that is perfect with soundness `delta < 1` puts
   `Lang` in P.
3. **(M3) Certified affine-local wrappers.** Let `W` be a wrapper of
   `left-preserving-local-richness-wrappers-are-affine-ug-merges` satisfying
   (LC) and (R2). Suppose its completeness proof exhibits certified labelings,
   so `beta = 0`, and `delta < 1 - alpha_k` with
   `alpha_k = (4k-5)/((2k-1)(2k-3))`. Then `R = W o R'` puts `Lang` in P.
4. **(M4) Affine encodings.** Suppose the run of `R` supplies bijections
   `e_u : Sigma_u -> F_q^(d_u)` and `e_v : [k] -> F_q^(d_v)` on a set of edges
   of mass `> delta`, and in these coordinates every constraint on those edges is
   an affine map. Then `Lang in P`. With `q = 2` the 2-to-1 affine constraints
   are exactly the translation pairings `x ~ x + b`. So any `F_lin`-rich stage
   whose output carries such an encoding dies at perfect completeness. That
   includes a perfect-completeness start `F_0 = F_lin` of the BKM enrichment
   chain.

The proofs are in `perfect-completeness-tractable-skeletons-proof`.

**Where the class dies.**

* **Invariant.** The *tractable skeleton mass*: the edge mass of a sub-instance
  that can be computed from the run of `R` and lies in a class whose search
  problem is polynomial. The classes are constant-seed forcing closures, unique
  games and affine systems.
* **Step.** Completeness. A satisfiable game has satisfiable sub-instances, and
  searching the skeleton finds a labeling of value `>= mass > delta`. Soundness
  forbids that on NO instances.
* **Consequences.**
  * BKM Theorem 8's UGC-to-Rich direction is a right merge.
  * The w4 wrapper class is a merge.
  * The proved 2-to-1 instances are `F_lin` in affine form.

  So none of them, run with perfect completeness from any NP-hard source, can
  prove `rich-2to1-perfect-completeness-conjecture` unless P = NP.
* **Boundary.** At completeness `1 - eps` every member stops working:
  * propagation breaks at the first violated constraint;
  * near-satisfiable unique games are UGC-hard;
  * near-satisfiable affine systems are Håstad-hard;
  * M3 turns back into the wrapper transfer theorem.

  So nothing here bears on `rich-2to1-games-conjecture` directly. It explains
  mechanically why Conjecture 7 is out of reach of the constructions that give
  Conjecture 6 its equivalences.

**Computation.** The artifact brute-forces the claims on small cases:

* closure soundness on 3705 (satisfying labeling, seed set) pairs;
* `sat(Psi(U)) = sat(U)` and one-seed closure equal to the component, on 80
  random unique games with `2k = 4, 6`;
* on the Grassmann skeleton over `F_2^n` (left: 2-subspaces, right: nonzero
  vectors), the closure of `t` seeds is exactly the set of 2-subspaces of their
  span. Its maximum mass at `n = 6` is `0.0015` for `t = 1` and `0.054` for
  `t = 2`, yet Gaussian elimination returns a satisfying labeling of the offset
  skeleton.

So M1 and M4 are incomparable, and both are needed.

**Survivors.** These are not covered.

* **(P1)** Re-encoding reductions: long-code or dictatorship-test compositions,
  including BKM's noise test and the BKLM multi-slice setting. Their YES
  labelings have `o(1)` constant-seed closure, no computable unique-game skeleton
  and no affine encoding.
* **(P2)** Uncertified or non-affine wrappers, survivors G2 and G3 of the wrapper
  theorem, where `U_W(G)` need not be satisfiable.
* **(P3)** Skeletons of mass at most `delta`.
* **(P4)** Skeletons in other tractable constraint languages. Bounded-width and
  few-subpowers languages presumably die the same way through the CSP dichotomy
  theorem, but that is not claimed here.
