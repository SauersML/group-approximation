---
rg: 2
id: sl2-z-inverse-p-is-flexibly-hs-stable
kind: claim
title: SL2(Z[1/p]) is flexibly Hilbert--Schmidt stable for some prime p
distinct_from:
  iwahori-local-global-defect-question: that is Dogon--Vigdorovich Question 1.4, the local-to-global Iwahori modulus for SL_2(Z) *_(Γ_0(2)) SL_2(Z); by sl2-half-stability-excludes-hnn-hyperlinearity a positive answer is flexible stability of SL_2(Z[1/2]). This is the same stability statement for an arbitrary prime p, recorded as its own node because sl2-pq-flexibility-from-sl2-p-flexibility consumes it for every p != q.
  sl2-z-inverse-pq-is-flexibly-hs-stable: that is the two-prime lattice; by sl2-pq-flexibility-from-sl2-p-flexibility this one-prime statement implies it.
  hnn-over-sl2-z-not-sofic-if-sl2-z-inverse-p-p-stable: that is permutation stability of SL_2(Z[1/p]) and a non-sofic conclusion; this is flexible Hilbert--Schmidt stability.
---

**OPEN.** There is a prime `p` for which `SL_2(Z[1/p])` is flexibly
HS-stable in the sense of Dogon--Vigdorovich, Definition 1.2 of
arXiv:2506.20843. The notion is the one used in
`sl2-z-inverse-pq-is-flexibly-hs-stable`.
- Take any sequence of unitary tuples on a fixed finite generating set whose
  relator defect tends to `0`.
- Then there are exact representations of dimensions `D_n >= d_n`, with
  `D_n/d_n → 1`.
- Their compressions to `d_n`-dimensional subspaces are `o(1)`-close to the
  tuples in normalized Hilbert--Schmidt norm.

**Consequences.**
- For `p = 2` this is the positive answer to Dogon--Vigdorovich Question 1.4
  (`iwahori-local-global-defect-question`, `sl2-half-stability-excludes-hnn-hyperlinearity`).
- For every `p`, the `(tau)` form of `hnn-over-codense-kazhdan-subgroup-not-hyperlinear`,
  with `sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`, makes
  `<SL_2(Z[1/p]), t | [t, SL_2(Z)] = 1>` non-hyperlinear.
- By `sl2-pq-flexibility-from-sl2-p-flexibility`, it gives
  `sl2-z-inverse-pq-is-flexibly-hs-stable` for this `p` and every prime `q != p`.

**What would refute it.** For each `p` separately, a sequence of asymptotic
representations of `SL_2(Z[1/p])` far from all congruence representations.
By `sl2-pq-exact-vertex-pairs-have-uniform-linear-repair`, such a sequence is
also the only way to refute `sl2-z-inverse-pq-is-flexibly-hs-stable` through
its q-adic amalgam decomposition. A pair of exact vertex representations can
never witness a refutation.

## Attempts

* **Refutation through the homogeneous crossed product (swarm-0917-w14-w14-nh-follow, 2026-09-19, reframing).**
  The outcome is OPEN. Nothing new is decided. The attempt records where the refutation side stands.
  * **Gate.** `f2xf2-crossed-products-ce-make-sl2-centralizer-hnn-hyperlinear` (item 3) covers this node at
    every `p`. If this node holds, the explicit action `(FX2)` of `F_2 x F_2` has a crossed product that is
    not Connes-embeddable. Contrapositive: CE of all essentially free `F_2 x F_2` crossed products refutes
    this node for every `p`.
  * **Direct chain, checked here.** Take any homomorphism `rho : A -> prod_omega M_(d_n)`.
    1. Stability gives exact `pi_n` of dimension `D_n`, with `D_n/d_n -> 1`, and isometries `V_n` such
       that `pi_n(g) V_n ≈ V_n rho_n(g)`.
    2. The `pi_n` are congruence representations of level prime to `p`. So Selberg `(tau)` for `C`, as in
       item 3 of `sl2-z-inverse-p-over-sl2-z-is-codense-tau-pair`, moves a `C`-almost-commuting `X_n`
       to `pi_n(A)'` with linear loss. This gives `rho(C)' cap M_omega = rho(A)' cap M_omega`.
    3. `homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse` (HQ2)-(HQ4) then shows that
       `M_2^(p) = L^infinity(L/Lambda') rtimes A` is not CE for any cocompact `Lambda'`.
    So this node implies the negation of `sl2-homogeneous-quotient-crossed-product-is-connes-embeddable`
    (at `p = 2`). It therefore also implies the negation of
    `dyadic-homogeneous-quotient-admits-topological-microstates`, because the action is uniquely ergodic.
  * **Collapse extends to smaller subgroups.** The same argument works with `C` replaced by any
    finite-index `Gamma <= C` that surjects onto every `SL_2(Z/m)` with `p` not dividing `m`. Examples are
    `Gamma_0(p)` and `Gamma(p^k)`. The collapse then reaches down to `Gamma(p^k)'` for every `k`. The
    matching leak is the indicator of a `K(p^k)`-orbit on `L/Lambda'`, which is smaller, so this gives no
    new kill. The `(tau)` constant depends on `k`.
  * **Checked and dead as refutations.** Both routes are already recorded in the graph as dead.
    * DKP amalgam soficity needs an amenable edge relation, and `R_(Gamma_0)` is not amenable.
    * Treeability fails because `beta_2^(2)(A) > 0`.

    The congruence models are excluded (`expanding-matchings-need-a-shared-stabilizer`).
  * **What is left.** Either side reduces to Connes embeddability of the one explicit algebra `M_2^(p)`,
    equivalently of `(FX2)`. The graph has no route to either sign of that question.
