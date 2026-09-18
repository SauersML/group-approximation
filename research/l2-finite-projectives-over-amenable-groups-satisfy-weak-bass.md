---
rg: 2
id: l2-finite-projectives-over-amenable-groups-satisfy-weak-bass
kind: claim
title: Over a torsion-free amenable group, a countably generated projective integral module of finite L2-dimension has rational rank at most its L2-dimension
distinct_from:
  amenable-cd-two-bass-defect-equals-euler-characteristic: that proves the rank-gap target follows from this inequality for one module, the relation module of a cd-2 group, and that flatness and finite truncations cannot give it; this is the inequality for all countably generated projectives
  l2-small-projectives-with-rank-gap-are-finitely-generated: that shows an L2-small projective is finitely generated when a rank gap holds; this asks for a Bass-type inequality on the core with no finitely generated summand, with no rank-gap hypothesis
---

**OPEN.** Let `G` be a torsion-free amenable group, `U = U(G)`, and let `C` be a countably
generated projective `Z[G]`-module with `dim_U(U ⊗_{Z[G]} C) < ∞`. Then

> `rank_Q(Q ⊗_{Z[G]} C) <= dim_U(U ⊗_{Z[G]} C)`,

where `Q` is the trivial module. In other words, the Bass defect `D(C)` of
`amenable-cd-two-bass-defect-equals-euler-characteristic` is `<= 0`.

**Why it matters.** By item 3 of `amenable-cd-two-bass-defect-equals-euler-characteristic`, this
statement implies `amenable-cd-two-groups-have-an-l2-rank-gap`, and so Kropholler's question in
dimension 2. It is enough to have it when `G` is finitely generated with `cd G = 2` and finite
abelianization, and `C` is the part `P'` of the relation module that has no nonzero finitely
generated direct summand. For a counterexample `K`, that `P'` has `D(P') = 1 + b_2(K) >= 1`.
This is the direction proved. The converse is not known.

**What is known.**

- *Finitely generated `C`:* equality holds. This is the weak Bass conjecture for amenable groups
  (Berrick–Chatterji–Mislin; recalled): the Hattori–Stallings rank of `C` is concentrated at `1`.
- *Direct sums* of modules for which it holds: both sides are additive in `[0, ∞]`.
- *Induction from a subgroup:* for `H <= G` and `C` over `Z[H]`,
  `Q ⊗_{Z[G]} (Z[G] ⊗_{Z[H]} C) = Q ⊗_{Z[H]} C`, and the `U(G)`-dimension of the induced module
  equals the `U(H)`-dimension of `U(H) ⊗ C`. So the class of `(G, C)` satisfying the inequality is
  closed under induction.
- *Virtually finitely generated abelian `G`:* take a normal free-abelian `A` of finite index.
  `Z[A]` is commutative noetherian with connected spectrum, so by Bass ("big projective modules are
  free"; recalled) the restriction of `C` to `A` is either free of infinite rank, which gives
  `dim = ∞`, or finitely generated. So `C` is finitely generated over `Z[G]`, and the first case
  applies. This is Step 5 of `amenable-cd-two-bass-defect-equals-euler-char-proof`.

**Calibrations (hypotheses that cannot be dropped).**

- *Torsion-freeness.* With coefficients `Q[G]` and `G` finite, `C = Q[G]e` for
  `e = |G|^{-1} Σ g` has rank 1 and `U`-dimension `1/|G|`.
- *Projectivity, not flatness.* Over the Hantzsche–Wendt group, the flat colimit module `M_B` of
  item 5 of `amenable-cd-two-bass-defect-equals-euler-characteristic` has rank `n`, `U`-dimension
  `n − 1` and defect 1. So the analogous inequality for countably generated flat modules is
  false. Any proof has to use a splitting `C ⊕ C'' = Z[G]^(∞)` and not just a colimit
  presentation.
- *Finite `L²`-dimension.* Without it, `C = Z[G]^(∞)` gives `∞ <= ∞`, which says nothing. A
  hypothesis weaker than finite dimension, such as "no finitely generated summand", would not
  give a numerical statement.

**Where a proof would have to go.** Write `C` as the image of an idempotent
`E ∈ M_∞(Z[G])` (each row finitely supported), acting by right multiplication. Then
`rank_Q(Q ⊗ C) = rank_Q ε(E)`. For a finite matrix `E`, `dim_U = tr_{NG}(E) = Σ_i E_{ii}(1)`, and
the Bass conjecture gives `rank ε(E) = Σ_i Σ_g E_{ii}(g) = tr_{NG}(E)`. For an infinite `E`,
neither identity is available. The sums need not converge absolutely, and `ε(E)` is an
idempotent of infinite size whose rank is not controlled by its diagonal.
The obstruction items 4–6 of `amenable-cd-two-bass-defect-equals-euler-characteristic` show that
finite corners of `E` and the `U`-dimensions alone cannot carry the argument. A proof has to use
the relation `E² = E` over `Z[G]` globally, for example through a trace on a suitable ideal of
column-finite matrices that restricts to the Hattori–Stallings trace on finite corners.

## Attempts

- **2026-09-18 (lane `w13-112`): specialization from the universal field. Proved for locally
  indicable and virtually locally indicable groups. Flat arguments work for exactly the locally
  indicable groups.** See `flat-weak-bass-holds-exactly-for-locally-indicable-groups`
  (proposed ESTABLISHED).
  - *Characterization.* For every group `G`, the following are equivalent:
    - `G` is locally indicable;
    - `rank_Q ε(A) <= rk_U(A)` for every matrix `A` over `Z[G]`;
    - `rank_Q(Q ⊗ M) <= dim_U(U ⊗ M)` for every flat module `M`.

    The proof of the forward direction: by Jaikin-Zapirain (2021), `D(G)` is the universal
    division ring of fractions, and Cohn specialization to the augmentation gives the rank
    inequality. Lazard's theorem then carries it to flat modules. The converse: Fox matrices of
    a finitely generated subgroup with `b_1 = 0` give a flat module `M_B` of positive defect.
  - *New cases of this node.* The statement holds for every locally indicable group, amenable or
    not, and for all flat modules. It is subgroup-closed. By Swan's theorem it passes up finite
    index, with `rank_Q(Q ⊗_G C) = rank_Q(Q ⊗_N C)/[G:N]`. So it holds for every virtually
    locally indicable group, and a proof for `K` may pass to any finite-index subgroup first.
  - *Obstruction.* Item 5 of `amenable-cd-two-bass-defect-equals-euler-characteristic` was a
    Hantzsche–Wendt example. It now holds for every group that is not locally indicable. In
    particular the counterexample `K` itself carries a countably generated flat module of defect
    `>= 1`. `K` is not virtually locally indicable, since otherwise it would be elementary
    amenable. So every case of this node that matters for the flagship lies outside the reach
    of flat arguments.
  - *Where the difference is visible.* Hantzsche–Wendt separates the flat statement from the
    projective one. There the statement holds only because of Swan's theorem: the
    `Q[G/N]`-module `Q[G/N] ⊗ C` is free, so its trivial isotypic part is exactly its `1/[G:N]`
    share. `M_B` violates this.
  - *Next step.* Find a replacement for Swan's theorem when `K` has no finite-index locally
    indicable subgroup. Concretely, for `N ⊴ K` with `K/N` infinite and amenable, does
    `Z[K/N] ⊗_{Z[K]} C` satisfy an isotypic-share identity in the sense of `U(K/N)`? This is an
    "L²-Swan" statement for big projectives over the quotient.
