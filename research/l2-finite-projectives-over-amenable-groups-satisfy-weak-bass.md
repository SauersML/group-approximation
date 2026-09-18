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
