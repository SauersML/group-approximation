---
rg: 2
id: bernoulli-cylinder-comparison-fails-for-some-group
kind: claim
title: Some countable group has a non-surjective Bernoulli cylinder comparison, which would refute trivial-coefficient Baum--Connes for F_p wr_Z G
distinct_from:
  monster-bc-failure-at-measured-coefficient-is-the-module-crux: that is question (Q) for measured dual-module coefficients and module triples; this is its Bernoulli case with the host removed, one explicit map on reduced K-theory.
  some-nonexact-group-has-a-k-inexact-module-triple: that asks for a K-theory exactness defect of a module triple; this asks for a non-surjective comparison at a single coefficient, with no triple.
---

**OPEN.** There are a countable group `G`, a prime `p` and a `G`-set `Z` with finite point stabilizers such that the
cylinder comparison

```text
T_r : ⊕_([s] ∈ G\S) R(G_s)  ->  K_*( C_0((Z/p)^Z \ {0}) ⋊_r G )
```

of `bernoulli-bc-splits-into-host-and-cylinder-comparison` is not surjective. On `[τ] ∈ R(G_s)`, `T_r` gives
`[1_(C_s) p_τ]`.

**What it would give.** Route `bc-counterexample-via-bernoulli-cylinder-defect`: reduced assembly for `F_p wr_Z G`
would not be surjective. That is a counterexample with trivial coefficients, with no dichotomy on the host and no module
triple.

**Equivalent forms.**
- `T_r` is always injective (`bernoulli-assembly-injective-beyond-the-host`). So the claim says `T_r` is not an
  isomorphism.
- Let `C_ρ` be the mapping cone of the cylinder *-homomorphism
  `ρ : c_0(S) -> K(l^2 S) ⊗ C_0((Z/p)^Z \ {0})`.
  - The mapping-cone extension is completely positively split, so its reduced crossed products are exact. Hence
    `K_*(C_ρ ⋊_r G) = 0` iff `T_r` is an isomorphism.
  - `ρ` is a weak K-equivalence (Claim W of `research/artifacts/bc-bernoulli-rank-functionals-torsion-2026-09-13.md`),
    so `K_*(C_ρ ⋊ H) = 0` for finite `H`, and going-down gives `K^top_*(G; C_ρ) = 0`.
  - So the claim says that `G` fails Baum--Connes at the weakly contractible coefficient `C_ρ`.
- For torsion-free `G` and `Z = G`, some class of shape (b) or (c) of `bernoulli-assembly-injective-beyond-the-host`
  exists. Shape (a) never occurs (`bernoulli-pattern-expansions-are-finite`).

**Model test.** `G = Z` (amenable) fails the claim, because `T_r` is an isomorphism by Pimsner--Voiculescu. So does
every group satisfying Baum--Connes with coefficients. No group satisfying it is known.

## Attempts

The [further general-closure attempt](artifacts/Cairn_Baum_Connes_General_Attempt.md#21-reduced-descent-is-not-formal)
leaves this input OPEN. Weak equivalence on compact-subgroup tests computes
the topological domain, not reduced descent. Locality and product-trace
invisibility leave the virtual degree-zero complement and odd K-theory
unresolved. Even their vanishing for every torsion-free host would leave
the host assembly summand, not prove general Baum–Connes.

- **Hosts with coefficients.** If `G` satisfies Baum--Connes with coefficients, `T_r` is an isomorphism (CEKN
  arXiv:2210.09209, Theorem 2.8, second sentence). So a witness fails Baum--Connes with coefficients. Among known groups
  that means a large-girth expander monster (`osajda-monster-hosts-for-bc-module-route`), whose known failure is
  injective-not-surjective (Willett--Yu I, Corollary 1.7) at a coefficient that is not a module dual.
- **Rank functionals.** Ranks at finite-support configurations prove injectivity and would see shape (a). They vanish on
  the rank-invisible tail classes of shape (b) and do not see `K_1`, shape (c). Shape (a) turned out to be empty; see
  the locality bullet below.
- **Gapped induced-subgraph operators.** A shape-(a) candidate is a projection whose rank at a configuration counts a
  non-local invariant of its support, such as the kernel dimension of the Laplacian of the induced subgraph (its number
  of components). Such kernel projections are not in the algebra. The full shift contains every induced subgraph,
  including long paths, whose small nonzero eigenvalues close the gap. A monster's embedded expanders give a uniform gap
  only on the subshift of expander markings, and that subshift is not a module dual.
- **Where it stopped (before 2026-09-13 locality).** A witness seemed to need a spectral gap uniform over all Bernoulli
  configurations, or a K-theory class not produced by functional calculus from local operators. The locality theorem
  below rules out the first option on every host.
- **Subgroup tubes (2026-09-13, `bernoulli-defects-vanish-along-bcc-subgroup-tubes`, established).**
  - Regular representations at configurations supported in a tube `HF` live on a finite union of right `H`-cosets. This
    gives a restriction *-homomorphism to the Bernoulli datum `(H, HF)`.
  - When `H` satisfies Baum--Connes with coefficients, shapes (b) and (c) restrict to zero along `HF`. A shape-(a) class
    has only finitely many `H`-orbits of patterns with nonzero coefficients inside `HF`.
  - So thin ghosts along cyclic, free, hyperbolic or amenable subgroups are excluded. A witness must spread over pattern
    shapes that escape every good tube, as a monster's embedded expanders do.
  - Where it stops: the tubes of good subgroups do not cover the expander-shaped patterns, so the restriction decides
    nothing there.
- **Locality of ranks (2026-09-13, `bernoulli-pattern-expansions-are-finite`, established, unreviewed).**
  - For every projection over `C_0(Λ^G \ {0}) ⋊_r G`, the mixed second difference of its ranks at two far sites is an
    integer trace through gapped resolvents. It is bounded by `C e^(-α d)`, with no growth factor (Combes--Thomas), so
    it is `0`.
  - Hence every class has a finite pattern expansion, and shape (a) never occurs, over any torsion-free host (monsters
    included).
  - Any local operator gapped uniformly over the full shift has local ranks. Embedded expanders, isometric or weak,
    cannot produce a witness through ranks.
  - Where it stops: a witness is invisible to every finite-support orbit representation. It is either a rank-zero class
    in `∩_k im K_0(I_k ⋊_r G)` (shape (b)) or an odd class (shape (c)).
  - Every independent product trace now annihilates the rank-invisible virtual remainder
    (`bernoulli-product-traces-kill-rank-invisible-k0`, 2026-09-20). Haar trace cannot
    detect that remainder. The exact host-and-tail cokernels are
    `bernoulli-assembly-defects-split-into-host-and-tail`.
  - The marking-subshift HLS lift under hypothesis (M) is ruled out by the newer
    `hls-ghost-class-never-lifts-to-the-bernoulli-full-shift`; it is not an open lift question.
- **Historical HLS ghost-lift proposal (2026-09-13, `hls-ghost-lift-needs-forest-shift-failure`, established, unreviewed).**
  - HLS Section 7's projection is a Bernoulli coefficient on the marking subshift of isometrically embedded expanders.
    It has rank `1` at each marked expander and vanishes on the tree boundary (`hls-ghost-projection-breaks-k-exactness`).
  - Assume max-to-reduced K_0 injectivity at the tree boundary (`expander-tree-boundary-k0-max-reduced-injective`). A
    full-shift class with vanishing tree-boundary part and nonzero ranks at infinitely many marked expanders is then a
    witness here (route `bc-bernoulli-defect-via-hls-ghost-lift`, via `hls-ghost-class-lifts-to-the-bernoulli-full-shift`).
  - It also forces Baum--Connes surjectivity to fail at the forest coefficient
    (`forest-shift-bernoulli-comparison-is-surjective`).
  - **Resolved against this lift, 2026-09-16–17:** CND-support coefficient assembly and rank locality
    imply eventually zero marked-expander ranks for every full-shift class vanishing on the boundary.
    The HLS class has rank one at every expander and zero boundary restriction, so cannot lift.
    This keeps the stated isometric large-girth hypothesis (M) and the Tu/going-down imports.
  - The remaining degree-zero virtual classes have zero finite ranks, zero CND-support restriction
    (for finitely generated torsion-free hosts), and zero independent product traces.
    Odd classes also have zero CND restriction. No general vanishing theorem for either group
    is supplied, and no unproved reduced-exactness inference from zero restriction is made.
