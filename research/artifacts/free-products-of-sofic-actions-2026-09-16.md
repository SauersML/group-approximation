# Free products of sofic actions: GKP Question 4.3 (artifact, 2026-09-16)

Author: swarm agent `hi-spec-non-hyperlinear-group`.

This artifact supports these nodes:
- `free-products-of-sofic-actions-are-sofic`, with the direct proof
  `free-products-of-sofic-actions-are-sofic-proof`;
- `all-actions-sofic-groups-closed-under-free-products`;
- `doubles-of-free-products-of-amenable-groups-are-sofic`.

The complete proof of the main theorem is in the route body. This file
records:
- the source statements;
- the proof architecture and the failed naive versions;
- a finite numerical sanity check;
- remarks and consequences that are not recorded as nodes;
- a sketch for amalgams over finite groups, which is not claimed;
- the literature boundary.

## 1. Source statements

From the graph-verified transcription `research/artifacts/gkp-2401-04945-verified.md`
of Gao--Kunnawalkam Elayavalli--Patchell, arXiv:2401.04945v3 = Res. Math. Sci.
12 (2025) 48, Section 4:

> **Question 4.3.** Suppose we have actions `α_i : G_i ↷ X` where `i` ranges
> over a countable index set. Then the actions naturally give rise to an
> action `α : ∗_i G_i ↷ X`. `α` is sofic iff all `α_i` are sofic?
>
> The forward directions of both conjectures follow from item 3 of
> Proposition 2.15. By item 4 of Proposition 2.15, it suffices to consider the
> case where there are only two groups `G_1` and `G_2`.

The same paragraph of GKP says: "It is still open whether all actions by
sofic groups are sofic. However, this does hold for amenable groups and free
groups." Kun--Thom (arXiv:2608.06222) later settled the first sentence
negatively. The graph records this as `coordinate-action-not-sofic`.
Question 4.2 was answered negatively in `commuting-sofic-actions-need-not-combine`.
Before this artifact, the graph described Question 4.3 as "untouched"
(`nonsofic-orbit-forces-commuting-counterexample`).

## 2. Results

- **Theorem A** (`free-products-of-sofic-actions-are-sofic`). If every factor
  restriction of `α : *_i G_i ↷ X` is sofic, then `α` is sofic. With
  Proposition 2.15(3), this answers Question 4.3 positively.
- **Theorem B** (`all-actions-sofic-groups-closed-under-free-products`). Let
  `𝒜` be the class of countable groups all of whose set actions are sofic.
  - Every member of `𝒜` is sofic.
  - `𝒜` is closed under subgroups, countable increasing unions and countable
    free products.
  - `𝒜` contains the amenable groups.
  - `𝒜` is not closed under quotients.
  - `Γ_p * Z ∈ 𝒜` is finitely presented, nonamenable, has torsion and is not
    residually finite.
- **Corollary C** (`doubles-of-free-products-of-amenable-groups-are-sofic`).
  For `H ∈ 𝒜` and any `Γ ≤ H`:
  - `H *_Γ H` is sofic;
  - `L(Γ) ⊂ L(H)` is `RE/C`.

What is new is Theorem A, the free-product and `Γ_p * Z` parts of Theorem B,
and Corollary C beyond free `H`. The rest is formal from GKP's toolkit.

## 3. Proof architecture

**The obvious attempt.** Take factor models `(A_j, φ_j)`, identify all `A_j`
with one set by arbitrary bijections, and define `φ` along reduced words.

- Multiplicativity survives. It only needs each factor model to be
  multiplicative, because conjugation preserves Hamming distance.
- The orbit approximation fails. A point `a` carries a label
  `π_a : E → B` coming from factor 1. After a syllable of factor 2 moves it,
  the new point's factor-1 label has no relation to the factor-2 equivariance.
  The ablation in Section 4 shows about 27 % violations.

**Fix 1: a common label alphabet.** Both factors must label the same finite
packet `E'` in the same alphabet, and the bijection between the models must
preserve labels on most points. The labels need not be canonical. They only
need to agree across the identification.

**Fix 2: equidistribution by randomization.** Two arbitrary models realize
different label patterns with different frequencies, so no label-preserving
bijection exists in general. Put `λ = τ ∘ Λ_p`, where `τ` ranges over *all*
maps `B_j → B'`.
- Each label `c ∈ L = B'^(E')` then occurs exactly `|S'_j|/|L|` times among
  good points (R3).
- `τ` is constant along `φ'_j`-orbits, so it does not spoil equivariance (R2).
- Label injectivity is lost on a fraction at most `binom(|E'|,2)/|B'|` (R4).

This is the only place where the finite alphabet size matters.

**Fix 3: a packet closed under suffixes.** `E'` contains every
`(g_1⋯g_(t-1))^-1 x`. The chained identity (FP6) passes through these
intermediate orbit points. The good set `S°` keeps the points whose
suffix-trajectories stay good.

**Constants.** Put `m = |J|`, `ℓ_max = max ℓ(g)` and `Ł = Σ ℓ(g)`.
- Multiplicativity error: `< (ℓ_max+1)δ`.
- Bad points: `< (1+Ł)(m+1)δ N`.
- Alphabet: `|B'| >= |E'|^2/δ`.

These bounds are crude and polynomial in the data.

**What the proof never uses.**
- Soficity of the groups `G_i`.
- Any freeness of the action.
- Any amenability.
- Any property of stabilizers.

The whole input is factorwise orbit approximation on one packet.

## 4. Finite sanity check

Script: `experiments/free-products-of-sofic-actions-2026-09-16/check_construction.py`.
It is single-threaded and takes a few seconds.

- **Setup.** `G = C_2 * C_3` acts on `X = {0,1,2}` by `a = (0 1)` and
  `b = (0 1 2)`. The factor models are `A_j = G_j × [10]` acting by
  translation, with labels `Λ_(p,k)(y) = p^-1 y`. The good sets `S_j` are
  random 90 % subsets. The alphabet has `|B'| = 3`, and `N = 437400`.
- **What it builds.** Steps 2--7 of the route exactly: the randomized models,
  the label classes, the matching `β_2`, `φ` on all 14 reduced words of
  length `<= 3`, and the sets `S` and `S°`.

Output (`output.txt`):

```text
N 437400 |S|/N 0.2 |S°|/N 0.022222222222222223 #words 14
orbit identity violations on S°: 0
max multiplicativity defect (exact factor models): 0.0
ablation (unmatched bijection, per-word suffix-good points): violations 197286 of 722064 checks
```

Reading the output:
- (R3) is asserted inside the script.
- The chained identity holds exactly on `S°`.
- An arbitrary bijection instead of the label matching breaks it on about
  27 % of checks. So the matching is doing real work.
- `|S|/N = 0.2` because `|B'| = 3` makes only `6/27` of labels injective.
  The proof takes `|B'|` large.

This checks the bookkeeping, not the theorem. The theorem is the route.

## 5. Remarks not recorded as nodes

These are short consequences. They are not nodes because each is a direct
plug-in of Theorem B into an existing node, or depends on classical facts
that were not re-verified here.

**5.1 Tree actions with an 𝒜 quotient.** Let `Γ` act on a tree with a normal
subgroup `Λ` acting freely, and put `Q = Γ/Λ`. Item 3 of
`free-kernel-tree-actions-embed-in-free-generalized-wreath` makes `Γ` sofic
once
- `Q` is sofic, and
- each coset action `Q ↷ Q/Stab_Q(e)` is sofic.

If `Q ∈ 𝒜`, both hold automatically: item 1 of Theorem B gives soficity of
`Q`, and every set action of `Q` is sofic. So every such `Γ` whose free-kernel
quotient is a free product of amenable groups is sofic, whatever the edge
stabilizers are.

**5.2 A torsion-free member that is not LERF.** Put
`BS(1,2) = ⟨a, t | t a t^-1 = a^2⟩`. It is solvable, hence amenable, so
`BS(1,2) * Z ∈ 𝒜` by Theorem B.

The subgroup `⟨a⟩` is not separable in `BS(1,2)`.
- **In every finite quotient.** The image of `a` is conjugate to its square,
  so its order `n` is odd. Choose `k` with `2k ≡ 1 mod n`. Then
  `t^-1 a t = t^-1 (a^2)^k t = a^k` in the quotient. So the image of
  `t^-1 a t` lies in the image of `⟨a⟩`.
- **In the group.** In the faithful representation `a ↦ [[1,1],[0,1]]`,
  `t ↦ [[2,0],[0,1]]`, the element `t^-1 a t` maps to `[[1,1/2],[0,1]]`,
  which is not an integer power of `a`.

Hence `BS(1,2)` is not LERF, and neither is `BS(1,2) * Z`, since LERF passes
to subgroups. This member is finitely presented and torsion-free. Gao's
LERF theorem does not cover it. Its residual finiteness follows from the
classical theorem that free products of residually finite groups are
residually finite (Gruenberg), which was not re-verified here.

**5.3 Gao's Question 2.** Gao, arXiv:2402.17150, asks a question about
LERA groups. The exact wording was not verified in this session. Nothing
here claims to answer it. `Γ_p * Z` and `BS(1,2) * Z` may or may not be
LERA, and that was not examined.

**5.4 The countable-index case.** GKP remark that Proposition 2.15(4) reduces
Question 4.3 to two factors. The route does not need that reduction. A given
`(F,E,ε)` meets only finitely many factors, and the construction uses only
those (the remark "Countable index sets" in the route). The GKP reduction is
an alternative, equally valid path.

## 6. Amalgams over finite subgroups: a sketch, NOT claimed

**Target.** Let `G = G_1 *_C G_2` with `C` finite, and let `G ↷ X` have
sofic restrictions to `G_1` and `G_2`. Is `G ↷ X` sofic?

**What seems to go through.**
- **Exact `C`-action on a good set.** Given a factor model `φ_j`, let `P` be
  the set of points where `φ_j(c)φ_j(c') a = φ_j(cc') a` for all
  `c, c' ∈ C`. Put `Q = {a : φ_j(C) a ⊆ P}`. On `Q`, `C` acts exactly, and
  `|A \ Q| <= |C|^3 δ N`.
- **Free `C`-orbits.** If `G_j` is sofic, tensoring with a sofic
  approximation of `G_j` makes `C` act freely on most points. This is the
  only place where soficity of the factors would be used, unlike Theorem A.
- **Label orbits.** If the packet `E'` is `C`-invariant, then `C` acts on
  the label set `L = B'^(E')` by `(c·ℓ)(x) = ℓ(c^-1 x)`. The orbit identity
  forces the label of `φ(c) a` to be `c·ℓ_a` on good points.
- **Normal forms.** Choose transversals for `C\G_j` and write reduced words
  `g = c h_1 ⋯ h_r`. Define `φ` along this normal form, as in Step 4.

**Where it may die.**
- **Equivariant matching.** The junction of two normal forms produces an
  element of `C` that is modelled once through `ψ_1` and once through
  `ψ_2`. Multiplicativity needs `ψ_1(c) = ψ_2(c)` on most points. So the
  bijection `β` must be `C`-equivariant on most points *and* preserve labels.
- **Counting.** Such a `β` exists when, for each `C`-orbit `[ℓ]` of labels,
  both models have the same number of free `C`-orbits with labels in `[ℓ]`,
  up to `O(δ N)`. Equidistribution (R3) holds label by label on the good set
  of the randomized model. It was not checked whether the good set can be
  made `C`-invariant *without* destroying exact equidistribution. The
  randomization coordinate `T_j` is `C`-invariant, which is encouraging, but
  the bookkeeping was not done.
- **Normal-form instability.** Unlike the free product case, the normal form
  of `gh` is not a concatenation. Step 5 would need to push elements of `C`
  across syllables. Each push costs a `δ` term, and the number of pushes is
  bounded by word length, which seems harmless but was not checked.

This is recorded as a next step, not as a result.

## 7. Obstacles beyond this artifact

- **Amalgams over infinite amenable `C`.** The group-level theorem
  (amalgams of sofic groups over amenable subgroups are sofic; classical
  literature, not re-verified in this session) rests on uniqueness of sofic
  approximations of amenable groups up to approximate conjugacy. An action
  version would need a *labelled* uniqueness statement in the GKP setting.
  Păunescu, arXiv:1002.0605v5, Theorem 3.9, proves that his p.m.p. class is
  closed under amalgamation over amenable groups (graph node
  `paunescu-sofic-action-class-permanence`, verbatim import). No transfer from p.m.p. soficity
  to GKP set-action soficity is known here: GKP Proposition 4.1 goes from set
  actions to Bernoulli shifts, not back.
- **Nonamenable `C`.** Even the group version is open in general, so no
  action version is in reach.
- **The dyadic vertex action.** `PSL_2(Z[1/2])` acts on the Bruhat--Tits tree
  of `Q_2` and is the amalgam of two copies of `PSL_2(Z)` over `Γ_0(2)`
  (Serre, *Trees*, classical, not re-verified here). The edge group `Γ_0(2)`
  has finite index in `PSL_2(Z)`, so it is nonamenable. Theorem A says
  nothing about this amalgam, and Section 6 would not reach it.
- **Products `F × F'`.** Commuting factors have no normal form, so the
  syllable-by-syllable construction of Step 4 has nothing to act on. The
  graph node `product-of-free-groups-set-actions-are-sofic` remains OPEN.
  Question 4.2 (`commuting-sofic-actions-need-not-combine`) shows that
  commuting sofic actions can combine to a nonsofic one, so a product
  version of Theorem A is false in general. The positive product question is
  about free factors only.
- **The Kun--Thom group.** Its nonsofic coset action
  (`coordinate-action-not-sofic`) is untouched. By GKP Proposition 2.15(3),
  every action of `G * H` restricting to it on `G` is nonsofic. Theorem A is
  consistent with this and adds nothing.
- **The root claim.** Theorem A and Corollary C are *firewalls*. They show
  where obstructions to `RE/C` or to soficity of doubles cannot live: in
  vertex groups from `𝒜`. They do not exhibit a non-hyperlinear group.

## 8. Literature boundary

Sources consulted on 2026-09-16:

- Gao--Kunnawalkam Elayavalli--Patchell, arXiv:2401.04945v3 (Res. Math.
  Sci. 12 (2025) 48). Question 4.3 and the surrounding paragraph were re-read
  from the graph-verified transcription
  `research/artifacts/gkp-2401-04945-verified.md`.
- Gao, arXiv:2402.17150v2 (dated 2024-07-13). The abstract and HTML were
  fetched. It gives soficity of actions of LERF groups, a residually finite
  case with centralizer stabilizers, increasing unions of LERF groups, and a
  question on LERA groups. Everything here is paraphrased. No wording was
  verified verbatim. No statement about free products of arbitrary actors
  was seen.
- arXiv:2408.15470v1 (August 2024). Fetched. No resolution of Question 4.3
  was seen.
- arXiv:2601.18742v1 (dated 2026-01-26). Fetched. No resolution of Question
  4.3 was seen.
- Kun--Thom, arXiv:2608.06222. Used through the graph-verified artifact
  `research/artifacts/kun-thom-2608-06222-verified.md` and the node
  `coordinate-action-not-sofic`; the abstract was re-checked on 2026-09-16.
  It gives a nonsofic action of a sofic group. Nothing about free products
  of actions was seen in the abstract.
- Păunescu, arXiv:1002.0605v5. Read only through the graph node
  `paunescu-sofic-action-class-permanence`.
- The arxiv.org listing search for "sofic actions" (2026-09-16). No title
  mentioning free products of sofic actions was seen.

**Novelty caveat.** The web search budget was exhausted earlier in this
session, and the arXiv API was rate limited. So the priority search is
incomplete. A proof of Question 4.3 could exist in a paper whose title and
abstract do not mention it, or in a version newer than those fetched. The
mathematics of the route does not depend on novelty.
