# Idea lane nh-hs-stability (2026-09-13)

- **Target:** `non-hyperlinear-group`.
- **Lens:** Hilbert–Schmidt stability, strict and flexible.
- **Status:** ideas only. Nothing here is claimed, and no Cairn node was edited.

## What the lens already has on main

These were read so the lane would not repeat them:
- **Dichotomy for Kazhdan groups:** `hs-stability-plus-fd-residual-forces-nonhyperlinearity`, `hyperlinear-flexibly-hs-stable-group-is-residually-finite`, and `infinite-hyperlinear-kazhdan-group-is-not-hs-stable`. By Fournier-Facio–Gerasimova–Spaas (arXiv:2307.13155, abstract checked), infinite hyperlinear property (T) groups are not even locally HS-stable. For a Kazhdan group without finite-dimensional representations, HS stability is therefore the same statement as non-hyperlinearity.
- **Conditional routes:**
  - Dogon (arXiv:2211.10492, abstract checked): flexible HS stability of `Sp_2g(Z)` gives a non-hyperlinear group (`dogon-sp2g-weak-ucp-nonhyperlinear`).
  - Dogon–Vigdorovich (arXiv:2506.20843, abstract checked): flexible HS stability of `SL_2(Z[1/p])` gives a non-hyperlinear finite central extension (`dv-s-arithmetic-hs-stable-nonhyperlinear-extension`).
  - The root's September 7 entry shows that flexible HS stability of `SL_5(Z)` is equivalent to its seed bounds.
- **Metric ladder for Deligne covers:** `deligne-cover-sector-floor-below-exponent-one-half` is OPEN, and b = 0 there is non-hyperlinearity.
- **The non-sofic group:** `binary-leavitt-unit-group-is-permutation-stable` is ESTABLISHED, through `binary-leavitt-full-character-simplex` and `openai-leavitt-unit-nonsofic`. Its HS analogue is exactly the open branch recorded on `binary-leavitt-unit-group-hyperlinear` ("needs an actual bad trace").

## Approach 1: monomial and block-monomial models of the Leavitt unit group

- **Idea.** Let `H = L_(F_2)(1,2)^x`. Take an HS almost-homomorphism of H into monomial unitaries, or into `U(k) wr S_n`.
  - Its permutation part is a Hamming almost-homomorphism, since `d_H <= ||M-M'||_2^2/2`.
  - That part's fixed-point character lies in the trivial–regular simplex.
  - Nonsoficity forces the regular weight to vanish, so the model is almost block diagonal.
  - For monomials, perfectness of H then kills the diagonal phases. For bounded k, ultralimits in the compact group `U(k)` are genuine representations, which are trivial by minimal almost periodicity (`binary-leavitt-minimal-almost-periodicity-proof`).
- **Would prove.** No hyperlinear approximation of H is monomial, or block-monomial with bounded blocks.
- **Kill test (run):** repository duplicate check.
- **Result:**
  - `binary-leavitt-unit-group-hyperlinear` (lines 374–379 at 8a07ad7d0) already records the monomial exclusion, phases included, by the same projection and perfectness argument.
  - `block-monomial-hs-models-sofic-mod-amenable-soft-kernel` (ESTABLISHED) covers block-monomial models in general. The quotient by the soft kernel is sofic, and the soft kernel is amenable for bounded blocks.
  - Remaining delta, unclear: for unbounded blocks with an approximately normalized abelian subalgebra, does the model descend to a direct sum of smaller H-models? This needs H to have no nontrivial sofic quotient beyond what that claim gives, which is not recorded.
- **Verdict:** killed as a duplicate. The direct-sum descent delta is unclear and low value.

## Approach 2: norm interpolation through Bachner–Dogon–Lubotzky

- **Idea.** BDL Theorem 1.3 (arXiv:2508.17392v3, quoted on `bdl-deligne-type-two-norm-inapproximability`): if a Deligne-type group is `||.||_q`-stable, it is not `||.||_p`-approximated for `p <= q`. The hope was to run this at q = 2 in the normalized norm and get non-hyperlinearity.
- **Would prove.** Non-hyperlinearity of a finite Deligne cover.
- **Kill test (run):** read the node and the BDL abstract.
- **Result:**
  - BDL's norms are unnormalized Schatten norms.
  - The normalized HS form is b = 0 in `deligne-cover-sector-floor-below-exponent-one-half` (OPEN), i.e. the recorded metric ladder.
  - BDL Proposition 1.5 (operator-HS-stable plus Deligne-type implies not MF) gives non-MF, not non-hyperlinear.
- **Verdict:** killed as a new route. It is the recorded ladder.

## Approach 3: dimension-free defect diminishing from vanishing H²

- **Idea.** De Chiffre–Glebsky–Lubotzky–Thom (arXiv:1711.10238, abstract checked) turn higher cohomology vanishing into Frobenius stability. With non-residually-finite central extensions of p-adic lattices, that gives groups not approximable in the Frobenius norm. The idea was to rerun their iteration with the normalized HS norm on `M_d(C)`, whose conjugation representation has the same uniform vanishing constants.
- **Would prove.** HS stability of those extensions. Since they are not residually finite, that means non-hyperlinearity.
- **Kill test (run):** the correction step's quadratic remainder, and the root's audits.
- **Result:**
  - The remainder is bounded by operator norm times HS norm. Normalized HS almost-representations can have O(1) operator-norm error on small subspaces, and the normalized norm is not submultiplicative.
  - The root's September 5 entry records that vanishing H² concentrates curvature on supports of quadratic relative rank, but does not make those supports invariant.
  - BDL Conjecture 1.8 (vanishing H² implies operator-HS stability) is the open operator-norm form.
- **Verdict:** killed as recorded.

## Approach 4: amplify the Deligne sector floor by cutting down the dimension

- **Idea.** The floor in (SF1) is `c d^(-b)` with `b < 1/2`. If cutting a model down to dimension `d'` cost only `O(d'^(-1/2))` in defect, then fixing a large `d'` would give a floor independent of d, and so non-hyperlinearity.
- **Would prove.** b = 0, i.e. the root, for the finite Deligne covers.
- **Kill test (run):** when can a compression stay almost unitary?
- **Result:**
  - Random subspaces give O(1) non-unitarity.
  - Almost-invariant subspaces are controlled by `kazhdan-unitary-corners-require-finite-dimensional-mass` (KFM1): almost-unitary Kazhdan corners need nearly full finite-dimensional mass, and finite-dimensional representations kill the central sector.
  - The root's September 5 entry records that small exact seeds plus regular tails cannot build the needed dilation.
- **Verdict:** killed.

## Approach 5: round the finite vertex groups, then solve a finite twisted intertwiner system

- **Idea.**
  - **Setting.** Take a lattice Γ acting on a simply connected high-rank building with finite stabilizers. Γ is then the colimit of its finite stabilizers over the finite quotient complex. The non-residually-finite central extensions `Γ~` used by dCGLT are central extensions of such colimits.
  - **Rounding.** Restrict an HS almost-representation of `Γ~` in sector `z -> zeta` to each finite preimage stabilizer. All-pairs defects there are bounded by the relator defects, with fixed constants. `gowers-hatami-finite-group-hs-stability` (universal constant 42ε, flexible enlargement) rounds each restriction to a genuine representation.
  - **Edges.** Along an edge group, two genuine representations whose compressions are close have nearly equal multiplicities, so there is an approximate intertwiner.
  - **Finite system.** The model becomes: vertex multiplicity vectors, edge unitaries on multiplicity spaces, and a 2-cell holonomy condition carrying ζ.
  - **Why ζ matters.** Exact data would give a genuine finite-dimensional representation of the colimit extension. There z dies, because z lies in the finite residual and superrigidity makes finite-dimensional representations factor through finite quotients.
  - **Payoff.** The question becomes stability of a finite twisted system. It has an explicit, bounded search space of multiplicities and intertwiners, which could be probed numerically for small buildings.
- **Would prove.** If the twisted system has a d-independent defect floor, `Γ~` is non-hyperlinear. These groups are Frobenius stable (dCGLT) and not residually finite, so their normalized HS status is the open question.
- **Kill test (run):**
  - Repository duplicate check: the Deligne sector-floor artifacts and the metric ladder don't use finite-subgroup rounding or complexes of groups. `finite-subgroup-combination-defects-2026-09-12` concerns idempotents in `F_p[G]`.
  - Literature: the colimit structure for lattices acting on buildings with finite stabilizers is the standard complex-of-groups picture. It was not source-checked here. The web search found no treatment of this rounding.
- **Result.** There are three open risks:
  1. The rounding may not lower the difficulty: the twisted system could be equivalent to flexible stability of the colimit itself.
  2. The flexible enlargements differ from vertex to vertex, so gluing needs bookkeeping.
  3. The extension class may be invisible on the stabilizers, and then it appears only as the holonomy scalar. That is intended, but it must be checked for the specific dCGLT groups.
- **Verdict:** unclear. It survives to triage.
- **Next tests:**
  - Source-check the complex of finite groups for one concrete dCGLT lattice.
  - Write the twisted intertwiner system exactly.
  - Test whether a d-independent floor for it follows from, or is equivalent to, a recorded open node.

## Sources checked

- Dogon, arXiv:2211.10492 (abstract).
- Dogon–Vigdorovich, arXiv:2506.20843 (abstract).
- Fournier-Facio–Gerasimova–Spaas, arXiv:2307.13155 (abstract).
- de Chiffre–Glebsky–Lubotzky–Thom, arXiv:1711.10238 (abstract).
- Bachner–Dogon–Lubotzky, arXiv:2508.17392 (abstract; statements as quoted on the repository node).
- Fournier-Facio, arXiv:2512.09180 (abstract: Frobenius-stable fp (T) groups far from (T_2); no normalized HS content).
