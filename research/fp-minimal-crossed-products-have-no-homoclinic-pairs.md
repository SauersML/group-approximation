---
rg: 2
id: fp-minimal-crossed-products-have-no-homoclinic-pairs
kind: claim
title: Over any finitely generated acting group, a finitely presented crossed product of an infinite minimal subshift forces the subshift to have no homoclinic pairs, so every finite pattern is determined by its shell
distinct_from:
  sft-wall-rigidity-iff-idempotent-commutator-ideal: that is the case P = Z^2, where wall certificates are the first-order obstruction for SFTs; this proves the wall obstruction over every finitely generated group and turns homoclinic pairs of minimal subshifts into walls.
  positive-entropy-sft-crossed-products-are-not-fp: that kills positive entropy over Z^2 through ergodic pigeonholing; this kills a single homoclinic pair over any acting group, amenable or not, with no entropy or measure argument.
  labbe-shift-is-wall-rigid: that verifies wall rigidity for one Z^2 shift, killing finite clusters through entropy and a rotation factor; this derives the absence of finite clusters from finite presentation alone, over any group.
  fp-crossed-products-force-sft-over-any-group: that forces finite type; this is the next necessary condition, trivial homoclinic relation, and it uses that theorem for splicing.
  fp-crossed-products-force-connected-differences: concurrent independent derivation of the same wall obstruction (landed on another lane the same day); that states it as 2n-connectivity of every difference set and derives the minimal case from it, while this states the minimal-case conclusion directly and splices a homoclinic pair into a wall by recurrence. The two overlap essentially completely on infinite minimal subshifts; that one is the more general statement, since it constrains Δ(x,y) for all pairs, not only finite ones.
artifacts:
  - research/artifacts/fp-minimal-crossed-products-homoclinic-kill-2026-09-17.md
---

**OPEN** as stated (demoted 2026-09-18; see Attempts). Item 1 (no homoclinic pair), the wall
lemma and the recurrence splice are proved. Item 2 is proved only with the width-`2r` shell
`N_{2r}(F) \ F`; at the width `r` written below it needs the new hole
`fp-minimal-crossed-product-patterns-fill-width-r-shells`, now required by the route.

Let `P` be a finitely generated group, `A` a finite alphabet, `X ⊆ A^P`
an infinite minimal subshift and `k` a field. Suppose `LC(X,k) ⋊ P` is finitely presented. Then:
1. **No homoclinic pair.** There are no `T_1 != T_2` in `X` differing on a finite set.
2. **Unique shell filling.** Let `r` be the SFT radius of `X`. For every finite `F ⊆ P`, any two points of
   `X` that agree on the shell `N_r(F) \ F` agree on `F`.

**Wall lemma (the engine, no minimality needed).** Let `ℓ` bound the monomial lengths of a finite set of
relators in the generators `e_a`, `u_s^(±1)`. Then no `T_1, T_2 ∈ X` agree on `M` and differ somewhere in
`I` and somewhere in `O`, for a partition `P = I ⊔ M ⊔ O` with `d(I,O) > 2ℓ`.

*Why.* Take the module `k[P] ⊗ k^2` where `e_a` reads `diag(T_1, T_2)` in the basis `(w_1, w_2)` on `I ∪ M`,
and in the basis `(w_1 + w_2, w_2)` on `M ∪ O`. Each relator only sees an `ℓ`-ball, which misses `I` or
`O`, so it acts as `ρ_(T_1) ⊕ ρ_(T_2)` and vanishes. But the idempotents at a site in `I` and a site in
`O` do not commute.

**Why it matters.** Any Cantor crossed-product host of
`decidable-group-algebras-have-fp-cantor-crossed-hosts` is simple, hence minimal, so it must be
shell-determined. Every construction that stores information in locally re-colourable cells dies at
finite presentation, over every acting group. This includes decorations of a rigid base by free local
bits, and strongly irreducible minimal SFTs. The quantitative consequences are in
`fp-minimal-crossed-products-have-shell-bounded-complexity`.

DERIVATION
fp-minimal-crossed-products-have-no-homoclinic-pairs-proof

## Attempts

- 2026-09-18 (adversarial referee pass, outcome refuted as stated, verdict 38d515af): **item 2
  states the shell at half its proved width.** Referee's reason, verbatim:
  - "Compiled status on current origin/main was ESTABLISHED (route
    fp-minimal-crossed-products-have-no-homoclinic-pairs-proof marked COMPLETE), so review was
    required. Citation lens PASSES: the sole prerequisite fp-crossed-products-force-sft-over-any-group
    is ESTABLISHED and says exactly what is used (X is defined by forbidding n-ball patterns, i.e.
    window radius r, same quantifiers, right direction). Calibration lens PASSES: Lemma 1 genuinely
    uses group-only input — invertibility of u_p in step 4 (e_a commutes with u_p e_b u_p^{-1})
    collapses over a monoid, and left-invariance of d is used both for the locality of monomials
    (sites lie in z^{-1}B_l) and for N_w(gF)=gN_w(F) in the splice; nothing non-unimodular or
    tree-automaton-specific is smuggled in. Gaps lens DECIDES and fails, at route Step 6 = artifact
    Corollary 3: it asserts 'every r-window meeting F lies in N_r(F)'. That is false. A window is
    y|_{pB_r}; if pB_r meets F then p in F B_r, hence pB_r is only contained in F B_{2r} =
    N_{2r}(F). So the spliced point z (= y on F, x elsewhere) is only certified to lie in X when
    x = y on N_{2r}(F)\\F, not on N_r(F)\\F as the claim's item 2 states. The artifact contradicts
    itself here: Theorem 2 Step 4 uses the correct inclusion ('it meets D_0, it lies in N_{2r}(D_0)
    = K'), and the concurrent sibling fp-crossed-products-force-connected-differences states the
    same result with layer width 2r (∂F = {p in F : pB_{2r} not contained in F}) and proves it via
    'a window pB_r meeting I at q lies in qB_{2r}'. The underlying general principle invoked at
    radius r is demonstrably false: the period-4 orbit of (0011)^inf in {0,1}^Z is a minimal SFT of
    window radius r = 1 (allowed 3-blocks 001, 011, 110, 100; follower graph is a single 4-cycle so
    the SFT is exactly that 4-point orbit) with no homoclinic pairs, yet the two points with shell
    (x(-1),x(1)) = (0,1) differ at 0 — verified by script; at 2r = 2 the collision disappears. Item
    1 (no homoclinic pair), Lemma 1 (two-basis module on k[P] ⊗ k^2, the relator-vanishing and
    non-commuting-idempotent steps) and the recurrence splice all survive scrutiny, but claim item
    2 as written is unproved, so the route is not COMPLETE and the claim is not ESTABLISHED as
    stated. It also propagates: artifact Corollary 4 (|L_F(X)| <= |A|^{|N_r(F)\\F|}) inherits the
    wrong exponent. Fix is to restate items 2 and Cor. 3/4 with N_{2r}(F)\\F. No computation is
    asserted by the claim (artifacts list only
    research/artifacts/fp-minimal-crossed-products-homoclinic-kill-2026-09-17.md; nothing under
    experiments/)."
  - **The exact step that fails.** Step 6 of the route (= Corollary 3 of the artifact): "its
    windows meeting `F` lie in `N_r(F)`".
  - **Demotion.** The missing statement is now
    `fp-minimal-crossed-product-patterns-fill-width-r-shells` (OPEN), added to the route's
    `requires:`. The proof file is kept: items 1 and the wall lemma stand, and Step 6 proves item 2
    at width `2r`.
