---
rg: 2
id: fp-minimal-crossed-products-have-shell-bounded-complexity
kind: claim
title: A finitely presented crossed product of an infinite minimal subshift has pattern counts bounded by shell size, so it has zero entropy over amenable groups, is impossible over virtually cyclic groups, and has log-complexity at most C N^(d-1) over Z^d
distinct_from:
  positive-entropy-sft-crossed-products-are-not-fp: that is Z^2 and all SFTs; this is every amenable acting group, for minimal subshifts, with a quantitative bound by the shell rather than only zero entropy.
  minimal-subshift-crossed-product-is-not-finitely-presented: that is P = Z through LEF; this covers every virtually cyclic P, including torsion, through bounded shells, with no LEF argument.
  fp-minimal-crossed-products-have-no-homoclinic-pairs: that is the qualitative shell determination; this is its counting consequences.
  fp-crossed-products-force-connected-differences: parts 2 and 3 of that node, landed concurrently on another lane, give the same counting consequences from the same wall argument, with the bound written over the inner boundary layer ∂F rather than the outer shell N_r(F) \ F; the zero-entropy and virtually-cyclic corollaries coincide; the two are NOT equivalent up to the choice of layer, since an inner layer of width 2r and an outer shell of width r differ by a factor of two in thickness, and part 1 as stated here is the strictly stronger one (see Attempts, 2026-09-18).
artifacts:
  - research/artifacts/fp-minimal-crossed-products-homoclinic-kill-2026-09-17.md
---

**OPEN** as stated (demoted 2026-09-18; see Attempts). Parts 2, 3 and 4 go through verbatim
with `2r` in place of `r`. Part 1, the headline quantitative bound, is proved only as
`|L_F(X)| <= |A|^(|N_{2r}(F) \ F|)`; at the width `r` written below it needs the new hole
`fp-minimal-crossed-product-patterns-fill-width-r-shells`, now required by the route.

Let `P` be finitely generated, `X ⊆ A^P` an infinite minimal subshift and
`k` a field. Suppose `LC(X,k) ⋊ P` is finitely presented, and `X` has SFT radius `r`. Then:
1. **Shell bound.** `|L_F(X)| <= |A|^(|N_r(F) \ F|)` for every finite `F ⊆ P`.
2. **Amenable `P`.** `h_top(X) = 0`.
3. **Virtually cyclic `P`.** This never happens: `LC(X,k) ⋊ P` is not finitely presented for any infinite
   minimal `X`.
4. **`P = Z^d`.** `log|L_(B_N)(X)| <= C N^(d-1)`.

**Why it matters.** For `decidable-group-algebras-have-fp-cantor-crossed-hosts` over `Z^2`, a host's ball
complexity is at most exponential in the perimeter `N`. Growth counting for hosting `F_2` gives the
matching lower bound `e^(cN)`, so the complexity is pinned to `Θ(N)`. That is sharper than `e^(o(N^2))`:
hard languages must live in which one-dimensional boundary data occur, not in bulk. Over every amenable
acting group, positive-entropy minimal hosts die with no measure-theoretic input.

DERIVATION
fp-minimal-crossed-products-have-shell-bounded-complexity-proof

## Attempts

- 2026-09-18 (adversarial referee pass, outcome refuted as stated): **part 1's shell width is off
  by a factor of two.** Referee's reason, verbatim:
  - "Refuted at Step 1 of the route
    (research/fp-minimal-crossed-products-have-shell-bounded-complexity-proof.md line 14-16), which
    is Corollary 3 + Corollary 4 of
    research/artifacts/fp-minimal-crossed-products-homoclinic-kill-2026-09-17.md (lines 100-108).
    The shell width is off by a factor of two.
  - The artifact's own conventions (lines 9-10, 75) fix N_w(F) = F B_w for the left-invariant
    metric, and fix the SFT windows to be BALLS OF RADIUS r, i.e. sets p B_r of diameter 2r.
    (fp-crossed-products-force-sft-over-any-group confirms this: 'X is defined by forbidding the
    n-ball patterns'.) So a window p B_r that meets F at some f satisfies f in p B_r, hence p in
    f B_r, hence p B_r is contained in f B_2r, i.e. in N_2r(F) — NOT in N_r(F). The containment is
    sharp: take F = {f} and p at distance exactly r from f; the window reaches distance 2r from f.
  - Corollary 3's proof asserts exactly the false containment: 'Every r-window meeting F lies in
    N_r(F)'. With only x = y on N_r(F) \\ F, the spliced point z (= y on F, = x elsewhere) is a MIX
    of y and x on windows that poke into N_2r(F) \\ N_r(F), so those window patterns need not be in
    L_{B_r}(X) and z need not lie in X. The homoclinic-pair contradiction is therefore never
    reached.
  - This is an internal contradiction, not an interpretation: the SAME artifact gets the geometry
    right 25 lines earlier. Theorem 2, step 4 (line 83) says of a window meeting D_0: 'It lies in
    N_(2r)(D_0) = K' — and sets K = N_2r(D_0) (line 77) precisely because window-meets-a-set puts
    it in the 2r-neighbourhood. Corollary 3 then writes N_r for the identical situation.
  - Consequence: claim part 1, |L_F(X)| <= |A|^(|N_r(F) \\ F|), is unproven as stated; what the
    argument gives is |A|^(|N_2r(F) \\ F|). That is not a cosmetic constant — part 1 is the
    headline quantitative content that the node's distinct_from block uses to separate it from its
    siblings. Corroboration from main: the concurrent independent node
    fp-crossed-products-force-connected-differences (also ESTABLISHED) states the same result with
    the layer taken at width 2r — dF = {p in F : p B_(2r) not contained in F} — and its 'Why it
    matters' says explicitly 'read off from a layer of width 2r'. The reviewed node's distinct_from
    entry for that node claims 'the two are equivalent up to the choice of layer'; that is false,
    inner-layer-of-width-2r versus outer-shell-of-width-r differ by the factor 2 in thickness, and
    the reviewed node is strictly stronger and unsupported.
  - What survives: parts 2, 3 and 4 all go through verbatim after substituting 2r for r, since they
    only need the shell to be o(|F_n|) (Cor. 6), bounded (Cor. 5: F_n B_2r still lies in {c^i g_j :
    |i| <= n + C_2r}, shell <= 2 m C_2r, so |X| <= |A|^C, contradicting X infinite — I checked the
    coset bookkeeping, it needs no normality and is correct), or O(N^(d-1)) (Cor. 7). I also checked
    the other two lenses and found nothing worse: citations — the route cites
    fp-minimal-crossed-products-have-no-homoclinic-pairs for exactly its part 2 (which carries the
    same N_r misstatement upstream), and the whole prerequisite chain (no-homoclinic-pairs,
    fp-crossed-products-force-sft-over-any-group) is ESTABLISHED; calibration — the wall lemma
    genuinely uses invertibility of u_s (relators include U_s U_s^(-1) - 1) and the left-invariant
    metric, so it does not transfer to monoids, and the shell counting is honestly vacuous over
    trees/one-ended non-amenable P, which the artifact acknowledges. The only other blemish is Cor.
    6 step 1's justification 'An amenable group acting on a set admits Følner sets for that action',
    which is not a valid general principle, though the conclusion it needs (two-sided Følner
    sequences exist in every amenable group) is a true standard theorem, so that is a sloppy
    citation rather than a gap. No computation is asserted, so step 4 of the review was vacuous.
  - The claim should be demoted to OPEN, or restated with N_2r(F) \\ F in part 1 (in which case
    parts 1-4 all hold)."
  - **The exact step that fails.** Step 1 of the route, "the pattern of a point on `F` is a function
    of its pattern on `N_r(F) \ F`".
  - **Demotion.** The missing statement is now
    `fp-minimal-crossed-product-patterns-fill-width-r-shells` (OPEN), added to the route's
    `requires:`. The proof file is kept: parts 2-4 stand at width `2r`.
