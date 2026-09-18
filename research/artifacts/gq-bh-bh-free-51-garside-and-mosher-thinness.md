# bh-free-51: thinness tests on mapping-class-group automatic structures

Lane bh-free-51, BH swarm, 2026-09-18. These are lane proofs, not independently reviewed, and
no priority is claimed. The coordinator asked for the thinness (E1') and germ (E4') tests of
`automatic-groups-embed-in-corner-germ-extensions` to be run on Mosher's automatic structure,
starting small and ending with closed `Mod(S_g)`.

## 1. Sources read at source

- **BBCMP.** Belk--Bleak--Chatterji--Matucci--Perego, *Rational embeddings of continuous
  automatic groups* (preliminary 2026), pp. 2--6 and 11--14. The PDF is in the swarm scratchpad
  `src/bbcmp/`.
  - The Deligne language (p. 11):
    "`L = {Δ^{-j} x_1 ⋯ x_n | x_1 → x_2 → ⋯ → x_n and x_1 ≠ Δ if j > 0}`", where
    `x → y` means `pref(xy) = x`.
  - Theorem 2.4 (continuity) is proved on pp. 11--12.
- **Mosher.** L. Mosher, *A user's guide to the mapping class group: once punctured surfaces*,
  arXiv:math/9409209v1. The TeX source was fetched on MSI to `gqsrc/bh-free-51/`, with a copy
  in `src/mosher/`. Read: the introduction, §I pp. on ideal arc systems and elementary moves,
  and §II (asynchronous normal forms) in full.
  - **Closed surfaces are non-constructive.** From the introduction: "while an automatic
    structure for the mapping class group of a closed surface is described in [M], in this
    case the results are *not* suited for practical calculation, because of the
    non-constructive nature of the proof".
  - **Shape of the once-punctured normal forms** (§II):
    - The alphabet consists of labelled elementary moves (flips) and relabellings.
    - The language `L_0` is prefix closed: "the set of failure states forms a dead end set".
    - Every word factors as `w = w^κ ∘ ⋯ ∘ w^1 ∘ r` into "uncombing blocks", with
      `κ = 12g − 6`. Levels only decrease.
    - Inside a block, every move after the first is a *parity arrow*, `L` or `R`: a flip of
      `h^L` or `h^R` at the marked prong.
    - The deepest level `M^1_0` "is a strongly connected digraph".
    - So every infinite normal form is a finite prefix followed by an infinite `L`/`R`
      parity sequence inside one level `j`. During that tail the base arcs `g_1, …, g_{j−1}`
      stay combed.
  - The Annals paper [M] (*Mapping class groups are automatic*, Ann. of Math. 142 (1995)) is
    not on arXiv and was not read.

## 2. Results landed

- **`deligne-forms-are-singular-on-commuting-parabolic-diagonals`** (+ proof).
  - *Where it applies.* The Garside/Deligne structures:
    - BBCMP's language, and bh-hhg's quotient language `L̄`;
    - of Artin groups with an edge `{s,t}` (`m ≥ 3`) and a node `u` commuting with both,
      for example `B_n`, `n ≥ 5`.
  - *Mechanism.* Commuting parabolics are processed in lockstep:
    `NF(p u^m) = (x_1u) ⋯ (x_mu) x_{m+1} ⋯`.
  - *Result.* `s^N` shifts the `P`-column against the `u`-column. So `s^N` is singular, over
    `B` and over `V` after any recoding, on a Cantor set of diagonal points.
  - *Consequence.* This kills (E1') for the structures bh-hhg uses on `Mod(S_{0,n})`,
    `n ≥ 6`, and on `Mod(S_2)`. BH is already known for those groups.
- **`b3-center-first-normal-form-passes-the-germ-condition`** (+ proof).
  `B_3 = Mod(S_1^1)`.
  - The BBCMP language is thin, with singular points `Δ^{±∞}`.
  - But (E4') fails in both branches, because `⟨Δ⟩` is a non-normal, infinite-index subgroup
    of the germ group `B_3`.
  - Writing `z = Δ^2` as a leading letter repairs it: the germ group is `B_3` over `Z(B_3)`,
    with quotient `PSL_2(Z)`, so `Γ` is `F_∞` and `B_3 ∈ B_A` through the machine.
  - This is the first nonabelian germ group, and it shows central `F × Z` pieces are harmless
    when the center is written first.
  - It calibrates bh-free-08's `bhm-corollary-hosts-over-v-are-cover-centralizer-groups` (b):
    the Deligne germs commute with `τ_q^2`, so (b) holds with `a = 2`, yet hypothesis (3)
    fails. So (b) is necessary but not sufficient.
  - BH for such central extensions is already on main, through a different host
    (`odometer-lift-central-extensions-of-v-subgroups-into-2v-tau`). No separate
    central-extension node was landed.

## 3. Status of the Mosher test (not a result; recorded so no one repeats the search)

- **Closed `Mod(S_g)`, `g ≥ 2`.** The test cannot be run on Mosher's structure: at source the
  structure is non-constructive, so there is no transducer to test.
- **Once-punctured `Mod(S_{g,1})`.** The structure is explicit. The test has two stages:
  1. Continuity of `L_0`, which is BBCMP Q1.16 for these surfaces; bh-hhg owns it.
  2. Thinness.
- **Heuristic, unproved.** Mosher's normal forms are sequential by base-arc index, not
  lockstep: the arc `g_κ` is uncombed first and `g_1` last. So the Garside mechanism of §2 does
  not transfer. The relevant test is the behaviour at deeper-level tails, where
  `g_1, …, g_{j−1}` stay combed forever and the tail runs in the stabilizer of those arcs.
- **The crux, for any structure on closed `Mod(S_g)`, `g ≥ 2`.** It contains `F_2 × F_2`,
  from `Mod` of two disjoint one-holed tori, and neither factor is central.
  - Lockstep processing fails, by §2.
  - Sequential processing fails once the first factor has a Cantor limit set (bh-free-21's
    product computation).
  - The `B_3` repair needs a central factor, which is not available here.
  - Whether some continuous normal form on a group containing `F_2 × F_2` is thin is the
    precise open question.

## 4. Lesson for general BH

- **Rank-one hosts absorb only virtually central cyclic directions.** A germ extension of `V`
  certified by Belk--Hyde--Matucci has, at every singular point, a period shift that is
  central in the germ group (bh-free-08 (b), normal clause). A normal-form boundary can
  therefore feed it only through commuting directions of that kind: flat corners, or a
  center written first.
- **Non-central commuting pairs fail uncountably.** Garside lockstep, and product forms,
  produce relative phase shifts, and these are singular on Cantor sets.
- **Consequence for mapping class groups.** Closed `Mod(S_g)`, `g ≥ 2`, contains
  `F_2 × F_2` with no central side. So the automatic-structure route to it through rank-one
  hosts is blocked for these forms, and a higher-rank host (bh-free-36's cube categories) is
  the natural replacement.
- **A cap on the whole method.** bh-free-08's cap (d), a proof sketch there, says that everything BHM certifies
  over `V` has bounded word-problem complexity.
