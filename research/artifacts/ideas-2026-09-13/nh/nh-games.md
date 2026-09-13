# Idea lane nh-games: MIP* = RE and solution groups, 2026-09-13

Target: `non-hyperlinear-group`. Lens: MIP* = RE and Slofstra's solution
groups of linear-system games. This file records ideas and kill tests. It
claims nothing and changes no node.

## What the repo already has in this lens (read first)

This family is heavily mined; the 2026-09-12 route map
(`research/artifacts/nh-fresh-route-map-2026-09-12.md`, §1.C) lists about 70
routes.

- **The exact target.** `lcs-tracial-ru-gap-equiv-nonhyperlinear` (Paddock–Slofstra, Prop. 5.8): a finitely presented nonhyperlinear group exists iff some binary LCS is tracially satisfiable but not R^U-satisfiable. `locally-affine-support-bcs-is-exactly-the-lcs-boundary` extends this to BCS whose tracial local supports have affine hulls inside the allowed sets.
- **Perfect-completeness crux.** `perfect-completeness-constant-soundness-lcs-compiler` is OPEN. Its sub-routes go through Culf–Mastel / DFNQXY supports (`affine-halt-support-and-pcpp-section-close-nonhyperlinear-chain`, conditional), Fano caps and central-tagged ONE3.
- **Known walls.**
  - `central-pinning-forbids-nonlinear-predicates`: with a unique sector, joint spectra are affine.
  - `inverse-semigroup-globalization-cannot-groupify-nonru-bcs`.
  - `diracization-gap-equals-nonhyperlinear-group`.
  - `exact-fd-invisibility-has-no-general-hs-robustification`.
  - The trace-selection separation in `research/artifacts/ex-nh-mipstar-quantum-symmetry-rung-2026-09-12.md`: MIP* = RE gives a trace that no symmetry selects.
- **Group-factor holes.** `non-ru-bcs-is-satisfiable-in-a-group-factor` (OPEN) and `non-ce-twisted-group-factor-exists` (OPEN, feeding `nonce-twisted-factor-gives-nonhyperlinear-group`).

The approaches below were chosen to avoid these, or to be killed against them
explicitly.

## Approach 1. Marked-group limits of approximate group models

**Idea.** Do not ask one group algebra to carry the non-R^U BCS `B_*` exactly.
Build groups `Gamma_n` whose regular-trace corners `(1-J_n)/2` carry
`eps_n`-approximate models of `B_*`, with `eps_n -> 0`. Pass to a limit `Gamma`
in the space of marked groups. The regular character is continuous under
marked convergence (a word is trivial in the limit iff trivial eventually), so
the constraints would hold exactly in a corner of `L(Gamma)`.

**Would prove.** `non-ru-bcs-is-satisfiable-in-a-group-factor` for the limit,
hence a nonhyperlinear `Gamma`.

**Kill test.** Can the stage groups `Gamma_n` be hyperlinear?

**Result.** No, once `eps_n` is small. By
`non-ce-bcs-has-finite-dimensional-forbidden-mass-gap`, `B_*` has a constant
`beta_B > 0`: every matricial tuple of involutions commuting exactly within
contexts has total forbidden mass at least `beta_B`. If `Gamma_n` were
hyperlinear, its approximate corner model would pass to matricial microstates
with forbidden mass `O(eps_n)`, contradicting the gap. So all but finitely many
stage groups must already be nonhyperlinear.

**Caveat.** FMG assumes exact within-context commutation, so the transfer needs
a rounding step for almost-commuting involutions. That step only makes the kill
stronger in practice, not weaker.

**Verdict.** Killed (circular).

## Approach 2. Nonabelian central packets with many odd sectors

**Idea.** Central pinning forces affine supports only when exactly one
irreducible has `pi(J) = -I`. Use quasirandom finite groups with a central
involution and many odd sectors, such as covers of `PSL_2(F_p)`. Nonlinear
predicates then become sector predicates, while Gowers–Hatami stability for
finite groups keeps HS robustness.

**Would prove.** A group-realizable compiler for nonlinear BCS predicates,
evading the linear-only limit.

**Kill test.** Is a nonabelian packet for every predicate already on main, and
where does that route stop?

**Result.** Yes: `every-predicate-has-s3-equivariant-raw-radical-drop`, used by
`algebraic-pcp-s3-radical-groupification-route`, gives an S3-equivariant packet
for every predicate. That route stops at
`binary-pcp-coordinate-atlas-in-hs-microstates` (shared involution words for
proof coordinates in arbitrary matrix microstates). Swapping S3 for a
quasirandom group changes the packet constants, not that atlas crux.

**Verdict.** Killed (duplicate; same terminal crux).

## Approach 3. Trace selection by verifier symmetries

**Idea.** The MIP* = RE trace is not selected by any symmetry. Average it over
a finite or amenable group `K` of question/answer relabelings of the verifier,
or over `S_infinity` permuting tensor copies (de Finetti). The result is a
`K`-invariant trace. The set of Connes-embeddable traces is closed and convex,
and embeddability passes to central summands, so averaging keeps the trace
non-embeddable.

**Would prove.** A symmetry-selected non-CE trace, supposedly the missing
selection.

**Kill test.** Does automorphism invariance produce a group algebra?

**Result.** No. The host becomes `A(B_*) ⋊ K` with an invariant trace, which is
not a group algebra, so the hole `non-ru-bcs-is-satisfiable-in-a-group-factor`
is untouched. The ex-nh-mipstar rung shows that the collapse selecting the
trace needs a group-like coaction (`g -> g ⊗ g`) with a unique invariant state.
Automorphic actions do not provide that.

**Verdict.** Killed (reduces to the open hole with no leverage).

## Approach 4. Quantum tiling games: translation-invariant LCS as finitely presented hosts

**Idea.**
- Take a binary linear constraint rule on `Z^2`: finitely many local contexts, invariant under translation, with the usual central `J`.
- Its solution group `Sol` is infinitely generated. The semidirect product `Gamma = Sol ⋊ Z^2` is finitely presented: one site's variables and the translations generate it, and the local rule plus its translates are finitely many relations modulo conjugation.
- Hyperlinearity of finite-patch groups does not pass to `Sol`, because a patch group only maps onto a subgroup of `Sol` (a quotient, not a subgroup). The infinite-volume limit can therefore lose hyperlinearity even when every patch is hyperlinear.
- The source of non-approximability is aperiodicity, not a compiler.

**Would prove.** If some local rule has `J != 1` in `Gamma` and every R^U model
of `Gamma` kills `J`, then `Gamma` is a finitely presented nonhyperlinear group.

**Kill tests run.**
1. **Amenable reduction.** `Gamma` is hyperlinear iff `Sol` is (standard permanence under amenable extensions and subgroups). Passes; it only moves the problem to `Sol`.
2. **Quotient loophole.** Patch groups surject onto subgroups of `Sol`, so no inheritance obstruction. Passes.
3. **Classical periodicity.** For commuting (classical) linear rules, algebraic `Z^2`-subshifts have dense periodic points, so classical linear rules cannot be aperiodic. This kills commutative rules only. Noncommutative magic-square-type local rules are not covered.
4. **Repo overlap.** The 2026-09-13 quantum-tiling nodes are the closest.
   - `labbe-lef-via-periodic-quantum-tilings` and `free-minimal-z2-sft-is-quantum-rigid` concern derived full groups and ring crossed products of free minimal SFTs, not solution groups with central `J`.
   - Technique overlap: periodic quantum tilings (finite-dimensional modules of the local tiling algebra) are exactly what must fail here. A periodic finite-dimensional quantum tiling with `J = -I` at every scale gives finite-dimensional models of `Gamma` and kills that rule.
   - Not a duplicate of any route in the route map.
5. **Literature spot check.** A web search for undecidability of translation-invariant nonlocal or linear-system games found only the standard linear-system-game undecidability results (Slofstra; Paddock–Slofstra; NPA papers), nothing on translation-invariant solution groups. The search is not exhaustive.

**Sharp next test.**
- **Exact condition.** A rule must have `J != 1` in `Gamma` and admit no nonzero finite-dimensional module of its local algebra with `J = -I` at any period lattice. This is the LCS analogue of quantum rigidity.
- **Needed extra.** A Følner/Ornstein–Weiss averaging step turning any R^U almost-model of `Gamma` into approximately periodic almost-modules. If that averaging works, "no approximate periodic modules" becomes the HS-robust criterion, a finite-dimensional inequality for the local algebra that can be tested one rule at a time.

**Verdict.** Unclear; survives as a new host family with a concrete checkable criterion.

## Summary

| # | Approach | Verdict |
|---|---|---|
| 1 | Marked limits of approximate group models | killed: forbidden-mass gap makes it circular |
| 2 | Quasirandom nonabelian packets | killed: duplicate of S3 packet route; atlas crux |
| 3 | Trace selection by verifier symmetries | killed: automorphism invariance gives no group algebra |
| 4 | Quantum tiling games `Sol ⋊ Z^2` | unclear: survives; periodic quantum tilings are the test |

Sources checked: repo nodes named above on origin/main; web search for
translation-invariant nonlocal games (results: arXiv:1606.02278,
arXiv:2111.14928, arXiv:2205.04645, arXiv:2510.04943 abstract listings).
