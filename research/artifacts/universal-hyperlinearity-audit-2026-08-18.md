# 2026-08-18 - External dossier: retarget from Q3.4 to universal hyperlinearity

Source: user-supplied external research session (LLM-assisted, unrefereed),
pasted 2026-08-18.  It is a follow-up to the dossier ingested the same day as
`hyperlinear-divergent-strategies-2026-08-18.md`, and argues that the target
should shift from "is every hyperlinear group sofic" to "is every group
hyperlinear", on the grounds that the new nonsofic groups make either answer
a landmark and that the unitary endpoint removes the classicalization step.

It claims no answer in either direction.  This file records the ingestion
audit; the content that survived it lives in the graph.

## Headline finding of the audit

**Most of the dossier's machinery is already in this repository, and its
central strategic conclusion is this repository's own recorded diagnosis.**
That is a good sign for the dossier and a bad sign for treating it as new
lanes.  Specifically:

| Dossier section | Already here |
| --- | --- |
| §1 quotient reformulation | `all_groups_isHyperlinear_iff_quotient_closed`, `exists_not_isHyperlinear_iff_exists_hyperlinear_quotient`, `exists_not_isHyperlinear_iff_exists_fg` in `GroupApproximation/Sofic/HyperlinearReduction.lean` -- **kernel-checked, and until today cited by no node** |
| §2 idempotent traces | the same theorem in trace language; `docs/FALSE_PROJECTIVE_UNITARY_GROUP_SHORTCUT.md` §5 |
| §3 power-to-Dirac | `docs/TRUE_RADICAL_DOMINATION_CONSTANTS.md` already uses conjugate-double tensor powers with `q_chi(g)=1-|chi(g)|^2`; formalized as `character-domination-collapse-equivalences` (`GroupApproximation/Domination/*.lean`); the finite-table half landed today as the peer node `balanced-replica-hs-amplification` |
| §5 IRS intersection | `docs/FALSE_RECENT_LITERATURE_AUDIT.md` §3, on Manzoor: "taking normal cores destroys the information in the currently available examples" -- the intersection powers *are* the normal core |
| §6 perfect-completeness game compilation | `docs/TRUE_NORMAL_TORIC_GAP_IMPLIES_NONHYPERLINEAR.md`: a **proved** conditional reduction, stronger than the dossier's ask (toric syntax suffices; full LCS is not logically necessary), plus the Taller--Vidick perfect-completeness note |
| §10 "the problem is trace selection" | `docs/FALSE_PROJECTIVE_UNITARY_GROUP_SHORTCUT.md` §5, the decisive trace mismatch between `delta_e` and `tau_M` |

The genuinely new items are §3's *identification of the limit* (see below) and
the strategic reading of §8 -- that an explicit nonsofic group is now a fork
machine, which only became true on 2026-08-01.

## Literature verified this session

- **arXiv:2502.06697**, Manzoor, *There Is An Equivalence Relation Whose von
  Neumann Algebra Is Not Connes Embeddable*, submitted 2025-02-10, v2
  2026-04-04.  Abstract confirms: defines hyperlinearity for an IRS, produces
  a **non co-hyperlinear IRS on any non-abelian free group**, and derives a
  relation whose von Neumann algebra is not Connes embeddable, by simplifying
  the Aldous--Lyons-to-nonlocal-games reduction and removing subgroup tests.
  **Checks out**, and the dossier reports it correctly, including that it does
  *not* produce a nonhyperlinear group.
- **arXiv:2310.07901**, Paddock--Slofstra, *Satisfiability problems and
  algebras of boolean constraint system games*, 2023-10-11, rev. 2025-01-15.
  Abstract confirms the closing sentence the dossier leans on: "the question
  of whether or not there is a non-hyperlinear group is linked to dichotomy
  theorems for `R^U`-satisfiability".  **Checks out.**

Not re-fetched, because no node below takes a theorem from them as a premise:
Watts--Helton--Klep 2111.14928 (used only for the *definition* of torically
determined, and re-derived in the repo doc), MIP\*=RE 2001.04383,
Taller--Vidick 2507.22444, Fournier-Facio 2608.02025.  The dossier's citation
of an OpenAI August 2026 "exponential parallel repetition theorem for general
two-player quantum games" was **not** verified and no node depends on it.

## Corrections to the dossier

1. **Its §4 hypothesis is equivalent to its conclusion, not weaker.**  The
   dossier asks for a non-CE trace `tau` and a finite-word witness `L` with
   `inf_k [L(|tau|^{2k}) - sup_{CE} L] > 0`, and presents this as a target to
   be manufactured by gap amplification.  Recorded here as
   `diracization-gap-equals-nonhyperlinear-group`: the hypothesis holds **iff**
   a nonhyperlinear group exists.  Forward is continuity of a finitely
   supported functional; backward take `tau = 1_N` for the answer group, whose
   powers are constant, and separate the point from the closed convex set of
   microstate characters by Hahn--Banach.  So no general amplification
   argument can supply it.  What survives is the pinned form: prove it for a
   *named* `tau`, where the trivial witness is unavailable.
2. **Two degeneracies kill the mechanism before the gap is even discussed.**
   If `K_tau = {e}` the limit is `delta_e`, embeddable over a free group; if
   `|tau|^2` is embeddable then so is every power and the limit, because the
   microstate characters are a **closed sub-semigroup** under pointwise
   product.  Recorded as `ce-characters-closed-multiplicative-semigroup`.  The
   dossier states the "non-CE can converge to CE" worry but not these, and
   they are what make the worry concrete: the map keeps only the scalar locus
   of `tau`.
3. **The IRS instance is a known dead end here, not a fresh lane.**  Its
   intersection powers converge to the normal core, and
   `docs/FALSE_RECENT_LITERATURE_AUDIT.md` §3 already records that taking
   normal cores destroys the information in the available examples.
4. **Non-CE of `L(R_mu)` is not the same as `tau_mu` being non-CE.**  The
   dossier slides between Manzoor's non-co-hyperlinear IRS and the group
   character `tau_mu(g)=Pr[g in H]` having no microstates.  A subalgebra of a
   non-embeddable algebra can be embeddable, and the GNS algebra of `tau_mu`
   is the algebra generated by the image of `Gamma` in the crossed product,
   not the whole relation algebra.  Whether Manzoor's notion is exactly
   `tau_mu notin CE` was **not** verified this session; no node assumes it.
5. **The "demotion" table is not adopted.**  The dossier proposes demoting
   de Finetti rounding, spherical designs, traffic moments and coherent
   configurations because the new target needs no permutations.  Those nodes
   landed in this graph *today*, in the peer lane from the previous dossier,
   and they target Q3.4.  Note that the goal flag moved the same day (user
   directive, commits 81adcf48 + 6ce43eca): the single goal is now
   `non-hyperlinear-group`, with `q3-4-resolved` keeping root status and all
   its wiring.  So the dossier's retargeting argument and the program's own
   flag now agree -- which is a reason to read the demotion table, not to
   execute it.  Nothing here was demoted, deleted or re-pointed; the peer
   lane's nodes stand as written.

## Mathematics re-derived here

- **Power-to-Dirac (its §3).**  Correct.  In the tracial GNS algebra
  `||u_g - tau(g)1||_2^2 = 1 - |tau(g)|^2`, so `|tau(g)|=1` iff `u_g` is
  scalar; the scalar preimage is normal; `t^k -> 1_{t=1}`.  The limit is the
  regular character of `Gamma/K_tau`.  Recorded as
  `character-diracization-limit`, together with the IRS corollary
  `tau_{mu^{∩k}} = tau_mu^k -> 1_{core(mu)}`.
- **Its §5 intersection identity.**  Correct: independence of `k` iid samples.
- **Its §7 normalized-HS dilution.**  Correct, and sharpened.  The dossier
  says a topological defect must be extensive to survive normalization; the
  repository already has the matching no-go for the raw index
  (`additive-index-instability`).  The observation that closes the loop is
  that `index/dim` is *unchanged* by `phi |-> phi ⊗ I_k`, so the no-go reaches
  every normalization except the density.  Recorded as
  `index-density-is-amplification-stable`, with the construction target as
  `extensive-cosystolic-index-defect`.
- **Its §1 and §9.**  Correct, and already formalized; §9's
  "Positivstellensatz" framing is the dual of
  `character-domination-collapse-equivalences`, which states the equivalence
  with a single linear domination constant and is machine-checked.  No new
  node: adding one would restate an established Lean interface.

## Recorded in the graph

Claims: `hyperlinear-quotient-permanence-equivalence`,
`ce-characters-closed-multiplicative-semigroup`,
`character-diracization-limit`, `diracization-gap-equals-nonhyperlinear-group`,
`phase-safe-toric-gap-implies-nonhyperlinear`,
`phase-safe-toric-gap-game-exists`, `binary-leavitt-unit-group-hyperlinear`,
`index-density-is-amplification-stable`, `extensive-cosystolic-index-defect`.

Routes: the six `-proof` companions, plus
`nonhyperlinear-from-phase-safe-toric-gap` and
`nonhyperlinear-from-extensive-index-defect` into the goal
`non-hyperlinear-group`, and `hyperlinear-nonsofic-from-leavitt-unit-group`
into the root `hyperlinear-nonsofic-group`.  The fixpoint's own report on this
change: six claims newly established, and each of the three new routes
"missing only" its single open prerequisite.  No root or goal moved status.

Deliberately **not** recorded: a route from the Diracization hypothesis into
`non-hyperlinear-group` (it would be a restatement dressed as a reduction, per
correction 1), a separate Manzoor/IRS lane (correction 3), and any change to
goal or root marking.
