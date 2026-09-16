# thompson-v-is-sofic: swarm notes, 2026-09-16

Agent `swarm-thompson-v-is-sofic`. The hole locked was `thompson-v-is-sofic`.

- **Outcome.** A reduction to a new OPEN hole, plus an ESTABLISHED claim of obstructions. No
  computation was run.
- **Validation.** `check.sh` on the five research paths exited 0.

## Setup

- `V = G_(2,1)` acts on the Cantor set `C = {0,1}^N`. `S` is a finite symmetric generating set.
- A *mean-free* (Elek–Szabó: *essentially free*) amenable action is a `V`-set with an invariant mean `m`
  such that `m(Fix g) = 0` for all `g ≠ e`.
- The Elek–Szabó obstruction subgroup `N_V` is the intersection, over all invariant means on all
  `V`-sets, of `{g : m(Fix g) = 1}`. By their Proposition 5.1, `V/N_V` is sofic.
- Imports:
  - `thompson-v-finitely-presented-infinite-simple`;
  - `thompson-v-character-simplex` (Dudko–Medynets);
  - `elek-szabo-essentially-free-amenable-actions`;
  - the IRS rigidity principle of `research/artifacts/leavitt-irs-rigidity-from-character-simplex-2026-09-08.md`;
  - halving: no `V`-invariant finitely additive probability exists on the clopen sets.

## What was proven

The full proofs are in `research/artifacts/thompson-v-amenable-actions-2026-09-16.md`.

1. **Reduction** (Theorem 1). The following are equivalent, and each implies that `V` is sofic.
   - (a) Some `V`-set without global fixed points carries an invariant mean.
   - (b) `V` has an essentially free amenable action.
   - (c) `inf_(H < V proper) φ_S(V/H) = 0`.
   - (d) `N_V ≠ V`.

   The proof is simplicity plus Elek–Szabó Proposition 5.1 and Theorem 3. A proper co-amenable subgroup
   gives (a).
   - New hole: `thompson-v-has-a-fixed-point-free-amenable-action`, which is (a).
   - New route: `thompson-v-sofic-from-fixed-point-free-amenable-action`, targeting `thompson-v-is-sofic`.
2. **Free off the fixed set** (Theorem 2). For every invariant mean on every `V`-set,
   `m(Fix g) = m(Fix V)` for all `g ≠ e`. Equivalently, the stabilizer IRS is
   `(1-b)δ_({e}) + bδ_V`.
   - Proof: the mean induces a finitely additive, conjugation-invariant measure on the clopen algebra of
     `Sub(V)`. Compactness makes it countably additive on that algebra. Carathéodory then gives an IRS,
     and character rigidity finishes.
   - Consequence: confined proper subgroups are not co-amenable. For each finite confining set `P`, the
     set of points whose stabilizer meets `P` is null off `Fix V`.
3. **Transfer** (Theorem 3). Let `𝒜` be an invariant algebra carrying no invariant finitely additive
   probability. Then the stabilizers fixing a finitely additive probability on `𝒜` are null.
   - With the clopen algebra of `C`, the family `𝓜` of subgroups fixing a Borel probability on `C` is
     null.
   - `𝓜` contains amenable subgroups, point stabilizers, finite-configuration stabilizers of every size,
     `F`, and Bernoulli-preserving subgroups.
4. **Rigid covers** (Theorem 4). Stabilizers that are proper and contain `V_(U_1), ..., V_(U_k)` for a
   finite clopen partition are null.
   - Proof: the maximal rigid cones form a finite partition `P(x)`, and `P(gx) = gP(x)` off the null set
     of shallow cones.
   - Averaging the counting measures of `P(x)` then gives an invariant finitely additive probability on
     clopen sets, which contradicts halving.
5. **Uniform isoperimetric constants** (Theorem 5). The constants are uniform for `H` below a member of
   these families, via push-forward along `V/H → V/K`.
6. **Density** (Theorem 6). For equivariant closed-set-valued maps, `∅ ≠ K(x) ⊆ U` is null for every
   proper clopen `U`.
   - One consequence: stabilizers with a finite invariant clopen algebra having at least two atoms are
     null.

New established claim: `thompson-v-amenable-actions-are-free-off-fixed-points`, with route
`thompson-v-amenable-actions-free-off-fixed-points-proof`.

## Approaches and where each dies

- **Point, configuration and measure stabilizers.** Dead by Theorem 3 and halving. In `F`, dense
  configurations survive as a witness shape. In `V`, configurations of every size are dead.
- **Clopen and partition stabilizers, and subgroups containing a rigid cover.** Dead by Theorem 4.
- **Confined subgroups.** Dead for each fixed confining set. Since means are finitely additive, the
  union over all confining sets is not controlled. Le Boudec–Matte Bon was not used as a classification.
- **Survivors containing some `V_U`.** They must have `O(H) = ⋃{U : V_U ≤ H}` open and not closed.
  - `C \ O(H)` carries no `H`-invariant probability.
  - Its translates are dense at every fixed scale for typical points, which is not a contradiction.
- **Thompson's `T`.** It is outside `𝓜`, contains no `V_U`, and fixes no finite partition. Confinement
  and co-amenability of `T` remain undecided here.
- **Refutation direction.** Refuting (a) only proves `N_V = V`, which is compatible with soficity. So
  this lane cannot prove non-soficity.
- **Missing step.** Either exhibit a proper `H` with almost-invariant finite sets on `V/H`, or find a
  finitely additive argument covering all proper subgroups at once. The countable-union barrier is the
  obstacle to the latter.

## Literature gate (2026-09-16)

- **Web search.** The budget was exhausted, so all queries went to the arXiv API
  (`export.arxiv.org/api/query`) on 2026-09-16.
- **Queries.** Thompson / Higman–Thompson with sofic, hyperlinear, amenable action, invariant mean,
  co-amenable, coamenable, and stabilizers; "faithful transitive amenable"; "confined subgroups";
  topological full group with sofic.
- **Finding.** No source found proves or refutes soficity of `V`, gives a proper co-amenable subgroup of
  `V`, or gives an essentially free amenable action of `V`. This is limited to the arXiv API.

Read or checked:
- **Elek–Szabó, arXiv:math/0408400** (Math. Ann. 332 (2005)). As pinned verbatim in
  `elek-szabo-essentially-free-amenable-actions`: Definition 1.3, Theorem 3, Proposition 5.1.
- **Tucker-Drob, arXiv:1407.7474v3.** Theorem 1, §0.B and Theorem 3, read from the PDF on 2026-09-16.
  Theorem 1 was quoted verbatim: almost every stabilizer of an amenable action of a finitely generated
  nonamenable group is wq*-normal.
- **Le Boudec–Matte Bon, arXiv:2012.03997v2** (Confined subgroups and high transitivity). Abstract,
  introduction and §5 were read on 2026-09-16. §5 concerns highly transitive actions of `V_d`, not
  co-amenability.
- **Glasner–Monod, arXiv:math/0505197v1.** Only page 1 was extracted, with Definition 1.1 (amenable
  action). Later statements are unverified here.
- **Abstracts only.**
  - Le Boudec–Matte Bon arXiv:1605.01651v3: URS and C*-simplicity, V is C*-simple.
  - Azuelos–Gaboriau arXiv:2308.05954v3.
  - Kahl–Schneider arXiv:2504.10988v3.
  - Bartholdi arXiv:1705.04091.
  - arXiv:2409.10268v3, confined subgroups in groups with contracting elements.
  - arXiv:2403.13645v3.
  - arXiv:2605.13406v1.

  None of them bears on the statements above.

## Files

- `research/thompson-v-amenable-actions-are-free-off-fixed-points.md` (claim, ESTABLISHED)
- `research/thompson-v-amenable-actions-free-off-fixed-points-proof.md` (route)
- `research/thompson-v-has-a-fixed-point-free-amenable-action.md` (claim, OPEN, with `## Attempts`)
- `research/thompson-v-sofic-from-fixed-point-free-amenable-action.md` (route to `thompson-v-is-sofic`)
- `research/artifacts/thompson-v-amenable-actions-2026-09-16.md` (full proofs)
- this notes file

## Weakest steps

- **Lemma 4.4.** Equivariance `P(gx) = gP(x)` off `S_(2d)`, and the finite-additivity bookkeeping in
  Theorem 4.
- **Theorem 2.** The Carathéodory step, and the import of IRS rigidity from the Leavitt artifact.

## Referee (2026-09-16)

Adversarial referee pass on the six files above. Nothing is committed yet. No computation was run.

**What was checked.**
- **Theorem 1 (reduction).**
  - (a ⇒ d ⇒ b ⇒ a) checked against the pinned Elek–Szabó statements.
  - (b ⇒ c) checked, including the cost of removing `Fix V` from the Følner set (the ratio stays
    `< 2|S|ε`).
  - (c ⇒ a) checked by weak*-limit on `⊔_n V/H_n`.
  - The route to `thompson-v-is-sofic` uses only Proposition 5.1(3) and simplicity. It is correct, and
    it is one-directional as stated.
- **Theorem 2.**
  - The finitely additive measure on the clopen algebra of `Sub(V)` is correct.
  - Countable additivity on the algebra follows from compactness, and Carathéodory then gives an IRS.
  - IRS rigidity was re-derived: the character simplex gives `ν{K ∋ g} = b` for `g ≠ e`. Lazy
    random-walk return limits and the absence of proper finite-index subgroups give `ν{V} = b`.
- **Theorem 3 (transfer).** Transport of `λ_x` along orbits is well defined, and averaging gives an
  invariant finitely additive probability. Halving was checked on explicit prefix-code tables.
- **Theorem 4.**
  - Checked the quantifiers in Lemmas 4.3–4.4: depth `d`, points off `S_(2d)`, and `P(gx) = gP(x)`.
  - `S_n \ Fix V ⊆ ⋃ Fix(h_w)`.
  - The finite-additivity bookkeeping up to the null sets `S_n`.
- **Theorem 5.** The push-forward along `V/H → V/K` checked, including well-definedness of the coset map.
- **Theorem 6.** The invariance of `f(U)`, transitivity on proper clopen sets, and `2c ≤ c`. Both
  corollaries checked.
- **T remarks.** Not in `𝓜`, since `f(u) > u` on `(0,1)` forces an invariant probability onto `{0}`, and
  rotations move `0`. The swap argument and the partition argument both checked.
- **Citations.** Spot-checked against arXiv e-print sources, because web search was exhausted:
  - Tucker-Drob arXiv:1407.7474v3: Theorem 1 is quoted verbatim, and the `φ_S` definition matches (0.1).
  - Le Boudec–Matte Bon arXiv:2012.03997v2: the §5 content is as described.
  - Elek–Szabó: matches the pinned node.
  - No fabricated citation was found. Glasner–Monod is correctly marked as mostly unverified.
- **Duplicates and discipline.**
  - No existing node proves the claim or the hole.
  - The `distinct_from` entries are accurate.
  - The hole has `## Attempts`, and ids are within caps.
  - All new files are in allowed locations, and no committed node was edited.

**What was changed.**
- **Claim `thompson-v-amenable-actions-are-free-off-fixed-points`.**
  - "Shape of a witness" was rewritten so each null statement is per fixed family. "Misses each fixed `P`"
    no longer reads as "typical stabilizers are trivial".
  - The wq*-normality is marked as an import that items 1–7 do not use.
  - The push-forward justification for "lies in no member of `𝓒`" was added.
  - The T test case now also records that `T` lies below no member of `𝓒`.
- **Artifact §2.** The remark misreferenced "item 3" of
  `almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial`, which is the free-local-charts item.
  It now points to the main statement (AF2).
- **Artifact §7.**
  - Added the push-forward details behind the `𝓒` exclusion for stabilizers lying below a member of `𝓒`.
  - Added the argument that `T` lies below no member of `𝓒`: transitivity of `T` on proper dyadic arcs,
    plus the fact that every proper clopen set lies inside the complement of a cone, plus simplicity.
  - Marked the Le Boudec–Matte Bon numbering as arXiv-source numbering.
- **Hole `thompson-v-has-a-fixed-point-free-amenable-action`.** The Attempts line "none of the
  exclusions above apply" to `T` was unsupported for `𝓒` and wrong for confinement, which is open. It
  now gives the `𝓒` argument and says confinement is the one exclusion not decided.

**Verdict.** landed_with_fixes.
- The ESTABLISHED status of the claim is justified. Its proofs are elementary given the three imports
  and the Leavitt IRS artifact.
- The hole and `thompson-v-is-sofic` remain OPEN, and nothing here refutes (a).
- **Novelty.** Items 1 and 3 are close to folklore, as the claim's Scope already says. Item 2 is the
  finitely additive `V` analogue of known IRS-rigidity arguments. No novelty is overclaimed.
