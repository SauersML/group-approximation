# Lane `sp-evenside-n` — the `F₂` Step D bridge at general rank `n`

Programme note: `notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.4 (the uniform theorem) and
§1.1 (the generic objects).  Clone: `rank-four` (cores 24-29).

Owns `GroupApproximation/CharClass/LIXStepDGen*.lean` and nothing else.  Does not edit
`ParityEven.lean`, `ParityInstance.lean`, `SqDataInstance.lean`, `LemmaTwoStepD.lean`,
`LIXShapeGeneric.lean`, or anything of `sp-evenside`'s `ParityP*`.

**Deliverable**: the mod-2 Step D at the real objects, generic in the rank `n` (with `n`
even, the hypothesis Step D consumes at `p = 2`), with the `n = 2` instance bridging to the
landed rank-two declarations rather than replacing them.

---

## PLAN (authored 2026-09-10 ~14:45, before the first probe)

Three numbers in the rank-two even side are the rank in disguise:

| rank two | rank `n` | what it is |
|---|---|---|
| `σ₅ : Hmod2 S₅ 5` | `σodd : Hmod2 Sodd (2 * n + 1)` | the dimension of the odd sphere |
| `2 * k < j + 6` | `2 * k < j + (2 * n + 2)` | the degree of `z = t x` |
| `γ ((∑ⱼ dⱼ) + 3)` | `γ ((∑ⱼ dⱼ) + (n + 1))` | the `𝟏^{n+1}` block of `V` |

Everything else on the even side is **already rank-free** and is reused, not copied:
`ParityData` and its convolution proof (`sum_a_mul_b_eq_zero`, `b_odd_eq_zero`),
`Wu.tClass`, `Wu.sq_pull_sphere_eq_zero` and `Wu.mul_self_pull_sphere_eq_zero` (both
generic in the sphere's dimension already), `Wu.CartanTotal`, `Wu.HasSplitting`,
`sliceClass` and its coefficient lemmas, and `ne_zero_of_degree_ne_zero` (the degree
bridge, which mentions no degree beyond the one it is applied at).

Two hypotheses appear at rank `n` that have no rank-two counterpart, and both are the
programme's standing assumptions:

* **`Even n`** — the `p = 2` case of `p ∣ n`.  It is used exactly once, to make
  `r = m + (n + 1)` odd when `m = ∑ⱼ dⱼ` is even, which is what lets `b_odd_eq_zero` kill
  the `z`-component of `γ_r`.
* **`2 ≤ n`** — used exactly once, to turn the rank-`n` instability hypothesis
  (`2 * k < j + (2 * n + 2)`) into `ParityData`'s field (`2 * k < j + 6`), which it implies
  because `6 ≤ 2 * n + 2`.  This is the only place the rank-two shape of `ParityEven.lean`
  shows through, and it is why the landed convolution proof can be reused verbatim instead
  of duplicated at rank `n`.

Files:

* `CharClass/LIXStepDGenParity.lean` — the even side over `TotalH`, generic in `n`:
  `Gen.gamma_top_rank_eq_zero(_of_slice)` (the abstract conclusion at the rank-`n` index),
  `Gen.sphereClass` (the pullback of a sphere generator in **any** degree — the rank-two
  `Wu.xClass` pins degree five in its type, which is the only reason it cannot be reused),
  `Gen.sq_b_of_grading` and `Gen.tx_inj_of_degreewise` (the instability and Künneth helpers
  with `2n + 2` in place of `6`), `Gen.parityData_of`, and the two endpoints
  `Gen.gamma_top_eq_zero_of_slice_totalH` / `Gen.gamma_top_eq_zero_of_hasSplitting`.
* `CharClass/LIXStepDGenData.lean` — the real objects over `sp-tower`'s shape layer:
  `Gen.WuStepDData n`, `Gen.WuStepDData.gamma_top_eq_zero`, and **`Gen.stepD_of_wu`**, the
  Step D half of `LemmaTwoInput` at rank `n` over `Gen.baseM n dd`, `Gen.VIdx n dd`,
  `Gen.Vmat n`; plus `Gen.stepD_of_wu_stage`, the same at the dimensions the tower actually
  carries (`LIX.Gen.lixDD n j`, i.e. `d_i = n·2^i`), where the single hypothesis `Even n`
  discharges the evenness at **every** stage through `LIX.Gen.even_lixDD`.  That is the
  uniformity the limit needs: one theorem quantified over the stage, not a family proved
  stage by stage.  Note `Gen.stepD_of_wu` itself is stated for an arbitrary `dd`, so the
  stage version is a corollary, not a separate argument.
* `CharClass/LIXStepDGenAxiomCheck.lean` — a leaf, the axiom gate on all eighteen
  endpoint-facing declarations.  Named explicitly on every probe (a closure gate is blind
  to a leaf).  It uses the repository's `#audit_axioms` (`Meta/AxiomGuard.lean`), not
  `#print axioms`: that command prints the same report and then **throws** if the closure
  leaves `[propext, Classical.choice, Quot.sound]`, so a green build of the module *is* the
  certificate and the known "axiom lists wrap across lines" trap cannot make a log grep
  under-report.  The fleet rule still applies: a replayed line is not evidence, so the log
  cited must show `Built` for this module.

**The `n = 2` bridges are kernel-checked, not asserted.**  Three declarations exist only to
make the subsumption a build error if it ever stops holding:

* `Gen.gamma_top_eq_zero_of_hasSplitting_two` — the statement of
  `Wu.gamma_top_eq_zero_of_hasSplitting` **verbatim**, proved by
  `Gen.gamma_top_eq_zero_of_hasSplitting 2 even_two le_rfl`;
* `Gen.ofRankTwo` / `Gen.toRankTwo` — the rank-two `WuStepDData` and `Gen.WuStepDData 2`
  convert field by field with no proof obligation (`5` **is** `2 * 2 + 1`, `6` **is**
  `2 * 2 + 2`);
* `stepD_of_wu_of_gen` — the statement of `LemmaTwoStepD.stepD_of_wu` verbatim, proved by
  `Gen.stepD_of_wu 2 …`.  This is the one that also exercises `sp-tower`'s `rfl` bridges
  (`baseM dd ≡ Gen.baseM 2 dd`, `Vmat ≡ Gen.Vmat 2`, `VIdx dd ≡ Gen.VIdx 2 dd`) inside a
  quantified hypothesis rather than in isolation.

Nothing consumes the three bridge declarations; they are gates.

## GREEN (with job counts)

**The definitive log**: clone `rank-four`, `.lake/laneprobe-20260910-154302.log`, **PROBE
GREEN at 8815 jobs**, empty error index, `purged 7 stale artifact sets` under the lead's
transitive `purge_stale.py`.  My own artifacts were deleted in the clone before this probe
(there were none: the first probe never reached my modules), so every module I claim has a
`Built` line in this one log.

| module | line | time |
|---|---|---|
| `CharClass.LIXStepDGenParity` | `✔ [8813/8815] Built` | 308s |
| `CharClass.LIXStepDGenData` | `✔ [8814/8815] Built` | 293s |
| `CharClass.LIXStepDGenAxiomCheck` | `ℹ [8815/8815] Built` | 237s |

No `Replayed` line on any of the three, no `sorry`, no error anywhere in the log.  The
three files in the shared tree and the three the clone built are **byte-identical**
(`md5`: `42758eff985ab1710c50ad8ff99e7ac7`, `1068c5e00b160ec191466d1518480877`,
`d82a00e9e0acb5831c4d6e17cbcdd2d2`), checked after the probe, so the green is about the
sources the lead would land and not about a version that has since moved.

**Axioms.**  All **18** endpoint-facing declarations report exactly
`[propext, Classical.choice, Quot.sound]`.  That is not a log-reading claim: the gate is
`#audit_axioms`, which throws, so the `Built` line on `LIXStepDGenAxiomCheck` is itself the
certificate.  Six of the eighteen lines wrap across three lines in the log — the known
multi-line axiom trap — which is exactly why the gating command was used instead of
`#print axioms`.

What the green covers, in the order that matters:

* `Gen.stepD_of_wu` — **the deliverable**: Step D at the real objects at rank `n`, over
  `Gen.baseM n dd` / `Gen.VIdx n dd` / `Gen.Vmat n`, concluding
  `γ_{(∑ⱼ dⱼ)+n+1}(W_g) = 0` for every unitary Step A can produce.
* `Gen.stepD_of_wu_stage` — the same at `LIX.Gen.lixDD n j`, every stage, one `Even n`.
* `stepD_of_wu_of_gen` — the landed rank-two `stepD_of_wu`, **statement for statement**,
  proved by `Gen.stepD_of_wu 2 even_two le_rfl`.  This is the bridge that had the only real
  risk in it: it makes the elaborator use `sp-tower`'s `rfl` bridges
  (`baseM dd ≡ Gen.baseM 2 dd`, `VIdx dd ≡ Gen.VIdx 2 dd`, `Vmat ≡ Gen.Vmat 2`) *inside a
  quantified hypothesis over `G`*, and it went through with no `show`, no cast and no
  rewrite.
* `Gen.gamma_top_eq_zero_of_hasSplitting_two` — likewise for
  `Wu.gamma_top_eq_zero_of_hasSplitting`.

## AUTHORED, UNVERIFIED

Nothing.  Every file this lane owns is in the green probe above with a `Built` line.

## NEEDS

* Nothing from another lane to finish this deliverable.  `sp-tower`'s
  `CharClass/LIXShapeGeneric.lean` is already landed and is imported.
* Downstream, the fields of `Gen.WuStepDData n` are owed by the same owners as at rank two:
  `tx_inj` and `gamma_eq` by the Künneth layer, `sq_b` through `Gen.sq_b_of_grading`,
  `split` by `cc-projective`, `slice` by `cc-projective`.  Each is now stated at the
  rank-`n` degree, so nobody has to guess what `6` meant.

### What is NOT in this deliverable, and what it would take (for the lead)

At rank two, `stepD_of_wu` is not the end of the even side: three further layers sit above
it, and none of them is generalised here.

1. **`WuStepDLix` (`LemmaTwoStepDLix.lean`)** — Step D restated at the *geometric* space
   `lixN dd = ↥sphereOne × baseM dd` instead of an abstract `N` with three projections.
   It runs through `Wu.lixIso : lixN dd ≅ KnTwo.NTop (baseY dd)` and
   `ParityEvenTransport.lean`.  Note the rank-two seam here was the "green about different
   spaces" bug (`ParityEvenTransport.lean`'s docstring); at rank `n` the same trap is open.

   **The sphere half of it is already done, by two different lanes, and I did not know that
   when I wrote the hypothesis.**  My `hSodd : HasSphereCohomology Sodd (2 * n + 1)` is
   discharged for the model's own sphere by `Gysin.hasSphereCohomology_unitVectors`
   (`CharClass/GysinSphere.lean`), which is generic in the rank already:
   `HasSphereCohomology (TopCat.of ↥(unitVectors (Fin (d + 1)))) (2 * d + 1)`.  And
   `sp-oddside`'s `KGen.unitVectorsHomeo n` (`CharClass/LIXKGenSphere.lean`) is a
   **homeomorphism** `unitVectors (Fin (n+1)) ≃ₜ Sphere (2n+1)`, stronger than the homotopy
   equivalence `Gysin` uses.  So whoever builds the rank-`n` transport has both models and
   the comparison between them; nothing about the sphere is owed.

   I deliberately did **not** wire a pinned-sphere corollary into my files: the wiring
   belongs to the transport layer, `sp-oddside` is actively building `KGen`, and a
   half-layer from me would be the thing the transport lane then has to reconcile.
2. **`WuStepDPinned` / `WuStepDSlice` (`LemmaTwoStepDPinned.lean`)** — the Chern splitting
   pinned to `lixChernSplit`.  Rank-`n` needs `cc-projective`'s splitting at rank `n`.
3. **`LemmaTwoInput` / `lemmaTwoHolds_of` (`LemmaTwoGlue.lean`)** — the two steps about one
   class.  The rank-`n` form would pair `Gen.stepD_of_wu` with `sp-oddside`'s Step C at
   rank `n` and land in `LIX.Gen.LemmaTwoHolds n` (`sp-tower`'s seam, already stated).  It
   is glue, not Step D, and I have not written it: `LemmaTwoGlue.lean` is not mine and the
   rank-`n` Step C does not exist yet.  When both sides are green, the glue is the same
   three lines as at rank two.

So: the even side is generic in the rank as of this lane; the *wiring* of it to the
geometric model is not, and item 1 is the next thing anyone should ask for.

## The lead's ruling of 2026-09-10, and what the green actually does

The lead ruled: *"the abstract half of your deliverable is the p = 2 instance of
`sp-evenside`'s uniform theorem — INSTANTIATE it, do not re-derive it; your work is the
bridge at rank n."*  Both halves of that are satisfied, and the second literally, but the
first is worth being exact about because I did not import `ParityPData`.

**Nothing is re-derived.**  `Gen.gamma_top_rank_eq_zero` is four lines and contains no
induction, no convolution and no argument: it applies the **landed**
`ParityData.b_odd_eq_zero` at the index `m + (n + 1)`, having observed that the index is odd
because `m` and `n` are both even.  There is no second copy of the uniform theorem anywhere
in this lane's files, and the only mathematical content that is mine is the observation that
`Even n` is what makes the rank odd — which is the hypothesis the lead asked me to state.

**Why not the import.**  Going through `ParityPTwo.toParityPData` instead would add a
dependency without adding a theorem, and it would tie a green `F₂` artifact to a structure
that is moving twice this week: `ParityPData` is scheduled to lose `[CommRing H]` for
`[Ring H]` plus `z_comm` when `sp-cupone` lands, **and** to be restated for the index
orientation below.  `sp-evenside`, who owns it, endorsed this explicitly ("A green F₂
artifact should not track that... I would leave it until my structure has stopped moving"),
and `sp-design`'s scope correction struck their own earlier instantiate instruction on the
ground that the `p = 2` instance already exists, so there is no abstract work left to do.

**The swap remains one line** inside `LIXStepDGenParity.lean` §4, because neither of my
files mentions `ParityData` or `ParityPData` in any *statement*.  If the lead wants the
import now, say so: it is one edit and a warm re-probe.

### The index orientation, which turned out to be a real defect

Warning `sp-evenside` about the argument order found a live bug on their side, not a
hypothetical one.  `ParityPData.gamma_rank_eq_zero` concludes `γ (n + 1 + m) = 0` and
`ParityPTwo.gamma_top_eq_zero'` concludes `γ (2 + 1 + m) = 0`, while the landed
`ParityData.gamma_top_eq_zero` concludes `γ (m + 3) = 0`.  `Nat.add` recurses on its second
argument, so `m + 3` reduces to `succ (succ (succ m))` while `3 + m` is stuck for a variable
`m`: propositionally equal, definitionally not.  So `ParityPTwo` never produces the landed
*form*, and their calibration claim was weaker than stated.  Nothing in either lane's probes
could have surfaced it — both files are green — because the mismatch only appears at the
first consumer, which is this lane.  `sp-evenside` has corrected their report and queued the
restatement (`γ (m + (n + 1))`) into the landing batch the lead is holding.

`sp-tower` arrived at the same convention independently and has written the reason into
`CharClass/LIXShapeGenericRank.lean`'s docstring, so it should now survive a later
"simplification".

### Two things adjacent to the deliverable that I did **not** do

* **`Gen.lixRank`.**  `sp-tower` has authored `CharClass/LIXShapeGenericRank.lean` with
  `Gen.lixRank n dd := (∑ j, dd j) + (n + 1)` — *literally* my conclusion index, so
  `Gen.stepD_of_wu` already proves `γfun … (Gen.lixRank n dd) = 0` by `rfl` and a citation
  lemma is a one-liner.  I have not added it and have not imported that file: it is authored
  but **not yet probed** (their clone is behind a two-hour gate), and importing an unprobed
  peer module into a green artifact trades a certificate for a convenience.  Worth doing the
  moment they post its `Built` line.
* **`trace_Vmat`, `lixRank`, `lixTopDegree`** — the three declarations shared with
  `sp-oddside-n`.  The lead ruled them `sp-tower`'s; I never authored any of them, and a
  grep of my three files confirms none of the names appears in them.

### The unit leading coefficient (`sp-design`'s correction) does not reach this lane

At `p = 2` the Wu coefficient is invisible, and my structure has no field for it: the
diagonal relation does not appear in `Gen.WuStepDData` at all — the field is
`split : Wu.HasSplitting N γ`, which *subsumes* it, exactly as at rank two.  So if the
abstract half is later swapped to `ParityPData`, the unit `c` travels inside their structure
and my interface does not move.

### Weakening `2 ≤ n`, if anyone ever wants to

`sp-evenside` points out the route.  Their structure asks for instability only at the single
index it consumes (`pR_b_succ : ∀ i, PR i (b (i+1)) = 0`), and their
`pR_b_succ_of_instability` derives that from the general form as soon as the weight of `z` is
at least two, i.e. `n ≥ 1`.  Mine needs `2 ≤ n` only because `ParityData`'s field is stated
at the *threshold* (`2 * k < j + 6`) rather than at the instance.  Ask for the instance, not
the threshold, and the hypothesis drops to `1 ≤ n`.  Not worth doing while the programme
assumes `2 ≤ n` throughout.

## Relation to `sp-evenside` (coordinated by message, 2026-09-10)

`CharClass/ParityPData.lean` already proves the same conclusion generic in `p` **and** in
the rank (`ParityPData.gamma_rank_eq_zero`: `p ∣ n → p ∣ m → γ_{n+1+m} = 0`), and
`ParityPTwo.lean` exhibits a `ParityData` as a `ParityPData 2`.  So
`Gen.gamma_top_rank_eq_zero` is `P.toParityPData.gamma_rank_eq_zero` up to `add_comm` on
the index, and the mod-`p` even side can replace the `F₂` one **without touching anything
downstream**: no statement in either of this lane's files mentions `ParityData` or
`ParityPData`, so the swap is internal to `LIXStepDGenParity.lean` §4.

Two deliberate choices at the seam:

* the index is written `m + (n + 1)`, not `n + 1 + m`, because `m + (2 + 1)` is
  **definitionally** the landed `m + 3` while `2 + 1 + m` is not (`Nat.add` recurses on the
  second argument);
* this lane keeps the `F₂` route for now so that the rank-generic bridge does not depend on
  a lane still in flight (`ParityPData` is scheduled to lose `CommRing H` for `[Ring H]`
  plus `z_comm` once `sp-cupone` lands).

## TRAPS

* **The first probe died on a foreign file, at job 8777 of 8814, after 55 minutes.**
  `CharClass/ProjectiveSpaceCohomology.lean:214:47: unexpected token 'namespace'; expected
  'lemma'` — a **syntax** error, i.e. `sp-coeff`'s coefficient generalisation caught
  mid-edit by my rsync.  The owner had it well-formed by the time I re-probed and it built
  in 71s.  Two things worth knowing from it: the shared-tree hazard is not only "a peer's
  file is red", it is "a peer's file is *half-written*", and that costs the whole probe
  because the purge and the rebuild run first; and the error index makes it instantly
  distinguishable from your own work — one error, in a file you do not own, at a line you
  never touched.  Losing that probe was not wasted, though: it left the closure warm, so
  the citable probe took minutes rather than an hour.
* **The transitive purge's first run is the expensive one.**  On this cold clone it deleted
  `2885 of 4774` artifact sets (`source-newer=145, import-newer=2740`) and the scan alone
  took about ten minutes with no output; the second probe purged `7`.  A log that sits at
  zero bytes for ten minutes is the purge, not a hang — check for the `purge_stale.py`
  process before concluding anything.
* **`#audit_axioms`, not `#print axioms`.**  The repository has a gating command
  (`Meta/AxiomGuard.lean`) that prints the same report and then throws when the closure
  leaves the classical three.  A `#print axioms` module logs a verdict nobody has to read,
  and the axiom lists wrap across lines, so a line-oriented grep of them under-reports.
  Appended to `FLEET_TRAPS.md`.
* **Precaution, not a confirmed trap.**  I first wrote the rank-two bridges as
  `def Gen.ofRankTwo … (D : WuStepDData …)` *outside* `namespace Gen`, then moved them
  inside it and spelled the rank-two record
  `_root_.GroupApproximation.CharClass.WuStepDData`.  Reason: a declaration named
  `Gen.foo` elaborates with `Gen` pushed onto the current namespace, so the short name
  `WuStepDData` in its own signature would resolve to `Gen.WuStepDData` — the very name the
  bridge is supposed to be distinguishing itself from.  A bridge that silently resolves to
  the wrong one of two same-short-named declarations proves nothing, and this is a live
  hazard for every lane that mirrors a rank-two name into `Gen`.  I did not probe the
  broken spelling, so I am not claiming it as a trap; I am claiming that the ambiguity is
  not worth carrying.
