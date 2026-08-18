# Probing the true criterion: design, cost model, and the first exact numbers

Date: 2026-08-15 (night).  Working notes, not canonical.

This is the design for the first probe of the **actual** §9 criterion — the
one-unitary optimization at the regular representation.  Every prior probe in
the repo optimized a 15-point or 64-dimensional chart truncation, which is a
different problem; the criterion's factor restrictions are `λ ⊗ I_k` on the
nose, and nothing has ever been run there.

It also reports the first exact objective values, which turned out to be
available in closed form.

---

## (a) The objective

For `U ∈ U(20160k)` define the exact representation

```
π(h) = λ(h) ⊗ I_k            (h ∈ K₁)
π(h) = U (λ(h) ⊗ I_k) U*     (h ∈ K₂)
```

and, over the relator list `T_St` (`|T_St| = 4,636` in the emitted JSON, plus
the 12 reverse-dictionary relators),

```
F_max(U) = max_{s ∈ T_St} ‖π(s) − I‖₂ ,     F_rms(U)² = mean_s ‖π(s) − I‖₂² .
```

**Reduction to traces.**  Every `π(s)` is unitary, so

```
‖π(s) − I‖₂² = 2 − 2 Re tr_d(π(s)) .
```

The objective therefore needs only normalized traces — no full matrices.  That
is the first thing that makes the problem approachable at all, and it is worth
stating because the natural implementation (form `π(s)`, subtract `I`, take a
norm) is hopeless at `d = 20160`.

**Do not use a trace estimator.**  Hutchinson's `tr(A) ≈ (d/m) Σ v_j* A v_j`
has variance that does **not** vanish as `A → I`, which is exactly the regime
the criterion cares about; resolving a defect of `0.01` would need `m ~ 10⁴`
probes.  Use the residual estimator instead:

```
E_V ‖(π(s) − I) V‖_F² / m  =  ‖π(s) − I‖_F²  =  d · ‖π(s) − I‖₂²
```

for `V` a `d × m` block with `E[VV*] = I`.  Its variance vanishes as
`π(s) → I` — at the optimum every probe returns exactly zero — so it is
well conditioned precisely where the trace estimator is worst.  This is the
single most important implementation choice in the design.

---

## (b) Computational structure, with measured numbers

`λ(g)` is a **permutation** matrix (regular representation), so `λ(g) ⊗ I_k`
permutes the `d = 20160k` basis vectors in blocks — an `O(d)` gather, no
arithmetic.  A word alternates permutations with `U`-conjugated permutations,

```
π(s) = P₁ · U P₂ U* · P₃ · U P₄ U* · …
```

so the **entire cost is the `U`-applications**: two per `K₂` syllable.

### Measured on the emitted list

```
relators                                    4,636
syllables, total                          180,716   (mean 39.0, min 4, max 117)
  K₁ syllables                             90,358
  K₂ syllables                             90,358      → 180,716 U-applications
distinct GL_4(F₂) syllable values             344   → all λ(g) precomputable (14 MB)
prefix-trie nodes                         134,644   → sharing only 1.34×
```

Two consequences worth recording.  Only **344 distinct group elements** appear
across the whole list, so every permutation can be precomputed once and reused;
and **prefix sharing buys only 1.34×**, so a trie is not the lever it looks
like — the words diverge almost immediately.

### Memory

`U` in complex64 is `(20160k)² × 8` bytes: **3.25 GB at k = 1**, 13 GB at
k = 2, 52 GB at k = 4.  So `k = 1` is comfortable on a 48 GB node, `k = 2`
is the practical ceiling in complex64, and `k ≥ 4` needs either a GPU with
80 GB or a structured `U`.

### Flops, and why the unrestricted problem is out of reach

Per `U`-application on an `m`-column block: `8 d² m` real flops, reading
`8 d²` bytes.  At `k = 1`, full list:

| regime | cost per objective evaluation |
|:--|:--|
| single probe (`m=1`, bandwidth-bound) | 180,716 × 3.25 GB = **587 TB** → 1.6 h at 100 GB/s |
| batched (`m=64`, BLAS-3) | 3.8 × 10¹⁶ flops → **10.5 h** at 1 Tflop/s |
| batched on an A100 (`m=64`) | ≈ **32 min** at 19.5 Tflop/s |

Gradient by reverse-mode roughly doubles it.  An optimization needs hundreds of
evaluations, so **the unrestricted `U(20160)` problem on the full list is three
to four orders of magnitude out of reach.**  That is the central design finding
and it is why the staging below exists.

### Word-set subsampling: the pilot answers this

The coordinator asked whether "the 72 cartesian-escaping + 24 involutivity +
a random slice" is the right stage-1 objective.  The pilot (§f) settles it:

* the **72 escaping relators are exactly the support of the objective at the
  best known warm start** — at `U = J` every other relator has defect exactly
  zero, and these 72 have defect exactly `√2`;
* the **24 involutivity relators are already zero at `U = J`** (none of them
  escapes the cartesian subgroup), so they add nothing to stage 1;
* a **random slice of the 4,564 zero-defect relators is still needed**, but as
  a *control*: the deformation must not break what is already satisfied.

So the recommended stage-1 objective is **the 72 escaping relators as the
active set, plus a rotating random control slice** of a few hundred others.
Cost of the active set:

```
72 relators, 2,104 syllables (mean 29.2, max 53), 1,052 K₂ syllables
→ 2,104 U-applications per objective evaluation
```

which is 86× cheaper than the full list: ≈ 23 s per evaluation on an A100 at
`m = 64`, or ≈ 7 min on a CPU node.  All 72 come from the `st3` block.

---

## (c) The optimizer

**Geometry.**  `U(d)` with the Cayley retraction is the right default:
`U ← U · (I − A/2)⁻¹(I + A/2)` for skew-Hermitian `A`, which needs one
`d × d` solve per step (`O(d³)`, 8 Tflop at `k = 1` — comparable to a few
objective evaluations, so not dominant but not free).  The alternative
`U ← U exp(A)` requires a matrix exponential and is strictly worse here.

**Do not reuse the chart probes' L-BFGS-on-tangent scheme unmodified.**  It
was tuned at `d = 15`, where the retraction is free and the Hessian is tiny.
At `d = 20160` the memory for L-BFGS history alone is `2 · r · d²` — 65 GB at
history depth `r = 10`. Use either (i) Riemannian gradient descent with
Barzilai–Borwein step sizes, or (ii) L-BFGS with the history stored as
low-rank factors, never as dense `d × d` blocks.

**Objective smoothing.**  `F_max` is nonsmooth; optimize
`log Σ_s exp(β ‖π(s) − I‖₂²)` with `β` annealed upward, or minimize `F_rms`
with defect-proportional reweighting.  The chart probes' experience is that
raw max-optimization stalls on a single active constraint.

**Warm starts**, in the order they should be tried:

1. `U = J`, the tensor flip.  Exactly zero on 4,564 of 4,636 relators (§f).
   This is by far the best starting point and no prior probe used it at the
   regular representation.
2. `U = (I_{ℓ²(M)} ⊗ V) J` with `M` an index-15 maximal stabilizer and
   `V ∈ U(15)` — the deformation family already identified in the repo, which
   preserves the exact factor restrictions and reduces the live variable to
   225 parameters.  Cheap: `V` acts in 1,344 identical `15 × 15` blocks, so
   one application is `1344 × 15² × 8 ≈ 2.4 × 10⁶` flops instead of
   `3.3 × 10⁹` — **1,350× cheaper**.  The **full** 4,636-relator objective is
   then ≈ `4.4 × 10¹¹` flops, well under a second of compute per evaluation.
3. Identity and random unitaries, as controls only — the identity alignment
   is measurably worse than `J` (§f) and every automorphism alignment sits at
   max defect `√2`.

---

## (d) MSI resourcing

Single node, normal partition (`amdsmall`), no GPU needed for stages 0–1;
stage 2 wants one A100.  Get-signal-fast staging:

| stage | what | `U` family | cost | verdict horizon |
|:--|:--|:--|:--|:--|
| 0 | exact warm-start baseline | `I`, all 40320 alignments, `J` | seconds | **done, §f** |
| 1 | index-15 coset deformation on the full list | `(I ⊗ V)J`, `V ∈ U(15)` | <1 s/eval, CPU | one 2 h job |
| 2 | unrestricted `U`, 72-word active set + control | `U(20160)` | ~23 s/eval, A100 | one 4 h job |
| 3 | `k = 2, 4, …` trend | as stage 2 | ×`k²` | only if stage 2 moves |

Stage 1 should run before stage 2: it is over a thousand times cheaper, it uses the best warm
start, and if a 225-parameter deformation cannot move the objective below the
tensor-flip value then the unrestricted run needs a different starting point
rather than more iterations.

---

## (e) What the outputs would mean

**This is evidence and structure discovery. It is never proof**, in either
direction, and the notes should say so wherever numbers are quoted.

* A **decreasing-in-`k` trend** in `inf_U F_max` is the signature the FALSE
  side needs; a **plateau independent of `k`** is evidence for the TRUE side.
  Neither is conclusive: the criterion is a statement about `k → ∞`, and
  `atlas_kernel_collision_results.md` already contains a cautionary example
  where an exact minimax over a large sector (`2/7`, then `3/11`) was
  positive and yet the sector was not the whole space — the tensor flip beat
  it outright.
* **The real prize is structure in near-optimal `U`**, not the number.  Things
  worth extracting and reporting: block patterns relative to the coset
  decomposition `A₈/M`; whether `U` approaches a monomial matrix (which the
  `TF6/TF7` no-go says cannot succeed, so approaching one is a sign of a
  descent trap, not progress); Fourier/Weil shapes, i.e. whether `U` is close
  to the group-algebra sector `⊕_σ (u_σ ⊗ I)`; and the spectrum of `U`, since
  a spectrum concentrating on roots of unity would suggest a finite-order
  `U` and hence a finite-dimensional obstruction.
* **A negative stage-1 result is informative and cheap**: it would say the
  225-parameter neighbourhood of the tensor flip is a strict local minimum on
  the true list, sharpening the repo's existing seed-sweep evidence from the
  radius-5 window to the actual relator set.

---

## (f) PILOT, RUN: the exact objective at every classical warm start

`experiments/atlas_true_criterion_warmstarts.py`, `k = 1`, full list, exact —
no linear algebra at `d = 20160` is needed, because both classical families
have closed-form traces.

* **Automorphism alignments** (`U` implementing `θ ∈ Aut(A₈)`, all 40320
  inner and graph-twisted): `π(s) = λ(fold_θ(s))`, so `tr_d π(s) ∈ {0, 1}`
  and every relator contributes defect `0` or `√2`.
* **Tensor flip** `U = J`: `π_J(s) = L_{p₁(s)} R_{p₂(s)}`, and
  `tr(L_a R_b) = #{g : g⁻¹ a g = b}`, which is `1/|class(b)|` when `a ∼ b`
  and `0` otherwise.

```
U = I   (identity alignment)   max √2   RMS 0.327091   zero on 4,388 / 4,636
U = J   (tensor flip)          max √2   RMS 0.176242   zero on 4,564 / 4,636
```

**The tensor flip's defect is supported on exactly the 72 cartesian-escaping
relators, and on each of them it is exactly `√2`.**  For all 72 the factor
projections are non-conjugate — one is trivial (class size 1), the other a
transvection (class size 105) — so the trace is exactly `0` with no partial
cancellation.  All 72 lie in the `st3` block.

Three things follow.

1. **The classical sector is uniformly bad on the true list.**  Every
   automorphism alignment has `F_max = √2`, the worst possible value, since no
   alignment kills the whole list (the fold screen refuted that).  So the
   classical sector is not merely suboptimal — it is maximally bad in the max
   norm, and only the RMS distinguishes its members.
2. **The tensor flip is exactly as good as the length-nine theorem predicts,
   and no better.**  Its failure set is precisely the set of relators that
   escape `ker(A₈ * A₈ ↠ A₈ × A₈)`.  That is the same 72 words the screens
   track, arrived at from a completely different direction — the analytic
   objective, not the finite-quotient obstruction.  The two agree exactly.
3. **The stage-1 active set is determined**, not chosen: it is those 72 words.

`F_rms(J) = √(2 · 72 / 4636) = 0.176242`, matching the computed value, which
is a useful arithmetic check on the pilot.

### What the pilot does *not* say

It says nothing about whether `inf_U F_max` is positive, because it evaluates
two points, not an infimum; and `F_max = √2` at both means the max-norm
objective cannot distinguish them at all — only the RMS does.  Any optimizer
started at `J` and driven by `F_max` will see a flat landscape until it moves
all 72 words at once, which is a concrete reason to start with the smoothed or
RMS objective (§c).

---

## (g) Ready-to-submit

`experiments/atlas_true_criterion_warmstarts.py` is committed and reproduces
§f in seconds:

```
python3 atlas_relator_rank5_full_family.py --emit atlas-rank5-full-family.json
python3 atlas_relator_rank5_involutivity.py --merge atlas-rank5-full-family.json \
        --emit-merged atlas-rank5-T_St.json
python3 atlas_true_criterion_warmstarts.py atlas-rank5-T_St.json
```

Stage 1 is **not** written.  Its specification, for the next session:
re-point `experiments/atlas_stabilizer_coset_search.py` — which already
implements the `U = (I_{ℓ²(M)} ⊗ V) J` ansatz with left/right translations as
permutations of the regular basis and `V` acting in 1,344 identical `15 × 15`
blocks — from the radius-5 collision window to `atlas-rank5-T_St.json`, and
replace its Hutchinson trace estimate with the residual estimator of §a.
That estimator change is not cosmetic: the existing script's loss is a trace
estimate, and §a explains why that is the wrong statistic near the optimum.

## Stage-1 pilot: first descent data (MSI job 15868462, 32 min)

Implementation: `experiments/atlas_true_criterion_stage1.py` — the
(I ⊗ V)J ansatz with V ∈ U(15) complex, residual estimator (m = 16),
per-word backward.  Both built-in gates passed: the control slice was
EXACTLY zero at V = I (validating the 20160-dimensional coset model
outright) and the active baseline reproduced the landed 2.0 at 1.9964.

Result: 60 Adam iterations (lr 3e-3) moved the total loss from 1.99643
to 1.99632 — a decrease of ~1.1e-4 — with active mean defect² pinned at
~1.9963 throughout and the control never above 4e-4.  The landscape
adjacent to the tensor flip is locally flat for the index-15 coset
deformation at k = 1: the cheap ansatz buys back none of the 72
obstructed relators, consistent with the finite-quotient wall and with
the design's note that a negative stage-1 outcome is informative — it
says stage 2 needs a different starting point, not more iterations.

Scope: one seed, 60 iterations, weak-evidence grade; the probe engine
costs ~31 s/iteration because it propagates 20160-dim probes (the
general stage-2 engine, used early).  A stage-1b exact engine — the
(I ⊗ V)J traces decompose into 1,344 blocks of dimension 15, so the
exact objective should cost milliseconds — is the right next
implementation and would allow full V-landscape sweeps before any
stage-2 spend.

## Stage-2 execution log (2026-08-17)

Design as §(d): `U = W·J`, `W ∈ U(20160)` dense complex64, warm start
`W = I + 1e-4·(A - A†)` re-unitarized, Adam lr 2e-4, QR retraction
with diagonal-phase fix each step, residual estimator m = 8, the
determined 72-word active set against a 72-word satisfied control
slice.  Baseline gate (identity fast-path, no matmuls) passed on both
attempted devices: active mean defect² 1.998732, control max exactly
0.000e+00.

**Run 1 (V100 32 GB, job 16009229): OOM postmortem.**  Died at the
iteration-1 backward ("tried to allocate 3.03 GiB" = one W-sized
complex64 buffer).  Ledger: W (3.03) + grad (3.03) + Adam moments
(6.06) are unavoidable; the killers were the QR retraction's `q, r`
outputs (3.03 each) surviving as *loop locals* through the entire next
backward pass, plus the gradient overlapping the cusolver QR workspace
spike — 27.4 GiB live at the fault.  Fix: `del q, r, d` after the
in-place copy, `zero_grad(set_to_none=True)` immediately after the
optimizer step (before QR), `PYTORCH_CUDA_ALLOC_CONF=
expandable_segments:True` against fragmentation.  Iteration 0 was
logged before death and is valid data: loss 2.0015, active mean
1.9988, control mean 0.0028, block_diag_distance 0.054,
monomial_distance 0.0014, 237 s/iteration.

**Run 2 (V100, job 16009606): cancelled at iteration ~7 — the fixed
probe set became the objective.**  Memory fix held (past the run-1
fault point, 30+ min healthy).  But by iteration 5 the trajectory read
active mean `2.00 → 1.32` with control `0.003 → 0.65`: the probe
matrix was drawn ONCE, so the optimizer was free to learn
identity-on-an-8-dimensional-subspace for the active words instead of
operator proximity — with `4×10⁸` parameters against `161k` probe
entries, the empirical estimator is gameable and its descent says
nothing about the true HS landscape.  (A control rise alone would be
legitimate — a saddle direction of the total objective may trade
slices — the diagnosis is the fixed-probe coupling, not the trade.)
Killed as contaminated; the numbers are recorded here as the
overfitting signature to recognize, not as landscape evidence.

**Run 3 (V100, job 16010002): the unbiased design — cancelled on a
MISDIAGNOSIS, recorded here as the lesson.**  Probes resampled every
iteration (true SGD on the exact objective, reports conditionally
unbiased), `grad_norm` and `‖W − I‖` logged.  Iteration 0 read
`w_minus_identity = 1.9993` where the step size predicts 0.04, and I
killed the run believing the cusolver QR retraction had scrambled `W`.
The CPU repro (`experiments/qr_phase_repro.py`, torch 2.4.1, identical
numbers) then showed the truth: **LAPACK/cusolver Householder QR of a
near-identity input returns `Q ≈ −I`** (with `R ≈ −I`, product `+I`),
the script's *init* used raw QR with no phase fix, so every run's warm
start sat at the gauge copy `−I` — and a global phase cancels in
`W R_h W*`, so `−I` is model-equivalent to `I`.  The in-loop
phase-fixed QR retraction was then continuous *in that gauge* (`R`'s
diagonal stays positive around `−I`, the fix a no-op).  Nothing was
broken; the diagnostic measured gauge, not damage.  Iteration 0's
other reads were genuine and correct: `grad_norm 2.21` is the m=8
estimator's noise floor at the (provably zero-gradient) flip, and
active/control matched baseline.  Moral: before killing a run over a
diagnostic, check whether the quantity is gauge-invariant in the
model; the honest drift measure is `2 − 2|tr W|/n`.

**Run 4 (V100, job 16010744): COMPLETED — the clean design, and the
stage-2 verdict.**  Resampled probes; Newton–Schulz polar retraction
(pure GEMMs, nearest unitary, init in the `+I` gauge so
`w_minus_identity` is honest); `unitarity_defect` logged (`~1e-7`
throughout after the first retraction).  All 100 iterations, exit 0,
`research/artifacts/atlas-stage2-run4-result.json`.

Outcome: **zero descent.**  `best_loss` remained iteration 0's
2.00035 for the entire run.  The dynamics equilibrated by iteration
~20 into a noise ball of radius `‖W − I‖ ≈ 0.048–0.052` around the
flip, with the loss hovering at `≈ 2.019` — strictly ABOVE baseline
everywhere the trajectory wandered — active mean pinned at
`2.000 ± 0.003`, control damage saturating at `≈ 0.018–0.022`, and
`grad_norm` constant at the `2.19–2.20` estimator noise floor (the
theorem says the true gradient is exactly 0; the floor is m=8
sampling noise).

Reading, per the pre-registration: unbiased SGD found **no accessible
negative curvature** at this radius and noise scale — the empirical
complement of `atlas-flip-first-order-rigidity`.  Consistent with the
flip being a local minimum of the full objective at `k = 1`; NOT proof
of it (sign-normalized Adam is a weak saddle-escaper; thin or rare
negative directions among `8×10⁸` coordinates could hide).  A stall
decides nothing about the branch question.  The GPU chapter of this
probe is closed.

## Exact restricted Hessian scan (2026-08-18)

Instrument (i) was then executed exactly
(`experiments/atlas_flip_hessian_scan.py`; engine self-tested 300/300
against dense `S₄` computation): every Hessian term reduces to
canonical `tr(X T₂ X T₁)` / `tr(X² T)` forms with translation
contexts, evaluated by fixed-point counts on the structured directions
`E(u,v) = L_uR_v − L_{u⁻¹}R_{v⁻¹}` and `i(L_uR_v + L_{u⁻¹}R_{v⁻¹})`.
Verdict over 4,000 catalog pairs × 2 families (full active set +
72-control sample): **zero negative-curvature directions; max Q = 0 on
flat directions; and `Q_active = 0` on every single evaluation** —
confirmed per class (both the `p₁`-trivial and `p₂`-trivial escapees,
separately) on 600 fresh directions from an independent seed.  All
second-order resistance in the sector belongs to the control words.
A dense `S₄` counterexample separately shows the flatness is NOT a
global identity in `W` (active-type traces move for random unitaries),
so none of this is a `k = 1` impossibility theorem.  Full record:
`research/atlas-flip-translation-sector-hessian.md` and
`research/artifacts/atlas-flip-hessian-scan-2026-08-18.json`.

**Pre-registered interpretation (unchanged from §(d)):** a descent of
the active mean visibly below the 1.9987 baseline is the
hyperlinear-side signature at k = 1 and the trigger for a k-trend
study; a stall at the baseline is stability-side evidence and elevates
the stationarity question below.  Neither is proof.  Monomial drift
(monomial_distance → 0 with loss stuck) is the recorded descent trap;
block_diag_distance tracks collapse back into the dead index-15 coset
slice.

**The stationarity question — ANSWERED (2026-08-17, exact):** the flip
is a critical point of the full defect objective on U(20160), per
word, at every multiplicity, provably — see
`atlas-flip-first-order-rigidity(-proof)` and
`atlas-flip-stationarity-2026-08-17.json`.  The CPU-exact computation
ran ahead of the GPU (integer verdict: the unsymmetrized differential
itself vanishes at the pair level; 376 raw terms, 0 surviving), and
the analytic proof came out of reading the machine's answer: every
T_St word escapes in at most one factor (36 + 36 + 4,564, none in
both), `p₂ = I` kills each site via `b = h⁻¹`, and `p₁ = I` makes the
terms telescope cyclically.  **Run 2 is therefore reinterpreted before
its data arrives: it is a negative-curvature (Hessian) probe.**
Descent below the 1.9987 baseline now means the flip is a strict
saddle and names an escape direction; a stall is consistent with a
local minimum and decides nothing.  The earlier trend framing
("decreasing-in-k = FALSE-side signature") survives unchanged one
level up: any such trend must now come from second-order or global
structure, never from a gradient flow off the flip.
