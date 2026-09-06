# cs-clutching

Owns `Analysis/LIXClutching.lean`, `Analysis/LIXGeneratorUnitary.lean`,
`Analysis/LIXObstructionComplementUnitary.lean`, `Analysis/LIXLemmaSix*.lean`.

Written by the Opus owner during the review-only pairing with `cs-clutching-s`;
the Lean files are `cs-clutching-s`'s until the lead hands them back.

## 1. GREEN

Measured on this lane's own clone, probe round 1.

| module | verdict | what was probed |
|---|---|---|
| `Analysis/LIXClutching.lean` | `Build completed successfully (8655 jobs)`, `✔ Built … (16s)` | the file as it now stands in the tree, 1185 lines, unchanged since |
| `Analysis/LIXObstructionComplementUnitary.lean` | `Build completed successfully (8657 jobs)`, `✔ Built … (40s)` | the file **as authored at 234 lines**, ring-level Step A only |
| `Analysis/LIXGeneratorUnitary.lean` | red, five errors; repaired and committed green by `cs-clutching-s` at `0f65b8a7e` | job count for the green not measured by this lane |

Two cautions on the second row, so that nothing here is read as more than it is.

**The 8657 was not a measurement of the current file.** At probe time
`LIXObstructionComplementUnitary.lean` was the committed 234-line version
carrying only the ring-level Step A (`mvn_complement_unitary_apply_eq` and its
neighbours). It is now 466 lines in the working tree, with a continuous-family
form and a vector form added, and in that state it is **RED** — reported by
`cc-lix-odd`, whose `LemmaTwoUnitary` imports it. So the green above tells you
the ring-level half is sound and localises the breakage entirely inside the
added material; it is not a fallback state for the file as it stands.

**No green claim here rests on a replay.** Both counts come with a `Built` line
and an elapsed time for the module itself.

## 2. AUTHORED, UNVERIFIED

Nothing in Lean from this lane. What follows is worked out and hand-checked,
and has been handed to `cs-clutching-s` in transcribable form.

### The lane's recorded negative finding is wrong

`research/artifacts/stw59-clutching-layer-and-generator-cost-2026-09-05.md` §3
concludes that `clutch u ≅ F` and the null-homotopy of `diag(u,1)` are Bott's
unstable computation and not elementary. It rules out one ansatz — the planar
rotation with a phase, singular on the great `S³ = {x₃ = 0}` — and then
over-generalises. The correct statement is that no *one-step* transport works,
because `{pᴴx = 0}` is a 3-sphere meeting both closed hemispheres for every base
point `p` and every equator. Two steps work.

**The transport.** A Householder reflection `reflMat v = 1 − (2/(vᴴv))·v vᴴ` is
self-adjoint and squares to `1`, so it is unitary, and

```text
reflMat (a + b) * reflMat a    carries a to b
```

whenever `a`, `b` are unit vectors with `aᴴb` real and not `−1`. Rephasing the
target by `w = aᴴb/‖aᴴb‖` removes the reality condition, giving `transportRot a b`
defined whenever `aᴴb ≠ 0`. It acts as the scalar `w`, not as the identity, off
`span{a,b}`; that is harmless and is what keeps it continuous.

**The frame.** Composing two transports through the normalised midpoint,

```text
frameRot p x  :=  transportRot (midVec p x) x * transportRot p (midVec p x),
midVec p x    :=  (p + x)/‖p + x‖
```

gives a continuous unitary with `frameRot p x * rk1 p v = rk1 x v`. Both inner
products that must be nonzero are the *same* number `(1 + pᴴx)/‖p + x‖`, and
`‖p + x‖ = 0` iff `pᴴx = −1`, so the single hypothesis `pᴴx ≠ −1` covers both
steps and the domain is the sphere minus one point — far more than a closed
hemisphere needs.

**What it buys.** With `e₃ = Pi.single 2 1`, `sigmaPlus x := frameRot e₃ x` on
`{x₂ ≠ −1} ⊇ D₊` and `sigmaMinus x := frameRot (−e₃) x * reflMat e₃` on
`{x₂ ≠ 1} ⊇ D₋` satisfy the same identity `σ_± x * rk1 e₃ e₃ = rk1 x e₃`, hence
`σ_± (1 − rankOneProj e₃) σ_±ᴴ = 1 − rankOneProj x = Fproj`. The generator
`genU x := (sigmaPlus x)ᴴ * sigmaMinus x` fixes `e₃`, so it *is* `diag(u,1)`
with no submatrix surgery. Its null-homotopy is explicit: contract each
hemisphere along great circles, which stay in their hemisphere because the
equator condition `(x₂).re = 0` is exactly real-orthogonality to `e₃`; the
homotopy ends at the constant `reflMat e₃ = diag(1,1,−1)`, joined to `1` by
`diag(1,1,exp(iπs))`. No `π₄(U(3))` anywhere.

`frameRot p p = 1` is the sanity lemma the endpoints of that homotopy need: the
midpoint of `p` with itself is `p`, and `reflMat (2p) = reflMat p` because the
scalar absorbs the square of the scale.

### Lemma 6 is deleted

Every block that `connect` adds is constant in the `S⁴` coordinate:
`φ_i(a)(x,z) = a(π_i x) ⊕ (a(x_i) ⊗ 1_{L_{i+1}})`, `π_i` is the identity on `S⁴`,
`a(x_i)` is a constant matrix, and `1_L` depends only on the new `CP` factor.
So

```text
tower.climb j 0 u  =  u ⊕ c_j     for a unitary c_j of p_{H_j} over Y_j alone
```

as an **equality**, by induction on the tower's own recursion — not a homotopy.
Package it as a predicate so the induction and Corollary 4 meet syntactically:

```lean
def HasGeneratorShape (i : ℕ) (u : Matrix (Fin 2) (Fin 2) C(↥sphereFour, ℂ))
    (a : StageAlgebra i) : Prop :=
  ∃ c : Matrix (HIdx i) (HIdx i) C(baseY i, ℂ),
    toFunctionMatrix a = Matrix.fromBlocks (pullMat prS4 u) 0 0 (pullMat prY c)
```

Then the **generalised Corollary 4** — for every unitary `c` of `p_{H_i}` over
`Y_i`, `u ⊕ c ∉ unitaryComponentOne (StageAlgebra i)` — closes `cs-endpoint`'s
`hstage` at `c := c_j`. Same hemisphere gluing, with `c` carried on the north
side; the seam then demands that `diag(u,1) ⊕ cᴴ` extend over the disc, and
since `c ↦ cᴴ` is a bijection of those unitaries, quantifying over all `c` makes
the orientation a non-issue. `i = 0` with the empty `c` gives
`u ∉ U₀(StageAlgebra 0)` as a special case rather than a separate argument.

State the shape lemma at `tower.climb j 0` from the start, per `cs-endpoint`:
`climbHom_apply` makes `climbHom` and `climb` `rfl`, but a hand-rolled composite
is only propositionally equal and costs a transport lemma plus its induction.

## 3. NEEDS

**From `cc-lix-odd` — Lemma 2**, over `↥sphereFive × baseY i`, arbitrated by the
lead as the fixed target statement and recorded in the program note §1.3:

```lean
¬ MurrayVonNeumannEquiv
    (Matrix.fromBlocks (pullMat prS5 Fproj) 0 0 (pullMat prY (HprojY i)))
    (Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) C(↥sphereFive × baseY i, ℂ)) 0 0
      (pullMat prY (HprojY i)))
```

Index types `Fin 3 ⊕ HIdx i` and `Fin 2 ⊕ HIdx i`, reconciled downstream by
`murrayVonNeumannEquiv_blockSum` and `murrayVonNeumannEquiv_submatrix`. **Not**
as a `ClutchingObstruction` instance.

**From `cs-stages` — `HprojY`**, which blocks even stating the above. `Hproj i`
lives over `C(baseX i, ℂ)` with `baseX i = sphereFour × baseY i`, and cannot be
typed over `sphereFive × baseY i`. Since `lineProj i j` reads only `z.2 j`, the
Y-level version is immediate by the same recursion:

```lean
def HprojY : (i : ℕ) → Matrix (HIdx i) (HIdx i) C(baseY i, ℂ)
theorem Hproj_eq_pullMat (i) : Hproj i = pullMat (baseY-projection) (HprojY i)
```

Assigned to `cs-stages` by the lead.

**From `cs-stages` — a constraint on `connect`, load-bearing.** The added block
must be constant in the `S⁴` coordinate: evaluate at a fixed point of `baseX i`
(their `stagePoint i` already is one) and do not reindex the first block through
anything `x`-dependent. It costs them nothing, but if `connect` lands otherwise
the shape lemma fails and Lemma 6 comes back — with a Mathlib input that does
not exist (see TRAPS).

## 4. TRAPS

**`ring` inside `first` never fails.** Mathlib's `ring` falls back to `ring_nf`
and *succeeds* with a "Try this: ring_nf" info message without closing the goal,
so the later alternatives of a `first | ring | …` block are never tried and the
failure surfaces as "unsolved goals" at the end of the block. Two of the five
reds in `LIXGeneratorUnitary` were this. Use `ring1`.

**`clutchingObstruction_of_equiv` is unusable as stated.** It assumes
`hΩ : IsDiscUnitary Ω` and concludes `ClutchingObstruction t ν Ω`, which
`not_isDiscUnitary_of_clutchingObstruction` turns straight back into
`¬ IsDiscUnitary Ω`. Its hypotheses are jointly contradictory, so the file's
advertised bridge — "the obstruction lane may deliver Lemma 2 in whatever
concrete model it prefers" — is dead code. The proof uses `hΩ` once, for
`isClutchDatum_coneMat`; weakening the hypothesis to
`∀ x, IsClutchDatum (t x) (coneMat Ω (ν x))` repairs it, and that is satisfiable
from unitarity on the unit sphere alone. Repair assigned to `cs-clutching-s`.

**The unitary group of `Matrix (Fin r) (Fin r) ℂ` is not known path-connected in
Mathlib at pin `81a5d257`.** `Analysis/Matrix/Spectrum.lean` carries only the
Hermitian spectral theorem, `LinearAlgebra/Matrix/UnitaryGroup.lean` has no
connectedness result, and `Unitary.mem_pathComponentOne_iff` only characterises
the component of `1` as products of exponentials, leaving you to prove that every
unitary matrix is such a product — cheapest via finiteness of the spectrum, a
rotating scalar, `Unitary.norm_sub_one_lt_two_iff` and
`expUnitary_argSelfAdjoint`, over `CStarMatrix`. Lemma 6 as originally specified
needed exactly this. The `u ⊕ c` generalisation avoids it entirely.

**`Fin 3 → ℂ` carries the sup norm.** `‖x‖ = 1` is the wrong condition; state
everything with `dotProduct`. `LIXProjectiveSpaceModel.sum_star_mul_self` is the
bridge from `unitVectors` membership, and `rankOneProj` there is already the
rank-one primitive — do not define a second one under another name.

**A bare lambda for a `Matrix` value breaks entry-level `simp`.** Matrix apply
lemmas are stated through `Matrix.of`, so `def f : Matrix K K ℂ := fun i j => …`
gives an apply lemma that will not fire where it is needed. Use `Matrix.of`.
Relatedly, `congrFun` on an equality of `Matrix` values can fail to elaborate,
because the type is not syntactically a Pi; `congrFun₂` is the idiom Mathlib
itself uses.

**The shared scratchpad is shared.** Two lanes wrote `scratchpad/probe1.log` and
truncated each other. Use a lane-specific directory, and read `cc-last.log`
inside your own clone as the authoritative copy.

**`ccprobe.sh` died with "Argument list too long"** on a fresh clone — the whole
tree counts as changed on the first sync, and the artifact-clearing list is
passed on the command line — and still exited 0 with no build attempted. Fixed
in place by the lead since; a lane copy that ships the changed-file list in a
file is at `scratchpad/cs-clutching/ccprobe2.sh`.
