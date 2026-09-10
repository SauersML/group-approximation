# `sp-oddside` — Step C with `k` zeros (the odd side)

Lane of `notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3.4.  Clone `spare2`.
Owns `GroupApproximation/CharClass/LIXK*.lean` **only**; edits no existing file.

First deliverable: the `k`-zero Step C over `F₂` at `n = 2`.

Status key: **GREEN** = a `✔ … Built <module>` line cited; **AUTHORED, UNVERIFIED** = written,
never near a compiler; **PLANNED** = in the file list below, not written.

---

## 0. The plan (written 2026-09-10, before authoring)

### 0.1 What the reading pass settled

Four facts decide the shape of the whole deliverable.  Each is **VERIFIED (read)** at the
declaration named.

1. **The zero-locus theorem is already parametric and needs no change.**
   `CharClass/LemmaTwoZero.lean: mtSection_manuscript_eq_zero_iff` is stated for abstract
   `a b : M → ι → ℂ`, `c : M → κ → ℂ`, and uses exactly `a m ≠ 0`, `∑‖a m i‖² = 1`,
   `∑‖b m i‖² = 1`, `χ(1/2) = 1`.  Its conclusion is
   `t = −1 ∧ y = 0 ∧ b m = −a m ∧ c m = 0`.  So the whole `k`-zero geometry is the single
   substitution `a := e₁`, `b := Ψ_k ∘ x` inside a *new* concrete instance beside
   `LIXSectionManuscript.lean`, and `LemmaTwoZero.lean` is reused verbatim.  This confirms
   `sp-design` §1.1 independently.

2. **`ψ_k` enters my files only through the scalar map.**  `sp-powers`' `joinPow` is
   `planeSub e₁ e₂ (joinC k)` on a **real inner-product space**; `S⁵` here is
   `STW59.unitVectors (Fin 3) ⊆ (Fin 3 → ℂ)`, a sup-normed pi type with no
   `InnerProductSpace ℝ` instance, so `joinPow` does not apply at this type.  What does
   apply, and is the *same map*, is their scalar
   `Powers.joinC k z = (‖z‖^k : ℂ)⁻¹ * z^(k+1)`: my sphere map is
   `Function.update x 0 (joinC k (x 0))`, which is `sp-design` §2.1's `Ψ_k` written in the
   coordinates this side of the tree uses.  **One name, theirs.**  I import
   `Analysis/LIXPowersJoinPower.lean` for `joinC`, `norm_joinC`, `continuous_joinC`,
   `joinC_id`, `joinC_zero` and define nothing that duplicates them.  (Closure cost: three
   modules, `LIXPowersGauge → LIXPowersNaturality → LIXPowersJoinPower`, all GREEN in
   `sp-powers`' report.  I do **not** import their `Angle`/`Pinch`/`EH` files.)

3. **Indexing convention, fixed once.**  `joinC k` is the map of degree `k + 1`
   (`sp-powers` shifted the index so `k = 0` is the identity and no `1 ≤ k` side condition
   is ever carried).  I keep their `k` as the internal parameter, so the zero set is indexed
   by `Fin (k+1)` — non-empty definitionally, which the counting argument wants — and the
   **exponent** in the theorem statement is `k + 1`.  A wrapper states the same result over
   an exponent `e` with `0 < e`.

4. **The count does not need a direct-sum decomposition.**  `sp-design` §4.2 item 3 asks for
   `H^{2r}(N, N∖Z) ≅ ⊕_i H^{2r}(N, N∖{z_i})` compatible with `j`.  The consumer only ever
   uses the **surjectivity half**, and in the cheaper direction: for each `i` the identity
   of `N` is a map of pairs `(N, N∖Z) → (N, N∖{z_i})` (because `N∖Z ⊆ N∖{z_i}`), so
   `relPullback` gives `ρ_i : H^{2r}(N, N∖{z_i}) ⟶ H^{2r}(N, N∖Z)` with
   `ρ_i ≫ j = j_i` by naturality of `relToAbs` along the identity.  The obligation is then
   `x = ∑_i ρ_i (x_i)` — an equation between elements, no `⊕`, no biproduct, no
   compatibility square to state separately.  This is a strict simplification of §4.2(3)
   and I recommend `sp-evenside`/`sp-coeff` adopt the same shape wherever a splitting is
   needed.

### 0.2 The abstract counting engine, stated over an arbitrary field

Everything downstream of the geometry is this, and it is coefficient-generic from the
start (`K` a field; `ZMod 2` is the `p = 2` instance), so `sp-coeff`'s parameter costs this
lane nothing later:

```text
j.hom x = ∑ i, (jloc i).hom (xloc i)         -- from hsplit + hcompat
        = ∑ i, c = (k+1) • c                  -- from hloc
        ≠ 0                                   -- K a field, c ≠ 0, ((k+1 : ℕ) : K) ≠ 0
```

At `K = ZMod 2` the arithmetic side condition `((k+1 : ℕ) : K) ≠ 0` is exactly
"`k + 1` is odd", i.e. the program's "every **odd** power of the witness stays outside `U₀`".
No local degree, no determinant, no orientation appears anywhere in the engine, which is
the design goal of §1.3.4 and it is met.

### 0.3 File list (all new, prefix `CharClass/LIXK*`)

| file | proves | depends on |
|---|---|---|
| `LIXKMap.lean` | the map `Ψ_k` on `Fin 3 → ℂ`, its norm/continuity, **and the `k+1` roots**: `Ψ_k x = −e₁ ↔ ∃ j : Fin (k+1), x = ζ_j e₁`, the `ζ_j` distinct, on the equator, a free `ρ`-orbit | `LIXSectionManuscript`, `Analysis.LIXPowersJoinPower` |
| `LIXKSection.lean` | the manuscript data with `a = e₁`, `b = Ψ_k ∘ x`; `isMTSectionData`; **the zero locus is exactly the `k+1` points** `(southPole, (ζ_j e₁, basePoint))`; the zero set as a `Finset` of card `k+1` | `LIXKMap`, `LemmaTwoGlue` |
| `LIXKPunctured.lean` | Mayer–Vietoris in the *intersection* direction; **`H^m(N ∖ S) = 0` for a finite non-empty `S` and `m ≥ d`**, by induction on `S`; instance at the LIX base | `MayerVietorisElement`, `ThomPuncturedRecursion`, `LIXStepEPunctured` |
| `LIXKCount.lean` | the abstract engine of §0.2 over `[Field K]`, plus the named obligation `Prop`s | `CohomologyBasic` only |
| `LIXKStepC.lean` | the `k`-zero analogue of `ThomStepCOddLocal.topChernClass_ne_zero_odd_local`: abstract `N`, `k+1` zeros, over the obligations | `LIXKCount`, `ThomPuncturedRecursion`, `RelativeLES` |
| `LIXKStepCWired.lean` | the LIX instantiation, shaped like `LIXStepCOddWired.lix_topClass_ne_zero_of_three` with `k` explicit; the exponent-facing wrapper | all of the above + `LIXStepCOddRelative` |

### 0.4 The obligations, as named `Prop`s

Stated with docstrings in `LIXKCount.lean` / `LIXKStepC.lean` before any proof, per §3 of
the program note.  Two are discharged in this deliverable, three are not and say who owes
them.

| `Prop` | meaning | owner |
|---|---|---|
| `KPuncturedVanish` | `H^{2r}(N ∖ Z; K) = 0` for the `k+1`-point `Z` | **this lane, discharged** (`LIXKPunctured`) |
| `KZeroLocus` | the section vanishes exactly on `Z`, `#Z = k+1` | **this lane, discharged** (`LIXKSection`) |
| `KLocalSplit` | `x = ∑_i ρ_i(x_i)` — excision to `k+1` disjoint balls | this lane, **later**; needs `RelativeExcision` at a disjoint open cover of the zeros |
| `KLocalClassEq` | `j_i(x_i) = j_0(x_0)` — `sp-design` §4.1 Half A **and** Half B | this lane, **later**; Half A is `relToAbs_naturality` + absolute homotopy invariance along `ρ_t`, Half B is the `F₂` line trick of `RelativeLineHomotopy` at `p = 2` and needs `sp-coeff`'s relative homotopy invariance at odd `p` |
| `KLocalNonzero` | `j_0(x_0) ≠ 0` — the one-zero computation at `−e₁` | this lane, **later**; it is the existing `LIXHsq*`/`LIXSectionChart` chain with `e₃` replaced by `e₁`, which `sp-design` §1.3 recommends doing generically in the unit vector `a` and an ℝ-linear isometry `L` onto `a^⊥`, not as a `Fin 3` relabelling |

The three "later" items are exactly the shape the existing tree already uses: the mod-2
Step C ends at `lix_topClass_ne_zero_of_three`, which carries `hsq`, `hres`, `hclass` as
open binders.  The `k`-zero theorem ends the same way, with `k` explicit and one extra
binder for the split.

### 0.5 Model tests to run before proving (queued; MSI wrapper on auth cooldown until ≈12:10 CDT)

1. **the zero count** — that `{z : z^{k+1} = −1}` has exactly `k+1` elements and that
   `Ψ_k x = −e₁` forces `x₁ = x₂ = 0`, over random `x ∈ S⁵`, `k ≤ 8`;
2. **the local model** — that the derivative of `(u, x) ↦ (1−τ)e₁ + τΨ_k(x)` at each of the
   `k+1` zeros is the *same* matrix once the source frame is transported by `ρ^j`
   (re-running `sp-design` §2.3's check in **my** coordinates, `Fin 3 → ℂ` with the
   `Function.update` spelling, not theirs);
3. **the sign-free count** — that `∑_j 1 = k+1` is the whole content, i.e. that no local
   contribution differs, checked by evaluating the section's local class through explicit
   charts at every `z_j` for `k ≤ 6`.

`sp-design`'s and `sp-powers`' tools are on the node under `scratch/`; mine will go to
`scratch/sp-oddside/`.

---

## GREEN (with job counts)

Nothing yet.  `spare2`'s real-copy warm is queued behind the other lanes and the MSI
wrapper is on an auth cooldown until ≈12:10 CDT (lead, 2026-09-10).

## AUTHORED, UNVERIFIED

Nothing yet.

## NEEDS

* **`sp-powers`**: `Analysis/LIXPowersGauge`, `LIXPowersNaturality`, `LIXPowersJoinPower`
  to stay green — my `CharClass/LIXKMap.lean` imports the third for `joinC`.  If you rename
  `joinC` or move it, tell me; I use `joinC`, `joinC_zero`, `joinC_id`, `norm_joinC`,
  `continuous_joinC` and nothing else.
* **`sp-powers`**: eventually, the bridge lemma identifying *your* `joinPow e₁ e₂ k` on the
  equatorial `EuclideanSpace ℝ (Fin 5)` with *my* `Function.update x 0 (joinC k (x 0))` on
  `Fin 3 → ℂ` across `LIXLemmaSixGenerator.equatorEmb`.  Neither of us needs it for our own
  first deliverable; Step A needs it, because Step A must produce `G *ᵥ (e₁,0) = (Ψ_k x, 0)`
  for the *same* `Ψ_k` that your clutching naturality pulls back.  I state it as a `Prop`
  and do not prove it.
* **`sp-coeff`**: relative homotopy invariance over a field `K` (their item 1 /
  `sp-design` §4.4).  Not blocking at `p = 2`, blocking for the second deliverable.
* **`sp-tower`**: the `Gen` shape layer for `VIdx`/`baseM` at general `n`.  Not blocking:
  I write against the `n = 2` shape layer as it is, but never against `e₃` or the south
  pole of the sphere — the zeros are `−e₁` and its `ρ`-rotates, on the equator.

## TRAPS

* `Analysis/LIXPowersJoinPower.lean`'s `joinPow` is **not usable at `Fin 3 → ℂ`**: it is
  built from `planeSub`, which needs `InnerProductSpace ℝ E`, and the LIX five-sphere is a
  sup-normed pi type with no such instance.  The scalar `joinC` is the shared part and the
  only shared part.  Reaching for `joinPow` and then trying to supply the instance would
  land in `EuclideanSpace`/`WithLp` transport, which `LIXSectionChart.lean`'s header already
  records as the trap that file exists to avoid.
