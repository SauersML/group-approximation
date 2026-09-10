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
| `KLocalSplit` | `x = ∑_i ρ_i(x_i)` | this lane, **later**; see the route below — **relative** Mayer–Vietoris, *not* excision to disjoint balls |
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

Eight files exist; seven have a `Built` line at their current content, one
(`LIXKStepCWired`) does not yet.  **A single-log citation covering all of them is in
flight** — the lead's new transitive purge cleared 2538 artifact sets in `spare2`
(`purged 2538 stale artifact sets (source-newer=0, import-newer=2538) of 3308 oleans`), so
`laneprobe-20260910-135224.log` is a near-total rebuild and will carry one `Built` line per
module.  Until it lands, this is the per-module evidence, each line quoted from the log
named:

| module | `Built` line | log | content |
|---|---|---|---|
| `LIXKCount` | `ℹ [6752/6792] Built … (28s)` | `laneprobe-20260910-124334.log` | current |
| `LIXKMap` | `ℹ [8875/8877] Built … (125s)` | `laneprobe-20260910-124334.log` | current |
| `LIXKStepC` | `ℹ [8874/8877] Built … (123s)` | `laneprobe-20260910-124334.log` | current |
| `LIXKStepCTwo` | `ℹ [8855/8878] Built … (145s)` | `laneprobe-20260910-125237.log` | current |
| `LIXKSection` | `ℹ [8843/8877] Built … (194s)` | `laneprobe-20260910-120446.log` | see note |
| `LIXKPunctured` | `ℹ [8862/8877] Built … (111s)` | `laneprobe-20260910-120446.log` | see note |
| `LIXKRelativeMV` | — | — | authored, never compiled |
| `LIXKStepCWired` | — | — | authored, one fix in flight |

**Note on the two `120446` rows.**  Those two files each later received one line,
`set_option linter.unusedSimpArgs false`, and in `124334` they show `Replayed`.  I cannot
prove from the logs alone whether the `120446` build saw that line, so by the fleet rule
those two rows should be read as *provisional* until the running rebuild replaces them.
Everything else is unambiguous.

The marker is `ℹ` rather than `✔` only because each of these modules emits `info:` lines
(the axiom audits); the verb is `Built`, which is what the rule is about.  Fifteen audited
endpoints have printed exactly `[propext, Classical.choice, Quot.sound]`:
`map_eq_nsmul_of_localSplit`, `map_ne_zero_of_localSplit`, `psiVec_eq_neg_eOne_iff`,
`kRoot_injective`, `psiVec_kRot`, `lixKSection_eq_zero_iff`, `lixKZero_injective`,
`isZero_inter_of_cover`, `isZero_punctured_finite`, `topChernClass_ne_zero_kzero`,
`topChernClass_ne_zero_kzero_naturality`, `eq_of_ne_zero_of_line_two`,
`localClassesAgree_of_ne_zero_two`, `topChernClass_ne_zero_kzero_two`, and
`puncturedVanish_lixKZeroSet`.  Lexical `sorry` scan across all eight files: **0 hits**.

What that covers, mathematically:

* **the `k+1` zeros** — the section with `a = e₁` and `b = Ψ_k ∘ x` vanishes at exactly the
  `k+1` distinct points `(southPole, (ζ_j e₁, basePoint))`, all on the equator;
* **the punctured vanishing** at any finite non-empty puncture set, and with it the
  Mayer–Vietoris direction the tree did not have;
* **the count**, over an arbitrary field;
* **the `k`-zero Step C, abstractly**, and its `F₂` form with `LocalClassesAgree` removed;
* **the rotation and the free orbit**.

## AUTHORED, UNVERIFIED

`CharClass/LIXKStepCWired.lean` only — blocked by the foreign red above, never compiled.
The other five files in the table below are GREEN; the table is kept because it is the
inventory of what each file contains.

No `sorry` in any of the six (lexical scan: 0 hits), and none is imported by anything
outside this lane.

| file | contents |
|---|---|
| `GroupApproximation/CharClass/LIXKMap.lean` | `eOne`, `negEOne`, `re_neg_eOne_two`; `psiVec` (= `Ψ_k`, via `sp-powers`' `Powers.joinC`), `norm_psiVec_apply`, `normSq_psiVec`, `psiVec_mem_unitVectors`, `continuous_psiVec`, `psiVec_zero_eq`; `kUnity`/`kBase`/`kRoot` with `kRoot_pow`, `norm_kRoot`, `kRoot_injective`, `exists_kRoot_of_pow_eq_neg_one`; `kZeroVec`/`kZero` with `kZero_injective`, `re_kZeroVec_two`; **`psiVec_eq_neg_eOne_iff`**; `kRot` with `psiVec_kRot` and `kRot_kZeroVec_zero` |
| `GroupApproximation/CharClass/LIXKSection.lean` | `aVecK`, `bVecK` with norms and continuity; `isMTSectionData_manuscriptDataK`; `bVecK_eq_neg_aVecK_iff`; `lixKSection`, `lixKZero`, **`lixKSection_eq_zero_iff`** (exactly `k+1` zeros); `lixKZero_injective`, `lixKZeroSet`, `finite_lixKZeroSet`, `lixKSection_ne_zero_of_notMem` |
| `GroupApproximation/CharClass/LIXKPunctured.lean` | `isZero_inter_of_cover` (Mayer–Vietoris at the intersection), `isZero_cohomology_setCongr`, `isZero_punctured_finset`, **`isZero_punctured_finite`** |
| `GroupApproximation/CharClass/LIXKCount.lean` | `LocalSplit`, `LocalClassesAgree`, **`map_eq_nsmul_of_localSplit`**, `map_ne_zero_of_localSplit`, `natCast_ne_zero_zmod_two`; all over `[Field K]` |
| `GroupApproximation/CharClass/LIXKStepC.lean` | **`topChernClass_ne_zero_kzero`**, `topChernClass_ne_zero_kzero_naturality` |
| `GroupApproximation/CharClass/LIXKStepCWired.lean` | `lixKJ`, `lixKJloc`, `lixKI`, `lixK_hexact`, `lixK_mapsTo`, `lixKRho`, `lixK_hcompat`; `lixKSectionTotal`, `lixKSectionTotal_mapsTo`, `lixKSRel`, `lixKS`, `lixKSAbs`, `lixK_hnat`, `lixK_hsection`; `puncturedAcyclic_lixPoint`, `puncturedVanish_lixKZeroSet`; **`lixK_topClass_ne_zero`**, `lixK_topClass_ne_zero_odd` |

Model test: **ALL PASS**, `scratch/sp-oddside/oddside_modeltest.py` on MSI (source in this
session's scratchpad `sp/`), in *this lane's* coordinates rather than `sp-design`'s, so a
coordinate slip between the two spellings cannot hide.

| test | claim | result |
|---|---|---|
| A1–A3 | `Ψ_k` preserves every coordinate's modulus, damps to `0` at the origin, is the identity at `k = 0` | pass, `k ≤ 7`, 200 random points each |
| B1–B3 | the `k+1` roots are distinct, the Lean enumeration `ζ^j·α` equals the closed form `e^{iπ(2j+1)/(k+1)}`, each is a zero and lies on the equator | pass, `k ≤ 7` |
| B4 | **no stray zeros**: 4000 random starts refined by descent, `k ≤ 7` | pass, 0 strays |
| C1–C2 | `Ψ_k ∘ ρ_m = Ψ_k`, and `ρ_j` carries `z₀` to `z_j` | pass, `k ≤ 6` |
| D1 | **the `k+1` local derivatives of the section are literally one matrix** in the `ρ^j`-transported frames | pass, spread `≤ 1e−12`, `k ≤ 5` |
| D2–D3 | the section vanishes at each `z_j`, and each local derivative is invertible | pass; `det J = −(k+1)/32`, smallest singular value `0.5`, identical across `j` |
| E1–E2 | the count is `k+1`, and `(k+1 : F₂) ≠ 0` iff `k+1` is odd | pass |

**Two of my own tests were wrong before they were right**, and both would have read as
mathematics.  (i) I evaluated the section's derivative at circle coordinate `u = −1`; the
zero is at `u = 0` (`τ = 1/2`), and at `u = −1` the derivative degenerates to `−e₁ du` for
every `j`, so D1 passed **vacuously** — the calibration case that tells you nothing.
(ii) I asserted rank `5`; the source is 6-real-dimensional (5 sphere + 1 circle) and the
correct assertion is invertibility, rank `6`.  Both are now checked at `u = 0` with the
determinant printed.

### The structural finding, for the fleet

**The `k`-zero Step C is the one-zero Step C at a single chosen zero, plus the count.**
`γ_r = j(σ^* u)` comes from the naturality square `topClass_eq_of_naturality'`, which never
uses surjectivity of `j`; so the only place a group has to be a line — hence the only place
punctured acyclicity is consumed — is at the **distinguished** zero `z_{i₀}`, where
`ThomStepCEuler.topChernClass_ne_zero_of_su_ne_zero_line` applies character for character
with `gamma := c`, `j := j_{i₀}`, `su := x_{i₀}`.

Two consequences worth propagating:

1. **The `k+1`-point punctured vanishing is not on the critical path.**  It is proved
   anyway (`LIXKPunctured.lean`, and instantiated as `puncturedVanish_lixKZeroSet`) because
   `sp-design` §4.2 item 1 asks for it and because any arrangement that identifies `γ_r`
   through exactness rather than through the section needs it.  But this route does not
   consume it.  `sp-evenside` and `sp-endpoint` should not budget for it as a blocker.
2. **`sp-design` §4.2 item 3 can be weakened.**  The direct-sum splitting
   `H^{2r}(N, N∖Z) ≅ ⊕_i H^{2r}(N, N∖{z_i})` is more than the consumer uses.  What is used
   is the single equation `x = ∑_i ρ_i(x_i)`, with `ρ_i` the relative pullback along the
   **identity** of `N` seen as a map of pairs `(N, N∖Z) → (N, N∖{z_i})`.  The compatibility
   `ρ_i ≫ j = j_i` is then naturality of `relToAbs` along the identity and costs one
   rewrite (`lixK_hcompat`), with no biproduct and nothing to invert.

### The route to `LocalSplit`, revised (recommended, not yet built)

`sp-design` §4.2 item 3 and my own first plan both said "excision to `k+1` disjoint balls".
That route needs a metric, a disjointness argument, and the splitting of a *relative* group
over a disjoint union, none of which the tree has.  There is a route with none of that:

> **Relative Mayer–Vietoris.**  For opens `A, B ⊆ X` with `A ∪ B = X`, the sequence
> `H^n(X, A∪B) → H^n(X,A) ⊕ H^n(X,B) → H^n(X, A∩B) → H^{n+1}(X, A∪B)` has zero at both
> ends, because `A ∪ B = X` and `H^*(X, X) = 0`.  So the middle map — which is exactly
> `(a, b) ↦ ρ_A a + ρ_B b` — is an **isomorphism**.

Applied with `A = N ∖ {z_0, …, z_{k−1}}` and `B = N ∖ {z_k}`: `A ∪ B = N` because the two
puncture sets are disjoint, and `A ∩ B = N ∖ Z`.  Induction on the number of punctures then
gives `x = ∑_i ρ_i(x_i)` with the `ρ_i` exactly the ones already built here
(`lixKRho`), and the composition of two `relPullback`s along identities is again one.
**No balls, no metric, no disjoint-union splitting, no geometry at all.**

What it costs is one genuinely new piece of infrastructure: relative Mayer–Vietoris.  Having
read `CharClass/RelativeExcision.lean` in full, it is a **faithful mirror of that file** with
a biproduct in the middle, and it needs no new geometry at all:

```text
   0 ⟶ smallAnn(X; {A,B}) ⟶ C^*(X,A) ⊕ C^*(X,B) ⟶ C^*(X, A∩B) ⟶ 0
```

* **mono** — the first map is `(ι, −ι)`; injectivity is `Subtype.ext`, as in
  `excisionShortComplex_degreewise_shortExact`'s middle bullet.
* **exact** — the kernel of `(α, β) ↦ α + β` is `{(α, −α) : α ∈ C(X,A) ∩ C(X,B)}`, and a
  cochain vanishing on the `A`-simplices *and* the `B`-simplices is exactly one vanishing on
  all `{A,B}`-small chains.  The one lemma needed is
  `RelativeExcision.subordinate_or_of_isSmallSimplex`, which is already there and already
  used for the same purpose.
* **epi** — and this is the pleasant surprise: **no subdivision**.  Split `φ` on basis
  simplices by `α(σ) := if IsSubordinate A σ then 0 else φ(σ)`, `β := φ − α`.  Then `α`
  kills the `A`-simplices by construction, and `β` kills the `B`-simplices in both cases:
  if `σ ⊆ A ∩ B` then `φ(σ) = 0` and `α(σ) = 0`; if `σ ⊆ B` but `σ ⊄ A` then
  `α(σ) = φ(σ)`.  Same shape as `excisionCochainMap_preimage`'s `by_cases`.
* **acyclicity of the kernel** is `isZero_smallAnnComplex_homology`, already in the tree and
  already the only geometric input excision consumes — and it is where `A ∪ B = X` enters.

So the file is `CharClass/RelativeMayerVietoris.lean` beside `RelativeExcision.lean`,
about the same length, generic in `[CommRing R]`, and `sp-coeff` gets it for free.  It also
retires `sp-design` §4.2's "excision to `k+1` disjoint balls", which would have needed a
metric, a disjointness argument and a relative splitting over a disjoint union — none of
which the tree has.

## Since the first green (2026-09-10 afternoon)

Three things happened after the five-module green; all three are in flight, none is cited
as green yet.

**1. `sp-design`'s `p = 2` simplification, implemented.**  New file
`CharClass/LIXKStepCTwo.lean`.  Their observation is that at mod-2 coefficients
`LocalClassesAgree` needs **neither Half A nor Half B**: `H^{2r}(N; F₂)` is a line, an
`F₂`-line has a unique nonzero element, so the `k` local classes agree as soon as each is
nonzero, and each of those is the one-zero argument at `z_i`.  So the `F₂` deliverable
carries no isotopy, no naturality square along the rotation and no homotopy invariance at
all.  The file provides `eq_of_ne_zero_of_line_two`, `localClassesAgree_of_ne_zero_two`,
`localClass_ne_zero` and `topChernClass_ne_zero_kzero_two`.  It does **not** import
`RelativeLineHomotopy`, per their warning that it is mod-2-only by construction and would
have to be torn out for the odd-`p` deliverable.

I also corrected `LIXKCount`'s `LocalClassesAgree` docstring, which had cited that file.
The correct citation is `ThomStepCEuler.eq_localGenerator_of_ne_zero`.  The docstring now
records both routes and `sp-design`'s caveat on my finding 1: the **`k`-point** punctured
vanishing is off the critical path, but the **one-point** statement at every `z_i` is not,
because the `F₂` route runs the one-zero argument `k` times.  `puncturedAcyclic_lixPoint`
already supplies it at every point of the LIX base.

**2. Relative Mayer–Vietoris, authored.**  New file `CharClass/LIXKRelativeMV.lean`,
namespace `GroupApproximation.CharClass.LIXKRelMV`, generic in `[CommRing R]`.  Reading
`RelativeExcision.lean` in full turned the "one new piece of infrastructure" into something
smaller than expected, and the `epi` half needs **no subdivision at all**:

* `relKeep A` is the idempotent on chains keeping the `A`-simplices, built from the tree's
  own `relRetract` and `singularChainMap`, both already generic in the ring;
* `splitKeep φ := relKeep A ≫ φ` lies in `C^n(X, B)` whenever `φ ∈ C^n(X, A ∩ B)`, and
  `splitDrop φ := φ − splitKeep φ` lies in `C^n(X, A)` for any `φ` at all;
* the two halves are not cocycles, but `δ(splitDrop φ) = −δ(splitKeep φ)`, so that
  coboundary vanishes on every `{A,B}`-small simplex, and `smallAnnComplex_acyclic` — the
  single geometric input, the same one excision consumes, and the only place `A ∪ B = X`
  enters — corrects both halves at once.

`exists_relCocycle_split_of_acyclic` takes the acyclicity as a hypothesis and is generic;
`exists_relCocycle_split` is the `ZMod 2` instance, discharged by
`CupVanishSmallAnn.exists_smallAnn_preimage`.  The hypothesis disappears when `sp-coeff`
generalises `RelativeSmallChains`.

What remains between this and `LocalSplit`, precisely, so the next resume does not have to
re-derive it:

1. **A relative cocycle-class API.**  The tree has the absolute one and it is already
   generic — `CoeffCohomology.cocycleClassK`, `cocycleClassK_surjective`,
   `iCycles_cyclesMkK`, `cyclesMk_iCyclesK` — and there is **no relative analogue**.  The
   relative complex is `relCochainComplex R X A`, whose homology *is* `relCohomology R X A`,
   so the analogue is a faithful mirror of that file: `relCocycleClass` built from
   `homologyπ ∘ cyclesMk`, plus its surjectivity.  Roughly 60–100 lines, no new mathematics.
   This is **not** what `sp-coeff` is doing (they are changing coefficients, not adding an
   API), so it does not collide with their work.
2. **The two-set statement on classes.**  With 1, `exists_relCocycle_split` gives
   `x = ρ_A a + ρ_B b` directly, because `ρ_A` on cochains is the inclusion
   `C^n(X, A) ↪ C^n(X, A ∩ B)` and so sends `[α]` to `[α]`.
3. **The induction on the punctures.**  `A := N ∖ {z_0, …, z_{k−1}}`, `B := N ∖ {z_k}`; the
   two puncture sets are disjoint so `A ∪ B = N`, and `A ∩ B = N ∖ Z`.  Composites of
   `relPullback` along identities are again `relPullback` along the identity, so the `ρ_i`
   that come out are the ones `LIXKStepCWired.lixKRho` already defines.

**2b. `LIXKStepCTwo` is GREEN.**  Log
`cc_clones/spare2/.lake/laneprobe-20260910-125237.log`:
`ℹ [8855/8878] Built GroupApproximation.CharClass.LIXKStepCTwo (145s)`, with
`eq_of_ne_zero_of_line_two`, `localClassesAgree_of_ne_zero_two` and
`topChernClass_ne_zero_kzero_two` each printing exactly
`[propext, Classical.choice, Quot.sound]`.  It compiled on the first attempt.

**3. The `ChernTotalRing` blocker is a second-order stale artifact, not a source break.**
After the purge that `laneprobe.sh` now runs, spare2 still held
`SteenrodCupOne.olean` from 09-05 22:37 beside a `CohomologyBasic.olean` rebuilt today at
12:10.  `ChernTotalRing` imports both, so it was elaborated against the new generic `cup`
and an old `cup_comm` compiled against the `cup` that no longer exists — which is why the
error prints as `cup_comm a b has type cup = cohCast`.  The purge rule misses it because
`SteenrodCupOne.lean` itself has not changed; the correct predicate is transitive, an olean
is stale if it predates the olean of any of its **imports**.  Reported to the lead, who has
put the transitive rule into `laneprobe.sh`; its first run reported
`purged 2538 stale artifact sets (source-newer=0, import-newer=2538) of 3308 oleans`, which
is the size of the problem the old rule was missing.

**Confirmed** in `laneprobe-20260910-125237.log`:
`✔ [8826/8878] Built GroupApproximation.CharClass.ChernTotalRing (77s)` once
`SteenrodCupOne`'s artifacts were deleted.  sp-coeff's sources were never at fault.

**4. `LIXKStepCWired`'s own first errors, and they were one root cause.**  With the foreign
blocker gone the file finally elaborated and produced `Unknown identifier absPull` at four
call sites.  `absPull`, `absPull_id_eq` and `absPull_comp` live in
`GroupApproximation.CharClass.RelativeSupport`; the existing consumers use them unqualified
only because those files open that namespace themselves.  Qualified and re-probing.  The
`sorryAx` lines in that log are error recovery, not a `sorry`: the lexical scan is still
clean at 0 hits across all eight files.

## NEEDS

* **`sp-coeff` (BLOCKING, and the only thing between this lane and a complete first
  deliverable)**: `CharClass/ChernTotalRing.lean` is red at line 94 —
  `cup_comm a b` elaborates against a different `cup` than the `⌣` in the goal, which is
  the coefficient generalisation half-landed.  It is in `LIXKStepCWired`'s closure through
  `LIXStepCOddRelative → LIXBundlePair → LemmaTwoStepC → LemmaTwoTopClass`, and `lake`
  aborts the whole build on it, so my sixth file cannot be compiled at all.  Everything
  below `ThomStepCEuler` is unaffected — `LIXKStepC` built at job 8876, after the failure.
* **`sp-powers`**: `Analysis/LIXPowersGauge`, `LIXPowersNaturality`, `LIXPowersJoinPower`
  to stay green — my `CharClass/LIXKMap.lean` imports the third for `Powers.joinC`.  If you
  rename or move `joinC`, tell me; I use `joinC`, `joinC_zero`, `joinC_id`, `norm_joinC`,
  `continuous_joinC` and nothing else.
* **`sp-powers`**: eventually, the bridge lemma identifying *your* `joinPow e₁ e₂ k` on the
  equatorial `EuclideanSpace ℝ (Fin 5)` with *my* `psiVec k = Function.update x 0 (joinC k (x 0))`
  on `Fin 3 → ℂ` across `LIXLemmaSixGenerator.equatorEmb`.  Neither of us needs it for our
  own first deliverable; **Step A does**, because Step A must produce
  `G *ᵥ (e₁,0) = (Ψ_k x, 0)` — my `hGe` binder — for the *same* `Ψ_k` that your clutching
  naturality pulls back.
* **`sp-coeff`**: relative homotopy invariance over a field `K` (their item 1 /
  `sp-design` §4.4).  Not blocking at `p = 2`; blocking for the second deliverable and for
  `LocalClassesAgree` at odd `p`.
* **`sp-design`**: a ruling on whether the local model at `−e₁` should be done as
  `LIXSectionChart` reindexed (`Fin 3` relabelling) or as their §1.3 generic form
  (a unit vector `a` with `Re (a n) = 0` plus an ℝ-linear isometry `L` onto `a^⊥`).  I
  recommend the generic form and will write it that way unless told otherwise; it is what
  `sp-tower`'s general `n` needs too, and the `![…]` literal has no analogue there.
* **`sp-tower`**: the `Gen` shape layer for `VIdx`/`baseM` at general `n`.  Not blocking:
  I write against the `n = 2` shape layer as it is, but never against `e₃` or the south
  pole of the sphere — the zeros are `−e₁`'s rotates, on the equator.

### Owed cleanup

`set_option linter.unusedSimpArgs false` is set at file scope in `LIXKMap`, `LIXKSection`,
`LIXKPunctured` and `LIXKStepCWired`.  It is a **deliberate, temporary** guard, not a
finding: under `-DwarningAsError=true` an unused `simp` argument is a hard error, the first
probe of `LIXKMap` failed on exactly one (`mul_assoc` in a three-element list), and without
a compiler I cannot tell which of the remaining `simp only` lists are redundant.  Once the
files are green the suppression comes out and the flagged arguments get deleted.  Two
shapes to look for when doing that: a lemma already carrying `@[simp]` passed explicitly,
and `fin_cases i <;> simp [a, b, c]`, which is *three* `simp` calls and is flagged if any
branch does not use all three.

## TRAPS

* `Analysis/LIXPowersJoinPower.lean`'s `joinPow` is **not usable at `Fin 3 → ℂ`**: it is
  built from `planeSub`, which needs `InnerProductSpace ℝ E`, and the LIX five-sphere is a
  sup-normed pi type with no such instance.  The scalar `joinC` is the shared part and the
  only shared part.  Reaching for `joinPow` and then trying to supply the instance lands in
  `EuclideanSpace`/`WithLp` transport, which `LIXSectionChart.lean`'s header already records
  as the trap that file exists to avoid.
* `LocalSplit` and `LocalClassesAgree` are `def`s returning `Prop`, so `rw [hsplit]` does
  **not** fire: `rw` matches `Eq` only up to *reducible* transparency and a plain `def` is
  not reducible.  Convert first (`have hs : x = ∑ … := hsplit`), which typechecks by defeq
  at default transparency.  The same trap will bite any lane that names an obligation as a
  `def` and then tries to rewrite with it — which the program note's "statements before
  proofs" rule makes likely.  Appended to `notes/lix-lane-reports/FLEET_TRAPS.md`.
