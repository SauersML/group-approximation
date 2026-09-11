# Lane `sp-descent` — the degree-one normalisation constant `λ₁ = ((p−1)/2)!`

Owner of `GroupApproximation/CharClass/OddPDescent*.lean`.  One deliverable: the constant
of the odd-primary Steenrod construction at degree one, proved in Lean **generic in the odd
prime `p`**, with the sign convention derived and stated, and its unit-ness.

Sources read in full before authoring: `notes/LIX_STRONGER_PROGRAM_2026-09-10.md`;
`sp-design.md` §"Model tests for the lead (b) The descent", §"The descent needs no cone
operator", §"κ(1,1), and `c_2` computed directly"; `sp-steenrod.md` §3 (the tuple model),
§11a (the sign contract), §11b (the `Δ¹` descent at lemma precision), §12; their landed files
`CharClass/OddPGroupRing.lean`, `OddPResolution.lean`, `OddPSign.lean`, `OddPTuple.lean`,
`OddPTupleSign.lean`, `OddPNorm.lean`; `notes/lix-lane-reports/FLEET_TRAPS.md`.

---

## PLAN (2026-09-10, within the first hour)

Model tests (all on MSI, never locally), copied into
`notes/lix-stronger-lane-reports/tools/`: `descent_ext.py` (the exterior re-description
against `sp-design`'s word model, the descent over `ℤ` and mod `p`, the dual descent, the
domino closed form), `descent_lemmas.py` (every identity the Lean proof states, on every
basis element), `check_general.py` (the two identities that quantify over `T`-invariant
inputs).  Node copies under
`/projects/standard/hsiehph/sauer354/nonsofic_existence/scratch/sp-descent/`.

### 0. The mathematical route, settled by model test before any Lean

`sp-design`'s descent runs in the two-letter complex `E⁰ = ⟨f⟩`, `E¹ = ⟨g⟩`, `δf = g`, on
`E^{⊗p}`: `2^p` words, every operator preserving it.  **The whole of `E^{⊗p}` with its four
operators is the exterior algebra `Λ(ξ_0, …, ξ_{p−1})`**, and this re-description is what
makes a generic-in-`p` proof possible.  Under the dictionary

```text
    word w   <->   e_S ,   S = { j : w_j = g }      (f degree 0, g degree 1)
```

* `D` (the Koszul tensor differential, sp-steenrod's convention: the prefix sign is the
  total degree of the slots strictly before the differentiated one) is **left
  multiplication by `σ := ξ_0 + ⋯ + ξ_{p−1}`**;
* `H = h ⊗ 1^{⊗(p−1)}` is **the left partial derivative `∂/∂ξ_0`**;
* `T` (sp-design's cyclic shift, slot `0` to the end, sign `(−1)^{d₀(k−d₀)}`) is **the
  graded algebra automorphism `ξ_j ↦ ξ_{j−1 mod p}`**;
* `N = Σ_k T^k`.

VERIFIED (model, `scratch/sp-descent/descent_ext.py`, §0): the four operators of the
exterior description agree with a direct re-implementation of sp-design's word model on
**every** basis element at `p = 3, 5, 7` — `0` mismatching pairs.  In this language
`D∘D = 0` is `σ∧σ = 0` and `DH + HD = 1` is the derivation identity `∂_0(σx) + σ∂_0(x) =
(∂_0σ)x = x`.

### 1. What the constant is, and the closed form that proves it

Put `m := (p−1)/2`, `R := ` multiplication by the **cyclic domino element**
`ρ := Σ_{a ∈ ℤ/p} ξ_a ∧ ξ_{a+1}`.  Two sequences:

```text
    primal (the descent)   B_0 = ξ_0∧⋯∧ξ_{p−1},   B_{k+1} = (T−1) ∘ ∂_0 ∘ N ∘ ∂_0 (B_k)
    dual   (built upward)  X_0 = ξ_0,             X_{k+1} = ξ_0∧ N (ξ_0∧ (T^{-1}−1) X_k)
```

`λ₁ = ⟨B_m, ξ_0⟩`.  The three facts:

1. **`X_k = ξ_0 ∧ ρ^k`.**  Two lines: `T^{-1}ρ = ρ` and `T^{-1}ξ_0 = ξ_1`, so
   `ξ_0∧(T^{-1}−1)X_k = ξ_0∧ξ_1∧ρ^k`; then `N(ξ_0ξ_1ρ^k) = (Σ_j T^jξ_0ξ_1)·ρ^k = ρ·ρ^k`
   because `T` is an algebra map and `ρ` is `T`-invariant; wedge `ξ_0` back.
2. **Adjointness.**  `⟨B_{k+1}, X_t⟩ = ⟨B_k, X_{t+1}⟩`, from `⟨∂_a u, v⟩ = ⟨u, ξ_a∧v⟩`,
   `⟨Tu,v⟩ = ⟨u,T^{-1}v⟩`, `⟨Nu,v⟩ = ⟨u,Nv⟩`.  Hence `λ₁ = ⟨B_m, X_0⟩ = ⟨B_0, X_m⟩`,
   the `ω`-coefficient of `ξ_0∧ρ^m`.
3. **`[e_{\{i,…,i+2k−1\}}] ρ^k = k!`** for `1 ≤ i`, `i+2k ≤ p`, by induction on `k`:
   `∂_i ρ^k = k·ρ^{k−1}(ξ_{i+1} − ξ_{i−1})`, the `ξ_{i−1}` term misses the interval, and
   `ξ_{i+1}∧` peels the next letter.  At `i = 1`, `k = m` this is `λ₁ = m!`.

**No domino combinatorics and no tiling-uniqueness argument survives into the Lean**: the
`k!` comes out of the derivation identity `∂_iρ^k = kρ^{k−1}(…)`, not out of counting.

### 2. The sign convention, derived

* **Evaluation.**  The `p`-fold Alexander–Whitney diagonal of `ι₁` has exactly **one** term
  with no vertex-`0` factor, namely `([01], [1], …, [1])` (VERIFIED, model, all cut
  sequences enumerated at `p = 3,5,7`), so the pairing reads off the coefficient of the
  single word `g ⊗ f^{⊗(p−1)}`.  That word has degrees `(1,0,…,0)`, so the Koszul
  evaluation sign `(−1)^{Σ_{i<j}|u_i||u_j|}` is `(−1)^0 = +1` **and** sp-steenrod's
  contract ("evaluation carries no sign", §11a item 3) gives `+1`.  The two conventions
  agree here, so no sign is owed:  **`λ₁ = ((p−1)/2)!`, with no sign factor.**
* The `(−1)^{(p−1)/2}` in the launch message is **`κ(1,1)`, not a sign on `c₁`** — it is
  the Cartan coefficient at the top corner, and `c₂ = κ(1,1)·c₁²`.  sp-design's own table
  (report, "The numbers") lists `c_1 = λ_1 = 1, 2, −1, −1, 5`, which is `((p−1)/2)!` mod `p`
  with **no** sign at `p = 3,5,7,11,13`, agreeing with their `Δ¹` descent.  Recorded so
  nobody inserts a sign that is not there.
* **The direction of the cyclic generator is load-bearing** and must be pinned: see TRAPS.

### 3. File plan

| file | contents |
|---|---|
| `OddPDescentWord.lean` | the alphabet, `EWord`/`EMod`, `eDeg`, `ePre` (sp-steenrod's `tupPre` shape), `eWedge a` (= `ξ_a ∧ −`) and `ePart a` (= `∂/∂ξ_a`), the prefix-update lemmas |
| `OddPDescentClifford.lean` | `eWedge a ∘ eWedge a = 0`, anticommutation, `ePart a ∘ eWedge b + eWedge b ∘ ePart a = δ_{ab}` |
| `OddPDescentComplex.lean` | `eD = Σ_a eWedge a`, `eH = ePart 0`, **`eD∘eD = 0`** and **`eD∘eH + eH∘eD = 1`** (deliverable 1) |
| `OddPDescentShift.lean` | `eT`, `eTinv`, `eT^p = 1`, `eT ∘ eWedge a = eWedge (a−1) ∘ eT`, `eT ∘ eD = eD ∘ eT` |
| `OddPDescentNorm.lean` | `eN = Σ_{k<p} eT^k`, `eN ∘ (eT − 1) = 0` (the shape of `grNorm_mul_grS`), `eN ∘ eD = eD ∘ eN` |
| `OddPDescentChain.lean` | the descent `eA`, `eY = eH (eA)`, `eA` a cocycle and `eY` a primitive at every level over `ZMod p` (deliverable 2) |
| `OddPDescentPairing.lean` | the pairing and the three adjunctions |
| `OddPDescentDomino.lean` | `eR`, its commutations, `X_k = ξ_0∧ρ^k`, the interval coefficient `= k!` |
| `OddPDescentValue.lean` | **`λ₁ = ((p−1)/2)!`** (deliverable 3) and **`IsUnit λ₁`** in `ZMod p` (deliverable 4) |

Vocabulary borrowed, never redefined: `grGen`/`grS`/`grNorm` and `grNorm_mul_grS`
(`OddPGroupRing.lean`), `even_pred_of_odd`/`neg_one_pow_mul_pred` (`OddPSign.lean`), the
`tupPre` prefix-sign recipe and the `abbrev`-not-`def` index rule (`OddPTuple.lean`).

---

## GREEN (with job counts)

**PROBE GREEN (`thm-d`, 2026-09-10):** `GroupApproximation.CharClass.OddPDescentWord`,
`…OddPDescentClifford`, `…OddPDescentComplex` — `Built` lines for all three in the cited
log, `purged 0 stale artifact sets`.  The remaining four modules are in the build-fix loop
(see AUTHORED); no `sorry` anywhere in the lane
(`grep -rn sorry GroupApproximation/CharClass/OddPDescent*.lean` is empty).

Nothing of this lane may be landed as a batch until the four remaining modules are green and
a single log carries a `Built` line for each of the seven, taken after deleting this lane's
own artifacts (fleet rule "Built, never Replayed").

## AUTHORED, UNVERIFIED

Seven new files, all under the lane's `OddPDescent*` prefix, nothing outside it touched.

| file | contents | state |
|---|---|---|
| `OddPDescentWord.lean` | `ELetter`/`EWord`/`EMod`, `eDeg`, `ePre` (= `tupPre` for this alphabet), the two prefix-update lemmas, `eWedge a` (= `ξ_a ∧ −`), `ePart a` (= `∂/∂ξ_a`), `eMod_ext` | **GREEN** |
| `OddPDescentClifford.lean` | `eWedge a ∘ eWedge a = 0`, `eWedge_anticomm`, `ePart_eWedge_self`/`ePart_eWedge_of_ne` (the CAR relation) | **GREEN** |
| `OddPDescentComplex.lean` | `eD = Σ_a eWedge a`, `eH = ePart 0`, **`eD_comp_eD`** and **`eD_comp_eH_add`** (deliverable 1) | **GREEN** |
| `OddPDescentShift.lean` | `Fin p` shift arithmetic, `eRot`, `eSgn`, `eT`, **`eT_pow_card : eT^p = 1`**, **`eT_comp_eWedge`**, `eT_comp_eD`; `eN`, `eN_mul_eT_sub_one`, `eT_mul_eN`, `eN_comp_eD` | fixing |
| `OddPDescentPairing.lean` | `ePair`, `eAdj` and its composition rules, `eAdj_ePart_eWedge`, `ePair_eT_eT` (the shift is an isometry), `eAdj_eT`, `eAdj_eN` | not yet elaborated |
| `OddPDescentDomino.lean` | `eR = ρ ∧ −`, its commutations, `ePart_eR_pow_apply` (the derivation identity), coefficient extraction, interval words, **`eR_pow_interval : ⟨ρ^k, e_I⟩ = k!`**, `eN_eWedge_zero_one` | not yet elaborated |
| `OddPDescentValue.lean` | the descent `eA`/`eY1`/`eMid`/`eY2`, **`eD_eA`/`eD_eY1`/`eD_eY2`** (deliverable 2), the dual sequence `eX`, `eAdj_eRound`, `eX_succ`, **`eDescent_value`** (deliverable 3), **`eDescent_value_isUnit`** (deliverable 4), the `EvalIsHeadCoeff` obligation, `#audit_axioms` on all of them | not yet elaborated |

The headline statements as authored:

```lean
theorem eDescent_value (m : ℕ) (hm : p = 2 * m + 1) (hp : 1 < p) :
    (eA K m) (eHeadWord p) = (Nat.factorial m : K)

theorem eDescent_value_isUnit (m : ℕ) (hprime : p.Prime) (hm : p = 2 * m + 1) :
    IsUnit ((Nat.factorial m : ZMod p))

theorem eD_eA (hp : 1 < p) (hodd : Odd p) (hchar : (p : K) = 0) (k : ℕ) :
    eD K (eA K k) = 0
```

The value theorem carries **no** characteristic hypothesis: it holds over an arbitrary
commutative ring, because the composite `((T−1)∘∂_0∘N∘∂_0)^m(ω)` has `ξ_0`-coefficient the
integer `m!` on the nose.  Only the descent's *interpretation* — `eD_eA` and the two
primitive statements — needs `Odd p` and `(p : K) = 0`.

## NEEDS

* From `sp-steenrod`: nothing blocking.  `tupT` is **not landed**
  (`grep -rn tupT GroupApproximation/` returns nothing; it is only in their report §3.2), and
  their planned convention there reads the sign off the **last** slot, which is the
  **inverse** of `sp-design`'s `T`.  Sent by SendMessage with the measured table below.  My
  files define `eT` explicitly in `sp-design`'s direction and pin it in the docstring, so
  nothing of mine changes whichever they land; but a transcription of "(T−1)" from this lane
  into their vocabulary must be inverted if they take the last-slot sign.
* Nothing from `sp-coeff`: this lane is generic in `K` from the start and never touches
  `Hmod`, cup products or the cochain layer.  Deliberate: importing `OddPTuple.lean` would
  pull the whole vendored cochain tower into every probe of this lane for zero mathematical
  content — the descent is finite linear algebra in `2^p` words and reaches the singular
  tensor power only by functoriality of `E → C^*(X)`.
* **One obligation is stated but not discharged here**: `EvalIsHeadCoeff`, that the `p`-fold
  Alexander–Whitney evaluation of a degree-one element of `E^{⊗p}` is the coefficient of
  `eHeadWord`.  It is VERIFIED (model) at `p = 3, 5, 7` by enumerating every cut sequence,
  and it is what makes `eDescent_value` a statement about `λ₁`; it needs `tupEval` and the
  iterated diagonal, which live in `sp-steenrod`'s layer.  No theorem of this lane rests on
  it — `eDescent_value` is the coefficient statement itself.

## TRAPS

* **(sp-descent, 09-10) The direction of the cyclic generator changes the constant, and only
  one direction gives `((p−1)/2)!`.**  Running the identical descent with `T` replaced by
  `T^{-1}` (a consistent relabelling of the generator of `ℤ/p`; `N` is unchanged) gives

  | p | 3 | 5 | 7 | 11 |
  |---|---|---|---|---|
  | `(T−1)`, sp-design's `T` (slot 0 to the END, sign `(−1)^{d₀(k−d₀)}`) | 1 | 2 | 6 | 10 |
  | `(T^{-1}−1)` | 2 | 2 | 1 | 1 |
  | `((p−1)/2)!` mod p | 1 | 2 | 6 | 10 |

  (`p = 13` re-checked separately: `c₁ = 720 = 6!` over `ℤ`, `= 5` mod `13`, and
  `x_k = k!·X_k` at every `k ≤ 6`.)

  Both are units, so the programme is safe either way, but **`λ₁ = ((p−1)/2)!` is a theorem
  about sp-design's direction only**.  The asymmetry is real: `H = ∂/∂ξ_0` and the
  Alexander–Whitney evaluation both single out slot `0`.  VERIFIED (model).
* **(sp-descent, 09-10) The `A_j` are cocycles only mod `p`, and the step that needs the
  characteristic is not the one you expect.**  It is the **first**:
  `D A_1 = N D Y_1 = N(ω) = p·ω`, because `ω` is `T`-invariant — not `N(T−1) = 0`, which
  holds over `ℤ`.  Over `ℤ` the descent's cocycle and primitive assertions are all false at
  every level while the *value* of the composite is the integer `m!` on the nose
  (`1, 2, 6, 120, 720` at `p = 3,5,7,11,13` — `((p−1)/2)!` on the nose, not merely mod `p`).  Value theorem and descent interpretation are therefore
  separate theorems with separate hypotheses.
* **(sp-descent, 09-10) The forward descent has no closed form; the adjoint one does.**
  `sp-design`'s `p = 13` run has intermediate supports `1, 12, 11, 100, 81, 288, 196, 336,
  175, 140, 45, 12`.  Read against the basis pairing the same computation is
  `X_k = ξ_0 ∧ ρ^k` with `ρ = Σ_a ξ_a ∧ ξ_{a+1}`, two lines per step.  General lesson: when a
  descent's terms look structureless, transpose it before looking for a pattern.
* **(sp-descent, 09-10) A Koszul cancellation stated as a disjunction is a trap.**  I wrote
  "the two exponents differ by one, in one order or the other" as `A + 1 = B ∨ B + 1 = A` and
  picked the wrong disjunct in one branch.  Both orders of `a`, `b` in
  `∂_a ξ_b + ξ_b ∂_a = 0` give the **same** disjunct, because the operator that moves the
  prefix is `∂_a` in one case and `ξ_b` in the other.  Cost: one probe; `omega`'s
  counterexample listed the atoms with no relation between them, which reads like a missing
  hypothesis rather than a wrong goal.
* **(sp-descent, 09-10) Five build traps, all recorded in `FLEET_TRAPS.md`:** the `ℕ → Fin p`
  coercion is a **scoped** instance (`open Fin.NatCast`, and the failure reads as a bare type
  mismatch with no instance mentioned, while `(0 : Fin p)` in the same statement is fine);
  `omit [inst] in` must come BEFORE a docstring, not between it and the theorem;
  `LinearMap.mul_apply`/`one_apply` are `Module.End.mul_apply`/`one_apply`;
  `Mathlib.Algebra.GeomSum` does not exist (it is `Mathlib.Algebra.Ring.GeomSum`); and
  `abel`/`push_cast` are not in scope from the `Finsupp`/`Fin`-interval imports while
  `ring`/`omega` are.  Together they cost five probes, almost all of it in cascades: a
  missing tactic `sorry`s its declaration and the twenty downstream errors each look like a
  different problem.
* **(sp-descent, 09-10) Rewriting the CONDITION of an `ite` with a `Prop` equality makes the
  motive ill-typed** (the `Decidable` instance travels with the condition).  Prove the
  equality of the two whole `ite` terms by `by_cases` + `if_pos`/`if_neg` and rewrite that.
