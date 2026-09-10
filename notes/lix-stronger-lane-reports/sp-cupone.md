# Lane `sp-cupone` — signed cup-1 and graded commutativity over `K`

Program note: `notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5 (first bullet, the owned
item of 12:35).  Clone: `thm-e`.  Owns: `GroupApproximation/CharClass/CupOne*.lean`
(new files only; nothing existing is edited, and the `F₂` `Steenrod*` files stay
untouched).

## 0. The derivation (done first, per §3 "Lean only after solving")

### 0.1 What the `F₂` tree has, and exactly where characteristic two enters

`SteenrodCupOne.cup_comm` descends from `SteenrodCoboundary.cochainCupI_coboundary`,
which is Steenrod's cup-`i` coboundary formula **without signs**.  The whole
development is already generic in the coefficient ring except in four places:

| file | line | char-2 step |
|---|---|---|
| `SteenrodCochain.faceVal_coboundary` | 165 | `neg_one_pow_zmod2` kills the sign `(-1)^i` of the coboundary through a face |
| `SteenrodCoboundary.cochainCupI_coboundary` | 217 | `neg_one_pow_zmod2` kills the sign `(-1)^k` of the ambient coboundary |
| `SteenrodCoboundary.cut_coboundary_master` | 101 | `char2_move h2` moves a term across a sum |
| `SteenrodCutCancel.cut_insert_cancel` / `telescope_char2` | 297 / 285 | `Ξ j + Ξ (j+1)` telescopes only because `x + x = 0` |

Everything else — `cutU`, `cutV`, `cutLow`, `cutHigh`, the eight `insert` lemmas,
`cutU_map_succAbove`, `sum_cutIndex_map`, `sum_cutIndex_succ_erase`,
`sum_compl_swap`, `sum_erase_split` — is **sign-free `Finset` combinatorics and is
reused verbatim**.  `cochainCupI` itself is already `{R : Type} [CommRing R]`
(`SteenrodCochain.lean:210`), and so is `cochainCupI_zero`
(`SteenrodCupEdge.lean:87`), the identification of `⌣₀` with the vendored
Alexander–Whitney `cochainCup`.  So this lane adds signs; it does not redo
combinatorics.

### 0.2 The sign, derived not guessed

Attaching an unknown sign `ε(S)` to each cut and **fixing the two Leibniz
coefficients at `1` and `(-1)^a`** so that the formula agrees with
`CoeffLeibniz.aw_cochain_leibniz` (`δ(φ ⌣ ψ) = δφ ⌣ ψ + (-1)^p φ ⌣ δψ`), the
coboundary formula becomes a **linear** system in the `ε` and in the two
coefficients of the low terms.  Solved exactly over `ℚ` for every bidegree
`0 ≤ a, b ≤ 5` at once (the system couples `(a,b)`, `(a+1,b)`, `(a,b+1)`, so the
whole rectangle is one system), normalised by `ε = 1` at `a = b = 1`:
**consistent, unique, every value `±1`**.  Script `scratch/sp-cupone/cupone_signs.py`
on MSI; 5678 equations, 100 unknowns, no free parameters.

The fit, and the form this lane uses, is stated **without reference to the
bidegree** — which is what makes the Lean proof uniform (see §0.4):

```text
cutExp S := ((cutU S).card + 1) * (cutV S).card + ∏ c ∈ S, (c : ℕ)
cupOneSign K S := (-1 : K) ^ cutExp S
```

On the cuts that survive (`|cutU S| = a+1`, `|cutV S| = b+1`, `S = {c₀ < c₁}`) this
is `(-1)^(a + a*b + c₀*c₁)`, which is the closed form the solver produced.

### 0.3 The formula

```text
δ(α ⌣₁ β) = δα ⌣₁ β + (-1)^a (α ⌣₁ δβ) + (-1)^n (α ⌣ β) + (-1)^(a+b+ab) (β ⌣ α)
```

with `α` of degree `a`, `β` of degree `b`, the left cup-1 at literal output degree
`n`, every right-hand term at literal degree `n + 1`, and **no degree cast
anywhere** (the free-output-degree device of `SteenrodCut.lean` is kept).

For cocycles the two derivative terms die and, since `n = a + b - 1` on the only
degree where anything is nonzero,

```text
α ⌣ β - (-1)^(a*b) (β ⌣ α) = (-1)^(a+b+1) δ(α ⌣₁ β),
```

so `[α ⌣ β] = (-1)^(ab) [β ⌣ α]`.  Sanity: the two low coefficients satisfy
`s₄ = -s₃·(-1)^{ab}` at every bidegree tested, which is exactly the statement that
the pair is `±(α ⌣ β - (-1)^{ab} β ⌣ α)`.  A first recollection of Steenrod's
printed formula had the **opposite** sign on the `v ⌣ u` term, which would give
`u ⌣ v = -(-1)^{pq} v ⌣ u`; the solver rejected it.  This is why the model test came
first.

### 0.4 Why the sign is stated through the face cardinalities, not through `(a,b)`

The `F₂` proof never case-splits on degree: off-degree every term is `0` by
`faceVal`, and the identity is proved termwise.  A sign written as `(-1)^{a+ab+c₀c₁}`
would make the termwise identity **false** off-degree, forcing a case split
through the whole proof.  Written as `cutExp`, the two termwise sign identities the
proof needs hold for *every* cut and *every* vertex, unconditionally:

```text
(i)  k ∈ cutU T \ T :  k + cutExp S ≡ cutExp T + cutRank (cutU T) k                 (mod 2)
(ii) k ∈ cutV T \ T :  k + cutExp S ≡ ((cutU T).card - 1) + cutExp T + cutRank (cutV T) k
```

where `S` is the cut of the small simplex with `S.map (succAbove k) = T`.  Verified
for every 2-cut and every outside vertex up to `n = 8`
(`scratch/sp-cupone/cupone_verify.py`, `OVERALL: GREEN`).  Both are linear once the
three positions of `k` relative to `T = {t₀ < t₁}` are separated: the `∏` terms
cancel or shift by a linear amount, and the two `(card+1)*card` terms differ by a
single factor.  This is the whole content of the sign bookkeeping.

The one place a degree hypothesis is still needed is the **leftover** (the terms
where the deleted vertex *is* a cut point), which telescopes to the two low terms;
there the `(β ⌣ α)` coefficient is `s`-dependent until one uses `|cutV S| = a+1`,
i.e. `s = b`.  That is one `by_cases` on a cardinality, inside a `Finset.sum_congr`,
in the idiom `faceVal` already uses.

### 0.5 The telescope, signed

`cut_insert_cancel`'s `Θ (cutLow S t) (cutHigh S t)` becomes `Ξ t := ω t • Θ …` and
`Σ (Ξ j + Ξ (j+1)) = Ξ 0 + Ξ N` becomes `Σ (Ξ (j+1) - Ξ j) = Ξ N - Ξ 0`.  The
weights were computed by hand and cross-checked against the solver:

```text
ω t = (-1)^(n(1+s+t) + t·s + t + 1)   for t ≤ s          (S = {s} a singleton cut)
ω t = (-1)^(n(t+s) + t·s + 1)         for t ≥ s + 1
ω s = ω (s+1) = (-1)^(n+1)            (the two branches meet, so the c = s term drops)
ω N = (-1)^(n+1),  ω 0 = (-1)^(n + n·s + 1)
```

`ω s = ω (s+1)` is what replaces `x + x = 0` in `telescope_char2`: the term at the
*old* cut point vanishes because `cutLow S (s+1) = cutLow S s` **and** the weights
agree, not because 2 = 0.

## 1. Files (all new, prefix `CupOne`)

| file | contents | imports |
|---|---|---|
| `CharClass/CupOneSign.lean` | `cutExp`, `cupOneSign`, the pair description of `cutU`/`cutV`/cards, the two termwise sign identities (i),(ii), the telescope weights | `SteenrodCutCancel` |
| `CharClass/CupOneCochain.lean` | signed `faceVal_coboundary`, `cochainCupOne`, bilinearity, off-degree vanishing, naturality | `CupOneSign`, `SteenrodCochain` |
| `CharClass/CupOneCoboundary.lean` | the signed master identity and the coboundary formula of §0.3 | `CupOneCochain`, `SteenrodCupEdge` |
| `CharClass/CupOneComm.lean` | `cup_comm_signed`, `cup_comm_of_even` over `K` | `CupOneCoboundary`, `CoeffCohomology`, `CohomologyAssoc` |
| `CharClass/CupOneTotal.lean` | `TotalH.IsEven`, closure under `+`, `*`, `map`, `mul_comm_of_even` | after `sp-coeff`'s `ChernTotalRing` over `K` |

## 2. Obligations, as named `Props` with docstrings (landed before discharged)

* `SignedCutMaster` — the signed replacement for `cut_coboundary_master`.
* `SignedFaceCoboundary` — `faceVal (a+1) (δα) τ A = Σ_{c ∈ A} (-1)^{cutRank A c} faceVal a α τ (A.erase c)`.
* `CupOneCoboundaryFormula` — §0.3.
* `CupCommSigned` — `cup a b = (-1)^(p*q) • cohCast (Nat.add_comm q p) (cup b a)`.
* `CupCommOfEven` — the corollary the program actually consumes.

## 3. Convention alignment

Fixed by `CoeffLeibniz.aw_cochain_leibniz` (`δ(φ ⌣ ψ) = δφ ⌣ ψ + (-1)^p φ ⌣ δψ`),
which is the two-variable Koszul convention `sp-steenrod`'s `OddPSource.lean:25`
uses on the tensor half (`d(e_i ⊗ σ) = d_W e_i ⊗ σ + (-1)^i (e_i ⊗ ∂σ)`).  The
coefficient argument follows `sp-coeff` §0c: **implicit** wherever a class or
cochain determines it, **explicit and first** otherwise.  `sp-steenrod` asked to
confirm the two-variable placement; message sent.

## GREEN (with job counts)

- nothing yet; first probe of `CupOneSign` was FAILED (four errors, both causes below),
  fixed, re-probing the whole chain.

## AUTHORED, UNVERIFIED

All five files are written; the sign derivation and the coboundary formula are
model-verified, the Lean is not yet green.

| file | contents |
|---|---|
| `CharClass/CupOneSign.lean` | `cutExp`, `cupOneSign`, the pair description of `cutU`/`cutV`/cards/ranks, the two termwise sign identities |
| `CharClass/CupOneCochain.lean` | `cutRank_orderEmbOfFin`, the **signed** `faceVal_coboundary`, `cochainCupOne` and its zero/off-degree lemmas, three generic restatements |
| `CharClass/CupOneInsert.lean` | `mul_self_mod_two`, `cutExp_pair_mod_two`, `telExp`, `telTerm`, `cut_insert_cancel_signed` (the signed telescope) |
| `CharClass/CupOneCoboundary.lean` | `cupOneWeight`, `cupOneSign_succAbove`, `sum_compl_split`, `cut_coboundary_master_signed`, `cochainCupOne_coboundary` |
| `CharClass/CupOneComm.lean` | `cocycleClassK_add`/`_smul`, `cochainCupOne_coboundary_cocycle`, `cup_comm_signed`, `cup_comm_of_even_left`/`_right` |

**First probe (thm-e, 2032 jobs, `CupOneSign` at 123 s): FAILED with exactly four
errors, of two kinds.**  The two big sign theorems `cutExp_succAbove_cutU` and
`cutExp_succAbove_cutV` were structurally right on the first pass; both failures were
in the small `Finset` plumbing under them.

## NEEDS

- Nothing blocking.  Deliverable (3) (`TotalH.IsEven`) waits on `sp-coeff`'s
  `ChernTotalRing` over `K`; deliverables (1) and (2) do not.

## TRAPS

- Steenrod's cup-`i` coboundary formula as usually quoted
  (`… + (-1)^{pq+p+q+i} v ⌣_{i-1} u + …`) gives `u ⌣ v = -(-1)^{pq} v ⌣ u`, the
  wrong sign.  The solved coefficient is `(-1)^{pq+p+q+i+1}`.  Do not copy the
  formula from memory.
- Writing the cup-1 sign in terms of the bidegree `(a,b)` rather than the face
  cardinalities makes the termwise sign identity false off-degree and forces a
  degree case split through the entire proof.  `cutExp` is stated through
  `(cutU S).card` and `(cutV S).card` for exactly this reason.
