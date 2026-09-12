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
telExp s t = N(t+s) + t·s + 1 + (if t ≤ s then N + t else 0)      (S = {s}, N vertices)
telExp s s ≡ telExp s (s+1) ≡ N + 1     (the two branches meet at the old cut point)
telExp s N ≡ N + 1,   telExp s 0 ≡ N + N·s + 1                    (the two endpoints)
```

`N` is the number of vertices of the big simplex, `n + 2`.  The four sign identities the
telescope needs — two per side of the old cut point — were checked by hand and against
the solver before authoring, and are `hs1`/`hs2` in each branch of
`cut_insert_cancel_signed`.

`ω s = ω (s+1)` is what replaces `x + x = 0` in `telescope_char2`: the term at the
*old* cut point vanishes because `cutLow S (s+1) = cutLow S s` **and** the weights
agree, not because 2 = 0.

## 1. Files (all new, prefix `CupOne`; nothing existing edited)

| file | contents | imports |
|---|---|---|
| `CharClass/CupOneSign.lean` | `cutExp`, `cupOneSign`; the pair description of `cutU`/`cutV`, their cards and ranks; the two termwise sign identities `cutExp_succAbove_cutU`/`_cutV` | `SteenrodCutCancel` |
| `CharClass/CupOneCochain.lean` | `cutRank_orderEmbOfFin`, the **signed** `faceVal_coboundary_signed`, `cochainCupOne` with its zero and off-degree lemmas, `cochainCupI_zero_zero_comm_of` | `CupOneSign`, `SteenrodCupEdge` |
| `CharClass/CupOneInsert.lean` | `mul_self_mod_two`, `pair_prod_mod_two`, `cutExp_pair_mod_two`, `telExp`, `telTerm`, `cut_insert_cancel_signed` | `CupOneSign`, `SteenrodCupEdge` |
| `CharClass/CupOneCoboundary.lean` | `cupOneWeight`, `cupOneSign_succAbove`, `sum_compl_split`, `cut_coboundary_master_signed`, `cochainCupOne_coboundary` | `CupOneCochain`, `CupOneInsert`, `SteenrodCoboundary` |
| `CharClass/CupOneComm.lean` | `cocycleClassK_add`/`_smul`, the two degree-cast lemmas, `cochainCupOne_coboundary_cocycle`, `cup_comm_signed`, `cup_comm_of_even_left`/`_right` | `CupOneCoboundary`, `CohomologyAssoc` |
| `CharClass/CupOneAxiomCheck.lean` | the `ZMod 2` instance checks and thirteen `#print axioms` | `CupOneComm`; imported by nothing |
| `CharClass/CupOneTotal.lean` | `TotalH.IsEven`, closure under `+`, `*`, `map`, `mul_comm_of_isEven` | **not written**: waits on `sp-coeff`'s `ChernTotalRing` over `K` |

The split into `CupOneSign` / `CupOneInsert` is deliberate: the two halves of the sign
bookkeeping (deleting a vertex of the ambient simplex, and inserting a new cut point) are
independent, so a failure in one does not cost a probe on the other.

## 2. The obligations, and where each is discharged

| obligation | name | file |
|---|---|---|
| the coboundary through a face carries the position sign | `faceVal_coboundary_signed` | `CupOneCochain` |
| the two termwise sign identities, with no degree hypothesis | `cutExp_succAbove_cutU`, `cutExp_succAbove_cutV`, packaged as `cupOneSign_succAbove` | `CupOneSign`, `CupOneCoboundary` |
| the signed replacement for `cut_insert_cancel` | `cut_insert_cancel_signed` | `CupOneInsert` |
| the signed replacement for `cut_coboundary_master` | `cut_coboundary_master_signed` | `CupOneCoboundary` |
| the coboundary formula of §0.3 | `cochainCupOne_coboundary` | `CupOneCoboundary` |
| signed graded commutativity | `cup_comm_signed` | `CupOneComm` |
| the corollary the program consumes | `cup_comm_of_even_left`, `cup_comm_of_even_right` | `CupOneComm` |

## 3. Convention alignment

Fixed by `CoeffLeibniz.aw_cochain_leibniz` (`δ(φ ⌣ ψ) = δφ ⌣ ψ + (-1)^p φ ⌣ δψ`),
which is the two-variable Koszul convention `sp-steenrod`'s `OddPSource.lean:25`
uses on the tensor half (`d(e_i ⊗ σ) = d_W e_i ⊗ σ + (-1)^i (e_i ⊗ ∂σ)`).  The
coefficient argument follows `sp-coeff` §0c: **implicit** wherever a class or
cochain determines it, **explicit and first** otherwise.  `sp-steenrod` asked to
confirm the two-variable placement; message sent.

## 4. Next deliverable: the Kronecker/UCT and sphere port over `K` (plan, before authoring)

Assigned by the lead 2026-09-10 after deliverable (2) went green, taken off `sp-coeff`'s
plate.  Target: `CharClass/CohomologyContractible.lean` (4 declarations) and
`CharClass/CohomologySphere.lean` (17 declarations) over a field `K`, which the odd side
over `F_p` needs and which nothing else can supply.

### 4.1 The six entry points

The two target files touch the vendored `ZMod 2` layer through exactly six names, and
this is the whole surface to be ported:

| entry point | file | what it is |
|---|---|---|
| `kroneckerEquiv X n` | `KroneckerNaturality.lean:214` | the universal-coefficient isomorphism `Hⁿ(X) ≅ Hom(Hₙ(X), F₂)` |
| `homologyZMod2`, `homologyDualZMod2_isZero_of_homology_isZero` | `H1ClassifierZMod2.lean` | singular homology and the dual of a zero object |
| `sphere_top_cohomology_finrank_one_direct` | `SphereTopCohomologyRankOne.lean` | `dim H^n(Sⁿ) = 1` |
| `sphereCohomology_isZero_of_gt` | `SphereModTwoHomologyAboveDimension.lean` | vanishing above the dimension |
| `sphereCohomology_isZero_of_lt` | `SphereModTwoHomologyVanishing.lean` | vanishing in the middle range |
| `H0Gen.H0aug` and friends | `SingularH0General.lean` | the degree-zero augmentation |

### 4.2 The census, checked rather than taken

`sp-coeff`'s report says this layer is "a port, not a reproof".  I read the load-bearing
parts myself, because their own §0b records that their first reading of this same
mechanism was wrong and that checking is what corrected it.

* **Exactly one declaration is genuinely field-specific**: `moduleInjective_ZMod2`
  (`H1ClassifierZMod2.lean:313`).  Its characteristic-two core is a `fin_cases a`
  enumerating the two elements of `ZMod 2` to get `a ≠ 0 → a = 1`.  Over a field that is
  "a nonzero element is a unit, so the ideal is `⊤`", which is exactly `sp-coeff`'s
  `moduleInjective_of_field` in `CoeffField.lean`, already green.  Its one consumer in the
  Kronecker layer is `zmod2_extend_functional` (`KroneckerNaturality.lean`), which is
  three lines.
* **The Mayer–Vietoris suspension tower under the sphere computation is already generic.**
  `SphereHomologyS1BaseMV.lean` (374 lines, 26 declarations), `SphereHomologyMVStep.lean`
  (359 lines, 43 declarations), `SphereSuspensionTowerFromMV.lean` and
  `Branch2CoefficientReduction.lean` contain **zero** occurrences of `ZMod 2`.  Nothing to
  do there at all.
* **`Subspace.dual_finrank_eq` needs `[Field K]` and nothing else.**  I read it at the pin:
  it handles the infinite-dimensional case itself, so the port adds no finiteness
  hypothesis to the sphere rank computation.
* **The `+decide` sites are mostly geometry, not arithmetic.**  Of eleven `+decide` uses in
  the chain, the ones in `SphereHomologyMVStep`, `SphereModTwoHomologyVanishing` and
  `SingularH0General` are discharging `EuclideanSpace.norm_eq`, `Fin.sum_univ_succ` and
  simplicial face identities, all coefficient-free.

### 4.3 The one risk worth naming in advance

Two proofs in the core — `kroneckerFunctional_add` and `kroneckerFunctional_smul`
(`H1ClassifierZMod2.lean:143,154`) — are closed by `simp_all +decide [...]` and
`simp +decide [...]`.  Their **statements** are ring-generic, but `decide` cannot run over
an abstract `K`.  If those `+decide` flags are load-bearing rather than incidental, the two
proofs must be rewritten by hand rather than substituted.  That is the only place I expect
to spend real time, and it is two short additivity/homogeneity lemmas, so the exposure is
bounded.  I will probe those two first, alone, before porting anything downstream of them.

### 4.4 Method: no vendored file is edited

The same pattern `CoeffLeibniz.lean` established and that this lane already used for the
cup-1: the vendored `ZMod 2` names are never edited and never removed, the generic twin is
a new file in `CharClass/`, and a `rfl` bridge records that the twin *is* the vendored
object at `K = ZMod 2`.  That keeps the `F₂` instance — which is the verified LIX answer —
incapable of moving, and it keeps every existing consumer byte-unchanged.

### 4.5 Names, proposed to `sp-coeff`

None of these has an argument from which `K` could be inferred (`kroneckerMap X n` names
only a space and a degree), so by their §0c the coefficient is **explicit and first**, with
the `…Of` suffix they use for that case:

```text
homologyOf K X n            kroneckerFunctionalOf K X n    kroneckerMapOf K X n
homologyDualOf K X n        kroneckerEquivOf K X n         sphereCohomologyOf K n k
```

### 4.6 Order, each step separately probeable

1. `CharClass/KroneckerClassifier.lean` — the `H1ClassifierZMod2` port: `homologyOf`,
   `homologyDualOf`, `kroneckerFunctionalOf`, its additivity and homogeneity (§4.3), the
   splitting of the cycle inclusion over a field, `kroneckerMapOf` and its surjectivity.
   `[CommRing K]` as far as the splitting, `[Field K]` from `moduleInjective_of_field` on.
2. `CharClass/KroneckerEquiv.lean` — the `KroneckerNaturality` port: naturality,
   injectivity, `kroneckerEquivOf`, plus the `rfl` bridge to the vendored `kroneckerEquiv`.
3. `CharClass/KroneckerContractible.lean` — the three vanishing theorems and
   `cohZeroEquivOfContractible` over `K`.
4. `CharClass/KroneckerSphere.lean` — the sphere computation over `K`: vanishing range,
   top rank via `Subspace.dual_finrank_eq`, `cohZeroEquivOf`.

Step 1 is the only one with unknown cost; 2 to 4 are substitution over an already-generic
Mayer–Vietoris tower.

## GREEN (with job counts)

Clone `thm-e`, log `.lake/laneprobe-20260910-141205.log`, **2068 jobs, PROBE GREEN,
zero errors, zero `sorry`**.  Every module's own artifacts (`.olean`, `.ilean`,
`.trace`, `.olean.hash`, `ir/*.c`, `ir/*.setup.json`) were deleted before the run, so
all six carry a `Built` line in that one log and none was replayed.

| module | jobs | note |
|---|---|---|
| `CharClass.CupOneSign` | 2063/2068 (81 s) | `cutExp`, `cupOneSign`, the two termwise sign identities |
| `CharClass.CupOneCochain` | 2064/2068 (73 s) | signed `faceVal_coboundary`, `cochainCupOne` |
| `CharClass.CupOneInsert` | 2065/2068 (75 s) | the signed telescope `cut_insert_cancel_signed` |
| `CharClass.CupOneCoboundary` | 2066/2068 (82 s) | signed master identity, `cochainCupOne_coboundary` |
| `CharClass.CupOneComm` | 2067/2068 (161 s) | `cup_comm_signed`, `cup_comm_of_even_left/right` |
| `CharClass.CupOneAxiomCheck` | 2068/2068 (90 s) | leaf, imported by nothing |

**Axioms.**  All thirteen endpoint-facing theorems report exactly
`[propext, Classical.choice, Quot.sound]`: `cutExp_succAbove_cutU`,
`cutExp_succAbove_cutV`, `faceVal_coboundary_signed`, `cut_insert_cancel_signed`,
`cupOneSign_succAbove`, `cut_coboundary_master_signed`, `cochainCupOne_coboundary`,
`cochainCupOne_coboundary_cocycle`, `cocycleClassK_add`, `cocycleClassK_smul`,
`cup_comm_signed`, `cup_comm_of_even_left`, `cup_comm_of_even_right`.

### Kronecker port, step 1 of 4

`CharClass/KroneckerClassifier.lean` — **PROBE GREEN**, 2093 jobs,
`✔ Built … KroneckerClassifier (170 s)`, zero errors.  `chainCxOf`, `homologyOf`,
`homologyDualOf`, `homology_hom_extOf`, `kroneckerFunctionalOf` with its defining
factorisation, value on a cycle class, additivity, homogeneity, vanishing and congruence,
all over `[CommRing K]`.  Four `rfl` bridges typecheck, so the generic objects **are** the
vendored `ZMod 2` ones rather than copies of them.

**The risk of §4.3 was real and is retired.**  The two vendored linearity proofs do use
their `+decide`, and the substituted versions failed on the first probe.  They do not need
`decide`: additivity is `Preadditive.comp_add` and homogeneity is `Linear.comp_smul`,
applied to the **right-hand** composite first.  The rewrite order is the whole content —
`homologyπ ≫ (kF φ + kF ψ)` does not match the defining factorisation until the sum is
distributed — and that is the same rewrite-order trap this lane hit twice in the cup-1
files.  So the remaining three steps of the port face no known obstacle.

### Kronecker port, step 2 of 4

`CharClass/KroneckerMap.lean` — **PROBE GREEN**, 2096 jobs,
`✔ Built … KroneckerMap (113 s)`, zero errors.  `kroneckerFunctionalOf_coboundary`, the
two linearity-on-cycles lemmas, `kroneckerCyclesMapOf`, `kroneckerMapOf` with its defining
factorisation and its computation rule on the class of a cocycle, all `[CommRing K]`; then
`chainCxOf_iCycles_split` and `kroneckerMapOf_surjective` over `[Field K]`.  Two `rfl`
bridges to the vendored `kroneckerCyclesMap` and `kroneckerMap`.

`[Field K]` is used at exactly one place in the whole layer, the splitting of the cycle
inclusion, via `sp-coeff`'s `moduleInjective_of_field`.  Everything above it is
`[CommRing K]`, which is worth knowing because it means the classifier itself exists over
any commutative ring and only its *surjectivity* is a field statement.

Two things cost probes here and both are recorded as traps.  The vendored surjectivity
proof chases elements through `ModuleCat.hom`/`ofHom`; rewriting the representing cochain
as a **composite of morphisms** (`s ≫ homologyπ ≫ ofHom g`) rather than of linear maps
makes the whole argument three `rw`s of `Category.assoc` and kills four errors at once.
And `convert … using 1` on a term carrying a proof argument leaves a goal that differs only
in that proof, which neither `rfl` nor `simp` closed.

### Kronecker port, steps 3 and 4a of 4

`CharClass/KroneckerEquiv.lean` — **PROBE GREEN**, 2098 jobs,
`✔ Built … KroneckerEquiv (176 s)`.  `extend_functional_of_field`,
`factor_of_ker_le_of_field`, `mem_range_iCyclesOf_of_d`, `kroneckerMapOf_injective`,
`kroneckerMapOf_bijective`, **`kroneckerEquivOf K X n : Hⁿ(X; K) ≅ Hom_K(Hₙ(X; K), K)`**,
and `homologyDualOf_isZero_of_homology_isZero`.  A `rfl` bridge shows the generic
isomorphism's underlying map is the vendored `kroneckerEquiv`'s.

`CharClass/KroneckerContractible.lean` — **PROBE GREEN on the first probe**, 2812 jobs,
`✔ Built … KroneckerContractible (168 s)`.  `pull_eq_of_homotopicOf`,
`pull_eq_of_homotopyOf`, `pullEquivOfHomotopyEquivOf`, `cohomology_unit_isZeroOf`,
`cohomology_isZero_of_contractibleOf`, `cohomology_eq_zero_of_contractibleOf`, with three
`ZMod 2` restatements.  **A point is acyclic over `K`**, which is half of what makes
`H^*(CP^d; K)` a line in each even degree.

Homotopy invariance needed no port at all: `singularCohomologyMap_eq_of_homotopic` in the
vendored layer already takes `(R : Type) [CommRing R]`, and the `ZMod 2` statements
beneath it are thin instantiations.  The two lines that name the right functor are the
whole of it.  `[Field K]` enters this file only through `kroneckerEquivOf`.

### What remains: the sphere half

`sphere_top_cohomology_finrank_one_direct` and the two vanishing ranges, which rest on
`SphereModTwoTopGeneratorData.lean` (146 lines), `SphereModTwoHomologyVanishing.lean` and
`SphereModTwoHomologyAboveDimension.lean`.  I checked the `ZMod 2` occurrences in those
rather than assuming: **every one is an instantiation of an already-generic construction**
— `subChainComplex (ZMod 2)`, `mvShortComplex (ZMod 2)`, `mvHomologyIso_succ (ZMod 2)`,
`homologyIsoOfHomotopyEquivModule (ZMod 2)`, each taking `(R) [CommRing R]`.  So it is
substitution, as `sp-coeff` said, but roughly 600 lines of it across three files, and it
is the one remaining piece.  `Subspace.dual_finrank_eq` at the top of it needs `[Field K]`
and, as recorded in §4.2, adds no finiteness hypothesis.

**Tree state.**  Six `CupOne*` files and four `Kronecker*` files, **nothing existing
edited**: `git status` shows the six
as untracked and every `Steenrod*` file clean.  Nothing existing imports them, so no
other lane's closure changes and the `F₂` instance cannot move.  They are not reachable
from the root `GroupApproximation.lean` (which this lane must not edit), so the lead's
landing needs to add them there or the main build will never compile them.

### What the consumers get

```lean
cup_comm_signed        (a : Hmod K X p) (b : Hmod K X q) :
    cup a b = (-1 : K) ^ (p * q) • cohCast (Nat.add_comm q p) (cup b a)
cup_comm_of_even_left  (hp : Even p) (a b) : cup a b = cohCast (Nat.add_comm q p) (cup b a)
cup_comm_of_even_right (hq : Even q) (a b) : cup a b = cohCast (Nat.add_comm q p) (cup b a)
```

The even-degree conclusion is byte-identical to the `F₂` `SteenrodCupOne.cup_comm`, so
each consumer takes it by adding an evenness hypothesis and changing nothing else.  Of
the sixteen `cup_comm` sites in `CharClass/`, **fifteen are consumer sites** and each
commutes a degree-2 or degree-`2d` generator (`cpGen`, `cpTaut`, `cpTop`, `ξ`, a Chern
class), so the hypothesis is available at every one.  The sixteenth,
`ChernTotalRing.lean:94`, is **not a consumer**: it is the `mul_comm` field of the `F₂`
`GCommRing` instance, which quantifies over all degrees, so no evenness hypothesis can be
added and none should be.  That is precisely the case that is false at odd `p`, and it is
why `sp-coeff`'s generic `ChernTotalRing` drops to `DirectSum.GRing` with commutativity
supplied only through the even-degree route.  `sp-lh` confirms ten of the fifteen in their
own layer, five needing `cup_comm_of_even_left` and five `_right`, which is why both
handednesses are exported.

**Certification, stated explicitly rather than left to be inferred.**  `sp-steenrod` and
`sp-coeff` both warned not to certify the formula on the cut-index-zero case, which
collapses to the signed Leibniz rule and pins only the two derivative coefficients; the
two terms that lower the cut index are where a reindexing hides.  The solve here is not
exposed to that: the two Leibniz coefficients are **pinned as inputs** at `1` and
`(-1)^a`, so the cut-index-lowering coefficients are the only unknowns the system solves
*for*, over every bidegree `0 ≤ a,b ≤ 5` at once.  The collapse case could not have
produced them.  The closed form was then re-verified independently to `n = 8`.

`CupOneAxiomCheck.lean` also machine-checks two things about the `F₂` instance, in a
leaf nothing imports (re-probed alone at 14:32, `Built`, 2068 jobs, PROBE GREEN):

* `cup_comm_signed` and `cup_comm_of_even_left` typecheck at `Hmod2` with no bridging, so
  the generic statements *are* statements about the mod-2 cohomology the LIX answer is
  built on;
* **`cochainCupOne a b n α β = cochainCupI 1 a b n α β` over `ZMod 2`** — every sign is
  `1` there, so the signed cup-1 is literally the tree's cup-1, and
  `cochainCupOne_coboundary` is a refinement of `SteenrodCoboundary.cochainCupI_coboundary`
  at `i = 0` rather than a different operation.  This is the cheap cross-check that a
  blind-authored signed development did not drift from the `F₂` one it replaces.

## AUTHORED, UNVERIFIED

- Nothing.  Deliverables (1) and (2) are green; deliverable (3) is not started, see NEEDS.

## NEEDS

- **From `sp-coeff`, for deliverable (3) only.**  `ChernTotalRing.lean` is still pinned
  at `ZMod 2`: `TotalPiece`, `TotalH`, `TotalH.of`, `TotalH.component`, `TotalH.map` all
  name `ZMod 2`, and the `GCommRing` instance rests on the unsigned `cup_comm`.  I asked
  them (message sent) for three signatures before writing against a guess: whether
  `TotalH K X` takes the coefficient explicitly first (their §0c rule would say yes),
  whether the graded structure becomes `DirectSum.GRing` with commutativity supplied only
  through the even-degree predicate, and whether the predicate is to be called
  `TotalH.IsEven`.  The moment their generic `TotalH` lands I write `IsEven` closed under
  `+`, `*`, `TotalH.of` at even degree and `TotalH.map`, plus `mul_comm_of_isEven`.
  Deliverables (1) and (2) did not need any of it.
- Nothing from `sp-steenrod`.  I sent them my four conventions and the sign trap below;
  no clash reported.

## TRAPS

- **Steenrod's cup-`i` coboundary formula as usually quoted is wrong in one sign.**  The
  printed `… + (-1)^{pq+p+q+i} v ⌣_{i-1} u + …` yields `u ⌣ v = -(-1)^{pq} v ⌣ u`.  The
  solved coefficient is `(-1)^{pq+p+q+i+1}`.  The linear solve over every bidegree
  `0 ≤ a,b ≤ 5` is unique with no free parameter, so this is not a convention choice.  Do
  not copy the formula from memory; solve for it.
- **Write the cup-1 sign through the face cardinalities, never through the bidegree.**
  `(-1)^{a+ab+c₀c₁}` and `cutExp` agree on every cut that survives, but only `cutExp`
  makes the termwise sign identity true *off* the bidegree, and the `F₂` proof's whole
  economy is that it never case-splits on degree.  Exactly two degree hypotheses survive
  with `cutExp`, both one `by_cases` on a cardinality inside a `Finset.sum_congr`.
- **`omega` silently drops an equality of `Fin`s.**  It reports "could not prove the
  goal" with a counterexample listing only the numeric atoms, which reads as a missing
  bound.  `simp only [Fin.ext_iff]` did **not** convert `x = t₀` arising from
  `Finset.mem_insert` inside a disjunction.  Convert membership by hand
  (`x ∈ {t₀,t₁} ↔ x.val = t₀.val ∨ x.val = t₁.val`, by `rintro (rfl|rfl)` and `Fin.ext`).
- **A chain `rw [h1, h2]` can fail on `h2` because `h1` already fixed it.**  If `h1`'s
  left side is a subterm of `h2`'s, the first rewrite consumes the occurrence and the
  second reports "did not find an occurrence" although it is true.  Hit when normalising
  `c + 1 + (N - (c₁+1))` and the same expression `+ 1` in one step.
- **Rewrite the `.erase` form of a cut before the bare form.**  `cutV_insert_eq_cutHigh`
  rewrites every `cutV (insert c S)`, including the one inside
  `(cutV (insert c S)).erase c`, after which
  `cutV_insert_erase_eq_cutHigh_succ` has nothing to match.  The four `insert` lemmas of
  `SteenrodCutCancel` must be applied erase-first.
- **`Finset.pair_comm` on the goal destroys the `insert c S` shape those same lemmas
  need.**  In the branch where the new cut point is *above* the old one the cut is
  `{s, c}` for the arithmetic but must stay `insert c {s}` for the eight `insert` lemmas.
  Use `hins : insert c {s} = {s, c}` only inside the sign computations, never on the goal.
- `cochainCast_rfl` lives in `CohomologyAssoc.lean`, not in the vendored layer; a file
  that casts cochains and does not import it fails with `Unknown identifier`.
- Multiplication of two non-constant naturals must be kept out of `omega`.  The pattern
  that worked: prove the one product identity with `ring`, then let `omega` treat the
  product as an atom (`cutExp_pair_mod_two`, `mul_self_mod_two`, `pair_prod_mod_two` do
  the whole file's share of this).
