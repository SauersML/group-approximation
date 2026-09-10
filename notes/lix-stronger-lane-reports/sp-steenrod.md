# Lane `sp-steenrod` — odd-primary Steenrod reduced powers

Program note: `notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.5, second bullet.
Clone: `cs-limit`, cores 72–79.  Owns `GroupApproximation/CharClass/OddP*.lean`
(new prefix, chosen so that nothing collides with `Steenrod*`, `Cartan*`,
`Acyclic*`, which stay mod-2 and stay green).

This file is **the construction plan**, deliverable one.  No Lean has been
authored.  Nothing in the shared tree has been edited by this lane.

---

## 0. What the plan says, in one page

**The route.**  The `ℤ/p`-equivariant diagonal `Δ : W ⊗ C(X) → C(X)^{⊗p}` exists
and is unique up to equivariant homotopy **by the acyclic-models theorem the tree
already has**, which is stated over an arbitrary commutative ring `Λ`, an
arbitrary category and an arbitrary family of models.  Instantiating it at
`Λ = F_p[ℤ/p]` is not a new theorem; it is the existing theorem with a different
`Λ`.  That is the single largest asset in the tree and it makes the lane
possible.

**What has to be built** is the two functors the theorem is applied to, and the
evaluation layer on top:

* the resolution `W` over `Λ = F_p[ℤ/p]` — cheap, and cheaper than expected
  because `F_p[ℤ/p] ≅ F_p[s]/(s^p)` with `s = T − 1`, so the two alternating
  differentials are multiplication by `s` and by `s^{p-1}`, and `d ∘ d = 0` is
  `s^p = 0`;
* the source `W ⊗ C(X)` — cc-cartan's design transfers with one sign added;
* the target `C(X)^{⊗p}` as a **flat `p`-tuple `Finsupp` model with explicit
  Koszul signs**, arity `r` a free parameter (so the Cartan target `C^{⊗2p}` is
  the same construction at `r = 2p`, not a second one);
* the evaluation of `u^{⊗p}` against it, and the class-level operations.

**The one thing the acyclic-models route cannot deliver is the normalisation
constant, and that is the lane's crux.**  Everything else — naturality,
well-definedness, independence of the choice of `Δ`, additivity, instability,
`P^{q/2} = p`-th cup power, and the Cartan formula — comes out of an *abstract*
`Δ`.  `P^0 = id` does not: it is equivalent to knowing the value of a universal
constant `c_q ∈ F_p`, and no property of an abstract `Δ` pins it.  §4 explains
why, gives the two routes to it, and asks `sp-design` for one cheap model test
that may make the value irrelevant.

**Size.**  About 5000–6500 lines in 34–40 modules if the constant comes from the
cheap route, plus 1500–2500 lines and high risk if it needs the explicit
diagonal.  This is bigger than any other lane in the program and it is the
critical path.  §7 gives the landing order so that partial progress is usable.

---

## 1. Inventory: what exists, what is characteristic-two only, what is new

### 1.1 Reusable **as is**, with no coefficient work

| file | declaration | why it transfers |
|---|---|---|
| `CharClass/AcyclicModels.lean` | `FreeOnModels`, `AcyclicOnModels`, `acyclicModelsHomotopy`, `NaturalHomotopy`, `NaturalHomotopy.homotopy` | stated over `{Λ : Type} [CommRing Λ]`, arbitrary `C`, arbitrary `M : ι → C`; the module docstring says in as many words that `Λ` is never assumed to be a field or to have characteristic two.  `ZMod 2` occurs once, in prose. |
| `CharClass/AcyclicModelsExistence.lean` | `Augmentation`, `AcyclicZeroOnModels`, `acyclicModelsMap`, `acyclicModelsMap_zero`, `amMap_naturality`, `amMap_comm` | zero occurrences of `ZMod 2`.  This is the **existence** half and it is what produces `Δ`. |
| `CharClass/AcyclicModelsContraction.lean`, `AcyclicModelsHomology.lean` | the two routes into `AcyclicOnModels` | zero occurrences of `ZMod 2`. |
| `CharClass/AcyclicModelsSplitting.lean` | `splitHomotopy`, `splitAlpha`, `PositiveContraction`, `ker_le_range_of_positiveContraction`, `acyclicOnModels_of_ker_le_range` | stated over `{F : Type} [Field F]`.  `ZMod 2` occurs twice, both in prose.  `F := ZMod p` needs only `[Fact p.Prime]`. |
| `CharClass/AcyclicModelsTensor.lean` | `tensorCx`, `tensorPositiveContraction`, `tensorCx_exists_preimage` | over `[CommRing Λ]`; `tensorCx` is Mathlib's `HomologicalComplex.mapBifunctor`, i.e. the **signed** total complex.  Used here only as a fallback route to acyclicity (§3.4). |

### 1.2 Reusable after a mechanical `ZMod 2 ↦ K` substitution

| file | what it gives | the substitution |
|---|---|---|
| `CharClass/CartanSingular.lean` | `singFreeSimplicial`, `singFree`, `singFree_obj_X` | the composite `TopCat.toSSet ⋙ free R ⋙ alternatingFaceMapComplex` is generic in `R`, and `∂∂ = 0` comes from `AlternatingFaceMapComplex.d_squared`.  The only characteristic-two lemmas in the file (`ModuleCatZMod2.hom_add_self`, `neg_eq_self`, `neg_one_pow_zsmul`, `singFree_d_single`) exist **to drop the alternating signs**.  This lane keeps the signs, so those four are not ported and not needed. |
| `CharClass/CartanSimplexContractible.lean` | `homZMod2_isZero_of_contractible`, `homZMod2_isZero_stdSimplexTop` | built on Mathlib's `AlgebraicTopology.singularHomologyFunctor (ModuleCat R) k` applied to `ModuleCat.of R R`, which is generic in the coefficient object; the file pins `ZMod 2` in the abbreviation only. |
| `CharClass/AcyclicModelsResolution.lean` | `periodicDiff`, `periodicResolution`, `periodicResolutionBasis` | genuinely mod-2: one repeated differential, because `1 − T = 1 + T`.  §2.2 replaces it with a **two-differential** version that has the mod-2 file as its `a = b = 1 + T` instance. |
| `CharClass/CartanGroupRing.lean` | `GroupRingZ2`, `groupRingGen`, `galEnd`, `galAlgHom`, `moduleOfInvolution`, `moduleOfInvolution_smul` | the shape transfers; `galEnd`'s `if toAdd a = 0 then 1 else τ` becomes `τ ^ (ZMod.val a)`, and the `by decide` case analysis on `ZMod 2` becomes one `ZMod.natCast_self`-style computation.  See §2.1. |
| `CharClass/CartanSimplexExact.lean` | the degreewise iso between Mathlib's coproduct carrier and the `Finsupp` carrier, hence "over a standard simplex every positive-degree cycle is a boundary" | **corrected 2026-09-10, see §1.2a** — this is *not* a mechanical substitution. |

### 1.2a Correction (2026-09-10), from `sp-coeff`, verified here

The row above originally said the `CartanSimplexExact.lean` port was a mechanical
`ZMod 2 ↦ K` substitution that would come out shorter.  That was wrong, and the
reason is worth more than the correction.

The file's chain-map step is `rw [hL, singular_d_ι]` at l.129, and
`singular_d_ι` (vendored, `CoveringTransferBoundary.lean` l.106) encodes
characteristic two **in the shape of its statement**, not in its proof: it says
the differential applied to a basis simplex is the *unsigned* sum of the
coproduct injections of the faces, where the alternating sum belongs.  I read
both sites; the claim holds.  Its proof reaches `AlternatingFaceMapComplex.obj_d_eq`
and `singularChainSimplicialModule_δ_ι`, which are the honest signed steps, and
then discards the signs with `neg_one_zsmul_eq_self` against the 2-torsion lemma
`singularChain_add_self`.

Two consequences.

* **No token grep finds this.**  There is no `ZMod 2` on the statement's
  characteristic-two-ness; the file is mod-2 throughout, so a scan for the token
  flags everything and distinguishes nothing.  `sp-coeff` found it by a one-hop
  *use* analysis — collect declarations whose **code**, not docstring, is false
  outside characteristic two, then find their callers — and that method also
  found five in-scope files they had missed.  This lane adopts the method.
* **The repair is to re-derive, not to transport.**  The signed statement is the
  same proof stopped one line earlier, before `neg_one_zsmul_eq_self`; whether
  the surrounding vendored objects (`singularChainCx`, `transferCoeff`,
  `singularChainSimplicialModule`) are generic in the coefficient ring is a
  separate question this lane must check before relying on it.  Nothing
  downstream of `singular_d_ι` may be carried to odd `p` by substitution.

`CartanSimplexExact` is this lane's only concern here: `sp-coeff` reports it is
`singular_d_ι`'s only `CharClass` consumer, and of the 367 vendored declarations
whose code mentions `ZMod 2`, exactly 19 are reachable from an in-scope
`CharClass` file and `singular_d_ι` is not among them.

### 1.3 **Not** reusable

`CharClass/CartanFreeCx*.lean` (`CartanFreeCx`, `Aug`, `Hom`, `Swap`,
`TensorAug`, 1236 lines) is a hand-rolled tensor product of index-presented free
modules with a **sign-free** differential; `tensorD_tensorD` works because "the
two mixed terms are equal and cancel because two is zero".  Every one of those
cancellations is false at odd `p`.  The flat tuple model of §3 replaces the whole
group and is **not** a port of it: it is arity-generic, which the binary `FreeCx`
is not, and arity-genericity is what makes `C^{⊗2p}` free.

`CharClass/Steenrod*.lean` (29 modules) is the cup-`i` construction.  There is no
cup-`i` at odd `p` and none of it transfers.  Its **design** transfers, and that
is worth more than the code: see the recipes in §8.

### 1.4 What this lane needs from `sp-coeff`

Exactly two things, both already on their plan (`notes/lix-stronger-lane-reports/sp-coeff.md`):

1. `CharClass/CoeffLeibniz.lean` — the **signed** Leibniz rule
   `δ(φ ⌣ ψ) = δφ ⌣ ψ + (-1)^{|φ|}(φ ⌣ δψ)` over `[CommRing R]`, replacing the
   mod-2 `aw_cochain_leibniz_zmod2`.  This lane consumes it for "the `p`-fold cup
   product of a cocycle is a cocycle" and for the evaluation layer.
2. `CharClass/CoeffCohomology.lean` + `CohomologyBasic.lean` — `Hmod K X n`,
   `cocycleClassK`, `cupK`, `oneK`, `cohPullbackK`, `cohCast` over a field `K`.

Nothing else.  In particular this lane does **not** need Leray–Hirsch, Chern
classes, Thom, Gysin or Mayer–Vietoris over `K`; those are `sp-evenside`'s
consumers.  Until (1) and (2) land, everything below is authored against the
vendored generic layer directly: `singularCochainGroup K X n`, `cochainEval`,
`cochainCup`, `cochainPullback`, `cochainCoboundary K` are already
`{R : Type} [CommRing R]` in
`ThirdParty/HamSandwich/SphereOddDegree/AlgebraicTopology/CupProduct.lean` and
`AlexanderWhitneyChainMap.lean`.  **Name coordination sent to `sp-coeff`: this
lane will use `Hmod K`, `cocycleClassK`, `cupK`, `cohCast` verbatim and will
define no cohomology vocabulary of its own.**

---

## 2. The algebra: `Λ`, `W`, and the source functor

### 2.1 `Λ = F_p[ℤ/p]`, and the one structural fact that pays for itself

```lean
abbrev GroupRingZMod (p : ℕ) : Type := MonoidAlgebra (ZMod p) (Multiplicative (ZMod p))
noncomputable def grGen (p : ℕ) : GroupRingZMod p := MonoidAlgebra.single (Multiplicative.ofAdd 1) 1
theorem grGen_pow_card (p : ℕ) : grGen p ^ p = 1
noncomputable def grS (p : ℕ) : GroupRingZMod p := grGen p - 1
theorem grS_pow_card (p : ℕ) [Fact p.Prime] : grS p ^ p = 0
theorem grNorm_eq (p : ℕ) [Fact p.Prime] : ∑ j ∈ Finset.range p, grGen p ^ j = grS p ^ (p - 1)
```

`grS_pow_card` is `(T − 1)^p = T^p − 1 = 0`, i.e. the Frobenius `add_pow_char`
in the commutative `F_p`-algebra `Λ`.  It is one line and it is the reason
everything below is cheap:

* `d ∘ d = 0` for the resolution is `s · s^{p-1} = s^p = 0`;
* the norm `N = Σ_j T^j` equals `s^{p-1}`, so `N` is **not** a separate element
  with separate lemmas — every `N`-fact is an `s`-fact.  **The justification
  originally given here was wrong** and `sp-design` caught it in review: "multiply
  `Σ T^j` by `T − 1` and telescope" proves only `N · s = 0`, i.e. `N ∈ Ann(s)`,
  and in `Λ ≅ F_p[s]/(s^p)` the annihilator of `s` is the one-dimensional
  `(s^{p-1})`, so the telescope pins `N` only up to an undetermined constant —
  including zero.  That is this report's own §4 hazard appearing in the lane's
  first lemma, which is worth more as a warning than the lemma is as a fact.
  The correct proof telescopes in `F_p[X]`, a **domain**, where `X - 1` may be
  cancelled: `(Σ_{j<p} X^j)(X-1) = X^p - 1 = (X-1)^p` by Frobenius, so
  `Σ_{j<p} X^j = (X-1)^{p-1}`, and only then does one map `X ↦ T`.  Landed as
  `OddPNorm.lean`;
* `N e_i` is a boundary in `W` in **every** degree `i` — for odd `i` because
  `d e_{i+1} = N e_i` by definition, for even `i` because
  `N = s·s^{p-2}` and `d e_{i+1} = s e_i`.  This is what makes additivity of
  `P^i` (§5.3) a two-line argument instead of a parity case split.

`Λ` is commutative because `ℤ/p` is abelian, so `AcyclicModels.lean`'s
`[CommRing Λ]` is satisfied — the same reason the mod-2 instance works.

The module bridge, generalising `moduleOfInvolution`:

```lean
noncomputable def galEndP (τ : Module.End (ZMod p) V) (hτ : τ ^ p = 1) :
    Multiplicative (ZMod p) →* Module.End (ZMod p) V           -- a ↦ τ ^ (ZMod.val a)
noncomputable def galAlgHomP … : GroupRingZMod p →ₐ[ZMod p] Module.End (ZMod p) V
noncomputable abbrev moduleOfOrderP … : Module (GroupRingZMod p) V
theorem moduleOfOrderP_smul … : grGen p • v = τ v
```

`galEndP`'s `map_mul'` is where `hτ` is spent: `τ^(val a + val b)` versus
`τ^(val (a+b))`, which differ by `τ^p = 1` exactly when the addition wraps.  The
clean spelling is to build the additive hom `ZMod p →+ Additive (Module.End …)`
with `ZMod.lift p ⟨zmultiplesHom _ (Additive.ofMul τ), _⟩` and transport, rather
than to case-split on `ZMod.val`; the side condition `ZMod.lift` wants is
literally `hτ`.

### 2.2 The resolution, with two differentials

`AcyclicModelsResolution.lean` is generalised, **not edited**, into
`OddPResolution.lean`:

```lean
variable {Λ : Type} [CommRing Λ] (a b : Λ)
noncomputable def altDiff (i : ℕ) : ModuleCat.of Λ Λ ⟶ ModuleCat.of Λ Λ   -- mulLeft (if Even i then b else a)
noncomputable def altResolution (hab : a * b = 0) : ChainComplex (ModuleCat.{0} Λ) ℕ
theorem altResolution_d_odd  (k) : (altResolution a b hab).d (2*k+1) (2*k) = mulLeft a
theorem altResolution_d_even (k) : (altResolution a b hab).d (2*k+2) (2*k+1) = mulLeft b
noncomputable def altResolutionBasis (k) : Module.Basis Unit Λ ((altResolution a b hab).X k)
```

with `W p := altResolution (grS p) (grS p ^ (p-1)) (by rw [← pow_succ']; exact grS_pow_card p)`.
The mod-2 file is the instance `a = b = 1 + T`; it is **not** replaced, because
`Cartan*.lean` consumes it and the `F₂` LIX answer must stay green.

Both differentials are `mulLeft` of a fixed scalar, so the parity split lives in
one `if` inside `altDiff` and is discharged once, by `Nat.even_or_odd`, in the
two `_d_` lemmas.  Do not index the resolution by "even/odd degree" as two
families; that reintroduces the transports cc-cartan's `CartanMidFour` post-mortem
warns about ("never let a degree be an expression in the inputs").

### 2.3 The source functor

cc-cartan's design, unchanged except for one sign.  Degree `k` carrier indexed
**by the simplex dimension, not by the `W`-index**:

```lean
abbrev WSIdx (X : TopCat.{0}) (k : ℕ) : Type := Σ n : Fin (k+1), singularSimplices X n.val
abbrev srcMod (p) (X) (k) : Type := WSIdx X k →₀ GroupRingZMod p
```

so that the `W`-index is the derived quantity `k − n`.  The differential is
`d(e_i ⊗ σ) = (d_W e_i) ⊗ σ + (-1)^i (e_i ⊗ ∂σ)`, written as two `Fin`
eliminators exactly as cc-cartan prescribes (`Fin.lastCases` for the resolution
half, `Fin.cases` for the boundary half), so that no simplex is ever transported.
`d ∘ d = 0` is four groups: `a·b = 0` and `b·a = 0` for the resolution half,
`∂∂ = 0` for the boundary half, and the two mixed terms, which now cancel
**because of the sign `(-1)^i` against `(-1)^{i-1}`** rather than because two is
zero.  That is the one place where the mod-2 proof is replaced rather than
copied, and it is three lines.

Freeness on the models is cc-cartan's `srcFree` verbatim: the index
`FreeOnModels` wants is `WSIdx X k` on the nose, the basis is
`Finsupp.basisSingleOne`, and `basis_apply` is `Category.id_comp`, modulo the one
`ULift` reindex their traps section flags (`singularSimplices X n` is
`ULift (Δ^n ⟶ X)`, and `Module.Basis.reindex` is spent in the `basis`/`basis_apply`
fields and nowhere else).

Estimated: `OddPGroupRing` 180, `OddPResolution` 160, `OddPSource` 380,
`OddPSourceFree` 200 lines.

---

## 3. The target: a flat `r`-tuple model with explicit signs

### 3.1 Why flat and arity-generic

Three candidates were considered.

* **Mathlib's iterated `tensorCx`.**  Rejected: the cyclic permutation of `r`
  factors needs a braiding, and cc-cartan's traps record that Mathlib has
  `MonoidalCategory` for `HomologicalComplex` at this pin but **no**
  `BraidedCategory`/`SymmetricCategory`; the graded-object braiding is not
  transported to complexes.  Building a `p`-cycle out of associators for a
  *variable* `p` is not affordable.
* **A signed port of `CartanFreeCx` (binary, iterated).**  Rejected: the cyclic
  shift on `((C ⊗ C) ⊗ C) ⊗ …` is a composite of `p − 1` adjacent transpositions
  with `p` variable, and every degree becomes an expression in the inputs.
* **A flat `r`-tuple `Finsupp` model.**  Chosen.  One construction, arity `r`
  free, so `C^{⊗p}` and the Cartan target `C^{⊗2p}` are the same object at two
  values of `r` and share every lemma.  The cyclic shift is a permutation of the
  index type with one scalar sign.

### 3.2 The objects

```lean
/-- A degree-tagged singular simplex. -/
abbrev TagSimp (X : TopCat.{0}) : Type := Σ n : ℕ, singularSimplices X n
/-- `r`-tuples of tagged simplices whose degrees sum to `k`.  An `abbrev`, not a
`def`: cc-steenrod lost six rewrites in one probe to a `def` index type. -/
abbrev TupIdx (X : TopCat.{0}) (r k : ℕ) : Type := { t : Fin r → TagSimp X // ∑ j, (t j).1 = k }
abbrev tupMod (K) [CommRing K] (X) (r k) : Type := TupIdx X r k →₀ K
```

The degree data is carried **as data with the sum as a `Prop`**, which is
cc-steenrod's `PairIdx`/`PairDeg` recipe and is what removed every degree cast
from their lane.  The flat spelling `Fin r → TagSimp X` is preferred over
`Σ d : {d : Fin r → ℕ // ∑ d = k}, ∀ j, singularSimplices X (d.1 j)` because the
latter's dependent function makes the pushforward along `f : X ⟶ Y` a dependent
rewrite.

Partial degrees and the two signs:

```lean
def pre (t : Fin r → TagSimp X) (j : Fin r) : ℕ := ∑ l ∈ Finset.filter (· < j) Finset.univ, (t l).1
def tupD  (K) (X) (r k) : tupMod K X r (k+1) →ₗ[K] tupMod K X r k        -- Σ_j (-1)^{pre t j} Σ_i (-1)^i ⟨t with slot j faced⟩
def tupT  (K) (X) (r k) : tupMod K X r k →ₗ[K] tupMod K X r k            -- (-1)^{(t last).1 * (k - (t last).1)} • cyclic shift
```

`tupD`'s summand is **totalised** in cc-steenrod's sense: the face of slot `j`
returns `0` unless the resulting tuple has total degree `k`, which it always
does, so no sum ever carries a cardinality hypothesis and no face map appears
with a proof argument.  Write the face of slot `j` through a named function
`faceSlot X r j i t` whose *result type* does not mention `j` or `i`; that is the
junction recipe from cc-steenrod's composite-B post-mortem and it is what makes
`congrArg` apply with no dependent motive.

### 3.3 The three sign lemmas, and where `p` odd is used

```lean
theorem tupD_tupD : tupD K X r k ∘ₗ tupD K X r (k+1) = 0
theorem tupT_tupD : tupT K X r k ∘ₗ tupD K X r k = tupD K X r k ∘ₗ tupT K X r (k+1)
theorem tupT_pow_card (hr : r = p ∨ …) : (tupT K X r k) ^ r = 1
```

* `tupD_tupD`: within one slot it is `∂∂ = 0`; across two slots `j < j'` the
  term "face `j` then face `j'`" and the term "face `j'` then face `j`" carry
  signs `(-1)^{pre j + pre j'}` and `(-1)^{pre j + (pre j' - 1)}` — the second
  slot's prefix has dropped by one — and cancel.  This is the standard
  computation and it is the honest replacement for
  `CartanFreeCx.tensorD_tensorD`'s characteristic-two cancellation.
* `tupT_pow_card`: `r` applications of the shift multiply the signs to
  `(-1)^{k² − Σ_j n_j²}`, and `x² ≡ x (mod 2)` gives `k² − Σ n_j² ≡ k − Σ n_j = 0`.
  So `tupT^r = 1` **for every `r`**, with no hypothesis on `r` at all.  Record
  this: it is the fact that lets `moduleOfOrderP` apply at both `r = p` and
  `r = 2p`, and it costs one parity lemma.

`p` odd enters this lane in exactly **two** places, and nowhere else:

1. `tupEval` is `tupT`-invariant on the nose (§5.1), because the sign is
   `(-1)^{q²(p-1)}` and `p − 1` is even.  At `p = 2` that sign is `(-1)^{q²}`
   and the mod-2 tree needs no invariance argument because `−1 = 1`.
2. `⟨u^{⊗p}, N y⟩ = p·⟨u^{⊗p}, y⟩ = 0` — the norm dies against an invariant
   functional.  This is the odd-`p` replacement for "the `(1 + t)` half dies
   because `2 = 0`", and it is *stronger*: **both** halves of the source
   differential die (§5.2), so the coboundary formula has no parity case split.

### 3.4 Acyclicity on the models

`AcyclicOnModels stdSimplexTop Λ tgt` is what the theorem consumes, and
`acyclicOnModels_of_ker_le_range` reduces it to `ker d ≤ range d` for
`tupCx (Δ^n) r` in every positive degree.  Two routes; the first is recommended.

* **(A) Direct telescoping contraction, arity-generic.**  `C(Δ^n; K)` has a
  contraction `s` with `d s + s d = 1 − ηε` (from `CartanSimplexContractible` at
  `K`, plus `AcyclicModelsSplitting.splitHomotopy`, which is over an arbitrary
  field and needs only `ker ≤ range`).  On tuples set
  `S(t) = Σ_j (-1)^{pre t j} (ηε)^{⊗(j)} ⊗ s ⊗ 1^{⊗(r-j-1)} (t)`.
  Then `dS + Sd = 1 − (ηε)^{⊗r}` by a telescoping sum in which consecutive terms
  cancel — one computation, `r` free, no induction on `r`.  This is strictly
  easier in the flat model than in an iterated binary one, which is the second
  reason to be flat.
  **Confirmed independently, and the sign worry resolves trivially (2026-09-10).**
  `sp-design` built this operator for the chain-level diagonal and reports two
  things this section needs.

  * The **full** operator `Σ_l (ηε)^{⊗(l-1)} ⊗ s ⊗ 1^{⊗(p-l)}` is required;
    the one-slot version leaves an `(ηε) ⊗ 1` residual and their first run died
    on it.  The defect of the full one is `1 - (ηε)^{⊗p}`, supported in degree
    `0` only, which is exactly what §3.4(A) wants.  Note that the one-slot
    operator **does** suffice on the resolution `W ⊗ W`, because a resolution has
    nothing in negative degrees for the residual to leak into; on chains it does
    not.  Two claims about two complexes, not to be conflated.
  * **No Koszul signs appear.**  The `l`-th term is nonzero only when the prefix
    slots are vertices, since `ηε` kills positive degrees, so the input prefix
    degrees are `0` on the support and the sign is `+1`.  The operator can be
    written sign-free.

  That last point supersedes the convention warning below in the best possible
  way: the two readings I was guarding against agree, because both are `0` on the
  support.  **The warning stays**, because it is the reason one has to check, and
  the check is what produced the simplification rather than a bookkeeping
  exercise.

  **The sign convention, settled before writing (2026-09-10, on `sp-design`'s
  instruction).**  The contraction is
  `S(x_1 ⊗ ⋯ ⊗ x_r) = Σ_j ± (ηε)x_1 ⊗ ⋯ ⊗ (ηε)x_{j-1} ⊗ s x_j ⊗ x_{j+1} ⊗ ⋯`,
  and the Koszul sign of applying a degree-`+1` operator in slot `j` past a
  prefix of degree-`0` operators is `(-1)^{|x_1| + ⋯ + |x_{j-1}|}` — the degrees
  of the **inputs**.  The trap is that the prefix slots of the **output** have
  degree `0`, because `ηε` has landed on them, so an implementation that reads
  the prefix off the output tuple computes `(-1)^0 = 1` in every term and gets
  the contraction wrong in a way that still typechecks.

  `tupD` does not have this problem and that is what makes it seductive: its
  slots before `j` are untouched, so input and output prefixes agree and either
  reading gives the same sign.  `S` is the first place they diverge.  **Rule for
  this file: `S`'s sign is a function of the input tuple, passed explicitly, and
  is never recomputed from the value.**

  **The prerequisite, checked at the pin (2026-09-10).**  Route (A) needs
  `ker d ≤ range d` for `singFree.obj (Δ^n)`, the `Finsupp`-carrier complex, and
  the vanishing-homology input is stated for Mathlib's
  `singularHomologyFunctor`.  Those are *not* the same object: Mathlib's
  `singularChainComplexFunctor C = SSet.chainComplexFunctor C ⋙ …` uses the
  **coproduct** presentation (`Sigma.ι` throughout), while `singFree` takes
  `ModuleCat.free R` levelwise.  A bridge is genuinely required — that is what
  `CartanSimplexExact.lean` is — and per §1.2a it must be rebuilt with signs
  rather than substituted.  Two encouraging facts:
  `singularChainSimplicialModule (R : Type) [CommRing R]` is already generic
  (`AlexanderWhitneyChainMap.lean` l.58), so only `transferCoeff` and
  `singularChainCx`, both pinned at `ZMod 2`, need generic twins.  The
  alternative — an explicit cone contraction on the singular chains of a convex
  set — is the thing cc-cartan deliberately avoided building, and it stays the
  fallback of last resort.

* **(B) Fallback: transport along an isomorphism to the iterated `tensorCx`**,
  and use `tensorCx_ker_le_range` by induction on `r`.  Costs a degreewise iso
  `tupCx C r ≅ tensorCx (tupCx C (r-1)) C` compatible with both differentials,
  which is `finsuppTensorFinsupp` plus a bidegree bookkeeping argument.  Take
  this only if (A)'s telescoping fights the `Finset.filter (· < j)` prefix sums.

Estimated: `OddPTuple` 300, `OddPTupleSign` 260, `OddPTupleD` 320,
`OddPTupleAction` 280, `OddPTupleFunctor` 200, `OddPTupleAcyclic` 380 lines.

---

## 4. The normalisation constant — the crux, stated honestly

### 4.1 Where it comes from

For `u ∈ C^q(X; F_p)` a cocycle, put

```
D_j(u) ∈ C^{pq - j}(X; F_p),     D_j(u)(σ) = ⟨ u^{⊗p} , Δ(e_j ⊗ σ) ⟩
```

and the operation with `i` given by `j = (q − 2i)(p − 1)`, so that `D_j(u)` has
degree `q + 2i(p−1)`.  The two ends of the range are

| `i` | `j` | degree | what it should be |
|---|---|---|---|
| `q/2` (`q` even) | `0` | `pq` | `u^p` |
| `0` | `q(p−1)` | `q` | `u` |

The classical operation is `P^i(u) = (-1)^i ν(q) D_{(q-2i)(p-1)}(u)` with
`ν(q) = (-1)^{mq(q-1)/2}(m!)^q`, `m = (p−1)/2`.  **Why it is a unit mod `p` is
trivial and needs no citation:** `m! = 1·2⋯m` with `m = (p−1)/2 < p`, a product
of integers prime to `p`, so `m! ∈ F_p^×`; and `(-1)^k ∈ F_p^×`.  (For the
record, Wilson gives `(m!)^2 = (-1)^{m+1}` in `F_p`, so `m!` is a square root of
`±1`; this is not needed anywhere.)  **Why it has that particular value is the
problem.**

### 4.2 The `i = q/2` end is free; the `i = 0` end is not

`j = 0` is easy and needs no constant.  `Δ(e_0 ⊗ −) : C(X) → C(X)^{⊗p}` is a
natural chain map agreeing in degree `0` with `x ↦ x^{⊗p}`.  So is the iterated
Alexander–Whitney diagonal
`Φ₀^{(p)}(σ) = Σ_{n_1+⋯+n_p = n} σ|_{[0..n_1]} ⊗ σ|_{[n_1..n_1+n_2]} ⊗ ⋯`.
By the **non-equivariant** uniqueness half (`acyclicModelsHomotopy` at
`Λ = F_p`, not the group ring) the two are naturally homotopic, so
`[D_0(u)] = [⟨u^{⊗p}, Φ₀^{(p)}(−)⟩] = [u ⌣ u ⌣ ⋯ ⌣ u] = [u]^p`, the last step
being the definition of the vendored `cochainCup` iterated.  **No constant.**

`j = q(p−1)` is the problem.  Write `Q^i(u) := [D_{(q-2i)(p-1)}(u)]`
(unnormalised).  What an abstract `Δ` gives:

* `Q^0_q(u) = c_q · u` for a universal `c_q ∈ F_p` — **not provable abstractly**;
* even granting it, `c_q` is not determined by any other property.  Concretely:
  `c_0 = 1` (degree `0` is `Δ(e_0 ⊗ x) = x^{⊗p}` and `t^p = t` in `F_p`);
  the Cartan formula at `k = 0` forces `c_{q+q'} = κ(q,q') c_q c_{q'}`; and the
  `p`-th power property at the top forces `κ ≡ 1` on even degrees, hence
  `c_{2k} = c_2^k`.  **Every one of these is satisfied for any value of `c_2`,
  including `c_2 = 0`.**  So no combination of naturality, additivity,
  instability, the `p`-th power property and Cartan pins `c_2`.  At `p = 2` the
  question does not arise because the explicit cup-`i` formula gives
  `Sq^0(u) = u ⌣_q u = u` on the nose (`cochainCupI_self`), constant `1`.

Two further dead ends, recorded so they are not re-explored:

* *"The off-diagonal terms die against the norm."*  True and useful — for a
  `(q,…,q)`-component, tuples with unequal entries have free `ℤ/p`-orbits and
  `⟨u^{⊗p}, N w⟩ = p⟨u^{⊗p}, w⟩ = 0`.  But it applies only to a `T`-invariant
  element, and `Δ(e_{q(p-1)} ⊗ ι_q)` is not one: `T e_j ≠ e_j`.  Chasing
  `(T−1)Δ(e_j ⊗ ι)` through the chain-map identity reproduces the coboundary
  formula and yields no information about the constant.
* *"Rescale the classes."*  `P^0 = id` and `P^{q/2} = p`-th power are two
  normalisations and there is one degree of freedom; substituting `y ↦ λy` moves
  the constant by `λ^{p-1} = 1`, so it cannot be moved.

### 4.3 The two routes, and the one cheap question that may kill the problem

**Route 1 (cheap, contingent).**  Keep the constant symbolic.  Define
`P̃^i := c_q^{-1} Q^i`, which satisfies `P̃^0 = id`, is multiplicative
(the rescaling is consistent precisely because `c_{q+q'} = κ c_q c_{q'}`), and
satisfies `P̃^{q/2}(u) = c_q^{-1} u^p`.  On a degree-2 class this reads
**`P̃(h) = h + κ h^p` with `κ = c_2^{-1} ∈ F_p^×` unknown**, and the Wu relations
become `P̃(γ_j) = e_j(y_i + κ y_i^p)`.

> **Ask to `sp-design` (blocking nothing, but it decides this lane's shape):
> re-run the §1.4 model test with `P(h) = h + κ h^p` for every `κ ∈ F_p^×`, and
> report whether the "forced ⟹ `γ_r(W) = 0`" column of the table in §1.4 is
> independent of `κ`.**  If it is, this lane never has to compute the constant
> and the plan drops §4 Route 2 entirely; the remaining obligation is only
> `c_q ≠ 0`, and `c_q = c_2^{q/2}` reduces that to `c_2 ≠ 0`.

Route 1 still owes `Q^0_q = c_q · id` (the *shape*, not the value) and `c_2 ≠ 0`.
The shape is available on the classes §1.4 actually uses, at no cost: every class
in `H^*(Y; F_p) = F_p[y_1,…]/(…)` is a polynomial in degree-2 Euler classes,
each pulled back from `ℂP^N` where `H^2` is one-dimensional, so `Q^0` on it is a
scalar by naturality and the scalar is `N`-independent by naturality along
`ℂP^N ↪ ℂP^{N+1}`; `t` and `x` are pulled back from spheres, same argument; and
everything else is generated from those by sums and products, where Cartan and
additivity carry `Q^0` along.  **`c_2 ≠ 0` is not available this way and remains
owed under Route 1 too.**

**Route 2 (expensive, unconditional).**  Construct `Δ` explicitly — the
`p`-fold "interval cut" formula generalising cc-steenrod's `cochainCupI`, with
signs and with two families for the two parities of the `W`-degree — and read the
constant off the top component, where the only surviving cut is the one that
assigns the whole vertex set to every slot.  This makes `P^0 = id`, instability
*and* the constant cochain-level facts, exactly as at `p = 2`.  Cost: cc-steenrod
spent ten modules (`SteenrodCut`, `SteenrodCutCancel`, `SteenrodCochain`,
`SteenrodCupEdge`, `SteenrodCoboundary`, …) on the sign-free binary case, whose
core `cut_coboundary_master` is already a telescoping argument valued in an
abelian group of exponent two.  Estimate 1500–2500 lines, and it is the single
highest-risk item in the whole program.

**Recommendation:** author Routes 0–5 of §7 (everything except the constant)
first; they are unconditional and they are what every other lane is waiting for.
Start Route 2 only if `sp-design`'s κ-sweep says the value matters, and even then
consider restricting the explicit construction to the top component alone.

> **Superseded by the lead's ruling of 2026-09-10; see §10.**  Route 1 is
> approved, the scoping is approved, Route 2 is forbidden for now, and a third
> route to `c_2 ≠ 0` — a descent on a small model — is to be evaluated first.
> §4.1 and §4.2 stand unchanged: they are why the question exists.

---

## 5. The operations, from an abstract `Δ`

### 5.1 The evaluation layer

```lean
def tupEval (K) (X) (r) (q : Fin r → ℕ) (u : ∀ j, singularCochainGroup K X (q j)) (k) :
    tupMod K X r k →ₗ[K] K                              -- t ↦ ∏ j, u j (t j) when degrees match, else 0
theorem tupEval_tupT (u : constant tuple) : tupEval … ∘ₗ tupT … = tupEval …
theorem tupEval_tupD  : tupEval … ∘ₗ tupD … = Σ_j ± tupEval (… δ(u j) …)
```

`tupEval` is **totalised**: it vanishes off its bidegree, so no degree hypothesis
survives anywhere downstream.  cc-cartan's finding that "no degree hypothesis
survives in composite B's evaluation, because the cup-`i` product of two cochains
of the wrong degrees is zero and that is the *same condition* as the pairing's
bidegree selection" is the same phenomenon and the same design.

`tupEval_tupT` for a **constant** tuple `u_j = u` is the invariance of §3.3 and it
is where `p` odd is used.  `tupEval_tupD` with every `u_j` a cocycle gives
`δ(u^{⊗p}) = 0`.

### 5.2 The operations and their well-definedness

```lean
noncomputable def oddD (p) (X) (q j : ℕ) (u : singularCochainGroup (ZMod p) X q) :
    singularCochainGroup (ZMod p) X (p*q - j)
theorem oddD_cocycle  (hu : δu = 0) : δ (oddD p X q j u) = 0
theorem oddD_natural (f : X ⟶ Y) : cochainPullback f _ (oddD p Y q j u) = oddD p X q j (cochainPullback f q u)
theorem oddD_coboundary (hu : δu = 0) (w) : oddD p X q j (u + δw) - oddD p X q j u = δ (…)
noncomputable def redPow (p) (i : ℕ) {q} (x : Hmod (ZMod p) X q) : Hmod (ZMod p) X (q + 2*i*(p-1))
```

`oddD_cocycle` is the calculation of §3.3 item 2 and has **no parity case
split**: `d_W e_j` is `s e_{j-1}` or `s^{p-1} e_{j-1}`, `Δ` is `Λ`-linear, and the
functional is `Λ`-linear into a trivial-action module, so `⟨u^{⊗p}, s·y⟩ =
(1 − 1)⟨u^{⊗p}, y⟩ = 0` and `⟨u^{⊗p}, s^{p-1}·y⟩ = ⟨u^{⊗p}, N y⟩ = p⟨…⟩ = 0`.
That both halves die at once is the odd-`p` simplification and it should be
stated as one lemma `tupEval_smul_grS`.

**Instability is free.**  `redPow p i` for `2i > q` has `j = (q − 2i)(p−1) < 0`,
so there is no `e_j`; define `redPow p i x = 0` there, by the same `dite` the
degree forces.  `P^i = 0` for `2i > q` is then `rfl`.  The mod-2 tree got
instability from `cochainCupI_of_degree_ne`; here it is definitional.  What must
be checked is that the Cartan formula produces zeros in that range, which it does
because the comparison only ever mentions `e_a` with `a ≥ 0`.

**Independence of the choice of `Δ`** is `acyclicModelsHomotopy` plus the fact
that the functional annihilates boundaries when `u` is a cocycle — cc-cartan's
`fourEvalMor`/`fourEval_compA_eq_compB` pattern, where "two of the three terms of
the homotopy identity die".  Here the `d ∘ s` term dies because the functional
annihilates boundaries and the source-differential term dies by
`tupEval_smul_grS`.

### 5.3 Additivity

`(u+v)^{⊗p} = Σ_{S ⊆ Fin p} u^S v^{S^c}`.  The `2^p − 2` mixed terms are
permuted freely by `ℤ/p`, so summing over an orbit gives
`⟨mixed, N·Δ(e_j ⊗ σ)⟩ = ⟨mixed, Δ(N e_j ⊗ σ)⟩`, and **`N e_j` is a boundary in
`W` for every `j`** (§2.1) — so each orbit contributes `⟨mixed, dΔ(w ⊗ σ)⟩ ±
⟨mixed, Δ(w ⊗ ∂σ)⟩`, i.e. a coboundary.  Hence `redPow` is additive on classes.
This is the classical argument; the only input that is not already needed
elsewhere is `grNorm_eq` together with `N = s·s^{p-2}`.

Estimated: `OddPEval` 300, `OddPDiagonal` 260, `OddPCochain` 320,
`OddPClasses` 380, `OddPAdditive` 240, `OddPTopPower` 300 lines.

---

## 6. The Cartan formula

### 6.1 The route, and why the target is `C^{⊗2p}` and not `C^{⊗p²}`

The mod-2 internal route compares two natural equivariant chain maps
`W ⊗ C(X) → C(X)^{⊗4}`.  The `4` is `2 · 2` = (number of tensor slots of `Φ`) ×
(number of cochains being multiplied), **not** `2²` in the sense of `p²`.  So at
odd `p` the target is `C(X)^{⊗2p}`, which in the flat model of §3 is the same
object at `r = 2p` and inherits every lemma.  No new construction.

```
A = (slotwise Φ₀) ∘ Φ                        : W ⊗ C → C^{⊗p} → C^{⊗2p}
B = shuffle ∘ (Φ ⊗ Φ) ∘ regroup ∘ (ψ_W ⊗ Φ₀) : W ⊗ C → C^{⊗2p}
```

* `slotwise Φ₀` carries **no Koszul sign**, because `Φ₀` has degree `0`.  This is
  a real saving and should be stated as such.
* `A` intertwines `T` with the **block shift by two** on `2p` slots; `B` naked
  intertwines `T` with the shift-by-one-inside-each-block; the riffle shuffle
  `x_1…x_p y_1…y_p ↦ x_1y_1x_2y_2…x_py_p` conjugates one to the other.  At
  `p = 2` this is cc-cartan's `(13)(24)` versus `(12)(34)` and `midSwap`; the
  general statement is the same conjugation and the index-level proof is again
  `rfl` plus the riffle's Koszul sign
  `ε = Σ_j |y_j| · Σ_{l>j} |x_l|`.
* The evaluating functional is `u ⊗ v ⊗ u ⊗ v ⊗ ⋯` (`2p` slots), invariant under
  the block shift by the parity lemma of §3.3, **not** invariant under the naked
  action — which is the same forcing cc-cartan records ("under `(12)(34)` the
  evaluation step does not typecheck at all").
* `A` and `B` are defined **by their values on the `Λ`-basis of the free source
  and extended with `Module.Basis.constr`**, never assembled as tensor products
  of maps, because `ψ_W` and `Φ₀` are individually not `Λ`-linear.  cc-cartan's
  instruction, and it applies verbatim.

### 6.2 `ψ_W`, the resolution's coproduct

`B` needs `ψ : W → W ⊗_{F_p} W` (diagonal action), `Λ`-linear, counital.  Two
options:

* **Explicit.**  Over `Λ = F_p[s]/(s^p)` the classical formula has the shape
  `ψ(e_{2i}) = Σ_{a+b=i} e_{2a} ⊗ e_{2b} + Σ_{a+b=i-1} Σ_{0≤σ<τ<p} T^σ e_{2a+1} ⊗ T^τ e_{2b+1}`
  and a companion in odd total degree.  **I will not write this from memory.**
  The deliverable is: solve the chain-map recursion symbolically, confirm the
  closed form, and only then state it.  This is a numeric obligation and it goes
  to MSI (§9), not to this laptop.
* **Abstract.**  `W` is free over `Λ` and `W ⊗ W` is positive-degree acyclic
  (Künneth over a field, or the §3.4 telescoping at `r = 2`), so
  `acyclicModelsMap` over a **one-object category** — the comparison theorem for
  projective resolutions is the acyclic-models theorem with `C := Unit` — gives
  `ψ` with no formula.  Cheaper, but then `B`'s value carries unknown
  coefficients `c_{a,b,σ} ∈ F_p` and the Cartan formula comes out with an
  unknown constant `κ`, which folds into §4's problem rather than adding to it.

**DECISION REVERSED, 2026-09-10, and the explicit `ψ` wins.**  The reasoning
above assumed writing `ψ` down was the expensive option.  `sp-design` has now
**solved** the recursion rather than recalled it, so it is the cheap one, and the
abstract route is the expensive one because it *creates* an unknown constant
where the explicit route retires one.

The closed form, verified block by block at `p = 3, 5, 7` over every degree
`n ≤ 2(p-1)`:

```text
ψ(e_n) = Σ_{a+b=n}   e_a ⊗ e_b                          when a is even
                     e_a ⊗ T e_b                        when a is odd, b even
                     Σ_{0 ≤ u < v < p} T^u e_a ⊗ T^v e_b   when a, b both odd
```

obtained from an explicit `F_p`-linear contraction of `W`
(`h(T^j) = 1 + T + ⋯ + T^{j-1}` in even degrees, `h(T^j) = [j = p-1]` in odd
ones), whence `H := h ⊗ 1` contracts `W ⊗ W` and `ψ` is built degree by degree in
time linear in the size, with the chain-map identity asserted at every step.
This discharges the "I will not write this from memory" of the original §6.2.

**The reduced coefficients, and why the competing terms die.**  Writing `c̄_{a,b}`
for the coefficient summed over the twist: `c̄ = 1` when `a` is even, and when `a`
is odd and `b` even; and `c̄ = 0` when `a` and `b` are **both odd**.  The
vanishing is one line of arithmetic, and I checked it: the `(odd,odd)` block's
reduced coefficient is the number of pairs `u < v` in `[0,p)`, which is
`C(p,2) = p·((p-1)/2)`, divisible by `p` because `(p-1)/2` is an integer for `p`
odd.  The integral count is not zero; the reduction to `F_p` is what kills it.

**Consequence: `C = 1`, and instability is not needed for the bridge.**  In the
Cartan identity at index `2(p-1)` for two degree-1 cocycles, `a + b` is even so
`a` and `b` share a parity.  Both odd gives `c̄ = 0`, which kills exactly the two
competing terms `(p, p-2)` and `(p-2, p)`.  Both even with `a ≠ p-1` forces one
of the two factors into a negative cochain degree, where the group is zero.  And
`p - 1` is even, so the surviving term is exactly `(p-1, p-1)`, with `c̄ = 1`.
**SUPERSEDED within the hour, and the superseded version was false.**  `C = 1`
is the reduced **coproduct** coefficient alone.  It is not the Cartan
coefficient: the riffle Koszul sign and the reordering of the evaluation
contribute the other factors, and the true value is

```text
κ(1,1) = (-1)^{(p-1)/2} ,     c_2 = κ(1,1) · c_1² = -1   for every odd prime,
```

`c_2 = -1` having also been computed **directly**, from the equivariant diagonal
on the models evaluated on the fundamental class of the torus, at
`p = 3, 5, 7, 11`.  Wilson reconciles the two routes:
`κ · c_1² = (-1)^{(p-1)/2}·(-1)^{(p+1)/2} = (-1)^p = -1`.

**So `c_2 = c_1²` is false**, and not marginally: I checked it and it fails at
`p = 3, 7, 11` and holds at `p = 5` only by coincidence.

| `p` | `c_1` | `c_1²` | `κ(1,1)` | `c_2` |
|---|---|---|---|---|
| 3 | 1 | 1 | −1 | −1 |
| 5 | 2 | 4 | +1 | −1 |
| 7 | −1 | 1 | −1 | −1 |
| 11 | −1 | 1 | −1 | −1 |

Had the earlier version been adopted it would have put a false statement into the
tree.  The endpoint would have survived, since the value never enters Step D, but
anything later reading the constant would have broken.  My objection reached only
half of this: I argued the counit pins the wrong corner of the splitting range.
The other half, that even the right corner's coproduct coefficient is not the
whole Cartan coefficient, `sp-design` found themselves.  **The general lesson is
the lane's own and now has three instances: a constant is not known until it is
computed end to end, and a partial computation that stops at one of its factors
looks exactly like the whole answer.**

**Consequences for this lane.**  `c_2 ≠ 0` no longer depends on the bridge at
all, since `c_2 = -1` is computed directly; the bridge becomes the independent
cross-check on the chain-map identity that I said I would run anyway, which is
now its best use.  The route to `c_2 ≠ 0` should be whichever is cheapest in Lean
*knowing* the answer.

**Prerequisite to name now, not at the end**: the identity needs two degree-1
classes with nonzero product, and at an odd prime a degree-1 class squares to
zero, so they must be distinct.  The space is `S¹ × S¹`, reached through
`CharClass/CohomologyKunnethSphere.lean` rather than through sphere cohomology
alone.

### 6.2a RETRACTED — the even-degree lemma pins the opposite corner

**Struck 2026-09-10, by me, hours after the lead accepted it.**  The derivation
below is correct and its stated consequence is false, for exactly the reason I
had raised against the earlier bridge argument.

The index dictionary, which is what I should have written down first:

```text
Cartan, in D-form:   D_i(u ⌣ v)  =  Σ_{a+b=i}  c̄_{a,b} · (D_a(u) ⌣ D_b(v))
Dictionary:          Q^s(u) := [D_{(q-2s)(p-1)}(u)]
                     s = 0    ↔  a = q(p-1)     the TOP resolution index
                     s = q/2  ↔  a = 0          the BOTTOM
c_q is defined at the TOP end, by Q^0_q = c_q · id.
```

*Multiplicativity of the constants* is read at `i = (q+q')(p-1)`, where the
ranges force `a = q(p-1)` and `b = q'(p-1)`, so it involves `c̄` at the
**top-top** corner.  *The lemma below* is read at `i = 0`, where instability
forces `a = b = 0`, so it pins `c̄` at the **bottom-bottom** corner — which is the
counit case, already known.  Opposite corners; nothing connects them.

So `c_{q+q'} = c_q c_{q'}` does **not** follow, and the claim that the programme
rests on a single number is not established by this argument.  Both are struck.

That is the second corner confusion in this lane in one day and the first one of
mine.  The cure is mechanical rather than attentional: the two ends of the
splitting range read alike in prose, so the dictionary above now lives in the
plan and every coefficient claim must name which end it is about.

**Unaffected**: `c_2 = -1`, computed directly on the torus, goes through none of
this.

**The replacement, ruled by the lead, and it is better than what it replaces**
because it sits inside the Cartan deliverable rather than beside it.  Read the
Cartan identity at the **top** resolution index, where the ranges force both
split indices to their maxima `q(p-1)` and `q'(p-1)`.  Since `p - 1` is even,
both are even **for every `q`**, so `sp-design`'s reduced coefficient is `1`
there and the whole coefficient is the riffle Koszul sign — a closed form in
`(q, q')`.  Hence

```text
c_{q+q'} = κ_top(q,q') · c_q · c_{q'} ,   κ_top an explicit unit,
```

every even constant is a computed unit times a product of `c_2`s, and the
normalisation making `P̃` multiplicative on even classes is the classical
`ν(q) = (-1)^{m q(q-1)/2}(m!)^q` up to this lane's sign convention.  Three
deliverables, all inside §6: the Cartan identity with the explicit coproduct
coefficients; the closed form of `κ_top` for even `q, q'`; the normalisation and
its multiplicativity on even classes, which is all Step D consumes.
`sp-design` is deriving `κ_top` and cross-checking `c_4`, `c_6` on products of
circles.

### The degree-one constant now has two independent derivations

`sp-design`'s chain-level construction of the diagonal on the models and the
`Δ¹` cochain descent are different machinery, and they agree on `c_1` at every
prime tested.  Recorded because **the descent is the part this lane will
formalise**, and it now has corroboration that does not share its method.

The retracted derivation, kept because it is the evidence for the rule:

```lean
theorem cartanCoeff_even_eq_one (q q' : ℕ) (hq : Even q) (hq' : Even q') :
    κ q q' = 1
```

Proof.  Evaluate the Cartan formula at the **top** index `n = (q + q')/2`.  By
instability every term `Q^a(u) ⌣ Q^b(v)` with `a + b = n` vanishes unless
`2a ≤ q` and `2b ≤ q'`, which with `a + b = n` forces `a = q/2` and `b = q'/2`.
Both survivors are top operations, so the surviving term is `u^p ⌣ v^p`, which
is `(u ⌣ v)^p` in even degrees.  The left side is `Q^n(u ⌣ v) = (u ⌣ v)^p` by
the top-operation property.  Hence `κ · (u ⌣ v)^p = (u ⌣ v)^p`, and a projective
space of dimension at least `p(q + q')/2` supplies a class whose `p`-th power
does not vanish.  ∎

Consequence: `c_{q+q'} = c_q c_{q'}` for even `q, q'`, so `c_{2k} = c_2^k` and
**the programme rests on the single number `c_2`**.  With `c_1 = ((p-1)/2)!` in
hand, the only remaining link is the odd×odd coefficient of §"The bridge",
which `sp-design` is computing.  Nothing may be authored on that bridge until
the number is in this report; the lead's instruction, and it is the right one.

### 6.3 What the comparison then gives

`A` and `B` agree in degree `0` (both send `e_0 ⊗ x` to `x^{⊗2p}` for a
`0`-simplex `x`), so `acyclicModelsHomotopy` applies; evaluating against
`u⊗v⊗u⊗v⊗⋯` kills two of the three terms of the homotopy identity and leaves the
Cartan formula as an identity of cochains, then of classes.  The reindexing of
the sum into `P^i` shape must happen **after** passing to classes — cc-cartan's
hardest-won finding, twice restated in their report: at cochain level it needs one
number spelled two ways inside the *type* of a cochain, and no lemma can bridge
that; in the total ring degrees are plain naturals and `of_cohCast` absorbs
everything.  So the published shape is theirs:

```lean
def CartanOfP (p) (X : TopCat.{0}) : Prop :=
  ∀ (n a b : ℕ) (x : Hmod (ZMod p) X a) (y : Hmod (ZMod p) X b),
    TotalH.of X _ (redPow p n (cupK x y)) = ∑ i ∈ Finset.range (n+1), … * …
```

Estimated: `OddPWDiagonal` 220, `OddPCompA` 380, `OddPCompB` 900,
`OddPCompBChain` 700, `OddPShuffle` 300, `OddPCartanEval` 500,
`OddPCartanClasses` 400 lines.  The `CompB` chain-map identity is the one genuine
computation, as it was at `p = 2`, and cc-steenrod's post-mortem says its
cancellation is **not uniform across bidegrees** — three bidegrees, three proofs,
and the degenerate ones are not mirror images.  Budget for that.

---

## 7. Landing order

Each step is a probe on its own; nothing below is authored before `sp-design`
signs off on this plan.

| # | modules | unblocks |
|---|---|---|
| 0 | `OddPGroupRing`, `OddPResolution` | everything; also the cheapest possible smoke test that `Λ` elaborates |
| 1 | `OddPSource`, `OddPSourceFree` | the `FreeOnModels` side of both comparisons |
| 2 | `OddPTuple`, `OddPTupleSign`, `OddPTupleD`, `OddPTupleAction` | the target carrier, arity-generic |
| 3 | `OddPTupleFunctor`, `OddPTupleAcyclic` | `AcyclicOnModels`; **`Δ` exists after this** |
| 4 | `OddPDiagonal`, `OddPEval`, `OddPCochain` | `D_j`, cocycle, naturality |
| 5 | `OddPClasses`, `OddPAdditive`, `OddPTopPower` | `redPow`, additive, natural, instability (free), `P^{q/2} = p`-th power |
| 6 | `OddPWDiagonal`, `OddPCompA`, `OddPShuffle` | the two composites' easy halves |
| 7 | `OddPCompB`, `OddPCompBChain` | the comparison's hypothesis |
| 8 | `OddPCartanEval`, `OddPCartanClasses` | `CartanOfP` |
| 9 | `OddPZero` (constant) — Route 1 or Route 2 of §4 | `P^0 = id`, hence `P(h) = h + h^p` |

Steps 0–5 are unconditional and are what `sp-evenside` needs first.  A usable
partial export exists after step 5: natural additive operations with instability
and the top `p`-th power, everything except multiplicativity and `P^0`.

---

## 8. Design rules adopted wholesale from the mod-2 lanes

These are not restatements for their own sake; each one cost the `F₂` lanes
probe rounds and each applies verbatim here.

* **Totalise.**  Output degree a free parameter, value `0` off the diagonal.
  Removes every cast.  (`faceVal`, `padIdx`, `padTen` at `F₂`; `tupD`, `tupEval`
  here.)
* **Never let a degree be an expression in the inputs.**  `a + 1 + b` and
  `(a+b)+1` are propositionally but not definitionally equal for variable `b`.
* **Index types must be `abbrev`.**  `rw` checks type-correctness at `instances`
  transparency and will not unfold a plain `def`; `attribute [local reducible]`
  cannot be set for an imported declaration, so the fix must be at the
  definition.
* **Junction lemmas.**  Where one number arrives spelled two ways, state the
  reconciliation as a one-line lemma with the degrees free and the equation as a
  hypothesis, on an abstraction whose *result* type does not mention the index,
  and cross it with `congrArg` before any block lemma fires.
* **Cross definitional junctions with terms, never rewrites**, wherever an
  instance is pinned by an `@`-application.
* **A definition is pinned down only by the first property that distinguishes it
  from its plausible neighbours.**  cc-steenrod's `compBTerm` was wrong for four
  green probes because linearity, the degree-zero value and the Leibniz rule all
  hold of the wrong map too.  Here the analogous hazard is the **riffle sign**
  and the **block-shift convention**: every property except the chain-map
  condition holds of the unshuffled grouping.  Write the shuffle in, do not
  promise to inline it later.
* **Grep for uses, not declarations**, and re-check a negative claim about the
  tree before repeating it.

---

## 9. Model tests owed (all on MSI, never locally)

Per the standing orders, nothing runs on this laptop.  Three numeric obligations,
in priority order:

1. **The κ-sweep** (§4.3) — `sp-design`'s script, one extra parameter.  Decides
   whether §4 Route 2 and §6.2's explicit `ψ` are needed at all.  Highest value
   per minute in the whole lane.
2. **`ψ_W`'s closed form** — solve `dψ = ψd` degree by degree over `F_p[s]/(s^p)`
   for `p = 3,5,7` and confirm the closed formula before it is stated in Lean.
3. **The riffle sign and the conjugation** `sh ∘ (shift-in-block) = (shift-by-2) ∘ sh`
   — check on explicit small tuples for `p = 3,5` and degrees up to `4`, because
   a sign convention that is wrong by `(-1)^{something even}` survives every
   small test and dies at the chain-map condition.

---

## 10. The lead's ruling (2026-09-10), and what it changed

Received after the plan was routed.  Recorded here in full effect, with my
evaluation of the part I was asked to check.

**(a) The κ-sweep is decided by a scaling symmetry, so I am not waiting for it.**
The lead's argument: if `P` satisfies the axioms with `P(h) = h + h^p`, then
`P'^i := κ^i P^i` satisfies every axiom (the total `P'` is still a ring
homomorphism because `κ^{a+b} = κ^a κ^b`) with `P'(h) = h + κ h^p`, and the
universal polynomial for `P'(e_j)` in weight `j + i(p−1)` is `κ^i` times the one
for `P`.  So the per-`j` Wu relations of the κ-family are the `κ = 1` relations
rescaled by nonzero scalars, the solution space is identical, and §1.4's verdict
is κ-independent.  I have checked this and agree; it is cleaner than the
numerical sweep and it makes §4's Route 2 unnecessary **provided `c_2 ≠ 0`**.
`sp-design` confirms numerically for the record.

**(b) Scope approved, and it is exactly Step D's reach.**  `Q^0 = c_q · id` is to
be delivered on the subring generated by degree-2 Euler classes of line bundles,
the sphere classes `t` and `x`, and their pullbacks, with `c_{q+q'} = c_q c_{q'}`
on even degrees and naturality; `P̃ := c_q^{-1} Q` is normalised on **even
degrees only**.  The lead's justification, which I am recording because it is the
thing a later reader will want: `H^*(N) = Λ(t) ⊗ Λ(x) ⊗ H^*(Y)` with `H^*(Y)`
generated by Euler classes, and the splitting-principle towers over `N` are
generated over `H^*(N)` by tautological Euler classes via Leray–Hirsch.  So the
subring is everything Step D touches, and `P(z) = z` comes out as
`c_{2n+2} = c_2^{n+1}` rather than needing an odd-degree case.

**(c) `c_2 ≠ 0` is a theorem I owe, on the critical path, and Route 2 is
forbidden.**  Route 3, to be evaluated first: a descent on `Δ^1` using only the
chain-map property of the abstract `Δ` and its degree-0 component.

### My check of the Route 3 descent — three findings

I have worked the lead's sketch through.  Two of its steps check out exactly as
stated; the third has a discrepancy at one endpoint, and there is a growth risk
that the sketch does not mention.

**Checks that pass.**

* `(δf)^{⊗p} = δ_tot(f ⊗ (δf)^{⊗(p−1)})` on the nose, with **no sign**: the
  Koszul sign for differentiating slot `0` is `(-1)^0`, and every other slot
  carries `δ(δf) = 0`.
* The point terms genuinely vanish, and for a slightly sharper reason than
  "every word carries a `δf` factor".  On a point, `δf` is not merely zero on
  non-degenerate simplices — it is the zero cochain, because the restriction of
  `f` to a point is constant and `δ` of a constant `0`-cochain is `0`.  So the
  vanishing survives the degenerate `1`-simplices of a point, which is the case
  a "dimension" argument would miss.  Worth stating as its own lemma.

> **RETRACTED 2026-09-10, after `sp-design`'s review.**  There is no
> discrepancy and no endpoint irregularity; the paragraph below contains an
> arithmetic slip and its conclusion is false.  I wrote
> `λ_{p-2}(-1)^{p-2} = (p-1)(-1)^{p-1}`, reading `(-1)^{p-2}` as `(-1)^{p-1}`.
> For `p` odd, `p-2` is **odd**, so `λ_{p-2}(-1)^{p-2} = (p-1)·(-1) = 1-p ≡ +1`,
> which is exactly what the alternating pattern wants.  **The telescope closes
> with `λ_i = i + 1` and no endpoint correction**, and I have confirmed it
> numerically at `p = 3, 5, 7, 11, 13`.
>
> The sign vector is not an anomaly either.  My `+, +, −` is correct as a
> function of the **rotation index** `k`, and `T^k v_0 = ε_k v_{p-k}`; read by
> the **position** `j = p-k` of the `f`, `ε_{p-j} = (-1)^{p-j-1} = (-1)^j`
> because `p-1` is even.  So `N v_0 = Σ_j (-1)^j v_j` on the nose: one vector
> read in two orders, not two patterns.  Also confirmed numerically at those
> five primes.  This is **not** the composite-B hazard, and I invoked that
> precedent wrongly.
>
> The lesson is not about signs.  I reported a *blocking* obstruction on the
> strength of a hand computation I did not check numerically, in a lane whose
> own report tells everyone to model-test before claiming.  The growth risk in
> the next paragraph, which I did not miscompute, remains the genuinely open
> item.  Kept below rather than deleted, because a retraction that removes the
> error also removes the evidence for the rule.

**The discrepancy.**  With `w_i := (δf)^{⊗i} ⊗ f ⊗ f ⊗ (δf)^{⊗(p−2−i)}` and
`v_m :=` the word with `f` in slot `m`, the Koszul signs give

```text
    δ_tot w_i = (-1)^i (v_i + v_{i+1})
```

— both slots carry prefix degree `i`, because the first `f` has degree `0`.  So
the coefficient family `λ_i = i + 1` the lead proposes yields, for the interior
indices, coefficient `(j+1)(-1)^j + j(-1)^{j-1} = (-1)^j` on `v_j`, which is the
alternating pattern and is right.  The two ends are not interior: `j = 0` gives
`+1`, matching, but `j = p−1` gives `λ_{p-2}(-1)^{p-2} = (p−1)(-1)^{p-1} = −1`
with `p` odd, where the alternating pattern wants `+1`.  So the telescoping
produces `Σ_j (-1)^j v_j − 2 v_{p-1}`, not `Σ_j (-1)^j v_j`.

Either the coefficients need an endpoint correction, or — more likely — the sign
pattern of `N^*` on this bidegree is not `(-1)^j`.  I computed the first two
terms directly: `v ∘ T^0 = v_0` with sign `+1`, `v ∘ T^1 = v_{p-1}` with sign
`+1` (the moved factor has degree `0`, so the Koszul sign is trivial), and
`v ∘ T^2 = −v_{p-2}` (the moved factor now has degree `1` and passes `p−2`
factors of degree `1`, and `p−2` is odd).  So the pattern is `+, +, −, …`, which
is **not** `(-1)^j` and is exactly the kind of endpoint irregularity that makes
the two ends behave differently.  This is the same shape of hazard cc-steenrod
recorded for composite B: the cancellation is not uniform, and the degenerate
indices are not mirror images of each other.

**The growth risk, which is the real one.**  The descent has `p − 1` levels, and
at level `k` the cochains are words with `k` copies of `f` and `p − k` copies of
`δf`, so the coefficient vector at level `k` is indexed by the `C(p, k)`
placements.  Level `1` is the lead's `w_i` family; level `p − 1` is the single
word `δf ⊗ f^{⊗(p−1)}` the answer is read off from.  A Lean proof generic in `p`
needs a **closed form for the coefficient vector at every level**, not just the
first, and nothing in the sketch supplies one.  If the recursion has no closed
form the descent proves `c_2 ≠ 0` for each fixed small `p` and not in general,
which would leave the general theorem short.  The lead's staging (`p = 3` first,
then generic) already assumes two computations rather than one; I am flagging
that the second may not exist in closed form, and that this should be settled by
`sp-design`'s numerics **before** any Lean, since it decides whether the lane can
close the general statement at all.

### What I therefore asked `sp-design` to compute

Beyond the `c_1`, `c_2` values for `p = 3, 5, 7, 11, 13` the lead has already
requested: the **sign vector** `ε_m` of `N^*` on the bidegree `(0,1,…,1)`, and
the coefficient vectors at **every** level of the descent for those primes, so
that the closed form in `p` can be recognised or ruled out.

## GREEN (with job counts)

> **Caveat DISCHARGED 2026-09-10, and the hazard was real here.**  The purging
> helper's first run on `cs-limit` reported **`purged 234 stale artifact sets
> (source newer than olean)`**, so this clone did carry stale imports and the
> earlier greens were resting on some of them.  All seven rebuilt green under the
> purge, together with three of the six new modules, in one probe:
> **`purged 234`, ten of thirteen targets built, `2180` jobs.**  The three that
> failed did so on their own errors, listed under AUTHORED below.
>
> Worth stating plainly because it nearly went the other way: a replayed stale
> olean leaves **no line in the log**, so the `Built`-not-`Replayed` discipline
> cannot see it.  Marking the greens provisional and re-running was the only
> thing that would have caught it, and the count says it was not a theoretical
> risk.

**ALL THIRTEEN OWNED MODULES BUILD TOGETHER, FROM DELETED ARTIFACTS, UNDER THE
PURGING HELPER**: `cs-limit`, 2026-09-10, `Build completed successfully (2181
jobs)`, `EXIT=0`.  Every one of the thirteen has its own `✔ … Built …` line in
that single log and **not one `Replayed` line**, counted mechanically:
`grep -c Built … = 13`, `grep -c Replayed … = 0`, `purged 0`.  The artifacts were
deleted first precisely so the count would mean something.

| module | build |
|---|---|
| `OddPSign` | 19s |
| `OddPGroupRing` | 22s |
| `OddPFrobenius` | 23s |
| `OddPModule` | 23s |
| `OddPResolution` | 25s |
| `OddPTuple` | 28s |
| `OddPNorm` | 22s |
| `OddPSource` | 26s |
| `OddPSourceComplex` | 53s |
| `OddPSourceDD` | 44s |
| `OddPSourceFunctor` | 29s |
| `OddPSourceFree` | 30s |
| `OddPSingular` | 34s |

So §7 steps 0 and 1 are closed and step 2's carrier is landed: the group ring,
the alternating resolution, the source functor with its differential, `d ∘ d = 0`,
functoriality, freeness on the models, the concrete signed boundary, and the
flat arity-generic tuple carrier.  No `sorry`; nothing reachable from the root.

The earlier, superseded green:  The two maximal
elements are named in the log as freshly `Built` (`OddPResolution` 20s,
`OddPSource` 25s); the other three are separate targets of the same green build,
and none of them exists in the node-side tree, so none can be a replayed stale
olean.  As of 2026-09-10 that argument has a second leg: the lead has
de-hardlinked `cs-limit`'s build directory in place, so it holds real copies with
zero hard links to the main tree or to any other clone, and a `Replayed` line
there can now only replay an artifact this clone built from these sources.

* `GroupApproximation/CharClass/OddPGroupRing.lean` — `GroupRingZMod`, `grGen`,
  `grGen_pow_card`, `grS`, `grNorm`, `grNorm_mul_grS`, `grS_mul_grNorm`.
* `GroupApproximation/CharClass/OddPFrobenius.lean` — the `CharP` instance and
  `grS_pow_card`.
* `GroupApproximation/CharClass/OddPModule.lean` — `pow_mod_of_pow_card_eq_one`,
  `galEndP`, `galAlgHomP`, `moduleOfOrderP`, `moduleOfOrderP_smul`.
* `GroupApproximation/CharClass/OddPResolution.lean` — `altCoeff`, `altDiff`,
  `altCoeff_mul_succ`, `altDiff_comp`, `altResolution`, `altResolutionBasis`,
  `Wodd`.
* `GroupApproximation/CharClass/OddPSource.lean` — `OddPBoundaryData`,
  `OddWTensor`, `oddDiffW`, `oddDiffS`, `oddDiffGen`, `oddDiff` and their six
  computation lemmas.

No `sorry` anywhere.  None of these is imported by `GroupApproximation.lean` or
by any existing module, so no root build can be affected by them.  `WSIndex` and
`stdSimplexTop` are **reused** from `CartanDiagonalModule.lean` rather than
redefined: neither mentions the coefficient ring, and a second declaration of
either in this namespace would be a root-only failure invisible to every probe.

### What the two red rounds cost, and what they were

Both were Mathlib-presentation issues, neither was mathematics.

1. `Finsupp.single_injective` for the injectivity of the constants of a
   `MonoidAlgebra`.  At this pin a `MonoidAlgebra` is a **structure** wrapping
   its coefficient `Finsupp`, not the `Finsupp`, so no `Finsupp` lemma applies;
   the live name is `MonoidAlgebra.single_right_injective`.  The error is a bare
   "Application type mismatch" that reads like a binder-name problem.
2. `-DwarningAsError=true` makes the auto-included-section-variable linter fatal:
   `altCoeff` needs no ring structure, so the section's `[CommRing Λ]` is
   included in the two `altCoeff_even`/`altCoeff_odd` statements and unused.
   `omit [CommRing Λ] in` before each is the fix.

Both are in `FLEET_TRAPS.md`, together with the design note that paid for itself:
the first red blocked three downstream modules only because the Frobenius
consequence was sitting in the same file as the group ring.  Splitting it into
`OddPFrobenius.lean` cost one file and turned a blocking red into an isolated
one.

### The three cancellations are green

`GroupApproximation/CharClass/OddPSourceComplex.lean`, log line
`✔ [2009/2010] Built GroupApproximation.CharClass.OddPSourceComplex (41s)` —
**Built**, not Replayed.  Contents: `altCoeff_smul_oddDiffW` (resolution then
resolution), `linearCombination_oddDiffS_bd` (`∂∂ = 0`), `oddMixed_terms_eq` (the
two mixed terms before their signs), plus `neg_one_pow_add_succ`,
`altCoeff_succ_junction` and the three `Finsupp` helpers over an arbitrary
`[CommRing R]`.

The mixed cancellation is where the mod-2 proof and this one part company.  At
`p = 2` the two terms are *equal* and die because two is zero; here they are
`c · (-1)^{i-1}` and `(-1)^i · c` times the same element and die because
`(-1)^{i-1} + (-1)^i = 0`.  That single fact is the entire reason `oddDiffS`
carries a sign, and §2.3's argument that the sign cannot be reindexed away is
what says no alternative exists.

### `d ∘ d = 0` is green, and §2 is closed

`GroupApproximation/CharClass/OddPSourceDD.lean`, log line
`✔ [2010/2010] Built GroupApproximation.CharClass.OddPSourceDD (67s)`,
`Build completed successfully (2010 jobs)`, `PROBE GREEN` — **Built**, not
Replayed.  `oddScalar_junction` and `oddDiff_oddDiff`.

That closes everything the lead authorised: the group ring, the resolution, the
source functor and its chain-complex condition.  **`W ⊗ C(X)` is a complex of
`Λ`-modules at odd `p`, with no `sorry` and no hypothesis beyond an abstract
signed singular boundary.**  What §2 still owes before the acyclic-models theorem
can be applied to it is the functoriality in `X` and the freeness on the models
(`OddPSourceFunctor.lean`, `OddPSourceFree.lean`), both of which are
cc-cartan's `CartanSourceFunctor.lean` with the coefficient ring changed and no
new mathematics; the one delicate field is the `ULift` reindex their traps
section flags.

## AUTHORED, UNVERIFIED

**Nothing.**  Everything this lane has written is in the thirteen-module green
above.

### What the six outage-written files cost to green, and why

They were authored without a compiler during the network outage and needed three
probe rounds.  Every failure was a spelling, an import or a tactic detail; not
one was mathematical.  The five that recurred are worth naming because four of
them are the *same* failure wearing different messages.

* **A name that exists in a module you have not imported.**  Twice, and the
  message points away from the cause both times.  `faceSimplex` reported as
  `Unknown identifier`, which reads as a missing `open`; it is in
  `AlexanderWhitneyFaceMaps.lean`, which `CupProduct.lean` does not import.
  `Field (ZMod p)` reported as `failed to synthesize IsRightCancelMulZero
  (ZMod p)[X]`, an error naming the polynomial ring and never mentioning `ZMod`;
  the instance is in `Mathlib/Algebra/Field/ZMod.lean`, not in
  `Mathlib/Data/ZMod/Basic.lean`.  Adding an `open`, or supplying the instance by
  `haveI := inferInstance`, fixes neither, and the second attempt fails *at the
  `haveI` line*, which is the tell.
* **A file or directory that no longer exists at the pin.**  `Mathlib/Algebra/GroupPower/`
  and `Mathlib/Algebra/CharP/Polynomial.lean`.  Caught before probing, by
  checking imports against the pin rather than from memory.
* **A number spelled two ways inside a type.**  Already in the traps section;
  it recurred here as a `0` typed at a `ModuleCat` carrier rather than at the
  `Finsupp`, where `rw [Finsupp.mapDomain_zero]` cannot match and the term
  `exact Finsupp.mapDomain_zero` closes it.
* **`rw`'s trailing `rfl` not firing** on a goal whose two sides print
  identically.
* **An orientation slip**: `exact h.symm` where the goal wanted `h`.

The lesson I am keeping: *before treating an unknown identifier as a namespace
problem, grep for the declaration and check whether its file is in your import
closure.*  Checking names against the pin during the outage caught six errors for
free; the two that still got through were both about which module a known name
lives in, which a name-existence check does not test.

### Superseded record: the outage batch as it stood before those fixes

* `GroupApproximation/CharClass/OddPSourceFunctor.lean` — `oddSrcComplex`,
  `oddSrcComplex_d`, `lmapDomain_oddDiffW`, `lmapDomain_oddDiffS`,
  `lmapDomain_oddDiffGen`, `oddSrcMap`, `oddSrc`, `oddSrc_map_single`.
* `GroupApproximation/CharClass/OddPSourceFree.lean` — `oddSrcFree`, the
  `FreeOnModels` instance.
* `GroupApproximation/CharClass/OddPNorm.lean` — `geom_sum_eq_sub_one_pow`,
  `grNorm_eq`, `grNorm_eq_grS_mul`, replacing the wrong justification `sp-design`
  caught (see §2.1).
* `GroupApproximation/CharClass/OddPSingular.lean` — `singFreeSimplicialR`,
  `singFreeR`, `singFaceR`, `singFreeR_d`, `singFreeR_d_single`,
  `singFreeR_map_apply`, `singFreeR_d_natural`, `bdRHom`, `bdRHom_bdRHom`,
  `bdRHom_natural`, and **`oddSingularBoundary p : OddPBoundaryData p`**.

The last one closes a gap that would otherwise have been a gate certifying
nothing: until it exists, `oddSrc p data` is a functor for every `data` and there
is no `data`, so nothing has been built.  With it,
`oddSrc p (oddSingularBoundary p)` is a concrete functor.

**It is cheaper at odd `p` than at `p = 2`, and that is not a slogan.**  The
whole assembly `toSSet ⋙ free R ⋙ alternatingFaceMapComplex` is generic in `R`,
`ModuleCat.free R` gives `Finsupp` carriers on the nose, and `∂∂ = 0` and
naturality are `HomologicalComplex.d_comp_d` and `Hom.comm`.  The mod-2 files
spend four lemmas (`ModuleCatZMod2.hom_add_self`, `neg_eq_self`,
`neg_one_pow_zsmul`, `singFree_d`) **discarding the alternating signs**, which is
the only place their characteristic is used; this lane deletes those four rather
than replacing them, and the signed formula it needs,
`alternatingFaceMapComplex_obj_d`, is the very statement `singFree_d` rewrites
away from one line before it drops the signs.

That also settles the shape of the §1.2a repair in the one place this lane needs
it.  The unsigned `bdU` of `CartanTargetBoundary.lean` is generic in the ring but
its `bdU_bdU` requires `[Algebra (ZMod 2) Λ]`, and necessarily: `∂ ∘ ∂ = 0` is
false for the unsigned face sum outside characteristic two.  Nothing downstream
of `bdU` is carried here.

Both are `CartanSourceFunctor.lean` with the coefficient ring changed and no new
mathematics.  The reason there is none: the two things that distinguish odd `p`
— the alternating resolution coefficient and the Koszul sign — are **scalars**,
and `Finsupp.lmapDomain` is linear, so both cross the pushforward by `map_smul`
and neither appears in a naturality argument at all.

`srcMapIdx` is reused from `CartanSourceFunctor.lean`, like `WSIndex` and
`stdSimplexTop`: it does not mention the coefficient ring, and a second
declaration would be a root-only failure no probe can see.

### A correction to §2.3 of this plan, found by reading the landed code

§2.3 repeated cc-cartan's report that the `FreeOnModels` basis needs a `ULift`
reindex "spent in the `basis`/`basis_apply` fields and nowhere else".  Their
landed `srcFree` needs no reindex: the degree-`k` carrier is indexed by the
**bare hom-set** `Σ n : Fin (k+1), (stdSimplexTop n.val ⟶ X)`, which is what
`FreeOnModels` wants on the nose, so the basis is `Finsupp.basisSingleOne` and
`basis_apply` is `Category.id_comp`.  The remark was true of an earlier design
and outlived it.

This is the second time today that a *report* about the tree was wrong where the
*code* was right — the first was my own §1.2 row about `CartanSimplexExact`.
Both were caught by reading the declaration rather than the sentence describing
it.  cc-thom's "docstring rot" trap says to prefer stating a negative about your
own file over a claim about someone else's state; the corollary this lane adds is
that a *plan* inherits every such claim it copies, so a plan's inventory rows
must be re-read against the code before they are acted on, not merely before they
are written.

## 11. `sp-design`'s review (2026-09-10) — sign-off, and what it changed

Verdict: §2, §3 and §6 mathematically sound, signed off.  Checked and correct
with no action: §2.3's `(-1)^i` versus `(-1)^{i-1}` cancellation; §2.1's "`N e_i`
is a boundary in every degree"; §3.3's `tupT^r = 1` and its parity argument;
§3.3's cross-slot sign in `tupD_tupD`; §6.1's four sign claims including the
riffle sign; §6.3's degree-zero agreement.

**The κ question is settled, and the argument is better than the sweep.**  Their
Step D lemma list uses exactly four things about `P`: that the total `P` is a
ring homomorphism, that `P(h) = h + κh^p` on degree-2 generators, that
`P(z) = z`, and instability.  It never uses the `p`-th power property and never
uses the value of any constant.  With `κ ≠ 1`: L1 is untouched; L2 becomes
`∏(1 + h^p + κh^{p²})^{d/p}` using `κ^p = κ`, so the Frobenius support mod `p`
is unchanged and L3a/L3b survive; L4a's coefficient becomes
`κ^i(-1)^{i(p-1)}C(b-1,i)`, so the diagonal leading coefficient at `(b,i)=(i+1,i)`
is `κ^i`, a unit; L5's triangularity therefore holds with a unit leading
coefficient instead of `1`; L6 and L7 are unchanged.  **So the forcing conclusion
is identical for every `κ ≠ 0`, and only `c_2 ≠ 0` matters, never its value.**
That closes §4 Route 1 as the lane's route and retires Route 2 unless `c_2 ≠ 0`
fails.

**Three corrections adopted.**

1. §3.3's "`p` odd enters in exactly two places" is really **one fact used three
   times**, `(-1)^{a(p-1)} = 1`: `tupEval`'s `T`-invariance, and again in §6.1
   for the alternating functional under the block shift at `r = 2p` with block
   degree `a + b`.  It becomes one named lemma rather than three appeals.
2. §6.2's justification was wrong in a harmless direction: the comparison
   theorem needs `W` **projective** (it is free) and `W ⊗ W` acyclic in positive
   degrees.  Freeness of `W ⊗ W` is not needed and is struck from the argument.
3. §3.4(A)'s real difficulty is not the `Finset.filter` prefix sum: it is that
   the prefix sign is computed on **input** degrees while the prefixed slots'
   outputs have degree `0` after `ηε`.  Settle that convention before writing
   the telescoping contraction, not during.

## 11b. The `Δ¹` descent at lemma precision, and the one thing that is not settled

Next in the lead's order.  Writing it out before authoring, per §3 of the program
note, because reading the numerics carefully turned up a model question that
decides the shape.

### The chain, in Lean statements

```lean
-- (1) the contraction of the relative cochains on the 1-simplex
h        : Ccoch (Δ¹, {0}) n+1 →ₗ Ccoch (Δ¹, {0}) n
h_delta  : δ (h u) + h (δ u) = u
-- (2) its one-slot extension to the p-fold tensor power
H_D      : D (H y) + H (D y) = y
-- (3) each level's input is a D-cocycle
A_cocycle : D (A k) = 0                        -- because N·(T-1) = 0 in Λ
-- (4) the descent, and the endpoint
Y k      : Y k = H (A k),      A (k+1) = op k (Y k)
lambda_1 : ⟨ A_final , AW(ι₁) ⟩ = ((p-1)/2)!
```

`(3)` is `grNorm_mul_grS`, already green.  `(2)` is a one-slot sign computation.
`(1)` and `(4)` are the work.

### The unsettled point, and why I am not authoring past it yet

`sp-design`'s contraction is written `h(τ*) = (τ∖{0})*`, which is **simplicial**
notation: it removes a vertex from a face.  That makes sense on the finitely many
faces of the simplicial `Δ^n` and does not typecheck on singular cochains, where
a cochain is a function on *all* maps `Δ^n → Δ¹`.  This lane's whole tower is
singular (`singularSimplices`, `singFreeR`, the `TupIdx` carrier).  Three
readings, and they cost very different amounts:

* **(a) the singular cone operator.**  `Δ¹` is convex, so the straight-line cone
  from vertex `0` contracts its singular chains, and `h` is its dual.  Explicit,
  elementary, and **not in Mathlib** — I checked the pin, there is no cone or
  star operator in `Mathlib/AlgebraicTopology/`, only homotopy invariance.  It is
  also the object cc-cartan's report boasts of never having had to build.  New
  work, bounded, maybe 250 lines.
* **(b) an abstract contraction.**  `AcyclicModelsSplitting.splitHomotopy` gives
  one over a field from `ker ≤ range`, already green and generic.  Free — but it
  computes nothing, so it can only work if the descent's *value* does not depend
  on the choice.  `sp-design` reports exactly that, tested exhaustively over
  single-word perturbations at every level.  If that is a theorem rather than an
  observation, this route needs no cone operator at all and the endpoint is
  reached by proving invariance and then evaluating one explicit choice.
* **(c) transfer from a simplicial model.**  Correct, and it needs the
  equivariant diagonals compared across the two models, which is another acyclic
  models argument.  Most expensive; mentioned only to be ruled out.

**Question sent to `sp-design`**: which complex is their `h` on, and is the
independence of the value from the primitive a theorem they can state, or an
observed invariance over the perturbations they happened to test.  The first
answer selects (b) and makes this cheap; the second forces (a).

Not authoring past this point until it comes back.  The rest of §7 step 2 — the
tuple differential's `d ∘ d = 0`, the cyclic action, acyclicity — is unaffected
and is where I go meanwhile.

## 11a. Sign conventions — the inter-lane contract (2026-09-10)

`sp-coeff` needs the signed two-fold cup-`i` coboundary formula and asked to
match this lane rather than choose independently.  Three conventions are fixed
here, all standard Koszul with no twists, and the third is the one that usually
goes unwritten.

1. **Tensor differential.**  `d(x ⊗ y) = dx ⊗ y + (-1)^{|x|} x ⊗ dy`.  This is
   what `tupD` specialises to at `r = 2`, the prefix sign being the total degree
   of the slots strictly before the differentiated one.
2. **Transposition.**  `T(x ⊗ y) = (-1)^{|x||y|} y ⊗ x`, which is what `tupT`
   specialises to at `r = 2`.
3. **Evaluation carries no sign.**  `⟨u_1 ⊗ ⋯ ⊗ u_r, t⟩ = ∏_j u_j(t_j)`, slot by
   slot.  `tupEval` is defined this way and nothing in the lane compensates for
   it elsewhere.

**The two-fold formula is not a by-product of this lane and `sp-coeff` owns it.**
Their framing, and the lead's, was that their `r = 2` case is what the tuple
model does `p`-fold.  It is not: `cochainCupI` is the pairing against the
**explicit cut** diagonal, and this lane's diagonal is abstract, from acyclic
models, with the explicit interval-cut construction deliberately retired.
Extracting `cochainCupI` here would first require proving the abstract diagonal
equals the explicit one, which is the work the lane exists to avoid.  Told them
to schedule it.

**The calibration warning given with it**, because it is this lane's own rule
turned outward: the cut-index-zero case of their formula collapses to the signed
Leibniz rule they have already landed, so it will pass and it pins only two of
the four terms.  The two terms that *lower* the cut index are exactly the ones it
cannot see, and are where an overall reindexing hides.  They need both degrees
`1` and cut index `1` on a `3`-simplex, where all four terms are present and
distinguishable.

## 12. The descent numerics (2026-09-10, `sp-design`), and where `c_2` now stands

**The constant at degree one is `((p-1)/2)!`**, computed at `p = 3, 5, 7, 11, 13`
as `1, 2, -1, -1, 5`, which is `1, 2, 6, 120, 720` reduced.  That is the
classical `m!` with `m = (p-1)/2`, **derived rather than cited**, which is what
the program note demanded.  Nonvanishing is then free: `m!` is a product of
integers below `p`.  Well-definedness was tested exhaustively against every
single-word perturbation of every primitive at `p = 3, 5` and the value never
moved.

**The growth risk I flagged is gone, and by a better route than a closed form.**
Work in the cochains on `Δ^n` vanishing on vertex `0`; the cone on that vertex is
an explicit contraction, and applied to slot `0` only it contracts the `p`-fold
tensor power on the nose, because the two mixed Koszul terms cancel.  So every
primitive in the descent is that operator applied to the previous term, with no
linear solve at any level, and the whole descent is an explicit composite of two
one-line operators.  **This retires §4 Route 2 for good**: the Lean cost is three
lemmas — the cone contraction, its one-slot tensor version, and `N(T-1) = 0` —
plus one evaluation.

**The `Δ²` route for `c_2` is dead, and the reason is instructive.**  Every
primitive exists and the descent runs, but the answer is not well defined: over
exhaustive perturbations it takes *every* value in `F_p`.  The cause is the
failure at `q = 2` of the very point-term lemma I verified at `q = 1`.  Changing
the primitive changes the answer by a pairing against the boundary of the
simplex; on `Δ¹` that boundary is a sum of **points**, where every word carries a
factor that is the zero cochain, and on `Δ²` it is a sum of **edges**, where
nothing kills it.  Only `q = 1` has a boundary of points, so no `Δ^q` descent can
be made well defined for `q ≥ 2`.

**The clean statement of the same fact, which arrived later and is worth having
instead:** the constant is well defined on a **cycle**, because the `∂c` term of
the homotopy dies there and the `T`-invariance of `w^{⊗p}` kills the `d_W` term.
A simplex is not a cycle, which is why `Δ²` fails; the torus's fundamental class
is one, which is why the direct computation of `c_2` on the torus works.  That
formulation says what to look for next time — find a cycle — where the
points-versus-edges version only says which case happened to work.

### The bridge from `c_1` to `c_2`, and the gap in it

`sp-design` recommends `c_2 = c_1²` from multiplicativity, on the grounds that
the comparison's degree-zero agreement normalises the Cartan coefficient to `1`.
**I do not think it does, and I have said so to them and to the lead.**  Writing
`C_{a,b}` for the coproduct's coefficients summed over the twist (the twist being
invisible to the functional, by the invariance lemma of §3.3), the comparison
gives

```text
D_i(u ⌣ v) ≡ Σ_{a+b=i} C_{a,b} · (D_a(u) ⌣ D_b(v))     (mod coboundary)
```

with coefficient `1` on the left.  The degree-zero agreement is the **counit**
condition, which pins `C_{0,0} = 1` and nothing else; that is the `i = 0` case of
the formula, which says `(uv)^p = u^p v^p` — true and empty.  The identity
`c_2 = C_{p-1,p-1} · c_1²` needs the coefficient at `(p-1, p-1)`, which the
counit condition does not reach.

Two observations make this small rather than alarming.

* We need `C_{p-1,p-1} ≠ 0`, **not** `= 1`: the normalisation absorbs any unit,
  and the consistency condition `c_{q+q'} = κ c_q c_{q'}` is automatic.
* `C_{p-1,p-1}` is a purely arithmetic quantity in the group ring, computable by
  the machinery `sp-design` has already built and far smaller than the descent.
  Requested.

**A second prerequisite nobody had named**: the bridge needs two degree-1 classes
with nonzero product, and at an odd prime a degree-1 class squares to zero, so
they must be distinct.  That means a space like `S¹ × S¹`, reached through the
Künneth layer rather than through sphere cohomology alone.

### The lead's ruling (2026-09-10), and the one claim held open

Ruled: `c_1 ≠ 0` by the `Δ¹` descent generic in `p`; `c_2 = c_1²` by Cartan; no
`Δ²` descent; §2.1's telescoping proof replaced; `sp-design`'s review is a
sign-off; proceed with §7 steps 0–5, then the descent lemmas, then Cartan.  All
adopted.  §2.1 is already replaced, by the polynomial-ring route rather than the
binomial one.

The ruling's justification for `c_2 = c_1²` was the one questioned above, and our
messages crossed.  **RESOLVED the same day**: the lead held the ruling, `sp-design`
withdrew the overstated sentence by name, and the coefficient was *computed*
rather than asserted — `C = 1` at `p = 3, 5, 7, 11, 13`, with the mechanism given
in §6.2 and both of its arithmetic claims re-checked here independently.  So the
bridge closes as the lead ruled, but on a computation rather than on the
justification originally offered.  Nothing was built on it in the interval.

### What this lane can prove unconditionally, which narrows it to one number

**The Cartan coefficient is `1` whenever both degrees are even**, with no
reference to the coproduct.  Evaluate the formula at the top index; instability
kills every term except the one where each factor takes its own top operation;
the top operation is the `p`-th power; so `κ · (uv)^p = (uv)^p`, and a projective
space of large enough dimension supplies a product whose `p`-th power does not
vanish.  Hence `c_{q+q'} = c_q c_{q'}` for even degrees, every even constant is a
power of `c_2`, and the whole programme rests on `c_2 ≠ 0` alone.

## The outage of 2026-09-10

Every lane died at 15:55 UTC on the Mac's network, not on any lane's work.  The
lead reports nothing lost.  For this lane the state at the cut was:

* the seven §2 modules green, with `Built` lines cited for four of them;
* an artifact-deleting rebuild of all seven in flight, started so that one log
  would carry seven `Built` lines, which may have died on the node.

At the time that meant the clone might be missing this lane's oleans, since the
deletion certainly ran and the rebuild may not have.  **All of it is moot now**:
the wrapper returned, the clone was de-hardlinked, and the thirteen-module
from-scratch build above supersedes every artifact question raised here.  Kept
only as the record of what an outage costs a lane, which was: nothing in the
sources, and one probe cycle.

### The spelling trap, three times in one lane

Every red round in §2 after the first was one shape: **a number that is
definitionally but not syntactically what a lemma's statement spells, sitting
inside the type of a `Finsupp`.**  `rw` matches at `instances` transparency, so
it neither fires nor can be made to fire by a `show`; the goal displays the
pattern and the rewrite reports "Did not find an occurrence", followed by a note
that the target is not type-correct at that transparency.

| where | goal spells | lemma spells |
|---|---|---|
| `linearCombination_oddDiffS_bd` | `↑i.succ` | `i.val + 1` |
| `oddDiff_oddDiff`, interior branch | `↑i.castSucc` | `i.val` |

The cure both times is a `have` whose **stated** type carries the goal's
spelling and whose **proof** is the lemma, because `have` checks at default
transparency where the two are equal.  Where the two sides of the junction want
different spellings — the goal's on the left, the next rewrite's on the right —
state the `have` with one on each side; that is what `hmix` does.
`CartanSourceComplex.lean` does exactly this and it reads as a stylistic
preference.  It is not one, and this lane paid two probe rounds to learn it.

## NEEDS

* **`sp-design`:** the descent numerics of §10 — the sign vector of `N^*` on the
  bidegree `(0,1,…,1)`, and the coefficient vector at *every* level of the
  descent for `p = 3, 5, 7, 11, 13`, not only the first.  Whether a closed form
  in `p` exists decides whether `c_2 ≠ 0` can be proved in general or only prime
  by prime.  No Lean on the constant until those numbers are in this report, per
  the lead's ruling.
* **`sp-design`, review of §3 and §6** (the flat arity-generic tuple model and
  the sign conventions).  §2 is authored on the lead's authorisation, being pure
  algebra with no design risk; §3 waits on the sign-convention answer.
* ~~**`sp-coeff`:** the signed Leibniz rule and the generic cohomology
  vocabulary.~~  **DELIVERED 2026-09-10**, all probe-green on `cs-endpoint`:
  `CoeffLeibniz.lean` (2031 jobs) with `aw_cochain_leibniz` over `[CommRing R]`
  and the three sign-free consequences `cochainCup_respects_cocycles`,
  `cochainCup_coboundary_left'`, `cochainCup_coboundary_right'`;
  `CoeffCohomology.lean` (2055 jobs); `CohomologyBasic.lean` and
  `CohomologyAssoc.lean` (2057 jobs) with `Hmod K`, `cup`, `pull`, `cohCast`,
  `one` generic and `K` **implicit**.  `[CommRing K]` throughout, so `ZMod p`
  with `[Fact p.Prime]` needs no extra hypothesis at this layer.  This lane has
  nothing further to ask of them.

  Two rules adopted from their delivery.  **Never carry the Leibniz sign into a
  cohomology-level statement**: differentiating `(-1)^p • (φ ⌣ η)` instead of
  `φ ⌣ η` squares the two signs to one, which is how the mod-2 shape survives
  over any ring.  And **name the coefficient ring wherever a partial application
  leaves it undetermined** — `pull (K := ZMod 2) f n`, not `pull f n` — because
  `K` implicit has no argument to be inferred from; 36 sites needed it in their
  scope and the tuple model of §3, where the ring and the arity are both section
  variables, will have the same shape.

### A rule from the lead, adopted (2026-09-10)

The lane clones were warmed by hard-linking the main tree's oleans, so a stale
artifact can be replayed.  **A module is green only when its own line in the
probe log reads `✔ [k/N] Built …`; a `Replayed` line on a module that was edited
is a false green and the probe is FAILED**, as is an unmoved job count across a
structural change.  The remedy is to delete that module's remote `.olean`,
`.ilean` and `.trace` in `cs-limit` and re-probe.  This lane's modules cannot in
fact be replayed from the warm tree — none of them exists there — but the log
line is cited from now on rather than inferred.

## TRAPS

New, this lane's own.  All of the confirmed ones are now appended to
`FLEET_TRAPS.md`; the ones below that a probe has not yet exercised are marked as
such.

* **The mod-2 tree's `FreeCx` layer is a trap for a reader, not an asset.**
  `CartanFreeCx.tensorD_tensorD` reads like a general tensor-of-complexes lemma;
  its proof is "the two mixed terms are equal and cancel because two is zero".
  Anyone porting it to odd `p` by substituting the coefficient ring gets a false
  theorem with a proof that still compiles for a while.
* **`CartanSingular.lean`'s sign-dropping lemmas are load-bearing for `Cartan*`
  and must not be touched.**  This lane wants the signed complex, which is the
  same `singFree` *before* `singFree_d_single` is applied.  Do not "fix"
  the mod-2 file.
* `p` odd is used in exactly two places (§3.3).  If a proof anywhere else seems
  to need it, the sign convention is wrong.
* The Koszul sign of the cyclic shift on an `r`-tuple is `+1` after `r`
  applications **for every `r`**, by `x² ≡ x (mod 2)` — not only for `r` prime.
  A proof that case-splits on `r` is doing unnecessary work.
