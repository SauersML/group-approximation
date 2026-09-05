# cc-steenrod

Cup-`i` products, the chain-level coboundary formula, and `Sq` on
`cohomologyZMod2`.  Namespace `GroupApproximation.CharClass`, files
`GroupApproximation/CharClass/Steenrod*.lean`.

## Design (settled 2026-09-05, before authoring)

### Degrees without casts, and without a dependent index set

The two ideas that make this cheap:

1. **Faces are evaluated through a total function.**  `faceVal a α σ A` takes an
   arbitrary vertex subset `A : Finset (Fin (n+1))` of an `n`-simplex `σ` and
   returns `α (σ ∘ faceOfFinset A)` when `A.card = a+1` and `0` otherwise.  So
   every sum below runs over *all* `(i+1)`-subsets, with no `filter`, no
   `Finset.attach`, and no proof-carrying face map.
2. **The output degree is a free parameter.**  

   ```lean
   cochainCupI (i a b n : ℕ) (α : C^a) (β : C^b) : C^n
   (cochainCupI i a b n α β) σ = ∑ S ∈ cutIndex i n, faceVal a α σ (cutU S) * faceVal b β σ (cutV S)
   ```

   Since `|cutU S| + |cutV S| = (n+1) + (i+1)` always, the two cardinality
   tests can only both succeed when `a + b = n + i`; in every other degree
   *every* term is `0` and `cochainCupI` is the zero cochain.  So the
   definition needs no hypothesis, and the coboundary formula is stated at
   literal degrees `n` and `n+1` with **no `cochainCast` anywhere**.

`i = 0`, `a = p`, `b = q`, `n = p+q` is the Alexander–Whitney cup product
(`cochainCupI_zero`, proved: `cuts` for `i = 0` is the singleton `{p}` and the
two faces are `frontFace p q`, `backFace p q`).  So `⌣₀` is on the nose the
vendored `cochainCup`, with the vendored convention.

### The coboundary formula (deliverable 2)

```lean
theorem cochainCupI_coboundary (i a b n : ℕ) (h : a + b = n + (i + 1))
    (α : singularCochainGroup (ZMod 2) X a) (β : singularCochainGroup (ZMod 2) X b) :
    cochainCoboundary (ZMod 2) X n (cochainCupI (i+1) a b n α β)
      = cochainCupI (i+1) (a+1) b (n+1) (cochainCoboundary (ZMod 2) X a α) β
        + cochainCupI (i+1) a (b+1) (n+1) α (cochainCoboundary (ZMod 2) X b β)
        + cochainCupI i a b (n+1) α β
        + cochainCupI i b a (n+1) β α
```

`⌣₋₁ = 0` is not needed: the statement is indexed so that the two low terms
carry `i` and the high ones `i+1`.

### INTERFACE FOR cc-cartan

The chain-level content of the coboundary formula is a **single combinatorial
theorem, valued in an arbitrary 2-torsion abelian group**, so the same lemma
serves the cochain formula and any chain-level packaging of `Φ` you prefer.
It is `GroupApproximation.CharClass.cut_insert_cancel` in
`CharClass/SteenrodCutCancel.lean`:

```lean
/-- `Θ` is an arbitrary "pair of faces ↦ value" function. -/
theorem cut_insert_cancel {M : Type*} [AddCommGroup M] (h2 : ∀ x : M, x + x = 0)
    {N : ℕ} (Θ : Finset (Fin N) → Finset (Fin N) → M) (S : Finset (Fin N)) :
    ∑ c ∈ Sᶜ, (Θ ((cutU (insert c S)).erase c) (cutV (insert c S))
             + Θ (cutU (insert c S)) ((cutV (insert c S)).erase c))
      = Θ (cutU S) (cutV S) + Θ (cutV S) (cutU S)
```

Read it as the equivariance/boundary identity: the left side is what
`∂Φ(e_{i+1} ⊗ σ)` contributes after the vertices of `σ` that are *not* cut
points have been summed away, and the right side is
`Φ(e_i ⊗ σ) + T Φ(e_i ⊗ σ)`.  The proof is a genuine telescoping (see TRAPS),
not an involution.

Supporting combinatorics, all in the same file, also `M`-valued where relevant:

```lean
def cutRank (S : Finset (Fin N)) (x : Fin N) : ℕ            -- #{c ∈ S | c < x}
def cutU (S : Finset (Fin N)) : Finset (Fin N)              -- x ∈ S ∨ cutRank even
def cutV (S : Finset (Fin N)) : Finset (Fin N)              -- x ∈ S ∨ cutRank odd
def cutIndex (i n : ℕ) : Finset (Finset (Fin (n+1)))        -- (i+1)-subsets
theorem cutU_union_cutV : cutU S ∪ cutV S = Finset.univ
theorem cutU_inter_cutV : cutU S ∩ cutV S = S
theorem cutU_card_add_cutV_card : (cutU S).card + (cutV S).card = N + S.card
theorem cutU_map_succAbove (k : Fin (n+2)) (S : Finset (Fin (n+1))) :
    (cutU S).map (Fin.succAboveOrderEmb k).toEmbedding
      = (cutU (S.map (Fin.succAboveOrderEmb k).toEmbedding)).erase k
theorem sum_cutIndex_succ_erase (i N : ℕ) (G : Finset (Fin N) → Fin N → M) :
    ∑ T ∈ powersetCard (i+2) univ, ∑ c ∈ T, G (T.erase c) c
      = ∑ T ∈ powersetCard (i+1) univ, ∑ c ∈ Tᶜ, G T c
```

**Explicit `Φ`.**  The `(a,b)`-component of Steenrod's diagonal on the
generator `e_i ⊗ σ`, for `σ` an `n`-simplex, is

```text
Φ_{i,a,b}(σ) = ∑_{S ∈ cutIndex i n} (σ ∘ faceOfFinset (cutU S)) ⊗ (σ ∘ faceOfFinset (cutV S))
```

with the same "wrong cardinality ⇒ drop the term" convention.  If you want it
as a `Finsupp`-valued map (free `ZMod 2`-module on pairs of singular
simplices) rather than as the cochain operation, say so in
`notes/lix-lane-reports/cc-cartan.md` and I will export

```lean
def steenrodDiag (i a b n : ℕ) (σ : singularSimplices X n) :
    (singularSimplices X a × singularSimplices X b) →₀ ZMod 2
```

together with its boundary identity — it is `cut_insert_cancel` instantiated
at `Θ A B := Finsupp.single (σ|_A, σ|_B) 1`, which is why the core lemma is
stated for an arbitrary `M`.  I did **not** build the categorical
`W ⊗ S_*(X) ⟶ S_*(X) ⊗ S_*(X)` object: it costs a monoidal-category detour
and `cut_insert_cancel` already carries all the mathematics.

### `Sq` (deliverable 3)

```lean
def sqCochain (k i : ℕ) (α : C^(k+i)) : C^(k+i+k) := cochainCupI i k k (k+i+k) α α
def Sq (k : ℕ) {n : ℕ} (x : cohomologyZMod2 X n) : cohomologyZMod2 X (n + k)
```

`Sq k` is defined by `dite (k ≤ n)`: for `k ≤ n` it is the class of
`sqCochain k (n-k)` of a cocycle representative, transported along
`k + (n-k) + k = n + k`; for `k > n` it is `0` (instability, definitional).
`Sq_mk` states the computation rule at `n = k + i`, where no transport occurs.

## GREEN

Nothing yet (first probe pending).

## AUTHORED, UNVERIFIED

* `CharClass/SteenrodCut.lean`
* `CharClass/SteenrodCutCancel.lean`
* `CharClass/SteenrodCochain.lean`
* `CharClass/SteenrodCoboundary.lean`
* `CharClass/SteenrodSquare.lean`

## NEEDS

Nothing from a peer.  Everything is built on the vendored
`AlgebraicTopology/{AlexanderWhitney,CupProduct,AlexanderWhitneyChainMap,
CochainCupLeibniz,CohomologyCupProduct}.lean` plus Mathlib.

If `cc-cohom-api` restates `cohomologyZMod2` cup/pullback in element form
under new names, `Sq` naturality is already available directly from
`cohPullback` and does not need it.

## TRAPS

* The untracked `AlgTop/SteenrodCut.lean` is mathematically sound (its parity
  test `x ∈ S ∨ cutRank S x % 2 = 0` really is Steenrod's alternating-block
  `U`), but its `cuts i p q` filter and the proof-carrying `cutFrontFace` /
  `cutBackFace` are the wrong shape for the coboundary formula: they force a
  dependent index set and degree casts.  The `faceVal`/free-output-degree
  design above removes both.
* The proof of the coboundary formula does **not** work by pairing terms with
  an involution.  Write `A_t := (cutU S ∩ {x < t}) ∪ (cutV S ∩ {x ≥ t})` and
  `B_t` with `U`, `V` swapped (`cutLow`, `cutHigh`).  Then for `c ∉ S` the two
  terms coming from `insert c S` are `Θ(A_c, B_c)` and `Θ(A_{c+1}, B_{c+1})`
  in one order or the other according to whether `c ∈ cutU S`, and for `c ∈ S`
  one has `A_c = A_{c+1}` and `B_c = B_{c+1}`.  So the sum over `Sᶜ` extends
  to a sum over all `c` and telescopes to `Ξ 0 + Ξ N`, which is exactly
  `Θ(cutV S, cutU S) + Θ(cutU S, cutV S)`.
