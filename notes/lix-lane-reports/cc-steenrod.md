# cc-steenrod

Cup-`i` products on the vendored mod-2 cochains, Steenrod's coboundary formula,
graded commutativity of the cup product, and the equivariant diagonal.
Namespace `GroupApproximation.CharClass`, files
`GroupApproximation/CharClass/Steenrod*.lean`.

## EXPORTS

For `cc-projective`, `cc-wu`, `cc-lix-odd` and `cc-cohom-api`, in
`CharClass/SteenrodCupOne.lean`, against `cc-cohom-api`'s `Hmod2`, `cup` and
`cohCast` of `CharClass/CohomologyBasic.lean`:

```lean
theorem cup_comm {X : TopCat.{0}} {p q : ℕ} (a : Hmod2 X p) (b : Hmod2 X q) :
    cup a b = cohCast (Nat.add_comm q p) (cup b a)
```

And in `CharClass/SteenrodSquare.lean`, the Steenrod squares:

In `CharClass/SteenrodTotal.lean`, namespace `CharClass.Steenrod`, the shape
`cc-wu`'s `ParityData` consumes, on `cc-projective`'s `TotalH X = ⨁ n, Hmod2 X n`:

```lean
def SqH (X : TopCat.{0}) (k : ℕ) : TotalH X →+ TotalH X
theorem SqH_of (X) (k n) (a) : SqH X k (TotalH.of X n a) = TotalH.of X (k + n) (Sq k a)
theorem SqH_zero_apply (X) (c) : SqH X 0 c = c
theorem SqH_of_eq_zero_of_lt (X) (k n) (hk : n < k) (a) : SqH X k (TotalH.of X n a) = 0
theorem SqH_map (f : X ⟶ Y) (k) (c) : SqH X k (TotalH.map f c) = TotalH.map f (SqH Y k c)
theorem SqH_of_self (X) (n) (a) :
    SqH X n (TotalH.of X n a) = TotalH.of X n a * TotalH.of X n a
theorem Sq_pull (f : X ⟶ Y) (k n) (a) : Sq k (pull f n a) = pull f (k + n) (Sq k a)
```

`SqH X` **is** `cc-wu`'s `SqH` field; additivity is inherited from the direct
sum, and `SqH_zero_apply` is their field of the same name.

And the graded squares themselves:

```lean
def Sq (k : ℕ) {n : ℕ} (x : Hmod2 X n) : Hmod2 X (k + n)
theorem Sq_mk (k n : ℕ) (φ) (hφ) :
    Sq k (cocycleClass X n φ hφ) = cocycleClass X (k + n) (sqCochain n k φ) _
theorem Sq_add (k n : ℕ) (x y : Hmod2 X n) : Sq k (x + y) = Sq k x + Sq k y
theorem Sq_self (n : ℕ) (x : Hmod2 X n) : Sq n x = cup x x
theorem Sq_zero (n : ℕ) (x : Hmod2 X n) : Sq 0 x = cohCast (Nat.zero_add n).symm x
theorem Sq_eq_zero_of_lt (k n : ℕ) (hk : n < k) (x : Hmod2 X n) : Sq k x = 0
```

`Sq k` lands in degree `k + n`, not `n + k`, deliberately: the cokernel
condition needs the predecessor of the output degree, and `k + (j+1)` reduces to
`(k+j)+1` definitionally while `(j+1)+k` does not reduce for a variable `k`.
`cohCast` converts in one step.  Instability is free from
`cochainCupI_of_degree_ne`, so there is no `dite` in the definition of `Sq`.

**All degrees, no evenness hypothesis.**  Mod 2 the proof never inspects
parity: for cocycles `φ, ψ` the identity `φ ⌣ ψ + ψ ⌣ φ = δ(φ ⌣₁ ψ)` is
`cochainCupI_coboundary` at `i = 0` with the two Leibniz terms killed, and the
only case split is `p + q = 0` against `p + q = n + 1`, which is about having
somewhere to put the cup-1 primitive.

For `cc-cartan`, in `CharClass/SteenrodDiagonal.lean`:

```lean
def steenrodDiag (i a b : ℕ) {n : ℕ} (σ : singularSimplices X n) : tensorTwo X a b
theorem steenrodDiag_naturality (f : X ⟶ Y) (i a b : ℕ) {n : ℕ} (σ) :
    Finsupp.mapDomain (Prod.map (pushSimplex f a) (pushSimplex f b)) (steenrodDiag i a b σ)
      = steenrodDiag i a b (pushSimplex f n σ)
theorem steenrodDiag_boundary (i a b n : ℕ) (σ : singularSimplices X (n + 1)) : …
```

`tensorTwo X a b` is `(singularSimplices X a × singularSimplices X b) →₀ ZMod 2`,
the bidegree-`(a,b)` part of `S_*(X) ⊗ S_*(X)` as a free module rather than
through the monoidal structure; `T` is `tensorSwap = Finsupp.mapDomain Prod.swap`.
The `(13)(24)` action convention concerns `S(X)^{⊗4}` and does not touch this
interface: `Φ`'s own identity is the two-factor one, and `cut_insert_cancel`
delivers it as the two orders of the same cut, which is what `T` exchanges.

And, for the acyclic-models comparison itself, in namespace
`CharClass.Steenrod`, the target complex, the diagonal and the chain-map
condition:

```lean
abbrev PairIdx (X : TopCat.{0}) (k : ℕ) : Type          -- both degrees, sum as a Prop
def swapEnd (X) (k) : Module.End (ZMod 2) (PairIdx X k →₀ ZMod 2)
instance tgtModule (X) (k) : Module GroupRingZ2 (PairIdx X k →₀ ZMod 2)
def dTgt (X) (Λ) [CommRing Λ] (k) :
    (PairIdx X (k+1) →₀ Λ) →ₗ[Λ] (PairIdx X k →₀ Λ)
def dTgtLin (X) (k) :
    (PairIdx X (k+1) →₀ ZMod 2) →ₗ[GroupRingZ2] (PairIdx X k →₀ ZMod 2)
def PhiHom (X) (k) : WTensorSMod X k →ₗ[GroupRingZ2] (PairIdx X k →₀ ZMod 2)

theorem swapEnd_dTgt (X) (k) (y) :
    swapEnd X k (dTgt X (ZMod 2) k y) = dTgt X (ZMod 2) k (swapEnd X (k+1) y)
theorem dTgt_smul (X) (k) (c : GroupRingZ2) (y) :
    dTgt X (ZMod 2) k (c • y) = c • dTgt X (ZMod 2) k y
theorem dTgt_PhiHom (X) (k) (y : WTensorSMod X (k+1)) :
    dTgt X (ZMod 2) k (PhiHom X (k+1) y) = PhiHom X k (wDiff singularBoundary X k y)
theorem dTgtLin_comp_PhiHom (X) (k) :
    (dTgtLin X k).comp (PhiHom X (k+1)) = (PhiHom X k).comp (wDiff singularBoundary X k)

def pairIdxPush (f : X ⟶ Y) (k) : PairIdx X k → PairIdx Y k
def pairPushGRLin (X Y) (f) (k) :
    (PairIdx X k →₀ ZMod 2) →ₗ[GroupRingZ2] (PairIdx Y k →₀ ZMod 2)
theorem dTgt_naturality (f : X ⟶ Y) (k) (y) :
    pairPushLin X Y f k (dTgt X (ZMod 2) k y) = dTgt Y (ZMod 2) k (pairPushLin X Y f (k+1) y)
theorem PhiHom_naturality (f : X ⟶ Y) (k) (y : WTensorSMod X k) :
    pairPushLin X Y f k (PhiHom X k y)
      = PhiHom Y k (Finsupp.lmapDomain GroupRingZ2 GroupRingZ2 (srcMapIdx f k) y)
theorem smul_of_swap (F : (PairIdx X j →₀ ZMod 2) →ₗ[ZMod 2] (PairIdx Y k →₀ ZMod 2))
    (hF : ∀ z, F (swapEnd X j z) = swapEnd Y k (F z)) (c : GroupRingZ2) (z) :
    F (c • z) = c • F z
```

So `Φ` is a **natural equivariant chain map**: natural by `PhiHom_naturality`
against `cc-cartan`'s own `srcMapIdx`, equivariant because it is `Λ`-linear by
construction (the source is free over `Λ`, so the extension from the basis is the
whole of `Λ`-linearity), and a chain map by `dTgt_PhiHom`.  `smul_of_swap` is the
reusable criterion: an `F₂`-linear map between two target modules commuting with
their swaps is `Λ`-linear.

`dTgt_PhiHom` is **the chain-map condition**.  The source is
`cc-cartan`'s `WTensorSMod`/`wDiff` on the nose; the single `Equiv.ulift` between
`singularSimplices X n` and `stdSimplexTop n ⟶ X` is spent in
`SteenrodChainMapHom.lean` and nowhere else.

The target is the free `F₂`-module on pairs with `Λ` acting **through the
geometric swap**, not the free `Λ`-module on pairs.  On the free `Λ`-module the
chain-map condition is *false*: the source differential's first half is
`(1 + t) •`, so the condition demands `t • y = T y` with `T` the index swap, and
in the free module the generator moves coefficients instead of data.  The
published `Phi` of `SteenrodDiagonalLambda.lean` lands in the free module and is
kept only because its signature was consumed; `PhiSwap` and `PhiHom` are the
corrected maps.

## Design

`cutIndex m n` is the set of `m`-element cut sets among the `n+1` vertices, and
`cochainCupI i` sums over `cutIndex (i+1) n`.  Indexing by the **size** rather
than by `i` is what makes `cutIndex 0` expressible, which is what lets the
Leibniz case `i = 0` come out of the same `cut_coboundary_master` as the general
formula instead of needing a separate argument.

Two decisions remove every degree cast from the coboundary formula:

* `faceVal a α σ A` is **total**: it returns `0` when `A` does not have `a + 1`
  vertices.  So no sum carries a cardinality hypothesis and no face map appears
  with a proof argument that would block `rw`.
* the **output degree of `cochainCupI i a b n` is a free parameter**.  Since
  `|cutU S| + |cutV S| = (n+1) + (i+1)`, the two cardinality tests can both
  succeed only when `a + b = n + i`; in every other degree the cochain is `0`
  (`cochainCupI_of_degree_ne`).

```lean
theorem cochainCupI_coboundary (i a b n : ℕ) (α β) :
    cochainCoboundary (ZMod 2) X n (cochainCupI (i + 1) a b n α β)
      = cochainCupI (i + 1) (a + 1) b (n + 1) (cochainCoboundary (ZMod 2) X a α) β
        + cochainCupI (i + 1) a (b + 1) (n + 1) α (cochainCoboundary (ZMod 2) X b β)
        + cochainCupI i a b (n + 1) α β
        + cochainCupI i b a (n + 1) β α
theorem cochainCupI_coboundary_zero (a b n : ℕ) (α β) :   -- the Leibniz end
    cochainCoboundary (ZMod 2) X n (cochainCupI 0 a b n α β)
      = cochainCupI 0 (a + 1) b (n + 1) (cochainCoboundary (ZMod 2) X a α) β
        + cochainCupI 0 a (b + 1) (n + 1) α (cochainCoboundary (ZMod 2) X b β)
```

`cochainCupI_zero : cochainCupI 0 p q (p+q) φ ψ = cochainCup p q φ ψ` is an
equality on the nose with the vendored Alexander–Whitney cup, not up to a
convention: a `1`-cut is a single vertex `c`, its left family is `Iic c` and its
right family `Ici c`, only `c = p` has the right size, and the two faces are
`frontFace p q` and `backFace p q`.  `cochainCupI_self : cochainCupI m m m m α α
= α` is `Sq^0 = id` at the cochain level.

The mathematical content is one lemma, valued in an arbitrary abelian group of
exponent two, so that the cochain formula and the chain-level diagonal are two
readings of one proof:

```lean
theorem cut_insert_cancel {M} [AddCommGroup M] (h2 : ∀ x : M, x + x = 0)
    (Θ : Finset (Fin N) → Finset (Fin N) → M) (S : Finset (Fin N)) :
    ∑ c ∈ Sᶜ, (Θ ((cutU (insert c S)).erase c) (cutV (insert c S))
             + Θ (cutU (insert c S)) ((cutV (insert c S)).erase c))
      = Θ (cutU S) (cutV S) + Θ (cutV S) (cutU S)
theorem cut_coboundary_master {M} [AddCommGroup M] (h2 : ∀ x : M, x + x = 0)
    (m : ℕ) (Θ : Finset (Fin (n+2)) → Finset (Fin (n+2)) → M) : …
```

## GREEN

**All nineteen owned modules build clean together:
`Build completed successfully (2192 jobs)`, `LAKE_EXIT=0`, `PROBE GREEN`**, log
verified to name all nineteen targets and `clone cc-steenrod`.  Per-module job
counts below are from the probe that first compiled each:

* `CharClass/SteenrodCut.lean`
* `CharClass/SteenrodCutCancel.lean`
* `CharClass/SteenrodCochain.lean`
* `CharClass/SteenrodCupEdge.lean`
* `CharClass/SteenrodCoboundary.lean`
* `CharClass/SteenrodCupOne.lean` — contains `cup_comm`
* `CharClass/SteenrodDiagonal.lean` — `steenrodDiag`, naturality, boundary
* `CharClass/SteenrodSquare.lean` — the Steenrod squares
* `CharClass/SteenrodTotal.lean` — the total operation on `⨁ n, H^n`, 2135 jobs
* `CharClass/SteenrodDiagonalLambda.lean` — the group-ring packaging of the
  diagonal, 2037 jobs
* `CharClass/SteenrodCartanTotal.lean` — the Cartan transport, 2136 jobs
* `CharClass/SteenrodDiagonalTarget.lean` — the pair carrier and its
  differential, 2082 jobs
* `CharClass/SteenrodDiagonalPhi.lean` — `swapEnd`, `tgtModule`, `PhiSwap`,
  2082 jobs
* `CharClass/SteenrodPairBoundary.lean` — `tenBdL`/`tenBdR` and the boundary
  identity in operator form, 2036 jobs
* `CharClass/SteenrodPairCell.lean` — `cellPair`, `dTgtL`/`dTgtR`, the
  equivariance step, 2084 jobs
* `CharClass/SteenrodChainMap.lean` — **the chain-map condition on a
  generator**, 2085 jobs
* `CharClass/SteenrodTargetLinear.lean` — the target differential is equivariant
  and group-ring linear, 2085 jobs
* `CharClass/SteenrodChainMapHom.lean` — the chain-map condition against
  `wDiff`, 2089 jobs
* `CharClass/SteenrodChainMapNat.lean` — naturality of `Φ` and of the target
  differential, 2092 jobs
* `CharClass/SteenrodComparisonMap.lean` — **`Φ : src ⟶ tgt`**, the natural
  transformation the comparison consumes, 2870 jobs
* `CharClass/SteenrodFourfoldAW.lean` — `Φ₀`, the Alexander–Whitney diagonal,
  2093 jobs
* `CharClass/SteenrodFourfoldA.lean` — composite `A`, all four properties,
  2874 jobs
* `CharClass/SteenrodFourfoldB.lean` — composite `B`, defined; `Λ`-linearity and
  the degree-zero value, 2875 jobs
* `CharClass/SteenrodFourfoldBoundary.lean` — the boundary identity at a free
  index, and the Leibniz rule for the fourfold, 2876 jobs
* `CharClass/SteenrodFourfoldBridge.lean` — the Leibniz rule in consumable form,
  2877 jobs
* `CharClass/SteenrodFourfoldAgree.lean` — the two composites agree in degree
  zero, `cc-cartan`'s `hzero`, 2876 jobs
* `CharClass/SteenrodPairing.lean` — pairing the diagonal against two cochains
  is the cup-`i` product, 2037 jobs
* `CharClass/SteenrodFourfoldBChain.lean` — the chain map's first two layers,
  2878 jobs
* `CharClass/SteenrodFourfoldBNat.lean` — naturality up to the interchange,
  2880 jobs

## A correction, and what it cost

`compBTerm` was wrong for its first four green probes.  It grouped the four slots
of the fourfold as the two factors of `Φ(e_p ⊗ σ')` against the two of
`t^p Φ(e_q ⊗ σ'')` — the second composite **without** the middle transposition —
so it intertwined the generator with the permutation that swaps *inside* each
block rather than with the block swap the fourfold carries.  Corrected in
`ca1cebf87` by applying `cc-cartan`'s `midSwap`; the un-transposed value is kept
as `compBPre`, since the Leibniz rule is stated on it and does not care how the
slots are grouped.

Two things about how it survived, both worth generalising.

* **Every property proved before it was true of the wrong map too.**  Group-ring
  linearity, the degree-zero value, the Leibniz rule, the vanishing — all hold of
  the un-transposed grouping.  The chain-map property is the first statement that
  separates them.  A definition is pinned down only by the first property that
  distinguishes it from its plausible neighbours; until that one is proved, green
  probes are evidence about the proofs and not about the definition.
* **I had identified the exact hazard in advance and then walked into it.**  The
  argument for retiring the transposition — that `B` is defined on a free basis
  so the regrouping can be written into the value — is correct, and I wrote the
  un-transposed value anyway.  Retiring an object because its effect can be
  inlined only works if the effect is actually inlined.

## The remaining computation, specified

What is left of composite `B` is its **chain-map property**, then naturality and
the packaging as `compB : src ⟶ four`.  The design is settled; recording it so it
is not re-derived.

The statement wanted, at a free index and free total degree, is

```lean
theorem tensorD_compBGen_succ (X) (k i M : ℕ) (σ : singularSimplices X (M + 1)) :
    tensorD (pairFreeCx X) (pairFreeCx X) k (compBGen X (k + 1) (i + 1) σ)
      = (compBGen X k i σ + tenSwap (pairFreeCx X) k (compBGen X k i σ))
        + ∑ jj : Fin (M + 2), compBGen X k (i + 1) (faceSimplex X M jj σ)
```

together with its `i = 0` companion, where the `(1 + T)` term is absent for the
same reason it is absent from `dTgt_phiAtDeg_zero`.

Everything it runs on is green:

* `tensorD_padFour_succ` — differentiate one term of the double sum;
* `dTgt_phiAtDeg_succ`, `dTgt_phiAtDeg_zero` — the boundary identity applied to
  each differentiated factor;
* `dTgt_smul` — to move the differential past the `t^p` on the second factor;
* `dTgt_phiZero` — `Φ₀` is a chain map, which converts the sum over the faces of
  `σ` into the two halves of `∂Φ₀(σ)`;
* `pair_add_self` — the one characteristic-two cancellation.

The shape of the argument: differentiating the `p`-th term gives four families,
`Φ(e_{p-1} ⊗ σ')` and `T Φ(e_{p-1} ⊗ σ')` against `t^p Φ(e_q ⊗ σ'')`, and
`Φ(e_p ⊗ σ')` against `t^p Φ(e_{q-1} ⊗ σ'')` and `t^{p+1} Φ(e_{q-1} ⊗ σ'')`.
Reindexing `p ↦ p + 1` in the second pair makes the two middle families coincide,
and they cancel in characteristic two; what survives is `(1 + T)` applied to `B`
one index down, plus `B` of the boundary.  That cancellation is the concrete form
of `cc-cartan`'s `deltaW_chain_identity`, which never has to be invoked because
the tensor square of the group ring is never built.

## AUTHORED, UNVERIFIED

Nothing.

## STILL OWED

**Nothing.**  All four original deliverables are green, and so is everything
added since: `cup_comm`, the total operation `SqH`, the Cartan transport, the
target carrier and its differential, the corrected `PhiSwap`/`PhiHom`, the
chain-map condition, naturality, and

```lean
noncomputable def Steenrod.PhiNat : src singularBoundary ⟶ tgt
```

which is `Φ` in the shape the acyclic-models comparison consumes.  `d ∘ d = 0`
for the pair differential was ruled to be `cc-cartan`'s and is theirs
(`CartanSingularFreeCx.dTgt_dTgt`); this lane never wrote it.

One duplication is outstanding and is a decision, not a gap: `cc-cartan`'s
`pairIdxMap`/`pairMapF2`/`pairMapLambda` and this lane's
`pairIdxPush`/`pairPushLin`/`pairPushGRLin` are the same terms.  Theirs is the
one wired into the functor, so theirs should stay and these should be retired;
proposed to them, not yet actioned.  The `Sq^k` layer is green; what remains for
the program is the **Cartan formula**, which is `cc-cartan`'s to prove from
`steenrodDiag`, and the assembly of the graded `SqH : ℕ → H →+ H` on the total
cohomology, which needs `cc-cohom-api`/`cc-projective`'s direct sum.  My
`Sq k : Hmod2 X n → Hmod2 X (k + n)` is the graded piece it is assembled from.

## NEEDS

One input, from `cc-cartan`: the **graded** Cartan formula.  The transport to the
shape `cc-wu` and `cc-projective` consume is already green and waiting, so what
they need from `cc-cartan` is exactly

```lean
def CartanOf (X : TopCat.{0}) : Prop :=
  ∀ (n p q : ℕ) (a : Hmod2 X p) (b : Hmod2 X q),
    TotalH.of X (n + (p + q)) (Sq n (cup a b))
      = ∑ i ∈ Finset.range (n + 1),
          TotalH.of X (i + p) (Sq i a) * TotalH.of X ((n - i) + q) (Sq (n - i) b)
```

and then `Steenrod.SqH_mul_of_cartanOf` gives `cartanH` / `SqData.cartan`
verbatim.  Note the hypothesis is stated in `TotalH` rather than degreewise **on
purpose**: the naive graded statement does not typecheck, because the two sides
have degrees `n + (p+q)` and `(i+p) + ((n-i)+q)`, equal only propositionally and
only for `i ≤ n`.  `TotalH.of` absorbs the degree and the ring multiplication
does the bookkeeping.

`cc-wu` has discharged everything else that was on this list: `sqH_t`, `sqH_x`
and `t_mul_t` come from `SqH_map` plus sphere cohomology at one stroke, and
`sqH_ι` is `SqH_map` verbatim.  The projective-space input
(`H^3(ℂP^d; F₂) = 0`) is needed only for their `sq_y_one`; `sq_y_two` is
`Sq_self` and `sq_y_high` is `Sq_eq_zero_of_lt`, both already green.

## TRAPS

* The coboundary formula does **not** work by an involution on the index set.
  It telescopes.  Write `cutLow S t = (cutU S ∩ {x < t}) ∪ (cutV S ∩ {x ≥ t})`
  and `cutHigh` with the two families exchanged.  Inserting one cut point `c`
  produces the two threshold pairs at `c` and `c+1`, in one order or the other
  according to which family `c` was in; crossing an **old** cut point changes
  nothing, so the sum over `Sᶜ` extends to a sum over all `c` and telescopes to
  the two endpoints, which are the two orders of the original cut.
* At this Mathlib pin the Finset lemmas use the `notMem` spelling
  (`card_insert_of_notMem`, `notMem_erase`, `notMem_compl`,
  `erase_eq_of_notMem`), and `FunctorToTypes.map_id_apply` /
  `map_comp_apply` are deprecated, hence hard errors; use `Functor.map_id_apply`
  and `Functor.map_comp_apply`.
* `Finset.card_eq_iff_eq_univ` takes its `Finset` **explicitly**, so
  `.1` on the bare name fails with "projections cannot be used on functions".
* Two sums need two `Finset.sum_singleton` rewrites: `rw` instantiates the
  summand from the first match, so a second sum with a different summand is
  left untouched and the following `ring` then has a sum on one side.
* Instantiating a lemma whose argument is a lambda leaves beta-redexes in the
  resulting type, and `rw … at` will not match through them.  Either `exact` it
  (defeq does beta) or give the `have` an explicit, beta-reduced type.
* `cc-cohom-api`'s `cohCast` is `Eq.rec`, while the vendored `cocycleClass_cast`
  is stated with `eqToHom`.  `CharClass/CohomologyAssoc.lean` already bridges
  them with `cohCast_cocycleClass`; do not re-derive it.
* **An index type used inside `rw` must be reducible.**  `rw` checks
  type-correctness at `instances` transparency and will not unfold a plain
  `def`, so a goal mentioning `⟨⟨(a,b),h⟩,p⟩ : PairIdx X k` is untouchable while
  `PairIdx`/`PairDeg` are `def`s — every rewrite fails with "did not find an
  occurrence" plus a note about `↑p` having type `PairDeg k` rather than the
  subtype.  That cost six failures in one probe.  `abbrev` fixes it, changes no
  signature, and has one knock-on: a `rw` that used to leave a goal for a
  trailing `rfl` now closes it itself, so the `rfl` becomes "no goals to be
  solved".
* `attribute [local reducible]` **cannot** be set for a declaration from an
  imported module ("failed to set `[local reducible]`"), so the fix has to be
  made at the definition.
* End every `rw` chain whose two sides become syntactically identical with an
  `exact`, not by relying on the trailing `rfl`: whether `rw` closes such a goal
  depends on reducibility, so the same proof text can fail either as "unsolved
  goals" or as "no goals to be solved" depending on an unrelated `abbrev`.
* `subst h` with `h : J = k` where **both** sides are local variables eliminates
  `k`, not `J`, and every later mention of `k` in the proof becomes an unknown
  identifier.  For an index hypothesis whose right side is a variable, use
  `rw [h]`; keep `subst` for hypotheses whose right side is a literal, and for
  the one hypothesis (`N = 0`) that occurs in a simplex's type.
* `MonoidAlgebra.induction_on` cannot infer its motive from the goal; pass
  `(p := fun c : GroupRingZ2 => …)` explicitly.
* Totalising removes the casts twice over.  `faceVal` returns `0` on a vertex set
  of the wrong size; `padIdx` returns `0` unless the two degrees sum to the total
  one.  With the second, every sum over bidegrees runs over `Finset.range` with a
  summand that is a function of a bare natural, so `Finset.sum_range_succ` and
  `Finset.sum_nbij'` apply with no transport — which is what makes the
  `a ↦ k - a` reindexing of the equivariance step a three-line `omega`.
* **`cc-cartan`'s `singFreeCx` is a plain `def`**, so no `rw` with a lemma whose
  left side mentions `A.ι` can see that the index type is a type of simplices —
  and neither can the `rfl` that `rw` attempts afterwards.  Four probe rounds
  went to this in composite `A`.  Work in `calc` closed by `exact`, rewrite only
  with *closed* equations, and put an explicit `rfl` after each such rewrite.
* **Never force the structure projection `(pairFreeCx X).d`.**  `tensorFreeCx` is
  a structure literal whose square-zero field is a large proof, and naming that
  projection inside a `congrArg` with a dependent motive times out at `whnf` at
  200000 heartbeats — four timeouts across two attempts.  Route through `tdL` and
  `tdR` instead.  The projection *can* be named, but only on its own:
  `pairFreeCx_d_eq` is `rfl` and elaborates fine in a module by itself, which is
  why `SteenrodFourfoldBridge.lean` exists.
* A `calc` step ending `(lemma f k _ 1).symm` can fail where the same step with
  the index element written out succeeds, because the underscore has to be found
  by higher-order unification through a `def`.

## Composite B is finished (2026-09-06)

`compBNat : src singularBoundary ⟶ four` is green and landed at `ea7ff6a92`
(2913 jobs).  It is built exactly like `cc-cartan`'s `compA`, so the comparison
consumes the two composites the same way.

Landing order, one file per step, each green before the next was written:

| file | what it adds |
| --- | --- |
| `SteenrodFourfoldBBranch` | every branch of the Leibniz expansion, four degrees free |
| `SteenrodFourfoldBJunction` | the back-index junction, and the two live block splits |
| `SteenrodFourfoldBDegenCase` | the two degenerate bidegrees |
| `SteenrodFourfoldBGeneric` | the generic bidegree, with the cancellation |
| `SteenrodFourfoldBFaces` | the faces are the pair differential; the three branches assembled |
| `SteenrodFourfoldBChainMap` | the identity summed over the diagonal |
| `SteenrodFourfoldBEdgeCases` | resolution index `0`, simplex degree `0`, and the interchange |
| `SteenrodFourfoldBPackage` | the condition against `wDiff`, then `compBCx` and `compBNat` |

### What the collapsed formula hides

* **The cancellation is not uniform.**  Where both simplices are
  positive-dimensional the left block at index `p + 1` cancels the right block at
  index `p`, and that is `sum_cancelA_cancelB`.  Where either simplex is a point
  that pairing does not exist: the surviving family comes from the other block
  entirely, and the identity holds because the involution fixes a cochain of a
  point.  Three bidegrees, three proofs, and the two degenerate ones are not
  mirror images of each other.
* **Total degree zero needs the same fact.**  On a point `B` vanishes in positive
  resolution index but not in degree `0`, and there the `(1 + t)` half of the
  source differential dies only because the block swap fixes
  `x ⊗ x ⊗ x ⊗ x`.  Without `compBGen_add_tenSwap_pt` the chain map is false at
  the bottom of the complex.

### The junction recipe, which is what made the big proof cheap

Wherever the same number arrives spelled two ways, state the reconciliation as a
one-line lemma with the degrees free and the equation as a hypothesis, and cross
it with `congrArg` **before** any block lemma fires.  The abstraction has to be a
genuine function of the index whose *result* type does not mention it — `bBack`,
`padFourLBack`, `padFourRBack`, `faceLBack`, `faceRBack` — so `congrArg` applies
with no dependent motive.  Four such declarations, and afterwards the generic
branch compiled without one failed rewrite.

Three spellings and their status:

* `c + (p + 1)` versus `c + p + 1` — the same term; `exact` crosses it, `rw` does
  not.  No lemma needed, but never `rw`.
* `i + 1 - (p + 1)` versus `i - p` — **not** the same term (`Nat.sub` recurses on
  its second argument), and the number sits in the type of a cochain.  Needs
  `congrArg` along one of the abstractions above.
* `M + 1 + p` versus `M + (p + 1)` — **not** the same term either
  (`Nat.succ_add` is a theorem, not `rfl`).  Same treatment.

### Two more traps

* `Nat.succ_add M i` states its left side as `M.succ + i`, so a `congrArg` built
  from it carries the successor spelling and the rewrite will not fire on a goal
  written `M + 1 + i`.  Use `show M + 1 + i = M + (i + 1) by omega` so the proof
  carries the goal's spelling.
* A junction lemma stated on an abstraction (`bBack`) cannot fire on a goal in
  which the abstraction is not visible.  State it a second time on the term the
  goal actually contains (`bTerm_back_congr`).
* A `rw` chain that ends definitionally equal does **not** always close: `rw`'s
  trailing `rfl` failed on three goals whose only remainder was `0 - 0`, `M + 0`
  and an unfolded `def`.  Ending with an explicit `rfl` is the fix, but it is an
  error when the chain *did* close, so it costs one probe round either way.

## Chern factorisation, in cc-projective's name (2026-09-06)

Assigned after composite B.  Two files landed, both green, and the open
obligation is now a single named Prop instead of a hypothesis buried in three
consumers.

| commit | file | jobs |
| --- | --- | --- |
| `7b29c1d5a` | `ChernFactorBridge.lean` | 8871 |
| `984ddc130` | `ChernRootSection.lean` | 8872 |

Design note: `notes/chern-split-factorisation-design-2026-09-06.md`.

### What the survey settled

* The **algebra is complete**: `chernPoly_eq_prod_of_root` and `chernPoly_map`
  compose to the factorisation.  Nothing to add.
* The **tensor route is blocked**: there is no tensor product of bundles in the
  projection model and no dual.  The route needs the tensor, its classifying
  map, and additivity of the Euler class under tensor of lines, the last of which
  is a real theorem.
* **Nothing constructs a `LerayHirschData`** anywhere in the tree.

### The sharp obstruction

A section of the projective bundle gives a Chern root, by pure functoriality; at
rank one that proves `γ₁ = e(L)`.  It does not iterate: `p = (X - y₁)q` and
`p(y₂) = 0` give `(y₂ - y₁)q(y₂) = 0`, and `y₂ - y₁` is not a non-zero-divisor
in a cohomology ring.  On `P(L ⊕ 1)` the two sections give `γ₂ = 0` and
`e(L)(e(L) + γ₁) = 0`, leaving exactly `γ₁ = e(L)`, which is *equivalent* to
`SplitRelation` there.  The two are one obligation.

### The `rw` trap of this layer

`LerayHirschData.algebra` is a `@[reducible] def` and not an instance, so
`D.chernPolynomial` carries a pinned instance and is never syntactically
`chernPoly D.powerBasis`.  Every `rw` with a `ChernRelation` lemma fails on it;
cross the junction with a term (`.trans`) instead.  Both red rounds here were
this.

### A survey can go stale under you

The survey recorded that `Nontrivial (TotalH X)` was unproved.  `cc-cohom-api`
landed it three and a half minutes later.  Re-check a negative claim about the
tree before repeating it in a second message, not only before making it the
first time.

### The cover mechanism (2026-09-06, after the lead's ruling)

The lead ruled a third route to `SplitRelation`, needing neither a tensor product
nor a Gysin pushforward: each factor vanishes on the open set where its component
is nonzero, and a product of classes vanishing on the members of a finite open
cover is zero.  The bundle side goes to `cc-bundle` (shapes sent); the cochain
side is mine.

| commit | file | jobs |
| --- | --- | --- |
| `a87e86482` | `CupVanishCochain.lean` | 8737 |
| `f5f91f6ce` | `CupVanishSmallAnn.lean` | 8741 |

Both halves of the class-level theorem are green.  The core is the
Alexander–Whitney formula plus the observation that **both** faces stay inside
whatever the simplex is inside, so the two directions are one lemma and only
which factor dies differs.  The other half is acyclicity of the
small-annihilator complex, already on main, so nothing here subdivides anything.

The statement is about *small* simplices and not all of them, and that is the
shape of the argument rather than a weakness: a general simplex meets both sets
and the cochain product genuinely need not vanish on it.  Any attempt to state a
cochain-level equality is wrong.

**Blocked on**: `exists_cocycle_vanishing_on` in `CharClass/CartanCoverRep.lean`,
which is complete but **untracked** in the shared tree and not on origin.  Not
mine to land.

**A defect of mine.**  The first version rebuilt `twoSetCover` and
`subordinate_or_of_isSmallSimplex`, both of which already existed.  Removed one
commit later.  The check that failed: I grepped for the `OpenCoverData`
*declaration*, not for *constructions* of it, and the duplicate had a different
name so no name-based scan could catch it.  Grep for uses, not declarations.
