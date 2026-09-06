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

`Build completed successfully (2131 jobs)`.  Every module below has a `Built`
line (not `Replayed`) in the probe that first compiled it, and none has changed
since:

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

## AUTHORED, UNVERIFIED

Nothing.

## STILL OWED

Nothing from the original brief, and the chain-map condition is now green too.  The `Sq^k` layer is green; what remains for
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
