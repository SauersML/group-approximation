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

`Build completed successfully (2062 jobs)`, all seven built (not replayed):

* `CharClass/SteenrodCut.lean`
* `CharClass/SteenrodCutCancel.lean`
* `CharClass/SteenrodCochain.lean`
* `CharClass/SteenrodCupEdge.lean`
* `CharClass/SteenrodCoboundary.lean`
* `CharClass/SteenrodCupOne.lean` — contains `cup_comm`
* `CharClass/SteenrodDiagonal.lean` — `steenrodDiag`, naturality, boundary
  (built at 7.0s in the immediately preceding probe of the same clone, unchanged
  since, replayed in the 2062-job run)

## AUTHORED, UNVERIFIED

Nothing.

## STILL OWED

The `Sq^k` layer (deliverable 3).  `Sq k x : Hmod2 X (n+k)` can be defined with
no `dite` as the class of `cochainCupI (n-k) n n (n+k) r r` for a chosen cocycle
representative `r`, and instability `Sq^k = 0` for `k > n` is then free from
`cochainCupI_of_degree_ne`.  Everything else (`Sq_mk`, naturality, additivity,
`Sq^0 = id`, `Sq^n x = x ⌣ x`) needs one lemma the vendored tree does not have:
`cocycleClass X n χ hχ = 0 → χ` is a coboundary.  Route:
`ShortComplex.moduleCatHomologyIso` plus
`ShortComplex.moduleCatLeftHomologyData` present the homology as
`ker g ⧸ range f'`, so `Submodule.Quotient.mk_eq_zero` gives it; the work is
transporting `HomologicalComplex.homologyπ` through `π_moduleCatCyclesIso_hom`.

## NEEDS

Nothing from a peer.

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
