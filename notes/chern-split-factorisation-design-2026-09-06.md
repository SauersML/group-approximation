# The Chern polynomial of a sum of lines factors — design

Lane `cc-steenrod`, assigned 2026-09-06 in `cc-projective`'s name under rule 13.
Rule 14 survey first; no Lean written before this note.

## 1. What the consumers want, verbatim

Three places want the same thing.

* `CharClass/ChernWhitneyFlag.lean:103`, `hasSplitting_of_splitPoly`, hypothesis
  `hsplit`.
* `CharClass/ChernSplittingInjective.lean:72`,
  `hasSplitting_of_splitPoly_injective`, the same hypothesis — and this is the
  form the flag bundle can actually supply, because it never mentions a
  Leray–Hirsch structure for the tower, only injectivity of the pullback.
* `CharClass/LemmaTwoStepDLix.lean:62`, `WuStepDLix.hslice`, the slice instance
  for `V = 𝟏³ ⊕ H` over `Y`.

The statement, with `D : LerayHirschData N P` and `proj : F ⟶ N`:

```lean
D.chernPolynomial.map (TotalH.map proj)
  = ∏ l ∈ Finset.range r, (X + C (TotalH.of F 2 (root l)))
```

## 2. Survey: what is already on `origin/main`

**The algebra is complete.**  `CharClass/ChernRelation.lean` has everything:

| name | statement |
| --- | --- |
| `chernPoly_eq_of_monic` | a monic degree-`dim` polynomial killing the generator **is** the Chern polynomial |
| `chernPoly_eq_prod_of_root` | if `∏ (ξ + y_i) = 0` with `#s = dim`, then `chernPoly = ∏ (X + C y_i)` |
| `chernPoly_map` | naturality: a base change preserving the relation maps one Chern polynomial to the other |
| `chernClass_eq_esymm` | Vieta in coefficients |

So the target is `chernPoly_eq_prod_of_root` composed with `chernPoly_map`, and
**no new algebra is needed at all**.

**The sign convention is already pinned and already correct.**  The module
docstring of `ChernRelation.lean` fixes `p = X^r + γ₁X^{r-1} + ⋯` with `+` signs,
so that `p = ∏ (X + y_k)` and `γ(L) = X + e(L)` for a line.  This is exactly the
`r = 1` convention the assignment asked to check, and it is not merely invisible
mod 2: the coefficient indexing `chern i = chernPolynomial.coeff (rank - i)`
places `γ₁` at `coeff 0` at rank one, which is the constant term, which is the
root.  That indexing is already exercised by the landed
`chern_split_of_splitPoly`, so it is verified, not assumed.

**The geometry is entirely open.**  Two facts decide the route.

* **Nothing constructs a `LerayHirschData`.**  Grep over the whole tree: the
  structure is mentioned in four files and is a *hypothesis* in every one
  (`ChernClasses`, `ChernWhitneyFlag`, `ChernSplittingInjective`,
  `ThomChernBasis`).  There is no bridge from `Bundle X ι` to `LerayHirschData`.
* **There is no tensor product of bundles in the projection model.**  The
  operations that exist are `comap`, `plusOne`, `triv`, `pushforward`,
  `reindex`, `blockSum`, `tautLine`, `flagLine`, `flagComplement`, `cpTaut`,
  `hopfLine`, `lineOf`.  No `⊗`, no dual.  `AlgTop/Kronecker.lean` is the
  homology pairing, not a bundle operation.  Nothing named Segre exists.

What does exist on the geometric side and is relevant:

* `CharClass/BundleFlag.lean` — `Flag p n`, `flagProj`, `flagLine`,
  `flag_decomposition` (the lines exhaust the pullback, by the trace argument),
  `flagLine_mul_flagLine` (pairwise orthogonality), `flagForget`, `flagOne`.
* `CharClass/ChernEulerBundle.lean` — `eulerOfBundle`, its naturality
  `eulerOfBundle_comap`, the normalisation `eulerOfBundle_cpTaut`, and
  `eulerOfBundle_eq_zero_of_factors` (which is only about a classifying map
  factoring through an `H^2`-free space, *not* about common zeros).
* `CharClass/LerayHirschPlusOneClosed.lean` —
  `lerayHirschGraded_plusOne_tautEuler`, Leray–Hirsch for `P(L ⊕ 1)` over any
  base with no compactness.  This is the **freeness** half only.  There is no
  relation for `P(L ⊕ 1)` anywhere.

## 3. The consequence for the route

The assignment offered two routes.  The survey kills one of them.

* **Tensor route** — each `ξ + e(L_l)` is the Euler class of `taut* ⊗ π^*L_l`,
  the `r` sections have no common zero, so the product vanishes.  This needs a
  tensor product of rank-one projection fields, its classifying map, and
  `e(L ⊗ M) = e(L) + e(M)`.  None of that exists, and the last one is a real
  theorem (the group structure on `[X, ℂP^∞]`), not a definition chase.
* **Induction route** — through `P(L ⊕ 1)`, where Leray–Hirsch is already
  unconditional.  This needs the *relation* on `P(L ⊕ 1)`, which is the `r = 2`
  case with one trivial summand.

Mod 2 the dual is invisible (`e(L*) = -e(L) = e(L)`), so nothing in either route
has to distinguish `taut` from `taut*`.  That is a genuine simplification and it
is worth stating once.

## 4. What I will build, and what it leaves open

The honest split is **one algebraic bridge, which I can land immediately, and
one geometric Prop, which I cannot**.

### 4.1 The bridge (buildable now, no geometry)

```lean
/-- The one geometric input, named. -/
def SplitRelation {F P' : TopCat.{0}} (D' : LerayHirschData F P') (r : ℕ)
    (root : ℕ → Hmod2 F 2) : Prop :=
  ∏ l ∈ Finset.range r,
      (TotalH.of P' 2 D'.taut + TotalH.map D'.proj (TotalH.of F 2 (root l))) = 0

/-- **The factorisation, from the split relation upstairs.** -/
theorem splitPoly_of_splitRelation
    {N F P P' : TopCat.{0}} (D : LerayHirschData N P) (D' : LerayHirschData F P')
    (proj : F ⟶ N) (q : P' ⟶ P)
    (hsq : D'.proj ≫ proj = q ≫ D.proj)
    (htaut : TotalH.of P' 2 D'.taut = TotalH.map q (TotalH.of P 2 D.taut))
    (r : ℕ) (hr : D.rank = r) (hr' : D'.rank = r)
    (root : ℕ → Hmod2 F 2)
    (hrel : SplitRelation D' r root) :
    D.chernPolynomial.map (TotalH.map proj)
      = ∏ l ∈ Finset.range r, (X + C (TotalH.of F 2 (root l)))
```

Proof, three named steps and nothing else:

1. `chernPoly_eq_prod_of_root D'.powerBasis (Finset.range r) _ (card = rank)
   hrel` gives `D'.chernPolynomial = ∏ (X + C (root l))`.  The algebra map of
   `D'.algebra` is `TotalH.map D'.proj` by construction, which is why
   `SplitRelation` is written with that map.
2. `chernPoly_map D.powerBasis D'.powerBasis (TotalH.map proj) hdim hroot` gives
   `D'.chernPolynomial = D.chernPolynomial.map (TotalH.map proj)`.  Its `hroot`
   is discharged from `hsq` and `htaut` alone: pushing `aeval` through the two
   compatibilities turns it into `TotalH.map q` applied to
   `D.aeval_taut_chernPolynomial`, hence `TotalH.map q 0 = 0`.  Functoriality is
   `ThomChern.totalMap_comp`, already on main.
3. Chain them.

Nothing in this is geometry, and after it the *only* thing anyone owes is
`SplitRelation`.

### 4.2 The geometric Prop (not buildable without new bundle theory)

`SplitRelation D' r root` for `D'` the projectivisation of `⊕_l L_l` over the
flag space, `root l = e(flagLine p r l)`.  Cost estimate below.

## 5. Model tests

Standing order: model-test every hypothesis Prop.  Both cases are genuine
instances, neither vacuous nor false.

**`r = 1`.**  `E = L`, `P(E) = X`, `D.rank = 1`, `D.taut = ξ`.  Leray–Hirsch is
satisfiable: `lhFun proj 1 taut c = TotalH.map proj (c 0)`, bijective exactly
when `TotalH.map proj` is, which holds because `proj` is an isomorphism.  The
relation is `ξ + γ₁ = 0`, so `γ₁ = ξ`, and the tautological line of `P(L)` is `L`
itself, so `ξ = e(L)` and `chernPolynomial = X + C(e(L))`.  Matches the
convention.  `SplitRelation` reads `ξ + e(L) = 0`, which is true and, mod 2,
carries no sign information — so this case confirms the *coefficient indexing*
but cannot confirm a sign, which is why the indexing was checked separately in
§2.

**`r = 2`.**  Take `X = ℂP^d`, `E = taut ⊕ 1`, so `e_1 = h`, `e_2 = 0`.  The
claim is `ξ² + hξ = 0`, that is `ξ(ξ + h) = 0`.  Geometrically the two zero loci
are the disjoint sections `P(1)` and `P(taut)` of `P(taut ⊕ 1)`, so the product
vanishes and neither factor does.  Non-vacuous, and it is exactly the `P(L ⊕ 1)`
case where Leray–Hirsch is already unconditional.

**A free field, worth knowing.**  `Wu.SplittingData`'s `hroot` — every root is
pulled back from some `CPtop d` — is automatic for any root of the form
`eulerOfBundle`, because `eulerClass hgen f` is *by definition* `pull f 2 hgen`.
Take `g := cmap (Bundle.classifyOne _ _)` and `h := cpGen d hd`.  Nobody has to
prove that field.

## 6. Cost

* §4.1, the bridge: one file, no geometry, no new imports beyond `ChernRelation`,
  `ChernClasses` and `ThomChernBasis`.
* §4.2, `SplitRelation` for the flag bundle: blocked on either a tensor product
  of line bundles in the projection model with `e(L ⊗ M) = e(L) + e(M)`, or the
  relation for `P(L ⊕ 1)` plus an induction over the summands.  Neither is a
  small build, and the second is the cheaper of the two because Leray–Hirsch for
  `P(L ⊕ 1)` is already unconditional.

The recommendation is therefore: land §4.1 now, so that the open obligation is a
single named Prop rather than a hypothesis buried in three consumers, and take
the `P(L ⊕ 1)` relation as the next target.
