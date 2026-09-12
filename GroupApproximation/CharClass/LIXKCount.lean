import GroupApproximation.CharClass.CohomologyBasic
import GroupApproximation.Meta.AxiomGuard

/-!
# The count: a class that splits into `k` equal local pieces is `k` times one of them

Lane `sp-oddside` of the STW Problem LIX strengthening
(`notes/LIX_STRONGER_PROGRAM_2026-09-10.md` §1.3.4; `sp-design`'s report §4.2).

This is the whole of the `k`-zero Step C downstream of the geometry, and it is pure linear
algebra over an arbitrary field.  It is written over `[Field K]` from the start, so that
`sp-coeff`'s coefficient parameter costs this lane nothing later; `ZMod 2` is the `p = 2`
instance and is a field.

## What replaces `sp-design` §4.2's direct-sum splitting

Their item 3 asks for `H^{2r}(N, N∖Z) ≅ ⊕_i H^{2r}(N, N∖{z_i})` compatible with `j`.  The
consumer uses only the surjectivity half, and only in the cheaper direction.  For each `i`
the identity of `N` is a map of pairs `(N, N∖Z) → (N, N∖{z_i})`, because `N∖Z ⊆ N∖{z_i}`,
so relative pullback gives

```text
  ρ_i : H^{2r}(N, N∖{z_i}) ⟶ H^{2r}(N, N∖Z) ,     ρ_i ≫ j = j_i
```

the second by naturality of `relToAbs` along the identity.  The obligation is then the
single equation `x = ∑_i ρ_i (x_i)` — no biproduct, no compatibility square stated
separately, and nothing to invert.  `LocalSplit` below names it.

## The count, and where the parity enters

```text
   j(x) = ∑_i j(ρ_i x_i) = ∑_i j_i(x_i) = ∑_i c = k • c ,
```

so `j(x) ≠ 0` as soon as `c ≠ 0` and `(k : K) ≠ 0`.  **No local degree, no determinant and
no orientation is computed anywhere**, which is the design goal of §1.3.4: the `k` local
contributions are equal because the zeros are one orbit of a rotation, not because their
local degrees have been computed and compared.

At `K = ZMod 2` the arithmetic side condition `(k : K) ≠ 0` is exactly "`k` is odd", which
is the strengthening's "every **odd** power of the witness stays outside `U₀`".

## Main declarations

* `LocalSplit`, `LocalClassesAgree` — the two obligations, named.
* `map_eq_nsmul_of_localSplit` — **the count**, `j(x) = k • c`.
* `map_ne_zero_of_localSplit` — the conclusion, over `c ≠ 0` and `(k : K) ≠ 0`.
* `natCast_ne_zero_zmod_two` — the `p = 2` form of the side condition.
-/

noncomputable section

namespace GroupApproximation.CharClass

open CategoryTheory

variable {K : Type} [Field K]

/-! ## 1. The two obligations, named -/

/-- **The local splitting.**  The relative class `x` on the pair with all `k` punctures is
the sum of the images of `k` classes, one on each single-puncture pair.

Discharged by excision to `k` disjoint balls around the zeros; owner `sp-oddside`, and at
odd `p` it needs nothing from `sp-coeff` beyond the coefficient parameter itself, because
excision (`CharClass/RelativeExcision.lean`) is already stated over a `CommRing`. -/
def LocalSplit {rel : ModuleCat.{0} K} {k : ℕ} {relLoc : Fin k → ModuleCat.{0} K}
    (rho : ∀ i, relLoc i ⟶ rel) (x : rel) (xloc : ∀ i, relLoc i) : Prop :=
  x = ∑ i, (rho i).hom (xloc i)

/-- **The local classes agree.**  Every one of the `k` local pieces has the same image in
the absolute group.

There are two routes to it and they need different things (`sp-design`, review of this
lane, 2026-09-10):

* **at `p = 2`, no transport at all.**  `H^{2r}(N; F₂)` is a line, so an `F₂`-line has a
  unique nonzero element and `(jloc i).hom (xloc i) = c` for every `i` as soon as each is
  nonzero — which is the one-zero argument run at `z_i`.  No isotopy, no naturality square
  along the rotation, and no homotopy invariance of any kind.  The fact to cite is
  `ThomStepCEuler.eq_localGenerator_of_ne_zero`, **not**
  `CharClass/RelativeLineHomotopy.lean`: that file is mod-2-only by its own docstring and
  importing it would build a dependency the odd-`p` deliverable has to tear out again.
  What this route does need is `PuncturedAcyclic N (2r) z_i` at **every** `i`, not only at
  the distinguished one.
* **at any `p`, the rotation transport.**  `sp-design` §4.1's Half A and Half B: naturality
  of `relToAbs` along `R^i` plus absolute homotopy invariance, and then the equality of the
  local classes.  This needs no extra punctured acyclicity but does need `sp-coeff`'s
  relative homotopy invariance over a field.

The hypothesis is deliberately left abstract here because the two discharges have different
shapes.  Owner `sp-oddside`. -/
def LocalClassesAgree {A : ModuleCat.{0} K} {k : ℕ} {relLoc : Fin k → ModuleCat.{0} K}
    (jloc : ∀ i, relLoc i ⟶ A) (xloc : ∀ i, relLoc i) (c : A) : Prop :=
  ∀ i, (jloc i).hom (xloc i) = c

/-! ## 2. The count -/

/-- **The count.**  A class that splits into `k` local pieces with a common image is `k`
times that image.

Every step is an equality of classes; nothing is evaluated, compared or oriented. -/
theorem map_eq_nsmul_of_localSplit {rel A : ModuleCat.{0} K} {k : ℕ}
    {relLoc : Fin k → ModuleCat.{0} K}
    (j : rel ⟶ A) (rho : ∀ i, relLoc i ⟶ rel) (jloc : ∀ i, relLoc i ⟶ A)
    (hcompat : ∀ i, rho i ≫ j = jloc i)
    {x : rel} {xloc : ∀ i, relLoc i} (hsplit : LocalSplit rho x xloc)
    {c : A} (hloc : LocalClassesAgree jloc xloc c) :
    j.hom x = k • c := by
  have hl : ∀ i, (jloc i).hom (xloc i) = c := hloc
  have hs : x = ∑ i, (rho i).hom (xloc i) := hsplit
  have hterm : ∀ i : Fin k, j.hom ((rho i).hom (xloc i)) = c := by
    intro i
    calc j.hom ((rho i).hom (xloc i)) = (rho i ≫ j).hom (xloc i) := rfl
      _ = (jloc i).hom (xloc i) := by rw [hcompat i]
      _ = c := hl i
  rw [hs, map_sum]
  simp only [hterm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

/-- **The conclusion.**  If one local class is nonzero and `k` is invertible in the
coefficient field, the global class is nonzero. -/
theorem map_ne_zero_of_localSplit {rel A : ModuleCat.{0} K} {k : ℕ}
    {relLoc : Fin k → ModuleCat.{0} K}
    (j : rel ⟶ A) (rho : ∀ i, relLoc i ⟶ rel) (jloc : ∀ i, relLoc i ⟶ A)
    (hcompat : ∀ i, rho i ≫ j = jloc i)
    {x : rel} {xloc : ∀ i, relLoc i} (hsplit : LocalSplit rho x xloc)
    {c : A} (hloc : LocalClassesAgree jloc xloc c) (hc : c ≠ 0)
    (hk : ((k : ℕ) : K) ≠ 0) :
    j.hom x ≠ 0 := by
  rw [map_eq_nsmul_of_localSplit j rho jloc hcompat hsplit hloc]
  intro h0
  refine hc ?_
  have hkk : ((k : ℕ) : K) • c = 0 := by
    rw [Nat.cast_smul_eq_nsmul]
    exact h0
  have h1 : (((k : ℕ) : K))⁻¹ • ((((k : ℕ) : K)) • c) = 0 := by rw [hkk, smul_zero]
  rwa [inv_smul_smul₀ hk] at h1

/-! ## 3. The `p = 2` form of the side condition -/

/-- At mod-2 coefficients the side condition `(k : K) ≠ 0` is exactly that `k` is odd.
This is where "every **odd** power of the witness stays outside `U₀`" comes from: it is a
statement about the coefficient field, not about the geometry. -/
theorem natCast_ne_zero_zmod_two {n : ℕ} (hn : Odd n) : ((n : ℕ) : ZMod 2) ≠ 0 := by
  have h1 : n % 2 = 1 := Nat.odd_iff.mp hn
  have h2 : ((n : ℕ) : ZMod 2) = ((n % 2 : ℕ) : ZMod 2) := (ZMod.natCast_mod n 2).symm
  rw [h2, h1]
  decide

/-! Audited on every build: `#audit_axioms` prints the closure **and fails the build** if
it leaves the classical allowlist. -/

#audit_axioms map_eq_nsmul_of_localSplit
#audit_axioms map_ne_zero_of_localSplit

end GroupApproximation.CharClass
