import GroupApproximation.Sofic.GreendlingerSharpInvariant

/-!
# The window drop is the arc drop, and both are the composite landing

`GreendlingerSharpDropGate` reduces the sharp Greendlinger gate to two families,
one of which is `GreendlingerDeepInvariant.DeepWindowDropSharp`: given the deep
regime, exhibit a window `(s.drop k).take m` of some symmetrized relator, longer
than `(1 - 3λ)` of it, inside what survives.  `GreendlingerSharpInvariant` §3
supplies the payload at a landing factor whose own block is shallow, and records
that the back bound it reads is exactly what fails when that factor is itself
deep.

This file removes the gap by not crossing it.  Two observations, and their
composition.

## 1.  The window form is not stronger than the arc form

`deepArcDropSharp_of_deepWindowDropSharp` turns a window into an arc through
`greendlingerAtSharp_of_rotation_window`, read at position `0`.  The converse is
immediate and appears to have gone unrecorded: `GreendlingerAtSharp R λ 0 w`
carries `w = A ++ u ++ C` with `u <+: s` and `(1 - 3λ)|s| < |u|`, and a prefix
is the window at `k = 0` — `u = (s.drop 0).take |u|`, with `0 + |u| ≤ |s|`
because `u` is a prefix.  No rotation is needed, and no relator is chosen that
the arc did not already choose.

So `DeepWindowDropSharp` and `DeepArcDropSharp` are the same obligation.  The
window shape buys the drop route nothing it did not already have, and costs it
nothing either.

## 2.  The arc form is discharged by the composite landing

`GreendlingerDeepInvariant` §§6-7 replace the deep arc obligation by a
positional one, `DeepCompositeLandsSharp`, and prove the descent
`greendlingerAtSharp_drop_of_lands` over it — an induction on a bound for the
number of factors, with the deep branch handing the composite block to the next
stage rather than asking it for an arc.  That descent is a *closed* theorem, so
its deep branch can be replayed outside the induction with the descent itself in
place of the induction hypothesis: past the junction by
`exists_postJunction_drop_sharp`, into the landing site by
`DeepCompositeLandsSharp`, and then into the descent at the sub-expression the
site names, which is shorter and therefore terminates on its own count.

That is `deepArcDropSharp_of_compositeLandsSharp_of_landingSharp` below.  Its
proof is the deep branch of `greendlingerAtSharp_drop_of_lands` transcribed, with
`ih` replaced by the theorem itself; nothing about the deep regime is
re-examined.

## What this settles

`DeepWindowDropSharp` is not an independent leaf.  Composing §§1-2:

```
DeepCompositeLandsSharp + LandingProductionSharp
  → DeepArcDropSharp        (deepArcDropSharp_of_compositeLandsSharp_of_landingSharp)
  → DeepWindowDropSharp     (deepWindowDropSharp_of_deepArcDropSharp)
```

so anything that discharges the composite-landing pair discharges the window
family that `GreendlingerSharpDropGate.sharpGreendlingerGate_of_windowDropSharp_of_landingSharp`
consumes, and the two drop-route gates of that file are consequences of its §3.
The routing lane therefore has exactly one open deep obligation, not two, and it
is the positional one — the one `GreendlingerDeepInvariant` §9's
`landsInSharp_of_forward_alignment` speaks to, using only the front piece bound.

Nothing here discharges `DeepCompositeLandsSharp` or `LandingProductionSharp`.

## Where the hypotheses go

`hlam` and `hmetric` are read only by `exists_postJunction_drop_sharp` and by
the descent; `hR` and `hRne` only by the descent.  §1 reads none of them, and no
sign hypothesis on `λ` is read anywhere in this file.
-/

namespace GroupApproximation
namespace SmallCancellationRouter

variable {α : Type*}

/-! ## 1.  A located arc is a window at offset zero -/

/-- **The window payload, from the arc.**  A `GreendlingerAtSharp` at position
`0` already exhibits the decomposition `DeepWindowDropSharp` asks for: the
subword it names is a prefix of its relator, hence the window `(s.drop 0).take m`
with `m` its length, and the fit condition `0 + m ≤ |s|` is the prefix bound.

The converse direction is
`GreendlingerDeepTailWindow.greendlingerAtSharp_of_rotation_window`, which is
what `deepArcDropSharp_of_deepWindowDropSharp` spends.  Together the two say the
window form and the arc form of the drop obligation are one statement. -/
theorem exists_windowSharp_of_greendlingerAtSharp {R : Set (List (α × Bool))}
    {lam : ℚ} {w : List (α × Bool)} (h : GreendlingerAtSharp R lam 0 w) :
    ∃ (s A C : List (α × Bool)) (k m : ℕ),
      s ∈ symmetrization R ∧
        w = A ++ (s.drop k).take m ++ C ∧
        k + m ≤ s.length ∧
        (1 - 3 * lam) * (s.length : ℚ) < (m : ℚ) := by
  obtain ⟨A, u, C, hw, -, s, hs, hpre, hlt⟩ := h
  have hu : u = s.take u.length := List.prefix_iff_eq_take.mp hpre
  obtain ⟨v, hv⟩ := hpre
  have hlen : s.length = u.length + v.length := by
    rw [← hv, List.length_append]
  refine ⟨s, A, C, 0, u.length, hs, ?_, by omega, hlt⟩
  rw [List.drop_zero, ← hu]
  exact hw

/-- **The window family, from the arc family.**  The converse of
`GreendlingerDeepInvariant.deepArcDropSharp_of_deepWindowDropSharp`, so the two
predicates are interderivable with no side conditions at all. -/
theorem deepWindowDropSharp_of_deepArcDropSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ} (h : DeepArcDropSharp R lam) :
    DeepWindowDropSharp R lam := by
  intro c t e g P' M B' N i hmin ht hredp heq htail hlow hi hN hgt
  exact exists_windowSharp_of_greendlingerAtSharp
    (h c t e g P' M B' N i hmin ht hredp heq htail hlow hi hN hgt)

/-! ## 2.  The arc obligation, from the two positional families

The deep branch of `GreendlingerDeepInvariant.greendlingerAtSharp_drop_of_lands`,
replayed outside the induction.  The descent is closed, so it serves as its own
induction hypothesis at the sub-expression the landing site names; the count that
made the descent terminate — `f₃.length < f.length < e.length` — is not needed
here, because the recursive call is made at that sub-expression's own length.

Three steps, all quoted from the descent: past the junction, which is empty in
the deep regime; into the landing site of the composite block; and into the
descent at the factor the site names, whose conclusion transports along the two
drops by `drop_add` and `drop_suffix_append`. -/

/-- **`DeepArcDropSharp` from the composite landing and the landing
production.**  The deep obligation of the drop route, discharged over the two
positional families of `GreendlingerDeepInvariant` §7.

The landing site's fit field `(D + (N - |P'|)) + N₃ ≤ |A₃| + |c₃| + i₃` is what
makes the recursive offset `N₃ + (D + (N - |P'|) - |A₃|)` admissible against
`|c₃| + i₃`, exactly as it does inside the descent. -/
theorem deepArcDropSharp_of_compositeLandsSharp_of_landingSharp [DecidableEq α]
    {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam : lam ≤ 1 / 6) (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepCompositeLandsSharp R lam)
    (hland : LandingProductionSharp R lam) :
    DeepArcDropSharp R lam := by
  intro c t e g P' M B' N i hmin ht hredp heq htail hlow hi hN hgt
  obtain ⟨c₂, t₂, f, D, ht₂, hredp₂, hmin₂, hf, hD⟩ :=
    exists_postJunction_drop_sharp hR hRne hlam hmetric hmin ht hredp heq htail
      hlow hi hgt
  obtain ⟨c₃, t₃, f₃, A₃, N₃, i₃, -, hV₃, ht₃, hredp₃, hmin₃, hi₃, hN₃,
    hfit₃⟩ :=
    hdeep c t c₂ t₂ e f g P' M B' N i D hmin hmin₂ ht ht₂ hredp hredp₂ heq
      htail hlow hi hN hgt hf hD
  have hrec := greendlingerAtSharp_drop_of_lands hR hRne hlam hmetric hdeep
    hland f₃.length f₃ c₃ t₃
    (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord
    (N₃ + (D + (N - P'.length) - A₃.length)) i₃
    le_rfl FreeGroup.isReduced_toWord ht₃ hredp₃
    (by rw [FreeGroup.mk_toWord]; exact hmin₃) hi₃ (by omega)
  have hcomp : B'.drop (N - P'.length)
      = (conjEval f).toWord.drop (D + (N - P'.length)) := by
    rw [hD, ← drop_add]
  have hsuf : (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord.drop
      (N₃ + (D + (N - P'.length) - A₃.length))
      <:+ (conjEval f).toWord.drop (D + (N - P'.length)) := by
    rw [hV₃, drop_add N₃ (D + (N - P'.length) - A₃.length)
      (conjEval ((FreeGroup.mk c₃, t₃) :: f₃)).toWord]
    exact drop_suffix_append A₃ _ (D + (N - P'.length))
  rw [hcomp]
  exact hrec.of_suffix hsuf

/-! ## 3.  The window obligation, discharged over the same two families -/

/-- **`DeepWindowDropSharp` from the composite landing and the landing
production.**

The composition of §§1-2, and the point of the file: the window family that
`GreendlingerSharpDropGate.sharpGreendlingerGate_of_windowDropSharp_of_landingSharp`
takes as an open leaf is a consequence of the pair
`GreendlingerSharpDropGate.sharpGreendlingerGate_of_compositeLandsSharp_of_betaSharp`
already takes.

The two hypotheses remain open; nothing here is proved about either. -/
theorem deepWindowDropSharp_of_compositeLandsSharp_of_landingSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam : lam ≤ 1 / 6) (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepCompositeLandsSharp R lam)
    (hland : LandingProductionSharp R lam) :
    DeepWindowDropSharp R lam :=
  deepWindowDropSharp_of_deepArcDropSharp
    (deepArcDropSharp_of_compositeLandsSharp_of_landingSharp hR hRne hlam
      hmetric hdeep hland)

/-- **The same, over the (β)-regime landing residual.**  Stated against the two
names the residual bundles use, through
`GreendlingerSharpTwins.landingProductionSharp_of_betaSharp`. -/
theorem deepWindowDropSharp_of_compositeLandsSharp_of_betaSharp
    [DecidableEq α] {R : Set (List (α × Bool))} {lam : ℚ}
    (hR : ∀ r ∈ R, FreeGroup.IsCyclicallyReduced r) (hRne : ∀ r ∈ R, r ≠ [])
    (hlam : lam ≤ 1 / 6) (hmetric : MetricSmallCancellation R lam)
    (hdeep : DeepCompositeLandsSharp R lam)
    (hbeta : LandingProductionBetaSharp R lam) :
    DeepWindowDropSharp R lam :=
  deepWindowDropSharp_of_compositeLandsSharp_of_landingSharp hR hRne hlam
    hmetric hdeep (landingProductionSharp_of_betaSharp hmetric hbeta)

end SmallCancellationRouter
end GroupApproximation
