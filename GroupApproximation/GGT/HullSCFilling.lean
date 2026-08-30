import GroupApproximation.GGT.HullSCDGO
import GroupApproximation.GGT.HullSCSmallCancellation

/-!
# Hull's Theorem 5.1 split along Dahmani-Guirardel-Osin's Theorem 5.3

M. Hull, *Small cancellation in acylindrically hyperbolic groups*, Groups
Geom. Dyn. 10 (2016) 1077-1119, §5, over Dahmani-Guirardel-Osin,
*Hyperbolically embedded subgroups and rotating families in groups acting on
hyperbolic spaces*, Mem. Amer. Math. Soc. 245 (2017), no. 1156, §5.

`GGT/HullSCSmallCancellation.lean` reduces the whole lane to three leaves, one
of which -- `HullQuotientStatement`, Hull's Theorem 5.1 -- is a citation with
ten conclusions.  This module splits it where Hull's own proof splits: DGO's
Theorem 5.3 is applied to a rotating family built from the small cancellation
family, and the conclusions divide into the ones DGO's theorem supplies and the
ones about the *alphabet* of the quotient, which it does not.

* Supplied by DGO, so no longer cited: the quotient group and the quotient map,
  its surjectivity, the identification of its kernel with the normal closure of
  the relator, the lifting of finite order, and -- through
  `injOn_cayleyBall_of_action` below -- injectivity on the `R`-ball of
  `Γ(G,A)`.  Seven of the ten fields of `HullSC.HullFillingQuotient`.
* Left as `HullFillingDataStatement`: the construction of the rotating family
  from the `C(ε, μ, ρ)` condition, and the transfer of Hull's alphabet to the
  quotient with the prescribed suitable subgroups staying suitable.

## The space is not `Γ(G, A ⊔ H)`, and cannot be

The combinatorial cone-off `HullSC.coneOff` is the right model of the *metric*:
adjoining every element of `H` as a letter crushes each coset to diameter one.
It is the wrong model of DGO's cone-off for the *rotating family*, and the
obstruction is not a matter of approximation:

> `rot_eq_bot_of_cayley` -- **a rotating family on a Cayley graph of `G` has
> trivial rotation subgroups**, because `G` acts on `Γ(G,B)` freely: a rotation
> fixes its apex, and `g • c = c` reads `g · c = c` in `G`, so `g = 1`.  Hence
> `rotationNormalClosure_eq_bot_of_cayley`: the subgroup the rotations generate
> is `⊥`, and DGO's Theorem 5.3 applied on `Γ(G,B)` produces only the identity
> quotient.

DGO's cone-off attaches an actual cone over each coset `gH`, with an apex that
is *not* a vertex of `Γ(G,A)`, and `Rot` of that apex is `g ⟨⟨W⟩⟩ g⁻¹`, which
fixes it.  So the family lives on a space with more points than `G`, and
`RotatingData` below carries that space abstractly rather than naming it.

What the abstract space still has to supply is the comparison with `Γ(G,A)`
that the injectivity clause needs, and one inequality is enough for it: every
letter of `A` moves the basepoint by at most one (`RotatingData.letter_dist`).
That holds in DGO's cone-off because it contains `Γ(G,A)` with its edges of
length one, and `dist_smul_le_wordNorm` turns it into `d(y, g·y) ≤ |g|_A` for
every `g`, which is all `injOn_cayleyBall_of_action` uses.

This corrects the route `HullSCTheorem51.injOn_cayleyBall_of_rotatingQuotient`
takes.  That lemma is true as stated -- it does not assume `IsRotatingFamily`,
so nothing is refuted -- but a `RotatingQuotient` coming from DGO's theorem
does, and over a Cayley graph of `G` that forces the kernel to be trivial.  So
the injectivity clause has to be routed through an abstract space, which is
what `injOn_cayleyBall_of_action` does.

The second thing the abstract space has to supply is that the basepoint is not
an apex, and not near one: `HullSC.eq_one_of_dist_lt_everywhere` shows that a
displacement clause holding at every point of the space would force every
rotation subgroup to be trivial, since a rotation fixes its apex and lies in the
kernel.  `RotatingData.kernel_moves_base` is stated so that this cannot happen
-- it is quantified over the kernel and asserted at the basepoint alone -- and
in the construction it is free of charge for the same reason a separation clause
would have been: the identity vertex of `Γ(G,A)` sits at the cone radius from
the nearest apex.

`RotatingData` carries two clauses that are Hull's own and were once read off
DGO's Theorem 5.3: that one, and `finiteOrder_lift`.  Both moved after being
checked against the source, the second at issue #50, where the statement
carrying it was refuted outright.
-/

namespace GroupApproximation
namespace HullSC

open GroupApproximation.HullGeometry
open GroupApproximation.WordMetric
open GroupApproximation.Manuscript.NonMF.TorsionFree

universe u v

/-! ## Displacement of a basepoint under a word -/

/-- **A word of length `n` in letters that move the basepoint by at most one
moves it by at most `n`.**  Induction along the list, with the triangle
inequality and the isometry of the action. -/
theorem dist_smul_le_length {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] (hiso : IsIsometricAction G X)
    {S : Set G} (y : X) (hS : ∀ a ∈ S, dist y (a • y) ≤ 1) :
    ∀ l : List G, (∀ a ∈ l, a ∈ S) → dist y (l.prod • y) ≤ (l.length : ℝ) := by
  intro l
  induction l with
  | nil =>
      intro _
      have h1 : (List.nil : List G).prod • y = y := by
        rw [List.prod_nil, one_smul]
      rw [h1, dist_self]
      simp
  | cons a t ih =>
      intro hmem
      have ha : a ∈ S := hmem a (by simp)
      have ht : ∀ b ∈ t, b ∈ S := fun b hb => hmem b (by simp [hb])
      have hprod : (a :: t).prod • y = a • (t.prod • y) := by
        rw [List.prod_cons, mul_smul]
      have htri : dist y (a • (t.prod • y))
          ≤ dist y (a • y) + dist (a • y) (a • (t.prod • y)) :=
        dist_triangle _ _ _
      have hstep : dist (a • y) (a • (t.prod • y)) = dist y (t.prod • y) :=
        hiso a y (t.prod • y)
      have hlen : (((a :: t).length : ℕ) : ℝ) = (t.length : ℝ) + 1 := by
        rw [List.length_cons, Nat.cast_add, Nat.cast_one]
      have htail := ih ht
      have hone := hS a ha
      rw [hprod]
      linarith

/-- **Displacement of the basepoint is bounded by the word length.**  A
consequence of `dist_smul_le_length` at a shortest word. -/
theorem dist_smul_le_wordNorm {G : Type u} [Group G] {X : Type v}
    [PseudoMetricSpace X] [MulAction G X] (hiso : IsIsometricAction G X)
    (A : Alphabet G) (y : X) (hA : ∀ a ∈ A.carrier, dist y (a • y) ≤ 1)
    (g : G) : dist y (g • y) ≤ (wordNorm A.carrier g : ℝ) := by
  obtain ⟨l, hl, hlen⟩ := exists_isWord_length_eq A.symmetricGenerating g
  have h := dist_smul_le_length hiso y hA l hl.letters
  rw [hl.prod_eq, hlen] at h
  exact h

/-- **Injectivity on a ball of `Γ(G,A)` from an injectivity radius on any space
the group acts on by isometries**, provided the letters of `A` move the
basepoint by at most one.

This is `HullSC.injOn_cayleyBall_of_dist_lt` with the cone-off replaced by an
arbitrary `G`-space.  The replacement is forced: the space DGO's rotating
family lives on is not a Cayley graph of `G` (see `rot_eq_bot_of_cayley`), so
the hypothesis has to be available off `Γ(G, A ⊔ H)`. -/
theorem injOn_cayleyBall_of_action {G : Type u} [Group G] {Q : Type*} [Group Q]
    {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    (hiso : IsIsometricAction G X) (A : Alphabet G) (y : X)
    (hA : ∀ a ∈ A.carrier, dist y (a • y) ≤ 1) (q : G →* Q) {L : ℝ} (R : ℕ)
    (hL : 2 * (R : ℝ) < L)
    (hker : ∀ g : G, g ≠ 1 → dist y (g • y) < L → q g ≠ 1) :
    Set.InjOn q (cayleyBall A R) := by
  intro x hx z hz hxz
  by_contra hne
  have h1 : x⁻¹ * z ≠ 1 := fun h => hne (inv_mul_eq_one.mp h)
  have hq : q (x⁻¹ * z) = 1 := by
    rw [map_mul, map_inv, hxz]
    simp
  refine hker _ h1 ?_ hq
  have hxA : wordNorm A.carrier x ≤ R := by
    have hmem := (mem_cayleyBall_iff A R x).mp hx
    rwa [wordDist_one_left] at hmem
  have hzA : wordNorm A.carrier z ≤ R := by
    have hmem := (mem_cayleyBall_iff A R z).mp hz
    rwa [wordDist_one_left] at hmem
  have hmul : wordNorm A.carrier (x⁻¹ * z) ≤ 2 * R := by
    have hsub := wordNorm_mul_le A.symmetricGenerating x⁻¹ z
    rw [wordNorm_inv A.symmetricGenerating x] at hsub
    omega
  have hdisp := dist_smul_le_wordNorm hiso A y hA (x⁻¹ * z)
  have hcast : (wordNorm A.carrier (x⁻¹ * z) : ℝ) ≤ 2 * (R : ℝ) := by
    exact_mod_cast hmul
  linarith

/-- **Injectivity on a ball, from the kernel moving the basepoint.**

The injectivity radius is Hull's §5 rather than DGO's Theorem 5.3, whose
conclusions are the free splitting and the conjugate-or-loxodromic dichotomy --
loxodromy is asymptotic and gives no bound at the first power, and the splitting
is not metric.  So the clause is produced by the family, in the form
`RotatingData.kernel_moves_base`, and this is the two-line passage from it to a
statement about a given quotient map. -/
theorem injOn_cayleyBall_of_kernel_moves {G : Type u} [Group G] {Q : Type*}
    [Group Q] {X : Type v} [PseudoMetricSpace X] [MulAction G X]
    (hiso : IsIsometricAction G X) (A : Alphabet G) (y : X)
    (hA : ∀ a ∈ A.carrier, dist y (a • y) ≤ 1) (q : G →* Q) {K : Subgroup G}
    (hker : q.ker = K) {L : ℝ} (R : ℕ) (hL : 2 * (R : ℝ) < L)
    (hmove : ∀ g ∈ K, g ≠ 1 → L ≤ dist y (g • y)) :
    Set.InjOn q (cayleyBall A R) := by
  refine injOn_cayleyBall_of_action hiso A y hA q (L := L) R hL ?_
  intro g hg hdist hq
  have hmem : g ∈ K := by
    rw [← hker]
    exact MonoidHom.mem_ker.mpr hq
  have hge : L ≤ dist y (g • y) := hmove g hmem hg
  linarith

/-! ## Why the family cannot live on a Cayley graph of `G` -/

/-- **A rotating family on `Γ(G,B)` has trivial rotation subgroups.**  The
translation action of `G` on its own Cayley graph is free, and a rotation about
an apex fixes it. -/
theorem rot_eq_bot_of_cayley {G : Type u} [Group G] {B : Alphabet G}
    {C : Set (Cayley B)} {Rot : Cayley B → Subgroup G}
    (hfam : IsRotatingFamily G (Cayley B) C Rot) {c : Cayley B} (hc : c ∈ C) :
    Rot c = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro g hg
  have hfix : g • c = c := hfam.rot_fix hc g hg
  have hv : g * Cayley.val c = Cayley.val c := by
    have h : Cayley.val (g • c) = Cayley.val c := by rw [hfix]
    rwa [Cayley.val_smul] at h
  have hg1 : g = 1 := by
    have h : g * Cayley.val c * (Cayley.val c)⁻¹
        = Cayley.val c * (Cayley.val c)⁻¹ := by rw [hv]
    rwa [mul_inv_cancel_right, mul_inv_cancel] at h
  rw [Subgroup.mem_bot]
  exact hg1

/-- **So the rotations of a rotating family on `Γ(G,B)` generate nothing.**
Dahmani-Guirardel-Osin's Theorem 5.3, applied on a Cayley graph of `G` itself,
produces a quotient map with trivial kernel: the identity.  This is what forces
`RotatingData` below to carry an abstract space. -/
theorem rotationNormalClosure_eq_bot_of_cayley {G : Type u} [Group G]
    {B : Alphabet G} {C : Set (Cayley B)} {Rot : Cayley B → Subgroup G}
    (hfam : IsRotatingFamily G (Cayley B) C Rot) :
    rotationNormalClosure C Rot = (⊥ : Subgroup G) := by
  refine le_antisymm ?_ bot_le
  show Subgroup.normalClosure {g : G | ∃ c ∈ C, g ∈ Rot c} ≤ ⊥
  refine Subgroup.normalClosure_le_normal ?_
  rintro g ⟨c, hc, hg⟩
  have hbot : Rot c = ⊥ := rot_eq_bot_of_cayley hfam hc
  rw [hbot, Subgroup.mem_bot] at hg
  refine SetLike.mem_coe.mpr ?_
  rw [hg]
  exact Subgroup.one_mem _

/-! ## The data Hull's §5 produces -/

/-- **The rotating family Hull's Theorem 5.1 builds**, on the space DGO cone
off, together with everything DGO's Theorem 5.3 asks of it and the one
comparison with `Γ(G,A)` that the injectivity clause needs.

`L` is the displacement below which the quotient has to be faithful; Hull's
proof prescribes it by taking the relator deep enough, which is why `lt_sep` is
a field rather than a hypothesis of the theorem below.

The space is taken in the same universe as `G`.  Over the manuscript's ground
universe that is no restriction: DGO's cone-off of `Γ(G,A)` along the cosets of
`H` is built from `G` and `ℝ`, both of which are there. -/
structure RotatingData {G : Type u} [Group G] (A : Alphabet G) (w : G)
    (L : ℝ) where
  /-- DGO's cone-off. -/
  Space : Type u
  /-- Its metric. -/
  [metric : PseudoMetricSpace Space]
  /-- The action of `G` on it. -/
  [action : MulAction G Space]
  /-- The basepoint, the image of the identity vertex of `Γ(G,A)`. -/
  base : Space
  /-- Every letter of `A` moves the basepoint by at most one: `Γ(G,A)` sits in
  the cone-off with its edges of length one. -/
  letter_dist : ∀ a ∈ A.carrier, dist base (a • base) ≤ 1
  /-- The hyperbolicity constant of the cone-off. -/
  delta : ℝ
  /-- It is positive. -/
  delta_pos : 0 < delta
  /-- The cone-off is hyperbolic. -/
  hyperbolic : IsHyperbolicSpace delta Space
  /-- **The cone-off is geodesic.**  DGO work in geodesic spaces throughout, and
  `HullSC.DGOQuotientStatementGeodesic` asks for it: without one the very
  rotating condition constrains an annulus that can be empty.  It is why the
  family lives on the geometric realisation `GGT.Point` rather than on
  `Cayley A`, which `HullFillAxisDichotomy.not_isGeodesicSpace_cayley` refutes. -/
  isGeodesic : IsGeodesicSpace Space
  /-- The separation of the family. -/
  sep : ℝ
  /-- DGO's Theorem 5.3 asks for separation above `200 δ`. -/
  sep_ge : 200 * delta ≤ sep
  /-- The apices: one cone point over each coset carrying a rotation. -/
  apices : Set Space
  /-- The rotation subgroups. -/
  rot : Space → Subgroup G
  /-- They form a rotating family. -/
  isRotatingFamily : IsRotatingFamily G Space apices rot
  /-- It is `sep`-separated. -/
  isSeparated : IsSeparated apices sep
  /-- It is very rotating. -/
  isVeryRotating : IsVeryRotating G Space delta apices rot
  /-- The rotations generate the normal closure of the relator: killing the
  family is killing `w`. -/
  rotationNormalClosure_eq :
    rotationNormalClosure apices rot = Subgroup.normalClosure ({w} : Set G)
  /-- The injectivity radius. -/
  injRadius : ℝ
  /-- It exceeds the prescribed displacement. -/
  lt_injRadius : L < injRadius
  /-- **The kernel moves the basepoint, and this is Hull's §5 rather than
  DGO's.**  Every nontrivial element of the subgroup the rotations generate
  moves the basepoint by at least the injectivity radius.

  This was a field of `HullSC.RotatingQuotient` until the clauses of DGO's
  Theorem 5.3 were read against the source: that theorem concludes the free
  splitting and the dichotomy, and the injectivity radius follows from neither
  -- loxodromy is asymptotic and gives no bound at the first power, and the
  splitting is not metric.  So it belongs with the family Hull builds.

  Two things make this the right form.  It is quantified over the **kernel**,
  which is the honest domain: an element outside the kernel may fix the
  basepoint without harm, and in a Cayley graph of `G` no element fixes
  anything, which is the other half of `HullSC.rot_eq_bot_of_cayley`.  And it
  mentions no quotient map, so it is a statement about the family alone; the
  consequence for a given `q` is two lines from `ker_eq`, which is
  `injOn_cayleyBall_of_kernel_moves`.

  It is also the check that the basepoint is not an apex:
  `HullSC.eq_one_of_dist_lt_everywhere` refutes the form quantified over every
  point, a rotation fixing its apex and lying in the kernel. -/
  kernel_moves_base : ∀ g ∈ rotationNormalClosure apices rot, g ≠ 1 →
    injRadius ≤ dist base (g • base)
  /-- **Finite order lifts, with the order preserved, and this is Hull's §5
  rather than DGO's** (issue #50).

  It was a field of `HullSC.RotatingQuotient`, recorded as a second conclusion of
  Theorem 5.3.  It is not one: `GGT/DGORotatingQuotientRefutation.lean` refutes
  the statement that carried it, at a one-point space where the very rotating
  condition is vacuous because its annulus is empty, and where the clause
  amounts to *every finite-order element of every normal quotient of every group
  lifts with its order* -- which `ℤ` modulo the even integers refutes.  Neither
  of DGO's conclusions supplies it either: the model satisfies the dichotomy, and
  `GGT/DGOFreeSplittingOnePoint.lean` proves it satisfies the free splitting
  5.3(a) as well.

  What the clause needs is control of the **stabilisers** of the action, which
  no hypothesis of Theorem 5.3 mentions -- in the model the stabiliser of the
  one point is all of `G`.  At Hull's cone-off they are known: a vertex of
  `Γ(G,A)` has trivial stabiliser and an apex has the elementary closure of the
  relator, whose finite subgroups a torsion-free ambient group makes trivial.
  So the clause belongs here, with the family Hull builds.

  Stated for an arbitrary quotient by the normal closure of the relator, which
  is the form the consumer needs and the form Hull proves; the same shape the
  injectivity radius had before it was made quotient-free. -/
  finiteOrder_lift : ∀ {Q : Type u} [Group Q] (q : G →* Q),
    q.ker = Subgroup.normalClosure ({w} : Set G) →
      ∀ y : Q, IsOfFinOrder y → ∃ g : G, q g = y ∧ orderOf g = orderOf y

namespace RotatingData

instance instMetric {G : Type u} [Group G] {A : Alphabet G} {w : G} {L : ℝ}
    (D : RotatingData A w L) : PseudoMetricSpace D.Space := D.metric

instance instAction {G : Type u} [Group G] {A : Alphabet G} {w : G} {L : ℝ}
    (D : RotatingData A w L) : MulAction G D.Space := D.action

/-- The action on the cone-off is by isometries: it is a field of the rotating
family. -/
theorem isometric {G : Type u} [Group G] {A : Alphabet G} {w : G} {L : ℝ}
    (D : RotatingData A w L) : IsIsometricAction G D.Space :=
  D.isRotatingFamily.isometric

end RotatingData

/-- **The alphabet half of Hull's Theorem 5.1.**  The clauses DGO's Theorem 5.3
cannot state, because `RotatingQuotient` is indexed by an abstract metric space
with a group action and has no alphabet to speak of: the quotient carries a
Hull generating set containing the image of `A`, and the images of the
prescribed suitable subgroups are suitable in it. -/
structure FillingAlphabetData {G : Type u} [Group G] (A : HullGeneratingSet G)
    (N : Subgroup G) {k : ℕ} (S : Fin k → Subgroup G) {Q : Type u} [Group Q]
    (q : G →* Q) where
  /-- Hull's alphabet for the quotient. -/
  hullSet : HullGeneratingSet Q
  /-- It contains the image of Hull's alphabet for `G`. -/
  alphabet_image : ∀ a ∈ A.alphabet.carrier, q a ∈ hullSet.alphabet.carrier
  /-- The image of `N` is suitable. -/
  suitable_map : Suitable hullSet.alphabet (N.map q)
  /-- The image of each prescribed suitable subgroup is suitable. -/
  suitable_map_family : ∀ j : Fin k, Suitable hullSet.alphabet ((S j).map q)

/-- **Hull's §5, with DGO's Theorem 5.3 taken out.**

> Let `G` be acylindrically hyperbolic with Hull's alphabet `A`, let `N` be
> suitable, let `H ≤ N` be hyperbolically embedded with a loxodromic element,
> let `S₁, …, S_k` be suitable and let `R` be a radius.  Then there are
> `ε, μ, ρ` such that for every family `W` satisfying `C(ε, μ, ρ)` over `H` and
> every `v ∈ W`: the conjugates of the relator form a separated very rotating
> family on the cone-off, with separation above `2R` and below the distance from
> the basepoint to the apices, generating the normal
> closure of the relator; and every quotient of `G` by that normal closure
> carries a Hull alphabet containing the image of `A` in which the images of
> `N` and of the `Sⱼ` are suitable.

Both halves are quantified over the *same* parameters, which is what keeps them
from drifting: the alphabet clause is false for an arbitrary quotient by an
arbitrary element -- take the first projection of a product -- so it may not be
stated before the small cancellation condition that pins the relator down. -/
def HullFillingDataStatement : Prop :=
  ∀ {G : Type u} [Group G] (A : HullGeneratingSet G) (N : Subgroup G)
    (E : HypEmbeddedCore A N), Suitable A.alphabet N →
      ∀ {k : ℕ} (S : Fin k → Subgroup G),
        (∀ j : Fin k, Suitable A.alphabet (S j)) → ∀ R : ℕ,
          ∃ (eps rho : ℕ) (mu : ℝ), 0 < mu ∧
            ∀ (W : Set (List (GGT.RelLetter G Unit)))
              (v : List (GGT.RelLetter G Unit)), v ∈ W →
              RelWord.IsSmallCancellation E.rel W eps mu rho →
                Nonempty (RotatingData A.alphabet (GGT.RelLetter.listVal v)
                    (2 * (R : ℝ))) ∧
                  ∀ {Q : Type u} [Group Q] (q : G →* Q), Function.Surjective q →
                    q.ker = Subgroup.normalClosure
                        ({GGT.RelLetter.listVal v} : Set G) →
                      Nonempty (FillingAlphabetData A N S q)

/-! ## Hull's Theorem 5.1, from DGO's Theorem 5.3 -/

/-- **Hull's Theorem 5.1 from Dahmani-Guirardel-Osin's Theorem 5.3 and the
family Hull builds.**

Six of the ten fields of `HullFillingQuotient` come out of `RotatingQuotient`:
the group, the map, its surjectivity and the kernel (through
`RotatingData.rotationNormalClosure_eq`).  **Two more come from the family and
not from the quotient**, both of them clauses that were read off DGO's Theorem
5.3 until they were checked against it: injectivity on the ball, from
`RotatingData.kernel_moves_base` through `injOn_cayleyBall_of_kernel_moves` with
the injectivity radius prescribed above `2R`; and the lifting of finite order,
from `RotatingData.finiteOrder_lift`, which issue #50 moved here after the
statement carrying it was refuted.  The remaining three are the alphabet
clauses, and they are the second conjunct of `HullFillingDataStatement`. -/
theorem hullQuotient_of_fillingData
    (hDGO : DGOQuotientStatementGeodesic.{u, u})
    (hdata : HullFillingDataStatement.{u}) : HullQuotientStatement.{u} := by
  intro G _ A N E hN k S hS R
  obtain ⟨eps, rho, mu, hmu, hgood⟩ := hdata A N E hN S hS R
  refine ⟨eps, rho, mu, hmu, ?_⟩
  intro W v hv hsc
  obtain ⟨⟨D⟩, halph⟩ := hgood W v hv hsc
  obtain ⟨P⟩ := hDGO D.delta D.sep D.apices D.rot D.delta_pos D.sep_ge
    D.hyperbolic D.isGeodesic D.isRotatingFamily D.isSeparated D.isVeryRotating
  have hker : P.q.ker
      = Subgroup.normalClosure ({GGT.RelLetter.listVal v} : Set G) := by
    rw [P.ker_eq, D.rotationNormalClosure_eq]
  obtain ⟨F⟩ := halph P.q P.surjective hker
  have hinj : Set.InjOn P.q (cayleyBall A.alphabet R) := by
    refine injOn_cayleyBall_of_kernel_moves D.isometric A.alphabet D.base
      D.letter_dist P.q (K := rotationNormalClosure D.apices D.rot) P.ker_eq
      (L := D.injRadius) R D.lt_injRadius ?_
    intro g hgmem hg
    exact D.kernel_moves_base g hgmem hg
  exact ⟨{ Q := P.Q
           group := P.group
           q := P.q
           surjective := P.surjective
           ker_eq := hker
           hullSet := F.hullSet
           alphabet_image := F.alphabet_image
           injOn := hinj
           suitable_map := F.suitable_map
           suitable_map_family := F.suitable_map_family
           finiteOrder_lift := D.finiteOrder_lift P.q hker }⟩

/-- **Hull's Theorem 5.1 with the §6 relator**, from DGO's Theorem 5.3, Hull's
§6 and the family of his §5. -/
theorem hullTheorem51_of_fillingData
    (hDGO : DGOQuotientStatementGeodesic.{u, u})
    (hrel : HullRelatorStatement.{u}) (hdata : HullFillingDataStatement.{u}) :
    HullTheorem51Statement.{u} :=
  hullTheorem51_of_relator_of_quotient hrel
    (hullQuotient_of_fillingData hDGO hdata)

/-- **Hull's Theorem 7.1 for one relator**, from the same three, with the
hyperbolically embedded subgroup inside the suitable one. -/
theorem hullOneStep_of_fillingData (hEmb : ExistsHypEmbeddedInSuitable.{u})
    (hDGO : DGOQuotientStatementGeodesic.{u, u})
    (hrel : HullRelatorStatement.{u})
    (hdata : HullFillingDataStatement.{u}) : HullOneStepStatement.{u} :=
  hullOneStep_of_theorem51 hEmb (hullTheorem51_of_fillingData hDGO hrel hdata)

/-- **Hull's Theorem 7.1 in its published injectivity-radius form**, with the
manuscript's kernel datum, on four leaves: DGO's Theorem 5.3, Hull's §5 in the
two halves `ExistsHypEmbeddedInSuitable` and `HullFillingDataStatement`, and
his §6.  `HullCorrectedInputs.smallCancellation_of_ballFormNG` turns it into
the finite-set form the manuscript records. -/
theorem hullBallFormNG_of_fillingData (hEmb : ExistsHypEmbeddedInSuitable.{u})
    (hDGO : DGOQuotientStatementGeodesic.{u, u})
    (hrel : HullRelatorStatement.{u})
    (hdata : HullFillingDataStatement.{u}) :
    Manuscript.NonMF.HullCorrectedInputs.HullBallFormStatementNG.{u} :=
  hullBallFormNG_of_oneStep (hullOneStep_of_fillingData hEmb hDGO hrel hdata)

end HullSC
end GroupApproximation
