# Auditing Hull's small-cancellation theorem against baseline rows 3–4

**Date:** 2026-08-16.
**Question audited:** do the published acylindrical small-cancellation results
supply `DefectRoutingData`, the undischarged package behind rows 3 and 4 of
`notes/NON_MF_UNCONDITIONAL_BASELINE.txt`?

**Sources read in full, not from memory.**

* M. Hull, *Small cancellation in acylindrically hyperbolic groups*, Groups
  Geom. Dyn. **10** (2016) 1077–1119, DOI 10.4171/GGD/377 (published version;
  arXiv:1308.4345v2).  Statements below are quoted from the published
  pagination.
* D. Osin, *Groups acting acylindrically on hyperbolic spaces* (survey,
  arXiv:1712.00814), for the classification of acylindrical actions; the
  classification itself is proved in Osin, *Acylindrically hyperbolic groups*,
  Trans. AMS **368** (2016).

## 0. Verdict

The routing does **not** need the strengthening of Hull that the manuscript's
Question 2 describes.  Six of the seven fields of `DefectRoutingData` come out
of Hull's Theorem 7.1 as published, including finite presentation, which is the
field one would expect to be lost.  What is missing is a single hypothesis of a
different kind, and it is missing for a reason that a published theorem
explains rather than for want of effort:

> the routing needs a **suitable subgroup inside the compression defect**, and
> by Hull's Lemma 5.8 that reduces to **one infinite-order element `h` of the
> defect whose cyclic subgroup `⟨h⟩` is hyperbolically embedded in the ambient
> group** (with `⟨h⟩` a proper subgroup of the defect).

Nothing else is open.  Rows 3–4 should therefore be described as blocked on that
one certificate, not on a common-quotient technique that does not yet exist.

## 1. What the target package requires

`DefectRoutingData` (`GroupApproximation/Sofic/TorsionFreeFullMFRadical.lean`)
carries, for a `FournierFacioDefectData D` over a skeleton `E`:

| # | Field | Requirement |
|---|---|---|
| 1 | `quotient`, `quotient_surjective` | an epimorphism `E ↠ Q` |
| 2 | `finitelyPresented` | `Q` finitely presented |
| 3 | `kazhdan` | `Q` has property (T) |
| 4 | `defect_surjective` | `q(N_comp) = Q` |
| 5 | `protected_ne_one` | `q(s) ≠ 1` |
| 6 | `generatorOne/Two`, `generates` | `Q` two-generated |
| 7 | `torsionFree` | `Q` torsion-free (power form) |

## 2. What Hull's Theorem 7.1 gives

> **Definition 1.4.** Given `G ∈ 𝒜ℋ`, a generating set `𝒜` of `G` and a
> subgroup `S ≤ G`, we say `S` is *suitable with respect to `𝒜`* if (1)
> `Γ(G,𝒜)` is hyperbolic and the action of `G` on `Γ(G,𝒜)` is acylindrical;
> (2) the induced action of `S` on `Γ(G,𝒜)` is non-elementary; (3) `S` does
> not normalize any finite subgroup of `G`.

> **Theorem 7.1** (= Theorem 1.5).  Suppose `G ∈ 𝒜ℋ` and `S ≤ G` is suitable
> with respect to `𝒜`.  Then for any `{t₁,…,t_m} ⊂ G` and `N ∈ ℕ` there exist a
> group `Ḡ` and a surjective homomorphism `γ : G → Ḡ` with
> (a) `Ḡ ∈ 𝒜ℋ`; (b) `γ|_{B_𝒜(N)}` injective; (c) `γ(tᵢ) ∈ γ(S)`;
> (d) `γ(S)` suitable with respect to some `𝒜' ⊇ γ(𝒜)`; (e) every element of
> `Ḡ` of order `n` is the image of an element of `G` of order `n`.

Field by field:

* **1** — Theorem 7.1's `γ`.
* **4 and 6 are the same clause.**  The remark after Remark 7.2 (p. 1110):
  *"if `G` is finitely generated, we can choose `t₁,…,t_m` to be a generating
  set of `G`, and we get that `γ|_S` is surjective."*  So `γ(S) = Ḡ`.  Taking
  `S ≤ N_comp` gives field 4.  Taking `S = ⟨h₁,h₂⟩` — legitimate by Corollary
  5.7, which produces non-commensurable loxodromic `h₁,…,h_k ∈ S` with
  `E_G(hᵢ) = ⟨hᵢ⟩` — gives field 6 simultaneously, since then
  `Ḡ = γ(S) = ⟨γ(h₁),γ(h₂)⟩`.  This is exactly how Hull gets two-generated
  common quotients in the proof of Corollary 7.4.
* **5** — same remark: *"we can always choose `N` such that `B_𝒜(N)` contains
  any given finite subset of `G`"*, so choose `N` with `s ∈ B_𝒜(N)` and apply
  (b).
* **7** — clause (e): a torsion-free `G` gives a torsion-free `Ḡ`.
* **2 — available, and this is the surprise.**  The proof of Theorem 7.1 sets
  `Ḡ = G/⟨⟨ℛ⟩⟩` where `ℛ` is the set of all cyclic shifts of `W^{±1}` for a
  **single** word `W ≡ t⁻¹h₁^{m₁}h₂^{l₁}…h₁^{m_n}h₂^{l_n}` (the proof opens
  *"Clearly it suffices to prove the theorem with `m = 1`, and the general
  statement follows by induction"*).  So each application of Theorem 7.1 adds
  finitely many relators, and `m` applications add finitely many; a finitely
  presented `G` therefore has a finitely presented `Ḡ`.
* **3** — property (T) has to come from a second group.  Hull's Corollary 7.4
  (= Corollary 1.6) produces a common quotient of `G₁` and `G₂`, and property
  (T) then descends from a Kazhdan `G₁` (this is how Corollary 1.7, *"every
  countable `G ∈ 𝒜ℋ` has an infinite quotient with Property (T)"*, is proved).
  A torsion-free finitely presented Kazhdan `G₁ ∈ 𝒜ℋ` exists: a torsion-free
  uniform lattice in `Sp(n,1)`, `n ≥ 2`.

### 2.1 Finite presentation survives only on the Theorem 7.1 route

Corollary 7.3 must **not** be used.  Its proof builds
`Q = G₀/⋃_{i≥1} ker η_i` as a direct limit of infinitely many small-cancellation
quotients, which destroys finite presentation.  The general case of Corollary
7.4 routes through Corollary 7.3 and inherits that.  The escape is the last
sentence of Corollary 7.4's proof: *"Now if `G₂` is finitely generated, then we
can apply Theorem 7.1 to `F'` with a generating set of `F'` as a finite set of
elements to get `Q` such that the image of `G₁` maps onto `Q`."*  Two
applications of Theorem 7.1, no limit — so with both inputs finitely presented,
the common quotient is finitely presented.  Surjectivity of the defect is
preserved by the second application, because a surjection composed with a
quotient map is a surjection.

## 3. The one thing that is missing

Every route above is an application of Theorem 7.1, whose hypotheses are
`G ∈ 𝒜ℋ` **and** a suitable `S`.  The suitability of the defect is the
undischarged certificate.  Two published statements reduce it:

> **Lemma 5.5.**  Let `S` be a non-elementary subgroup of `G`.  Then `K_G(S)`
> is the maximal finite subgroup of `G` normalized by `S`.

So over a torsion-free ambient, condition (3) of Definition 1.4 is automatic
and suitability is exactly non-elementarity of the induced action.

> **Lemma 5.8.**  If `S` contains an infinite order element `h` such that
> `⟨h⟩` is a proper subgroup of `S` and `⟨h⟩ ↪_h (G,X)`, then `S` is suitable
> with respect to `𝒜` for some `𝒜 ⊇ X`.

That is the cheapest sufficient condition, and it is what rows 3–4 now reduce
to: **one infinite-order `h ∈ N_comp` with `⟨h⟩` hyperbolically embedded in the
skeleton and `⟨h⟩ ⊊ N_comp`.**  (Lemma 5.9 is the alternative: if the defect is
itself in `𝒜ℋ` and hyperbolically embedded in the ambient, suitability
transfers.)

### 3.1 Why the ascending HNN skeleton does not certify itself

The skeleton `E' = ⟨Γ, t | tΓt⁻¹ = α(Γ)⟩` cannot be shown acylindrically
hyperbolic by its own Bass–Serre action, and this is not a gap in the argument
but a theorem:

> **Theorem 2.10** (Osin's survey, proved in *Acylindrically hyperbolic
> groups*).  Let `G` act acylindrically on a hyperbolic space.  Then exactly one
> of: (a) elliptic; (b) lineal, in which case `G` is virtually cyclic; (c)
> general type.  *"Theorem 2.10 rules out parabolic and quasi-parabolic
> actions."*

In the Bass–Serre tree of an ascending HNN extension one of the two edge
inclusions is onto, so every vertex has exactly one edge in the `α`-direction
and the action fixes the end of the telescope.  With `[Γ : α(Γ)] = ∞` the action
is non-elementary, hence quasi-parabolic, hence not acylindrical.  So that tree
is the wrong space; whether `E'` lies in `𝒜ℋ` for some other action is not
settled by these sources.

Nor does Hull's own HNN section help directly:

> **Proposition 6.2.**  Suppose `S` is a suitable subgroup of a group
> `G ∈ 𝒜ℋ`.  Then for any isomorphic **cyclic** subgroups `A` and `B` of `G`,
> the corresponding HNN-extension `G *_{A^t = B}` belongs to `𝒜ℋ` and contains
> `S` as a suitable subgroup.

Section 6 is about HNN extensions over cyclic subgroups (Lemma 6.1, Proposition
6.2).  The compression datum needs the associated subgroups to be the whole
Kazhdan base, which is not cyclic, so Proposition 6.2 does not apply to `E'`.

## 4. Consequences for the repository

1. The manuscript's Question 2 mis-describes the intended route.  Prescribing
   the target elements inside a chosen subgroup is not a strengthening anyone
   needs to prove: Theorem 7.1(c) prescribes an arbitrary suitable `S`, and the
   remark after Remark 7.2 upgrades that to `γ(S) = Ḡ` for a finitely generated
   ambient.  The sentence is corrected in the same commit as this note.
2. Rows 3–4 of the baseline stay, with a sharper reason: the missing object is a
   hyperbolically embedded cyclic subgroup inside the compression defect (or,
   failing that, an acylindrically hyperbolic action of the skeleton), not a new
   small-cancellation theorem.
3. If that certificate is ever produced, the Lean side needs no new analytic
   input: `DefectRoutingData` is exactly the interface, and fields 1, 2, 4, 5,
   6, 7 are then discharged by one application of Theorem 7.1 to
   `B * E'` and a second to its output, with `B` a torsion-free finitely
   presented Kazhdan uniform lattice supplying field 3.

## 5. What this note does not claim

It does not claim `E' ∈ 𝒜ℋ`, and it does not claim `E' ∉ 𝒜ℋ`: only that the
Bass–Serre action cannot witness it and that Hull's HNN result covers a
different case.  It does not construct `h`.  It does not formalize any of the
quoted statements; they are literature inputs, quoted at the point of use, and
the two Lean endpoints behind rows 3–4 remain conditional on the data packages
they take as arguments.

---

## Addendum, 2026-08-19: the object now exists in Lean, minus its one geometric clause

`GroupApproximation/Sofic/HullSuitableDefectSubgroup.lean` builds the object §3
says is missing, and proves unconditionally every clause of it that is group
theory.  Nothing about acylindrical hyperbolicity or hyperbolic embedding is
encoded, as an opaque predicate or otherwise; §5's disclaimers stand unchanged.

What is now machine-checked:

* **Definition 1.4(3) is discharged for every subgroup at once.**
  `eq_bot_of_finite` proves that a torsion-free group has no nontrivial finite
  subgroup, in the ordinary power form the routing uses (the repository already
  had it only for Mathlib's stronger `IsMulTorsionFree`), and
  `normalizesNoNontrivialFinite_of_torsionFree` reads that as clause (3).  This
  is the remark after Lemma 5.5 quoted in §3, proved rather than cited.
* **Lemma 5.8's non-geometric hypotheses.**  `IsAlgebraicallySuitable` records
  them: an infinite-order `h ∈ S` with `⟨h⟩ ⊊ S`.  Infinite order is free over a
  torsion-free ambient; properness is *earned*, by
  `zpowers_lt_of_noncommuting` -- a cyclic subgroup is commutative, so it cannot
  contain the non-commuting pair the Fournier--Facio datum already carries in
  its `witness_commutator_ne_one` field.
* **The object.**  `SuitableDefectSubgroup` is a two-generated subgroup of the
  compression defect satisfying those clauses;
  `SuitableDefectSubgroup.ofNoncommutingPair` constructs one from a
  non-commuting pair in the defect of *any* compression core over a torsion-free
  ambient, and `FournierFacioDefectData.hullSuitableDefectSubgroup` is the
  instance at the intended datum, generated by `s` and `ι(r)`.
* **Osin's route as well.**  `IsSNormal` records `s`-normality and
  `defectNormal_isSNormal` proves the compression defect has it -- the defect is
  normal by construction and infinite by `defectNormal_infinite` -- so the
  hypothesis of Lemma 7.1 is verified, its conclusion still cited to nobody.
* **§2's "fields 4 and 6 are the same clause", checked.**
  `SuitableDefectSubgroup.defect_map_eq_top` and `generates_map` both come from
  the single hypothesis `S.carrier.map q = ⊤`, and
  `FournierFacioDefectData.routingDataOfSuitableSurjection` assembles a complete
  `OrderPreservingRoutingData` from it together with finite presentation,
  property `(T)` and order preservation.

So the reason §4.2 gives for rows 3--4 sharpens once more.  What is missing is
no longer "a suitable subgroup inside the compression defect": the subgroup is
built, two-generated, inside the defect, and every algebraic clause of
suitability holds of it.  What is missing is one clause *about* that subgroup --
that `⟨s⟩` is hyperbolically embedded in the skeleton, equivalently that the
subgroup acts non-elementarily -- and, downstream of it, the single equation
`S.carrier.map q = ⊤`.  Everything on the algebraic side of the routing is
discharged.

The prohibition of `notes/TORSION_FREE_HULL_ROUTE.md` is untouched by this: the
module closes nothing through Hull's theorem, states the remaining clause as a
hypothesis at its one consuming site, and is not cited by the manuscript.

### Addendum, later the same day: the object with no hypotheses at all

The module above still took one hypothesis, `IsPowerTorsionFree E`, and that
hypothesis cannot be proved away: over an ambient group with torsion,
Definition 1.4(3) is **false**, so any theorem about a general compression datum
must assume it.  The only way to discharge it is to stop quantifying over data
and build a group.

`GroupApproximation/Sofic/ExplicitSuitableDefect.lean` does that.  It constructs

    Coeff = free group of rank two,   Lamp = ℤ → Coeff,   Skeleton = Lamp ⋊ ℤ

with the integers acting by translating sites, and inside it the compression
pattern in its barest form: `iota` erases the negative sites, so its image is
the configurations supported on `[0,∞)`; the stable letter translates by one,
compressing that image strictly into itself; the root is a single lamp at site
`-1`, invisible to the compressed copy, so it centralizes it; transporting the
root moves it to site `0`, which the compressed copy sees, so the defect is
nontrivial.  Every one of those is an equation between explicit functions on
`ℤ`, proved by splitting on the site.  The result is an inhabitant of the
repository's own `ConcreteCompressionSource.CompressionSourceData`, and
`CompressionSourceData.defectNormal` (added in the same module) is proved to be
`KazhdanCompressionCore.defectNormal` whenever the source has property `(T)`, so
nothing about the notion of defect has been weakened by dropping the Kazhdan
field.

Three things then come out unconditionally:

* `skeleton_isPowerTorsionFree` --- Mathlib proves free groups are torsion-free
  (`IsMulTorsionFree (FreeGroup α)`, in `FreeGroup/CyclicallyReduced.lean`), that
  passes to `ℤ → Coeff` pointwise, and a semidirect product of a torsion-free
  group by `ℤ` is torsion-free because the `ℤ`-coordinate of a torsion element
  vanishes first.
* `defect_noncommuting` --- the marked commutators `[d, ι p]` are single lamps at
  site `0` carrying `[x, p 0]`, so two of them commute exactly when their
  coefficients do.  Taking `p 0 = y` and `p 0 = y²` reduces the question to
  whether `[x,y]` and `[x,y²]` commute in a free group of rank two.  They do
  not, and `FreeGroup` has decidable equality, so that is `decide` --- a kernel
  computation on reduced words.
* `explicitSuitableDefectSubgroup` --- a closed term, no arguments, of the type
  `SuitableDefectSubgroup explicitDatum.defectNormal`.

**Why the coefficients have to be free.**  The defect lands in the lamp factor
and is coordinatewise the normal closure of `[x, Coeff]`, so it is non-abelian
exactly when that is.  Every soluble coefficient group fails: lamps over `ℤ`,
over a Klein-bottle group, over any iterated extension with abelian kernels.
This is worth recording because the cheap-looking constructions are exactly the
ones that give an abelian defect and no object at all.

**What this settles and what it does not.**  It settles that the algebraic half
of Hull's hypothesis is inhabited without assumptions --- the object exists, it
is not vacuous, and no clause of it needs a hypothesis anyone has to discharge
later.  It does not touch rows 3--4: `Skeleton` has no Kazhdan source and is not
acylindrically hyperbolic, so Hull's theorem does not apply to it.  The
Fournier--Facio instance keeps `IsPowerTorsionFree E` in its type, and that is
the honest statement, because torsion-freeness of *that* group is a property of a
construction this library does not build.

### Addendum, third pass: the object in the ascending HNN skeleton, and what a datum forces

Two further things landed, both unconditional.

**1. The object now lives in the manuscript's own skeleton shape.** The lamp
group of the previous addendum is a semidirect product; `E'` is an ascending
HNN extension. `GroupApproximation/GroupTheory/HNNBrittonCyclic.lean` already
proves `isPowerTorsionFree_sourceGroup` --- an HNN extension over a torsion-free
base is torsion-free --- outright, from Britton's lemma, with no input. So
instantiating `ConcreteCompressionSource`'s own generic affine source at
`Γ = ℕ → FreeGroup (Fin 2)` with `α` the shift gives a compression datum over a
torsion-free ascending HNN extension, with no hypotheses anywhere.

The one thing the HNN group does not hand over cheaply is the non-commuting
pair: reading it off directly means a reduced word of sixteen syllables with
fifteen chain conditions. It is not needed. `psi`, built by
`HNNExtension.lift` from the base map "source copy to the nonnegative sites,
central direction to site `-1`" and the lamp group's stable letter, carries the
two marked commutators of the HNN datum exactly onto the two lamp commutators
already certified, so a pair whose image does not commute does not commute.
`hnnSuitableDefectSubgroup` is the resulting closed term.

**2. The interface is not satisfiable trivially.**
`CompressionSourceData.not_conjugation_surjective`: conjugation by the stable
letter is never onto the source copy, because if it were then
`commutesAfterCompression` would make the transported root centralize the whole
copy and the marked commutator would be trivial. Hence
`CompressionSourceData.infinite_source`: on a finite source the conjugation
self-map of the copy would be injective and therefore onto, which the first
theorem forbids. Transported along `ofFournierFacio`, this gives
`FournierFacioDefectData.infinite_source`: **the property-`(T)` source of a
Fournier--Facio datum is necessarily infinite.** No finite Kazhdan group can
inhabit the interface, so the datum is not vacuously satisfiable, and the
compression is always strictly proper.

**What is still not settled, and why it is not a formalization gap.** Rows 3--4
remain exactly where the audit put them. Hull's theorem needs an ambient in
`AH`, and §3.1 shows the ascending HNN skeleton's Bass--Serre action is
quasi-parabolic and therefore not acylindrical, so its membership in `AH` is not
settled by these sources in either direction. That is open mathematics about the
group, not missing Lean. Everything on the algebraic side --- the object, its
clauses, the ambient, the datum, the non-degeneracy --- is now proved with no
assumptions and no inputs.

### Addendum, fourth pass: the geometric clause is stated, and what it forbids is proved

The three addenda above all ended at the same sentence: the geometric clause of
Hull's Definition 1.4 is "not stateable in this library". That was true of
`Sofic.TorsionFreeFullMFRadical`'s vocabulary and it was not true of Lean.
Acylindricity, hyperbolicity and non-elementarity are ordinary ∀∃-statements
about a metric space and an action, and Mathlib has metric spaces.
`GroupApproximation/Sofic/HullSuitabilityGeometry.lean` writes them down --- as
definitions with bodies, not as opaque predicates:

* `gromovProduct`, `IsHyperbolicSpace δ X` (the four-point condition);
* `IsAcylindrical G X` (Osin's condition, verbatim);
* `IsLoxodromic g x`, `Independent g h x` (Gromov products of the two
  power-orbits bounded, powers over `ℤ` so that `g` and `g⁻¹` are correctly
  dependent), `ActsNonElementarily S x`;
* `IsSuitable δ S x` --- **Hull's Definition 1.4, all three clauses.**

**What the clause is worth, proved.** `IsSuitable.toIsAlgebraicallySuitable`:
a suitable subgroup is algebraically suitable. So `IsAlgebraicallySuitable` is
not a convenient weakening chosen to make the object provable; it is exactly
what Definition 1.4 says once the space is forgotten, and the unconditional
object carries everything Hull's hypothesis carries except the geometry itself.
The proof runs through `not_isOfFinOrder_of_isLoxodromic` and
`notMem_zpowers_of_independent`.

**What the clause forbids, proved.** `isOfFinOrder_of_commutes_of_bounded`: an
element with bounded orbit commuting with two independent loxodromics has finite
order --- the elementary half of "a loxodromic in an acylindrical action has a
virtually cyclic centralizer", proved here from the definitions. Over a
torsion-free ambient it is trivial (`eq_one_of_commutes_of_bounded`), and hence
`not_isSuitable_of_centralizing`: **a subgroup with a nontrivial centralizing
element of bounded orbit is never suitable.**

That has a direct consequence for the compression pattern, and it explains the
shape of this whole lane. The compressed copy `u ι(Γ) u⁻¹` is centralized by the
transported root, which the datum's own `witness_commutator_ne_one` makes
nontrivial. So `CompressionSourceData.not_isSuitable_compressedCopy`: **the
compressed copy is never Hull's suitable subgroup.** The search has to go to the
defect --- which is where the audit put it and where
`Sofic.HullSuitableDefectSubgroup` builds it.

**And the cheat is closed.** On a bounded space every action is acylindrical and
every space is hyperbolic, so clauses (1) and (3) alone are satisfiable
trivially; `not_actsNonElementarily_of_bounded` shows clause (2) fails outright
when the orbit is bounded.

**What is left.** `HasSuitableGeometry N` --- some hyperbolic space carries an
acylindrical action of the ambient in which `N` is non-elementary --- with
`isAlgebraicallySuitable_of_hasSuitableGeometry` recording that this is the only
implication still needed. Its truth value for the manuscript's skeleton is not
known to the sources this audit read: §3.1 proves the Bass--Serre action is
quasi-parabolic and therefore not acylindrical, and whether the skeleton is
acylindrically hyperbolic for some *other* action is claimed by nobody in either
direction. The theorems of this pass say why that is hard rather than
accidental: a compression pattern needs a nontrivial centralizing element, and
suitability forbids one of bounded orbit. That is a fact about the group, not
about the formalization.

### Addendum, fifth pass: the compressed direction is settled

The fourth pass left `HasSuitableGeometry N` as the one open statement and gave
a reason it is hard: a compression pattern needs a nontrivial centralizing
element, and suitability forbids one of bounded orbit. This pass settles half of
that, unconditionally, and identifies what the other half would need.

`HullSuitabilityGeometry` now carries the quantitative notion of loxodromy ---
`IsStronglyLoxodromic`, the orbit map bounded below by a linear function, which
is what the literature means and which implies the weak `IsLoxodromic` --- and
proves:

> **`not_isStronglyLoxodromic_of_compression`.** If `t p t⁻¹ = p ^ k` with
> `2 ≤ k`, then `p` is not strongly loxodromic, for *any* isometric action on
> *any* metric space.

The proof is elementary and needs neither hyperbolicity nor acylindricity.
`conj_pow_eq` iterates the relation to `t ^ j p t ^ (-j) = p ^ (k ^ j)`;
`dist_conj_le` bounds the displacement of a `t ^ j`-conjugate by
`2 j · d(x, t x) + d(x, p x)`, using only `dist_pow_le` and the triangle
inequality. So the orbit of `p` grows at most **linearly in `j`** along the
subsequence `k ^ j`, which is exponentially sparse, and no linear lower bound in
`n` survives.

**What this settles.** The compressed direction of a compression pattern is
never genuinely loxodromic. When the source copy is cyclic the compression
relation is exactly Baumslag--Solitar --- and it is always *proper*, by
`CompressionSourceData.not_conjugation_surjective` from the third pass --- so the
compressed copy contains no strong loxodromic at all. Together with
`not_isSuitable_compressedCopy` this closes the compressed copy completely: it is
not suitable, and it does not even contain the elements suitability would need.

**What it does not settle.** The defect. Its elements are not powers of the
compressed generator, so the Baumslag--Solitar obstruction does not reach them,
and `HasSuitableGeometry N` for the defect remains open. Refuting it for the
explicit ambients of `Sofic.ExplicitSuitableDefect` would need Osin's
elementary-closure theorem --- that an element commuting with a loxodromic lies
in its virtually cyclic elementary closure --- which is absent from the pinned
Mathlib and is a substantial formalization in its own right. Proving it would
need Hull's common quotient. Neither is available, and for the manuscript's own
skeleton the statement's truth value is claimed by no source in either
direction.

### Addendum, sixth pass: the open predicate is retired

`HasSuitableGeometry` --- the `def … : Prop` added in the fourth pass to name
the geometric half of Question 2 --- has been deleted from
`GroupApproximation/Sofic/HullSuitabilityGeometry.lean`.

It was the wrong shape for this repository. No corpus theorem concludes it, and
`scripts/check_non_mf_unconditional.py`'s `open-predicate` detector is exactly
the test for a corpus `def … : Prop` that nothing concludes; §3a above names
that shape and lists the literature stand-ins that wear it. Writing a
placeholder for an open problem into the library under the name of a definition
is what the audit exists to prevent, and the fourth pass did it. Nothing was
lost by the deletion: the predicate had no mathematical role --- no result was
conditional on it, and its one theorem
(`isAlgebraicallySuitable_of_hasSuitableGeometry`) was subsumed by
`IsSuitable.toIsAlgebraicallySuitable`, which is retained.

The open question itself is unchanged and is recorded here, in these addenda,
which is where open questions belong. It is: does some hyperbolic space carry an
acylindrical action of the ambient in which the compression defect is
non-elementary? Proving it needs Hull's common quotient. Refuting it, even only
for the explicit ambients of `Sofic.ExplicitSuitableDefect`, needs Osin's
elementary-closure theorem --- that an element commuting with a loxodromic lies
in its virtually cyclic elementary closure --- which the pinned Mathlib does not
have and which is a substantial formalization on its own. The naive elementary
argument fails at a identifiable point: an element `h` commuting with a
loxodromic `g` moves the `g`-orbit by a bounded amount, but the induction
bounding the distance from `h^m x` to that orbit accumulates linearly in `m`
rather than staying bounded, and it is exactly hyperbolicity that repairs it.

**State of the three modules after this pass.** 1943 lines, no `sorry`, no
declared axiom, all root-imported, every declaration either a definition with
proved consequences or a theorem with a closed proof. The objects ---
`explicitSuitableDefectSubgroup` and `hnnSuitableDefectSubgroup` --- are closed
terms taking no arguments. Nothing in them is conditional on the missing
geometry.

### Addendum, seventh pass: the constraint reaches the object

The fifth pass proved that a subgroup with a nontrivial centralizing element of
*bounded orbit* is never suitable, and left it general. It now reaches the
explicit compression defect, unconditionally.

**The defect is finitely supported.** `support`, `support_mul`, `support_inv`,
`support_conj`, `support_shift` and `finSupp` --- the subgroup of the skeleton
consisting of lamp configurations of finite support, proved normal by computing
conjugation in the semidirect product --- give
`defectNormal_le_finSupp`. Each marked commutator is a single lamp at site `0`,
so its support is a singleton, and the normal closure of finitely supported
elements is finitely supported because conjugation only translates and relabels
supports.

**Hence every pair in the defect is centralized.** `exists_commuting_ne_one`:
given any two elements of the defect, their supports are finite, so some site is
free of both, and the lamp there is a nontrivial element commuting with each.

**So the gap is now concrete.** `unbounded_of_isSuitable`: if the explicit
compression defect were suitable for some action, the lamp that always commutes
with the two witnessing loxodromics would have to have an **unbounded orbit**.
A suitable geometry for this defect is therefore not merely unproved --- it must
push every free-site lamp arbitrarily far from the basepoint.

**And the reusable core is exposed.** `HullGeometry.finite_commuting_ball`: under
an acylindrical action with two independent loxodromics, only finitely many
elements commuting with both lie in any ball. An element commuting with `g`
moves every point of the `g`-orbit by exactly its own displacement, so
acylindricity applied to two far-apart orbit points confines the whole common
centralizer's `ε`-ball. This is the properness statement Osin's
elementary-closure theorem starts from, and it is now available.

**What still separates this from a refutation.** The free-site lamps generate a
free abelian group of infinite rank inside the common centralizer, and
`finite_commuting_ball` says that group acts metrically properly. Refuting
suitability means showing an acylindrical action on a hyperbolic space admits no
such subgroup in the centralizer of a loxodromic --- which is Osin's theorem that
the centralizer is virtually cyclic. Its proof needs quasi-geodesic stability
(the Morse lemma) and the translation-length homomorphism, neither of which the
pinned Mathlib has. That is the next piece of real work, and it is now the only
one: everything on this side of it is proved.

### Addendum, eighth pass: translation length

The first component of the elementary-closure machinery is in.
`HullGeometry.stableTranslation g x` is the infimum of `d(x, gⁿ x) / n` over
positive `n` --- the Fekete limit of that sequence, taken as an infimum so that
no subadditivity argument is needed for the two facts that matter:

* `mul_le_dist_pow` --- the translation length bounds the orbit from below;
* `isStronglyLoxodromic_iff_pos` --- **an element is genuinely loxodromic
  exactly when its translation length is positive.**

Together with the fifth pass this gives
`stableTranslation_eq_zero_of_compression`: **a compressed element has
translation length zero.** That is the sharp form of "the compressed direction
is never loxodromic", and it is the form Osin's argument consumes.

Also proved: `isLoxodromic_of_isLoxodromic`, that loxodromy does not depend on
the basepoint, and `finite_commuting_ball` from the seventh pass, the properness
of a common centralizer.

**What is left of the elementary-closure theorem.** Two components, both
substantial and neither present in the pinned Mathlib:

1. *Quasi-geodesic stability* (the Morse lemma) --- needed to show that an
   element commuting with a loxodromic translates *along* its axis rather than
   transversally. Every attempt to get this from the definitions directly
   stalls at the same point: the induction bounding the distance from `hᵐ x` to
   the `g`-orbit accumulates linearly in `m` instead of staying bounded, and
   hyperbolicity is exactly what repairs it.
2. *The translation homomorphism* `C(g) → ℝ`, whose image is discrete and whose
   kernel is finite --- both by acylindricity, the second being
   `finite_commuting_ball` above.

With those two, `C(g)` is virtually cyclic, an infinite-rank free abelian
subgroup of it is impossible, and the seventh pass's free-site lamps refute
suitability for the explicit defect. Neither component is a lemma; each is a
project, and neither is attempted here.
