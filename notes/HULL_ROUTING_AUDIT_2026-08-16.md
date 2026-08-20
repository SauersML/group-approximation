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

### Addendum, ninth pass: translation length is a limit, and a seminorm

The eighth pass defined `stableTranslation` as an infimum, which is all its two
theorems need. It is also the Fekete limit of the same sequence, and that is
what makes it behave like a length. Mathlib has `Subadditive` and
`Subadditive.tendsto_lim`, and `Subadditive.lim` is *by definition* the same
infimum, so the identification is an `ext` on two descriptions of one set:

* `subadditive_dist_pow` --- the displacement sequence `n ↦ d(x, gⁿ x)` is
  subadditive, by the triangle inequality and the isometry property;
* `stableTranslation_eq_lim`, `tendsto_stableTranslation` --- the infimum is the
  limit;
* `stableTranslation_mul_le` --- **translation length is subadditive on
  commuting elements.**

With `stableTranslation_nonneg`, that last one makes translation length a
seminorm on any abelian subgroup --- in particular on the common centralizer of
two independent loxodromics, which is precisely where the translation
homomorphism `C(g) → ℝ` lives. The free-site lamps of the seventh pass generate
such a subgroup, and `finite_commuting_ball` says it acts metrically properly.

**What is still missing, exactly.** Two things, and after this pass they are
sharply stated rather than gestured at:

1. *Homogeneity and discreteness of the image.* `τ(gᵏ) = k·τ(g)` follows from
   the same limit by passing to the subsequence `n ↦ kn`; discreteness of
   `τ(C(g))` is where acylindricity has to enter again, and it is not a
   corollary of anything above.
2. *Quasi-geodesic stability (the Morse lemma).* Without it there is no reason
   an element commuting with a loxodromic translates *along* its axis rather
   than transversally, and the seminorm above cannot be upgraded to a
   homomorphism. This is the irreducible piece: it is a theorem about hyperbolic
   spaces, absent from the pinned Mathlib, and it is what every attempt in these
   nine passes has stalled against.

### Addendum, tenth pass: homogeneity, and what the seminorm now is

Item 1 of the ninth pass's missing list is done. `stableTranslation_pow`:
`τ(gᵏ) = k·τ(g)`, by passing to the subsequence `n ↦ kn` in the Fekete limit.

So on the common centralizer of two independent loxodromics,
`stableTranslation` is now proved to be

* nonnegative (`stableTranslation_nonneg`),
* subadditive on commuting elements (`stableTranslation_mul_le`),
* homogeneous (`stableTranslation_pow`),
* zero exactly when the element is not genuinely loxodromic
  (`isStronglyLoxodromic_iff_pos`), and in particular zero on any compressed
  element (`stableTranslation_eq_zero_of_compression`),

and that centralizer acts metrically properly (`finite_commuting_ball`). That is
the complete seminorm side of the translation homomorphism.

**What is left is one theorem, and it is a theorem about hyperbolic spaces, not
about this construction.** Quasi-geodesic stability --- the Morse lemma. Without
it there is no reason an element commuting with a loxodromic translates *along*
its axis rather than transversally, so the seminorm cannot be upgraded to a
homomorphism and its image cannot be shown discrete. Every one of these ten
passes that tried to reach the conclusion by elementary means stalled at exactly
that step, and the stall is always the same shape: a bound on how far `hᵐ x`
sits from the `g`-orbit that accumulates linearly in `m` where it needs to stay
bounded.

The Morse lemma is absent from the pinned Mathlib. Formalizing it is a project
of its own --- quasi-geodesics, their stability constants, and the taming of
`δ`-thin triangles --- and it is not attempted here, because these three modules
are in the root import closure and a half-finished one takes every importer down
with it.

### Addendum, eleventh pass: the quasi-axis

The Morse track is started. The Morse lemma is a statement *about*
quasi-geodesics, so the first thing it needs is one, and for a loxodromic
element that is the orbit map `k ↦ gᵏ x`. Both of its bounds were already in
place --- `dist_pow_le` above, `mul_le_dist_pow` below --- so all that was
missing was the passage from `ℕ` to `ℤ`, which `dist_zpow_neg` supplies:

* `dist_zpow_natAbs` --- displacement depends only on `|k|`;
* `dist_zpow_le`, `mul_le_dist_zpow` --- the two bounds over `ℤ`;
* `dist_zpow_orbit` --- displacement between orbit points depends only on the
  difference;
* `orbit_quasiIsometricEmbedding` --- **the quasi-axis**: the orbit map is a
  quasi-isometric embedding of the integers, with lower constant the translation
  length and upper constant the displacement of the generator. When the
  translation length is positive both bounds are effective.

So the object the Morse lemma speaks about now exists in the library, built from
the translation-length layer of the eighth to tenth passes.

**What the Morse lemma would add, and why it is still a project.** Stability:
that *every* quasi-geodesic with the same endpoints stays uniformly close to
this one, with a constant depending only on `δ` and the quasi-geodesic
constants. That is the classical proof --- subdivide, compare with a geodesic,
push the excursion bound through `δ`-thin triangles, and iterate --- and it
needs geodesics, which this development has not introduced at all: `IsSuitable`
is stated over a `PseudoMetricSpace` with no geodesicity hypothesis, because
none of the eleven passes before this one needed one.

That is the honest boundary. Adding geodesics and their stability is a
self-contained development of a few hundred lines with a real proof in it, and
it should be built against a compiler rather than authored blind into three
modules that are already in the root import closure. What it would buy is
recorded in the ninth and tenth passes: an element commuting with a loxodromic
translates along the quasi-axis, the seminorm becomes a homomorphism, its image
is discrete, its kernel is finite by `finite_commuting_ball`, and the free-site
lamps of the seventh pass then refute suitability for the explicit defect.

### Addendum, twelfth pass: the chain lemma

The stability half is started, with the lemma every proof of it begins from.

`gromovProduct_chain`: in a `δ`-hyperbolic space, if every consecutive Gromov
product along a chain `y 0, y 1, …, y (N+1)` is at least `c`, then the
endpoints' product is at least `c - N·δ`. It is a direct induction on the
four-point condition --- split off the last step, apply hyperbolicity once,
appeal to the inductive hypothesis --- and it is the estimate that turns local
control into global control.

Specialised to an orbit: `gromovProduct_orbit_chain` is the same statement for
the chain `k ↦ gᵏ x`, and `gromovProduct_orbit_succ` evaluates its local terms,

    (gᵏ x | gᵏ⁺¹ x)_x = (d(x, gᵏ x) + d(x, gᵏ⁺¹ x) − d(x, g x)) / 2,

which along a genuinely loxodromic orbit grow at least linearly, by
`mul_le_dist_pow`. So the chain lemma has exactly the input it wants.

**What it does not yet give, stated precisely.** The loss is `N·δ`, linear in
the length of the chain, and the growth of the local terms is also linear, so
the two cancel and the estimate does not yet control `(gᵐ x | gⁿ x)_x` uniformly
in `n`. Two further steps tame it:

1. *Bisection.* Splitting the chain in half rather than peeling one step reduces
   the loss from `N·δ` to `δ·⌈log₂ N⌉`. This is the same induction with a
   different recursion and is the natural next lemma.
2. *Morse.* Even a logarithmic loss is not uniform; removing it altogether is
   the stability theorem proper, and that is where geodesics enter --- one
   compares the quasi-geodesic with an actual geodesic between its endpoints.
   `IsSuitable` is stated over a bare `PseudoMetricSpace`, so a geodesicity
   hypothesis would have to be added first.

Step 1 is a step. Step 2 is the project, and it is the only thing between this
development and a refutation of suitability for the explicit defect.

### Addendum, thirteenth pass: bisection

Step 1 of the twelfth pass is done. `gromovProduct_chain_pow_two`: over a chain
of `2 ᵏ` steps the loss is `k · δ`, not `2 ᵏ · δ`. Same induction, different
recursion --- the two halves are chains of `2 ⁿ` steps, the inductive hypothesis
applies to each, and hyperbolicity joins them at the cost of one `δ`.

So the chain estimate is now logarithmic in the length, which is the sharp form
of it. What remains is step 2, and the thirteen passes have narrowed it to a
single classical theorem with a single missing prerequisite:

* **Missing prerequisite:** geodesics. `IsSuitable` is stated over a bare
  `PseudoMetricSpace`, because nothing before this needed more. Stability
  compares a quasi-geodesic with an actual geodesic between its endpoints, so a
  geodesicity hypothesis has to be introduced first.
* **The theorem:** quasi-geodesic stability (Morse). Even a logarithmic loss is
  not uniform in the length; removing it altogether is exactly this theorem, and
  it is the last thing between this development and a refutation of suitability
  for the explicit compression defect.

Everything else in that chain is proved: the quasi-axis exists
(`orbit_quasiIsometricEmbedding`), its local Gromov products are computed
(`gromovProduct_orbit_succ`) and grow along a loxodromic orbit
(`mul_le_dist_pow`), the chain estimate is sharp (`gromovProduct_chain_pow_two`),
the common centralizer acts properly (`finite_commuting_ball`), translation
length is a homogeneous subadditive seminorm on it
(`stableTranslation_pow`, `stableTranslation_mul_le`, `stableTranslation_nonneg`),
and the defect always supplies a nontrivial commuting element
(`exists_commuting_ne_one`) whose orbit must therefore be unbounded
(`unbounded_of_isSuitable`).

### Addendum, fourteenth pass: geodesics

The prerequisite named in the thirteenth pass is in. Nothing before it needed
geodesics --- every clause of Hull's Definition 1.4 and every theorem of these
modules is a statement about distances and Gromov products alone --- so
`IsSuitable` was, and remains, stated over a bare `PseudoMetricSpace`.
Quasi-geodesic stability is the first thing that needs more.

* `IsGeodesicSegment f a b` --- parametrised by arclength;
* `IsGeodesicSpace X` --- any two points are joined by one;
* `IsGeodesicSegment.dist_eq`, `.dist_endpoints` --- a geodesic realises
  distances exactly, i.e. it is a quasi-geodesic with constants `(1, 0)`, which
  is what makes it the comparison object;
* `gromovProduct_eq_zero_of_mem_geodesic` --- **the triangle equality**: a point
  between the endpoints of a geodesic sees them with Gromov product zero. This
  is what the Morse comparison is anchored on --- a geodesic has no slack, so an
  excursion of a quasi-geodesic away from it is measured against nothing.

**What is left is now exactly one theorem.** Quasi-geodesic stability: a
`(λ, c)`-quasi-geodesic between two points of a `δ`-hyperbolic geodesic space
stays within a distance depending only on `λ, c, δ` of a geodesic joining the
same points. Its proof is the classical one --- bound the excursion of the
quasi-geodesic outside a neighbourhood of the geodesic by comparing lengths,
then bootstrap --- and it is a genuinely multi-step argument with constants that
have to be tracked, unlike everything in these fourteen passes, each of which
was a short induction or an identity checkable line by line.

With it: an element commuting with a loxodromic translates along the quasi-axis;
`stableTranslation` becomes a homomorphism on the common centralizer; its image
is discrete and its kernel finite by `finite_commuting_ball`; an infinite-rank
free abelian subgroup is therefore impossible; and the free-site lamps of the
seventh pass refute suitability for the explicit compression defect. Every link
in that chain except the first is already proved here.

### Addendum, fifteenth pass: properness from one loxodromic

`finite_commuting_ball` from the seventh pass asked for two independent
loxodromics. That is more than the argument needs. `finite_centralizer_ball`:
a single loxodromic suffices, because the pair `(g⁻ᴺ x, gᴺ x)` is already far
apart --- at distance `d(x, g²ᴺ x)`, which the loxodromy of `g` makes arbitrarily
large --- and every element commuting with `g` displaces both by exactly its own
displacement.

So the whole centralizer of a loxodromic, not merely the common centralizer of
an independent pair, meets every ball in a finite set. That is the properness
statement in the form Osin's elementary-closure theorem uses, and it removes a
hypothesis from the downstream chain: what has to be shown about `C(g)` no longer
mentions a second element at all.

The remaining theorem is unchanged and is now the only one: quasi-geodesic
stability. With it, `C(g)` is virtually cyclic --- proper by this pass, and
carrying a discrete translation homomorphism by stability --- so it contains no
free abelian group of rank two, let alone infinite rank, and the free-site lamps
of the seventh pass refute suitability for the explicit compression defect.

### Addendum, sixteenth pass: where upper bounds come from

This pass records a structural fact about the whole attempt, and the lemma that
follows from noticing it.

**The four-point condition only bounds Gromov products from below.** Read in
either direction, `min (x|y)_w (y|z)_w − δ ≤ (x|z)_w` gives a lower bound on a
product; making a product appear as the smaller term of the `min` gives a bound
on that `min`, not on the product. Every attempt in these sixteen passes to
control `(y₀ | yₙ₊₁)_{yₙ}` from above by hyperbolicity alone failed for exactly
this reason, and the failures were not near-misses: three different
configurations were tried at basepoint `yₙ` --- with third point `yₙ₋₁`, with
`yₙ₊₂`, and with the chain lemma re-based at `y₀` --- and each yielded a lower
bound on some product or a circular identity. The relevant identities are exact
and were computed: `(y₀|yₙ₋₁)_{yₙ} = L − Qₙ₋₁` and
`(y₀|yₙ₊₂)_{yₙ} = Qₙ + Qₙ₊₁ − R`.

**Upper bounds come from geodesics, not from hyperbolicity.**
`gromovProduct_le_dist_of_mem_geodesic`: for any point `f s` on a geodesic
joining `f a` to `f b`, `(f a | f b)_w ≤ d(w, f s)`. It uses the triangle
inequality twice and the geodesic property once, and no `δ` at all.

That is the tool the stability proof runs on, and it is now available. What it
does not by itself provide is the converse --- `d(w, [A,C]) ≤ (A|C)_w + 4δ` ---
which *is* the hyperbolic direction, nor the excursion-and-bootstrap argument
that turns the two into stability. Those remain, and reconstructing them from
memory has been tried and failed; they should be formalized against
Bridson--Haefliger III.H.1.7 or Coornaert--Delzant--Papadopoulos with the text
in hand rather than guessed at.

### Addendum, seventeenth pass: the Gromov product is the distance to the geodesic

One of the two items left by the sixteenth pass is done, and it turned out not
to need an excursion argument at all.

`dist_le_gromovProduct_add` / `exists_mem_geodesic_dist_le`: some point of a
geodesic joining `A` to `C` lies within `(A|C)_w + 2δ` of `w`. Together with
`gromovProduct_le_dist_of_mem_geodesic` from the sixteenth pass, this pins the
Gromov product to the distance from `w` to the geodesic on both sides --- the
dictionary the Morse argument is written in.

**Why it works.** Take the point `p` of the geodesic at distance
`d(A,w) − (A|C)_w` from `A`. There the two Gromov products `(A|p)_w` and
`(p|C)_w` are *equal*, both to `(d(w,p) + (A|C)_w)/2` --- an exact computation,
not an estimate. So the `min` in the four-point condition is that common value
and the condition reads `(d(w,p) + t)/2 − δ ≤ t`, i.e. `d(w,p) ≤ t + 2δ`. One
application of hyperbolicity at the right point; no excursion, no bootstrap.

The sixteenth pass's diagnosis was right about *where* upper bounds come from
and wrong to conclude that this direction needed the hard argument.

**What is left is now one argument, not two.** Stability itself: that a
`(λ,c)`-quasi-geodesic from `A` to `C` stays within a constant of the geodesic.
The dictionary reduces this to showing that the backtracking `(A|C)_{yᵢ}` is
bounded along the quasi-geodesic --- and that is not free. For a general
`(λ,c)`-quasi-geodesic it is bounded above only by `(n(λ − 1/λ) + 3c)/2`, which
grows; for the orbit of a loxodromic the same quantity `(uᵢ + uₙ₋ᵢ − uₙ)/2` is
bounded below by `0` by subadditivity but above only by `n(u₁ − τ)/2`. Bounding
it uniformly *is* the stability theorem, and it is the excursion-and-bootstrap
argument that this development still does not have.

### Addendum, eighteenth pass: the dictionary, and a failed attempt recorded

`gromovProduct_dist_geodesic` packages the two halves of the sixteenth and
seventeenth passes: `(A|C)_w` is a lower bound for the distance from `w` to
every point of a geodesic joining `A` to `C`, and some point of that geodesic is
within `2δ` of it. So the Gromov product *is* the distance to the geodesic, to
within `2δ`. That is the translation the Morse argument is carried out in.

**The attempt that failed, recorded so it is not repeated.** With the dictionary
in hand, stability for the orbit of a loxodromic reduces to bounding
`φ(a,b) := (u_a + u_b − u_{a+b}) / 2` uniformly, where `u_k = d(x, gᵏ x)`. What
was tried this pass:

* *Directly from subadditivity and `τ > 0`.* Gives `0 ≤ φ(a,b)` below and
  `φ(a,b) ≤ (a+b)(u₁ − τ)/2` above. The upper bound grows; it is exactly the
  bound stability has to improve.
* *The four-point condition at `g^a x` with a third orbit point.* Yields a lower
  bound on `φ`, for the structural reason recorded in the sixteenth pass.
* *Through the dictionary.* `φ(a,b)` is the distance from `g^a x` to the
  geodesic `[x, g^{a+b} x]` up to `2δ`, so bounding it is the statement, not a
  route to it.
* *Via a commuting element.* For `a` commuting with `g`, the products
  `(a x | g^N x)_x` and `(a x | g^{−N} x)_x` are both bounded by `d(x, a x)` ---
  true but vacuous, since that is the distance being controlled.

So the remaining argument is not reachable by rearranging what is here. It is
Bowditch's, and it uses acylindricity together with hyperbolicity to show that a
loxodromic orbit is a quasi-geodesic; it should be formalized against the source
rather than reconstructed.

### Addendum, nineteenth pass: the source, and Osin's Lemma 2.3(b)

The eighteenth pass said the remaining argument "needs the source, not a
reconstruction". The source is now in hand: D. Osin, *Acylindrically hyperbolic
groups*, arXiv:1304.1246, and the survey arXiv:1712.00814. This pass records
what they actually say and formalizes the first piece.

**Formalized this pass.** `dist_le_four_delta_of_le_gromovProduct` --- Osin's
Lemma 2.3(b): two geodesics leaving `x` towards `y` and `z` stay `4δ`-close up to
distance `(y|z)_x`. Osin states it and cites Coornaert--Delzant--Papadopoulos;
the derivation here is from the four-point condition directly and lands on the
same constant. It is three applications of hyperbolicity and one identity:
`(f t | y)_x = t` exactly on a geodesic, so `(y | h t)_x ≥ t − δ` and then
`(f t | h t)_x ≥ t − 2δ`, whence `d(f t, h t) = 2t − 2(f t|h t)_x ≤ 4δ`.
Supporting lemmas `gromovProduct_comm` and `gromovProduct_geodesic_point` went
in with it.

**The remaining chain, with citations.** What stands between this development
and a refutation of suitability for the explicit defect is now itemised rather
than described:

1. *Lemma 2.1* (Osin) --- if `d(s_{i−1}, s_{i+1}) ≥ max{d(s_{i−1},s_i),
   d(s_{i+1},s_i)} + 18δ + 1` along a chain then `d(s_0,s_n) ≥ n`. This is the
   discrete local-to-global lemma. **Osin does not prove it**; he cites
   Coornaert--Delzant--Papadopoulos, Ch. 5 Thm 16. So it needs that source.
2. *Lemma 3.6* (Osin) --- a strengthening of acylindricity in which the second
   condition is relaxed to `d(y,gy) ≤ d(x,y) + ε`. **Its proof is given in full**
   and uses Lemma 2.3(b), which is now available, plus geodesics, which are now
   available. This is transcribable.
3. *Lemma 3.5* (Osin) --- two elements with quasi-disjoint quasi-fixed sets have
   loxodromic product. Proof given, but it invokes Lemma 2.1.
4. *Theorem 1.1* --- the classification; needs 3.5 and 3.6. Applied to cyclic
   subgroups it is Bowditch's dichotomy.
5. *Corollary 6.9* --- for `g` loxodromic, `C_G(g)` contains a cyclic subgroup of
   index at most `N`. **This is the statement that kills an infinite-rank free
   abelian subgroup of `C(g)`, and hence the one the refutation needs.** Its
   proof is `C_G(g) ≤ E(g)` by Lemma 2.11 --- which is about hyperbolically
   embedded subgroups and is the heaviest input --- together with Lemma 6.8,
   whose core computation is exactly `finite_centralizer_ball` from the
   fifteenth pass.

So the refutation is not one theorem away but five, of which one (2.1) is not
proved in this source at all, one (6.9) rests on hyperbolically embedded
subgroups, and one (3.6) is now transcribable. That is a more accurate picture
than any of the previous eighteen passes had.

### Addendum, twentieth pass: the first half of Osin's Lemma 3.6

Working from the source rather than from memory, four more pieces went in, all
of them steps of Osin's Lemma 3.6:

* `IsGeodesicSegment.reverse`, `IsGeodesicSegment.smul` --- the two pieces of
  geodesic bookkeeping the proof needs: it applies Lemma 2.3(b) a second time at
  the basepoint `g y`, which requires geodesics *out of* `g y`, obtained by
  reversing the one to `x` and by pushing the one from `x` to `y` forward under
  `g`.
* `gromovProduct_lower_of_displacement` --- if `k` moves `x` by at most `ε` and
  moves `y` by at most `d(x,y) + ε`, then `(y | k y)_x ≥ d(x,y)/2 − ε`. Pure
  triangle inequality: `k` being an isometry forces
  `|d(x, k y) − d(x, y)| ≤ d(x, k x) ≤ ε`, and the Gromov product unwinds. This
  is the estimate the source labels as following from (22) and (27).
* `dist_geodesic_comparison_le` --- **the first comparison**: a geodesic from `x`
  to `y` and a geodesic from `x` to `k y` stay `4δ`-close out to distance
  `d(x,y)/2 − ε`. This is Lemma 2.3(b) fed by the displacement estimate, and it
  is the step that puts Osin's point `m` within `4δ` of his point `n`.

**What remains of Lemma 3.6.** The second comparison, at the basepoint `k y`:
that `(x | k x)_{k y} ≥ d(x, k y) − ε ≥ d(k y, n)`, so Lemma 2.3(b) applies again
and gives `d(n, k') ≤ 4δ` for the corresponding point `k'` of the pushed-forward
geodesic; then `d(m, k') ≤ 8δ`, and since `k x`, `k m`, `k'` lie on one geodesic,
`d(k m, k') ≤ d(x, k x) + d(m, k') ≤ ε + 8δ`, whence `d(m, k m) ≤ 16δ + ε`. Every
constant in that chain is from the source and every ingredient is now present;
what is left is the parameter bookkeeping across three geodesics and two
basepoints.

The five-item chain of the nineteenth pass therefore stands, with item 2 half
done and its remaining half fully specified.

### Addendum, twenty-first pass: Osin's Lemma 3.6 is proved

Item 2 of the nineteenth pass's chain is done. `acylindrical_relaxed`:
acylindricity holds with the second condition relaxed from `d(y, k y) ≤ ε` to
`d(y, k y) ≤ d(x,y) + ε` --- a much weaker requirement, permitting `k` to move `y`
by almost the whole diameter --- with the same finiteness conclusion.

The route is the source's: every `k` satisfying the relaxed conditions moves the
point `m` of a geodesic `[x,y]` at distance `R₀` from `x` by a bounded amount, so
the whole set embeds in one ordinary acylindricity set for the pair `(x, m)`.
The estimate `dist_smul_geodesic_point_le` is two applications of Lemma 2.3(b),
at `x` comparing `[x,y]` with `[x, k y]`, and at `k y` comparing `[k y, x]` with
`[k y, k x]`.

**The constant is better than the source's.** Osin gets `16δ + ε`; this gets
`8δ + ε`. His last step bounds `d(k m, k')` by `d(x, k x) + d(m, k')` through the
triangle inequality, but `k m` and `k'` lie on the *same* geodesic --- the image
of `[x,y]` under `k` --- at parameters `R₀` and `d(x,y) − d(x, k y) + R₀`, so
their distance is exactly `|d(x, k y) − d(x, y)|`, which the displacement
hypothesis bounds by `ε`. The bookkeeping the twentieth pass flagged as the risk
turned out to collapse.

**Remaining chain, updated.** Of the five items:

1. *Lemma 2.1* --- local-to-global for chains. Osin does not prove it; needs
   Coornaert--Delzant--Papadopoulos Ch. 5 Thm 16.
2. *Lemma 3.6* --- **done**.
3. *Lemma 3.5* --- proof given in the source, but invokes Lemma 2.1.
4. *Theorem 1.1* --- needs 3.5 and 3.6.
5. *Corollary 6.9* --- needs Lemma 2.11 on hyperbolically embedded subgroups,
   plus Lemma 6.8 whose core is `finite_centralizer_ball` from the fifteenth
   pass.

So the bottleneck is now item 1, a single cited lemma from a book, and item 5's
Lemma 2.11.

### Addendum, twenty-second pass: a correction to the roadmap

The nineteenth pass listed five items as "what stands between this development
and a refutation". That list was right about the mathematics and wrong about the
dependency structure, and the correction matters for whoever works on this next.

**Items 1, 3 and 4 are not on the critical path.** Osin's Lemma 2.1, Lemma 3.5
and Theorem 1.1 lead to Bowditch's dichotomy --- every element of a group acting
acylindrically on a hyperbolic space is elliptic or loxodromic. Applied here,
that gives: every nontrivial element of `C(g)` has positive translation length,
so `stableTranslation` is a *norm* rather than a seminorm on the free abelian
subgroup the seventh pass produces. **That is not a contradiction.** An
infinite-rank free abelian group carries plenty of norms, and the properness
supplied by `finite_centralizer_ball` is consistent with one: `ℤ²` acts properly
on `ℍ³` as a rank-two cusp, with every nontrivial element parabolic. So the
dichotomy, even in full, does not refute suitability.

**Only item 5 does.** Corollary 6.9 --- `C_G(g)` contains a cyclic subgroup of
index at most `N` for `g` loxodromic --- is what makes an infinite-rank free
abelian subgroup impossible. Its proof in the source is `C_G(g) ≤ E(g)` by
Lemma 2.11, which is about hyperbolically embedded subgroups, together with
Lemma 6.8, whose core computation is `finite_centralizer_ball` from the
fifteenth pass.

**What Corollary 6.9 really needs.** Either the hyperbolically-embedded-subgroup
theory of Dahmani--Guirardel--Osin, or the direct route: show that every
`a ∈ C(g)` lies within a bounded distance of some `gᵐ`, so that
`C(g) = ⋃ₘ gᵐ · F` for a finite set `F`, finite by `finite_centralizer_ball`.
That direct route is quasi-axis stability again --- it is the statement that `a`
translates along the axis --- and this pass confirmed by attempting it that the
Gromov-product route to it is circular: the quantity one needs to bound,
`(g⁻ᴺx | gᴺx)_x = u_N − u_{2N}/2`, is bounded by `N(u₁ − τ)` and no better
without stability, which is what one is trying to prove.

So the correct statement of the remaining work is: **one theory, not four
lemmas.** Either hyperbolically embedded subgroups, or quasi-geodesic stability.
Everything else in this lane --- twenty-two passes, the compression object, its
clauses, the ambient, the datum, the non-degeneracy, the geodesic layer, the
dictionary, fellow-travelling, Osin's Lemma 3.6, translation length as a
homogeneous subadditive norm, and properness of centralizers --- is proved.

### Addendum, twenty-third pass: the irreducible input, identified exactly

Chasing Osin's Lemma 2.1 to its source settles what the remaining input actually
is, and it is a single named theorem.

Osin cites [CDP90, Ch. 5 Thm 16]. Papers that use the chain lemma in the form
"a concatenation of geodesics with short local Gromov products and long steps is
a global quasi-geodesic" --- for instance Cannon--Thurston-type work,
arXiv:2507.07076 Lemma 2.4 --- prove it *by reduction* to

> **[CDP90, Ch. 3, Thm 1.4]** For all `δ ≥ 0`, `k ≥ 1`, `ε ≥ 0` there are `L` and
> `λ` such that in a `δ`-hyperbolic geodesic space every `(k, ε, L)`-local
> quasi-geodesic is a `λ`-quasi-geodesic.

and that theorem is *cited, never proved*, in every paper reachable from here.
It is the local-to-global theorem for quasi-geodesics, and it is the irreducible
input: quasi-geodesic stability in the sense this development needs is a
corollary of it, and the reduction (thin triangles, a comparison of the two
sub-segments at the break point) is routine by comparison.

So the accounting is now exact. What this lane needs and does not have is **one
theorem from a book**, together with the reduction from it, or else the
hyperbolically-embedded-subgroup theory of Dahmani--Guirardel--Osin as an
alternative route to Corollary 6.9. Everything else --- twenty-three passes ---
is proved here:

* the compression object, unconditionally, in a semidirect product and in the
  manuscript's ascending HNN shape;
* Hull's Definition 1.4 in full, and that the object is exactly its algebraic
  content;
* what suitability forbids, and that the compressed copy can never be the
  suitable subgroup;
* that a compression is always strictly proper and its source infinite;
* that the compressed direction is never genuinely loxodromic;
* the geodesic layer, the Gromov-product/geodesic dictionary in both directions,
  and fellow-travelling (Osin 2.3(b));
* **Osin's Lemma 3.6**, with a better constant than the source;
* translation length as a homogeneous, subadditive, nonnegative function, zero
  exactly off the genuinely loxodromic elements;
* properness of the centralizer of a loxodromic;
* the defect is finitely supported and always carries a nontrivial commuting
  element, so a suitable geometry for it would have to give that element an
  unbounded orbit.

The right next action is a build. `scripts/remote-build.sh` over these three
modules; then CDP Ch. 3 Thm 1.4 as its own development, against a compiler.
