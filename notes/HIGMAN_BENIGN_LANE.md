# The benign-subgroup lane: what is proved, and the one lemma that is left

Written 2026-08-19, alongside `notes/HIGMAN_EMBEDDING_FORMALIZATION_PLAN.md`,
which reaches the same conclusion from the other side.  Both were written
while closing Chiodo Theorem 3.10 / Belegradek Theorem A.1 --- *there is a
finitely presented torsion-free group containing a copy of every finitely
presented torsion-free group* --- **unconditionally**.  This note records the
modules that landed, the two places where the classical route was shortened,
and exactly what is still owed.

## 1.  Chiodo §3, formalized whole and unconditionally

| module | contents |
|---|---|
| `Algebra/TorsionFreeRadical.lean` | `IsIsolated`, `torsionFreeRadical`, Corollary 3.4 both halves, `torsionFreeRadical_eq_bot_iff`, functoriality |
| `Algebra/TorsionFreeRadicalTower.lean` | Definition 3.1's tower, Lemma 3.2, Proposition 3.3 (`torsionOmega = torsionFreeRadical`) |
| `Algebra/TorsionFreeQuotient.lean` | `G^tf`, the lift, uniqueness, and the **retraction principle** |

The one design decision worth repeating: the radical is defined as the
infimum of the normal **isolated** subgroups (`g ^ n ∈ N → g ∈ N`), not
through the transfinite tower.  Isolatedness is visibly stable under
intersection where "has torsion-free quotient" is not, so the infimum is
again one of the subgroups it is an infimum of, and Corollary 3.4 is two
lines.  Proposition 3.3 then identifies it with Chiodo's own tower, so
nothing is lost.

## 2.  The absorber, and why its index set is the whole code type

`Monsters/ChiodoTorsionFreeAbsorber.lean` builds

    ChiodoAbsorber := (⨁_{c : FinitePresentationCode} G_c)^tf

and proves it countable, torsion-free, nontrivial, and absorbing every
finitely presented torsion-free group.  The point is the *index set*: the
older payload `Monsters/UniversalFinitelyPresentedTorsionFreeGroup.lean`
filtered the codes to the torsion-free ones, which is undecidable by
Adian--Rabin, so Higman/Chiodo could not be applied to it at all.  Filtering
is replaced by the torsion-free quotient, which is Chiodo's own device, and
the mechanism that makes it work is the retraction principle: a coordinate of
a direct product is a retract, and a torsion-free retract survives the
passage to `^tf` however much torsion the other coordinates carry.

`Sofic/ChiodoUniversalHost.lean` then formalizes Chiodo Definition 2.1
(`TorsionOrders`, with `torsionOrders_eq_empty_iff`) and **produces**
`FournierFacioUniversal.UniversalTorsionFreeHost` from one structure,
`TorsionFreeHigmanHull ChiodoAbsorber`.

A parallel lane in the same tree reaches the same place with a free product
in place of the direct sum (`Monsters/ChiodoFreeProductAbsorber.lean`,
`Sofic/ChiodoBelegradekTheorem.lean`); the two absorbers are independent
witnesses of the same statement and neither supersedes the other.

## 3.  The benign lane

| module | contents |
|---|---|
| `Higman/Benign.lean` | `BenignWitness`, `Benign`; `ofFG`; **`inf`** (intersections, by a direct product); **`ker`** (kernels of maps to finitely presented groups) |
| `Higman/BenignClosure.lean` | `FPOvergroup`; **`comap`** (preimages, Higman's Lemma 3.3(2)); finite intersections |
| `Higman/HNNCentralizer.lean` | `CentHNN`; **`mem_of_conj_mem_range`** (Britton in the form the theory uses); **`map_inf_conj_map`**: `G ∩ Gᵗ = G ∩ L`; finite presentation of `K ∗_L t` |
| `Higman/AmalgamPresentation.lean` | the amalgam as a presented quotient; **finite presentation over a finitely generated amalgamated subgroup** |
| `Higman/AmalgamPushout.lean` | that quotient **is** Mathlib's `PushoutI`, so the normal form theorem is available on it |
| `Higman/Pinch.lean` | **the pinch lemma, proved**: `⟨Z, Qᵗ⟩ ∩ P = Z` when `Q ⊓ M ≤ Z` and `Z ⊓ M ≤ Q` |
| `Higman/PinchGraph.lean` | the pinch descent with a value attached, and the homomorphism `τ : ⟨A, Aᵗ⟩ → T` it yields |
| `Higman/RopeTrick.lean` | **the rope trick, proved**: `fpOvergroup_of_benign` --- if `N` is benign in a finitely generated, finitely presented `F`, then `F ⧸ N` embeds in a finitely presented group |
| `Higman/RowSubgroup.lean` | **Higman's Example 3.5, proved**: `⟨bᵢ : i ∈ ℤ⟩` is benign in `⟨b, c⟩` |
| `Higman/EmbeddingTheorem.lean` | **Higman's embedding theorem from one input**: `REBenign` (his Sections 2--4) plus the rope trick |
| `Higman/RowBasis.lean` | **the row elements are a free basis**, by an explicit action on `FreeGroup ℤ × ℤ` |
| `Higman/ConjugateBasis.lean` | **the conjugates `a^h`, `h ∈ ⟨b,c⟩`, are a free basis**, by the same device |
| `Higman/SequenceSpace.lean` | Higman's sequence space, the coding `f ↦ a^{b_f}`, its faithfulness, and **the operations `ι` and `υ`** |
| `Higman/ShiftOperation.lean` | **the operation `σ`**, realized by an automorphism of `F₃` |
| `Higman/BenignJoin.lean` | **Higman's Lemma 3.2(2), proved**: `Benign.sup`, by the gluing above and two applications of the pinch lemma |
| `Higman/Program.lean` | `PinchProperty`; `RecursivePresentation`; the two remaining inputs and their composite |

### Two shortenings of the classical route

**(a) The `✻`-construction is not needed.**  The literature glues two benign
witnesses with a nested amalgam of HNN extensions.  Gluing with the *direct
product* `K₁ × K₂`, with `G` diagonal, already makes `L₁ × ⊤` and `⊤ × L₂`
finitely generated subgroups cutting out `A₁` and `A₂`; two stable letters
over that base do the rest, and finite presentation is `instProd` followed
twice by `isFinitelyPresented_hnnExtension`.  `Higman/BenignJoin.lean` is
that construction.

**(b) The join needs exactly one word lemma, and it is now proved.**  With the gluing above, the
remaining inclusion follows from `Higman.PinchProperty` applied twice --- once
in `Γ₁` with `Z = ⟨A₁, A₂⟩`, `Q = G`, and once in `Γ₂` with
`Z = ⟨A₁, A₂, Gᵗ¹⟩`, `Q = G`, whose second hypothesis is the conclusion of the
first application.  `PinchProperty` says: in `P ∗_M t`, if `Q ⊓ M ≤ Z` and
`Z ⊓ M ≤ Q`, then `⟨Z, Qᵗ⟩ ∩ P = Z`.  Its proof --- `Higman/Pinch.lean` --- is an induction on the
length of `z₀ · t⁻¹q₁t · z₁ ⋯`, in which the two hypotheses are exactly what
absorbs the two ways a letter can pinch, and whose base case is Britton's
lemma, taken from Mathlib through the reduced word `redList`.  So Higman's
Lemma 3.2 is complete: intersections by a direct product, joins by this.

## 4.  What is owed

**Update, same day.**  The rope trick is proved, so what Higman's embedding
theorem owes is exactly `Higman.REBenign`: *a recursively enumerable normal
subgroup of a free group of finite rank is benign*, which is his Sections
2--4.  Two further steps stand between that and Chiodo's Theorem 2.2 --- the
Higman--Neumann--Neumann bridge from countably generated to finitely
generated, and the torsion clause --- and both are named in
`Higman/Program.lean`.

    Chiodo Thm 3.10  =  everything above (proved)
                     +  (A) Chiodo Thm 2.2 = Higman embedding + torsion orders
                     +  (B) Chiodo Prop 3.8 at the absorber

with (B) splitting further:

* **(B1)** `Monsters.CodedDirectSum` is recursively presented.  Reachable
  inside this repository: a word is trivial in a restricted direct product
  exactly when each of its finitely many coordinates is, and
  `Computability/WordProblemRE.lean` already proves the word problem of a
  coded finite presentation recursively enumerable.  The one change of
  design it needs is to index the direct sum by
  `Computability.PresentationCodes.PresentationCode`, which is `Primcodable`,
  rather than by `Monsters.FinitePresentationCode`, which is not.
* **(B2)** the universal torsion-free quotient of a recursively presented
  group is recursively presented --- Chiodo's Proposition 3.8, whose proof is
  his Lemmas 3.5--3.7 over the tower `Algebra/TorsionFreeRadicalTower.lean`
  formalizes.

For (A) the shortest complete published route is Mikaelian, arXiv:1908.10153
(a modified proof of Higman's theorem), whose Sections 3--4 are Higman's own
argument with the sequence space `E` and the Higman operations; the free
constructions it rests on are Lemmas 3.1--3.7 of arXiv:2309.03030, and
`Higman/HNNCentralizer.lean` plus `Higman/AmalgamPushout.lean` are the
Mathlib-side ingredients those lemmas need.

## 5.  Duplication to merge

The parallel lane carries `Algebra/BenignSubgroup.lean` (`Benign.IsBenign`),
`Algebra/BinaryAmalgam.lean`, `Algebra/PushoutIFinitePresentation.lean` and
`Algebra/CoprodIFinitePresentation.lean`, which overlap this lane's
`Higman/Benign.lean`, `Higman/AmalgamPresentation.lean` and
`Higman/AmalgamPushout.lean`.  The namespaces are disjoint, so nothing
collides; whichever pair compiles first should absorb the other, and this
note should be updated to say which.
