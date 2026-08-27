# The Kun–Thom/Shulman double construction, formalized unconditionally

`metadata/LITERATURE_QUARANTINE.md` carried `KunThomShulmanDoubleData` with
"what discharging it needs" set to **the construction**.  This wave supplies the
construction.  Four modules, all unconditional, all wired into the root:

| module | what it proves |
|---|---|
| `Sofic/InfranormalCompressionPair` | the compression semigroup `P_Γ = {g : gΓg⁻¹ ≤ Γ}` as a submonoid, infranormality, and **the escape clause** |
| `Sofic/IteratedDoubleAmalgam` | the `ι`-fold amalgam `⋆_{Γ, i ∈ ι} G`, relabelling functoriality, and the embedding of the two-vertex double |
| `Sofic/FreeLampKernelSplitting` | the retraction `G *_Γ (Γ × K) → K`, the Bass–Serre covering, and the two permanence transfers |
| `Sofic/SymmetricDoubleCovering` | at `K = C₂` the covering **is** `G *_Γ G`, so MF and soficity are the same question for the double and for the lamp amalgam |
| `Sofic/CoveringWitness` | the Kun–Thom witness lies in the covering, with an explicit preimage word, and a named nontrivial element of `G *_Γ G` |
| `Sofic/KunThomShulmanDoubleConstruction` | the assembly, and the old six-field interface rebuilt from three hypotheses |

## The three things that were not previously proved here

**1. The escape clause is not a hypothesis.**  `KunThomShulmanDoubleData` asked
its caller for a compressor `t`, a mark `γ`, `γ ∈ Γ`, and `t⁻¹ γ t ∉ Γ`.  Those
four fields exist for *every* non-normal subgroup of *every* group:
`exists_escape_of_not_normal` is two lines, and
`nonempty_escapeWitness_iff` proves the converse, so the replacement is exact.
`Sofic/KunThomDoubleWitness` had already discharged them at the repository's own
marked-compression pair; this discharges them at every pair.

**2. The Bass–Serre covering is an isomorphism, in both directions.**

```text
G *_Γ (Γ × K)  ≅  (⋆_{Γ, k ∈ K} G) ⋊ K
```

with `K` acting on the vertex set by left translation
(`freeLampEquivSemidirect`).  Both maps are built from the universal property
and checked on generators; nothing is quoted.  Consequently
`ker(G *_Γ (Γ × K) → K)` is exactly the image of the `K`-fold amalgam
(`range_iteratedToFreeLamp`), the covering embeds
(`iteratedToFreeLamp_injective`), and for finite `K` it has index `|K|`.

**3. Operator-MF rises from the covering to the amalgam.**
`isOperatorMF_freeLamp_of_isOperatorMF_iterated`.  This is the step that makes
a *symmetric* amalgamation theorem usable at all: `G *_Γ (Γ × K)` is not an
amalgam of two copies of one group, but its covering is, and the passage
upwards is `InducedCorona.isOperatorMF_of_finiteIndex_subgroup`, already proved
in this repository.  Soficity transfers both ways by the same splitting.

`construction_unconditional` states all of this as one proposition, so "the
construction is formalized" is a single checkable claim rather than a reading of
a file list.

**4. At the order-two lamp the covering *is* the symmetric double.**

```text
IteratedDouble G Γ FlipC2  ≃*  SymmetricDouble G Γ
```

(`symmetricDoubleEquivIteratedFlip`), so operator-MF and soficity are literally
the same question for `G *_Γ G` and for `G *_Γ (Γ × C₂)` —
`isOperatorMF_freeLampFlip_iff_isOperatorMF_symmetricDouble` and
`isSofic_freeLampFlip_iff_isSofic_symmetricDouble`.  `Sofic/DoubleSoficTransfer`
already had the forward soficity direction through the flip semidirect product;
the converse is new, and the two routes agree.

This is what collapses the MF citation at `K = C₂` from the
finitely-many-factors form of the amalgamation theorem to its **symmetric**
form — whose group-level conclusion `IsOperatorMF (SymmetricDouble G Γ)` is
*literally the `operatorMF` field* of the quarantined datum.  So
`data_conclusion_both` shows the existing `KunThomShulmanDoubleData`, unchanged,
now settles the free-lamp amalgam as well as the double.

**5. The obstruction is a named element of the double.**  The witness
`w = [t k t⁻¹, γ]` is a commutator whose lamp letters cancel, so the retraction
kills it (`lampWitness_mem_lampKernel`) and it has an explicit preimage in the
covering: with `u = ⟨1⟩t · (⟨k⟩t)⁻¹`,

```text
w̃ = u · ⟨k⟩γ · u⁻¹ · (⟨1⟩γ)⁻¹,
```

`iteratedToFreeLamp_iteratedWitness`.  At `K = C₂` this is `doubleWitness`, a
nontrivial element of `G *_Γ G` produced from `¬ Γ.Normal` alone
(`exists_doubleWitness_ne_one`).  The Kun–Thom mechanism is then the assertion
that no sofic approximation of the double survives it — a statement about the
double, not about an auxiliary lamp group.

**6. The three degenerations are identified.**  One vertex, or `Γ = ⊤`, collapses
the amalgam to `G` (`iteratedUniqueEquiv`, `iteratedTopEquiv`); `Γ = ⊥` makes it
the free product `∗_{i ∈ ι} G` (`iteratedBotEquiv`).  `IsCompressionPair.ne_bot`
and `ne_top` say a compression pair avoids the two edge-group boundaries, and
these identifications are what give that content.

## What is left, and it is not the construction

Two sentences, from two different papers:

* `IsOperatorMF (IteratedDouble G Γ K)` — Shulman, *The MF property for
  amalgamated free products*, arXiv:2603.13564, Theorem 10 plus its
  finitely-many-factors form, applied to the profinite regular completion of a
  countable residually finite `G` (the group-level argument is in
  `notes/WEAK_MF_NONSOFIC_DOUBLE.md` §1–2);
* `HasSoficCentralizerNormalization Γ` — Kun–Thom, centralizer rigidity in a
  permutation ultraproduct.

Both appear as **bare hypotheses** in the statements of
`freeLamp_isOperatorMF_and_not_isSofic` and `symmetricDouble_not_isSofic`.  They
are deliberately *not* bundled into a named structure: the quarantine's own
argument is that a name for a package of literature conclusions is exactly the
shape the kernel cannot see, so this wave adds no new entry to
`literaturePackages`.

## Not done

* No inhabitant of either hypothesis is constructed, so no unconditional
  separation is claimed.  The endpoint theorems remain implications.
* The concrete Kun–Thom pair `Γ = EL_r(F_q[x₁,…,x_d])`,
  `G = EL_r(F_q[x₁^{±1},…,x_d^{±1}]) ⋊ SL_d(ℤ)` is not built.  What *is* now
  available is that its only combinatorial requirement — `Γ` non-normal —
  suffices for every field of the old datum.
* Nothing here was compiled: the wave was authored under a no-build directive.
