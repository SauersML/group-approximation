# The literal finitely presented non-MF group is sofic

Date: 2026-08-14.  Author: Cairn agent `cairn-literal`.
Status: complete written argument.  No compute, no Lean run, no manuscript
edit.  Companion to `notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md`
(structure) and `notes/TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md` (the
finite-stage tower template, 2026-08-13).

**Audit 2026-08-15 (adversarial): SOUND-WITH-FIXABLE-GAPS — and the theorem
is CONDITIONAL, which this document originally did not state.**  The single
irreducible conditional input is `B ≅ Γ̄` (equivalently: completeness of the
eight-relator presentation of `SL₃(ℤ)`, \cite{CRW} Theorem 2 via the
manuscript's `rem:classical-base`, which the manuscript quarantines as
unused literature).  It enters at exactly two places: the companion's
structure theorem (its input (I1), see the corrected header there), and
Lemma 3.1's residual finiteness of `Λ ≤ Γ_n` below.  Everything else is
unconditional; in particular `gammaBar_residuallyFinite` (Lean) already gives
the needed RF for the MATRIX levels, so the gap is precisely `B ≅ Γ̄`, not
Mal'cev.  Note the resulting trust-surface inversion: "`E` is not MF" is
unconditional while "`E` is sofic" is conditional — the reverse of the
manuscript's usual layering.  Per repo doctrine (zero literature inputs in
Lean; manuscript 1:1 with Lean) this theorem cannot enter the manuscript
until `B ≅ Γ̄` is formalized or replaced.

**Addendum 2026-08-16: the conditional input is discharged; the theorem is
unconditional, and the blocker is now a different one.**  The audit note
above is obsolete.  `Monsters/LiteralBaseCompleteness.lean` proves
`affineQuotient_injective` and `baseAffineEquiv : Base ≃* gammaBar` outright,
with no `sorry` and no literature premise, and the manuscript already badges
the equivalence at `rem:classical-base`.  Both places the note identifies —
the companion's input (I1), and Lemma 3.1's residual finiteness of `Λ ≤ Γ_n`
— are therefore discharged, the `E_lin` versus `E` distinction this document
maintains can be dropped, and §§2–8 are unconditional statements about the
literal `E`.  The trust-surface inversion the note describes no longer holds.

What now blocks the manuscript is not conditionality but formalization: no
Lean declaration concludes `IsSofic MarkedGroup`, and
`scripts/check_non_mf_claim_manifest.py` requires every numbered theorem to
name exactly one.  Drafts toward that endpoint are in
`GroupApproximation/Sofic/Literal{LampKernelSplit,BlockGeometry,LampKernelAmalgam,TelescopeCoreLEF,SoficEndpoint}.lean`
(commit `d4d87391`), none of them compiled.  The chain reduces to soficity of
`lampKernel ⋊ Telescope` at the literal carrier.

Two further corrections to this document, from formalizing §§2--3.  §2 derives
the retraction `π : Ê → V` from Lemma 2.1 and hence from Bass--Serre theory;
that is unnecessary.  The retraction is the universal property of the
presentation (send `c ↦ 1`; all forty-one relators die) and the section is the
universal property of the ascending HNN extension, so `E = N_E ⋊ V` needs no
amalgam theory and no normal-form theorem, and input (I4) is not used.  And
(3.2) defines `ζ` as "the common value" before stating the relations that make
the conjugates equal; define `ζ` as the image of `w` and let the relations
assert the equality.

**Theorem (unconditional; see the addendum above).**  The literal
forty-one-relator group `E` of `def:E` in
`non_mf_groups_exist.tex` is sofic.  Consequently `E` is an explicit
**finitely presented sofic — hence hyperlinear — group that is not MF**, and
`Rad_sof(E) = 1` while `w ∈ Rad_MF(E) \ {1}`.

This upgrades Theorem E of the manuscript from the finitely generated witness
`W` to the finitely presented source `E`, and settles item 3 of the
manuscript's open-questions list ("soficity ... of `E`") in the positive
direction.

---

## 1.  Why the obvious routes fail, and what replaces them

Two routes were tried before and both are dead:

* *Amenable kernel.*  `ker(E → W)` is free of countably infinite rank
  (`literal-witness-kernel-free`), not amenable.  And the permanence direction
  that route invoked — amenable kernel with sofic quotient — is not a theorem;
  `notes/TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md` §3 already warns against it
  in as many words ("One must not replace it by the false general claim that
  an amenable-by-sofic group is automatically sofic or hyperlinear").
* *Locally finite lamp kernel.*  The proof that `W` is sofic uses that
  `ClLamp(X)` is locally finite, so every finite window sits in a **finite**
  level-invariant subgroup.  The lamp kernel of `E` is
  `N_E = ∗_{⟨w⟩} ClLamp(8)`, which contains nonabelian free groups; no finite
  invariant subgroup contains a window that meets two blocks.

The replacement is one observation: the block structure computed in the
companion artifact is *locally finite in blocks even though it is not locally
finite in elements*.  Finitely many blocks generate a **finitely generated
virtually free**, hence residually finite, level-invariant subgroup.  So the
finite-stage tower of the `W` proof survives verbatim with "finite invariant
Clifford subgroup" replaced by "finitely generated residually finite invariant
block subgroup".

---

## 2.  Inputs

**(S1)** (`literal-telescope-split-normal-form` — `[audit-fix 2026-08-15]`
DOWNGRADED from ESTABLISHED to CONDITIONAL)
`E = N_E ⋊ V` with `V = T ⋊ ⟨τ⟩`, `T = ⋃_{n ≥ 0} Γ_n` the increasing union of
the telescope levels `Γ_n = τ^{-n} B τ^{n} ≅ ℤ³ ⋊ SL₃(ℤ)`, and
`V ≅ ⟨Γ̄, D⟩ ≤ GL₄(ℚ)` linear.  The identifications `Γ_n ≅ ℤ³ ⋊ SL₃(ℤ)` and
`V ≅ ⟨Γ̄,D⟩` carry the companion's conditional input (I1) (`B ≅ Γ̄`); the
split structure over the *presented* telescope is unconditional.

**(S2)** (`literal-lamp-kernel-clifford-block-amalgam`, ESTABLISHED)
`N_E = ∗_{⟨w⟩, i ∈ I} P_i` with every `P_i ≅ ClLamp(8)` of order 512, the
blocks being the components of the marked orbital graph on
`X = ⨆_{n∈ℤ} ℤ[1/2]³/2ⁿℤ³`; `V` permutes the blocks, and the block set is
`V`-isomorphic to `X`.

**(S3)** (`finite-telescope-level-coset-orbits`, ESTABLISHED; Lean
`MappingTelescopeFiniteOrbits.lean`)  Every telescope level has finite orbits
on `X`, hence — by the `V`-isomorphism of (S2) — finite orbits on the block
set `I`.  In coordinates: the `Γ_n`-orbit of a level-`m` site `[u]` lies in
the image in `ℤ[1/2]³/2^mℤ³` of the lattice `2^{-j}ℤ³`, `j = max(n,k)`, where
`2^{-k}` is the denominator of
`u`, because `SL₃(ℤ)` preserves the denominator lattice and the translation
part of `Γ_n` is `2^{-n}ℤ³`.

**(S4)** Standard permanence, all of it already used in the repository:
soficity is local over finite subsets (Lean
`SoficDirectedUnion.isSofic_of_every_finset_mem_sofic_subgroup`); LEF implies
sofic (`LEFSofic.isSofic_of_isLEF`); residually finite implies LEF; soficity
passes to subgroups and to finite-index overgroups; a sofic normal subgroup
with amenable quotient gives a sofic group (Elek--Szabó, `arXiv:math/0305352`;
the split integer case is Lean `SoficIntegerExtension.lean`).

**(S5)** Standard group theory: a finitely generated group acting on a tree
with finite vertex stabilisers is virtually free (Karrass--Pietrowski--Solitar);
`[audit-fix 2026-08-15: the Baumslag phrasing originally here ("finitely many
finite groups over a common finite subgroup is RF") overstates the two-factor
theorem — the route actually used is KPS virtual freeness, which the audit
verified within its hypotheses]`  finitely generated linear groups are
residually finite (Mal'cev); products of residually finite groups and
finite-index overgroups of residually finite groups are residually finite.

---

## 3.  The block-level models

Fix `n ≥ 0` and a finite `Γ_n`-invariant set `J ⊆ I` of blocks.  Write
`M_J = ⟨P_i : i ∈ J⟩ = ∗_{⟨w⟩, i ∈ J} P_i` (a sub-amalgam, by the normal form
theorem) and `sites(J)` for the `8|J|` sites carried by `J`.

**Lemma 3.1.**  `M_J ⋊ Γ_n` is residually finite, hence sofic.

*Proof.*  `M_J` is generated by the `8|J|` involutions `c_x`, `x ∈ sites(J)`,
so it is finitely generated; it is the fundamental group of a finite star of
finite groups (leaves `ClLamp(8)`, centre `⟨w⟩ ≅ ℤ/2`), so it acts on its
Bass--Serre tree with finite vertex stabilisers and is virtually free by (S5),
in particular residually finite.

`Γ_n` acts on `M_J` by permuting the generators `c_x`, `x ∈ sites(J)`, and
fixing `w`.  That action factors through the finite symmetric group on
`sites(J)`, so its kernel `Λ` has finite index in `Γ_n` and centralises `M_J`.
Hence `M_J × Λ` is a subgroup of `M_J ⋊ Γ_n` of index `[Γ_n : Λ] < ∞`.  Now
`Λ ≤ Γ_n ≅ ℤ³ ⋊ SL₃(ℤ)` is linear, hence residually finite by Mal'cev
`[audit 2026-08-15: THIS is the conditional step — `Γ_n` is a conjugate of
`ι(B)` with `B` the PRESENTED twenty-relator group, so linearity/RF of `Γ_n`
needs `B ≅ Γ̄`; for the matrix group the conclusion is unconditional and
already formalized as `gammaBar_residuallyFinite`, no Mal'cev needed]`, so
`M_J × Λ` is residually finite; residual finiteness passes to finite-index
overgroups, so `M_J ⋊ Γ_n` is residually finite.  Residually finite implies
LEF implies sofic by (S4). ∎

*Remark.*  Lemma 3.1 is the exact analogue of the step
`K_m = ClLamp(Y_m) ⋊ Γ` of `notes/TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md`
§3, where the lamp part was finite and one could quote finite index directly.
Here the lamp part is infinite but virtually free, and the same
kernel-of-the-site-action trick still puts everything inside a direct product
of two residually finite groups of finite index.

*Remark (what is not claimed).*  No claim is made that `M_J ⋊ Γ_n` is
residually finite for a non-split extension, nor that finite-by-residually-finite
extensions are residually finite in general — they are not (Deligne's central
extension of `Sp_{2g}(ℤ)`).  Splitness is used.

---

## 4.  The telescope core is locally residually finite

Let `E_T := N_E ⋊ T ⊴ E`.

**Theorem 4.1.**  Every finitely generated subgroup of `E_T` is residually
finite.  Hence `E_T` is LEF, sofic, and MF.

*Proof.*  Let `H ≤ E_T` be generated by `h_1, …, h_k`, and write
`h_j = p_j g_j` with `p_j ∈ N_E`, `g_j ∈ T` (S1).  The finitely many `g_j`
lie in a common level `Γ_n`, because `T` is the increasing union of the levels.
Each `p_j` is a word in finitely many blocks; let `J₀` be the (finite) set of
blocks occurring, and put `J = Γ_n · J₀`, which is finite by (S3) and
`Γ_n`-invariant by construction.  Then every `p_j ∈ M_{J₀} ≤ M_J`, and `Γ_n`
normalises `M_J`, so

    H ≤ M_J ⋊ Γ_n ,

which is residually finite by Lemma 3.1; subgroups of residually finite groups
are residually finite.  A group all of whose finitely generated subgroups are
residually finite is LEF, hence sofic (S4); and LEF gives MF by the argument
of `lem:rfmf`/`lem:lfmf` — exact finite models on each finite window, with the
`√3` separation. ∎

**Theorem 4.1a (`E_T` is LEF but *not* residually finite).**  So "locally" in
Theorem 4.1 is load-bearing, not a stylistic weakening.

*Proof* (argument due to `cairn-verify2`; the collapse step is written out here
for `E_T` rather than imported, since the published version is stated for a
different group).  Let `φ : E_T → F` be any homomorphism to a finite group.

*Step 1: `φ(B_n) = φ(T)` for every level.*  The image `A = φ(ℤ[1/2]³)` is a
finite abelian group on which multiplication by 2 is surjective, hence
injective, hence `|A|` is odd.  So 2 is invertible on `A`: `φ(2^{-k}u)` is the
unique `y` with `2^k y = φ(u)`, and it lies in `⟨φ(u)⟩`.  Therefore
`φ(ℤ[1/2]³) = φ(ℤ³)`, and since multiplication by `2^n` is an automorphism of
`A` also `φ(2^nℤ³) = φ(ℤ³)`.  As `T` is generated by `ℤ[1/2]³` and `SL₃(ℤ)`,
and `B_n = 2^nℤ³ ⋊ SL₃(ℤ)`, this gives `φ(B_n) = φ(B) = φ(T)` for all `n`.
No stable letter was used.

*Step 2: same-level lamps collapse.*  Let `x, x'` be sites of level `n`.  `T`
is transitive on each level (Proposition 4.1: level `n` is `T/B_n`), so
`x' = t·x` with `t ∈ T`.  The stabiliser `Stab_T(x)` is a `T`-conjugate of
`B_n`, and `φ` of a `T`-conjugate of `B_n` is a `φ(T)`-conjugate of
`φ(B_n) = φ(T)`, hence equals `φ(T)`.  From `φ(Stab_T(x)) = φ(T)` we get
`T ⊆ Stab_T(x)·ker φ`, so `t = s k` with `s ∈ Stab_T(x)`, `k ∈ ker φ`.  Then

    φ(c_{x'}) = φ(t) φ(c_x) φ(t)^{-1} = φ(s) φ(c_x) φ(s)^{-1}
              = φ(c_{s·x}) = φ(c_x).

*Step 3.*  The marked sites `a = τo` and `b = v₁τo` are both at level 1
(Proposition 4.1), so `φ(c_a) = φ(c_b)` and `φ(w) = φ([c_a,c_b]) = 1`.  Since
`w ≠ 1` in `E_T` (Theorem 5.1 of the companion structure artifact: `w = ζ` is
the nontrivial centre of every block), no finite quotient of `E_T` separates
it. ∎

This makes Objection 1 of §6a vivid rather than merely correct: `w` is
nontrivial in every member of the directed system and in every sufficiently
fine finite quotient of every member, yet dies in every finite quotient of the
union.  A directed union of residually finite groups need not be residually
finite, and this one demonstrably is not.

**Remark 4.2 (quantifier order — no uniformity in `n` is used or needed).**
The locality theorem consumes one statement: *for every finite `F ⊆ E_T`
there exist `n` and `J` with `F ⊆ M_J ⋊ Γ_n`*.  The pair `(n,J)` is allowed to
depend on `F` arbitrarily, and it does: `n` is the smallest level containing
the telescope coordinates of `F`, and `J = Γ_n · J₀` grows with both.  Nothing
in the argument asks for a bound on `n`, on `|J|`, on `[Γ_n : Λ]`, or on the
sizes of the finite models, and no constant is claimed uniform across windows.
The diagonalization that produces a single sofic approximation of `E_T` is over
an exhausting sequence of *windows*, not over `n`: window `k` is served by the
models of its own `M_{J(k)} ⋊ Γ_{n(k)}`, at whatever dimension and error that
group's residual finiteness provides.  This is the same quantifier order as the
`W` proof, where the invariant lamp subgroup `L` likewise depends on the
window.

Directedness (used in §6a) is a separate statement and is proved there: any two
windows are jointly served by one member of the family, so `E_T` is a directed
union rather than merely a union.

---

## 4a.  The marked quotient is sofic too, and a dichotomy follows

**Theorem 4.3.**  `E/⟨w⟩ = (∗_{i∈I} (ℤ/2)⁸) ⋊ V` is sofic.

*Proof.*  Verbatim §§3--5 with the block groups `ClLamp(8)` replaced by their
central quotients `(ℤ/2)⁸` and the central amalgamation deleted: `M'_J =
∗_{i∈J} (ℤ/2)⁸` is a free product of finitely many finite groups, hence
finitely generated and virtually free, so `M'_J ⋊ Γ_n` is residually finite by
Lemma 3.1 (whose proof used only that the lamp part is finitely generated
residually finite and that the level acts through a finite permutation group of
the sites).  Level orbits on blocks are finite as before, so the shift-free
part is LEF, and `E/⟨w⟩` is its `ℤ`-extension. ∎

**Corollary 4.4 (dichotomy).**  Exactly one of the following holds, and either
one moves an open node:

* `E/⟨w⟩` is residually finite.  Then it is MF (`lem:rfmf`), which is
  `literal-mark-quotient-mf`, and hence `Rad_MF(E) = {1,w}`
  (`literal-mf-radical-exact`).
* `E/⟨w⟩` is not residually finite.  Then, being sofic, it is **not stable in
  finite actions** (Theorem 3.1 of
  `notes/SOFIC_STABLE_IMPLIES_RESIDUALLY_FINITE_2026-08-14.md`), exactly as for
  `E` itself.

**Corollary 4.5 (the dichotomy resolves: second branch).**  `cairn-quotient-mf`
has since computed the finite residual of `E/⟨w⟩` exactly
(`literal-mark-quotient-finite-residual`): it is the level-collapse kernel

    R = ⟪ c_x c_{x'} : level(x) = level(x') ⟫ ,

which is nontrivial and contains elements of infinite order.  So `E/⟨w⟩` is
**not** residually finite, and Corollary 4.4 lands in its second branch:

> `E/⟨w⟩` is sofic and not residually finite, hence **not stable in finite
> actions**, hence not stable in any stronger permutation sense
> (`literal-mark-quotient-not-stable-in-finite-actions`).

Two consequences for the Gohla--Thom line, which is now closed for this pair.
Hypothesis (i) of their Theorem 3.13 fails outright for `E/⟨w⟩`, so the theorem
never applied to `(E/⟨w⟩, E)`: the three-way disjunction of Corollary 5.6 is
resolved, and resolved on the residual-finiteness disjunct.  Nothing follows
from it about the dimension-2 cosystolic inequality, which therefore remains
untouched — but also unneeded, since the stability conclusion above is proved
directly.  The independent structural heuristic against a cosystolic inequality
for `E/⟨w⟩` (a nontrivial amalgam acting on a Bass--Serre tree, with no
Bruhat--Tits geometry of the kind that produces the known inequalities) is
recorded in `literal-mark-quotient-flexibly-stable`, unproved and no longer
load-bearing.

Note the residual-finiteness failure is the same level-collapse phenomenon
recorded at §9(d) of the companion structure artifact — in every finite
quotient of `V` all telescope levels have one image, so all same-level lamps
are identified.  What was an obstacle to a proof strategy there is a theorem
here.

---

## 5.  The literal group is sofic

**Theorem 5.1.**  `E` is sofic.

*Proof.*  `T ⊴ V` with `V/T ≅ ℤ`, so `E_T = N_E ⋊ T` is normal in
`E = N_E ⋊ V` with `E/E_T ≅ ℤ`, and the extension splits along `⟨τ⟩`.  `E_T`
is sofic by Theorem 4.1 and `ℤ` is amenable, so `E` is sofic by the
sofic-kernel/amenable-quotient permanence (S4).  This is the valid direction of
the Elek--Szabó theorem — the same step that the `W` proof uses at
`S = K̃ ⋊ ℤ`. ∎

**Corollary 5.2.**  `E` is an explicit finitely presented sofic group that is
not MF; being sofic it is hyperlinear, so it is also an explicit finitely
presented hyperlinear non-MF group.  This strengthens Theorem E of the
manuscript, which gives the same separation for the finitely generated
witness `W`.

*Proof.*  Soficity is Theorem 5.1; `E` is finitely presented and non-MF by
Theorem A (`literal-central-mark-corona-invisible`,
`literal-group-fails-mf-conventions`); sofic implies hyperlinear
(`sofic-implies-hyperlinear`). ∎

**Corollary 5.3.**  `Rad_sof(E) = 1` and `Rad_MF(E) ⊇ {1, w} ≠ 1`.  So the two
radicals are separated on a finitely presented group, sharpening (LCV3) of
`notes/TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md`, which separated them only at
the level of the single word `w`.

*Proof.*  `Rad_sof(H) = 1` iff `H` is sofic (`sofic-radical-soficization`). ∎

**Corollary 5.4.**  MF is not closed under extensions with LEF kernel and
quotient `ℤ`: `E_T` is LEF (hence MF) by Theorem 4.1, `E/E_T ≅ ℤ` is MF, and
`E` is not MF.  *Read this in the repository's group-level operator-MF
convention* — MF here means the norm-matrix-corona property of
`countable-group-mf-conventions`, established for `E_T` by window models as in
`lem:rfmf`/`lem:lfmf`.  It is not a statement that a crossed product `A ⋊ ℤ` of
an MF C*-algebra fails to be MF; no C*-algebraic extension claim is made or
needed.  This is the `E`-level companion of the same phenomenon for the
witness, recorded concurrently by `lamp-telescope-base-is-lef`
(`ClLamp(X) ⋊ T` and `𝔽₂[X] ⋊ T` are LEF, and `W`, `W/⟨ζ⟩` are their
`ℤ`-extensions); no separate claim is raised here for it.

**Corollary 5.5.**  `E` is sofic but not LEF, and not residually finite: a
finitely presented LEF group is residually finite (Vershik--Gordon), while `E`
is not residually finite because residually finite groups are MF
(`lem:rfmf`).  So `E` is an explicit finitely presented group separating sofic
from LEF.

**Corollary 5.6 (what the Gohla--Thom theorem now says here).**  The primary
statement is Gohla--Thom, *High-dimensional expansion and soficity of groups*,
`arXiv:2403.09582v2`, Theorem 3.13, imported in the Cairn node
`gohla-thom-stable-base-nonsofic-extension`: for `Γ` countable and `A` finite
abelian, if (i) `Γ` is residually finite of finite type, (ii) `Γ` satisfies a
dimension-2 cosystolic inequality for all finite transitive actions with
coefficients in `A`, (iii) some central extension of `Γ` by `A` is not
residually finite, and `Γ` is stable in finite actions, then that extension is
not sofic.

Apply this with `Γ = E/⟨w⟩`, `A = ℤ/2`, `Γ̃ = E`.  Hypothesis (iii) holds: `E`
is a central `ℤ/2` extension of `E/⟨w⟩` and is not residually finite
(Corollary 5.5).  Theorem 5.1 says `E` *is* sofic.  Therefore

    at least one of  (i) E/⟨w⟩ residually finite of finite type,
                     (ii) the dimension-2 cosystolic inequality,
                     and stability in finite actions
    FAILS for E/⟨w⟩.

This is strictly weaker than the earlier draft of this corollary, which
asserted failure of flexible stability alone; that version relied on the
secondary rendering (`arXiv:2410.02913` Theorem 1.5, a specialization to the
p-adic Deligne extension) and silently dropped hypotheses (i) and (ii).  Note
(i) is exactly the open question `literal-mark-quotient-mf` is circling —
residual finiteness of `E/⟨w⟩` would give MF of that quotient — so a proof of
(i) would convert this corollary into "either the cosystolic inequality or
stability in finite actions fails", and a proof of (i) plus (ii) would give
non-stability outright.

**Corollary 5.7 (the sharp form: `E` is not stable).**  `E` is **not stable in
finite actions** in the sense of Gohla--Thom Definition 3.7, hence not stable
in any stronger permutation sense — not `ρ`-stable, not flexibly stable, not
weakly flexibly stable.  The first sentence is internal to this repository; the
strengthening in the second rests on Gohla--Thom Lemma 3.6 (each standard
notion implies theirs), an external input, source-verified and recorded in
`gohla-thom-stable-base-nonsofic-extension`.

*Proof.*  `E` is sofic (Theorem 5.1) and not residually finite (Corollary 5.5).
A sofic group that is stable in finite actions is residually finite
(`sofic-stable-implies-residually-finite`, proved in
`notes/SOFIC_STABLE_IMPLIES_RESIDUALLY_FINITE_2026-08-14.md`; also stated in
Gohla--Thom §3.2 and in Chapman--Dikstein--Lubotzky, both crediting
Glebsky--Rivera 2009).  Every
standard permutation-stability notion implies stability in finite actions
(Gohla--Thom Lemma 3.6 and the following remark), so all of them fail. ∎

This is the reversal of the route that motivated §5.6.  Gohla--Thom use
stability of a base to force non-soficity of a central extension; here
soficity of the extension is established first, so the same elementary
principle runs backwards and outputs non-stability — with no cosystolic
inequality, no cohomology, and no hypothesis on `E/⟨w⟩`.  It also strictly
strengthens the disjunction of Corollary 5.6 *for `E`*, while saying nothing
about `E/⟨w⟩`: stability does not pass between a group and its central
extension, and Chapman--Dikstein--Lubotzky §4 exhibit a lamplighter base that
is stable with a non-stable central extension (finitely generated, infinitely
presented; the finitely presented case is open).  `E` is finitely presented, so
Corollary 5.7 is also a data point on that open question — a finitely presented
non-stable group whose central quotient's stability is unknown.

---

## 6.  Consistency with the rest of the corpus

* **No conflict with Kun--Thom.**  Their non-soficity theorem needs the acting
  group to be Kazhdan.  Here the acting group is `V`, which surjects onto `ℤ`
  by the stable-letter exponent and is therefore not Kazhdan.  The Kazhdan
  subgroup `B` is infranormal in `V`, and that is exactly what supplies the
  non-MF mark; what fails for `V` is what permits soficity.  The two
  phenomena live on opposite sides of the same hypothesis.
* **No conflict with `w ∈ Rad_MF(E)`.**  Soficity is a permutation statement;
  non-MF is an operator-norm statement.  The sofic approximations produced
  here are honest finite models of *windows*, and `w` is visible in them —
  consistent with `w ∉ Rad_sof(E)` (LCV3).  What the manuscript proves is that
  no *norm matrix corona* representation keeps `w`, and Sym-models are not
  corona models: they do not converge in operator norm on the compression
  relations, exactly as `finite-quotient-blindness` predicts (each finite
  quotient collapses the telescope levels).
* **No conflict with the failure of residual finiteness.**  Non-residual
  finiteness of `E` enters only through the `τ`-direction: finite quotients
  must collapse all telescope levels, so `w` dies.  Nothing in §§3--5 produces
  a finite quotient of `E` itself; the finite models live on `E_T`-windows and
  are glued by an amenable `ℤ`.
* **Corpus precedence.**  The finite-stage tower, the coset tower `X_n` of
  cardinality `8ⁿ`, the soficity of `W`, and the warning about the invalid
  amenable-by-sofic direction are all already in
  `notes/TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md` (2026-08-13); the present
  document adds only the block-amalgam replacement for the finite lamp
  subgroup, which is what carries the argument from `W` up to `E`.

---

## 6a.  Verification notes: the exact permanence used, and two objections

**Which permanence statements the proof consumes, in full.**

1. *Directed unions / locality.*  If every finite subset of `G` lies in a sofic
   subgroup, `G` is sofic.  Lean:
   `SoficDirectedUnion.isSofic_of_every_finset_mem_sofic_subgroup`.  Used once,
   for `E_T`.
2. *Residually finite implies sofic*, via LEF.  Lean `LEFSofic.isSofic_of_isLEF`.
3. *Residual finiteness permanence*: subgroups, finite direct products, and
   finite-index overgroups.  All elementary.
4. *Sofic kernel with amenable quotient gives sofic* (Elek--Szabó,
   `arXiv:math/0305352`).  Used once, for `E = E_T ⋊ ℤ`; the split integer case
   is Lean `isSofic_int_semidirectProduct`, whose statement is exactly
   `N ⋊[φ] Multiplicative ℤ`.  The other three are Lean
   `isSofic_of_every_finset_mem_sofic_subgroup`, `isLEF_of_residuallyFinite`
   and `isSofic_of_isLEF`; `cairn-verify2` confirmed all four are sorry-free.  This is the direction
   the repository's own `notes/TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md` §3
   endorses; the converse direction (amenable kernel, sofic quotient), which
   that same section warns is false, is **not** used anywhere here.

**No wreath permanence, and no soficity-of-action hypothesis.**  The proof
invokes none of the wreath-product permanence theorems (Hayes--Sale,
Holt--Rees, GKEP, Alekseev--Bradford), and therefore never needs the
hypothesis those theorems require — that the acting group's coset action be
modelled by permutations, which Kun--Thom Corollary D forbids for their pair.
The block decomposition is used only to *locate subgroups* of `E_T`, never to
approximate an action.  The only action ever approximated is the action of a
single level `Γ_n` on the finite site set `sites(J)`, and that action is a
genuine finite permutation action: `Γ_n → Sym(sites(J))` has finite image by
construction, so its kernel `Λ` has finite index.  Nothing is asked of the
`V`-action on the infinite site set `X`.

*By-product, not an input* (observed by `cairn-verify2`): the `V`-action on `X`
is in fact sofic here, since `T` is an increasing union of finite-orbit
subgroups and `V/T ≅ ℤ`.  So there is no tension with the coordinate-action
cluster, which concerns the Kun--Thom pair
`EL_r(R_+) ≤ EL_r(R) ⋊ SL_d(ℤ)` — a different acting group, whose
non-sofic-action statement comes from Kun--Thom Theorem A and needs both groups
Kazhdan.  The point stands that the proof below never *uses* soficity of the
action.

That is exactly the hypothesis that separates this from the Kun--Thom setting.
There the acting group is Kazhdan, so it has no infinite amenable quotient and
no exhausting chain of subgroups with finite orbits on the coset space; the
`Γ`-orbits on `G/Γ` are infinite, which is what infranormal-and-nonnormal
means.  Here `V = T ⋊ ℤ` splits off an amenable `ℤ` and `T` is the increasing
union of levels with **finite** orbits on `X` (S3).  The finite-orbit input is
what supplies, for free, the local finiteness of action that a wreath
permanence theorem would otherwise have to hypothesize.

**Objection 1: do the finite models of overlapping block subgroups have to
agree on the shared central `w`?**  No, and nothing is glued.  The family
`{M_J ⋊ Γ_n}` is *directed*: given `(n, J)` and `(n', J')`, put
`n'' = max(n,n')` and `J'' = Γ_{n''}·(J ∪ J')`, finite by (S3) and
`Γ_{n''}`-invariant, so both lie in `M_{J''} ⋊ Γ_{n''}`.  Hence `E_T` is a
directed union of residually finite subgroups, and soficity of a directed
union needs no compatibility whatever between the finite models of different
members — each finite window is approximated by one member's models, and
different windows may use unrelated models.

Even so, the system is consistent on `w` in the strongest sense one could ask:
for `J ⊆ J'` the inclusion `M_J ↪ M_{J'}` is injective (sub-amalgams of an
amalgamated product), and every one of these inclusions sends `ζ = w` to
`ζ = w`, which is `≠ 1` in each `M_J` because `M_J` surjects onto the Clifford
lamp group on `sites(J)` where `ζ = −1`.  So `w` is nontrivial in every member
of the directed system and in every sufficiently fine finite quotient of every
member.  There is no diagonal argument anywhere that could drive `w` to `1`.

**Objection 2: how is that compatible with `w` dying in every finite quotient
of `E`?**  There are two answers, and the second is the sharper one.

*Why the collapse cannot reach a single level* (`cairn-verify2`).  Every
collapse mechanism in this corpus — `finite-quotient-blindness`,
`marked-quotients-not-lef`, the level-collapse theorem behind
`literal-mark-quotient-finite-residual` — consumes either `τ` or the whole
telescope `T`.  Inside one level there is nothing to consume: `[Γ_n : B] = 8ⁿ`
is *finite*, so `B` is separable in `Γ_n` outright and the finite quotients of
`Γ_n` do separate the levels below `n`.  The collapse is a `T`-phenomenon,
invisible in any single `Γ_n`, and the block models of §3 live in a single
`Γ_n` by construction.  That is why the windows are immune, not merely why
they are of a different kind.

*Why the kinds differ anyway.*  The finite objects produced here are finite
models of *subgroup windows*, not finite quotients of `E`.  A sofic approximation of `E`
is a sequence of maps `E → Sym(Ω_n)` that are only *approximately*
multiplicative; they are not homomorphisms and do not factor through any
quotient of `E`.  Exactness is lost precisely at the stable letter: the models
of §§3--4 are exact homomorphisms on `E_T`-windows, and the Elek--Szabó step
that adds `ℤ` is where approximate multiplicativity enters.  This is the same
division of labour as in the proof that `W` is sofic, and it is why `w` can be
simultaneously invisible to every finite quotient of `E`
(`finite-quotient-blindness`: any finite quotient must collapse the telescope
levels) and visible in sofic approximations (`w ∉ Rad_sof(E)`, (LCV3) of
`notes/TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md`).  The two statements quantify
over different things.

**Robustness remark.**  Finiteness of level orbits on *blocks* does not depend
on the `V`-set isomorphism `I ≅ X` of Proposition 4.2.  A block is determined
by its eight sites, so the `Γ_n`-orbit of a block injects into the set of
blocks meeting the (finite) `Γ_n`-orbit of any one of its sites, and each site
lies in exactly one block.  Finite site orbits alone therefore give finite
block orbits; the isomorphism `I ≅ X` is a convenience, not a load-bearing
step.

---

## 7.  Provenance and sweep record

Corpus checked before writing: `notes/TRUE_LITERAL_NONMF_MARK_IS_CE_VISIBLE.md`
(closest precedent, §§2--3 reused), `notes/EXPLICIT_FINITELY_PRESENTED_NON_MF_GROUP.md`
(historical snapshot of the construction), `notes/NOTEPAD.md` (searched for
kernel/telescope/LEF/soficity of `E`; the relevant entries are the Kun--Thom
adjudication of 2026-08-08 and the free-lamp reduction, neither of which
treats `E`'s own soficity), `notes/NON_MF_FINAL_REVIEW_AND_RESOLUTION_2026-08-14.md`
(records soficity of `E` as open), `notes/scout-2026-08-14.md` (via
`cairn search --notes`), `research/invariant-graph-clifford-phase` and its
artifacts `notes/TRUE_KUN_THOM_CLIFFORD_PHASE.md` (independent, concurrent
development of the same free-lamp/invariant-graph Clifford machinery in the
Kun--Thom setting — the present block computation is the literal-pair
instance), the Lean modules `SoficDirectedUnion`, `LEFSofic`, `SoficTransfer`,
`SoficIntegerExtension`, `SoficTelescope`, `MappingTelescopeFiniteOrbits`,
`FiniteOrbitInvariantKernel`, and the frozen manuscript (read-only):
`def:E`, `lem:linear`, `prop:witness`, proof of Theorem E, `lem:rfmf`,
`lem:lfmf`, `cor:notRFD`.  No prior proof of soficity of `E` was found in any
of these.

---

## Audit addendum, 2026-08-15 (adversarial audit, minor findings)

The load-bearing conditional gap is recorded in the header; the following
minor items were also found and stand corrected here rather than inline:

* **LEF ⟹ MF mis-citation** (§4, §5): attributed to `lem:rfmf`/`lem:lfmf`,
  neither of which states it.  The fact is nonetheless formalized:
  `isOperatorMF_of_isLEF` (`GroupApproximation/Sofic/LocallyFiniteMF.lean:39`).
* **Corollary 4.5**: the doc's own method proves only `R ⊆` the finite
  residual; "exactly `R`" is imported from another agent's artifact and was
  not verified by this audit.  Not load-bearing for Theorem 5.1.
* **Notation collision**: `Γ_n = τ⁻ⁿBτⁿ` (increasing levels, §§2–3) versus
  `B_n = 2ⁿℤ³⋊SL₃(ℤ)` (decreasing, §4a) are both used without a bridging
  sentence; the companion doc is itself inconsistent on `B_n` vs `B₁`.
  No mathematical error results.
* **Lean coverage confirmed by the audit**: `isSofic_int_semidirectProduct`
  (`SoficIntegerExtension.lean:330`) covers the final ℤ-extension step in
  full generality (any kernel, any action — not specialized to `W`);
  `finite_verticalLevel_orbit` / `finite_orbit_on_quotient_of_commensurated`
  (`MappingTelescopeFiniteOrbits.lean:219,188`) cover the orbit step as-is,
  because a block is determined by its eight sites, so block orbits reduce to
  the formalized site orbits with CRW-free hypotheses.
* **Formalization cost estimate** (from the audit): companion structure
  theorem ~3–5k lines (Mathlib `Monoid.PushoutI`/`NormalWord` supplies the
  amalgam normal form); RF of `M_J` (bespoke KPS-free proof for finitely many
  finite factors over a central ℤ/2) ~1.5–3k lines; RF product/overgroup
  lemmas ~150–300 lines each; assembly ~500 lines.  The blocking atom
  `B ≅ Γ̄` (CRW Theorem 2) is the decisive item: without it a Lean-checked
  "E is sofic" is out of reach, and it cannot be axiom-tagged because
  `scripts/Audit.lean` pins `literatureInputNames := []`.
