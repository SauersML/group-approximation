# Zero-input routes to `M_J ⋊ Γ_n` residual finiteness: design note

Date: 2026-08-15.  Status: design analysis for the next Lean phase of the
E-soficity tower.  Nothing here is asserted as established; the routes are
ranked for formalization cost.  Companion state:
`notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md` (Lemma 3.1, inputs S1–S5) and
`notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md` (§§3–5).

## 1. What is already kernel-checked (this repository, 2026-08-15)

The general permanence layer of the tower is complete and unconditional:

* `isLEF_of_forall_finset_subgroup` — LEF is closed under exhaustion by
  LEF subgroups (`Sofic/LEF.lean`), with the local characterization
  `isLEF_of_forall_fg` as a corollary.
* `isLEF_of_forall_finset_residuallyFinite`,
  `isSofic_of_forall_finset_residuallyFinite` (`Sofic/LEFSofic.lean`) and
  `isOperatorMF_of_forall_finset_residuallyFinite`
  (`Sofic/LocallyFiniteMF.lean`) — the exact quantifier order of
  Theorem 4.1/Remark 4.2 of the soficity artifact: the subgroup may depend
  on the finite subset arbitrarily, and the conclusions are the full
  LEF/sofic/MF package.
* `residuallyFinite_of_finiteIndex`, `residuallyFinite_of_injective`,
  `residuallyFinite_of_mulEquiv`, and
  `residuallyFinite_semidirectProduct_of_finite_range` — the site-action
  kernel trick of Lemma 3.1 as a general theorem: a semidirect product of
  residually finite groups whose action has finite range is residually
  finite.
* Mathlib supplies: `Group.ResiduallyFinite` with subgroup and product
  instances and the finite-index/normal characterizations;
  `Monoid.PushoutI` with a normal-form theory (amalgamated products);
  `Monoid.CoprodI` with a normal-form theory (free products);
  Nielsen–Schreier.  In-repo: residual finiteness of free groups
  (`Sofic/FreeGroupResiduallyFinite.lean`), `gammaBar_residuallyFinite`
  for the matrix side of `Γ_n`.

Consequently Lemma 3.1 reduces, in zero-input form, to exactly one
statement:

> **(M)** For finite `J`, the central amalgam
> `M_J = ∗_{⟨ζ⟩, i∈J} P_i` of copies of `ClLamp(8)` over the common
> central `⟨ζ⟩ ≅ ℤ/2` is residually finite (or merely LEF).

The instantiation of the kernel trick then needs only the finite-range
fact (the `Γ_n`-action permutes the `8|J|` sites) and `Γ_n` residual
finiteness (matrix side unconditional; presented side is d8's completeness
chain).  The exhaustion statement (every finite subset of `E_T` lies in
some `M_J ⋊ Γ_n`) is bookkeeping over the telescope coordinates (S3) and
is not the hard part.

## 2. The obstacle

The artifact's own route to (M) is input (S5): Karrass–Pietrowski–Solitar
virtual freeness of groups acting on trees with finite stabilisers.
Neither Bass–Serre theory nor KPS exists in Mathlib.  Formalizing them
wholesale is the worst-cost route.

## 3. Routes, ranked

**(B) The `ClLamp`-kernel acts freely — smallest new theory (recommended
first).**  Let `q_J : M_J → ClLamp(sites(J))` be the finite Clifford
quotient (impose the missing cross-block `ζ`-commutation relations; the
target has order `2^{8|J|+1}`) and `K_J := ker q_J`, of finite index.  The
observation: the composite `P_i ↪ M_J → ClLamp(sites(J))` is *injective*
(it is the sub-Clifford inclusion of the block), and by equivariance the
same holds for every conjugate of every factor.  So `K_J` meets every
conjugate of every amalgam factor trivially, i.e. `K_J` acts **freely** on
the Bass–Serre tree of the amalgam.  Freeness of `K_J` therefore needs
only the single theorem *a group acting freely on a tree is free* — no
virtual-freeness, no stabiliser bookkeeping, no graph-of-groups
decomposition.  With `K_J` free: `residuallyFinite_of_finiteIndex` +
free-group residual finiteness close (M).  Cost estimate: the free-action
theorem over Mathlib's `PushoutI` normal form (the tree can stay implicit:
"free on the tree" can be phrased as "trivial intersection with every
conjugate of every factor", and the Kurosh-style argument for that special
case is a transversal induction over normal forms).  This is a real but
bounded project; it also yields `ker(E → W)` free (Theorem 6.1 of the
structure artifact) with the same machinery.

**(C) The two-quotient separation — RESOLVED 2026-08-15, and it wins.**
The injectivity question closes trivially, with no normal-form
computation.  `ζ` is *central* in `M_J`, so the kernel of
`r : M_J → M_J/⟨ζ⟩` is exactly the two-element subgroup `⟨ζ⟩` — not some
larger normal closure.  The finite Clifford quotient
`q : M_J → ClLamp(sites(J))` satisfies `q(ζ) = ζ ≠ 1`.  Hence
`ker q ∩ ker r ⊆ ⟨ζ⟩ ∩ ker q = 1`, and

    (q, r) : M_J ↪ ClLamp(sites(J)) × C̄_J

is injective, where `C̄_J := M_J/⟨ζ⟩ = ∗_{i∈J} (ℤ/2)⁸` is a *plain* free
product (killing `ζ` abelianizes each block and removes every cross-block
relation).  The Deligne finite-by-residually-finite trap is avoided
precisely because the central kernel survives an explicit finite
quotient.  By `residuallyFinite_of_injective` and the product instance,
(M) reduces to:

> **(M′)** The free product of finitely many copies of `(ℤ/2)⁸` is
> residually finite.
>
> **STATUS: FORMALIZED 2026-08-15**, same-day:
> `Sofic/FreeProductSignReflection.lean` proves `rho_injective` (the
> signed-reflection representation on the coordinate module with a
> basepoint is faithful, by the block-sum invariant
> `2 + otherSum i₀ v ≤ blockSum i₀ v` at the first index versus
> `blockSum j v + 2 ≤ otherSum j v` elsewhere, propagated along
> `CoprodI` reduced words) and `residuallyFinite_coprodI_signGroup`
> (composition into `GL(Coord, ℤ)` plus
> `generalLinearGroup_int_residuallyFinite`).  Neither Bass--Serre nor
> Coxeter theory was needed; sub-routes (i)--(iii) below are obsolete.

Amalgamated products, `PushoutI`, and route (B)'s `K_J` analysis are all
eliminated from the critical path; only Mathlib's `CoprodI` is needed.
Route (B) survives solely as one candidate proof of (M′) (the kernel of
`∗_{i∈J}(ℤ/2)⁸ → ∏_{i∈J}(ℤ/2)⁸` meets every conjugate of every factor
trivially — the factors embed in the product — so the same Kurosh-lite
statement gives it free of finite index).

**(D) Direct LEF via truncated tree actions — not recommended.**  Finite
approximations of the tree action are only partially defined at the ball
boundary, and `LocalMultiplicativeOn` requires globally defined
permutations with exact multiplicativity on the test set; repairing the
boundary reintroduces exactly the bookkeeping (B) avoids.

**(A) Full Bass–Serre/KPS — last resort.**  Subsumes (B) at several times
the cost; nothing else in the tower needs the extra generality.

## 4. Next actions (updated after the (C) resolution)

1. Formalize the reduction of §3(C): the presented `M_J`, its central
   `⟨ζ⟩`, the two quotients, and the injection into the product —
   entirely elementary once `M_J` is stated (check the two in-repo
   Clifford realizations, `Sofic/CliffordLampGroup` and
   `Monsters/CliffordAlgebraLamp`, before writing anything new;
   duplication trap).
2. Prove (M′) — residual finiteness of `∗_{i∈J}(ℤ/2)⁸` over Mathlib's
   `CoprodI`.  Candidate sub-routes, in cost order: (i) Kurosh-lite —
   the kernel of the map to the direct product meets every conjugate of
   every factor trivially, so a normal-form/transversal induction shows
   it free, and `residuallyFinite_of_finiteIndex` +
   `Sofic/FreeGroupResiduallyFinite` close; (ii) explicit integral
   linearization by ping-pong (Mathlib `lift_injective_of_ping_pong` on
   `CoprodI`) into `GL_N(ℤ)` and the in-repo
   `Sofic/IntegralLinearResiduallyFinite.lean`; (iii) a direct
   Gruenberg-style finite-quotient scheme.  Start with (i).
3. The `Γ_n`-instantiation and the exhaustion statement wait on (S1)'s
   conditional half (d8's `B ≅ Γ̄`), but their statements can be authored
   against the presented telescope now.
