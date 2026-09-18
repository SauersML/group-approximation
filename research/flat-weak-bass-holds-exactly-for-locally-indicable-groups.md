---
rg: 2
id: flat-weak-bass-holds-exactly-for-locally-indicable-groups
kind: claim
title: The weak Bass inequality rank_Q(Q ⊗ M) <= dim_U(U ⊗ M) holds for all flat modules over Z[G] exactly when G is locally indicable; it is then Cohn specialization from the universal Hughes-free field to the augmentation; and weak Bass for big projectives passes to finite extensions by Swan's theorem
distinct_from:
  amenable-cd-two-bass-defect-equals-euler-characteristic: item 5 there gives one flat module of positive defect over the Hantzsche-Wendt group; this proves that such a module exists over every group that is not locally indicable, the counterexample K included, and that none exists over a locally indicable group
  l2-finite-projectives-over-amenable-groups-satisfy-weak-bass: that is the open inequality for countably generated projectives over torsion-free amenable groups; this proves it, for all flat modules and without amenability, over locally indicable and virtually locally indicable groups, and shows that flat-module arguments reach no other group
  amenable-cd-two-kropholler-iff-locally-indicable: that uses Jaikin-Zapirain--Lopez-Alvarez to make Q[G] a domain for amenable locally indicable G; this uses the universality of the Hughes-free division ring (Jaikin-Zapirain 2021), a different theorem, to compare the von Neumann rank with the augmentation rank
  strong-atiyah-passes-to-locally-indicable-extensions: that is a permanence theorem for strong Atiyah; this is a comparison between two Sylvester rank functions on Z[G], the von Neumann one and the one pulled back from the trivial representation
---

**ESTABLISHED** (proposed; referee pending) through
`flat-weak-bass-holds-exactly-for-li-groups-proof`. Recalled imports: Jaikin-Zapirain's theorem
that the Hughes-free division ring of `K[G]` is universal for locally indicable `G` (Selecta Math.
27, 2021); Jaikin-Zapirain–López-Álvarez: for locally indicable `G`, the division closure `D(G)`
of `Q[G]` in `U(G)` is a Hughes-free division ring (Math. Ann. 2020); Lazard–Govorov; Swan's
theorem that finitely generated projective `Z[F]`-modules are locally free, `F` finite; Lück's
additivity and cofinality for `dim_U`.

**Notation.** `G` is any group, `U = U(G)`, `ε : Z[G] → Z` the augmentation. For a matrix
`A ∈ M_{k×n}(Z[G])`, `rk_U(A)` is its von Neumann rank and `rk_ε(A) = rank_Q ε(A)`. For a left
`Z[G]`-module `M`, its **defect** is `D(M) = rank_Q(Q ⊗ M) − dim_U(U ⊗ M)` when the second term
is finite. **(WBB)** for `G` means `D(C) <= 0` for every countably generated projective `C` with
`dim_U(U ⊗ C) < ∞`.

1. **Characterization.** For every group `G` the following are equivalent.
   - (i) `G` is locally indicable.
   - (ii) *Semicontinuity:* `rk_ε(A) <= rk_U(A)` for every matrix `A` over `Z[G]`.
   - (iii) *Flat weak Bass:* `rank_Q(Q ⊗ M) <= dim_U(U ⊗ M)` in `[0, ∞]` for every flat
     `Z[G]`-module `M` (of any cardinality).
   - (iv) `D(M) <= 0` for every countably generated flat `M` with `dim_U(U ⊗ M) < ∞`, of the
     form `colim(Z[G]^n →·B Z[G]^n →·B ⋯)` with `B = B^*`.
2. **Mechanism of (i) ⇒ (ii).** For `G` locally indicable, `D(G)` is the universal division
   `Q[G]`-ring. The augmentation `Q[G] → Q` is an epic map to a division ring, so Cohn
   specialization gives `rank_Q ε(A) <= rank_{D(G)}(A) = rk_U(A)`. In the commutative case this
   is lower semicontinuity of fibre rank at the closed point `ker ε` against the generic point.
3. **Consequence: WBB for locally indicable and virtually locally indicable groups.** WBB holds,
   in the strong form (iii), for every locally indicable group, amenable or not. And WBB passes
   to finite extensions and to subgroups: if `N ≤ G` has finite index and WBB holds for `N`,
   then it holds for `G` (with equality `rank_Q(Q ⊗_G C) = rank_Q(Q ⊗_N C)/[G:N]`). So WBB holds
   for every virtually locally indicable group, torsion or not, for example every virtually
   polycyclic group.
4. **Obstruction: flat-module arguments prove WBB for exactly the locally indicable groups.**
   Let `G` be a group that is not locally indicable. By (iv) ⇒ (i) there is a countably
   generated flat module `M_B` with `dim_U(U ⊗ M_B) < ∞` and `D(M_B) > 0`, and `D(M_B) >= 1`
   when `G` is torsion-free. In particular this
   holds for a finitely generated amenable counterexample `K` to Kropholler's question in
   dimension 2 with finite abelianization. There the Fox rows of finitely many relators of `K`
   itself give `D(M_B) >= 1`. Over `K`, `M_B` and the core `P'` of the relation module both have
   positive defect. So an argument that proves `D(C) <= 0` for `C = P'` must use a property that
   `M_B` lacks. Being flat, being countably generated, finite `L²`-dimension and a colimit
   presentation are not enough. What is needed is projectivity as a direct summand of a free
   module. This extends item 5 of `amenable-cd-two-bass-defect-equals-euler-characteristic`
   from the Hantzsche–Wendt group to every group that is not locally indicable. The exact step
   where a flat argument fails is (ii): the comparison `rk_ε(A) <= rk_U(A)` on the finite
   matrices that present `M`. It holds only in the presence of a universal division ring of
   fractions that dominates the augmentation, and by (ii) ⇒ (i) such a ring exists only for
   locally indicable groups.
5. **What is left of WBB for the flagship.** For amenable `G`, a group that is locally indicable
   or virtually locally indicable and has cd 2 is already elementary amenable (see
   `amenable-cd-two-kropholler-iff-locally-indicable`). So items 1–3 settle no new case of the
   flagship. What they settle is the method: every remaining case of WBB that matters is a group
   `G` with no finite-index locally indicable subgroup, where flat WBB fails. A proof of WBB there
   must separate projective from flat modules by an invariant that `M_B` violates. By item 3,
   Swan's theorem lets one pass to any finite-index subgroup first.

**Calibrations.** Abelian torsion-free `G` of any rank (e.g. `Q`, `Z^(∞)`): (ii) is the
determinant argument, and WBB holds even when Bass's big-projective theorem is not available
(`Z[Q]` is not noetherian). Finite `G ≠ 1`: (ii) fails for `A = (Σ_g g)`, with
`rk_ε = 1 > 1/|G| = rk_U`, but WBB over `Z` holds, by item 3 with `N = 1`. So (ii) is strictly
stronger than WBB, and torsion is not an obstruction to WBB over `Z`. Hantzsche–Wendt: virtually
`Z³` but not locally indicable. Flat WBB fails and WBB holds (item 3), so this group separates
the flat statement from the projective one.
