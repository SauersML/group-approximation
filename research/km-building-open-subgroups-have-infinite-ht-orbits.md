---
rg: 2
id: km-building-open-subgroups-have-infinite-ht-orbits
kind: claim
title: In every highly transitive action of a Kac--Moody lattice over a finite field, every building-open subgroup and each of its finite-index subgroups has only infinite orbits
distinct_from:
  km-negative-completion-building-open-dichotomy: that gives these orbit constraints for negatively building-open subgroups, such as B_-; this proves them for positively building-open ones.
  km-building-open-subgroups-have-infinite-bi-index: that is the double-coset dichotomy for building-open subgroups; this applies it to point stabilizers and set stabilizers of multiply transitive actions and to the closures of subgroups of finite bi-index.
  kac-moody-lattice-confined-subgroups-are-lim-free-and-mif: that shows confined subgroups pass the Le Boudec--Matte Bon obstructions, so the confined route cannot refute high transitivity; this constrains non-confined subgroups (chamber fixators, parabolics) in a hypothetical highly transitive action, which Le Boudec--Matte Bon Theorem 1.1 does not address.
  fp-simple-type-a-actions-iff-finite-bi-index-subgroups: that identifies type (A) actions with finitely generated proper subgroups of finite bi-index; this shows that for Kac--Moody lattices the closure of such a subgroup in the building completion is non-open or of finite index.
  two-transitive-action-reduces-type-a-to-two-clauses: that is a general reduction for 2-transitive actions; this is a specific orbit constraint for Kac--Moody lattices in 2k-transitive actions.
artifacts:
  - research/artifacts/km-building-open-subgroups-bi-index-2026-09-16.md
---

**ESTABLISHED** through `km-building-open-ht-orbits-from-bi-index-proof`. Checked once by the
swarm referee (2026-09-16), not otherwise reviewed. No novelty is claimed.

**Statement.** Keep the setting of `km-building-open-subgroups-have-infinite-bi-index`: `(W,S)`
is irreducible, with `S` finite and `W` infinite. Let `N ⊴ Λ` with `N ⊆ Z_Λ(Λ^†)`, and put
`Γ = Λ/N`. For an open subgroup `V` of the positive completion `G`, let `Γ_V` be the image of
`Λ ∩ V`. For example, the pointwise fixator in `Γ` of any finite set of chambers of the
positive building is some `Γ_V`. Let `Γ` act on an infinite set `Ω`.

- **(a)** If the action is transitive with finitely many orbitals, no point stabilizer contains
  any `Γ_V`.
- **(b)** If the action is `2k`-transitive, every `Γ_V`-orbit has more than `k` points.
- **(b')** If the action is highly transitive, every orbit of every `Γ_V`, and of every
  finite-index subgroup of `Γ_V`, is infinite. For `Γ_V` itself this says
  `[Γ_V : Γ_V ∩ Γ_ω] = ∞` for all `V` and `ω`. The same holds for every subgroup of `Γ`
  containing some `Γ_V` (a building-open subgroup of `Γ`) and for its finite-index subgroups.
- **(c)** If the action is primitive with finitely many orbitals, the closure in `G` of the
  preimage of `Γ_ω` is `G` or is not open.
- **(d)** If `H ≤ Γ` has infinite index and finitely many double cosets, the closure in `G` of
  its preimage is not open, or is open of finite index.

**For the explicit members.** Take `S_q = Λ_q/Z`, type `(2,4,6)`, `q ≥ 4`. In any highly
transitive action of `S_q`, every Borel subgroup `𝓑_+/Z`, every fixator of finitely many
chambers, and every finite-index subgroup of one of these has only infinite orbits.

**What this does to the root question.**
- **Where it bites.** A highly transitive action cannot be built by making a building-local
  subgroup (a chamber or residue stabilizer, or something containing a small open trace) the
  point stabilizer, or even a finite-orbit subgroup.
- **What it leaves open.** Stabilizers whose closure in `G` is non-open are untouched. Examples
  are discrete subgroups of `G`, stabilizers of ideal points, and subgroups dense in `G`.
- **The confined route.** For confined subgroups, Le Boudec--Matte Bon (Ann. H. Lebesgue 5
  (2022), Theorem 1.1, as imported in
  `kac-moody-lattice-confined-subgroups-are-lim-free-and-mif`) already give high transitivity
  on the complement of finitely many finite orbits. Chamber fixators are expected not to be
  confined: item 5 of that node excludes subgroups with a bounded orbit in Rybak's space, and
  for chamber stabilizers this rests on a comparison it marks as unverified. So (b') is a
  constraint of a different kind, and it does not depend on confinement.
- **The negative building** is not covered.
