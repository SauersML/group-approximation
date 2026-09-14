---
rg: 2
id: mean-free-amenable-actions-residually-amenable-and-sofic
kind: claim
title: Residually amenable groups admit mean-free amenable actions, such actions pass to subgroups and force soficity, and invariant means of a nonamenable group are null on points with amenable stabilizers
distinct_from:
  thompson-f-mean-stabilizer-irs-is-trivial-or-contains-derived: that decides the stabilizer IRS of invariant means for Thompson's F only; this proves existence, heredity and soficity for mean-free amenable actions of every countable group.
  thompson-f-following-models-separate-iff-mean-charges-commutator: that builds permutation models for F from a mean charging the commutator's moved set; this builds sofic approximations of any group from any mean-free amenable action.
---

**ESTABLISHED.** **Setting.**
- `G` is a countable group and `Ω` a `G`-set. A mean on `Ω` is a positive normalized linear functional
  on `ℓ∞(Ω)`. It is invariant if `m(1_(gE)) = m(1_E)` for all `g ∈ G` and `E ⊆ Ω`.
- `Fix(g) = {ω : gω = ω}` and `Stab(ω)` is the stabilizer of `ω`.
- A *mean-free amenable action* of `G` is a `G`-set with an invariant mean `m` such that
  `m(Fix(g)) = 0` for every `g ≠ e`. This is the notion in the witness corollary of
  `thompson-f-mean-stabilizer-irs-is-trivial-or-contains-derived`.
- `G` is *residually amenable* if every `g ≠ e` survives in some amenable quotient of `G`.

**Statement.**
1. **Residually amenable groups.** If `G` is residually amenable, `G` admits a mean-free amenable
   action. In particular every amenable group and every residually finite group does, for instance the
   free group `F_2`.
2. **Subgroups.** A mean-free amenable action of `G` restricts to a mean-free amenable action of every
   subgroup `H ≤ G`.
3. **Soficity.** If `G` admits a mean-free amenable action on `Ω`, then for every finite `K ⊆ G` and
   `ε > 0` there is a finite nonempty `A ⊆ Ω` with
   `Σ_(s ∈ K) |sA Δ A| + Σ_(g ∈ K \ {e}) |A ∩ Fix(g)| ≤ ε|A|`.
   Any maps `σ : G → Sym(A)` with `σ(s)a = sa` whenever `a, sa ∈ A` then satisfy, for `g, h` with
   `g, h, gh ∈ K`: `d(σ(g)σ(h), σ(gh)) ≤ 3ε`, and `σ(g)` fixes at most `2ε|A|` points when
   `g ∈ K \ {e}`. Here `d` is the normalized Hamming distance. So `G` is sofic.
4. **Amenable stabilizers are null.** If `G` is not amenable, every invariant mean on every `G`-set
   gives mass `0` to `{ω : Stab(ω) is amenable}`.

**Consequences.**
- **No general route to amenability.** Mean-free amenable actions do not force amenability: `F_2` has
  one by item 1. So "F admits a mean-free amenable action ⇔ F is amenable", which would make
  following-model soficity of `F` equivalent to amenability of `F`, cannot come from a principle valid
  for all groups. Any proof has to use the structure of `F`.
- **Shape of a witness for F.** If `F` is not amenable, item 4 says a mean-free amenable action of `F`
  must put full mass on points whose stabilizers are nonamenable. By item 3 of the dichotomy claim, those
  stabilizers still contain no element of any fixed finite subset of `F \ {e}`, mean-almost surely.
- **Item 1 gives nothing for F.** Its nontrivial normal subgroups contain `F'` and `F/F' ≅ Z^2`
  (standard facts, as used in the dichotomy proof), so `F` is residually amenable only if it is amenable.
- **Kazhdan groups.** See `kazhdan-groups-mean-free-amenable-iff-residually-finite`.

**Trust surface.** Standard functional analysis only: weak*-density of `ℓ¹` densities among means
(Hahn–Banach), Mazur's lemma, and the layer-cake formula. The argument is close to folklore and no
novelty is claimed.

**Prior work.** Elek–Szabó (Math. Ann. 332 (2005)) introduced these actions as *essentially free
amenable actions* (`elek-szabo-essentially-free-amenable-actions`). Their Proposition 4.3 gives item 1
for amenable and residually finite groups. Their Theorem 3 gives the Følner form of item 3, and their
Corollary 4.2 relates almost-actions of this kind to soficity. For Thompson's `F`, see
`thompson-f-mean-free-actions-dense-configurations-or-unconfined`.

**ROUTES:** `mean-free-amenable-actions-residually-amenable-and-sofic-proof`.
