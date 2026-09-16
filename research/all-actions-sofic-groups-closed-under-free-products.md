---
rg: 2
id: all-actions-sofic-groups-closed-under-free-products
kind: claim
title: Groups all of whose set actions are sofic are closed under subgroups, increasing unions and free products, but not under quotients
distinct_from:
  free-products-of-sofic-actions-are-sofic: that is the action-level theorem for one action of a free product; this is the resulting permanence of the group class, together with subgroup closure by induction, quotient failure and a new finitely presented member
  gkp-amenable-group-actions-are-sofic: that imports one family of members (amenable actors); this proves closure properties of the whole class and uses that family only as input
  paunescu-sofic-action-class-permanence: that is Paunescu's class of groups all of whose p.m.p. actions are sofic; this is the class for actions on countable sets in the GKP sense, a different notion with no known implication from the p.m.p. one
  groups-containing-kun-thom-pair-have-nonsofic-actions: that gives nonsofic p.m.p. actions of overgroups by co-induction; this gives nonsofic set actions of overgroups of the Kun--Thom group by induction of sets
---

Let `𝒜` be the class of countable groups `G` such that every action of `G`
on a countable set is sofic, in the sense of GKP Definition 2.1(5). Then the
following hold.

1. **Members are sofic.** Every `G ∈ 𝒜` is a sofic group.
2. **Closure.** `𝒜` is closed under
   - subgroups,
   - countable increasing unions,
   - countable free products.
3. **Members.** `𝒜` contains every countable amenable group. Hence it
   contains every countable free product of amenable groups, such as all
   countable free groups, `PSL_2(Z) = C_2 * C_3`, and `K_1 * K_2 * ⋯` with
   each `K_i` amenable.
4. **No quotient closure.** `𝒜` is not closed under quotients. The group `G`
   of `coordinate-action-not-sofic` is not in `𝒜`, but it is a quotient of
   the free group `F_∞ ∈ 𝒜`. By item 2, no countable group containing that
   `G` lies in `𝒜`.
5. **A new finitely presented member.** For every prime `p`, let `Γ_p` be
   the Abels--Pruefer quotient of
   `abels-prufer-quotient-is-fp-sofic-with-fd-invisible-center`. Then
   `Γ_p * Z ∈ 𝒜`. This group has the following properties.
   - It is finitely presented and nonamenable.
   - It has torsion, so it is not free.
   - It is **not residually finite**, hence not LERF.

**What is new.**
- Items 2 (free products) and 5 are new, as far as the sources checked on
  2026-09-16 show.
- GKP Theorem 2.17 covers amenable actors only. Theorem 2.19 covers free
  actors only.
- Gao, arXiv:2402.17150, covers LERF groups. The graph has not verified the
  wording of that paper verbatim. Gao notes, citing Burns, that free products
  of LERF groups are LERF.
- None of these covers `Γ_p * Z`: it is not amenable, not free and not
  residually finite. It is finitely generated, so it is not a proper
  increasing union either.
- Items 1, 3 and the subgroup and union parts of item 2 are formal
  consequences of GKP's toolkit. They are recorded because the free-product
  closure is only useful together with them.

DERIVATION
all-actions-sofic-groups-free-product-closure-proof
