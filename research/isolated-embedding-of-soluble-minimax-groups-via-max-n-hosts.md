---
rg: 2
id: isolated-embedding-of-soluble-minimax-groups-via-max-n-hosts
kind: claim
title: A finitely generated soluble minimax group embeds in an isolated group as soon as it embeds in some finitely presented group satisfying max-n (for example a finitely presented soluble minimax group, or any quotient of an Abels group); in general it embeds in an isolated group iff some homomorphism to an isolated group is injective on a finite G-discriminating subset of its periodic radical
requires:
  - fp-groups-with-max-n-are-limits-of-isolated-groups
  - ascending-hnn-of-isolated-groups-embed-in-isolated-groups
  - rf-soluble-minimax-groups-satisfy-permutational-bh
  - linear-and-metabelian-groups-embed-in-isolated-groups
distinct_from:
  hall-type-prufer-quotients-embed-in-isolated-abels-groups: that treats the central quotients A_n/C by explicit Abels hosts; this reduces the whole soluble minimax class to one finite set in the periodic radical, and handles every soluble minimax subgroup of every finitely presented max-n group, including arbitrary quotients of Abels groups.
  fp-groups-with-max-n-are-limits-of-isolated-groups: that shows finitely presented max-n groups are limits of their isolated quotients; this turns that approximation into an honest embedding for soluble minimax subgroups, using that their periodic radical is discriminated by a finite set.
  fg-soluble-minimax-groups-satisfy-boone-higman: that is the OPEN Boone–Higman statement; this is the weaker isolated-embedding question (CGP Question 4) for the same class, reduced to one embedding problem.
---

**ESTABLISHED** (lane proof, bh-free-60, 2026-09-18; elementary modulo the landed nodes and
the standard facts listed; not reviewed). No priority is claimed.
- The key step is Cornulier–Guyot–Pitsch Prop. 2.3, through
  `fp-groups-with-max-n-are-limits-of-isolated-groups`.
- The consequence for their Question 4 is recorded here.
- The Abels host is owned by lane bh-solvable; this node only uses it as an example.

**Standard facts used, not re-read.** For a finitely generated soluble minimax group `G` with
maximal periodic normal subgroup `τ = τ(G)`:
- **(S1)** `τ` is a Chernikov group, a finite extension of a direct sum of finitely many
  Prüfer groups. So it satisfies the minimal condition on subgroups. This is as in
  `fg-soluble-minimax-groups-satisfy-boone-higman`.
- **(S2)** `G` is residually finite iff `τ` is finite (Pyber–Segal §3, as used in that node).
  Since `τ(G/τ) = 1`, the quotient `G/τ` is residually finite.

## Statement

Let `G` be a finitely generated soluble minimax group, and let `τ = τ(G)`.
1. **A finite discriminating set for the radical.** There is a finite `Φ ⊆ τ − {1}` such
   that every nontrivial subgroup of `τ` normal in `G` meets `Φ`.
2. **Reduction.** The following are equivalent:
   - `G` embeds in an isolated group;
   - some homomorphism from `G` to an isolated group is injective on `τ`;
   - some homomorphism from `G` to an isolated group is injective on `Φ`.
3. **Max-n hosts.** If `G` embeds in a finitely presented group `P` in which every normal
   subgroup is finitely normally generated (max-n), then `G` embeds in an isolated group.
4. **Examples of such `P`.** Here `G` can be any finitely generated subgroup:
   - of any quotient `A_{n,p}/N`, `n >= 4`, by any normal subgroup `N`. `A_n` is finitely
     presented (CGP Prop. 5.6). Max-n holds by P. Hall's criterion (standard, not re-read): the
     unipotent radical `U` is nilpotent, and `A_n/U'` is finitely generated
     abelian-by-abelian;
   - of any finitely presented abelian-by-polycyclic-by-finite group, which has max-n by P.
     Hall (1954; standard, not re-read), provided `G` is minimax.

   This extends `hall-type-prufer-quotients-embed-in-isolated-abels-groups` from central
   quotients to all quotients of Abels groups.

## Proof

**1.**
- **Minimal invariant subgroups.** Let `𝓜` be the set of minimal nontrivial subgroups of
  `τ` normal in `G`. By (S1), every nontrivial `G`-normal `L ≤ τ` contains a member of `𝓜`.
- **Each `M ∈ 𝓜` is finite.** Let `D` be the divisible part of `τ`, of finite index.
  - If `M ∩ D ≠ 1`, then `M ⊆ D` by minimality. `M` contains an element of prime order, and
    the elements of prime order in `D` form a finite `G`-invariant set, which generates a
    finite `G`-normal subgroup. By minimality `M` lies inside it.
  - Otherwise `M` embeds in `τ/D`.
- **`𝓜` is finite.** Suppose not. Build `S_0 = 1` and `S_(k+1) = S_k M_(k+1)` as follows.
  - `S_k` is finite, so some `M_(k+1) ∈ 𝓜` is not contained in it.
  - `M_(k+1) ∩ S_k` is `G`-normal and properly contained in `M_(k+1)`, so it is trivial.
  - Hence `τ` contains the infinite direct sum `⊕ M_i`, and `⊕_(i >= k) M_i` is an infinite
    strictly descending chain, which (S1) forbids.
- **Conclusion.** Take `Φ = ⋃_{M∈𝓜} (M − {1})`.

**2.** The first condition implies the second, which implies the third. For the converse, let
`f : G → I` be injective on `Φ`, with `I` isolated.
- **`f` is injective on `τ`.** `ker f ∩ τ` is normal in `G` and misses `Φ`, so it is
  trivial by 1.
- **An isolated group containing `G/τ`.** `G/τ` is residually finite (S2), hence linear over
  `Q` (`rf-soluble-minimax-groups-satisfy-permutational-bh`, via Pyber–Segal). So it embeds
  in an isolated group `I'` (`linear-and-metabelian-groups-embed-in-isolated-groups`).
- **The embedding.** `g ↦ (f(g), gτ)` is injective into `I × I'`, which is isolated by
  items 1 and 4 of `ascending-hnn-of-isolated-groups-embed-in-isolated-groups`. `∎`

**3.**
- **An isolated quotient.** By item 1 of `fp-groups-with-max-n-are-limits-of-isolated-groups`,
  there is `M ◁ P` maximal among normal subgroups disjoint from `Φ`. Then `P/M` is
  finitely discriminable. Under max-n, `M` is finitely normally generated, so `P/M` is
  finitely presented, hence isolated (CGP Prop. 2.2).
- **Injectivity.** `G ∩ M` is normal in `G` and misses `Φ`. So `G → P/M` is injective on
  `Φ`, and 2 applies. `∎`

## What remains, and what it implies

- **The one remaining problem.** CGP Question 4 for all finitely generated soluble minimax
  groups follows from a positive answer to:

  *Does every finitely generated soluble minimax group embed in a finitely presented group
  with max-n?*

  - A finitely presented soluble minimax overgroup would do.
  - This is the minimax analogue of the Baumslag–Remeslennikov theorem that every
    finitely generated metabelian group embeds in a finitely presented metabelian group,
    which satisfies max-n.
  - Its status was not found in the literature searched on 2026-09-18.
  - Kropholler–Lorensen (arXiv:1510.07583, abstract and main theorem read) cover every such
    group by a virtually torsion-free one, but with uncontrolled kernel. So covers do not
    answer it directly.
- **Obstruction check.** Every previously known obstruction for the non-residually-finite
  soluble inputs concerns locally moving or skew-product hosts
  (`hall-quotient-avoids-v-circle-groups-and-periodic-ends`,
  `compact-skew-products-cannot-carry-divisible-fiber-subgroups`). None applies to max-n
  arithmetic hosts.

## Lesson for general BH

**A Noetherian host turns approximation into embedding.**
- In a finitely presented group with max-n, every maximal normal subgroup avoiding a finite
  set is finitely normally generated. So every finite set survives in an *isolated* quotient.
- An input embeds in such a quotient as soon as its "invisible part" (the part no finite
  quotient sees, here the Chernikov radical) is discriminated by finitely many elements.
  Everything else is handled by residually finite, hence linear, means.

**Consequence for the soluble world.** Question 4 for soluble minimax inputs reduces to
finding finitely presented Noetherian overgroups, which is a classical kind of embedding
problem. Boone–Higman additionally needs those isolated quotients to embed in simple
groups: the per-input existential sentence of
`boone-higman-iff-isolated-hosts-and-local-boone-higman`.
