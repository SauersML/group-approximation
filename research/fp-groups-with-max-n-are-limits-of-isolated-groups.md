---
rg: 2
id: fp-groups-with-max-n-are-limits-of-isolated-groups
kind: claim
title: A finitely presented group in which every normal subgroup is finitely normally generated (max-n) is a limit of isolated groups; more generally it suffices that for each finite set some maximal normal subgroup avoiding it is finitely normally generated
requires:
  - limits-of-isolated-groups-basic-closure
distinct_from:
  limits-of-isolated-groups-basic-closure: that gives LEF and isolated groups and products; this adds a class defined by the ascending chain condition on normal subgroups, which contains groups that are neither LEF nor isolated.
  every-decidable-group-is-a-limit-of-isolated-groups: that is the open question; this is a sufficient condition.
---

**ESTABLISHED** (lane proof below, elementary, not reviewed; no priority claimed; it is the proof
of Cornulier--Guyot--Pitsch Proposition 2.3, arXiv:math/0511714v2 p. 8, with finite presentation
tracked).

**Statement.** Let `G` be finitely presented.
1. For every finite `F ⊂ G − {1}` there is a normal subgroup `N_F` maximal among normal
   subgroups disjoint from `F`, and `G/N_F` is finitely discriminable.
2. If for every finite `F` some such maximal `N_F` is finitely normally generated, then `G` is a
   limit of isolated groups.
3. In particular this holds when `G` satisfies max-n (the ascending chain condition on normal
   subgroups, equivalently every normal subgroup is the normal closure of a finite set).

**Examples.** Finitely presented simple groups (isolated already), and `S ⋊ P` for `S` infinite,
finitely presented and simple and `P` finitely presented polycyclic. A normal `N` meets `S` in `1` or `S`;
in the first case `N` centralizes `S`, and `C(S)` embeds in the Noetherian group `P`, so max-n holds.
These are not LEF (they contain the non-residually-finite `S`). The direct products `S × P` with `P`
infinite are also not finitely discriminable (the subgroups `1 × P_j` for a chain of finite-index
normal subgroups `P_j` of `P` with trivial intersection avoid every finite set), so they are neither LEF
nor isolated.

**Proof.**
1. The set of normal subgroups disjoint from `F` is nonempty (it contains `1`) and closed under
   unions of chains, so Zorn's lemma gives a maximal element `N_F`. If `M/N_F` is a nontrivial
   normal subgroup of `G/N_F`, then `M ⊋ N_F` meets `F` by maximality; so the image of `F`, which
   consists of nontrivial elements, is a finite discriminating set of `G/N_F`.
2. If `N_F` is the normal closure of finitely many elements, `G/N_F` is finitely presented, hence
   isolated (CGP Proposition 2.2). It lies in the basic neighbourhood "all relators of `G` hold and
   all `f ∈ F` are nontrivial", so by item 4 of `limits-of-isolated-groups-basic-closure`, `G` is a
   limit of isolated groups.
3. Under max-n every normal subgroup is finitely normally generated.
