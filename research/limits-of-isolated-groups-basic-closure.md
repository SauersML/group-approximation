---
rg: 2
id: limits-of-isolated-groups-basic-closure
kind: claim
title: The limits of isolated groups contain every LEF group and every isolated group, are closed under finite direct products and independent of the marking, and a finitely presented group is such a limit iff it has F-avoiding isolated quotients for every finite F
distinct_from:
  every-decidable-group-embeds-in-an-isolated-group: that is Cornulier--Guyot--Pitsch Question 4, an embedding question; this is about approximation in the space of marked groups (their Questions 1--3).
  every-decidable-group-is-a-limit-of-isolated-groups: that is the open Question 1 itself; this records the elementary structure of the class it asks about.
---

**ESTABLISHED** (lane proof below, elementary, not reviewed; no priority claimed; the
facts are routine consequences of Cornulier--Guyot--Pitsch, arXiv:math/0511714v2).

**Setting.** `G_m` is the space of `m`-marked groups (Grigorchuk). A group is *isolated*
if it is an isolated point of some (equivalently every, CGP Lemma 1) `G_m`; by CGP
Proposition 2 this means finitely presented and finitely discriminable (a finite
`F ⊂ G − {1}` meets every nontrivial normal subgroup). Let `L` be the class of marked
groups lying in the closure of the isolated marked groups.

**Statement.**
1. **Marking independence.** Whether `(G, S)` lies in `L` depends only on the abstract group
   `G`.
2. **Examples.** Every isolated group and every finitely generated LEF group lies in `L`.
   In particular every finitely generated residually finite group does.
3. **Products.** If `G, H ∈ L` then `G × H ∈ L`.
4. **Finitely presented inputs.** Let `G` be finitely presented. Then `G ∈ L` iff for every
   finite `F ⊂ G − {1}` there is a finitely normally generated `N ⊴ G` with `N ∩ F = ∅`
   and `G/N` finitely discriminable.
5. **Strictness.** `L` strictly contains the union of the LEF groups and the isolated
   groups: for an infinite finitely presented simple `S`, `S × Z ∈ L`, but `S × Z` is
   not LEF (it contains the non-residually-finite finitely presented `S`) and not
   finitely discriminable (the normal subgroups `1 × nZ` avoid any finite set).

**Proof.**
1. CGP Lemma 1 (p. 2): for isomorphic marked groups `G_1 ∈ G_{m_1}`, `G_2 ∈ G_{m_2}` there
   are clopen neighbourhoods `V_i ∋ G_i` and a homeomorphism `φ: V_1 → V_2` with
   `φ(G_1) = G_2` and `φ(H) ≅ H` for all `H ∈ V_1`. Isolatedness is an isomorphism
   invariant, so `φ` carries isolated points of `V_1` to isolated points of `V_2`, and
   `G_1` is a limit of isolated points iff `G_2` is.
2. Isolated groups are trivially limits of themselves. A finitely generated group is LEF iff
   it is a limit of finite marked groups (Vershik--Gordon; direct: a local embedding
   `φ: B_{2R}(G) → Q` into a finite group gives the finite marked group
   `(⟨φ(S)⟩, φ(S))`, whose `R`-ball agrees with that of `G`), and finite groups are
   isolated.
3. If `(G_i, S_i) → (G, S)` and `(H_i, T_i) → (H, T)` with all `G_i, H_i` isolated, mark
   `G_i × H_i` by `S_i ∪ T_i`. A word `w` in `S ∪ T` is trivial in `G × H` iff its
   `S`-letters form a trivial word in `G` and its `T`-letters a trivial word in `H`
   (the two factors commute), and the same holds in `G_i × H_i`; so
   `(G_i × H_i, S_i ∪ T_i) → (G × H, S ∪ T)`. Products of isolated groups are isolated
   (CGP Theorem 7(1): the class is closed under extensions).
4. CGP Lemma 1.3(2): a finitely presented `G = ⟨S | R⟩` has the clopen neighbourhood
   "all `r ∈ R` hold", which consists of quotients of `G`; inside it the basic clopen
   sets are "every `f ∈ F` is nontrivial" for finite `F`. So `G ∈ L` iff each such set
   contains an isolated quotient `G/N`. Finite presentability of `G/N` is equivalent to
   `N` being finitely normally generated (CGP Lemma 1.3(2), (iii) ⟺ (iv)).
5. By 2 and 3, since `S` is isolated and `Z` is residually finite.
