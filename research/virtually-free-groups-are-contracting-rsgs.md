---
rg: 2
id: virtually-free-groups-are-contracting-rsgs
kind: claim
title: Every finitely generated non-elementary virtually free group, SL_2(Z) included, is a contracting rational similarity group with trivial nucleus, acting by Thompson-like maps
distinct_from:
  virtually-free-product-hyperbolic-groups-are-contracting-rsgs: that already makes every non-elementary virtually free group a contracting RSG, through the horofunction boundary of a free-product subgroup and the induced action; this gives a second, elementary proof by a Bass–Serre normal-form coding, and adds that the nucleus is trivial, so the group lies in V_{Γ,E}.
  contracting-rsgs-closed-under-finite-index-overgroups: that is the induced-action closure used by the existing proof; this proof does not pass to a finite-index subgroup.
  free-products-of-hyperbolic-groups-are-contracting-rsgs: that covers freely decomposable groups through the horofunction boundary; this covers the virtually free ones, including freely indecomposable groups such as SL_2(Z), directly.
  contracting-rsgs-closed-under-products-with-finite-groups: that handles finite normal subgroups that are direct factors; here a finite normal subgroup need not split (the center of SL_2(Z) does not), and it acts faithfully through the head syllable of the normal form.
  non-elementary-hyperbolic-groups-are-contracting-rsgs: that is BBMZ-hyperbolic Question 1.1 for all non-elementary hyperbolic groups (OPEN); its virtually free case was already settled on main.
  hyperbolic-groups-embed-in-contracting-rsgs: that is an embedding (after adding a free factor Z); this is an isomorphism with no factor added.
---

**ESTABLISHED** (route `virtually-free-contracting-rsg-proof`; lane proof by `bh-free-52`, elementary, not reviewed; no priority claimed, may be folklore).

**Statement.** Let `G` be a finitely generated virtually free group that is not virtually cyclic. Then there are a finite directed graph `Γ` whose subshift `Σ_Γ` has an irreducible core and a faithful action of `G` on a cone `E = C_r ⊆ Σ_Γ` with these properties:
- every element acts by a Thompson-like homeomorphism, so `G ≤ V_{Γ,E} ≤ R_{Γ,E}`;
- for every pair of cones `C_α, C_β ⊊ E` with `t(α) = t(β)`, some element of `G` maps `C_α` to `C_β` by the canonical similarity (`def:rsg`);
- the nucleus is `{id_{C_v}}`, one identity map per node.

So `G` is a contracting RSG in the sense of Belk–Bleak–Matucci–Zaremsky (arXiv:2309.06224v3, `def:contracting`) with trivial nucleus.

**Relation to main.** That `G` is a contracting RSG is already on main (`virtually-free-product-hyperbolic-groups-are-contracting-rsgs`). What this node adds:
- a second proof with no hyperbolic-group machinery: no horofunction boundary, no contracting lemma, no Webster–Winchester, no induced action;
- the trivial nucleus. By BBMZ's characterization of full RSGs by their nucleus, the full closure `[[G | E]]` is then `V_{Γ,E}` itself;
- a direct faithful realization of non-split finite normal subgroups, such as the center of `SL_2(Z)` or of `GL_2(Z)`, through the head syllable.

**Why the horofunction boundary is avoided (lane remark).** For `SL_2(Z)` with `S = {a^{±1}, b^{±1}}` (`a^4 = 1`, `a^2 = b^3 = z`), `z` acts trivially on `∂_h`. Each coset `x⟨z⟩` is an antipodal pair shared by one 4-cycle and one 6-cycle of the Cayley graph. In a 4-cycle both points of the other pair are adjacent, so for `|x| > n + 2` the functions `d_x` and `d_{xz}` agree on `B_n`. So BBMZ's route cannot realize `SL_2(Z)` faithfully with this generating set. The normal-form coding keeps the vertex-group element in front, and `z` changes it.

**Scope.** The proof uses two standard facts about minimal non-elementary group actions on trees, cited in the route. It says nothing about one-ended groups, or about graphs of groups with finite edge groups and infinite vertex groups. For the latter, the coding would need an infinite alphabet at infinite vertex groups; that is the open part of the infinitely-ended case of Question 1.1.
