---
rg: 2
id: z2-free-z-embeds-in-a-finite-nucleus-rsg
kind: claim
title: The free product Z^2 * Z embeds in some rational similarity group with finite nucleus
distinct_from:
  z2-free-z-does-not-embed-in-thompson-v: that is Bleak--Salazar-Díaz's theorem for one finite-nucleus RSG, Thompson's V, whose nucleus consists of identity maps; this asks the same question for every finite-nucleus RSG, including Röver--Nekrashevych groups of contracting self-similar groups and the full RSGs that host hyperbolic groups.
  hyperbolic-groups-embed-in-contracting-rsgs: that puts every hyperbolic group in a full, contracting RSG; Z^2 * Z is the simplest group that is not hyperbolic but is hyperbolic relative to an abelian subgroup, so this is the first test of whether the BBMZ host class reaches past hyperbolic groups.
  closed-mcg-finite-index-subgroups-do-not-embed-in-v: that combines Koberda with Bleak--Salazar-Díaz to exclude V as a host for closed-surface mapping class groups; a negative answer here would exclude the whole BBMZ host class in the same way.
  finite-nucleus-rsg-abelian-stabilizers-have-rank-one-germs: that is one constraint on how Z^2 can sit in such a group; this is the embedding question itself.
artifacts:
  - research/artifacts/gq-bh-bh-hhg-bbmz-method-for-hhgs.md
---

**OPEN.** Is there a rational similarity group `G ≤ R_{Γ,E}` with finite nucleus,
in the sense of Belk--Bleak--Matucci--Zaremsky (BBMZ), arXiv:2309.06224v3, that
contains a subgroup isomorphic to `Z^2 * Z = ⟨a, b, c | [a,b]⟩`?

`Z^2 * Z` itself satisfies Boone--Higman: it is a right-angled Artin group, hence
linear over `Z`. This node is about the reach of the BBMZ method, not about
`Z^2 * Z`.

## Why it is the sharp test for the BBMZ method beyond hyperbolic groups

- **The method.** BBMZ embed a group in a full, contracting RSG
  (`thrm:hyp_to_contracting`). Contracting RSGs embed in finitely presented simple
  groups (`thrm:rsg_to_simple`, `prop:contr_to_simple`). BBMZ note that
  embedding in a contracting RSG already gives an embedding in a full, contracting
  one. So any group that embeds
  in no finite-nucleus RSG is out of reach of the method, whatever Cantor action is
  used.
- **What a negative answer excludes.** Every group containing `Z^2 * Z`. That
  includes:
  - every finite-index subgroup of the mapping class group of a closed surface of
    genus `g ≥ 2`, by Koberda, as recorded in
    `closed-mcg-finite-index-subgroups-do-not-embed-in-v`;
  - `Z^2 * Z` itself, which is hyperbolic relative to `Z^2`. BBMZ name
    "relatively hyperbolic groups with nice peripheral subgroups" as a natural
    next class for their techniques;
  - every group containing a right-angled Artin group on a graph with an edge and
    a vertex outside its star, for example `Z^2 * Z` inside many RAAGs, CAT(0)
    and hierarchically hyperbolic groups.
- **What a positive answer would show.** The main obstruction family recorded on
  main for the closed-surface case, via `V`, does not extend to the BBMZ host
  class. The open part of Problem 5.3(2) of arXiv:2306.16356v3 would then have no
  known obstruction on this route.

## What is known

1. **`V` is excluded.** `V` is a full RSG over the full binary shift with nucleus
   the identity maps of cones (BBMZ: Röver--Nekrashevych groups `V_d(H)` of
   finite-state self-similar `H` are full RSGs, and `V = V_2(1)`). It contains no
   `Z^2 * Z` (`z2-free-z-does-not-embed-in-thompson-v`).
2. **Constraint on the `Z^2`.** At every rational point fixed by a finite-index
   subgroup of `⟨a,b⟩`, some nontrivial element of that subgroup is the identity
   nearby (`finite-nucleus-rsg-abelian-stabilizers-have-rank-one-germs`). A
   product-type action, with `a` and `b` contracting towards a common rational
   point along independent directions, is therefore impossible. This is the model
   that puts `Z^2 * Z` in the Brin--Thompson group `2V`, whose natural coding has
   infinite nucleus (see the artifact).
3. **Equicontinuous directions (sketch, one case).** Suppose `a` acts on a binary
   cone as the binary odometer, which a nucleus can contain. Every homeomorphism
   commuting with it there is a translation of `Z_2`, and a rational one is a
   translation by an element of `Z_(2)`. So `⟨a, b⟩` restricted to that cone has
   rank at most `1`. Only this case is sketched (artifact §4); general codings of
   equicontinuous parts are not treated.
4. **Free products and ping-pong.** Items 2 and 3 say that, locally, `Z^2` acts
   through rank-one groups. The Bleak--Salazar-Díaz argument for `V` runs through
   the dynamics of elements of `V` (revealing pairs). The missing input for a
   negative answer is an analogue of that dynamics for elements of a finite-nucleus
   RSG: a decomposition of each element into finite-order, equicontinuous and
   attracting--repelling parts, with rational attracting points.

## Attempts

1. **bh-hhg, 2026-09-18.** Items 2 and 3 above. No construction and no proof of
   non-embedding. The stall is item 4: there is no revealing-pair theory for
   finite-nucleus RSGs.
