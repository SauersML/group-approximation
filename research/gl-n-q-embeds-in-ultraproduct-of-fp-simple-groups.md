---
rg: 2
id: gl-n-q-embeds-in-ultraproduct-of-fp-simple-groups
kind: claim
title: GL_n(Q) embeds in an ultraproduct of finitely presented simple groups, so the local form of the GL_n(Q) root holds and no universal sentence can refute it
distinct_from:
  gl-n-q-embeds-in-fp-simple-group: that asks for one finitely presented simple host; this gives only an ultraproduct of such hosts, one per finitely generated subgroup.
  rational-linear-groups-satisfy-boone-higman: that is Zaremsky's theorem for each finitely generated subgroup separately; this assembles those embeddings into one embedding of the whole countable group into an ultraproduct.
  local-boone-higman-iff-boone-higman: that shows the local and global forms coincide for finitely generated decidable inputs as a class; for the single non-finitely-generated input GL_n(Q) the local form is established here, while the global form is the open root.
---

**ESTABLISHED** by `gl-n-q-embeds-in-ultraproduct-of-fp-simple-groups-proof`
(elementary from Zaremsky's theorem; not independently reviewed; no novelty
claimed).

## Statement

Let `n >= 1`.

1. There are finitely presented simple groups `K_1, K_2, …` such that for every
   nonprincipal ultrafilter `U` on `N`, `GL_n(Q)` embeds in the ultraproduct
   `∏_U K_i`.
2. **Local root.** Every finite system `u_1(y) = 1, …, u_d(y) = 1,
   v_1(y) ≠ 1, …, v_k(y) ≠ 1` without constants that has a solution in `GL_n(Q)`
   has a solution in some finitely presented simple group.
3. **No universal refutation.** Every universal first-order sentence of group
   theory that holds in all finitely presented simple groups holds in `GL_n(Q)`.

## What this says about the root

- The root cannot be disproved by any universal property of finitely presented
  simple groups. A disproof would need information that no finite piece of
  `GL_n(Q)` carries. Examples: the divisibility of `(Q,+)` as a whole, or the
  finite presentation of every overgroup.
- Methods that realize each finitely generated subgroup of `GL_n(Q)` in its own
  host prove exactly this claim and no more. The open content of the root is
  uniformity: one host for the whole ascending union.
- For the simple inputs `SL_m(Q)`, `m` odd, the uniformity step collapses to a
  single existential sentence about any one finitely presented overgroup
  (`sl-odd-q-in-fp-simple-iff-fp-overgroup-maps-nontrivially`). The missing
  ingredient is a finitely presented overgroup whose image in a finitely
  presented simple group keeps one element alive. Local information does not
  supply it.
