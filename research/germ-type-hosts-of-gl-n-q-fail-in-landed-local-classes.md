---
rg: 2
id: germ-type-hosts-of-gl-n-q-fail-in-landed-local-classes
kind: claim
title: Localization (MT-A) - every landed class of germ-type, circle, line, almost-V and tree host fails for GL_n(Q) or its stepping stones through one of its local groups
distinct_from:
  germ-extensions-omit-standard-gl-n-q: that is one assembled input, for piecewise-projective and piecewise-affine bases; this is the conjunction of all twelve landed germ-type exclusions.
  gl-n-q-embeds-in-fp-simple-group: that is the open root; this collects the germ-type host classes excluded for it.
artifacts:
  - research/artifacts/gq-gq-critic-2.md
---

**ESTABLISHED (assembly)** through `germ-type-hosts-of-gl-n-q-fail-in-landed-local-classes-assembly`. The
established part is the conjunction of twelve landed claims, abbreviated from their statements. Each node has
the exact hypotheses, and no new proof is given here. The heuristic reading at the end is **not** claimed.
Source: critic pass 2, `research/artifacts/gq-gq-critic-2.md` §3, MT-A.

## Established part

1. **Circle and interval groups.**
   - `pp-circle-divisible-subgroups-act-freely`: take a group of circle homeomorphisms that are piecewise in
     a projective or affine group without divisible subgroups. Its divisible abelian subgroups act freely,
     and their normalizers are their centralizers.
   - `circle-groups-with-divisible-free-germs-omit-gl-n-q`: suppose every point-germ group of a circle or
     interval group has no divisible subgroup. Then `GL_n(Q)`, `Aff(Q)` and `U_3(Q)` do not embed, even with
     breakpoints accumulating at singular points.
2. **Piecewise hosts.**
   - `piecewise-commutative-linear-hosts-miss-linear-gl-n-q`: take a finitely generated group of
     homeomorphisms piecewise in a topologically free group linear over a commutative ring. It contains no
     linearly acting divisible group, so no linear copy of `GL_n(Q)`.
   - `germ-extensions-omit-standard-gl-n-q`: groups locally in a finitely generated piecewise-projective or
     piecewise-affine group off a nowhere dense set contain no standard copy of `GL_n(Q)`. This includes all
     finite germ extensions of such a group.
3. **Germ groups.**
   - `periodic-point-germ-groups-omit-aff-q`: take finite products of finitely generated germ groups that
     commensurate the local contractions at eventually periodic points. They contain no `Aff(Q)`, `SL_2(Q)`
     or `PSL_2(Q)`.
   - `commensurating-end-germ-groups-omit-aff-q`: the same holds for finitely generated groups of dyadic PL
     end-germs commensurating the germ of `x -> x+1`.
   - `rational-slope-germ-groups-have-bs-but-no-heisenberg`: germs with rational asymptotic slope contain
     every `BS(1,m)`, but no nonabelian nilpotent group.
4. **Almost-V hosts.**
   - `almost-v-fw-subgroups-act-through-finitely-many-germs`: take an FW group of Cantor homeomorphisms
     locally in `V` off finite sets. Modulo a subgroup of `V`, it virtually acts through its germs at finitely
     many fixed points.
   - `gl-n-q-almost-v-hosts-need-lattice-germs`: a finitely generated almost-V host of `GL_n(Q)`, `n >= 3`,
     has one singular germ group that contains a finite-index subgroup of every `SL_3(Z[1/m])`.
   - `normal-germ-extensions-of-thompson-v-contain-no-sl3z`: finite germ extensions of Higman–Thompson
     groups with normalizing or finite-index germs contain no finite-index subgroup of `SL_3(Z)`.
5. **Trees.** `aperiodic-tree-almost-automorphism-fg-subgroups-are-rf`: take a rooted tree whose branching
   is not eventually periodic. Every finitely generated group of its almost automorphisms is residually
   finite, so it contains no `(Q,+)`.
6. **Type (A) germs.** `type-a-orbit-accumulation-forces-fg-nontrivial-germs`: in a type (A) action by
   homeomorphisms, a point whose orbit accumulates at it has a nontrivial finitely generated germ group.

## Heuristic reading (not claimed)

- **The unifying principle.** The critic reads items 1–6 as one principle, "no base case".
  - For `n = 2`, an embedding of `Aff(Q)` puts a nontrivially normalized divisible `(Q,+)` into one local
    group: a piece group, a point-germ group, or the germ group at infinity.
  - For `n >= 3`, the chain `SL_3(Z[1/m])` lands in one singular germ group.
  - So a germ-type host would host `GL_n(Q)` only if one of its local groups already did.
- **What is proved.** Items 1–6 prove this only for the classes listed. No general localization theorem is
  claimed.
- **The critic's consequence.** A finitely presented germ-type host would have to implant, as a germ group,
  a finitely presented group that already contains the configuration. It would also have to keep the finitely
  presented germ stabilizers that the Belk–Hyde–Matucci criterion needs. Such groups exist, for example
  `St_N(R_L)` (`gl-n-q-explicit-natural-fp-overgroup`). No node proves or refutes that the implant can be
  made.
