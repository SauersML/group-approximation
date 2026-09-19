---
rg: 2
id: lef-groups-are-torus-surjunctive
kind: claim
title: Over every LEF group, injective torus automata have non-zero-divisor degree matrices and are surjective
distinct_from:
  torus-automata-over-rf-or-domain-groups-are-surjunctive: that uses invariance of domain on periodic invariant tori, available only for residually finite groups (or d = 1 over domains); this uses exact finite models that are not invariant submanifolds, together with a dimension-free small-fibre lemma, and covers locally finite and other non-residually-finite groups at every d.
  torus-degree-regular-on-prime-power-residual-support: that derives regularity from epsilon(D) when <supp D> is residually prime-power, for arbitrary G; this assumes G is LEF, puts no condition on supp D, and sees all of phi(D), not only its augmentation.
  injective-torus-automata-have-regular-degree: that is the statement for every group; this proves it for the LEF class, including every locally finite group, where the w9 record had placed the smallest open hosts.
  every-group-is-torus-surjunctive: that is torus surjunctivity for every group; this is the LEF case, plus invertibility of the degree matrix in every fine finite model.
artifacts:
  - research/artifacts/lef-torus-small-fibre-2026-09-18.md
---

Let `G` be LEF: for every finite `K ⊆ G` there are a finite group `Q` and an injective
`phi: K -> Q` with `phi(ab) = phi(a) phi(b)` whenever `a, b, ab in K`. Let `d >= 1` and
let `tau: (T^d)^G -> (T^d)^G` be injective, continuous and `G`-equivariant, with degree
matrix `D in M_d(Z[G])` (`tau^*(xi) = xi D` on `H^1 = Z[G]^d`). Then:

1. There are finite `W, F ⊆ G` such that, for every LEF model `phi: K -> Q` with
   `K ⊇ W ∪ F ∪ WF`, `phi(D)` is invertible in `M_d(Z[Q])`.
2. `D` is a two-sided non-zero-divisor in `M_d(Q[G])`. In particular
   `xi -> xi D` is injective on `Q[G]^d`, which is C2
   (`injective-torus-automata-have-regular-degree`) for `G`.
3. `tau` is surjective, hence a homeomorphism.

Key input (Theorem 1 of the artifact): a continuous `f: T^N -> T^N` with fibres of
sup-diameter at most `1/16` is onto and `f^*` is an automorphism of `H^1(T^N; Z)`, for
every `N`.

**Hosts.** These include:
- every locally finite group, such as `Q/Z`, `Z(2^inf) x Z(3^inf)` and `Alt_fin(N)`;
- every locally residually finite group, such as abelian and linear groups;
- `FSym(Z) ⋊ Z`, which is finitely generated, LEF and not residually finite.

**ESTABLISHED 2026-09-18** by [[lef-groups-are-torus-surjunctive-proof]]. The proof is
not yet independently reviewed.

## Attempts

- 2026-09-18 (swarm-0917-w10-w10-gs-follow): proof in artifact Sections 2 and 3.
  - Section 4 lists the hosts and proves that finitely presented LEF groups are
    residually finite.
  - Section 5 is Theorem 3, the obstruction to a defect-tolerant (sofic) version.
