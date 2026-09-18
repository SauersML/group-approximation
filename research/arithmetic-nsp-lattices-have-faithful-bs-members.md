---
rg: 2
id: arithmetic-nsp-lattices-have-faithful-bs-members
kind: claim
title: A commensurator element with no power in the lattice gives a faithful Hecke HNN extension of any torsion-free lattice with the normal subgroup property
distinct_from:
  bs-class-with-faithful-member-lies-in-type-a-class: that turns one faithful member of BS_G into B_A for the whole class; this supplies faithful members for non-amenable, non-scale-invariant G.
  free-generalized-bs-groups-have-type-a-overgroups: that is G = F_k, where faithfulness comes from free-group combinatorics; this uses the normal subgroup theorem and a commensurator element instead.
  higher-rank-lattice-normal-subgroups-central-or-finite-index: that is Margulis's dichotomy for normal subgroups; this consumes it to rule out every nontrivial kernel of a Bass--Serre action.
---

**ESTABLISHED** through `arithmetic-nsp-faithful-bs-member-proof` (lane proof,
elementary apart from the cited normal subgroup theorems; not independently
reviewed; no priority claimed).

**Lemma.** Let `L` be a locally compact, second countable group and `G <= L` a
finitely generated discrete subgroup with finite covolume (a lattice). Assume:
- (N) every normal subgroup of `G` is trivial or has finite index;
- (C) every finite-index subgroup of `G` has trivial centralizer in `L`;
- `c ∈ L` commensurates `G`, and `c^m ∉ G` for every `m >= 1`.

Put `G_1 = G ∩ c^{-1}Gc` and `H_c = ⟨G, t | t x t^{-1} = c x c^{-1}, x ∈ G_1⟩`.
Then `H_c ∈ BS_G`, and `H_c` acts faithfully on its Bass--Serre tree.

**Instances.** Each satisfies (N), (C) and has such a `c`.
1. `G` a torsion-free finite-index subgroup of `SL_n(Z)`, `n >= 3`, in
   `L = PGL_n(R)`, with `c = diag(r, 1, ..., 1)` for a prime `r`.
2. `G` a torsion-free finite-index subgroup of `Λ = O[1/pq]^× / Z[1/pq]^×`, where
   `D` is a definite quaternion algebra over `Q` split at the primes `p ≠ q` and
   `O` is a maximal order. Here `L = PGL_2(Q_p) × PGL_2(Q_q)`, where `Λ` is a
   cocompact lattice acting on the product of two Bruhat--Tits trees. `c ∈ D^×(Q)`
   is any element whose image in `PGL_2(Q_r)` is hyperbolic on the Bruhat--Tits
   tree, for a prime `r ∉ {p, q}` at which `D` splits.

**Consequences.** By `bs-class-with-faithful-member-lies-in-type-a-class`, every
group in `BS_G` lies in `B_A` for these `G`. In particular every finite graph of
groups whose vertex and edge groups are commensurable with `SL_n(Z)`, `n >= 3`,
with finite-index edge inclusions, embeds in a finitely presented simple group.
BLIW state "the only obstruction for applying Theorem C that we are currently aware
of is that any G satisfying its hypotheses must be residually finite". These
instances are residually finite non-amenable examples, beyond their list of
strongly scale-invariant groups and free groups.

**Scope.** Instance 2 for three or more primes needs Margulis's normal subgroup
theorem for S-arithmetic groups in place of the two-factor input. That theorem is
not on main, so the instance is not claimed here.
