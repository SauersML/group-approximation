---
rg: 2
id: cusp-extensions-of-rel-hyperbolic-groups-satisfy-pbh
kind: claim
title: Adding cusps E(g) x K along loxodromic elements keeps a relatively hyperbolic group in the permutational Boone--Higman class, torsion allowed
distinct_from:
  cusp-extensions-of-torsion-free-hyperbolic-groups-satisfy-pbh: that is one cusp on a torsion-free hyperbolic group, where E(h) is a centralizer; this allows torsion (E(h) is only a finite-index overgroup of a centralizer), several cusps, and a relatively hyperbolic base group.
  rel-hyperbolic-groups-with-bh-peripherals-satisfy-bh: that is the OPEN permanence statement for all peripheral structures; this proves it for peripheral structures obtained by cusp extension from a group already in B_A.
  pbh-coset-wreaths-iff-identity-edge-hnns: that is the general equivalence over one subgroup C; this applies it to maximal elementary subgroups and adds the relatively hyperbolic structure.
---

**ESTABLISHED** by `cusp-extensions-rel-hyperbolic-pbh-proof` (lane proof, not
reviewed; no priority claimed).

## Statement

Let `G` be a finitely generated group in `B_A`, hyperbolic relative to finitely
generated subgroups `P_1, ..., P_m` (`m = 0` allowed: `G` hyperbolic; torsion allowed).
Let `g_1, ..., g_n` be elements of infinite order, none conjugate into any `P_j`, and
pairwise non-commensurable (no nonzero powers of `g_i` and `g_k`, `i ≠ k`, are
conjugate). Let `E_i = E_G(g_i)` be the maximal elementary subgroups, and let
`K_1, ..., K_n` be finitely generated groups in `B_A`. Let `Γ` be the star amalgam

    Γ = G *_{E_1} (E_1 × K_1) *_{E_2} ... *_{E_n} (E_n × K_n).

1. `Γ ∈ B_A`. So `Γ` embeds in a finitely presented simple group.
2. `Γ` is hyperbolic relative to `{P_1, ..., P_m, E_1 × K_1, ..., E_n × K_n}`, and these
   peripheral subgroups all lie in `B_A` when the `P_j` do.
3. `A wr_(G/E_i) G ∈ B_A` for every `A ∈ B_A`.

Since `Γ` again satisfies the hypotheses, cusp extensions can be iterated.

## Examples

- **Hyperbolic groups with torsion** (`m = 0`), for example `H *_{E(h)} (E(h) × V)` with
  `H` a hyperbolic triangle group.
- **Linear bases.** `G = π_1(M)` for a finite-volume hyperbolic `n`-manifold, or a limit
  group, is linear in characteristic zero and hence in `B_A`
  (`char-zero-linear-groups-satisfy-permutational-boone-higman`). Adding a cusp
  `E(γ) × K` along a closed geodesic, with `K` non-linear (Thompson's `V`, say), gives a
  relatively hyperbolic group that is not linear.
