# Euclidean Artin groups via toric arrangements: what bundles can and cannot reach

Lane bh-verify-artin, free mode, 2026-09-18. These are lane proofs, not reviewed. The
source read was Bibby--Delucchi, arXiv:2202.11996v2: the PDF was fetched, and pages 1–18
and 24–29 were read.

## Landed nodes

| Node | Content |
|---|---|
| `free-kernel-extensions-stay-in-the-permutational-class` | (f.g. free, rank >= 2)-by-`B_A` groups are in `B_A`. The same holds for centreless kernels with `Aut ∈ B_A`, for iterates, and for bundles over aspherical bases. |
| `fiber-type-toric-arrangement-groups-lie-in-the-pbh-class` | `π_1` of every fiber-type (supersolvable) toric or elliptic arrangement complement is in `B_A`. |
| `euclidean-artin-toric-commensurability` | `A(X̃) ∈ B_A` iff `π_1(toric Weyl complement of X) ∈ B_A`. This reproves C̃_n (and Ã_n). |
| `weyl-toric-arrangements-b-d-e-f-are-not-fiber-type` | The B_n (n >= 3), D_n (n >= 4), E and F_4 toric arrangements are not fiber-type for any lattice. |

So the open Euclidean types D̃_n, Ẽ_6, Ẽ_7, Ẽ_8 and F̃_4 now have an explicit
target: the toric complement groups. For D_n with `L = Z^n` this is

    N_D = {v ∈ (C^×)^n : v_i ≠ v_j and v_i v_j ≠ 1 for i ≠ j}.

Toric projections cannot fibre `N_D`. The same is true of the B_n complement
`N_B = N_D ∩ {v_k ≠ 1}`, and Li--Roushon nevertheless fibred `N_B` nonlinearly, after
the Möbius map `v ↦ (v+1)/(v−1)`.

## Why the Li--Roushon trick does not transfer to D̃_n

**The inversions.** The inversions `σ_k: v_k ↦ v_k^(-1)` preserve both `N_D` and
`N_B`. The fixed locus of `σ_k` is `D_k = {v_k = ±1}` in `N_D`, and `{v_k = −1}` in
`N_B`: "strand `k` at a cone point" of the orbifold picture.

**Lemma (invariant maps cannot be submersions).** Let `k ≠ k'`, and let
`p: N_D -> B` be holomorphic with `p ∘ σ_k = p = p ∘ σ_(k')` and `dim B = n − 1`. Then
`p` is not a submersion at any point `x` with `v_k(x) = 1` and `v_(k')(x) = −1`. Such
points exist in `N_D` for `n >= 2`.

*Proof.* `dσ_k` at `x` is `−1` on the `v_k` direction and `+1` elsewhere, because
`d(1/v)/dv = −1` at `v = 1`. From `dp_x ∘ dσ_k = dp_x` we get `dp_x(∂_(v_k)) = 0`,
and likewise `dp_x(∂_(v_(k'))) = 0`. So `rank dp_x <= n − 2`. The point `x` lies in
`N_D`, because `1 ≠ (−1)^(±1)`. ∎

In `N_B` the loci `{v_k = −1}` are pairwise disjoint: two strands at `−1` would
coincide. So the lemma never bites there.

Li--Roushon's map depends on the strands through `y_k^2` for `k >= 2`, so it is
invariant under the corresponding sign changes. That is exactly the structure that
has no room in `N_D`, where the two cone points `±1` can be occupied simultaneously.

**Consequence.** Any fibration of `N_D` (or of a finite cover) with free fibres must
break the inversion symmetry. In the orbifold language, the two cone points of the
D̃_n picture (Allcock) must be treated asymmetrically.

## Other structure, recorded for the next attempt

1. **N_D is N_B with n disjoint divisors filled back in.**
   `N_D \ N_B = ⊔_k E_k` with `E_k = {v_k = 1}`, and the union is disjoint. Each
   `E_k ≅ N_B^(n−1)`, the B̃_(n−1) toric complement. So
   `π_1(N_D) = π_1(N_B)/⟨⟨μ_1, …, μ_n⟩⟩`, where `μ_k` is a meridian of `E_k`, and
   `π_1(N_B)` is in `B_A` by the B̃_n theorem. Membership in `B_A` does not pass to
   quotients, so this needs a section or a kernel-control argument. A homomorphic
   section would give D̃_n at once.
2. **Homogenized projective model.** Put the cone points at `0` and `∞` of `P^1` and
   the puncture at `±1`. Then
   `N_D × C^× ≅ {w ∈ (P^1)^(n+1) : w_0 ∈ C^×, w_i ≠ ±w_j}`. The Li--Roushon space
   `Y_(n+1)` is the open subset where every `w_i` is finite. So D̃_n is B̃_n with the
   point `∞` promoted from a puncture to a second cone point.
3. **Euler characteristic check.** `χ(A(X̃_n)) = (−1)^n` from the Salvetti complex,
   so `χ(N_D) = (−1)^n |W(D_n)|/2`. A fibre tower with punctured-`C^×` fibres of
   puncture counts `ℓ_i` would need `∏ ℓ_i = 2^(n−2) n!`. This is not an obstruction,
   only a constraint on a nonlinear tower.

## Direction of this lane after landing

Look for a non-invariant nonlinear fibration of `N_D`, or of `N_D × C^×`, with free
fibres, following Li--Roushon but breaking the `v ↦ v^(-1)` symmetry.
