---
rg: 2
id: perfect-subgroups-are-locally-trivial-in-abelian-germ-hosts
kind: claim
title: In a host whose point germs are torsion-free abelian (V, Higman--Thompson, Brin--Thompson nV, boundary Thompson groups), a finitely generated subgroup with finite rational abelianization is locally nontrivial at only finitely many of its fixed points; so closed mapping class groups of genus >= 4 cannot carry curve data at curve-indexed points of any such host
distinct_from:
  bhm-corollary-hosts-over-v-are-cover-centralizer-groups: that locates the germ groups that Belk--Hyde--Matucci can certify over V, at the singular points; this is about the nonsingular points, where perfect subgroups must be locally trivial, and holds for every host with abelian point germs, certified or not, including nV.
  closed-mcg-pair-orbit-finite-actions-have-large-stabilizers: that constrains the stabilizers of a type (A) action of a closed mapping class group; this constrains the local dynamics of any action by base-local maps, and says nothing about orbits of pairs.
  closed-mcg-finite-index-subgroups-do-not-embed-in-v: that excludes V itself through Koberda's Z^2 * Z; this applies to germ extensions of V and to nV, which that argument does not reach, and excludes a class of designs rather than all embeddings.
  deligne-forms-are-singular-on-commuting-parabolic-diagonals: that shows one family of normal-form boundaries is not thin; this is a structure theorem for every action by base-local maps with abelian point germs.
artifacts:
  - research/artifacts/gq-bh-bh-free-51-garside-and-mosher-thinness.md
---

**ESTABLISHED** by `perfect-subgroup-local-triviality-proof` (lane proof, elementary apart
from standard mapping class group facts recalled there; not independently reviewed; no
priority claimed).

## Setting

- `X` is a Hausdorff space and `B ≤ Homeo(X)` a **base** whose germ group `(B)_q` at every
  point `q` is torsion-free abelian.
  - Examples: Thompson's `V` and the Higman--Thompson groups, with germ `Z` at rational
    points and `1` elsewhere.
  - Brin--Thompson `nV`, with germ `Z^k`.
  - The boundary Thompson group of any regular path space
    (`germ-rate-homomorphism-tests-germ-extension-finiteness` §1).
- `G ≤ Homeo(X)` acts by **base-local maps off finite sets**: every `g ∈ G` agrees near each
  point outside a finite set `sing(g)` with some element of `B`. Two cases:
  - every subgroup of a finite germ extension of `B` in the Belk--Hyde--Matucci sense;
  - `G ≤ B` itself, with all `sing(g) = ∅`.
- `J ≤ G` is finitely generated with `H_1(J; Q) = 0`, for example perfect. Write
  `N_J = Fix(J) ∖ int Fix(J)`: the fixed points of `J` near which `J` is not the identity.

## Statement

1. **Finitely many special points.** `N_J` is contained in `⋃_i sing(j_i)` for any finite
   generating set `(j_i)` of `J`, so it is finite. The centralizer `C_G(J)` permutes `N_J`, and
   a finite-index subgroup of `C_G(J)` fixes `N_J` pointwise.
2. **Without singular points it is clopen.** If `G ≤ B`, for example `G ≤ V` or `G ≤ nV`,
   then `N_J = ∅`, so `Fix(J)` is clopen.
3. **Transport.** If `ψ ∈ C_G(J)`, `p ∈ Fix(J)` and the points `ψ^n p`, `n ≥ 0`, are pairwise
   distinct, then `J` is the identity on a neighbourhood of `p`.
4. **Closed mapping class groups have no curve points.** Let `g ≥ 4` and let `Mod(S_g)` act
   on `X` by base-local maps off finite sets. Let `d ↦ p_d` be an injective map on the
   `Mod(S_g)`-orbit of a nonseparating curve `d` with:
   - equivariance, `p_{φd} = φ(p_d)`;
   - `Stab^+(d)` fixing `p_d`, where `Stab^+(d)` is the stabilizer of `d` with its
     orientation.

   Then `Stab^+(d)`, and in particular the Dehn twist `T_d`, acts as the identity on a
   neighbourhood of `p_d`.

   For a finite-index subgroup `L` in place of `Mod(S_g)`, the argument gives less. Each
   `L ∩ Mod(S ∖ R)`, for `R` a one-holed torus containing `d`, acts as the identity near
   `p_d`, provided it has finite rational abelianization. Ivanov's conjecture predicts this
   finiteness for all `L`; for `L` containing the Torelli group it is Hain's theorem
   (recalled). Whether a power of `T_d` then acts trivially near `p_d` is not claimed.

## Consequences

- **Exploded designs with twist poles are impossible in rank-one hosts.** Any design for
  closed `Mod(S_g)` in `V`, a germ extension of `V`, `nV`, or a normal-form boundary host
  that puts, at points attached equivariantly to curves, a twist direction on which `T_d`
  acts nontrivially fails. Examples are the two poles of a "twist line" for each curve.
  - The obstruction does not need BHM's hypotheses, and does not need finite presentation.
  - It needs only the finiteness of singular sets and the abelian point germs of the base.
- **Where curve data can live.** Only in fixed-point-free form: for instance odometer-type
  pieces, where no point is fixed by `Stab^+(d)`, as in the odometer lift of
  `odometer-lift-central-extensions-of-v-subgroups-into-2v-tau`. Or at the finitely many
  special points `N_J`, where the germ group must be nonabelian: by
  `bhm-corollary-hosts-over-v-are-cover-centralizer-groups` it lies inside `C(C,Z) ⋊ V` for
  certified hosts over `V`. Or in a host with nonabelian point germs, such as the
  `GL(Z)`-germ host `𝒯_m` of `closed-mcg-embeds-in-rational-projective-full-group`, to which
  none of this applies.
- **A necessary condition for `Mod(S_g) ≤ nV`.** In any such embedding with `g ≥ 4`, every
  subsurface group `Mod(S ∖ R)` with complement of genus `≥ 3` has clopen fixed set.
  Compare `closed-mcg-in-nv-forces-braid-groups-in-nv`.

## Scope

- Item 4 is an obstruction to a class of designs: equivariant curve-indexed fixed points. It
  does not exclude an embedding of `Mod(S_g)` in any of these hosts.
- For `g ≤ 3` the subsurface groups used are not perfect, and nothing is claimed.

## Lesson for general BH

- **Perfect inputs see only nonabelian germs.** In every host with abelian point germs, a
  finitely generated perfect subgroup is locally trivial at all but finitely many of its
  fixed points. Those finitely many points must be singular points with nonabelian germ
  groups.
- **Consequences for the design of hosts:**
  - Hosts for perfect-rich inputs, such as closed mapping class groups, `Out(F_n)`, and
    lattices with perfect parabolic pieces, must carry the local structure of their perfect
    subgroups either at finitely many singular points, or by fixed-point-free
    (odometer-like) dynamics, or in a host with nonabelian point germs.
  - Rank-one "exploded boundaries" whose points are indexed by curves, subsurfaces or
    parabolic cosets cannot work.
  - This is a cheap first test for any proposed Cantor host: compute the point germs, and
    check whether the input's perfect subgroups can be locally trivial at the points they
    fix.
