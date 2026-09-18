---
rg: 2
id: kazhdan-simple-groups-act-only-on-exotic-2d-buildings
kind: claim
title: A finitely generated group with property (FA) and no nontrivial finite quotient acts trivially on every locally finite tree and every Bruhat–Tits building, so in building-coded hosts it can only act through exotic 2-dimensional factors, where a word problem outside EXP needs a non-discrete automorphism group
distinct_from:
  degree-coboundary-subgroups-of-coded-full-groups-are-rf: that constrains inputs of any finitely coded host through the degree cocycle; this constrains which geometry a geometric (building-coded) host can use for the hard inputs, through linearity and fixed points.
  euclidean-building-lattices-lie-in-permutational-bh-class: that is the positive host theorem for lattices; this says which buildings such hosts must use to carry simple Kazhdan inputs at all, and when those inputs are forced to have easy word problem.
  decidable-host-classes-reduce-to-canonical-kazhdan-groups: that names the canonical inputs H_Γ every universal host class must contain; this applies its Kazhdan filter to geometric codings over Euclidean buildings.
---

**ESTABLISHED** for items 1–3, given the cited imports. Lane proof, elementary; not reviewed; no priority
claimed. Item 4 is a consequence recorded with its dependence on an open question.

## Setting

- `K` is finitely generated, has property (FA), and has no nontrivial finite quotient.
  - Examples: every infinite finitely generated simple Kazhdan group, in particular every canonical input
    `H_Γ` of `decidable-host-classes-reduce-to-canonical-kazhdan-groups`. Kazhdan implies (FA) by
    Watatani.
  - Also every infinite finitely generated quasisimple Kazhdan group. A finite-index normal subgroup has
    image `1` or everything in the simple quotient by the centre, and perfection excludes both.
  - Such a `K` has no nontrivial residually finite quotient.
- `X = X_1 × ⋯ × X_m` is a locally finite Euclidean building with thick irreducible factors. Trees are
  allowed as factors.

**Imports** (context only, not re-read at source unless marked):
- (I1) *Classification.* A locally finite thick irreducible Euclidean building of dimension `≥ 3` is
  Bruhat–Tits. Tits; Weiss, *The Structure of Affine Buildings*.
  - An `Ã_2`-building is Bruhat–Tits iff its projective plane at infinity is Moufang. The locally finite
    ones are exactly those of `PGL_3(D)`, for `D` a finite-dimensional division algebra over a local field.
    This is quoted in Radu, arXiv:1703.10495, §1, read at source, citing Weiss, Chapter 28.
- (I2) *Automorphisms.* Let `X_i` be the Bruhat–Tits building of an absolutely almost simple group over a
  local field `k`, or over `D`.
  - Then `Aut(X_i)` has a normal subgroup `L_i`, the image of the adjoint group, which is a linear group
    over `k`.
  - The quotient `Aut(X_i)/L_i` embeds in `Aut(k) × F`, with `F` finite (diagram and duality automorphisms).
  - `Aut(k)` is finite for `k` of characteristic 0 and profinite for `k = F_q((t))`, so the quotient is
    residually finite.
  - Source: Tits, on the semilinear automorphism groups of Moufang spherical buildings.
- (I3) *Products.* `Aut(X)` contains `∏ Aut(X_i)` with finite index, the quotient permuting isomorphic
  factors.
- (I4) *Malcev.* Finitely generated linear groups are residually finite.
- (I5) *Fixed points.* A vertex stabilizer of a locally finite building acts on every ball through a finite
  group, so it acts faithfully only through a residually finite group.

## Statement

1. **Trees.** Every homomorphism `K → Aut(T)`, `T` a locally finite tree, is trivial.
2. **Bruhat–Tits buildings.** Every homomorphism `K → Aut(X_i)`, `X_i` Bruhat–Tits, is trivial. By (I1)
   this covers every factor of dimension `≥ 3`.
3. **Products.** Every action of `K` on `X` preserves each factor. It is trivial on all tree factors and
   all Bruhat–Tits factors. So `K` acts nontrivially on `X` only through its *exotic 2-dimensional* factors:
   the non-Bruhat–Tits `Ã_2`-, `C̃_2`- and `G̃_2`-buildings. It acts on each of them faithfully or
   trivially when `K` is simple.
4. **Consequence for building-coded hosts.** Let `Λ` act cocompactly and faithfully on `X`. Examples are
   the orbit-category hosts of `euclidean-building-lattices-lie-in-permutational-bh-class`, its product
   version (bh-lattices), and the infinite-stabilizer variant planned for S1b. Let `K ≤ Λ` be nontrivial.
   - (a) `X` has an exotic 2-dimensional factor `X_e` on which `K` acts nontrivially with no fixed vertex.
   - (b) Suppose `Aut(X_e)` is discrete. Then the image of `K` is a subgroup of the discrete cocompact group
     `Aut(X_e)`, which is a cocompact lattice on an irreducible Euclidean building. That lattice lies in
     the full group of a finitely coded groupoid with *finite* units, so every finitely generated subgroup
     has word problem solvable in exponential time
     (`finite-k-graph-full-groups-have-exponential-word-problem`, with the finite-unit count of
     `finitely-coded-cantor-actions-give-type-a-hosts`, Limits). When `K` is simple, it acts faithfully,
     so `WP(K)` is in EXP.
   - (c) So a building-coded host can carry a simple Kazhdan input whose word problem is not in EXP only if
     some exotic 2-dimensional building `X_e` has a *non-discrete* cocompact automorphism group. The closure
     of `K` in it would be a non-discrete closed subgroup with property (T) and no fixed vertex.

## Proof

**Item 1.** By (FA), `K` fixes a vertex `v`. Its image lies in `Aut(T)_v`, which acts faithfully on `T`
through the finite groups `Aut(B(v,r))`. So the image is residually finite, and it is a quotient of `K`,
hence trivial.

**Item 2.** Compose with `Aut(X_i) → Aut(X_i)/L_i`, which is residually finite by (I2). The image is a
residually finite quotient of `K`, hence trivial, so `K` maps into `L_i`. That image is a finitely generated
linear group, residually finite by (I4), and a quotient of `K`, hence trivial.

**Item 3.** By (I3), the image of `K` in the finite group permuting the factors is a finite quotient, hence
trivial, so `K` preserves every factor. Items 1 and 2 apply factor by factor. For simple `K`, a nontrivial
action on a factor is faithful.

**Item 4.**
- (a) `Λ` is faithful and `K ≠ 1`, so by item 3 `K` acts nontrivially on some exotic 2-dimensional factor
  `X_e`. If it fixed a vertex there, its image would be residually finite by (I5), hence trivial.
- (b) The projection of the cocompact group `Λ` to `Aut(X_e)` has cocompact image, so a discrete
  `Aut(X_e)` acts properly and cocompactly. By Step 2 of
  `euclidean-building-lattices-lie-in-permutational-bh-class`, which is type-free and uses no finiteness of
  stabilizers, `Aut(X_e)` embeds in the full group of the orbit-category groupoid. Its units are the tile
  stabilizers, which are finite.
- (c) This is the contrapositive of (b). The closure of `K` has property (T), since `K` does and is dense
  in it. ∎

## Status of the object in 4(c)

- **Radu, Theorem A** (arXiv:1703.10495, read at source). If `Aut(Δ)^+` of a locally finite thick
  `Ã_2`-building is transitive on panels of each type, then `Δ` is Bruhat–Tits or `Aut(Δ)` is discrete.
- **Radu, Theorem B.** The same conclusion holds if `Aut(Δ)` is vertex-transitive and unimodular,
  `Aut(Δ)^+` is transitive on vertices of each type, and the thickness is `p + 1` with `p` prime.
- **The one known exception fixes a point at infinity.** Radu records that the non-discrete exotic
  examples of Van Maldeghem, "Automorphisms of nonclassical triangle buildings" (Bull. Soc. Math. Belg. Sér. B; §7), built from valuations on planar ternary rings, are vertex-transitive but fix a
  vertex at infinity, so they are not unimodular.
  - *Sketch* (imports: transverse buildings at a point at infinity, after Leeb and Caprace–Monod; context
    only). A `K` as above fixing `ξ ∈ ∂X_e` has trivial Busemann character, since `K` has finite
    abelianization.
  - `K` then acts on the lower-dimensional transverse space at `ξ`, where it fixes a point by items 1–3 and
    the fact that `K` has no homomorphism to `Isom(R^j)` with infinite image.
  - Strongly asymptotic rays toward `ξ` eventually coincide, since their tails lie in a common apartment. So
    each generator fixes a tail of one ray, and `K` fixes a vertex. That contradicts (a).
  - So examples of this kind never carry such `K`.
- **Steger's question.** Radu reports that Tim Steger asked in 2007 whether every exotic `Ã_2`-building
  admitting a cocompact lattice has a discrete automorphism group. Radu's Theorems A and B are partial
  positive answers.
- **Other types.** Nothing was checked for exotic `C̃_2`- and `G̃_2`-buildings, for example those of the
  Titz Mite–Witzel lattices.

## Lesson for general BH

- **Geometry filters hard inputs by linearity and fixed points.** A simple Kazhdan input cannot act on a
  tree (FA). It cannot act on any Bruhat–Tits building, because those automorphism groups are linear by
  residually finite and the input has no linear or residually finite quotient. Every Euclidean building of
  dimension `≥ 3` is Bruhat–Tits.
- **What is left.** Geometric (building-coded) hosts can use only exotic 2-dimensional buildings for the
  hard inputs. There, residual finiteness of the units plus a discrete automorphism group give finite units
  and an exponential word-problem cap.
- **Consequence for S1b.** The building version of S1b reaches word problems outside EXP only through an
  exotic 2-dimensional building with a non-discrete cocompact automorphism group containing a
  fixed-point-free closed subgroup with property (T). No such building is known, and Radu's theorems point
  the other way.
- **Where universal finitely coded hosts must go.** They must be non-geometric: codings whose degree class
  on the input is nonzero (`degree-coboundary-subgroups-of-coded-full-groups-are-rf`), with complexity in
  residually finite units that come from no building. Non-Euclidean buildings with non-discrete automorphism groups, such as hyperbolic Kac–Moody
  buildings, are the geometric family this filter does not reach. Their Cantor codings and the linearity of
  their automorphism groups were not examined.
