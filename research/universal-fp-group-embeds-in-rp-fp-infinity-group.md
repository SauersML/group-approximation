---
rg: 2
id: universal-fp-group-embeds-in-rp-fp-infinity-group
kind: claim
title: "A universal finitely presented group embeds in a recursively presented group of type FP_infinity"
artifacts:
  - research/artifacts/zp-z1-01-higher-rope-defects-2026-09-13.md
distinct_from:
  every-finitely-presented-group-embeds-in-an-f-infinity-group: that quantifies over all finitely presented groups and asks for F_infinity hosts; this asks for one recursively presented FP_infinity host of one universal group, a homological target in which Leary-type FP constructions can be used; the two are equivalent through two routes resting on Fournier-Facio--Zaremsky's Theorem A
---

Let `U` be a finitely presented group containing an isomorphic copy of every
finitely presented group (Higman 1961). The claim: there is an injective
homomorphism `ι: U → H` with `H` recursively presented and of type `FP_∞`
over `Z`.

The choice of `U` does not matter: two universal finitely presented groups
embed in each other.

**Equivalences** (proved on the two routes named here):

1. this claim;
2. `every-finitely-presented-group-embeds-in-an-f-infinity-group`, via route
   `fp-f-infinity-hosts-from-rp-fp-infinity-host` (Fournier-Facio--Zaremsky,
   arXiv:2607.21727v1, Theorem A at `n = ∞`) and route
   `rp-fp-infinity-host-from-fp-f-infinity-hosts`;
3. **mapping-torus normal form:** `U` has an injective endomorphism `ψ` whose
   ascending HNN extension `U *_ψ` is of type `F_∞`.

(3) ⇒ (2): `U ≤ U *_ψ`.
(2) ⇒ (3): let `ι: U → K` with `K` of type `F_∞`, and let `ȷ: K → U` be an
embedding given by Higman's theorem (`K` is finitely presented). Put
`ψ = ȷι`. The route `fp-f-infinity-hosts-from-rp-fp-infinity-host` proves
`U *_ψ ≅ K *_{ιȷ}`. The latter is an ascending HNN extension with base and
edge group `K`, so it is of type `F_∞`.

So a host may always be taken to be a mapping torus of `U` itself.

4. **Universal form:** some universal finitely presented group is of type
   `F_∞`.

(4) ⇒ (2): trivial. (2) ⇒ (4): an `F_∞` host of `U` is finitely presented
and contains every finitely presented group, so it is itself a universal
finitely presented group of type `F_∞`. Higman's construction of `U` goes
through the rope trick, and its output is never `FP_3`
(`higman-rope-trick-group-is-never-fp3`). So in forms (3) and (4) the
finiteness has to come from a different construction or from the directed
system `(U, ψ)`, not from the Higman-built `U`.

**Power refinement.** If some power `ψ^k` factors as `U → K → U` through a
group `K` of type `FP_∞`, with both maps injective, then `U *_ψ` is of type
`F_∞`. Proof: `U *_{ψ^k}` is isomorphic to the index-`k` subgroup
`χ^{-1}(kZ)` of `U *_ψ`, where `χ` sends the stable letter to `1`, because
the directed systems `(U, ψ)` and `(U, ψ^k)` have the same colimit. So
`U *_{ψ^k}` is `F_∞` by the route argument, and `F_∞` passes to groups
containing an `F_∞` subgroup of finite index.

## Attempts

- **Host fence** (established: `universal-fp-group-hosts-have-unsolvable-word-problem`).
  Any host `H` of `U` has unsolvable word problem, contains `Z^k` for every `k`
  (so infinite cohomological dimension), and has finite subgroups of every
  order. Every host family with solvable word problem is therefore dead for
  `U`: hyperbolic, cocompactly CAT(0), automatic and f.g. linear groups;
  finitely presented residually finite groups (mapping class groups, `Aut(F_n)`,
  `Out(F_n)`); Thompson's `F`, `T`, `V` and the Brin--Thompson groups `nV`.
  Twisted Brin--Thompson hosts `SV_Γ` need the input to be of type `F_∞`
  already (recorded on `every-finitely-presented-group-embeds-in-an-f-infinity-group`).
- **Rope trick** (established: `higman-rope-trick-group-is-never-fp3`). The
  rope-trick outputs of Higman's and Leary's embeddings are never `FP_3(Q)`.
  So a recursively presented `FP_∞` host must come from a different device.
- **Type-`FP` hosts: dead** (established, item 2 of
  `universal-fp-group-hosts-have-unsolvable-word-problem`). A group of type
  `FP` over a nonzero ring `R` has `cd_R < ∞`, while a host of `U` contains
  `Z^k` for every `k`. That excludes Bestvina--Brady kernels `BB_L`, Leary's
  groups `G_L(S)` over acyclic `L`, and every other type-`FP` group, whatever
  their subgroup structure. So a recursively presented host has to be of type
  `FP_∞` but not of type `FP`, with torsion of every order and infinite
  cohomological dimension. That points to groups acting on
  infinite-dimensional contractible complexes, not to cube-complex level
  sets. Leary's `FP_2` embedding theorem is arXiv:1610.05813, and it goes
  through the rope trick.
- **Alexander-module test for form (3)** (necessary condition). Let
  `N = ker(χ: U *_ψ → Z)`, which is the directed union of the conjugates
  `t^{-j} U t^j`. If `U *_ψ` is of type `FP_m`, then for every `k <= m` the
  module `H_k(N; Z) = colim_{ψ_*} H_k(U; Z)` is finitely generated over
  `Z[t, t^{-1}]`. Reason: by Shapiro's lemma it is `H_k(U *_ψ; Z[t^{±1}])`,
  computed from a free resolution that is finitely generated through degree
  `m`, over a Noetherian ring. So `ψ_*` has to compress the homology of `U`,
  which need not be finitely generated in any degree `>= 3`, to finitely
  generated `Z[t^{±1}]`-modules. Factoring a power of `ψ` through an `FP_∞`
  group does exactly that.
- **Levelwise hosts.** If `U` has an `F_m` host for every finite `m`, does it
  have an `F_∞` host? That is the open claim
  `type-fn-plus-1-hosts-for-all-n-give-f-infinity-hosts`, and it is where the
  two parts of Problem 1.1 could come apart.
- **Split-edge rope containers: dead at level 3** (established:
  `split-edge-hnn-with-non-fp2-edge-is-not-fp3`). Suppose an HNN container has
  a finitely generated, non-`FP_2` edge group `L`, for instance Higman's double
  `F *_R F`, one of whose images is a retract of the vertex group with an
  `FP_2` kernel, while the other image passes through an `FP_2` subgroup. Then
  the container is never `FP_3`, on product coefficients, even when it is
  finitely presented and an integral homology circle. This kills the
  acyclic-host twisted rope container
  (`acyclic-host-twisted-rope-container-is-never-fp3`). So a rope-shaped host
  has to embed the double without a split retraction on either side.
- **Defect criterion for HNN hosts** (standard; not yet a node). Let
  `H = HNN(V, L', α, β)` be finitely generated and `X = ∏_Λ ZH`. By the
  Bieri--Eckmann criterion, `H` is of type `FP_n` iff `H_k(H; X) = 0` for
  `1 <= k <= n-1` and every `Λ`. By the Mayer--Vietoris sequence of the HNN
  extension, this holds iff `φ_k = α_* - tβ_*: H_k(L'; X) -> H_k(V; X)` is
  onto for `1 <= k <= n-1` and one-to-one for `0 <= k <= n-2`. A rope has to
  cancel the homological defects of the edge group against those of the vertex
  group in every degree up to `n-1`. Leary's rope does this in degree 1 only.
  See `research/artifacts/zp-z1-01-higher-rope-defects-2026-09-13.md`, §4.
- **Product ropes: preliminary, unreviewed.** Take `V = P x G`, `α = (ι, 1)`,
  `β = (ι, π)` with `P` of type `FP_∞`. On `X` the map `α_*` factors through
  `H_k(P; X) = 0` in positive degrees, so `φ_k = -t_* β_*`. If `ker π` is also
  of type `FP_∞`, then `β_*` compares the `G`-homology of the coinvariant
  modules `X_N` and `X_P`. The collapse `X_N -> X_P` looks non-injective in a
  way that adds `G`-defects. The computation and the guess are in the
  artifact, §6.
- **Splitting hosts over good edge groups add nothing** (established:
  `fp-n-splittings-over-fp-n-edges-have-fp-n-vertex-groups`). Suppose a host of
  type `FP_∞` splits as a finite graph of groups with edge groups of type
  `FP_∞`, and `U` is a factor or a retract of a vertex group. Then `U` is
  itself of type `FP_∞`. So such a host reduces to form (4).
- **Merge note.** Lane z1-01-embed-pos landed an equivalent claim over all
  finitely generated recursively presented groups at e7d92b58d4. It was
  retired in favor of this claim, together with its two routes, which
  duplicated this claim's two routes. The three bullets above are the content
  only the retired claim carried.
