---
rg: 2
id: universal-fp-group-embeds-in-rp-fp-infinity-group
kind: claim
title: "A universal finitely presented group embeds in a recursively presented group of type FP_infinity"
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
- **Leary-type `FP` groups** (not yet evaluated). Bestvina--Brady kernels and
  Leary's groups `G_L(S)` over acyclic flag complexes `L` are of type `FP` over
  `Z` without being finitely presented. That is exactly the gap Theorem A lets
  one use. Where it dies, or does not: these groups are built from
  right-angled Artin groups and cube complexes. Whether they are torsion-free
  has to be checked: a torsion-free host cannot contain `U`. Whether any
  version with torsion (right-angled Coxeter or graph-product analogues)
  contains arbitrary finitely presented subgroups is the open step. Pending:
  reading Leary, *Uncountably many groups of type FP*, and *Subgroups of
  almost finitely presented groups*, verbatim.
