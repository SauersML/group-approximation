---
rg: 2
id: literal-telescope-core-lef
kind: claim
title: The telescope core of the literal group is locally residually finite
distinct_from:
  literal-telescope-split-normal-form: That claim records the split structure `E = N_E semidirect V`; this one is an approximation property of the index-`Z` subgroup `N_E semidirect T`.
  literal-lamp-kernel-clifford-block-amalgam: That identifies the lamp kernel algebraically; this says the level-truncated pieces are residually finite.
  finite-site-orbits-invariant-clifford-kernel: That produces FINITE invariant subgroups from finite site orbits and needs local finiteness of the lamp group; this produces finitely generated virtually free invariant subgroups and applies to the block amalgam, which is not locally finite.
artifacts:
  - notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md
  - notes/LITERAL_GROUP_BLOCK_AMALGAM_STRUCTURE_2026-08-14.md
---

Let `E_T = N_E semidirect T` be the kernel of the stable-letter exponent
`E -> Z`, i.e. the lamp group extended by the telescope `T = union of the
levels Gamma_n`.  Every finitely generated subgroup of `E_T` is residually
finite.  Consequently `E_T` is LEF, sofic, and MF.

**"Locally" is load-bearing: `E_T` is LEF but NOT residually finite** —
`telescope-core-not-residually-finite`, with the argument written out as
Theorem 4.1a of `notes/LITERAL_GROUP_IS_SOFIC_2026-08-14.md` (`cairn-verify2`):
in any homomorphism from `E_T` to a finite group the image of `Z[1/2]^3` is
2-divisible and finite, hence of odd order, so 2 is invertible there and
`phi(Z[1/2]^3) = phi(Z^3)`, giving `phi(T) = phi(B)` with no use of the stable
letter; the level-collapse argument then identifies same-level lamps and kills
`w`.  So a directed union of residually finite groups need not be residually
finite, and this one is not — every window has finite models keeping `w`,
while the union has none.

**No conflict with `marked-quotients-not-lef`.**  That claim shows `E`, `W`,
`E/<w>` and `W/<zeta>` are all NOT LEF, by an argument that needs the stable
letter `tau` inside the window: a local embedding into a finite group forces
`phi(tau) Gamma^ phi(tau)^(-1) = Gamma^` by cardinality and hence kills the
defect.  `E_T` is exactly the stable-letter-free part, so that argument does
not apply to it, and LEF passing to subgroups is consistent with the ambient
group failing LEF.  The whole content of the pair of statements is that local
finite models exist for every window of `E_T` and cannot survive the addition
of `tau` — which is also why soficity does survive it (the `Z`-extension step
is only approximately multiplicative) while LEF and residual finiteness do not.

**Which MF, and how to reuse the step.**  The MF here is the operator-norm
norm-matrix-corona property of `countable-group-mf-conventions`, hence every
formulation equivalent to it there.  The implication is factored out as the
reusable node `lef-implies-operator-mf`: locally residually finite implies LEF
implies operator MF, by the manuscript's `lem:lfmf` argument run on local
embeddings instead of finite subgroups.  Nothing in that step is specific to
the literal group, so `lamp-telescope-base-is-lef` and any other
lamp-by-telescope argument can cite it directly rather than re-deriving MF.

The mechanism: a finite window lies in one level `Gamma_n` and touches
finitely many blocks; the level has finite orbits on the block set, so the
blocks it touches generate a finitely generated, level-invariant sub-amalgam
`M_J` of finitely many copies of `ClLamp(8)` over the common centre.  `M_J` is
virtually free, and the level acts on it through a finite permutation group of
the `8|J|` sites, so `M_J semidirect Gamma_n` contains `M_J x Lambda` with
finite index for a finite-index `Lambda <= Gamma_n` acting trivially.

**Virtual freeness is not needed.**  The route
`literal-telescope-core-lef-via-central-embedding` runs the identical window
argument but gets residual finiteness of `M_J` from
`clifford-block-amalgam-residually-finite` — a two-quotient embedding into
`C(sites(J)) x (*_{i in J} (Z/2)^8)` — instead of from
Karrass--Pietrowski--Solitar, and residual finiteness of `Gamma_n` from
congruence quotients instead of from Mal'cev plus the identification of the
presented base.  That is the version with no literature input; see
`notes/E_SOFICITY_SELF_CONTAINED_2026-08-16.md` §§7-10.
