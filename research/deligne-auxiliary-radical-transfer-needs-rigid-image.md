---
rg: 2
id: deligne-auxiliary-radical-transfer-needs-rigid-image
kind: claim
title: An approximation radical pushed into Deligne's triple cover along any homomorphism dies unless the auxiliary group's maximal approximable quotient maps onto a Deligne-rigid subgroup
distinct_from:
  mf-radical-functoriality: that is the bare inclusion f(Rad_MF G) <= Rad_MF H; this uses it, for every subgroup-closed approximation class, to compute exactly which auxiliary radicals can reach the Deligne center, and kills the rest.
  mf-radical-saturation-along-any-homomorphism: that pushes a radical word forward to saturate a target it normally generates; this shows the pushed-forward radical is killed whenever the target is a Deligne cover and the source is of any of the usual kinds.
  deligne-flexible-subgroup-restrictions-carry-exact-sector-models: that kills subgroup-local sector certificates on flexible subgroups of E_3; this kills certificates imported from other groups through homomorphisms, and reduces what survives to a rigid image.
  deligne-cover-compression-defects-are-trivial: that kills compression-defect criteria through the Guichardet--Wigner quasimorphism; this kills transported-radical criteria through centrality of C_3 and flexibility of amenable images.
  steinberg-gl-mf-radical-is-commutator-or-trivial: that computes MF radicals of GL_n over Steinberg algebras; this shows those radicals, and every other radical with an amenable maximal quotient, map trivially into every Deligne cover.
---

**ESTABLISHED** (route `deligne-auxiliary-radical-transfer-proof`).

**Setting.** `1 -> C_3=<z> -> E_3 --p--> Gamma=Sp_4(Z) -> 1` is Deligne's triple cover. Let `P` be any class of
groups closed under isomorphism and subgroups that contains every countable residually finite group: for example
MF, hyperlinear, sofic, LEF. For a group `H` put `Rad_P(H) = ∩ { ker pi : pi : H -> Q, Q in P }` and call
`Q_H = H / Rad_P(H)` its *maximal `P`-quotient*. Let `f : H -> E_3` be any homomorphism, `K = f(H)`,
`N = Rad_P(H)`.

- **(R1) Centrality and coinvariants.** `f(N) <= C_3 ∩ Rad_P(K)`, and `f([N,H]) = 1`. So `f|_N` factors through
  the coinvariants `N/[N,H]`. In particular `f(N) = 1` whenever `N = [N,H]`: for instance when `N` is perfect,
  when `N = H` (full radical of a perfect group), or when `N` contains a relative elementary subgroup
  `EL_n(R,I)`, `n >= 3`, of `H = EL_n(R)` (then `f(EL_n(R,I)) = 1`).
- **(R2) Rigid image.** If `f(N) != 1`, then `f(N) = C_3`, `z in Rad_P(K)`, and `p(K)` is a
  **Deligne-rigid** subgroup of `Gamma`, in the sense of `deligne-flexible-subgroup-restrictions-carry-exact-sector-models`.
  Moreover `Q_H` surjects onto `p(K)`.
- **(R3) Amenable or lawful quotients transfer nothing.** If `Q_H` is amenable, or satisfies a nontrivial law,
  then `f(N) = 1` for every homomorphism `f : H -> E_3`. This covers every `H` whose maximal `P`-quotient is
  trivial (full radical), abelian (for example the `K_1` extreme of
  `purely-infinite-steinberg-gl-max-mf-quotient-is-k1`), solvable, nilpotent or of bounded exponent.
- **(R4) Hosts give only upper bounds.** If `j : E_3 -> H` is a homomorphism, then
  `j(Rad_P(E_3)) <= Rad_P(H)`. A host can therefore certify `z notin Rad_P(E_3)` (when `j(z) notin Rad_P(H)`), but
  never `z in Rad_P(E_3)`.

**Readings.**
- `P = MF`: `z in Rad_MF(E_3)` is the flagship `deligne-triple-cover-exact-mf-radical`
  (`deligne-triple-cover-mf-radical-dichotomy`).
- `P = hyperlinear`: `z in Rad_HL(E_3)` iff `E_3` is not hyperlinear (route, step H), which is the HS gap
  `maslov-mod3-projective-defect-gap` (`deligne-sector-gap-is-exactly-nonhyperlinearity`).
- So a proof of either statement by importing a computed radical of an auxiliary group `H` needs three things.
  - `Rad_P(H)` must have coinvariants `N/[N,H]` that map onto `C_3`.
  - `Q_H` must be non-amenable.
  - `Q_H` must surject onto a Deligne-rigid subgroup of `Sp_4(Z)`.
- If no infinite-index Deligne-rigid subgroup exists (`sp4-deligne-rigid-infinite-index-subgroup-exists` false),
  then `K` has finite index in `E_3`, and the witness is the flagship on a finite-index subgroup.
- **Class killed.** The following MF radicals from the ring, groupoid and paradox lanes map trivially under every
  homomorphism into `E_3`:
  - full radicals, by (R3), e.g. `measure-free-ample-groupoid-el-n-full-mf-radical`,
    `simple-dedekind-infinite-ring-elementary-full-mf-radical`, `fp-simple-full-mf-radical-group`,
    `eighteen-relator-kazhdan-group-with-full-mf-radical`;
  - the `K_1`/commutator extreme, by (R3): `purely-infinite-steinberg-gl-max-mf-quotient-is-k1`,
    `steinberg-gl-mf-radical-is-commutator-or-trivial`;
  - relative elementary subgroups of defect ideals, by (R1): `mf-radical-contains-defect-ideal-elementary-subgroup`
    (rank `n >= 3`);
  - perfect kernels, by (R1): the finitary alternating radical of
    `dyadic-perturbation-group-mf-radical-is-finitary-alternating` and the locally finite perfect radical of
    `affine-perfect-lamp-wreath-has-locally-finite-mf-radical`.
- The same holds for any future explicit non-hyperlinear group whose maximal hyperlinear quotient is amenable, or
  whose hyperlinear radical is perfect.
- The invariants are the centrality of `C_3` (R1) and the flexibility of amenable subgroups of `Sp_4(Z)` (R3).
- **Not killed.** An auxiliary group whose radical has central coinvariants and whose maximal quotient maps onto a
  Deligne-rigid group, such as a finite-index subgroup of `E_3`. This is the flagship restated.
