---
rg: 2
id: mod-s2-gamma4-index-two-torelli-census-proof
kind: route
title: Run the Birman-Hilden level-four pipeline on the 122880-coset covers attached to one functional on Gamma(4)/Gamma(8) per Sp_4(F_2)-orbit, certify d = 1/30 by a mass-10 relation, and read off b_1 at level eight from the character decomposition
target: mod-s2-gamma4-index-two-torelli-census
requires:
  - genus-two-mapping-class-group-homology-and-symplectic-quotient
  - mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit
  - mod-s2-gamma4-torelli-census-is-one-thirtieth
artifacts:
  - experiments/mod-s2-gamma4-index2-census-2026-09-17/index2.py
  - experiments/mod-s2-gamma4-index2-census-2026-09-17/drive.py
  - experiments/mod-s2-gamma4-index2-census-2026-09-17/combine.py
  - experiments/mod-s2-gamma4-index2-census-2026-09-17/blocks.py
  - experiments/mod-s2-gamma4-index2-census-2026-09-17/blocks-output.txt
  - experiments/mod-s2-gamma4-index2-census-2026-09-17/test_lean.py
  - experiments/mod-s2-gamma4-index2-census-2026-09-17/crosscheck.py
  - experiments/mod-s2-gamma4-index2-census-2026-09-17/index2-results.json
  - experiments/mod-s2-gamma4-index2-census-2026-09-17/index2-lean-crosscheck.json
---

Notation as in the target.

**Inputs.**
- **[HOM]** `genus-two-mapping-class-group-homology-and-symplectic-quotient`, item 4: `M -> Sp_4(Z)` is
  onto with kernel the Torelli group `K`. So `M_4 / M_8 = Gamma(4)/Gamma(8)`, and every separating
  twist lies in every `M_chi`.
- **[TA]** `mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit`: the definitions of `v_c`,
  `W`, `d`, (TA2) monotonicity, and (TA3) certificates.
- **[G4]** `mod-s2-gamma4-torelli-census-is-one-thirtieth` and its route. This gives
  `H_1(M_4) = Z^54` and `d(Gamma(4)) = 1/30`. From Step 1 of the route it gives the
  Birman-Hilden and capping reduction: `M_4` is isomorphic to `K4 <= H = B_5/<Delta^2>`, and every
  separating twist is `h t_s h^(-1)` for a lift `h` of an element of `H`. That step uses only
  `-I != I mod 4`, so it holds verbatim for every subgroup of `M_4`.
- **Standard fact (transfer).** Let `N` be normal of finite index in a group `G`. Then restriction
  `H^1(G; C) -> H^1(N; C)` is injective, with image the `G/N`-invariants. So
  `H_1(G; C) = H_1(N; C)_(G/N)` (Brown, *Cohomology of Groups*, III.9–III.10, corestriction
  composed with restriction is multiplication by the index; recalled, not re-read).

## Step 1. The index-two subgroups and their orbits (`index2.py`: `gamma48_basis`, `orbit_reps`)

1. `Gamma(4)/Gamma(8) = {I + 4Y mod 8}` is elementary abelian, since
   `(I+4Y)(I+4Y') = I + 4(Y+Y') mod 8`. Conjugation by `g` in `Sp_4(Z)` acts on it by
   `Y -> g Y g^(-1) mod 2`, so through `Sp_4(F_2)`.
2. The script takes `Y` from the fourth powers `T_x^4 = I + 4 x x^T J` of the transvections, over
   the 15 nonzero `x` in `F_2^4`. These span a space of dimension 10. That is the order `2^10` of
   `Gamma(4)/Gamma(8)`, which the coset count in Step 2 confirms independently.
3. Index-two subgroups `Gamma(8) <= G <= Gamma(4)` correspond to nonzero functionals `chi`, via
   `G_chi = ker chi`. Every separating twist class, and hence `d`, is invariant under conjugation by
   `M`, so `d(G_chi)` depends only on the orbit of `chi`.
4. The images of `a_1, ..., a_5` generate `Sp_4(F_2)` by [HOM]. The orbit enumeration gives 15 orbits
   with sizes `60, 15, 45, 20, 180, 180, 60, 60, 120, 90, 10, 6, 90, 72, 15`, which sum to 1023.

## Step 2. Coset action for one `chi` (`index2.py`: `enumerate_chi`)

1. `M_chi = pi^(-1) G_chi` meets `<iota>` trivially, because `M_chi <= M_4`. By [G4] it is isomorphic
   to `K_chi <= K4 <= H`. So `H_1(M_chi) = H_1(K_chi)`, and the separating-twist classes are the
   classes of `h t_s h^(-1)`, with `h` running over `H/K_chi`.
2. *Coset key.* Right cosets `K_chi A`, with `A` the mod-8 matrix of an element of `H`, are keyed by
   `(+-A mod 4, chi(X))`. Here `X = +- A L^(-1) mod 8`, with the sign chosen so that
   `X = I mod 4`. The matrix `L` is the first lift met for the class of `+-A mod 4`.
   - The sign is unique, because `-I != I mod 4`.
   - Suppose `A = +-B mod 4`. Then `A B^(-1) = +- X_A X_B^(-1)`, and it lies in `+-G_chi` exactly
     when `chi(X_A) = chi(X_B)`, since `Gamma(4)/Gamma(8)` is abelian.
   So the key is a complete invariant of the coset.
3. For every one of the 15 representatives, the enumeration gives 122880 = 2 x 61440 cosets. So
   `chi` is nonzero on the image of `K4`, and `[K4 : K_chi] = 2`. The script checks that every relator
   of `H`, and the word `(sigma_1 sigma_2)^6` (which fixes every coset), act trivially.

## Step 3. Exact lattice computation (`index2.py`: `lattice`; `drive.py`, one process per orbit)

This step is the same pipeline as in [G4]:
- abelianised Reidemeister-Schreier, with 368641 Schreier generators;
- exact `+-1` elimination;
- incremental HNF;
- Smith invariants of `H_1(K_chi)`;
- the classes `v_c` reduced modulo the HNF;
- `W` as the relation lattice of those classes (`w_lattice`);
- the MILP distance point;
- the minimal-`l1` certificate search.

The per-orbit outputs are collected by `combine.py` into `index2-results.json`, and the table in the
target is read from that file.

*Two eliminators.* The `+-1` elimination was run in two implementations.
- Orbits 1, 2, 3, 7, 10, 11 used `census.unit_eliminate`, the eliminator of [G4].
- Orbits 0, 4, 5, 6, 8, 9, 12, 13, 14 used `index2.lean_eliminate`.
  - It makes the same unimodular generator changes: pivot on a `+-1` entry, then substitute.
  - It pivots only on short relators first, which keeps fill-in down.
  - It does not carry the target vectors along. Instead it rewrites them afterwards through the
    recorded substitutions, applied in elimination order.
  - Each step is a change of basis of `Z^gens` that maps the relator module onto itself. So the
    quotient, and each target class, is unchanged. Only the generator names differ.
- `test_lean.py` checks that the two eliminators agree on the level-2 and level-3 coset actions (120
  and 25920 cosets). They agree on the `H_1` invariants, the class count and multiplicities, the `W`
  rank, the augmentation gcd and the certificate `l1`.
- The lean eliminator was rerun on orbits 2 and 7, the two orbits whose `chi` kills a level-two
  block, and compared field by field with the `unit_eliminate` results (`crosscheck.py`, output
  `index2-lean-crosscheck.json`). Every recorded field agrees: `H_1` rank and torsion, the class
  count and multiplicities, the `W` rank, `gcd aug`, the MILP point and `theta`, and the
  certificate `l1`, augmentation and support.
- The same rerun of orbits 1, 3, 10 and 11 did not finish within the time limit, because the
  machine was shared. So for those four orbits the `unit_eliminate` result is the only one.

## Step 4. The distance

1. For every orbit, the certificate search returns `w` in `W(G_chi)` with `||w||_1 = aug(w) = 10`.
   Since `3` does not divide `10`, (TA3) gives `d(G_chi) >= 1/30`.
2. By (TA2) and [G4], `d(G_chi) <= d(Gamma(4)) = 1/30`. So `d(G_chi) = 1/30`. The MILP point
   `theta = 3/10` is only a cross-check.
3. Every index-two subgroup `Gamma(8) <= G <= Gamma(4)` is `Sp_4(Z)`-conjugate to one of the 15
   representatives `G_chi`, and `d` is a conjugation invariant (Step 1.3). So every such `G` has
   `d(G) = 1/30`. By (TA2), `d(Gamma') >= 1/30` also holds for every `Gamma'` containing some such
   `G`. QED for the distance part.

## Step 5. `b_1` at level eight (pure algebra on top of Step 3)

1. Let `A = M_4/M_8 = F_2^10` and `V = H_1(M_8; C)`. `V` is finite dimensional, because `M_8` has
   finite index in the finitely generated group `M`. As a `C[A]`-module it splits as
   `V = sum_psi V_psi`, over the characters `psi` of `A`.
2. By the transfer fact, `H_1(M_chi; C) = V_(G_chi/Gamma(8))`, which equals `V_1 + V_chi`. Also
   `H_1(M_4; C) = V_A = V_1`. So `dim V_chi = b_1(M_chi) - 54`.
3. Conjugation by `M` permutes the `V_psi` along the `Sp_4(F_2)`-action on characters. So
   `b_1(M_8) = 54 + sum over orbits |orbit| (b_1(M_chi) - 54)`.
4. Step 3 gives `b_1(M_chi) = 54` for all 15 representatives. So `V_psi = 0` for every
   `psi != 1`, `V = V_1` is the trivial `A`-module, and `b_1(M_8) = 54`.
5. Now let `Gamma(8) <= Gamma' <= Gamma(4)` be arbitrary, and put `B = Gamma'/Gamma(8)`. By
   transfer, `H_1(M'; C) = V_B = V`, so `b_1(M') = 54`.
6. Restriction `H^1(M_4; R) -> H^1(M'; R)` is injective, so it is an isomorphism. Hence:
   - Every real character of `M'` is the restriction of one of `M_4`.
   - The identity component of `Ann(W(Gamma'))` is the pullback of `Ann(W(Gamma(4)))` along the
     surjection of class sets. Every separating twist of `M'` maps to its class in `M_4`, and a
     character restricted from `M_4` takes the same value on both.
   - Pullback along a surjection preserves the `l_inf` distance to the constant `1/3`. So the
     identity component contributes exactly `d(Gamma(4)) = 1/30`.
   - Therefore any value `d(Gamma') < 1/30` must be attained on a non-identity component, that is,
     by a character that is nontrivial on the torsion of `H_1(M')`.

**Run times** (4 CPUs, 15 GB memory cgroup, one orbit at a time, via `drive.py`, one process per
orbit).
- `census.unit_eliminate`: 500 to 2500 s per orbit, with peak memory up to 13.8 GB. It ran out of
  memory on orbit 14.
- `lean_eliminate`: 100 to 300 s per orbit, and up to about 500 s on the loaded shared machine,
  with peak memory about 2.3 GB. On the torsion-free orbits it eliminates down to 54 generators and
  0 relators. On orbit 2 it leaves 55 generators.
