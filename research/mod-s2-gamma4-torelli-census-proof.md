---
rg: 2
id: mod-s2-gamma4-torelli-census-proof
kind: route
title: Pass from Gamma(4) to a 61440-coset cover of the braid group B_5 modulo its center by Birman-Hilden and capping, run exact abelianised Reidemeister-Schreier, and certify d = 1/30 by a transversal relation
target: mod-s2-gamma4-torelli-census-is-one-thirtieth
requires:
  - genus-two-mapping-class-group-homology-and-symplectic-quotient
  - mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit
artifacts:
  - experiments/mod-s2-gamma4-torsion-census-2026-09-17/gamma4.py
  - experiments/mod-s2-gamma4-torsion-census-2026-09-17/gamma4_lattice.py
  - experiments/mod-s2-gamma4-torsion-census-2026-09-17/gamma4_structure.py
  - experiments/mod-s2-gamma4-torsion-census-2026-09-17/gamma4_orbits.py
---

Notation as in the target.

**Inputs.**
- **[HOM]** `genus-two-mapping-class-group-homology-and-symplectic-quotient`, item 4: the exact
  sequence `1 -> K -> M -> Sp_4(Z) -> 1`, so `M -> Sp_4(Z/4)` is onto.
- **[TA]** `mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit`: definitions of `v_c`, `W`,
  `d`, (TA2) monotonicity, (TA3) certificates, and `d(Gamma(2)) = 1/30` from (TA4).
- **Standard facts** (Farb-Margalit, *A primer on mapping class groups*: Chapter 9 for
  Birman-Hilden, §3.6 for capping), used as recalled, not re-read, in `low-complexity-mcg-continuous-automatic-proof` (M1), (M2).
  - **(BH)** `M/<iota> = Mod(S_{0,6})`, with `a_i -> sigma_i` (half-twists on a chain of arcs
    through the six branch points) and `iota` central, mapping to `-I` in `Sp_4(Z)`.
  - **(CAP)** Capping the disk `D_5` gives `B_5 / <Delta^2> = H`, the stabilizer of puncture 6
    in `Mod(S_{0,6})`, where `Delta^2 = (sigma_1 sigma_2 sigma_3 sigma_4)^5` is central.

## Step 1. Reduction to 61440 cosets of `H`

1. `M_4` meets `<iota>` trivially, because `-I` is not `I` mod 4. So the projection `M -> Mod(S_{0,6})`
   maps `M_4` isomorphically onto its image `K4`. Also `K4 = ker(Mod(S_{0,6}) -> Sp_4(Z/4)/{+-I})`,
   because the preimage of `{+-I}` in `M` is `M_4 u iota M_4`. Hence `H_1(M_4) = H_1(K4)`.
2. `K4 <= H`. Let `Q_2` be the kernel of `Mod(S_{0,6}) -> Sp_4(F_2)`. The map is onto by [HOM], so
   it has order 720. The image of `H` has order 120 (computed in `gamma4.py`: `enumerate_Q(2)`). So
   `[Mod(S_{0,6}) : Q_2 H] = 720/120 = 6 = [Mod(S_{0,6}) : H]`, and `Q_2 <= H`. Since `K4 <= Q_2`,
   we get `K4 <= H`.
3. *Every separating twist is an `H`-conjugate of `t_s`.*
   - Every separating curve is `g(s)` for some `g` in `M` (change of coordinates), so every
     separating twist is `g t_s g^(-1)`.
   - `s` is the preimage of the curve `c` around branch points 1, 2, 3. The stabilizer of `c` in
     `Mod(S_{0,6})` is transitive on the six punctures: it contains `sigma_1, sigma_2, sigma_4,
     sigma_5` and the rotation `(sigma_1 ... sigma_5)^3`, which exchanges the two sides of `c`.
   - Hence `Mod(S_{0,6}) = H . Stab(c)`. A lift of an element of `Stab(c)` preserves `s`, so it
     commutes with `t_s`. And `iota` is central. So `g t_s g^(-1) = h t_s h^(-1)` for a lift `h` of an
     element of `H`.
4. So the classes `v_c` are the classes of `h t_s h^(-1)` in `H_1(K4)`, with `h` running over `H/K4`.
   By (BH), `t_s = (a_1 a_2)^6` maps to the word `(sigma_1 sigma_2)^6`.

## Step 2. Exact computation (`gamma4.py`, `gamma4_lattice.py`)

1. `H/K4` is the image of `H` in `Sp_4(Z/4)/{+-I}`, with `sigma_i` acting as the transvection of the
   chain class `x_i` (the matrices of `census.py`). Enumeration gives 61440 elements. The script
   checks that every relator of the presentation of `H` (the Artin relations of `B_5` and
   `Delta^2 = 1`) acts trivially, and so does `(sigma_1 sigma_2)^6`.
2. Abelianised Reidemeister-Schreier on the right regular action gives 184321 Schreier generators and
   430080 relators. Exact elimination through `+-1` pivots (the `unit_eliminate` routine of
   `census.py`) leaves 56 generators and 181090 integer relators. Their HNF has rank 2 and Smith form
   with unit diagonal. So `H_1(K4) = Z^54`, which is (G1).
3. The 61440 conjugates of `(sigma_1 sigma_2)^6` are rewritten along the same elimination. Reduced
   modulo the HNF they give 160 distinct classes, each hit by 384 cosets. `W` is the lattice of
   integer relations among them, computed by HNF of `[relators | 0 ; classes | I]` (`w_lattice` of
   `census.py`). It has rank 106. Its basis has Smith form with unit diagonal, so `W` is saturated,
   and the augmentations have gcd 10. This gives (G3).
4. The mixed-integer program of `census.py` returns the constant point `theta = 3/10` with deviation
   `1/30`. This is only a cross-check; the proof of (G5) below does not use it.

## Step 3. Structure (`gamma4_structure.py`, `gamma4_orbits.py`)

1. The splitting of a class is computed from its coset matrix `A` as `A . span(x_1, x_2)` mod 2.
   It is well defined on all 160 classes. Each splitting carries 16 classes of rank 10, which is (G2).
2. *Transversal relations.* The map `H_1 -> Z^54` is given by an integer kernel basis of the HNF.
   A meet-in-the-middle count over `16^5 x 16^5` choices finds exactly 1024 choices with total 0.
3. *Symmetry.* Conjugation acts on classes through coset matrices, `A -> M(h) A`, and the script
   checks this is well defined. `H/K4` acts faithfully (order 61440). The pure braid generators
   `A_ij` generate an action of order 512, which is `Gamma(2)/Gamma(4)` modulo `-I`. The 1024
   relations form one `H`-orbit, and two orbits of size 512 under the pure part. This is (G4),
   first part.
4. *Generation.* The 60 local relations are `W` intersected with the coordinates over one splitting,
   6 per splitting, of augmentation 0 and `l1` in `{6, 8}`. HNF comparison shows that local and
   transversal relations together have the same HNF as `W`. The transversal ones alone have Smith
   form `(1^101, 2^5)` against `W`, that is, index `2^5`. This is the rest of (G4).

## Step 4. The distance (G5) and (G6)

1. Take any transversal relation `w`. It lies in `W`, and `aug(w) = 10` is not divisible by 3, with
   `||w||_1 = 10`. So (TA3) gives `d(Gamma(4)) >= 1/30`.
2. By (TA2), `d(Gamma(4)) <= d(Gamma(2)) = 1/30`. Hence `d(Gamma(4)) = 1/30`. The constant
   `theta = 3/10` is admissible, because `aug(W) = 10 Z`, and it attains the value.
3. (G6) follows from (TA2): `Gamma' >= Gamma(4)` gives `d(Gamma') >= d(Gamma(4))`, and
   `Gamma' <= Gamma(2)` gives `d(Gamma') <= 1/30`. QED.

**Cross-check at level two.** The same pipeline with `N = 2` (120 cosets of `H`) returns
`H_1(PMod(S_{0,6})) = Z^9` and `W = Z (1, ..., 1)` on 10 classes. This matches the census row for
`Gamma(2)`: there `H_1` is taken of `M_2`, which contains `iota`, but `W` is the same.

**Run times** (4 CPUs, 15 GB): elimination about 10 minutes; all later stages under 30 s.
