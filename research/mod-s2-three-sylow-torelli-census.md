---
rg: 2
id: mod-s2-three-sylow-torelli-census
kind: claim
title: Below Gamma(2), along the 3-Sylow chain toward Gamma(6) where every index is divisible by 3, the Torelli census stays exactly d = 1/30 down to the Frattini level, but no single relation certifies it
distinct_from:
  mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit: that computes d at 29 subgroups, including three intersections of Gamma(2) with level-3 stabilizers of index prime to 3 in Gamma(2); this computes the subgroups Gamma_V of 3-power index in the 3-Sylow preimage Gamma_U, where no certificate transfers from Gamma(2).
  mod-s2-torelli-abelian-census-limit-is-positive: that asks for inf_N d(Gamma(N)) > 0; this settles d on the 3-power part of the passage Gamma(2) -> Gamma(6) down to the order-9 Frattini subgroup and gives no uniform bound.
  mod-s2-gamma4-torelli-census-is-one-thirtieth: that is the 2-adic step Gamma(2) -> Gamma(4); this is the 3-adic step Gamma(2) -> Gamma(6).
  mod-s2-igusa-torelli-census-is-one-thirtieth: that is the 2-adic level Gamma(4,8); this is a mixed level 6 computation.
  mod-s2-gamma4-index-two-torelli-census: that treats index-two subgroups between Gamma(8) and Gamma(4); every step here has index 3.
  mod-s2-torelli-positive-relations-have-bounded-mass: that asks for sup A_+ < infinity; this proves A_+ <= 20 at every computed Gamma_V (the MILP value is 20, twice A_+(Gamma(2)) = 10).
artifacts:
  - experiments/mod-s2-three-sylow-census-2026-09-17/sylow.py
  - experiments/mod-s2-three-sylow-census-2026-09-17/pbar.py
  - experiments/mod-s2-three-sylow-census-2026-09-17/fastelim.py
  - experiments/mod-s2-three-sylow-census-2026-09-17/orbits.py
  - experiments/mod-s2-three-sylow-census-2026-09-17/tietze_chain.py
  - experiments/mod-s2-three-sylow-census-2026-09-17/orbits.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/sylow-U.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/pbar-U.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/pbar-U-fast.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/pbar-max0.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/pbar-max1.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/pbar-max2.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/pbar-phi-fast.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/tz-U.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/tz-max0.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/tz-max0-fast.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact_d.py
  - experiments/mod-s2-three-sylow-census-2026-09-17/w-U.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact-U.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/w-max0.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact-max0.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/w-max1.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact-max1.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/w-max2.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact-max2.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/w-phi.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/exact-phi.json
  - experiments/mod-s2-three-sylow-census-2026-09-17/run-check-phi.log
---

**ESTABLISHED** through `mod-s2-three-sylow-torelli-census-proof`. This is a machine computation.
It is unreviewed, and no novelty is claimed.

**Notation.** As in `mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit` (classes `v_c`,
relation lattice `W`, distance `d`), with `A_+` as in
`mod-s2-induced-torelli-characters-have-positive-relation-floors`.
- `U` is a 3-Sylow subgroup of `Sp_4(F_3)`. In `sylow.py` (`sylow_U`), in the basis of `census.py`, it is
  cut out by the row conditions `e_0 A = e_0` and `e_2 A in e_2 + F_3 e_0`. It has order 81 (asserted)
  and Frattini quotient `F_3^2`.
- For `V <= U` put `Gamma_V = { A in Sp_4(Z) : A = I mod 2, A mod 3 in V }` and
  `M_V = pi^(-1)(Gamma_V)`.
- The chain is `U > max_k > Phi = Phi(U) > Z(U) > 1`, with orders `81, 27, 9, 3, 1`.
  - `max_0, ..., max_3` are the four maximal subgroups. Under `Sp_4(F_3)`-conjugacy `max_2 ~ max_3`, and the
    other two are alone in their classes (`orbits.json`).
  - `Phi = (Z/3)^2` is abelian. Of its four order-3 subgroups, one is `Z(U)` and the other three are
    conjugate.
- `Gamma_1 = Gamma(6)`.
- `[Gamma(2) : Gamma_U] = 640` is prime to 3. Every later step has index 3 or 9.

**Statement.** For `V` in the table, `H_1(M_V; Z)`, the census and the positive floor are as listed.
"cosets" is the index of the image of `M_V` in `Pbar = PMod(S_{0,6})`, which is `[Gamma(2) : Gamma_V] / 2`.
"counts" lists the distinct numbers of (Pbar coset, triple) pairs per class. The classes, `W`, `d` and
`A_+` depend only on the set of distinct classes, not on these multiplicities.

Every entry of the table is exact, except the column "MILP" (see below). In every row:
- `gcd aug W = 10`;
- **`d(Gamma_V) = 1/30` exactly.** The upper bound is an explicit point of `W^perp`, namely the constant
  `theta = 3/10`, checked in rationals. The lower bound has two proofs (route, Step 4). The first applies
  `mod-s2-short-generated-torelli-relations-pin-one-thirtieth` to an LLL basis of `W` satisfying (SG).
  The second is the independent box certificate of `exact_d.py`, checked in rationals;
- there is `w in W` with `||w||_1 = 12` and `aug(w) = 10`, so (TA3) alone gives only `d >= 1/36`;
- `A_+ <= 20`, by an explicit `w >= 0` in `W` with `aug(w) = 20`. Since `gcd aug W = 10`, `A_+` is 10 or 20.

The column "MILP" gives floating-point MILP optima (HiGHS, via scipy), which are not certified. They are
the least `||w||_1` of a `w in W` with `3` not dividing `aug(w)` (always 12), and `A_+` (always 20).

"SG" gives the largest `l1` among LLL basis rows with `aug = 0` and among rows with `|aug| = 10`. No row
has any other augmentation. So (SG) holds whenever the entries are at most 30 and at most 20.
- At `Phi` the plain LLL basis has one row of type `(10, 22)`, so it fails (SG) as it stands.
- The split test `exact_d.sg_split` repairs this. It finds `w_1` with `aug = 10` and `||w_1||_1 = 16`
  (not `>= 0`), and an LLL basis of `W_0` with `l1 <= 24`, whose union with `w_1` has the HNF of `W`.
- That union satisfies (SG) (entry "split").

| `V` | order | cosets | `H_1(M_V)` | classes | counts | `rank W` | `d` | SG | MILP: min l1, `A_+` |
|---|---|---|---|---|---|---|---|---|---|
| `U` | 81 | 320 | `Z^16 + (Z/3)^5` | 50 | 32, 64, 96 | 34 | 1/30 | 12, 12 | 12, 20 |
| `max_0` | 27 | 960 | `Z^18 + (Z/3)^10` | 100 | 96 | 82 | 1/30 | 14, 18 | 12, 20 |
| `max_1` | 27 | 960 | `Z^28 + (Z/3)^4` | 140 | 32, 288 | 112 | 1/30 | 16, 18 | 12, 20 |
| `max_2 ~ max_3` | 27 | 960 | `Z^16 + (Z/3)^5` | 50 | 96, 192, 288 | 34 | 1/30 | 12, 12 | 12, 20 |
| `Phi` | 9 | 2880 | `Z^30 + (Z/3)^8` | 180 | 96, 288 | 150 | 1/30 | 24, 22; split 24, 16 | 12, 20 |

**Consequences.**
1. *No decay at the first 3-power steps.* By (TA2), `d(Gamma'') <= d(Gamma')` for `Gamma'' <= Gamma'`, so
   `d = 1/30` for every group `Gamma'` with `Gamma_Phi <= Gamma' <= Gamma(2)`. This includes all 3-power
   index subgroups between `Gamma_Phi` and `Gamma_U`. None of these is reached by a transfer certificate
   from `Gamma(2)`: transfer multiplies `||w||_1` and `aug(w)` by the index, and `3` divides every index
   below `Gamma_U`.
2. *Single certificates stop being sharp.* At every level of the census of
   `mod-s2-torelli-abelian-scalar-gap-is-a-monomial-census-limit`, one relation `w` meets (TA3) with
   equality, `1/(3 ||w||_1) = d`. Here the best single relation found has `||w||_1 = 12`, which gives
   `1/36 < 1/30` (and MILP says 12 is least). The exact value needs the joint constraint of a whole basis
   of `W` together with the positive transfer relation `5 1_X`. This is the hypothesis (SG) of
   `mod-s2-short-generated-torelli-relations-pin-one-thirtieth`, which holds at every row (column "SG").
   So a proof of `inf_N d(Gamma(N)) > 0` cannot rest on exhibiting one short relation per level. It has
   to control several relations at once, and short generation of `W` is one way to do this.
3. *Positive floor.* `A_+ <= 20` at every computed `Gamma_V`, so (TA3) gives `d >= 1/60` from positive
   relations alone. The MILP value `A_+ = 20` would mean a single doubling from `A_+(Gamma(2)) = 10`,
   with no growth after that.
4. *Torsion.* The only torsion is 3-primary and elementary abelian. It appears already at `Gamma_U`.

**Scope.** `Z(U)`, the other order-3 subgroups of `Phi` and `V = 1` (that is, `Gamma(6)`) are not
covered. See `## Attempts` of `mod-s2-torelli-abelian-census-limit-is-positive` for their status.
