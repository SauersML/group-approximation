---
rg: 2
id: mod-s2-level-six-torelli-census-has-no-transversal
kind: claim
title: At level six the 900 separating-twist classes of pi^-1 Gamma(6) admit no transversal relation, already modulo 3, so A_+(Gamma(6)) >= 20 and the mass-10 certificate of levels two and four dies at the first odd-index step
distinct_from:
  mod-s2-level-eight-index-two-torelli-census: that proves (BS) and finds a transversal relation in all 1023 index-two subgroups of Gamma(4); this is the first subgroup of Gamma(2) where no transversal relation exists (Gamma(6), an odd-index step), shown by an exhaustive search modulo 3.
  mod-s2-gamma4-torelli-census-is-one-thirtieth: that computes Gamma(4), where A_+ = 10 and d = 1/30; this computes Gamma(6) modulo eight primes and shows that A_+ = 10 fails there.
  mod-s2-igusa-torelli-census-is-one-thirtieth: that is the 2-adic Igusa level Gamma(4,8), where the transversal survives; this is the odd step Gamma(2) cap Gamma(3), where it does not.
  mod-s2-torelli-positive-relations-have-bounded-mass: that asks for sup A_+ < infinity; this proves only the new lower bound A_+(Gamma(6)) >= 20, which raises the constant K there to at least 20 and does not refute the claim.
  mod-s2-torelli-abelian-census-limit-is-positive: that asks for d_inf > 0; this removes the mass-10 positive certificate at Gamma(6) but does not compute d(Gamma(6)), which stays in [1/60 if A_+ = 20 is attained, 1/30].
artifacts:
  - experiments/mod-s2-level-six-transversal-2026-09-17/level6_cosets.py
  - experiments/mod-s2-level-six-transversal-2026-09-17/level6_reduce.py
  - experiments/mod-s2-level-six-transversal-2026-09-17/level6_dump.py
  - experiments/mod-s2-level-six-transversal-2026-09-17/validate_dump.py
  - experiments/mod-s2-level-six-transversal-2026-09-17/rs_elim.cpp
  - experiments/mod-s2-level-six-transversal-2026-09-17/level6_lattice.py
  - experiments/mod-s2-level-six-transversal-2026-09-17/level6_modp.py
  - experiments/mod-s2-level-six-transversal-2026-09-17/level6_sat.py
  - experiments/mod-s2-level-six-transversal-2026-09-17/mitm.cpp
  - experiments/mod-s2-level-six-transversal-2026-09-17/mitm_prep.py
  - experiments/mod-s2-level-six-transversal-2026-09-17/mitm_check.py
  - experiments/mod-s2-level-six-transversal-2026-09-17/mitm_plant.py
  - experiments/mod-s2-level-six-transversal-2026-09-17/wperp_ratrec.py
  - experiments/mod-s2-level-six-transversal-2026-09-17/wperp_lll.py
  - experiments/mod-s2-level-six-transversal-2026-09-17/level6-results.json
---

**OPEN** (computation complete, not refereed). Every step is an exact computation (over `Z`, or
over `F_p` for the eight primes listed) or a stated consequence of one. Two points are not proved in
this note, and they are why the node is OPEN rather than ESTABLISHED:
- the class count 900 (item (L6-2)) uses the label/orbit argument sketched below, which is not
  written as a separate proof node;
- the correctness of the modular elimination code at level six is checked indirectly (items (V1) to
  (V4)), not by a second independent implementation.

Notation follows `mod-s2-level-eight-index-two-torelli-census`.
- `M'' = pi^(-1)(Gamma(6))`. Since `-I` is not in `Gamma(6)`, this maps isomorphically into
  `K2 = PMod(S_(0,6))` as the stabiliser of a point of `Sp_4(F_3)/{+-1}` (25920 cosets).
- `v_c` is the class of a conjugate of a separating twist in `H_1(M''; Z)`.
- `W` is the relation lattice on the distinct classes.
- A transversal relation is a 0/1 vector in `W` with exactly one `1` over each of the 10 level-two
  splittings.
- `A_+` is the least augmentation of a nonzero `w >= 0` in `W`.

## Statement

- **(L6-1) Homology modulo p.** Take the abelianised Reidemeister–Schreier relator matrix of `M''`
  (Artin presentation of `K2`, 25920 cosets). After exact unit elimination over `Z` it has 3466
  columns. Its rank modulo `p` is 3358 for each
  `p in {2, 3, 5, 7, 11, 13, 2147483629, 2147483647}`.
  - So `dim H_1(M''; F_p) = 108` for these `p`, and `b_1(M'') <= 108`.
  - If `b_1 = 108`, then `H_1(M''; Z)` has no `p`-torsion for these primes.
- **(L6-2) Classes.** There are exactly 900 twist classes, 90 over each level-two splitting. They are
  labelled by (level-two splitting, ordered mod-3 splitting `(P, P^perp)`). The index
  `[Sp_4(Z/6) : image of Stab(splitting)] = 720 * 51840 / (36 * 576 * 2) = 900`.
  - Classes are pairwise distinct modulo every one of the eight primes. This is a lower bound, since
    distinct modulo `p` implies distinct in `H_1`.
  - Over all 3036 sampled twist vectors the label is constant on classes and injective.
- **(L6-3) Spans.** The 900 classes span `H_1(M''; F_p)` in dimension 108 for `p >= 5` and 98 for
  `p = 2, 3`.
  - The linear relaxation (some `w in W` with every block sum equal to `1`) is solvable modulo every
    prime, and therefore over `Z`: `aug(W) = 10 Z`, since `W_p = W + p Z^900` (see Proof).
  - So the constant character `theta = 3/10` is in `Ann(W)`, and `d(Gamma(6)) <= 1/30`.
- **(L6-4) No transversal modulo 3.** Let `Phi_3(v_c)` be the image in `H_1(M''; F_3) = F_3^108`.
  Every choice of one class over each splitting has `sum Phi_3 != 0`. This covers all `90^10`
  choices and is decided by an exhaustive meet-in-the-middle search: `mitm.cpp`, all
  `2 * 90^5 = 1.18e10` half-sums enumerated, 0 solutions.
  - The same search modulo 2 finds exactly `7626240 = 2^9 * 3^2 * 5 * 331` transversals of `W_2`.
    Every one checked fails modulo 3 and modulo each other prime. So parity alone does not see the
    obstruction.
  - The same exhaustive search modulo 5 (`K = 7`) and modulo 7 (`K = 6`) also finds 0 solutions, over
    `1.18098e10` pairs each (`level6-results.json`, field `mitm`). So the obstruction is not only
    3-adic: no transversal exists in `W_3`, `W_5` or `W_7`.
- **(L6-5) Consequences.**
  - `W(Gamma(6))` contains no transversal relation.
  - By (BS3) of `mod-s2-level-eight-index-two-torelli-census`, `A_+(Gamma(6)) >= 20`.
  - Every `w in W(Gamma(6))` with `3 not| aug(w)` has `||w||_1 >= 12`. By (BS), `||w||_1 >= 10 |s|`,
    where `s` is the common block sum. Equality at `|s| = 1` forces `+-` a transversal. And
    `||w||_1 = aug(w) = 10 s (mod 2)`.
  - By (BS3), the positive mass-10 certificate that gives `d = 1/30` at `Gamma(2)`, at `Gamma(4)`, at
    all index-two subgroups of `Gamma(4)` and at `Gamma(4,8)` does not exist at `Gamma(6)`.
    `d(Gamma(6)) = 1/30` would need a non-positive certificate or a longer one.

## Proof (with the computational inputs)

1. **Phase 0 is exact.**
   - Unit elimination over `Z` replaces the relator lattice by an equivalent one.
   - So `Z^3466 / L = H_1(M'')`, and `Z^3466 / (L + p Z^3466) = H_1(M''; F_p)`.
   - `rs_elim.cpp`, in modular mode, computes a greedy RREF over all live rows modulo `p`, and the
     residue of each twist vector at the non-pivot columns. The residue is the coordinate vector of
     `Phi_p(v)` in the basis given by the non-pivot columns. This gives (L6-1).
2. **`W_p = W + p Z^900`.**
   - Let `V = Z^900 / W`. This is the subgroup of `H_1` spanned by the classes.
   - `Q/Z` is injective, so every character `V -> (1/p)Z/Z` extends to `H_1`.
   - Hence the order-`p` characters of `V` are exactly the restrictions of `Hom(H_1, F_p)`, and their
     common kernel `W + p Z^900` equals `W_p = ker(Z^900 -> H_1 (x) F_p)`.
   - In particular a 0/1 transversal in `W` would be one in `W_3`, which (L6-4) excludes.
   - The same argument gives `aug(W) = 10 Z` in (L6-3). Let `s` be the gcd of the block sums. Then
     `p not| s` for `p = 2, 3, 5` (and the other primes tested). Also `s` divides the block sum of the
     transfer relation `5 m`, which is `5 * 25920 * 3/10 * ...` and has only prime factors
     `2, 3, 5`. So `s = 1`.
3. **Class count.**
   - The separating curves with a given integral splitting form one Torelli orbit. The stabiliser of
     `s` in `M` surjects onto the stabiliser of `{P, P^perp}` in `Sp_4(Z)`, which is
     `(SL_2 Z x SL_2 Z) : 2`.
   - So `M''`-classes of twists correspond to `Gamma(6)`-orbits of splittings. Since `Gamma(6)` is
     normal, these correspond to cosets of the image of the splitting stabiliser in `Sp_4(Z/6)`, and
     that image has index 900.
   - The mod-`p` distinctness gives at least 900 classes, independently.
4. **Exhaustiveness of (L6-4).**
   - The blocks are split as `{0,1}, {2,3,4}, {5,6}, {7,8,9}`.
   - For every value `t` of the projection to the first 10 coordinates, all left half-sums with
     projection `t` are joined with all right half-sums with projection `-t`, on a 64-bit hash of the
     full vector, and every hash hit is confirmed by exact comparison.
   - The coordinates kept (`mitm_prep.py`) are independent on the span of the 900 rows, so the
     zero-sum test on them is equivalent to the zero-sum test in `F_3^108`.
   - The number of left or right pairs visited is `1.18098e10 = 2 * 90^5`, as printed.

**Validation.**
- (V1) The same pipeline (`rs_elim` modular mode, `level6_modp.py`) at `Gamma(4)` reproduces the
  integral census of `mod-s2-gamma4-torelli-census-is-one-thirtieth`: rank 806, 160 classes, 16 per
  splitting, and a transversal valid modulo all eight primes.
- (V2) `mitm.cpp` on the `Gamma(4)` data finds 1024 transversals modulo 3 and 1024 modulo 5. All 1024
  modulo 3 satisfy all eight primes, and they include the transversal found by the exact integral
  computation.
- (V3) Planted control. `mitm_plant.py` (seed 17) plants the transversal
  `{175, 246, 275, 350, 370, 396, 621, 625, 693, 842}` in a copy of the level-six mod-3 input. The
  full search then reports exactly that one solution, and no other, over the same `1.18098e10`
  pairs (`level6-results.json`, field `planted_control_mod3`).
- (V4) The CryptoMiniSat mod-2 transversal and 50 `mitm` mod-2 transversals are rechecked exactly.
  All satisfy `p = 2` only.
- The rational `W^perp` reconstructed from the two 31-bit primes agrees with the RREF modulo
  5, 7, 11 and 13, including the pivot sets (`wperp_ratrec.py`). This is evidence that
  `b_1(M'') = 108`, not a proof.

## What it changes

- In the census so far, every subgroup of `Gamma(2)` computed exactly (`Gamma(4)`, its 1023
  index-two subgroups, `Gamma(4,8)`) had a transversal relation. That was the only positive
  certificate known to give `d = 1/30`.
- `Gamma(6)` is the first odd-index step below `Gamma(2)`, and the bounded-mass note names it as the
  next hole. There the transversal is excluded, by a mod-3 obstruction.
- So the sharp conjecture `d_inf = 1/30` cannot be proved through (BS3) with mass-10 certificates.
- The sparse-certificate route of `mod-s2-torelli-abelian-census-limit-is-positive` needs `l1 >= 12`
  at level six, against `l1 = 5` at level three.

## Open

- **`d(Gamma(6))`: `1/30`, or smaller?** `d(Gamma(6)) < 1/30` would refute the sharp form.
  - Real characters need an integral basis of `W^perp`. The rational reconstruction has denominators
    up to `2.8e7`, and LLL of the cleared rows does not find short vectors, because that lattice is
    not saturated.
  - Characters of order dividing `30030` (from the six small primes) are one feasible test.
- **`A_+(Gamma(6))`: is it 20?** The next test is a mod-3 meet-in-the-middle search for `w >= 0` with
  all block sums 2.

## Attempts

This section records the attacks on the two open items, `d(Gamma(6))` and `A_+(Gamma(6)) = 20`, and
where each one stops.

### 2026-09-19, swarm-0917-w18c-w18c-deligne-follow (census-computation): the direct attacks on the two open questions

- **SAT for the transversal.**
  - `level6_sat.py` encodes "one class per block, sum 0 modulo 3" for CP-SAT. It returned UNKNOWN
    after 1201 s.
  - The CryptoMiniSat encoding modulo 2 finds a transversal of `W_2`, and it fails modulo 3.
  - Both are superseded by the exhaustive `mitm.cpp`, which settles (L6-4) and needs about 8 minutes
    per prime on 4 cores.
- **Integral `W^perp` for `d(Gamma(6))`.**
  - `wperp_ratrec.py` reconstructs the rational RREF of `W^perp` (rank 108) from the two 31-bit
    primes. Its denominators are up to `2.8e7`, and it agrees with the RREF modulo 5, 7, 11 and 13.
  - `wperp_lll.py` runs LLL on the cleared rows and gets entries up to `2.8e7`. That lattice is not
    saturated, so it is not `W^perp cap Z^900`, and no short real character comes out.
  - Where it dies: the saturation needs either a Hermite normal form of the 108 x 900 cleared matrix,
    or `W` itself over `Z`. Neither was run.
- **`A_+ = 20`?** Deferred.
  - The natural attack is `mitm.cpp` over multisets with two classes per block. That has `C(91,2)^10`
    choices, and the half-lists become about `4.1e3^5`, which is out of reach as written.
  - One could restrict to `w = t_1 + t_2` with `t_1`, `t_2` transversals of `W_2`, using the 7626240
    mod-2 solutions. That tests only a subfamily.
