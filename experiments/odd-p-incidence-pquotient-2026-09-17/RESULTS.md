# Odd-modulus graph incidence systems: p-quotient survival of the phase J (2026-09-17, sw-005)

Tools: GAP 4.12.1 (`EpimorphismPGroup`) and Python 3 (exact monomial checker).
Every run: `nice -n 10 timeout 1200 gap -q -o 2g <script>`.

`Gamma_p(G,b)` is the solution group of the oriented incidence system of `G`
over `Z_p` with `b=delta_1`, so there is no classical solution.  "J
survives" means the image of `J` in the largest p-quotient of class `<= c` is
nontrivial.  That gives a finite quotient in which `J` survives, and hence a
finite-dimensional operator solution.

## Calibration (p=2), `run_calib.g`

| graph | class 1 | class 2 | expected |
|---|---|---|---|
| K_{3,3} (magic square) | dies (2^4) | **survives** (2^5) | Pauli solution (Arkhipov) |
| cube (planar) | dies | dies through class 4 | J=1 for planar graphs |
| Heawood | dies (2^8) | **survives** (2^23) | nonplanar, so Pauli |

## p=3, `run_p3.g`, `run_batch3.g`, `run_batch_more.g`, `run_k44.g`

| graph | (min deg, girth) | class<=2 | class 3 | note |
|---|---|---|---|---|
| K_{3,3} | (3,4) | dies | dies (quotient stabilises at 3^4) | |
| K_4 | (3,3) | dies | dies (3^3, stable) | |
| K_5 | (4,3) | dies | dies (3^6, stable) | |
| Petersen | (3,5) | dies (3^11) | dies (3^23); class 4 dies (3^39) | |
| K_{4,4} | (4,4) | dies (3^21) | dies (3^57); class 4 dies (3^128); class 5 dies (3^308) | J has order 3 in Gamma (Slofstra-Zhang) |
| **Heawood** | (3,6) | dies (3^22) | **survives** (3^79) | reduced to order 3^17, class 3, exponent 9 |
| **Moebius-Kantor** | (3,6) | dies (3^29) | **survives** (3^126) | |
| **Pappus** | (3,6) | dies (3^37) | **survives** (3^188) | |
| **Desargues** | (3,6) | dies (3^46) | **survives** (3^267) | |
| **Tutte 8-cage** | (3,8) | dies (3^106) | **survives** (3^987) | |

Every class `<= 2` death is forced by the Lazard argument
(`research/lcs-phase-dies-in-every-nilpotent-quotient-of-class-below-p.md`).

## Exact certificate: `reduce.g`, `monomial.g`, `verify_monomial.py`

- The class-3 quotient of `Gamma_3(Heawood)` has order `3^79`.  Factoring out
  central hyperplanes avoiding `J` gives a quotient `P` with `|P|=3^17` and
  `Z(P)=<J>`.
- All relators of `Gamma` are re-evaluated on the images and hold.
- `P` has a self-centralizing abelian normal subgroup `A` with `|A|=3^9`.
  Inducing a linear character `chi` with `chi(J)=zeta_3^2` gives a monomial
  representation of dimension `3^8 = 6561`.  It is stored in
  `heawood_p3_monomial.json.gz`, with 21 edge matrices and then `J`.
- `python3 verify_monomial.py heawood_p3_monomial.json heawood 3` (after
  `gunzip -k`) prints `OK: heawood, p=3: exact operator solution in
  dimension 6561; ...`.
- Changing one phase makes it fail (`X_0^p != I`).

## Minor minimisation: `minor.g`, `run_minor2.g`, `run_minor3.g`

Deletion and contraction induce surjections of solution groups that fix `J`
(proof in `research/z3-heawood-exact-monomial-certificate.md`).

- p=2, class 2, starting from Heawood: ends at `K_{3,3}`.  Calibration
  passes.
- p=3, class 3, starting from Heawood: ends at an 11-vertex, 17-edge minor
  with degrees `[3,4,3,3,3,3,3,3,3,3,3]` and edges
  `[1,2],[2,3],[3,4],[4,5],[5,6],[6,7],[7,8],[8,9],[9,10],[10,11],[11,3],[1,5],[2,7],[4,9],[6,11],[8,1],[10,2]`.
  No single deletion or contraction of this minor survives at class 3.

## What is ruled out, and what is not

- For the five surviving graphs, and every graph having one of them as a
  minor, `Gamma_3(G,b)` has a finite quotient with `J` surviving.  So these
  are not nonhyperlinear (no R^U gap) candidates.
- `K_{4,4}` and Petersen show no survival at class `<=5` and `<=4`
  respectively.  That rules out only finite-dimensional solutions whose
  image is a 3-group of that class.  It says nothing about higher class or
  non-nilpotent images.
