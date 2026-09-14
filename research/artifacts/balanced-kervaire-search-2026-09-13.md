# Balanced Kervaire killing search, two generators (2026-09-13)

Lane hl-balanced-kl-search. Target: `kervaire-killing-failure-over-deficiency-zero-group-exists`.

## 1. What a witness must satisfy (filter theorem)

`deficiency-zero-kervaire-failure-forbids-finite-quotients` (landed in 56f8f8ca2,
renamed to a valid id in 58aa5ecdc):
- `H_1(G) = 0`, so the relator exponent matrix has determinant `+-1`;
- the presentation complex is acyclic and `G` is superperfect;
- `G` has no nontrivial finite quotient, and no nontrivial finite-dimensional
  unitary representation.

One certified nontrivial finite quotient of `G` rules out every killing word `w`,
of any length.

## 2. Census (MSI, `census_balanced.py`, md5 in logs)

Two-generator balanced presentations `<x, y | r1, r2>` with cyclically reduced
relators and `det = +-1`, up to rotation, inversion, relator swap and the 8
signed generator permutations.

| total length L | classes with det = +-1 | cumulative |
|---|---|---|
| 2 | 1 | 1 |
| 3 | 1 | 2 |
| 4 | 1 | 3 |
| 5 | 2 | 5 |
| 6 | 3 | 8 |
| 7 | 11 | 19 |
| 8 | 17 | 36 |
| 9 | 54 | 90 |
| 10 | 91 | 181 |
| 11 | 349 | 530 |
| 12 | 591 | 1121 |
| 13 | 2359 | 3480 |
| 14 | 4070 | 7550 |
| 15 | 17021 | 24571 |

(MSI jobs 747807 for L <= 13 and 748254 for L = 14, 15.)

## 3. Classification (MSI job 748253, GAP 4.13.1, `bal.g`, md5 in logs)

Per class, in order:
1. coset enumeration over the trivial subgroup (budget 200000 cosets):
   `TRIVIAL` (1 coset) or `FINITE n` (n > 1);
2. `LowIndexSubgroupsFpGroup` up to index 8: `QUOTIENT idx=k`;
3. `GQuotients` onto PSL(2,q) for q in {7,8,11,13,16,17,19,23,25}, A6, A7, A8,
   PSL(3,3), PSU(3,3), M11: `SIMPLE q`;
4. otherwise `OPEN`.

Calibration (job 747808): `<x, y | x, y>`, `<x, y | x^y = y^2, y^x = x^2>` and
AK(3) all return `TRIVIAL`; `<x, y | x^2 = y^3 = (xy)^5>` returns `FINITE n=2280`.

**L <= 13 (job 748253, 20 tasks, all COMPLETED; results md5 `fcab0572b897c33bb7aa22e6c0460900`).**
- 3480 classes: 3474 `TRIVIAL`, 6 `FINITE n=120`, 0 `QUOTIENT`, 0 `SIMPLE`, 0 `OPEN`.
- Every enumeration closed within the 200000-coset budget; the slowest took 4 ms.
- The six finite classes (each perfect of order 120, since `H_1 = 0`):

| id | L | r1 | r2 | order |
|---|---|---|---|---|
| 1098 | 12 | `XXYxY` | `XYYYYXy` | 120 |
| 2685 | 13 | `XXYxY` | `XXXYYYYY` | 120 |
| 2706 | 13 | `XXYxY` | `XYYYXyxy` | 120 |
| 3415 | 13 | `XYXYXy` | `XXXXXYY` | 120 |
| 3467 | 13 | `XYXyxy` | `XXXyxxy` | 120 |
| 3479 | 13 | `XYXyxy` | `XXyxYxy` | 120 |

Script md5s: `bal.g aacdc2535c7c4de96013e26f0d2a53dd`,
`census_balanced.py 9c06c60f275922de4f6f03c5b0c34c7c`,
`census13.txt a573de752d5f7afb0bce2d9f9eb23fb1`.

**Second enumerator (job 750365).** `tc_verify.py` (md5
`86266fbc645ab4ebcfdc58cb94cbacc3`), an HLT coset enumerator written independently of
GAP, re-checks each closed table as a consistent transitive action on which both
relators close. On all 3480 classes it returns 3474 `ORDER 1` and 6 `ORDER 120`
(output md5 `6a2c986f381255e6575ac66963b8e420`). Joining its output with GAP's by
class id gives 3480 matches and **0 disagreements**.

**Calibration of the second enumerator (job 750406)**, 10 presentations, both
implementations side by side:

| id | relators | Python | GAP |
|---|---|---|---|
| c1 | `x`, `y` | ORDER 1 | TRIVIAL |
| c2 | `xyXYY`, `yxYXX` | ORDER 1 | TRIVIAL |
| c3 | AK(3) `xxxYYYY`, `xyxYXY` | ORDER 1 | TRIVIAL |
| c4 | `xxYYY`, `xxYXYXYXYXYX` | ORDER 2280 | FINITE n=2280 |
| c5 | `xxxxx`, `y` | ORDER 5 | FINITE n=5 |
| c6 | `xx`, `yyy` (PSL(2,Z)) | OVERFLOW | QUOTIENT idx=3 |
| c7 | `xx`, `yy` (infinite dihedral) | OVERFLOW | QUOTIENT idx=2 |
| c8 | `xyXY`, `x` (Z) | OVERFLOW | QUOTIENT idx=2 |
| c9 | `xxx`, `xyxY` | OVERFLOW | QUOTIENT idx=2 |
| c10 | `xx`, `xyxyxyY` | ORDER 4 | FINITE n=4 |

The infinite groups overflow in the enumerator, as they must; the finite ones
agree in order.

**Census recount (job 751384).** `census_check.py` (md5
`77bd07e081172b20b4fcac3495005341`) enumerates every ordered pair of cyclically
reduced words and computes orbit minima under the move group by closure, with no
representative choice up front. Against `census13.txt` it gives per-length class
counts identical to the census for every L <= 9, <= 11, <= 12 and <= 13 (jobs
751384 and 751693), and at L <= 13: 3480 census classes, 0 duplicates, 0 missing,
0 extra, `MATCH`. At L <= 15 against `census15.txt` (md5 `88ce6d6c5600bd7df101de9b9966ea6a`), job
753123: identical per-length counts, 24571 census classes, 0 duplicates, 0 missing,
0 extra, `MATCH`.

**Finite-quotient certificates (job 751692).** `certs.g` (md5
`1eaa621c896b73cee8a4b2294b820deb`) exports, for each of the 24 order-120 classes
and the 8 index-7/8 classes, the permutation images of `x` and `y`: the regular
action read off the coset table, or the action on the cosets of the low-index
subgroup. `verify_certs.py` (md5 `67ce40e2058a4a1625e7b67085afaa7c`) evaluates both
relators letter by letter on every point and checks nontriviality, with no coset
enumeration: 32 PASS, 0 FAIL (degrees: 24 x 120, 3 x 7, 5 x 8; joined certificate
file md5 `8f2194a2d1ff388fdeaf21f4cd7f1ea4`). GAP writes long lines with `\`
continuations; the verifier runs on the joined file.

**L = 14, 15 (job 750364, 40 tasks, all COMPLETED, no NUL bytes, every chunk
complete; results md5 `9543a7245c7f0237df2e607e63efcaf1`).**
- 21091 classes: 21065 `TRIVIAL`, 18 `FINITE n=120`, 8 `QUOTIENT`, 0 `SIMPLE`,
  0 `OPEN`.
- By length: L = 14 gives 4066 trivial, 3 finite, 1 quotient; L = 15 gives 16999
  trivial, 15 finite, 7 quotient.
- The eight `QUOTIENT` classes overflowed the 200000-coset budget but have a
  proper subgroup of index 7 or 8, hence a nontrivial finite quotient:

| id | L | r1 | r2 | index |
|---|---|---|---|---|
| 7407 | 14 | `XXYxY` | `XYYYYYYXy` | 7 |
| 19009 | 15 | `XXYxY` | `XXXYYYYYYY` | 7 |
| 19146 | 15 | `XXYxY` | `XYYYYYXyxy` | 7 |
| 19600 | 15 | `XXYxyxY` | `XXXyxYxy` | 8 |
| 24191 | 15 | `XYXYXy` | `XXXXXXXYY` | 8 |
| 24468 | 15 | `XYXyxy` | `XXXXXyxxy` | 8 |
| 24477 | 15 | `XYXyxy` | `XXXXyxYxy` | 8 |
| 24513 | 15 | `XYXyxy` | `XXXyxYYxy` | 8 |

**Second enumerator on L = 14, 15 (job 751691).** `tc_verify.py` returns 21065
`ORDER 1`, 18 `ORDER 120` and 8 `OVERFLOW`, the overflows being exactly the eight
`QUOTIENT` classes above (output md5 `a8feedc246ca6cc067d978d3db065803`; input
`census_L1415.txt` md5 `00470fef9a671234c886c513f3db651d`). Joined with GAP's
results by class id: 21091 matches, 0 disagreements.

## 3b. Files

Directory `research/artifacts/balanced-kervaire-search-2026-09-13/`:
- `census_balanced.py`, `census_check.py`: census and independent recount.
- `bal.g`, `calib.g`: GAP classifier and its calibration.
- `tc_verify.py`, `tc_calib.txt`, `tc_calib_py.txt`, `tc_calib_gap.txt`: the second
  enumerator and the side-by-side calibration.
- `certs.g`, `verify_certs.py`, `certs_joined.txt`: exported finite-quotient
  certificates and their letter-by-letter verifier.
- `census13.txt`, `gap_L13.txt`, `tc13.txt`: the L <= 13 census and both enumerators'
  outputs.
- `gen_words.py`, `collapse.g`: the staged killing test (not run; no survivors).
- Job logs: `census.747807.log`, `census15.748254.log`, `calib.747808.log`,
  `tccal.750406.log`, `tc13.750365.log`, `tc15.751691.log`, `certs.751692.log`,
  `ccheck.751384.log`, `rc13.751693.log`.

The L = 14, 15 inputs and outputs are not landed, being about 2 MB. They are
reproducible with `census_balanced.py 15` and the two enumerators, and sit on MSI in
`/scratch.global/sauer354/hl-balanced-kl-search/` with md5s:
- `census_L1415.txt` `00470fef9a671234c886c513f3db651d`;
- GAP results (sorted) `9543a7245c7f0237df2e607e63efcaf1`;
- `tc15.txt` `a8feedc246ca6cc067d978d3db065803`.

## 4. Survivors and collapse test

There are no survivors at total length at most 15. Every class with trivial
abelianization is trivial, finite of order 120, or has a finite quotient of index
7 or 8. So there is no group on which to run the killing test, and the staged
collapse pipeline (`gen_words.py`, 3360 unimodular words per group with up to five
`t`-letters; `collapse.g`, which certifies a killing by a one-coset enumeration)
was not run.

Observation, not a claim: the order-120 groups and the eight index-7/8 classes
come in a few relator families (`XXYxY` with `XYYYY...Xy`, `XYXyxy` with
`XXX...xy`). Presumably these are SL(2,5) and quotients mapping onto small
permutation groups; none was identified.

## 5. Exact gap

- **Two generators, length 16 and up.** The census at total length 16 has an
  estimated 60000+ classes. It needs the same pipeline with a larger coset budget,
  and for survivors a search of simple quotients beyond PSL(2,q), q <= 25, A6, A7,
  A8, PSL(3,3), PSU(3,3) and M11, before any killing test.
- **Three or more generators.** Not touched. Balanced presentations with three
  generators and short relators are the natural next family: they include many
  known presentations of the trivial group, and small-cancellation proper-power
  relators, which give infinite hyperbolic groups with torsion.
- **Where a witness must live.** A deficiency-zero killing failure needs a
  superperfect group with no finite quotient, an acyclic presentation complex and
  torsion. In short presentations, trivial abelianization almost always forces the
  group to be trivial or finite. So a witness needs relators long enough for
  small-cancellation behaviour, which total length 15 in two generators does not
  allow: there the 3474 + 21065 trivial classes dominate.
- **No certified candidate** exists anywhere yet.
