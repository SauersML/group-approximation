# Hyperbolic triangles of finite simple groups: explicit candidates and first quotient searches

Lane `ex-hyperbolic-vtf`, 2026-09-12. Computational calibration only; it decides nothing.
Scripts and raw outputs: `experiments/hyperbolic-vtf-triangles/` (GAP 4.14 via
`module load sagemath/10.7`, `sage -gap`, on MSI; each run took seconds to minutes).

## 1. Why this class

By `simple-vertex-groups-vtf-iff-some-finite-quotient`, consider a hyperbolic triangle of
finite simple groups with nontrivial edge groups and trivial face group. Its fundamental
group is virtually torsion-free iff it has one nontrivial finite quotient. Every
nontrivial homomorphism is injective on all three vertex groups, and a member without
finite quotients decides both roots
(`hyperbolic-simple-triangle-group-without-finite-quotients`).

## 2. Presentations

```text
G = < p, q, r | R_A(p,q), R_B(q^e1, r), R_C(r^e2, p^e3) >
```

- `R_X(u,v)` are the relators of `X` in a generating pair `(x_X, y_X)` of elements of
  order 7 (GAP `IsomorphismFpGroupByGenerators`).
- Vertex groups `A = <p,q> ≅ A_7`, `B = <q,r> ≅ A_7`, `C = <r,p> ≅ A_8`.
- Edge groups `<p>, <q>, <r> ≅ Z/7`, and the face group is trivial.
- The exponents `e_i in {1..6}` twist the edge identifications. They do not change the
  links.

The link at a vertex is the coset graph `Γ(X; <x_X>, <y_X>)`. Its girth was computed by
breadth-first search (`girth_lib.g`). Pairs were chosen with girths `6, 6, 8`, so the
half-girth type is `(3,3,4)` and `1/3 + 1/3 + 1/4 < 1`. By Caprace–Conder–Kaluba–Witzel
Theorem 3.1 (v), `G` is infinite, non-elementary and word-hyperbolic. Also
`χ_orb = 1/2520 + 1/2520 + 1/20160 - 3/7 + 1 = 11537/20160`.

**Girth data** (random pairs of elements of order 7, `girth_scan.out`):

| vertex group | samples | girth 4 | girth 6 | girth 8 |
|---|---|---|---|---|
| `PSL(2,8)` | 58 | 58 | 0 | 0 |
| `A_7` | 59 | 38 | 21 | 0 |
| `PSL(2,13)` | 59 | 54 | 5 | 0 |
| `A_8` | 60 | 17 | 33 | 10 |
| `PSL(2,27)` | 40 | 22 | 18 | 0 |
| `PSL(2,29)` | 30 | 19 | 9 | 2 |

This matches the Moore bound: girth 6 needs at least 43 cosets per side, and girth 8 at
least 259.

**The four candidates** (`tri_run2.g`, verbatim):

| # | `A` pair | `B` pair | `C` pair | `e` |
|---|---|---|---|---|
| 1 | `(1,4,6,3,5,7,2), (1,4,6,3,7,2,5)` | `(1,6,4,7,2,5,3), (1,5,4,7,3,2,6)` | `(2,6,5,8,3,7,4), (1,2,7,4,3,6,8)` | `[4,2,4]` |
| 2 | `(1,5,3,2,7,4,6), (1,7,4,2,3,6,5)` | `(1,3,4,7,5,2,6), (1,7,4,5,6,3,2)` | `(2,6,3,7,4,5,8), (1,4,3,5,7,8,6)` | `[1,3,3]` |
| 3 | `(1,3,6,7,4,5,2), (1,6,5,3,4,7,2)` | `(1,7,6,4,2,5,3), (1,3,4,2,6,5,7)` | `(1,8,4,7,3,5,2), (1,4,6,2,3,8,7)` | `[4,3,3]` |
| 4 | `(1,6,7,4,5,2,3), (1,5,6,3,4,2,7)` | `(1,3,2,7,4,6,5), (1,2,7,5,4,3,6)` | `(1,8,4,3,6,5,2), (1,8,6,4,2,7,3)` | `[3,3,6]` |

## 3. Search method (complete within each target `S`)

For every class of elements of order 7 in `S`, fix a representative `p`.

1. Scan every element `q` of order 7 such that `(p,q)` satisfies `R_A` and generates a
   group of order `|A|`, with cheap prefilters on the orders of `pq`, `pq^-1`, `p^2 q`,
   `pq^2` and `[p,q]`. Keep `q` modulo `C_S(p)`.
2. For each kept `q`, scan every element `r` of order 7 such that `(q^e1, r)` satisfies
   `R_B` with order `|B|`, and `(r^e2, p^e3)` satisfies `R_C` with order `|C|`.

Every nontrivial homomorphism `G -> S` is vertex-injective, so it is found.

**Calibrations.**
- A literal Euclidean triple in `A_7`, `p = (1,7,4,6,5,2,3)`, `q = (1,2,4,7,6,3,5)`,
  `r = (1,6,3,2,7,4,5)`, has pairwise girth 6. With `e = [1,1,1]` the search finds 4
  homomorphisms into `A_7`, and 2 each into `A_9`, `A_10`, `A_11`: the inclusions
  (`tri_cal2.out`). So the enumeration does find homomorphisms that exist.

**Results** (`tri_run.out`, `tri_run2.out`): for each candidate, the number of
homomorphisms is 0 into each of `A_8`, `A_9`, `A_10`, `A_11`, `A_12`, `A_13` and
`Sp_6(2)`.

## 4. What the zeros mean (mostly nothing)

**The alternating zeros are forced for the whole family.** Take `S = A_n` with
`n <= 13`. Here every element of order 7 is a 7-cycle. The transitive actions of `A_7`
have degrees 1, 7, 15, …, and those of `A_8` have degrees 1, 8, 15, ….
- A vertex-injective image of `A` is a natural `A_7` on a 7-set equal to the support of
  `φ(q)`, and so is the image of `B`.
- So `φ(p)` and `φ(r)` both lie in `Alt(supp φ(q))`, which has order 2520, and cannot
  generate the image of `C ≅ A_8`.

So no member of this family, twisted or not, maps nontrivially into `A_n` for
`n <= 13`. The zeros there are a support argument, not evidence.

**`Sp_6(2)` is the only target that is informative.** It contains both `A_7` and `A_8`,
and the argument above does not apply. The zero there is weak data.

**Scale.** Caprace–Conder–Kaluba–Witzel searched simple quotients up to order `5·10^7`
and alternating quotients up to degree 30–40 (sometimes 40). Their Remark 5.16 shows
that such searches miss large congruence quotients. Genuine alternating evidence for
this family starts at degree 15, where `A_7` and `A_8 = L_4(2)` act on 15 points. That
needs the embedding-based enumeration, whose cost is `|C_S(t)|` per class, not a scan
of the conjugacy class.

## 5. The canonical chamber-transitive choice does not exist (parity of type changes)

A natural simple-vertex hyperbolic triangle over `F_2` would be chamber-transitive of
half-girth type `(4,3,3)`. It would take:
- vertex groups `A_6`, acting on GQ(2,2) through duads and synthemes, and two copies of
  `L_3(2)`, acting on PG(2,2) through points and lines;
- edge groups `S_4`;
- face group `D_8`.

The links check out: girth 8 and girth 6, all degrees 3 (`tri334_run.out`). But no such
triangle of groups exists.
- In each vertex group the two edge subgroups meet in `B = D_8`, and their normal
  Klein four-groups `O_2` are the two different Klein four-subgroups of `B`: elations
  with centre `p` versus axis `ℓ`, and `<(34)(56),(35)(46)>` versus `<(12)(34),(34)(56)>`.
- So an isomorphism between edge subgroups of different types restricts to an outer
  automorphism of `D_8`. One of the same type restricts to an inner one, because
  `N_{S_4}(D_8) = D_8`.
- Around the triangle the number of type-changing edges is
  `[a≠b] + [1-a≠c] + [b≠c] ≡ 1 (mod 2)` for every choice of types `a, b, c`.
- So the face holonomy is outer, and no consistent face embedding exists.

Exhaustive enumeration agrees: for all 8 type patterns and all `8·8·8` edge
isomorphisms mapping face to face, the number of consistent triples is 0
(`tri334_run.g`, `tri334_run.out`). The same code and argument give 0 for
`(L_3(2), L_3(2), L_3(2))` with face `D_8` (`tri333_cal.g`). That is consistent with the
known chamber-transitive `Ã_2` groups over `F_2` having vertex groups `7:3` and trivial
chamber stabilizers, but it means the run is not an independent calibration of the
code. The random-twist candidates of §2 have trivial face groups, so this holonomy
issue does not arise for them.

**Heuristic, not a proof.** The expected dimension of `Hom(G, GL_7)` modulo conjugation
is `47 + 47 + 48 - 3·42 - 48 = -32`. This takes `A_7` via `6+1`, `A_8` via `7`, and
`Z/7` with 7 distinct eigenvalues. Larger `d` are worse in every splitting into trivial
and nontrivial parts. So neither low-dimensional linear quotients nor, heuristically,
alternating quotients (count about `|S|^(-χ_orb)`) are expected. Rigid representations
can exist regardless.
