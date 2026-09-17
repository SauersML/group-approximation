---
rg: 2
id: a2-type-kernels-have-no-small-non-up-pairs
kind: claim
title: The torsion-free Kazhdan type kernels of all triangle-presentation groups of order 2 and 3, including the 65 non-linear exotic ones, have no small-radius pair without unique products, hence no small zero divisors over any field
distinct_from:
  e33-no-unique-product-pairs-of-small-radius: that censuses E_3(3), a linear group lying in a 3-adic congruence kernel; this censuses vertex-regular Ã2 lattices, 65 classes of which have no infinite linear image over any commutative ring and so lie in no congruence kernel.
  kazhdan-groups-without-unique-products-are-zero-divisor-hosts: that sorts Kazhdan groups that provably lack unique products but have no normal form; this runs an exact census on explicit torsion-free Kazhdan hosts where unique products are unknown.
  exotic-a2-lattices-satisfy-boone-higman: that is about embedding exotic Ã2 lattices in simple groups; this is about unique products and zero divisors in their type kernels.
artifacts:
  - experiments/a2-non-up-2026-09-17/up_a2.py
  - experiments/a2-non-up-2026-09-17/a2group.py
  - experiments/a2-non-up-2026-09-17/summarize.py
  - experiments/a2-non-up-2026-09-17/presentations_q2_all.json
  - experiments/a2-non-up-2026-09-17/presentations_q3.json
  - experiments/a2-non-up-2026-09-17/runs/control-q3-full-r11.jsonl
  - experiments/a2-non-up-2026-09-17/runs/control-q2-full-r11.jsonl
  - experiments/a2-non-up-2026-09-17/runs/q3-gamma0-r22.jsonl
  - experiments/a2-non-up-2026-09-17/runs/q2-gamma0-r33.jsonl
---

**ESTABLISHED (exact computation)** by `a2-type-kernels-no-unique-product-census-proof`.

**Setup.**
- `(λ, T)` is a triangle presentation over the projective plane of order `q` (Cartwright–
  Mantero–Steger–Zappa).
- `Γ_T = ⟨a_x | a_x a_y a_z = 1, (x,y,z) ∈ T⟩` acts simply transitively on the vertices
  of a thick Ã2 building.
- `Γ_0 = ker(Γ_T → Z/3, a_x ↦ 1)` is the type kernel.
- `|g|` is word length in `{a_x^{±1}}` and `B(r)` is the ball of `Γ_T`.
- For finite nonempty `A ⊆ Γ_0`:
  `rad_L(A) = min_{a_0∈A} max_{a∈A} |a_0^{-1}a|` and
  `rad_R(A) = min_{a_0∈A} max_{a∈A} |a a_0^{-1}|`.
- A pair `(A, B)` is *without unique products* if every `g ∈ AB` has at least two
  expressions `g = ab`.

**Statement.** Take `T` from `presentations_q3.json` (133 entries) or
`presentations_q2_all.json` (11 entries). Then `Γ_0` has no pair `(A, B)` without unique
products such that
1. `q = 3` and `rad_L(A) ≤ 2`, `rad_R(B) ≤ 2`; or
2. `q = 2` and `rad_L(A) ≤ 3`, `rad_R(B) ≤ 3`.

**Consequence, over every field.** If `k` is any field and `α, β ∈ k[Γ_0]` are nonzero with
`αβ = 0`, then `rad_L(supp α) ≥ 3` or `rad_R(supp β) ≥ 3` when `q = 3`, and
`rad_L(supp α) ≥ 4` or `rad_R(supp β) ≥ 4` when `q = 2`.

**Scope of the lists.**
- The lists are all `PGL(3,q)`-orbits of triangle presentations: 133 for `q = 3`, 11 for
  `q = 2`. Under reversal `T ↦ {(z,y,x)}`, which induces `Γ_T ≅ Γ_{T^rev}`, they merge into
  89 and 8 classes, the counts of CMSZ II. Completeness was certified by lane sw-108; see the
  proof, Step 5.
- By Herron (arXiv:2502.09536), the 89 `q = 3` classes are 65 exotic, 16 in
  `PGL(3,F_3((t)))` and 8 in `PGL(3,Q_3)`. The 8 `q = 2` classes are all linear (4 in
  `PGL(3,F_2((t)))`, 4 in `PGL(3,Q_2)`).
- `Γ_0` is torsion-free: a finite subgroup fixes a point of the CAT(0) building, preserves
  the simplex containing it, fixes its vertices because it preserves types, and so is
  trivial by simple transitivity.

**Host status of `Γ_0`, the reason for the census.**
- **Every class:** torsion-free and infinite, with property (T) (Cartwright–Młotkowski–
  Steger, Ann. Inst. Fourier 44 (1994)). So it is not elementary amenable, not a-T-menable
  and hence not in Linnell's class C, not locally indicable (finite abelianization), and not
  a subgroup of a torsion-free virtually compact special group
  (`kazhdan-groups-without-unique-products-are-zero-divisor-hosts`, items 1–4, whose proofs
  do not use the missing unique products).
- **Compact 3-manifold groups:** `Γ_0` is not a subgroup of one. It is finitely generated,
  so by Scott's core theorem it would be a compact 3-manifold group itself, and infinite
  3-manifold groups do not have (T) (Fujiwara, Proc. Japan Acad. 75 (1999)).
- **Left orders:** `Γ_0` is not left-orderable, so the route "left-orderable ⇒ unique
  products" is closed. This is the node a2-triangle-type-kernels-q2-q3-act-trivially-on-the-line of lane sw-108,
  which was staged for landing and was not yet on main when this was written.
- **The 65 exotic classes:** by Bader–Caprace–Lécureux (arXiv:1608.06265, Theorem
  `nonlinear`, quoted in `exotic-a2-lattices-satisfy-boone-higman`), every homomorphism
  `Γ_0 → GL_n(R)`, over any commutative unital ring `R`, has finite image. So `Γ_0` lies in
  no `p`-adic congruence kernel `CS(u,d,p) ⊆ GL_d(Z_p)`, and the Farkas–Linnell case does not
  apply in any characteristic.
- **Summary for the exotic `q = 3` classes:** they avoid every known case listed in
  `kaplansky-zero-divisor-conjecture`, over every field, except Strong Atiyah in
  characteristic 0. No source read here decides Strong Atiyah for them.
- **Summary for the linear classes:** they avoid the same list except that a finite-index
  subgroup may sit in a congruence kernel. That does not settle `k[Γ_0]` itself.

Whether any vertex-regular Ã2 lattice has unique products is not recorded in this graph, and
a web search found no source. The hosts on main that provably lack unique products, the
Arzhantseva–Steenbock Kazhdan groups, have no normal form, so no census can run on them. The
type kernels are explicit non-linear torsion-free Kazhdan hosts with exact multiplication,
and this is the first census on them.

**Runs** (CaDiCaL 1.5.3 via python-sat, single thread, `nice -n 10`, machine load about 30
on 4 cores; `python3 summarize.py`):

| host, radii | presentations | results | candidates for A, B | pairs | vars | clauses | solve s |
|---|---|---|---|---|---|---|---|
| control: full `Γ_T`, `q = 3`, orbit 0, `(1,1)` | 1 | SAT, verified (`A = {1, a_11, a_11^{-1}}`) | 27, 27 | 729 | 603 | 2375 | 0.0 |
| control: full `Γ_T`, `q = 2`, orbit 2, `(1,1)` | 1 | SAT, verified | 15, 15 | 225 | 229 | 821 | 0.0 |
| `Γ_0`, `q = 3`, `(2,2)` | all 133 | UNSAT x133 | 157, 157 | 24649 | 19505 | 81753 | 2.2–6.1 |
| `Γ_0`, `q = 2`, `(3,3)` | all 11 | UNSAT x11 | 267, 267 | 71289 | 96129 | 355259 | 94–260 |

Every product cell has the same statistics for every presentation at these radii:
- `q = 3`, `(2,2)`: 14899 cells, 12636 singleton cells;
- `q = 2`, `(3,3)`: 31403 cells, 14336 singleton cells.

**What the negative results rule out.** For every listed `T`, over every field, a zero
divisor on `Γ_0` needs a support pair of radii beyond those above. Inversion
`(A,B) ↦ (B^{-1}, A^{-1})` keeps both statements symmetric in the two radii. Nothing is claimed about larger radii, other finite-index
subgroups, non-vertex-regular Ã2 lattices, or `q ≥ 4`.

**Next instances.**
- `q = 3`, `(2,3)` (equivalently `(3,2)`): `157 × 2263` pairs, about 209k variables and
  968k clauses, about 8 minutes per presentation under load. It is running over one
  representative of each of the 89 reversal classes, into `runs/q3-gamma0-r23.jsonl` (not an
  artifact yet).
- `q = 2`, `(3,4)`: `267 × 939` pairs.
- `q = 2`, full `Γ_T` at `(3,3)` for the torsion-free orbits 0, 1, 3, 5, 9: `673 × 673`
  pairs.
