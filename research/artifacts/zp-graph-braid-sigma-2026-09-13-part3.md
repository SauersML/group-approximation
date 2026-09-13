# BNSR invariants of graph braid groups, part 3: complete answer for trees with n ≤ 3 and for radial trees

Lane z1-08-graph-braid, 2026-09-13. Notation as in parts 1–2. All sources
below were read from arXiv PDFs, with text extracted on MSI.

## 1. Verbatim inputs

**(FS-free)** Farley–Sabalka, *On the cohomology rings of tree braid groups*,
arXiv:math/0602444 (J. Pure Appl. Algebra 212 (2007)), proof of Theorem 5.11:
"If n < 4 and T is a tree, then Theorem 4.3 of [10] shows that BnT is in fact
a free group, since UDnT strong deformation retracts on a graph."
[10] = Farley–Sabalka, *Discrete Morse theory and graph braid groups*,
arXiv:math/0410539, AGT 5 (2005). Its Theorem 4.3: for a tree `Γ` and a
critical cell `c` of `UD_nΓ`, `dim c ≤ k := min{⌊n/2⌋, #{essential
vertices}}`, and "In particular, UDnΓ strong deformation retracts on
(UDnΓ)'_k."

**(FS-radial)** arXiv:math/0410539, Corollary 4.2 (credited there to Ghrist):
"If Γ is a radial tree – i.e. has exactly one essential vertex, v – then BnΓ
is free of rank Σ_{i=2}^{d(v)−1} [ C(n+d(v)−2, n−1) − C(n+d(v)−i−1, n−1) ]."

**(Gal)** Ś. R. Gal, *Euler characteristic of the configuration space of a
complex*, arXiv:math/0202143 (Colloq. Math. 89 (2001)):

- Definition: `eu_X(t) := Σ χ(C_n(X)) t^n/n!`, where `C_n` is the ordered
  configuration space;
- Theorem 2: `eu_X(t) = Π_σ (1 + (−1)^{d_σ}(1 − v_σ)t)^{(−1)^{d_σ}}`, where
  `d_σ` is the dimension of `σ` and `v_σ` the Euler characteristic of its
  normal link.

For a graph, a vertex `v` has a normal link of `deg v` points and gives the
factor `1 + (1 − deg v)t`. An edge has an empty normal link and gives
`(1 − t)^{−1}`. Since `S_n` acts freely on `C_n`,
`χ(UConf_nΓ) = χ(C_nΓ)/n!`, so
`Σ_n χ(UConf_nΓ) t^n = Π_v (1 + (1 − deg v)t) · (1 − t)^{−|E|}`.
This confirms the formula quoted in part 1.

## 2. Two-strand tree braid groups: rank formula

Let `T` be a finite tree, `V` vertices, `E = V − 1` edges, `a_v = 1 − deg v`.
Then `Σ_v a_v = V − 2E = 2 − V`, and

`e(UConf_2T) = [t²] Π_v(1 + a_v t)(1 − t)^{−(V−1)}`
`= C(V,2) + (2 − V)(V − 1) + ((2 − V)² − Σ a_v²)/2`
`= (V − Σ_v (deg v − 1)²)/2`.

Write `L` for the number of leaves, `V_2` for the number of degree-2
vertices and `k` for the number of essential vertices. Then
`V = L + V_2 + k`, `Σ_v (deg v − 1)² = V_2 + Σ_{ess} (d_v − 1)²`, and
`L = 2 + Σ_{ess}(d_v − 2)`. Hence

`e(UConf_2T) = 1 − Σ_{v essential} C(d_v − 1, 2)`.

`B_2T` is free by (FS-free), and `UConf_2T` is homotopy equivalent to a
graph. So its rank is

**`rank B_2T = Σ_v C(deg v − 1, 2)`.**

Checks against (FS-radial): for `d = 3`, rank 1; for `d = 4`, rank 3.

## 3. Theorem T (complete BNSR invariants)

Recall `S(F_r)` is empty for `r = 0` and `S⁰` for `r = 1`,
`Σ^m(ℤ) = S⁰` for all `m`, and `Σ¹(F_r) = ∅` for `r ≥ 2` (kernels of
nonzero characters are nontrivial normal subgroups of infinite index, which
are never finitely generated in a free group of rank `≥ 2`). Let `T` be a
finite tree and `n ≥ 1`.

1. **`n = 2`.** `B_2T` is free of rank `Σ_v C(deg v − 1, 2)`. So:
   - if `T` has exactly one essential vertex and it has degree 3 (a
     subdivided triod), then `B_2T ≅ ℤ` and `Σ^m(B_2T) = S⁰` for all `m`;
   - if `T` is an arc, `B_2T = 1`;
   - otherwise `Σ^m(B_2T) = ∅` for all `m`.
2. **`n = 3`.** If `T` is an arc, `B_3T = 1`. Otherwise `B_3T` is free of
   rank `≥ 3`, so `Σ^m(B_3T) = ∅` for all `m`.
3. **Radial `T`** (one essential vertex, of degree `d ≥ 3`), all `n ≥ 2`:
   `B_nT` is free of rank `r(n,d) = 1 − C(n+d−1, d−1) + (d−1)C(n+d−2, d−1)`.
   Then `r = 1` iff `(d, n) = (3, 2)`. So `Σ^m(B_nT) = S⁰` iff `(d,n) = (3,2)`,
   and `Σ^m(B_nT) = ∅` otherwise.
4. `n = 1`: `B_1T = 1`, and there are no characters.

**Proof of 2.** `B_3T` is free by (FS-free). A tree with an essential vertex
contains a subdivided triod `Y`, and `UD_3Y ⊆ UD_3T` is a full subcomplex:
a set of moves inside `Y` spans a cube of `UD_3T` iff its edges have
pairwise disjoint closures, the same condition as in `UD_3Y`. Full
subcomplexes whose links are full subcomplexes of the ambient links are
locally convex in a nonpositively curved cube complex, hence
`π_1`-injective. So `B_3Y ↪ B_3T`, and `B_3Y` is free of rank 3 by
(FS-radial) with `d = 3`, `n = 3`: `C(4,2) − C(3,2) = 3`. A free group
containing `F_3` is not `ℤ` or trivial, so its rank is `≥ 2`. (Rank `≥ 3`
also follows from the Euler characteristic count; only `≥ 2` is needed.)

**Proof of 3.** From Gal: the center gives `1 + (1−d)t`, degree-2 vertices
give `(1 − t)` each, leaves give 1, and the edges give `(1 − t)^{−(d+V_2)}`.
So `Σ_n e_n t^n = (1 + (1−d)t)(1 − t)^{−d}`, and
`e_n = C(n+d−1, d−1) − (d−1)C(n+d−2, d−1)`
`= C(n+d−2, d−1) · (d − 1 − n(d − 2))/n`.
For `n ≥ 2`, `d ≥ 3` this is zero iff `n(d−2) = d−1`, i.e. `(d,n) = (3,2)`,
and negative otherwise. So `r = 1 − e_n` is 1 exactly at `(3,2)` and
otherwise `≥ 2`. It agrees with (FS-radial) at `d = 3, 4` and `n = 2, 3`.

**Proof of 1.** Rank formula, §2. Rank 1 iff `Σ_v C(deg v − 1, 2) = 1` iff
exactly one vertex has degree 3 and none has degree `≥ 4`. Rank 0 iff all
degrees are `≤ 2`, i.e. `T` is an arc. ∎

## 4. Remarks

- These are the first complete families. They agree with Theorem E (part 1):
  `e ≠ 0` in every empty case, and `e = 0` exactly when `B_nT ≅ ℤ`.
- For `n ≥ 4` and nonlinear trees `B_nT` is not a RAAG (FS Theorem 5.11).
  For linear trees Connolly–Doig show `B_nT` is a RAAG. Once the defining
  graph is explicit, Meier–Meinert–VanWyk give the complete answer there.
  That is the next family.
