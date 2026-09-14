# Thompson's F: the metabelian barrier for the defect-to-separation ratio, and skew products (2026-09-14)

**Verdict: not decided.**
- `ρ_F = 0`, i.e. soficity of `F`, stays OPEN.
- **Sharp barrier (landed).** On pairs generating a metabelian group,
  `d(AB,BA) ≤ 2 d(R_1,1) + d(R_2,1)`, so the ratio `D/t` is at least `1/3` there, and the bound is
  attained. The exact small-`n` minima on main are exactly this barrier, attained by metabelian groups.
- **Extensions (landed).** Linear bounds exist for every bounded derived length and every law that
  `F` escapes. Skew products with abelian or bounded-solvable fibres over solvable bases are covered.
  With unrestricted fibres, skew products over commuting bases already contain every pair, so no barrier
  uniform over them exists short of proving `F` nonsofic.
- **Searches.** Nonabelian-fibre skew-product searches are recorded in §5 as evidence only.

Claims:
- `thompson-f-metabelian-pairs-obey-sharp-linear-commutator-bound`, route
  `thompson-f-metabelian-commutator-bound-proof`;
- `thompson-f-bounded-derived-length-pairs-obey-linear-bounds`, route
  `thompson-f-verbal-commutator-bounds-proof`.

Conventions as in `research/artifacts/hl-f-sofic-relator-instability-2026-09-14.md`:
- `R_1 = bAABaaBAba`, `R_2 = bAAABaaaBAAbaa`, `c = abAB`;
- words act last letter first, and capitals are inverses;
- `m_1, m_2, m_c` count points moved by `R_1, R_2, c`.

Scripts, certificates and logs: `research/artifacts/hl-f-skew-product-rate-2026-09-14-search/`.

## 1. Where this sits

`thompson-f-sofic-iff-defect-to-separation-ratio-vanishes` reduced soficity of `F` to `ρ_F = 0`. That
lane's exact enumeration gave minima `1/3` (max form, `n = 12`) and `1/2` (sum form, `n ≥ 10`), and
annealing found one pair on 16 points with ratio `4/13`. Its closure theorem left skew products and graph
surgery as the only mixing constructions not covered. This lane asked what the skew products can do.

## 2. The identity modulo the second derived subgroup

**Fox winding functions** (`fox.py`, exact integer Laurent polynomials; `W(w) = (∂w/∂a)/(t-1)`):
- `W(R_1) = -s^-2 + s^-1 t^-1 - s^-1`;
- `W(R_2) = -s^-3 + s^-2 t^-1 - s^-2 + s^-1 t^-1 - s^-1`;
- `W(c) = -1`.

**Bézout.** Put `u = s^-1` and `v = t^-1`. Then:
- `W(R_1) = -u f` with `f = 1 + u - v`;
- `W(R_2) = -u g` with `g = (1+u) f - u`;
- so `(s^2 + s) W(R_1) - s^2 W(R_2) = -1 = W(c)`.

That is `c ≡ (a^2 R_1 a^-2)(a R_1 a^-1)(a^2 R_2 a^-2)^-1` modulo `F_2''`.

**Explicit word.** The defect of this congruence is the explicit 34-letter word

`u_2 = abABaabAAABaaaBAbAAbaaBBabAAbaaBAA`,

with `c = u_2 · (a^2 R_1 a^-2)(a R_1 a^-1)(a^2 R_2 a^-2)^-1`.

**Checks.**
- **Fox derivatives.** Both Fox derivatives of `u_2` are `0` exactly (`u2_check.py`). By the grid
  criterion in the route, `u_2 ∈ F_2''`.
- **Magnus representation.** In the faithful Magnus representation of `F_2/F_2''` (`metab_check.py`),
  `c` and `(a^2R_1a^-2)(aR_1a^-1)(a^2R_2a^-2)^-1` have equal images.
- **Minimality.** No identity with fewer than three relator conjugates exists modulo `F_2''`; the
  argument is in the route, item 4.

## 3. The metabelian bound and its sharpness

**Violation search** (`metab_check.py`, `wreath_check.py`). Every one of 915,459 metabelian pairs with
`t > 0` satisfies `m_c ≤ 2 m_1 + m_2`, with no violation. The pairs:
- **Affine maps.** All pairs `x ↦ α x + β` on `Z/p` for `p ∈ {3,…,23}`, plus 1,200 random
  lamplighter-type pairs in `(Z/k)^m ⋊ Z/m`; together 460,170 pairs with `t > 0`.
- **Wreath products.** All pairs in `Z/k wr Z/m` acting imprimitively for small `(k, m)`, or random
  pairs where the group is large.
- **Torus skew products.** Random abelian-fibre skew products over `Z/N × Z/N`, `N ≤ 4`, fibres
  `Z/2`, `Z/3`.
- **Subtotal.** The wreath and torus families together give 455,289 pairs.

**Equality certificates.** Recounted by `u2_check.py` and by `analyze.py` from
`hl-f-sofic-relator-instability`.

| certificate | n | m_1 | m_2 | m_c | u_2 moves | group (GAP 4.13.1) |
|---|---|---|---|---|---|---|
| `cert.x12` | 12 | 3 | 3 | 9 | 0 | `(C3 x C3 x C3 x C3) : C8`, order 648 |
| `cert.s10` | 10 | 4 | 0 | 8 | 0 | `(C2 x C2 x C2 x C2) : C5`, order 80 |
| `cert.torus3xZ2.txt` | 18 | 4 | 4 | 12 | 0 | `Z/2`-fibre skew product over `Z/3 x Z/3` |
| `cert.Z2wrZ5.txt` | 10 | 4 | 0 | 8 | 0 | inside `Z/2 wr Z/5` |
| `cert.x16` (for contrast) | 16 | 4 | 4 | 13 | 11 | `((((C3^3) : (C2 x C2)) : C3) : C2) x A5`, order 38880, nonsolvable |

- **The torus certificate.** It is exhaustive over its family (`metab_certs.py`, all `2^18` cocycle
  pairs): minimum max ratio `4/12`. Its cocycles are
  - `c = [1,0,0,0,0,0,0,0,0]`,
  - `d = [0,1,1,0,0,1,0,0,0]`,
  - indexed by `3x + y`, acting by `(x,y,i) ↦ (x+1, y, i + c)` and `(x,y,i) ↦ (x, y+1, i + d)`.
- **The wreath certificate.** It is exhaustive over `Z/2 wr Z/5`: minimum sum ratio `4/8`.
- **The other landed certificates.** `cert.10` (`A4 x A5`) and `cert.12` (`(A6 x A6) : C4`) are
  nonsolvable too (`certgroups.log`).

**Reading.**
- The exact small-`n` minima over all of `Sym(n)` are metabelian and equal the metabelian bound.
- The one pair below `1/3` is nonsolvable, with an `A5` factor, and there `u_2` does the work.
- The ratio `1/3` is the metabelian wall, not a small-`n` accident.

## 4. Laws, derived length, skew products

**Laws.** `F'' = F'`, since the image of `u_2` in `F` is the commutator `[x_0, x_1] ≠ 1` and the import
applies. Hence `F^(ℓ) = F'` for all `ℓ`, and for every law `v` with `V(F) ≠ 1` the commutator is a
product of relator conjugates times a value of `v`. So:
- pairs of derived length `≤ ℓ` satisfy `t ≤ N_ℓ D`;
- pairs of exponent dividing `e` satisfy `t ≤ N_(e) D`;
- `N_ℓ` for `ℓ ≥ 3` is not computed.

**Skew products.** `A(p,i) = (A_0 p, c(p) i)`, `B(p,i) = (B_0 p, d(p) i)`.
- **Transformation law.** For every word `w`,
  `m_w(A,B) = k · m_w(A_0,B_0) + Σ_(p ∈ Fix w(A_0,B_0)) moved(κ_w(p))`, where `κ_w(p) ∈ K` is the
  holonomy of `w` around its closed path at `p`. So a skew product adds holonomy terms over the fixed
  points of the base.
- **Derived length.** It is at most `dl(base) + dl(K)`, where `K` is generated by the cocycle values.
- **Firewall.** Constant cocycles over the commuting torus are coordinatewise products with the torus
  pair, and they reproduce every pair on `k` points with unchanged `D` and `t`. So skew products over
  commuting bases with unrestricted fibres are complete, and any barrier uniform over them is nonsoficity
  of `F`.
- **What stays open.** The only structural lever inside skew products is the fibre group, which must
  be nonsolvable, or solvable of growing derived length.

## 5. Nonabelian-fibre skew-product search (job 793408, evidence only)

**Method.** `skew_anneal.c`: Metropolis on `log(max(m_1,m_2)/m_c)`, with a penalty keeping
`m_c ≥ frac · n`.
- **Moves.** Compose one cocycle value `c(p)` or `d(p)` with a fibre transposition (`sym` mode), or
  add a rotation (`cyc` mode, abelian fibre).
- **Bases.**
  - commuting torus `Z/N × Z/N` for `N ∈ {2,3,4,5}` with `k ∈ {3,4,5}` (`sym`);
  - the landed pairs `cert.x16` and `cert.x12` with `k ∈ {2,3}` (`sym`);
  - calibration runs in `cyc` mode on tori.
- **Scale.** `2·10^6` steps per run (`10^6` for calibration), 3 seeds on tori and 2 on file bases,
  `frac ∈ {0.1, 0.3}`.

**Calibration.**
- **Constant cocycles.** The torus with identity cocycles gives `m = 0`. The base `cert.x16` with
  `k = 1` reproduces `(4, 4, 13)`, and with `k = 3` gives `(12, 12, 39)`.
- **`cyc` mode.** On the torus with `N = 3`, `k = 2` it finds `4/12`, matching the exhaustive metabelian
  minimum, and by §3 it can never go below `1/3`.

**Results (job 793408, all 94 runs; full table in `skew-793408-results.txt`).** Best max ratio per
configuration (all seeds and `frac` values):

| base | fibre `k` | best `max(m_1,m_2)/m_c` | n |
|---|---|---|---|
| torus `N = 2` | 3 / 4 / 5 | `4/10` / `4/12` / `4/12` | 12 / 16 / 20 |
| torus `N = 3` | 3 | **`4/21 ≈ 0.1905`** (all 6 runs) | 27 |
| torus `N = 3` | 4 / 5 | `9/33 = 3/11 ≈ 0.2727` / `16/45 ≈ 0.356` | 36 / 45 |
| torus `N = 4` | 3 / 4 / 5 | `11/38 ≈ 0.289` / `17/55 ≈ 0.309` / `27/73 ≈ 0.370` | 48 / 64 / 80 |
| torus `N = 5` | 3 / 4 / 5 | `19/63 ≈ 0.302` / `33/93 ≈ 0.355` / `44/114 ≈ 0.386` | 75 / 100 / 125 |
| `cert.x16` | 2 / 3 | `8/26` / `12/39` (= `4/13`, no gain) | 32 / 48 |
| `cert.x12` | 2 / 3 | `1/3` (no gain) | 24 / 36 |
| torus, `cyc` (abelian fibre) | 2–4 | `≥ 1/3`, as forced by §3 | ≤ 64 |

**New certificates** (recounted by `analyze.py` on MSI and independently by a local script):
- **`cert.torus3xS3-4over21.txt`.** `n = 27`, `m_1 = m_2 = 4`, `m_c = 21`, `u_2` moves 24 points. So
  `ρ_F ≤ 4/21`, and every nonsoficity constant in the max form is at least `21/4 = 5.25`, improving
  `13/4`.
  - The pair is a skew product with fibre `Sym(3)` over the commuting `Z/3 × Z/3`, so by §4 its derived
    length is at most 3. GAP job 794552 (`skewgroups.log`) gives a solvable group of order 22,674,816
    and derived length exactly 3, structure `((C3^9 : C2^7) : C3) : C3`.
  - The `3/11` pair on 36 points is also solvable of derived length exactly 3, order 191,102,976.
  - Consequence: the linear constant for derived length three satisfies `N_3 ≥ 21/4`, strictly above
    the metabelian `N_2 = 3`.
- **`cert.torus3xS4-3over11.txt`.** `n = 36`, `m_1 = m_2 = 9`, `m_c = 33`, `u_2` moves 24 points.

**Reading.**
- **Nonabelian fibres help.** Nonabelian fibres over a commuting base beat both the metabelian wall
  and the previous best nonsolvable pair, and they do so reproducibly.
- **No growing mechanism yet.** The anneal did worse on larger tori and larger fibres, which may be
  search failure. By the closure theorem, unions and products of the `4/21` block stay at `4/21`.
- **Iterated skew products and larger tori (job 794431, 28 runs, `iter-794431-results.txt`): no gain.**
  - **Over the `4/21` pair, fibre `k = 2`.** Best `8/42 = 4/21`, only recovering the constant-cocycle
    doubling; the other seeds give `12/54`.
  - **Over the `4/21` pair, fibre `k = 3`.** Best `25/81 ≈ 0.309`.
  - **Over the `3/11` pair.** `k = 2` gives `18/66 = 3/11` again, and `k = 3` gives `≈ 0.39`.
  - **Tori with `Sym(3)` fibres.** `N = 6` gives `23/86 ≈ 0.267`, and `N = 9` gives `58/205 ≈ 0.283`.

  So growing derived length by iterating skew products did not lower the ratio in this search. That is
  search evidence only, and it decides nothing.

## 6. Exact gap

1. **Decide `ρ_F = 0`.** Equivalently, prove or refute `d(AB,BA) ≤ C · D` for all pairs, with
   `C ≥ 13/4` forced.
2. **Non-metabelian witnesses.**
   - A witness family must have nonsolvable groups or unbounded derived length, and must escape every
     law `F` escapes. The ratio must first go below `1/3`, which forces non-metabelian groups (§3).
   - Explicit constants `N_3`, and a growth rate for `N_ℓ`, would say how fast derived length must
     grow. Computing them needs the module `F_2''/F_2'''` over `Z[F_2/F_2'']`, a noncommutative group
     ring, and was not done.
3. **Skew products.** Only nonabelian-fibre skew products over non-trivially structured bases remain
   interesting.
   - **Flatness.** The fibre holonomy must be flat around the relator loops at most base points while
     curved around the commutator loop at a positive fraction.
   - **Exact case.** Over an exact `F`-set, flat connections are exactly permutation representations of
     the point stabilizers, which are finite-index subgroups containing `F'`. There the commutator's
     holonomy is trivial in every finite model, because `F'` is simple.
   - **Approximate case.** The approximate version of this is open.
4. **Graph surgery** (gluing blocks along shared points) was not studied.
