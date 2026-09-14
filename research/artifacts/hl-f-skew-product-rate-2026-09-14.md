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

**Results.** RUNNING at landing time; the table is appended when job 793408 finishes. The partial
outputs seen at 11:1x were all above `1/3`, the best being `33/93 ≈ 0.355` on a 100-point torus product
with fibre `Sym(4)`.

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
