---
rg: 2
id: cone-compactifications-over-z-are-rigid-proof
kind: route
title: Put a C_Z height on Λ_0 × Z, constant along Λ_0, and a copy of Y_0 on the seed slice only; the height is a commutative chain, slices are orthogonal, and one slice is a quantum family for Y_0
target: products-with-z-have-rigid-compactifications-with-fixed-points
requires: []
---

Lane proof by bh-break, 2026-09-18. Not reviewed. Notation as in the target. Quantum families (Q1–Q3)
are as in `fp-v-times-subshift-full-groups-force-quantum-rigidity`. The action is
`(g.x)(h) = x(g^(-1) h)`. Write points of `Γ` as `(g, n)`, `g ∈ Λ_0`, `n ∈ Z`. The *slice* `n` is
`Λ_0 × {n}`. With the generating set `S_0 ∪ {t^(±1)}`, the metric is
`d((g,n),(g',n')) = d_0(g,g') + |n − n'|`, so every slice is isometric to `Λ_0`.

## 1. The SFT

The alphabet is `A = ({+, −} × {β}) ∪ ({*} × A_0)`, where `A_0` is the alphabet of `Y_0` and `β` is a
blank. Write `x = (x^1, x^2)`. The rules are:
- (a) `x^1(qs) = x^1(q)` for `s ∈ S_0`, and `(x^1(q), x^1(qt))` is an allowed `C_Z` pair
  `(+,+), (+,*), (*,−), (−,−)`;
- (b) the alphabet itself: `x^2(q) ≠ β` iff `x^1(q) = *`;
- (c) on every slice `n` with `x^1 = *`, the map `g ↦ x^2(g, n)` avoids the forbidden patterns of `Y_0`.

All rules have radius `max(r_0, 1)`. The seed `π` is the pattern of `y_*` on `B_(R_0)`, where
`y_*(g, n) = (C_Z(n), [n = 0] · y^0_*(g))`, `C_Z(n)` is `+` for `n < 0`, `*` for `n = 0` and `−` for
`n > 0`, and `[n = 0] · c` means `c` on slice 0 and `β` elsewhere.

## 2. Points of Y

By (a), `x^1(g, n)` depends only on `n`, and `n ↦ x^1(·, n)` is a point of `C_Z`. There are three
cases.
- `x^1 = t^m.C_Z`, with `*` exactly on slice `m`. Then `x^2` is `β` off slice `m`, and on slice `m` it
  is an arbitrary point `z ∈ Y_0` by (c). Write this point `[m, z]`.
- `x^1 = +^Z`. Then `x^2 = β` everywhere. This is `y_+`.
- `x^1 = −^Z`. Then `x^2 = β` everywhere. This is `y_−`.

The action is `(h, m').[m, z] = [m + m', h.z]`, and `y_±` are fixed by all of `Γ`. This proves part 2.

## 3. (C1) and (C2)

- **(C1).** If `x|_(B_(R_0)) = π`, then `x^1(1, 0) = *`, so `x = [0, z]`, and `z` has the seed `π_0`
  at `1`. By (C1) for `Y_0`, `z = y^0_*`, so `x = y_* = [0, y^0_*]`. If `(h, m').y_* = y_*`, then
  `m' = 0` and `h.y^0_* = y^0_*`, so `h = 1`.
- **(C2).** The orbit of `y_*` is `{[m, h.y^0_*]}`. Its closure contains every `[m, z]`, because
  `Y_0` is the orbit closure of `y^0_*`. It contains `y_+` as the limit of `[m, y^0_*]` for
  `m → +∞`, and `y_−` as the limit for `m → −∞`. By Section 2 there are no other points.

## 4. Rigidity

Fix `D >= max(D_0, r_0, R_0, 1)` and a `D`-quantum family `E_c(q)` for `Y` on a `k`-space `W_0`.
- **Expansion (standard).** Letters within distance `2D` commute by Q2. So a product of letters over a
  pattern on a subset of a `D`-ball that no point of `Y` extends expands, by inserting
  `Σ_b E_b(u) = 1` at the missing sites, into products over non-occurring `D`-ball patterns. It is
  therefore `0` by Q3.
- **Letters.** Put `E^1_a(q) = Σ_(c : c^1 = a) E_c(q)` for `a ∈ {+, *, −}`, and
  `F_c(q) = E_((*, c))(q)` for `c ∈ A_0`. Then `E_((±, β))(q) = E^1_±(q)`, and
  `E^1_*(q) = Σ_(c ∈ A_0) F_c(q)`. So `F_c(q) ≤ E^1_*(q)`, meaning `F_c E^1_* = E^1_* F_c = F_c`.
  The letters are the `E^1_±(q)` and the `F_c(q)`.

**Step (i): the height is constant along `Λ_0`.** For `s ∈ S_0` and `a ≠ b`, (a) and expansion give
`E^1_a(q) E^1_b(qs) = 0`. Hence `E^1_a(q) = E^1_a(q) E^1_a(qs)`, and symmetrically
`E^1_a(qs) = E^1_a(qs) E^1_a(q)`. The two commute by Q2, so `E^1_a(q) = E^1_a(qs)`. By connectedness,
`E^1_a(g, n) =: E^1_a(n)` depends only on `n`.

**Step (ii): the height is a chain.** Put `M_n = E^1_−(n)`. Exactly as for `C_Z` in the tree-gluing node
(Basic members), the forbidden `t`-pairs give `M_n ≤ M_(n+1)` and
`M_(n+1) = M_n + E^1_*(n)`, so `E^1_*(n) = M_(n+1) − M_n` and `E^1_+(n) = 1 − M_(n+1)`. Transitivity
of `≤` for idempotents (`e ≤ f ≤ g` gives `eg = efg = ef = e` and `ge = gfe = fe = e`) makes
`(M_n)_(n ∈ Z)` a chain, which generates a commutative algebra `𝓜` containing every `E^1_a(n)`.

**Step (iii): fibre letters commute with the height.** Let `q` lie on slice `m`, and let `c ∈ A_0`.
- For `j <= m`, `M_j ≤ M_m`, so `E^1_*(m) M_j = M_j − M_j = 0 = M_j E^1_*(m)`. Hence
  `F_c(q) M_j = F_c(q) E^1_*(m) M_j = 0`, and likewise `M_j F_c(q) = 0`.
- For `j >= m + 1`, `E^1_*(m) ≤ M_(m+1) ≤ M_j`, so `F_c(q) M_j = F_c(q) = M_j F_c(q)`.

So every `F_c(q)` commutes with all of `𝓜`.

**Step (iv): different slices are orthogonal.** If `q` is on slice `m` and `q'` on slice `m' ≠ m`, then
`E^1_*(m) E^1_*(m') = 0 = E^1_*(m') E^1_*(m)`, being different differences of the chain. So
`F_c(q) F_(c')(q') = F_c(q) E^1_*(m) E^1_*(m') F_(c')(q') = 0`, and symmetrically. They commute.

**Step (v): one slice is a quantum family for `Y_0`.** Fix `m` and put `P = E^1_*(m)`. By (ii) and (iii),
`P` commutes with every letter, so `W_1 = P W_0` is invariant under every letter. For `g ∈ Λ_0` and
`c ∈ A_0` put `G_c(g) = F_c(g, m)|_(W_1)`.
- Q1: the `G_c(g)` are orthogonal idempotents with `Σ_c G_c(g) = P|_(W_1) = 1`.
- Q2: slice `m` is isometric to `Λ_0`, so `d_0(g, g') <= 2D` gives commutation.
- Q3: let `α` be a pattern on `B^0_D(p)` that does not occur in `Y_0`. The pattern `(*, α)` on
  `B^0_D(p) × {m} ⊆ B_D((p, m))` extends to no point of `Y`, since every point with `*` on slice `m`
  restricts on that slice to a point of `Y_0`. By expansion, `∏_f F_(α(f))(pf, m) = 0`, and so its
  restriction to `W_1` is `0`.

So `(G_c(g))` is a `D`-quantum family for `Y_0` with `D >= D_0`, hence commutes. On `(1 − P) W_0` every
`F_c(g, m)` vanishes, since `F_c = F_c P`. So all fibre letters on slice `m` commute.

**Conclusion.** By (ii) the height letters commute among themselves. By (iii) they commute with the fibre
letters. By (iv) and (v) the fibre letters commute among themselves. So every letter commutes with every
other, and `Y` is `D`-quantum rigid over `k`. This proves part 1. `∎`

## 5. Remarks

- Nothing about `Λ_0` beyond finite generation and `(Y_0, π_0)` is used. The characteristic and the
  dimension of `W_0` are arbitrary.
- The hypothesis "`D_0`-rigid" is used at scale `D >= D_0`. This is legitimate because a `D`-quantum
  family is a `D_0`-quantum family (Q2 weakens, and Q3 at `D_0` follows from Q3 at `D` by expansion).
- `y_±` are the only non-free points that do not come from `∂Y_0`: `Stab([m, z]) = {1} × Stab(z)`.
