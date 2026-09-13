# UN review, part 4 (lane un-verify-3, 2026-09-13)

Scope: the paradoxical families landed by `un-boundary-families` (0e439a2b56, 57c027734f, 4179e57149) and un-architect's
middle-rung wiring (88fc580eb0). Method as in parts 1–3.

**Summary.** 8 PASS, 0 GAP, 0 FAIL.
- The two open claims `hyperbolic-group-cantor-model-simple-kazhdan-not-mf` and
  `boundary-kazhdan-families-pairwise-non-isomorphic` have no incoming route, so they stay OPEN.
- Not load-bearing, and not re-read here: the imports `kp-algebra-steinberg-simple-iff-aperiodic-cofinal` and
  `grigorchuk-steinberg-algebra-not-simple-over-f2`. The first is recalled only, and the second is a firewall.

| § | Node | Verdict |
|---|---|---|
| 1 | `paradoxical-cantor-actions-give-simple-kazhdan-not-mf` | PASS |
| 2 | `north-south-minimal-cantor-action-is-paradoxical` | PASS |
| 3 | `paradoxical-steinberg-elementary-simple-kazhdan-not-mf` | PASS |
| 4 | `free-product-finite-groups-boundary-simple-kazhdan-not-mf` | PASS |
| 5 | `p-adic-projective-line-elementary-simple-kazhdan-not-mf` | PASS |
| 6 | `product-two-graph-kp-elementary-simple-kazhdan-not-mf` | PASS |
| 7 | `odometer-nekrashevych-elementary-simple-kazhdan-not-mf` | PASS (Exel–Pardo quote-checked) |
| 8 | `rank-modelled-simple-algebra-with-non-lef-kazhdan-el-group` (middle rung) | PASS (wiring) |

## §1 Paradoxical Cantor actions: PASS

- **Lemma F.** The clopens `U` with `χ_U ∈ R_0` form a Boolean algebra (products, complements `1 − χ_U`, unions by
  inclusion–exclusion). It contains `χ_(gP) = u_g χ_P u_g^(-1)`. A point-separating family of clopens in a compact
  totally disconnected space generates the clopen algebra, so `R_0 ⊇ LC(X,F_q)`, and with the `u_s` we get `R_0 = R`.
- **Effective.** An open set inside the isotropy meets `{g} × X` inside `{g} × Fix(g)`, and topological freeness
  empties it for `g ≠ e`.
- **Full defect.**
  - `χ_(A_i) u_(g_i^(-1)) = u_(g_i^(-1)) χ_(g_iA_i)`, so `ts = Σ_(i,i') u_(g_i^(-1)) χ_(g_iA_i) χ_(g_(i')A_(i')) u_(g_(i'))`.
    The images are disjoint, so this is `Σ_i χ_(A_i) = 1`.
  - `st = Σ_i χ_(g_iA_i) = χ_E`.
  - `χ_(B_j) u_(h_j)^(-1) χ_(X\E) u_(h_j) χ_(B_j) = χ_(B_j ∩ h_j^(-1)(X\E)) = χ_(B_j)`, and these sum to `1`.
- **Conclusion.** `full-defect-ring-non-mf-at-rank-two` (established) and the reviewed simplicity theorem.
- **Model test.** A minimal ℤ-subshift has an invariant measure, which is incompatible with (H-par).

## §2 North–south elements give an elementary paradox: PASS

- **Poles are the only fixed points.** `g^nξ^+ → ξ^+` together with continuity gives `gξ^+ = ξ^+`. A fixed `x ≠ ξ^-`
  lies in every neighbourhood of `ξ^+`. So `Fix(g) = {ξ^+, ξ^-}`.
- **A conjugate with new poles.** Minimal and infinite means infinite orbits, so point stabilizers have infinite index.
  The `c` sending a pole into `{ξ^±}` lie in at most four cosets, and B. H. Neumann's lemma gives some `c` outside
  them. Then `h = cgc^(-1)` is north–south with poles `cξ^±`, distinct from `ξ^±`.
- **Compression.** `A_1 = X\C` avoids `ξ^-` and `A_2 = C` avoids `η^-`; `B_1 = X\D` avoids `ξ^+` and `B_2 = D` avoids
  `η^+`. Powers `g^n, h^n, g^(-n), h^(-n)` push them into four disjoint neighbourhoods.

## §3 Interface theorem: PASS

- The reviewed simplicity theorem plus the rank-two full-defect theorem.
- The Leavitt copy gives `t_2(1 − s_1t_1)s_2 = 1`.

## §4 A*B on the ends of its Bass–Serre tree: PASS

- **Cantor.** After an `A`-letter there are `|B| − 1 ≥ 2` choices, so every cylinder branches infinitely often.
- **(H-gen).** `C(x_1…x_m) = (x_1…x_(m-1))·C(x_m)`, with no cancellation between different factors.
- **Minimal.** Insert letters so that `wyω` is reduced.
- **Topologically free.** Take a tail `ω''` that is not eventually periodic. If `γ` fixed `C(w')` pointwise with
  `|w'| ≥ k+2`, then `(γw')ω'' = w'ω''`; a length difference would make `ω''` eventually periodic. So `γw' = w'` and
  `γ = 1`.
- **North–south.** `ab` with poles `(ab)^∞` and `(b^(-1)a^(-1))^∞`.
- `D_∞` (`|A| = |B| = 2`) is correctly excluded.

## §5 PSL_2(ℤ[1/p]) on P^1(Q_p): PASS

- **Unipotents.** `d_p^k e_12(1) d_p^(-k) = e_12(p^(2k))`, so `e_12(ℤ[1/p]) ⊆ Γ_p`.
- **Minimal.** Density of `ℤ[1/p]` in `Q_p` makes the closure contain `SL_2(Q_p)`, which is transitive.
- **Topologically free.** A Möbius map fixing three points is trivial in `PGL_2`.
- **(H-gen).** The balls `a + p^mZ_p = e_12(b) d_p^k(p^εZ_p)`, with `m = 2k + ε`, separate points, and no ball contains `∞`.
- **North–south.** `z ↦ p²z` with poles `0` and `∞`.

## §6 L(1,m) ⊗ L(1,n): PASS

- **Cuntz groupoids.** Minimal. Effective: on `Z(α,β)` with `|α| ≠ |β|` the isotropy points solve `αz = βz`, one
  point; with `|α| = |β|` and `α ≠ β` there are none.
- **The product groupoid.** Minimal (orbits are products). Effective, since interiors of isotropy factor.
- **Tensor iso.** `A(𝒢_m) ⊗ A(𝒢_n) ≅ A(𝒢_m × 𝒢_n)`: convolution factorizes; surjective because compact opens are
  finite unions of products; injective because `Σ f_i(γ) g_i(η) = 0` with linearly independent `f_i` forces
  `g_i(η) = 0`.
- **Full defect.** `(t_2⊗1)(1 − s_1t_1⊗1)(s_2⊗1) = 1`.

## §7 Odometer Nekrashevych groupoid: PASS

- **Pseudo free.** `φ(a^(2k), x) = a^k`, so a trivial restriction forces `n = 0`.
- **Quote check.** arXiv:1409.1107 (plain-TeX source `ExelPardo3.tex`) matches the import
  `exel-pardo-pseudo-free-self-similar-groupoid-hausdorff` verbatim:
  - Definition `EssFree` (l.1342);
  - Proposition `EssFreePath` (l.1351);
  - Theorem `MainHausdorff` (l.3347);
  - Theorem `CharacMinimal` (l.3557);
  - Standing Hypothesis (l.700). The odometer's graph is finite (one vertex, two loops) with no sources, which
    satisfies it.
- **Hausdorff and minimal.** No `g ≠ 1` strongly fixes a nonzero-length path, so there are finitely many minimal
  strongly fixed paths, hence Hausdorff. One vertex means weakly `G`-transitive, hence minimal.
- **Effective.** A groupoid of germs is effective.
- **Finite generation and defect.** `paradoxical-steinberg-families-kazhdan-no-mf-quotient` (un-verify PASS) gives
  finite generation. The Leavitt generators give `t_1(1 − s_0t_0)s_1 = 1`.

## §8 Middle rung wiring (88fc580eb0): PASS

- **The firing route.** `rank-modelled-simple-algebra-with-non-lef-kazhdan-el-group` is established by
  `rank-modelled-non-lef-el-via-amenable-non-rf-subflow`. Every required node is either reviewed PASS
  (`amenable-minimal-crossed-products-have-faithful-rank-models`, `crossed-product-group-embeds-in-projective-elementary-group`,
  `finitely-presented-lef-groups-are-residually-finite`, `crossed-products-are-transformation-steinberg-algebras`,
  `steinberg-algebra-simple-iff-minimal-effective`) or an established import (GJS, Abels–Prüfer calibration, EJZ).
- **The second route.** `non-lef-kazhdan-el-group-from-fp-rank-modelled-simple-algebra` requires the OPEN
  `fp-simple-algebra-over-finite-field-with-rank-model`, so it cannot fire.
- **Root.** `kazhdan-elementary-approximation-type-mirrors-ring-type` is still OPEN: its ladder route requires the open
  (Σ⇒) and (M⇐) converses.
