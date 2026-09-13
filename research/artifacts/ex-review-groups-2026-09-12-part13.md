# EX review, groups: part 13. fp-kazhdan-kac-moody and fp-kazhdan-titz-witzel refills

Lane `ex-verify-groups`, 2026-09-13, ~02:25 CDT. Index: `ex-review-groups-2026-09-12.md`.

These claims bound what certificates can reach the finitely presented simple Kazhdan candidates.
`km-246-lattice-is-sofic`, `titz-witzel-kernel-nonsofic`, `titz-witzel-residual-is-mf` and
`hyperlinear-fp-infinite-simple-kazhdan-group` are all OPEN.

## 13.1 `almost-actions-of-irs-rigid-simple-groups-are-free-or-trivial`. PASS

- **The random subgroup.** `μ_n` is the stabilizer law of the genuine `F(A)`-action on `[d_n]` under the
  uniform measure. It is conjugation invariant, and `μ_n(C_w)` is the proportion of points fixed by `w`.
- **The limit.** Take a weak-* limit `μ` along a subsequence where (AF2) fails. For `w ∈ N`, `μ(C_w) = 1`,
  since `C_w` is clopen. `H ↦ H/N` is an equivariant homeomorphism `{H >= N} -> Sub(S)`, so rigidity gives
  `μ = p δ_(F(A)) + (1-p) δ_N`.
- **The event.** `E = C_g ∩ ∪_a C_a^c` is clopen, with `μ_n(E) >= δ`. But `F(A) ∉ E`, and `N ∉ E` because
  `g ∉ N`. So `μ(E) = 0`, a contradiction.
- **Consequences.** After deleting global fixed points, a nontrivial model is a sofic approximation. Finite
  subgroups act freely off `o(d_n)` points.

## 13.2 `irs-rigid-kazhdan-groups-avoid-haagerup-orbit-full-groups`. PASS

- **Free off the fixed set.** On `Y`, the stabilizer law is `p δ_S + (1-p) δ_e` with `p = 0`.
- **A fixed point.** A proper Haagerup cocycle `b` induces the affine isometric action (HF1) on `L^2(Y, K)`.
  The translation part is bounded because each `c(g, .)` has finite range. (FH) gives a fixed `f_0`, hence
  `||b(c(g,x))|| <= ||f_0(gx)|| + ||f_0(x)||`.
- **Bounded translations.** `c(g,x) ∈ F = {||b|| <= 2R}`, a finite set by properness, on measure
  `>= μ(Y)/2` for every `g`.
- **Counting.** `g ↦ c(g,x)` is injective at free points. Tonelli gives
  `Σ_g μ{c(g,x) ∈ F} <= |F| μ(Y)`, while every term is `>= μ(Y)/2` and `S` is infinite. So `μ(Y) = 0`.

## 13.3 `compression-triples-avoid-proper-cat0-groups`. PASS, with the conditional instance correctly flagged

- **Nesting.** (N1) gives an internal direct product `J_1 x ... x J_n`.
- **Infinite order.** A finitely generated infinite `J` is not torsion by hypothesis, so it has an element `j`
  of infinite order. The conjugates `j_k` generate `Z^n`.
- **Flat.** Cellular isometries with finitely many shapes are semisimple (Bridson 1999). The Flat Torus
  Theorem (Bridson–Haefliger II.7.1) embeds `E^n`, so invariance of domain forces `n <= dim X`.
  Contradiction at `n = d + 1`.
- **The instance.** The `(2,4,6)` Kac–Moody case needs finitely generated torsion subgroups to be finite. The
  node records this as conditional on Norin–Osajda–Przytycki, which was not read. Correct as recorded.

## 13.4 `km-246-lattice-fp-simple-kazhdan-irs-rigid-for-q-ge-4` (citation). PASS as an assembly

- **The type.** `(2,4,6)` is compact hyperbolic, since `1/2 + 1/4 + 1/6 < 1`, and 2-spherical. Thickness
  `q + 1`, so `q_min = q >= 3` for `q >= 4`.
- **The imports.**
  - Caprace–Thom Proposition 4.1(1): (T) for the completions.
  - Corollary 5.3: IRS rigidity, and (T) of `Λ/Z` as an irreducible lattice in `L_+ x L_-`.
  - Caprace–Rémy Theorem 20 with `q > 3`: `Λ = [Λ, Λ]`, and `Λ/Z` is simple.
  - Corollary 21: finite presentation for `q_min > 2`.
- **Trust surface.** Abramenko–Mühlherr 1997 was not read. Caprace–Thom v2 is an unrefereed 2026 preprint.

## 13.5 `kazhdan-compression-instances-have-infinite-vcd`. PASS

- **(N1).** The base case is the internal product `J_1 x tΓt^-1 <= Γ`. Conjugating by `t^n`, and using that
  `t^nΓt^-n` centralizes and meets `J_1 ... J_n` trivially, gives the induction.
- **(N2).**
  - An element of infinite order gives `Z^n` in every finite-index subgroup, so cd is infinite.
  - Otherwise `(Z/p)^n` forces unbounded finite subgroups, which is impossible in a finite-index torsion-free
    subgroup.
- **The correction about Kun–Thom doubles.** They can have finite cd (`kun-thom-double-of-hyperbolic-pair-has-finite-cd`).
  It is recorded honestly in the node.

## 13.6 `vcd-two-groups-contain-no-kazhdan-commuting-pairs`. PASS

- **(CD1).** `A ∩ G_0` is torsion-free and infinite, so it contains `Z`. `cd(Z x B_0) = cd B_0 + 1 <= 2`, so
  `B_0` is free by Stallings–Swan, and `B` is virtually free.
- **(CD2).** If `B` is infinite, `Z <= B_0`, so `cd(A_0) <= 1` and `A_0` is free. But `A_0` has finite index
  in a Kazhdan group, and infinite free groups are not Kazhdan.
- **(CD3).** `cd Z^3 = 3`, and finite subgroups have order `<= [G : G_0]`. An infinite lamp set gives `Z^3` or
  arbitrarily large finite subgroups.
- **Infranormality.** A finite-index infranormal subgroup has `tΓt^-1 <= Γ` of equal index, so they are equal
  and the subgroup is normal. Hence non-normal pairs have infinite index.

Queued: `cd-two-groups-have-no-infranormal-kazhdan-pairs` (a432d62afc, new) and
`kun-thom-double-of-hyperbolic-pair-has-finite-cd` (19e19dbbdb).
