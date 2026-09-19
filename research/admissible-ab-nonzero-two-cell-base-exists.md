---
rg: 2
id: admissible-ab-nonzero-two-cell-base-exists
kind: claim
title: The rank-5 core (C2) of w = yxYXXyyxYXYxYYxyXy is admissible. Its cylinder row c is unimodular over ZG by an explicit 16-term certificate, so pd I_{G/H} <= 1 with ab != 0, every one-cell deletion fails, rho(H,G) is 0 or 1, and either RP(H,G) holds or Gamma_{aleph_1}(H,G) is an Eilenberg-Ganea counterexample. The relator-slide route to RP from this certificate fails in A_5
distinct_from:
  rank-five-degree-one-two-cell-configuration-is-a-core: that proves pi_1(C) -> G is injective for (C2), so (C2) is a core, and leaves admissibility open. This proves admissibility by a certificate in ZG and draws the consequences for rho and for Eilenberg-Ganea.
  two-cell-core-deletions-need-a-unit-fox-coefficient: that reduces admissibility to unimodularity of c (U2) and shows one-cell deletions fail when ab != 0 (U3, U4). This supplies the first pair where the unimodularity actually holds with ab != 0, so its two conditions separate.
  degree-one-two-cell-cores-with-ab-nonzero-exist: that gives a rank-3 ab != 0 core whose row c is killed by a character, so it is not admissible. The core here has no killing character and is admissible.
  two-cell-ab-nonzero-admissible-needs-g-in-conj-closure: that proves necessary conditions for an admissible ab != 0 two-cell core. This shows those conditions are met by an admissible example, not only by a candidate.
artifacts:
  - research/admissible-ab-nonzero-two-cell-base-exists-proof.md
  - experiments/c2-free-by-cyclic-2026-09-18/verify_unimodular.py
  - experiments/c2-free-by-cyclic-2026-09-18/zg.py
  - experiments/c2-free-by-cyclic-2026-09-18/redJ.py
  - experiments/c2-free-by-cyclic-2026-09-18/searchJ.py
  - experiments/c2-free-by-cyclic-2026-09-18/solveQ.py
  - experiments/c2-free-by-cyclic-2026-09-18/certuni.py
  - experiments/c2-free-by-cyclic-2026-09-18/gamma2.py
  - experiments/c2-free-by-cyclic-2026-09-18/a5check.py
  - experiments/c2-free-by-cyclic-2026-09-18/solvcheck.py
  - experiments/c2-free-by-cyclic-2026-09-18/RESULTS.md
---

**ESTABLISHED** via `admissible-ab-nonzero-two-cell-base-exists-proof` (unreviewed,
computer-assisted). The certificate is a finite identity in `ZG`. `verify_unimodular.py` checks it
in under a second using the normal form of `G = F_4 ⋊ Z`, which solves the word problem exactly.
It imports nothing from the other scripts.

## Statement

Let `G = ⟨x, y | w⟩` with `w = yxYXXyyxYXYxYYxyXy`, and let `H = π_1(C) ≤ G` be the image of the
core (C2) of `rank-five-degree-one-two-cell-configuration-is-a-core`:
- basis `a = XyxYx`, `b = Xyyyx`, `c = XYxyx`, `d = y`, `e = xyX`;
- cells `u_0 = dEbcBADDed`, `u_1 = bcBAAbDcBd`;
- `g = Xy` and `ε = 1`.

Put `c_z = g ∂_z u_0 − ∂_z u_1 ∈ ZG` for `z ∈ {a,b,c,d,e}` (left Fox derivatives, evaluated in
`G`).

1. **(A1) Certificate.** `Σ_z c_z d_z = 1` in `ZG` for the following `d_z`, written as signed
   words in `x, y`:
   - `d_a = Xyx + XyxYXyx − xyXYYxYXyyXyxy − YYxyXyyxYXXyxYxYYxyXyyxYXYXyyXYxxyXYYxYXyyXyxyy`
   - `d_b = Xyx`
   - `d_c = −1`
   - `d_d = YXyx − Xyx + x`
   - `d_e = YXyx − yXYxxyXYYxYXyyXyxy + x + xYXyx − xyXYXyx + xx − yx`
2. **(A2) Admissibility.** `c` is unimodular, so `pd_{ZG} I_{G/H} ≤ 1` by (U2) of
   `two-cell-core-deletions-need-a-unit-fox-coefficient`. The complement `ker(d·)` of `c·ZG` in
   `ZG^5` is stably free of rank 4.
3. **(A3) No one-cell deletion.** `H` is a degree-one `(a,b) = (1,2)` base with `ab ≠ 0`, so by
   (U3) and (U4) no free basis of `π_1(C^1)` has a one-cell deletion that presents `G`.
4. **(A4) The dichotomy.** `ρ(H,G) ∈ {0, 1}` by Theorem 3 of
   `relative-realization-is-relative-efficiency`, since `n(C) = 2`. Since `cd G = 2`, the pair
   satisfies the hypotheses of `relative-eg-pair-iff-aleph-one-star-amalgam-has-gd-two`, so
   `cd Γ_κ(H,G) ≤ 2` for every `κ`. Hence exactly one of the following holds.
   - `ρ(H,G) = 0`. Equivalently `RP(H,G)` holds: some relative presentation `⟨H, T | R⟩` of `G`
     with `|R| − |T| = 2` is aspherical.
   - `ρ(H,G) = 1`. Then `Γ_{ℵ_1}(H,G)` has `cd 2` and `gd 3`, so it is a counterexample to the
     Eilenberg–Ganea conjecture.
5. **(A5) A route to RP from the certificate.** Since `d_c = −1`, sliding each relator
   `r_z = z φ(z)^{-1}` (`z ≠ c`) of the core relative presentation `Y_1` across conjugates of
   `r_c`, with coefficients `d_z`, turns the `r_c`-coefficient of the sphere into `−1`. Deleting
   `r_c` then gives a complex `Y''` with `ρ(Y'') = 0`. After eliminating `a, b, d, e` and putting
   `c = t φ(c)`,
   `π_1(Y'') = Γ'' = ⟨t, x, y | R_0, R_1⟩`,
   where `R_0` has length 391 and `t`-exponent 1, and `R_1` has length 350 and `t`-exponent 2
   (`gamma2.py`). The kernel `N = ⟨⟨t⟩⟩` of `Γ'' → G` (put `t = 1`) is perfect, and `Y''`
   realizes `RP(H,G)` iff `N = 1`, that is, iff `t = 1` in `Γ''`.
6. **(A6) This slide route fails for this certificate.** `Γ''` maps onto `A_5` with `t ↦` a
   nontrivial element (18 such maps with `x` fixed up to conjugacy, `a5check.py`; GAP's
   `GQuotients` agrees). So `t ≠ 1` in `Γ''` and `N ≠ 1`: this `Y''` does not present `G`. The
   image of `N` in `A_5` is all of `A_5`, as it must be for a perfect `N`. This decides nothing
   about `ρ`. Other certificates `d + k` (`k ∈ ker(c·)`, with `d_c` still `−1`) give other groups
   `Γ''`, and other relative presentations are not slides of `Y_1` at all.

## What this changes

- It is the first admissible degree-one two-cell base with `ab ≠ 0`. Before it, every
  `ab ≠ 0` candidate either had a character killing `c` or had unknown unimodularity. So the
  admissible `ab ≠ 0` case of the lane is not empty, and it is not closed by any test on `c`.
- For this one countable pair, Eilenberg–Ganea for groups of size `ℵ_1` reduces to a single
  rank question: can the stably free rank-1 module `π_2` of the defect-1 core presentation be
  removed? (A5) turns every certificate with a unit entry into a finite test, `t = 1` in `Γ''`,
  whose success proves `RP(H,G)`. (A6) shows that the first certificate fails that test, and
  it fails in `A_5`. A proof of `ρ = 1` must therefore defeat every such certificate at once.
