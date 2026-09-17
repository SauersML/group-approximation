---
rg: 2
id: lk-b4-never-proximal-on-finite-index-subgroups-proof
kind: route
title: Eigenvalue 1 in LK(s1 s3^-1) and the 3-2-1 multiplicity pattern of LK([a,b]) force modulus ties at every index
target: lk-b4-never-proximal-on-finite-index-subgroups
requires: []
artifacts: [experiments/braid-tropical-pingpong-2026-09-17/README.md, experiments/braid-tropical-pingpong-2026-09-17/lk.py, experiments/braid-tropical-pingpong-2026-09-17/lk_out.txt, experiments/braid-tropical-pingpong-2026-09-17/factor_witnesses.py, experiments/braid-tropical-pingpong-2026-09-17/factor_witnesses_out.txt, experiments/braid-tropical-pingpong-2026-09-17/exact_cover.py, experiments/braid-tropical-pingpong-2026-09-17/exact_cover_out.txt]
---

Notation is as in the claim. For a `6 × 6` matrix `M` over `K`, list its eigenvalues with multiplicity and
order them by decreasing absolute value, `|λ_1| >= ... >= |λ_6|`. Say `M` has a **gap at `k`** if
`|λ_k| > |λ_(k+1)|`. We show that for each `k` some `h ∈ H` has no gap at `k`. All eigenvalues below lie in
`K`, so no extension of the absolute value is needed.

**Step 0: two identities in `Z[q^±1, t^±1][x]`.** These are exact sympy computations
(`factor_witnesses.py`, output `factor_witnesses_out.txt`), using Krammer's matrices from `lk.py`. Those matrices
satisfy the `B_4` relations (`lk_out.txt`).

- `det(x - ρ(a)) = (x - 1)^2 (x + q)(x + q^-1)(x + q^2 t)(x + q^-2 t^-1)`.
- `det(x - ρ(c)) = (x - α)^3 (x - β)^2 (x - γ)`, with `α = q^4 t^2`, `β = q^-2 t^-2`, `γ = q^-8 t^-2`.

Both are polynomial identities, so they survive the ring map `q -> q_0`, `t -> t_0` into `K`. Over `K`, the
eigenvalues of `ρ(a)` are `1, 1, -q_0, -q_0^-1, -q_0^2 t_0, -q_0^-2 t_0^-1`. The eigenvalues of `ρ(c)` are
`α_0` three times, `β_0` twice and `γ_0` once, where `α_0, β_0, γ_0` are the specialized values. Some of these
may coincide.

**Step 1: powers and conjugates.** If `g ∈ B_4` and `m ∈ Z`, the eigenvalues of `ρ(g x^m g^-1)` are the `m`-th
powers of those of `ρ(x)`, with the same multiplicities. By hypothesis `H` contains `h_a = g a^m g^-1` and
`h_c = g' c^n g'^-1` with `m, n != 0`, and hence also `h_c^-1`. For a finite-index subgroup `H` of `F_2` or `B_4`,
take `g = g' = 1`: every element has a nontrivial power in `H`.

**Step 2: `k = 3`, from `h_a`.** The eigenvalue multiset of `ρ(h_a)` is
`{1, 1, (-q_0)^m, (-q_0)^-m, (-q_0^2 t_0)^m, (-q_0^2 t_0)^-m}`. It is closed under `λ -> λ^-1`, so the sorted
moduli satisfy `|λ_i| |λ_(7-i)| = 1`. In particular `|λ_3| |λ_4| = 1`.

Suppose `|λ_3| > |λ_4|`. Then `|λ_3| > 1 > |λ_4|`, so `|λ_1|, |λ_2|, |λ_3| > 1` and `|λ_4|, |λ_5|, |λ_6| < 1`.
No eigenvalue has modulus 1, which contradicts the eigenvalue `1`. So `ρ(h_a)` has no gap at 3.

**Step 3: `k ∈ {1, 2, 4, 5}`, from `h_c` and `h_c^-1`.** Group the six eigenvalues of `h = ρ(h_c)` into the
classes `A = {α_0^n × 3}`, `B = {β_0^n × 2}` and `C = {γ_0^n × 1}`, of sizes 3, 2 and 1.

If `h` has a gap at `k`, then the `k` eigenvalues of largest modulus have strictly larger modulus than the
others. So they form a union of whole classes: equal eigenvalues have equal modulus. The only unions of size 1
or 2 are `C` and `B`. Similarly, a gap at `6 - k` means that the `k` eigenvalues of smallest modulus form a union
of whole classes.

`h^-1` has the inverse eigenvalues, so `h^-1` has a gap at `k` exactly when `h` has a gap at `6 - k`.

- **`k = 1` or `k = 5`.** Suppose `h` and `h^-1` both have a gap at `1`. Then `h` has gaps at 1 and 5. So
  `C` is the unique eigenvalue of strictly largest modulus and also the unique one of strictly smallest modulus,
  which is impossible with six eigenvalues. So one of `h, h^-1 ∈ H` has no gap at 1. By the inverse rule, the
  other one has no gap at 5.
- **`k = 2` or `k = 4`.** Suppose `h` and `h^-1` both have a gap at 2. Then `h` has gaps at 2 and 4. The top two
  eigenvalues form a class of size 2, which must be `B`. The bottom two also form a class of size 2, which is again
  `B`. But `B` cannot be both the strictly largest and the strictly smallest pair. So one of `h, h^-1` has no gap
  at 2, and the other has no gap at 4.

**Conclusion.** For each `k ∈ {1, ..., 5}`, one of `ρ(h_a), ρ(h_c), ρ(h_c)^-1` has no gap at `k`. ∎

**Consequences.** In a P_Θ-Schottky group every nontrivial element is Θ-proximal, meaning it has a gap at
every `k ∈ Θ`. The step "P_Θ-Anosov implies every infinite-order element is Θ-proximal" is
the standard fact from Guéritaud–Guichard–Kassel–Wienhard, *Anosov representations and proper actions*,
Geom. Topol. 21 (2017). It is cited and was not re-checked here. The point `ker ρ ∩ F_2 = 1 ⇒ ker ρ` central is
proved in the README: the centralizer of `F_2` in `B_4` is `Z(B_4)`.

**Consistency check (not needed for the proof).** `exact_cover.py` verifies the monomial-valuation special
case, `|·| = e^(-w·(v(q), v(t)))` on `Q(q, t)` for every direction `w`, independently. It enumerates the
characteristic polynomials of all 372 cyclically reduced words of length at most 5 in `a, b`, checks every
critical ray exactly, and finds no uniform gap. For `k = 3` it finds length-1 witnesses (`a`), and for the other
`k` witnesses of length at most 4 (`c = abAB` has length 4), as the proof predicts. `spectra_L5.pkl` is regenerated by
`trop.py 5`.
