---
rg: 2
id: radu-horizontal-quotient-is-quaternionic-s-arithmetic-proof
kind: route
title: Compute the traces, trace form and conjugation action of two SL_2 elements, read off a definite quaternion algebra with a normalized maximal S-order, and conclude discreteness
target: radu-horizontal-quotient-is-quaternionic-s-arithmetic
requires:
  - radu-horizontal-tree-group-is-linear
artifacts:
  - research/artifacts/radu-pgl2-core.py
  - research/artifacts/radu-quaternion-invariants-check.py
  - research/artifacts/radu-quaternion-order-normalizer-check.py
  - research/artifacts/radu-quaternion-checks-output-2026-09-13.txt
---

# Proof

All computations are exact, in `R = Q[m,s]/(2m^4 − m^3 + 2m^2 − m + 2, s^2 + 4(m^2+m+1))`, by
the artifact scripts. Here `1/m = −(2m^3 − m^2 + 2m − 1)/2` and `1/(m+1) = −(2m^3 − 3m^2 + 5m − 6)/8`.
An element of `R` lies in `F = Q(w)`, `w = m + 1/m = 1/2 + m^2/2 − m^3`, iff it is
`α + βw` with `α, β ∈ Q`. Also `2w^2 − w − 2 = 0`, and `O_F = Z[2w]`, so
`O_F[1/2] = Z[1/2][w]`.

**Part 1: traces.** `det ρ(ba) = m^2` and `det ρ(abxyxy) = 16m^2(m+1)^4`, so `g, h ∈ SL_2(K)`.
The script gives `tr g = w`, `tr h = −1/2`, `tr gh = 1/2 − w`. By Fricke's identity,
`tr[g,h] − 2 = −2 ≠ 0`, so `<g,h>` is irreducible.

**Part 2: `B` is a quaternion algebra.** Polarized Cayley–Hamilton for 2×2 matrices gives
`XY + YX = tr(X)Y + tr(Y)X + (tr XY − tr X tr Y)·1`, together with `X^2 = tr(X)X − 1` for
`X ∈ SL_2`. With traces in `F` (resp. `Z[1/2][w]`), the span of `1, g, h, gh` over `F`
(resp. over `Z[1/2][w]`) is closed under multiplication. The trace form `T_ij = tr(e_i e_j)`
on `e = (1, g, h, gh)` is

```text
[[2, w, −1/2, 1/2−w], [w, w/2−1, 1/2−w, −1/2], [−1/2, 1/2−w, −7/4, −1/4−w/2], [1/2−w, −1/2, −1/4−w/2, −3/4−w/2]],
```

using `wt = −1` for `t = 1/2 − w` and `w^2 = (w+2)/2`. Its determinant is `−4` (script), so
the `e_i` are independent. `B ⊗_F K = M_2(K)`, so `B` is central simple of dimension 4.

**Part 3: ramification.**
* *Real places.* The leading minors of `T` are `2`, `w/2 − 3`, `4` and `−4`: the 3×3 minor,
  expanded by hand, has vanishing `w`-coefficient and constant term 4. At both real places
  `w/2 − 3 < 0`. The sign sequence `+, +, −, +, −` has three changes, so the trace form has
  signature `(1,3)`. That is the trace form of the Hamilton quaternions; on `M_2(R)` it is
  `(3,1)`. So `B` ramifies at both real places.
* *Odd primes.* `O = Z[1/2][w]⟨e⟩` is an order, and its trace-form determinant `−4` is a unit at
  every odd prime. So `O_𝔭` is a maximal order of reduced discriminant `1`, which exists only
  in the split algebra, and `B` is split at all odd `𝔭`.
* *Primes above 2.* `17 ≡ 1 mod 8`, so `2 = 𝔮𝔮'` in `F` with `F_𝔮 = F_(𝔮') = Q_2`. At the place
  `𝔮` where `w = m + 1/m` with `v_2(m) = 1` (so `v_𝔮(w) = −1`), the independent matrices
  `1, g, h, gh` lie in `M_2(Q_2)`, so `B_𝔮 = M_2(Q_2)`. Ramification sets have even size, so
  `B` is also split at `𝔮'`. This is item 1; item 2 is the determinant computation.

**Part 4: normalizing.** For each `s ∈ {a,b,c,x,y,z}` and each `e_i`, the script computes
`ρ(s) e_i ρ(s)^(-1)` exactly. It solves for coefficients in the basis `e` through `T^(-1)`,
checks the reconstruction, and checks that all coefficients lie in `Z[1/2][w]`. All 24 checks
pass. So conjugation by `ρ(s)` maps `O` into `O`, and onto it since `ρ(s)` is an involution in
`PGL_2`. Conjugation embeds `ρ(Γ_R)` into `Aut_F(B) = PB^×(F)` (Skolem–Noether). It is
injective, because an element of `PGL_2(K)` centralizing `B ⊗ K = M_2(K)` is trivial. Its image
lies in `N(O)/F^×`. This is item 3.

**Part 5: discreteness.** Let `U` be a compact neighbourhood of `1` in
`PB^×(F_𝔮) × PB^×(F_(𝔮'))`. For `γ ∈ N(O)/F^×` with coordinates in `U`, choose a representative
`β ∈ B^×` with `βOβ^(-1) = O`, scaled by an element of `F^×` so that `β ∈ O` and `nrd β` has
`𝔮`- and `𝔮'`-valuations in `{0, 1}`. The `S`-units modulo squares form a finite group, so
`nrd β` lies in a finite set. At odd places `β` is integral. At the two real places `B_v ≅ H`
and `nrd` is a positive definite form, so `β` is bounded there. At `𝔮`, `𝔮'` it is bounded by
`U`. So `β` ranges over a set of lattice points of `O ⊗ Z[1/2]` that is bounded at every
place, which is finite, and `N(O)/F^×` is discrete there. `PGL_2(Q_2)` acts properly on its
3-regular Bruhat–Tits tree, so `Q` acts properly on `T_h × T'`. At `𝔮` the representation is
the `ρ` of `radu-horizontal-tree-group-is-linear`, whose item 2 identifies it with the
horizontal tree action. `ρ(V) = Stab_Q(v_0)` is `Q ∩ (compact × PB^×(F_(𝔮')))`, so it is
discrete in `PGL_2(F_(𝔮'))`. This is items 4 and 5. ∎
