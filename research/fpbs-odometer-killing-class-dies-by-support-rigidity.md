---
rg: 2
id: fpbs-odometer-killing-class-dies-by-support-rigidity
kind: claim
title: The quasiconvex-null odometer killing-word class on the F_2 boundary is killed without cost by pointwise match rigidity, because its sign coding is two-sided injective (paperfolding recognizability survives the sparse killing windows); so every imp action over it, of any Krieger type, has totally dissipative diagonal, and support rigidity is a fourth filter beyond Dini, shadow and quasiconvex-null
distinct_from:
  fpbs-zero-entropy-ray-codes-are-support-rigid: that proves support rigidity for any two-sided injective binary coding and shows that every zero-entropy system has some such coding (Krieger); it says nothing about a given coding, and the odometer class is built from one specific coding, fixed by the killing-word construction. This proves that this specific coding is two-sided injective.
  fpbs-quasiconvex-null-small-classes-exist-on-free-boundary: that constructs the odometer class and shows it passes the Dini, shadow and quasiconvex-null filters, and leaves open whether anything short of the global cost argument excludes it; this shows support rigidity excludes it.
  fpbs-rotation-support-rigidity-kills-type-iii-classes: that kills classes on rotation rays, which lie in the limit set of a Schottky subgroup; the odometer class is null on every such limit set, so this is the first class that passes the quasiconvex filter and is still killed pointwise.
---

**ESTABLISHED for `F_2` (written proof; see `research/fpbs-odometer-killing-class-dies-by-support-rigidity-proof.md`;
script `experiments/odometer-match-rigidity-2026-09-17/recognize.py`, output `recognize.out`).** The proof uses
Birkhoff's theorem for the dyadic odometer and Theorem 2 of `fpbs-zero-entropy-ray-codes-are-support-rigid`. Otherwise
it is self-contained.

**Why this matters for the flagship.** The Bevilacqua--Bowen (BB) route to fixed price one for a cocompact `Sp(n,1)`
lattice needs an amenable, ergodic, PDR imp action. Its Zimmer boundary class must pass every known filter. Previous
lanes had three filters:
- **Dini**: the class is singular to every Dini measure;
- **shadow**: no measure in the class is shadow-summable;
- **quasiconvex-null**: the class is null on `Gamma Lambda_H` for every infinite-index quasiconvex `H`.

`fpbs-quasiconvex-null-small-classes-exist-on-free-boundary` built an odometer class `[nu]` on `dF_2` that passes all
three. `F_2` has cost 2, so it has no certificate. So the three filters are not enough, and a fourth mechanism was
needed that excludes `[nu]` without using cost.

This claim supplies it. `[nu]` is **support-rigid**. Pointwise match rigidity kills it, and it kills every class
carried by the same rays, whatever its Krieger type. So the filters now in hand are Dini, shadow, quasiconvex-null and
support rigidity.

## Setting

Use the construction of `fpbs-quasiconvex-null-small-classes-exist-on-free-boundary`:
- the dyadic odometer `Omega = lim Z/q_n`, `q_n = 2^{n+2}`, with Haar measure `m` and `T x = x + 1`;
- the symmetric labelling `F : Omega -> {a, A, b, B}`, with parity types (T), odd symmetry `F(-y) = F(y)^{-1}` (S), and
  killing windows `k_j` of length `l_j` inserted at stages `n_j`;
- `zeta(x) = F(x+1) F(x+2) ...` and `nu = sum_g c_g g_* zeta_* m`.

That construction leaves some choices free. Fix three of them. Each is admissible, and each is compatible with its
conditions (O1) and (O2).
- **(A1)** Every Toeplitz fill uses the letter `a`, not `A`.
- **(A2)** The stage-`n_j` window starts at `r_j ∈ {q_{n_j}/8 + 1, q_{n_j}/8 + 2}`, with the parity required by the first
  letter of `k_j`. Its length satisfies `l_j + 1 < 2^{n_j - 5}`.
- **(A3)** `delta := sum_j 2 l_j / q_{n_j} <= 2^{-5}`.

Write `s(y) = +1` if `F(y) ∈ {a, b}` and `s(y) = -1` if `F(y) ∈ {A, B}`. The **forward and backward sign itineraries**
are `iota_+(x) = (s(x+n))_{n >= 1}` and `iota_-(x) = (s(x-n))_{n >= 0}`.

## Theorem

**Theorem 1 (two-sided injectivity).** There is a `T`-invariant, `m`-conull Borel set `X_0 ⊂ Omega` on which
`iota_+` and `iota_-` are both injective.

The idea is **recognizability**. Off the killing windows, the signs form the regular paperfolding sequence
`p(2^k u) = chi(u)`, where `chi(u) = +1` if and only if `u ≡ 1 mod 4`. So `x` can be read off level by level:
- the parity of `x` is the parity class on which the signs alternate in steps of 2. On the odd class they alternate
  everywhere; on the even class they alternate with density exactly `1/2`;
- given `x mod 2^{k+1}`, the positions `y ≡ 2^k mod 2^{k+1}` carry `chi(y / 2^k)`, and this determines
  `x mod 2^{k+2}` by majority vote.

(A2) and (A3) keep the windows' relative density in every residue class at most `delta + 2^{-5} <= 1/16`. So both
votes have a fixed margin along every Birkhoff-generic orbit.

**Match rigidity** (proof, Corollary 5.1). `zeta` is injective on `X_0`. If `x, x' ∈ X_0`, `g ∈ F_2` and
`g zeta(x) = zeta(x')`, then `x' ∈ x + Z`.

**Corollary 2 (the class dies pointwise).** Let `(Z, mu_Z)` be an imp `F_2`-space with a measurable equivariant
`xi : Z -> dF_2`. Suppose that for every `E` of finite measure, `xi_*(mu_Z|_E)` is nonatomic and carried by
`F_2 zeta(X_0)`. This holds, for example, whenever `xi_*(mu_Z|_E) << nu`. Then `F_2` acts totally dissipatively on
`(Z x Z, mu_Z x mu_Z)`. In particular:
- no ergodic imp action over `[nu]` is PDR;
- the Maharam extension of `[nu]`, and every imp action over it, has totally dissipative diagonal;
- the same holds for every nonatomic class carried by `F_2 zeta(X_0)`, whatever its Krieger type. So no such class is
  the boundary class of a BB certificate.

*Proof of Corollary 2.* Embed `X_0` in `X_0 x Z/2` by `x -> (x, x + 1 mod 2)`. This intertwines `T` with
`sigma(x, j) = (Tx, j+1)`. It carries `zeta` to the ray code `zeta^+(x, j) = prod_n t_{n+j}^{s(x+n)}` of
`fpbs-zero-entropy-ray-codes-are-support-rigid`. `T` is aperiodic, because `x + p ≠ x` for `p ≠ 0`. By Theorem 1,
`(X_0, T, s)` is two-sided injective. Apply Theorem 2 of that claim. `□`

## Calibration

- **`F_2` has cost 2.** No certificate may exist. The corollary agrees and only removes a candidate.
- **Why (A2) and (A3) are imposed.** Without them, one window could cover a large share of a residue class `k` near
  `n_j`, and the majority vote at level `k` would lose its margin. The proof needs the margin. The conditions cost
  nothing, because the construction was free to choose `r_j` and `n_j`. Whether injectivity fails without them is not
  decided here.
- **Script** (`recognize.py`, output `recognize.out`). On `Z/2^16`, with windows `(n_j, l_j) = (8, 6), (12, 100)`:
  - the paperfolding alternation densities are `1.0000` on the odd class and `0.5000` on the even class;
  - the window densities satisfy `max_k eta_k = 0.028 <= delta + 2^{-5} = 0.055`;
  - the recognition algorithm recovers `x mod 2^15` from the forward and from the backward itinerary for all 65
    residues tested, and `x mod 2^13` from forward windows of length `q/4` for 60 random `x`. There are 0 failures.

## What this leaves (named open statement)

**Transplant to cocompact lattices.** Is there, for a torsion-free cocompact `Sp(n,1)` lattice (or any torsion-free
hyperbolic `Gamma`), a quasiconvex-null, Dini-singular, non-shadow-summable class that is **not** support-rigid?

Anything that passes the four filters on `F_2` is constrained: it cannot be carried by the rays of a two-sided
injective stationary coding. So a surviving class on `F_2`, if one exists, lives on the rays of a positive-entropy
coding, or of a zero-entropy coding that is not recognizable.

For lattices, the step is the one named in the odometer node: a symmetric odometer code in Cannon's geodesic
automaton. What this claim adds is that such a code must also be **recognizable**, with a skeleton whose votes survive
the killing windows. Only then will support rigidity transplant along with it.
