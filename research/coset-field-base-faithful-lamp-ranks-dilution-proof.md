---
rg: 2
id: coset-field-base-faithful-lamp-ranks-dilution-proof
kind: route
title: Clear denominators into a diagonal factorization over the lamp group ring, then dilute site idempotents along the infinite coset orbit
target: coset-field-rank-certificates-need-base-faithful-lamp-ranks
requires: []
---

Notation is as in the target. `rk` always denotes a Sylvester matrix rank function, meaning Malcolmson's axioms:
- `rk(1) = 1`;
- `rk(MN) <= min(rk M, rk N)`;
- `rk(M ⊕ N) = rk M + rk N`;
- `rk [[M, P], [0, N]] >= rk M + rk N`.

We use four elementary consequences.
- **(R1) Column bound.** A `d x r` matrix has rank at most `r`, since `M = M I_r`.
- **(R2) Subadditivity.** `rk(M + N) <= rk M + rk N`, since `M + N = [I I] (M ⊕ N) [I; I]`.
- **(R3) Conjugation invariance.** `rk(uMu^(-1)) = rk M` for an invertible `u`.
- **(R4) Orthogonal idempotents add.** If `e, e'` are orthogonal idempotents, then `rk(e + e') = rk e + rk e'`.
  - For `≤`, apply (R2).
  - For `≥`, write `e ⊕ e' = [e; e'] [e e']`. This gives `rk e + rk e' <= rk [e; e']`. Also
    `[e; e'] = [e; e'] (e + e')`, so `rk [e; e'] <= rk(e + e')`.

## Step 1: diagonal form (item 1)

**Only if.** Suppose `AB = I_d` over `R_p`, where `A` has size `d x r` and `r < d`. The entries have the form
`Σ f_g u_g` with `f_g ∈ K = Frac(O)`.
- **Left denominators for `A`.** Pick a common denominator `s ∈ S` of all coefficients in one row of `A`. Then
  `f = s^(-1) Σ (s f_g) u_g`, and every coefficient `s f_g` lies in `O`.
- **Right denominators for `B`.** Write `f = Σ u_g h_g` with `h_g = σ_g^(-1)(f_g)`. Pick a common denominator
  `t ∈ S` of all `h_g` in one column of `B`. Then `f = (Σ u_g (h_g t)) t^(-1)`.

So `A = D_1^(-1) A'` and `B = B' D_2^(-1)`, where `A'` and `B'` are over `O ⋊ G = F_p[W]` and
`D_1 = diag(s_i)`, `D_2 = diag(t_i)` have entries in `S`. Then `I_d = D_1^(-1) A'B' D_2^(-1)`, so
`A'B' = diag(s_i t_i)`. Each `s_i t_i` lies in `S` because `O` is a domain.

**If.** A factorization `diag(s_i) = A'B'` over `F_p[W]` gives `(diag(s_i)^(-1) A') B' = I_d` over `R_p`, and
`diag(s_i)` is invertible there.

## Step 2: rank-function certificates (item 2)

**A base-faithful `rk` proves the rank condition.** Suppose `A'B' = D = diag(s_i)`, with `A'` of size `d x r`.
- By the additivity axiom, `rk D = Σ rk s_i = d`.
- By the product axiom and (R1), `rk D <= rk A' <= r`.
- So `r >= d`, and Step 1 gives the rank condition for `R_p`.

**Restriction.** Let `rk'` be a rank function on `R_p`, and restrict it along the unital inclusion
`F_p[W] -> R_p`. Every `s ∈ S` is invertible in `R_p`, so `1 = rk'(s s^(-1)) <= rk'(s) <= 1`.

**Compactness.** The Sylvester rank functions form a closed subset of `∏_M [0, size(M)]`, which is compact. For
a finite `F ⊂ S`, the set `C_F = {rk : rk(s) = 1 for s ∈ F}` is closed. The sets `C_F` have the finite
intersection property, so they have a common point.

**Why this is exactly the rank-function method.** Suppose that for every diagonal factorization some rank
function obstructs it. Take `D` to be each `s_j ∈ F` repeated `N` times, with `|F| = m`. Its obstructing `rk`
needs `Σ rk = N Σ_j rk(s_j) > mN - 1`. So `rk(s_j) >= 1 - 1/N` for every `j`. A limit point as `N -> ∞` lies
in `C_F`. So obstructing every factorization is equivalent to the existence of one base-faithful `rk`.

## Step 3: idempotent dilution (item 3)

**The idempotent has rank 0.** Let `e_1, ..., e_N` be pairwise orthogonal conjugates of `e`. Then
`f = Σ e_i` is an idempotent. By (R3) and (R4), `N rk(e) = rk(f) <= rk(1) = 1`, and `N` is arbitrary.

**The ideal has rank 0.** Every `a ∈ TeT` is a finite sum `Σ y_k e z_k`. By (R2) and the product axiom,
`rk(a) <= Σ rk(e) = 0`.

**Every site.** `H = G/Γ` is one `G`-orbit, and `u_g (x_(c_0) - 1) u_g^(-1) = x_(g c_0) - 1`. Since `ψ` is
unital, (R3) applies.

**Matrices.** A matrix with entries in `TeT` also has rank 0: it is a sum of single-entry matrices, and
`rk(a E_ij) <= rk(a)`. So by (R2) the rank of any matrix depends only on its class modulo `TeT`. We use this
in Step 4.

## Step 4: the members (item 4)

**Marked-site targets.** Use the notation of `diagonal-tensor-orbit-corner-induction-proof`, with `A = Z`,
`k = F_p` and `X = H`.
- `T_r = R_r(G, 0) = C^(⊗r) ⋊ G`, and `Φ_r(n g) = v_n^(⊗r) u_g`. Here `v_n(∞) = 1`, and the kernel of
  evaluation at `∞` is `D = ⊕_H F_p[Z]`.
- **Site idempotents.** Let `e_x ∈ D` be the unit of the `x`-coordinate, and put `ẽ_x = e_x ⊗ 1`.
  - They are pairwise orthogonal idempotents of `R_r(G, j)`.
  - `u_g ẽ_x u_g^(-1) = ẽ_(gx)`.
  - `H` is infinite.
- **The kernel is site-generated.** The kernel `J` of (DWI3) satisfies `J = Σ_x ẽ_x J`, since
  `(e_x a ⊗ b) u_h = ẽ_x (e_x a ⊗ b) u_h`.
- **Factoring down.** By Step 3, every `rk` on `R_r(G, j)` vanishes on matrices over `J`, so it factors through
  `R_(r-1)(G, j)`. Induction on `r` makes it factor through `R_0(G, 0) = F_p[G]`, by evaluation at `∞` in every
  factor.
- **Conclusion.** This composite sends `Φ_r(x_c)` to `u_1 = 1`. So `Φ_r^* rk` is the pullback of a rank
  function on `F_p[G]` along the lamp augmentation `π`, and `rk(Φ_r(x_c - 1)) = 0`.
- **The tensor-power version.** The construction of `rf-lamp-permutational-wreaths-satisfy-stable-finiteness`
  has the same shape: a split quotient that keeps `F_p[G]`, and an ideal of finite-support matrix algebras over
  the orbit. The same argument applies to it as recorded there.

**First-order jets.**
- **The module.** `I` and `I^2` are `G`-stable, so `F_p[W]` acts on `V = O/I^2`, which has basis
  `1, τ_c = x_c - 1`. Here `x_c · 1 = 1 + τ_c` and `x_c · τ_(c') = τ_(c')`, so `ψ(x_c - 1)` is the rank-one map
  `1 -> τ_c`.
- **The idempotents.** Let `ε_c ∈ End(V)` be the projection onto `F_p τ_c` along the other basis vectors.
  - These are orthogonal idempotents.
  - They are permuted by `ψ(u_g)`.
  - `ψ(x_c - 1) = ε_c ψ(x_c - 1)`.
- **Conclusion.** Step 3 applies to every unital subring `T ⊆ End(V)` that contains `ψ(F_p[W])` and the `ε_c`.
  All of `End(V)` has no rank function at all, because `V ≅ V ⊕ V`.

## Remark: the linear-sofic example (not needed for the theorem)

This is the example in the target's last bullet.
- `P = (x + y + 1)` is prime in `F_p[x^(±1), y^(±1)]`. The quotient is `F_p[x^(±1), (1 + x)^(-1)]`, a domain.
- `x^a y^b - 1` maps to `x^a (-1 - x)^b - 1`.
  - If `b = 0`, this is `x^a - 1`, which is nonzero for `a ≠ 0`.
  - If `b ≠ 0`, the rational function `x^a (-1 - x)^b` has a zero or pole of order `|b|` at `x = -1`, so it is
    not 1.
- So the rank over `Frac(F_p[x^(±1), y^(±1)]/P)` is group-faithful but kills `x + y + 1`. ∎
