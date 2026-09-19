---
rg: 2
id: fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups-proof
kind: route
title: Proof that match rigidity of a Borel ray code on a torsion-free hyperbolic group gives finitely many joint returns off a Fubini-null set, hence a totally dissipative diagonal for every class on the rays
target: fpbs-match-rigid-ray-codes-die-on-hyperbolic-groups
requires:
  - fpbs-zero-entropy-ray-codes-are-support-rigid
  - fpbs-dini-boundary-class-diagonal-dissipative
  - fpbs-odometer-killing-class-dies-by-support-rigidity
---

# Proof

Notation and hypotheses (R), (MR), (MR±) are as in the claim. `|g|` is word length, and `Gamma ∪ dGamma` is the Gromov
compactification.

## Imported inputs

- **(G1)** If `g_n -> xi ∈ dGamma` and `u, v ∈ Gamma` are fixed, then `v g_n u -> v xi`. The reason is that
  `d(g_n, g_n u) = |u|` is bounded, and `Gamma` acts on `Gamma ∪ dGamma` by homeomorphisms.
- **(G2)** In a torsion-free hyperbolic group, every `g ≠ 1` is loxodromic and fixes exactly two points of `dGamma`.
  So the set `Q` of points with nontrivial stabilizer is countable.
- **(UM)** Analytic subsets of standard Borel spaces are universally measurable. Tonelli's theorem holds for the
  completion of a product of finite measures (e.g. Folland, *Real analysis*, 2.39).
- **(Rec)** Recurrence for nonsingular actions of countable groups (Aaronson, *An introduction to infinite ergodic
  theory*, §1.6). If `C` is the conservative part and `A ⊂ C` has positive measure, then a.e. point of `A` returns
  to `A` under infinitely many `g`.

## Step 1. Trivial stabilizers

**Lemma 1.1.** For each `xi ∈ dGamma`, the set `{x ∈ X_0 : xi ∈ Gamma zeta(x)}` is contained in one `T`-orbit. So
`P = {x ∈ X_0 : zeta(x) ∈ Q}` is countable and `T`-invariant, and `X_1 = X_0 \ P` is Borel, `T`-invariant and
co-countable.

*Proof.* If `h zeta(x) = h' zeta(x')`, then `h'^{-1} h zeta(x) = zeta(x')`, and (MR) gives `x' ∈ x + Z`. So `zeta`
is at most countable-to-one, and `P = zeta^{-1}(Q)` is countable. `Q` is `Gamma`-invariant and
`zeta(x + k) = c_k(x) zeta(x)`, so `P` is `T`-invariant. `□`

Since `Gamma zeta(P)` is countable, a nonatomic measure carried by `Gamma zeta(X_0)` is carried by `Gamma zeta(X_1)`.
From now on work on `X_1`. (R), (MR) and (MR±) restrict to it, and `Stab(zeta(x)) = 1` for `x ∈ X_1`.

**Lemma 1.2 (orbits through rays).** Let `x, y ∈ X_1` and `gamma ∈ Gamma`. Then `gamma zeta(x) = zeta(y)` if and only
if there is `k ∈ Z` with `y = x + k` and `gamma = c_k(x)`.

*Proof.* "If": `zeta(x + k) = c_k(x) zeta(x)`. "Only if": (MR) gives `y = x + k`. Then `c_k(x)^{-1} gamma` fixes
`zeta(x)`, so it is `1`. `□`

## Step 2. Finitely many matches off the bad relation

Put `Bad = Rel ∩ X_1^2`. It is Borel with countable sections.

**Lemma 2.1.** Let `(x, x') ∈ X_1^2 \ Bad` and `u, v ∈ Gamma`. Then only finitely many `(k, k') ∈ Z^2` satisfy

`c_k(x) = u c_{k'}(x') v`. (2.1)

*Proof.* Suppose infinitely many pairs satisfy (2.1).

*Both coordinates are unbounded.* If infinitely many solutions had `k` in a finite set `K`, then infinitely many `k'`
would satisfy `c_{k'}(x') ∈ u^{-1} c_K(x) v^{-1}`, a finite set. This contradicts `|c_{k'}(x')| -> ∞` in (R). The same
holds with the roles swapped.

*Pass to the boundary.* So there are solutions `(k_n, k'_n)` with `|k_n|, |k'_n| -> ∞` and with the signs of `k_n`
and of `k'_n` fixed. Invert (2.1): `c_{k_n}(x)^{-1} = v^{-1} c_{k'_n}(x')^{-1} u^{-1}`. By (R), the left side converges
to `rho ∈ {zeta(x), zeta^-(x)}`, the choice depending on the sign of `k_n`. By (R) and (G1), the right side converges
to `v^{-1} rho'` with `rho' ∈ {zeta(x'), zeta^-(x')}`. So `v rho = rho'`, and (MR±) gives `(x, x') ∈ Rel`. This is a
contradiction. `□`

## Step 3. The null set

**Lemma 3.1.** Put `N = ⋃_{h, h' ∈ Gamma} (h x h')(zeta x zeta)(Bad) ⊂ dGamma x dGamma`. Then `N` is universally
measurable, and `(lambda_1 x lambda_2)(N) = 0` for all finite nonatomic Borel measures `lambda_1, lambda_2` on `dGamma`.

*Proof.* `N` is a countable union of Borel images of Borel sets, so it is analytic, and (UM) applies.

Fix `eta`. Let `O_eta = {x ∈ X_1 : eta ∈ Gamma zeta(x)}`. By Lemma 1.1 it is contained in one orbit, so it is
countable. The section `N_eta` is contained in `Gamma zeta(⋃_{x ∈ O_eta} Bad_x)`. This is countable, because each
section `Bad_x` is countable. By Tonelli for the completed product,
`(lambda_1 x lambda_2)(N) = ∫ lambda_2(N_eta) d lambda_1(eta) = 0`. `□`

As in the free-group proofs, no quasi-invariance, ergodicity or invariant measure is used. This is the support-only
step.

## Step 4. Finite joint returns

**Proposition 4.1.** Let `(eta, eta') ∈ (Gamma zeta(X_1))^2 \ N`, and let `H ⊂ Gamma` be finite. Then only finitely many
`g ∈ Gamma` satisfy `g eta ∈ H zeta(X_1)` and `g eta' ∈ H zeta(X_1)`.

*Proof.* Write `eta = h_0 zeta(x)` and `eta' = h'_0 zeta(x')` with `x, x' ∈ X_1`. Since `(eta, eta') ∉ N`, we have
`(x, x') ∉ Bad`.

Let `g` be a joint return, with `g eta = h zeta(y)` and `g eta' = h' zeta(y')`, where `h, h' ∈ H`. Then
`(h^{-1} g h_0) zeta(x) = zeta(y)`, and Lemma 1.2 gives `h^{-1} g h_0 = c_k(x)` for some `k`. In the same way
`h'^{-1} g h'_0 = c_{k'}(x')`. Eliminating `g`,

`c_k(x) = (h^{-1} h') c_{k'}(x') (h'^{-1}_0 h_0)`.

This is (2.1) with `u = h^{-1} h'` and `v = h'^{-1}_0 h_0`. By Lemma 2.1, for each of the finitely many pairs
`(h, h') ∈ H^2`, only finitely many `(k, k')` occur. And `g = h c_k(x) h_0^{-1}` is determined by `(h, k)`. `□`

## Step 5. Proof of Theorem 1

This is the argument of §3 of `fpbs-zero-entropy-ray-codes-are-support-rigid-proof`, with Proposition 4.1 in place of
its Theorem 1. Modify `xi` on a null set to make it Borel.
- **A cover.** Choose finite-measure sets `E_n` increasing to `Z`, and finite sets `H_n` increasing to `Gamma`. The
  pushforward `xi_*(mu_Z|_{E_n})` is nonatomic and carried by `Gamma zeta(X_0)`, hence by `Gamma zeta(X_1)`. So the
  sets `E'_n = E_n ∩ xi^{-1}(H_n zeta(X_1))` are measurable (UM) and increase to a conull set.
- **Pairs avoid `N`.** Put `lambda_n = xi_*(mu_Z|_{E'_n})`, which is finite and nonatomic. Then
  `(xi x xi)_*(mu_Z|_{E'_n} x mu_Z|_{E'_n}) = lambda_n x lambda_n`. By Lemma 3.1, a.e. `(z, z') ∈ E'_n x E'_n` has
  `(xi z, xi z') ∉ N`.
- **Finite returns.** If `g(z, z') ∈ E'_n x E'_n`, then `g xi(z), g xi(z') ∈ H_n zeta(X_1)`. By Proposition 4.1, a.e.
  pair in `E'_n x E'_n` has only finitely many such `g`.
- **Dissipativity.** Let `C` be the conservative part of `Z x Z`. By (Rec), a.e. point of `C ∩ (E'_n x E'_n)` returns
  to that set infinitely often. So `C ∩ (E'_n x E'_n)` is null for every `n`, and `C` is null.
- **Consequences.**
  - PDR requires a conservative piece of the diagonal (Theorem A of `fpbs-dini-boundary-class-diagonal-dissipative`),
    and there is none.
  - For `nu_rho`: `nu_rho` is carried by `Gamma zeta(X_0)` and is nonatomic when `zeta_* rho` is. Every imp action over
    `[nu_rho]` has `xi_*(mu_Z|_E) << nu_rho`, and the Maharam extension is one of them. So the hypotheses hold. `□`

## Step 6. Calibration: the `F_2` odometer code

Let `X_0` be the set of Theorem 1 of `fpbs-odometer-killing-class-dies-by-support-rigidity`, and put
`X = X_0 ∩ (-X_0)`. It is conull and `T`-invariant, and `x ∈ X` implies `-x-1 ∈ X`.
- **(R).** The words are reduced and alternating, so `|c_k(x)| = |k|`. For `k > 0`, `c_k(x)^{-1}` is the prefix of
  `zeta(x)`. For `k < 0`, `c_k(x)^{-1} = F(x)^{-1} ... F(x+k+1)^{-1} = F(-x) F(-x+1) ...`, by (S). This is a prefix of
  `zeta(-x-1)`, so `zeta^-(x) = zeta(-x-1)`.
- **(MR)** is Corollary 5.1(2) of that proof.
- **(MR±).** Apply (MR) to the points `x` or `-x-1`, and `x'` or `-x'-1`, all in `X`. This gives `Rel = {x' ∈ ±x + Z}`,
  which has countable sections.

Theorem 1 then gives Corollary 2 of that claim again. The route is different: it avoids the `Z/2` embedding and the
exponent bookkeeping, and uses only (MR).
