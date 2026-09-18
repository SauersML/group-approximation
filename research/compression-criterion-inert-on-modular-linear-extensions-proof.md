---
rg: 2
id: compression-criterion-inert-on-modular-linear-extensions-proof
kind: route
title: Zariski rigidity makes the compressed factor central in the symbol image, the eigenspace determinant makes it torsion, and the locally finite kernel lifts finiteness
target: compression-criterion-inert-on-modular-linear-extensions
requires:
  - jacobson-elementary-subgroups-are-locally-finite-by-linear
---

Notation as in the target. Only standard facts are used beyond the prerequisite: Zariski closures of subgroups
are algebraic groups; an algebraic group has finitely many components; the Jordan decomposition `c = c_s c_u` in
`GL_d(kbar)`, with `c_s, c_u` polynomials in `c`; and a group with property (T) has finite abelianization.

## Step 1. The compressed image is Zariski dense in the same closure

Let `H` be the Zariski closure of `rho(Gamma)` in `GL_d(kbar)`, and put `s = rho(t)`. Conjugation by `s` is an
automorphism of the variety `GL_d(kbar)`, so the closure of `rho(t Gamma t^-1) = s rho(Gamma) s^-1` is `s H s^-1`.
From `t Gamma t^-1 <= Gamma` we get `s H s^-1 <= H`. Both are closed subgroups with the same dimension and the same
number of irreducible components. A closed irreducible subset of an irreducible variety of the same dimension is
the whole component, so `s H^0 s^-1 = H^0`, and counting components gives `s H s^-1 = H`. Hence
`rho(t Gamma t^-1)` is Zariski dense in `H`.

## Step 2. The factor is central in the symbol image

Let `C <= Gamma` be finitely generated with `[t Gamma t^-1, C] = 1`, and put `Lambda = rho(Gamma)` and
`C_bar = rho(C) <= Lambda`. Each `c in C_bar` commutes with `rho(t Gamma t^-1)`. The centralizer of `c` is Zariski
closed, so by Step 1 it contains `H`, hence `Lambda`. So `C_bar <= Z(Lambda)`, a finitely generated abelian group.

## Step 3. Lemma: central factors are finite in characteristic p

**Lemma.** Let `Lambda <= GL_d(k)`, `char k = p > 0`, with `Lambda^ab` torsion. Every finitely generated
`C_bar <= Z(Lambda)` is finite.

*Proof.* `C_bar / (C_bar cap [Lambda, Lambda])` embeds in `Lambda^ab`. It is finitely generated abelian and
torsion, hence finite. So `C_0 = C_bar cap [Lambda, Lambda]` has finite index in `C_bar` and is finitely generated
abelian.

Take `c in C_0` and its Jordan decomposition `c = c_s c_u` over `kbar`. Let `V_lambda` be an eigenspace of `c_s`,
which is the generalized `lambda`-eigenspace of `c`. Every `a in Lambda` commutes with `c`, so it preserves
`V_lambda`. `c` is a product of commutators `[a, b]` with `a, b in Lambda`, and each such commutator has
determinant `1` on `V_lambda`. So `det(c|V_lambda) = 1`. On the other hand `c|V_lambda = lambda * (unipotent)`,
so `det(c|V_lambda) = lambda^(dim V_lambda)`. Hence `lambda^(d!) = 1` for every eigenvalue, and `c_s^(d!) = 1`.
In characteristic `p`, `(c_u - 1)^d = 0` gives `c_u^(p^m) = 1` once `p^m >= d`. The two parts commute, so
`c^(d! p^m) = 1`.

So `C_0` is finitely generated abelian of bounded exponent, hence finite, and `C_bar` is finite. ∎

`Gamma^ab` is torsion by hypothesis, so `Lambda^ab` is torsion and the Lemma applies. So `rho(C)` is finite.

## Step 4. Lifting through the locally finite kernel

`C cap ker rho` has finite index in `C`, so it is finitely generated. It lies in the locally finite group
`ker rho`, so it is finite. Hence `C` is finite. This proves MLE1. MLE2 and MLE3 are the substitutions stated in
the target. ∎

## Step 5. The Jacobson class is in MLE

Let `Q = 1 - ST` and `e_ij = S^i Q T^j`. From `TS = 1` we get `TQ = 0` and `QS = 0`, so
`e_ij e_kl = delta_jk e_il`. The two-sided ideal `I = (Q)` is spanned by the `e_ij`, since
`S^a T^b Q S^c T^d` vanishes unless `b = c = 0`. Also `J_F / I = F[x, x^-1]`, with `S -> x` and `T -> x^-1`.

Let `rho : GL_n(J_F) -> GL_n(F[x, x^-1]) <= GL_n(F(x))` be reduction mod `I`. Its kernel is
`K = {g : g - 1 in M_n(I)}`. Take finitely many `g_1, ..., g_r in K`. Choose `m` so that all entries of all
`g_i - 1` and `g_i^-1 - 1` lie in `I_m = span{e_ab : a, b < m}`, and put `E = diag(e, ..., e)` with
`e = sum_(a<m) e_aa`. If `g = 1 + A` with `A = E A E` and `g^-1 = 1 + B`, then `(1 + A) B (1 - E) = -A(1 - E) = 0`.
So `B(1 - E) = 0`, and likewise `(1 - E) B = 0`. Hence `g -> E g E` identifies the group `<g_1, ..., g_r>` with a
subgroup of the unit group of `E M_n(J_F) E = M_(nm)(F)`, which is finite. So `K` is locally finite, and every
subgroup of `GL_n(J_F)` is in MLE. For `EL_n(J_F)` this is part 1 of the prerequisite
`jacobson-elementary-subgroups-are-locally-finite-by-linear`. ∎

## Closing remark: what the theorem does not reach (not part of the implication)

The rigid-defect criterion `DD(sofic)` is not killed by MLE1. Take `m >= 3` and `Gamma = EL_m(J_F) + 1` in
`GL_(2m)(J_F)`, and `u = [[S, Q], [0, T]]` with `u^-1 = [[T, 0], [Q, S]]`. Then
`u diag(g, 1) u^-1 = diag(S g T + Q, 1)`, so `u` compresses `Gamma`. The element `z = diag(1, 1 + e_12)` centralizes
`Gamma`, and `u z u^-1 = diag(1 + Q e_12, 1 + e_12)`. For `gamma = diag(1 + T e_23, 1)`,

```text
[1 + Q e_12, 1 + T e_23] = 1 + QT e_13 != 1 ,
```

so the defect is nontrivial, and it lies in `GL_(2m)(J_F, I)`. It fires only if some Kazhdan subgroup generated by
compressors of `Gamma` contains such a `u`. Here `rho(<Gamma, u>)` is block diagonal, the top-block determinant is
a character of the block-diagonal group, it is trivial on `rho(Gamma)`, and it sends `rho(u) = diag(x I_m, x^-1 I_m)`
to `x^m`, which has infinite order. So `<Gamma, u>` has infinite abelianization and is not Kazhdan. A Fredholm-index homomorphism on the compressor hull that is nonzero on every strict compressor
would kill `DD(sofic)` on the whole Jacobson class. That is recorded as open, not claimed.
