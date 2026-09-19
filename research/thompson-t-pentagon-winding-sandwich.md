---
rg: 2
id: thompson-t-pentagon-winding-sandwich
kind: claim
title: The pentagon winding of near-relator pairs is sandwiched — T not MF implies it vanishes near the relators, and its vanishing implies T is not quasidiagonal; the r_1-winding vanishes identically and the Euler class pairs to 1
distinct_from:
  thompson-v-k-shadow-cannot-detect-mf: that kills K-theoretic and homological lanes for V, which is rationally acyclic; this shows the lane is alive for T, whose H_2 contains a class of Euler number 1, and it names the single live invariant.
  dadarlat-matricial-stability-obstruction: that is Dadarlat's Corollary 3.3 (a QD group with a gamma-element and H_2(Q) != 0 is not matricially stable); this applies his Theorem 3.2 to one explicit class of T and turns it into a statement about exact pairs of finite-order unitaries.
  dadarlat-linear-groups-have-nonzero-h2-windings: that is the imported theorem, class by class, for linear groups; this is its use for the non-linear group T under the hypothesis that T is QD, and for the linear triangle group Delta(4,3,5).
  lifted-thompson-t-is-not-mf: that is the non-MF statement for the central extension T-bar; this uses T-bar only to compute the Euler pairing e(x_0) = 1.
  thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes: that is the uniform-gap criterion; this extracts from it a necessary, integer-valued condition that the direct-sum trick shows is not sufficient.
artifacts:
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/euler_pairing.py
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/out_euler_pairing.json
  - experiments/thompson-t-opnorm-defect-gap-2026-09-17/verify_ls.py
---

**ESTABLISHED** by `thompson-t-pentagon-winding-sandwich-proof` (written proof, with an exact computation
of the Euler pairing).

## Setting

The notation is that of `thompson-t-mf-iff-opnorm-z4-z3-defect-gap-vanishes`: exact pairs `(A,B)` with
`A^4 = B^3 = 1`, and the relators `r_1 = [X, JXJ]`, `r_2 = [X, WXW^(-1)]` and `r_P = (ba)^5`, where
`X = bab`, `J = a^2` and `W = a^2 b^2 a^2`.

For a unitary `U` with `||U - 1|| < 2`, put `kappa(U) = (1/2 pi i) Tr log U`, using the principal
branch. This is Dadarlat's `kappa` (Lemma 2.1 of arXiv:2111.05755, quoted in
`dadarlat-linear-groups-have-nonzero-h2-windings`).

The **pentagon winding** of a pair is `kappa_P(A,B) = kappa((BA)^5)`.

## Statement

1. **(Quantisation.)**
   - If `||(BA)^5 - 1|| < 2`, then `kappa_P` lies in `(1/12) Z`, because `det((BA)^5)` lies in `mu_12`.
   - If `||r_2(A,B) - 1|| < 2`, then `kappa(r_2(A,B))` lies in `Z`.
2. **(The r_1-winding vanishes identically.)** For every exact pair with `||r_1(A,B) - 1|| < 2`,
   `kappa(r_1(A,B)) = 0`.
3. **(A class of Euler number 1.)** Let `F = F(a,b)` and `N = ker(F -> T)`. Put
   `c_0 = r_P^12 (a^4)^(-15) (b^3)^(-20)`. Then `c_0` lies in `N` and in `[F,F]`, so it defines
   `x_0` in `H_2(T; Z)` by Hopf. The Euler pairing of the central extension
   `Z -> T-bar -> T` (lifts to the line) gives `e(x_0) = 1`. So `x_0` is non-torsion. For every exact
   pair, `c_0(A,B) = (BA)^60`.
4. **(Sandwich.)** Consider

   > **(PW)** There is `delta > 0` such that every delta-pair has `kappa_P(A,B) = 0`.

   Then

   ```text
   T not MF  ==>  (PW)  ==>  T is not a quasidiagonal group (in Dadarlat's sense).
   ```

   Equivalently, if some sequence of exact pairs has `D(A_n,B_n) -> 0` and `kappa_P(A_n,B_n) != 0`, then
   `T` is MF. If `T` is a quasidiagonal group, such a sequence exists.
5. **(The pentagon alone does not force (PW).)** The triangle group
   `Delta(4,3,5) = <a, b | a^4, b^3, (ba)^5>` has exact pairs with `||(B_n A_n)^5 - 1|| -> 0` and
   `kappa_P != 0`. So any proof of (PW) must use the smallness of `r_1` or `r_2`. By (2), `r_1` carries no
   winding of its own.
6. **(Windings cancel.)** Suppose `(A,B)` is a delta-pair with `kappa_P = k`. Then
   `(A,B) (+) (A-bar, B-bar)` is a delta-pair with `kappa_P = 0`. So the winding invariant cannot certify
   the uniform gap by itself. Witnesses to MF-ness with zero winding are invisible to it, and (PW) is a
   strictly one-sided test.

## Why it matters

- **The obstruction lane is open for T.** For `V`, every K-theoretic invariant of this kind vanishes
  rationally (`thompson-v-k-shadow-cannot-detect-mf`). For `T` there is exactly one live integer
  invariant on near-relator pairs, `12 kappa_P`, and it detects the Euler class.
- **A falsifiable intermediate target.** (PW) is `thompson-t-pentagon-winding-rigidity`.
  - Refuting (PW) proves that `T` is MF, and so kills `thompson-t-has-full-mf-radical`. It also kills
    every route to the flagship that goes through `T`.
  - Proving (PW) proves that `T` is not quasidiagonal. That is a non-approximation result for a finitely
    presented simple group with the Haagerup property.
- **Numerics.** A numerical search for (PW) is a search for low-defect pairs with nonzero integer
  `12 kappa_P`. Because the target is integer-valued, it is checkable to machine precision.
