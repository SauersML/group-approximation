---
rg: 2
id: deligne-sector-determinant-congruence-proof
kind: route
title: Collapse a commutator filling in the integral cover, take determinants, and extend the central phase character through the free abelianization
target: deligne-sector-determinants-see-only-dimension-mod-three
requires: [deligne-triple-cover-finite-residual-is-center]
---

Notation is that of the target.  `pi : F -> Gamma` is the quotient map.
`E_3 = Z/3 x_(b mod 3) Gamma`, with central generator `z = (1, e)`.

## Step 0: (DC0)

Let `j : F -> E_3` send `s` to `(0, s)`.  For `r in R`, `j(r) = (k_r mod 3, e)`.
So `phi(r) = k_r mod 3` is a homomorphism `R -> Z/3`.

Suppose, for contradiction, that `phi` vanishes on `R' = R cap [F,F]`.

1. **Extend `phi` to `F`.**  Then `phi` factors through
   `R/R' = R[F,F]/[F,F]`, which is a subgroup of `F/[F,F] = Z^S`.
   View `Z/3` inside `Q/Z`.  Since `Q/Z` is injective, the induced map
   extends to a homomorphism `psi : Z^S -> Q/Z`.  Its image is a finitely
   generated torsion group, hence finite, say `Z/N`.
2. **Descend to `E_3`.**  Define `sigma : F -> Gamma x Z/N` by
   `sigma(w) = (pi(w), psi(w))`.  Let `K = ker(j)`.  If `w in K`, then `w`
   lies in `R` and `phi(w) = 0`, so `sigma(w) = (e, 0)`.  Hence `sigma`
   descends to a homomorphism `sigma' : j(F) -> Gamma x Z/N`.
3. **Two cases for `j(F)`.**  `j(F)` maps onto `Gamma`, so `j(F) cap <z>`
   is `1` or `<z>`.
   - If it is `1`, then `E_3 = j(F) x <z>` with `j(F)` isomorphic to
     `Gamma`, so `E_3` is residually finite.
   - If it is `<z>`, then `j(F) = E_3`.  Here `z = j(r)` for some `r in R`
     with `phi(r) != 0`, and `sigma'(z) = (e, psi(r)) != 0`.  So `z` has
     nontrivial image in the residually finite group `Gamma x Z/N`.

In both cases `z` is not in the finite residual of `E_3`.  This contradicts
`deligne-triple-cover-finite-residual-is-center`.  Hence some `r in R'`
has `k_r` not divisible by three.

## Step 1: word collapse, used in (DC1) and (DC3)

1. **The extended map.**  Define `U~(n, g) = e(theta n) U(g)` on the
   elements `(n, g)` of `Gamma~` used below.  Multiplication in `Gamma~`
   is `(n,g)(m,h) = (n + m + b(g,h), gh)`.  So
   `||U~(p) U~(q) - U~(pq)|| = ||U(g)U(h) - c_theta(g,h)U(gh)|| <= delta`
   on window pairs.
2. **Inverses.**  `U(e) = I` because `b` is normalized.  So
   `U~(p) U~(p^-1)` is within `delta` of `I`.  Hence
   `||U~(p)^* - U~(p^-1)|| <= delta`.
3. **The window.**  Write `r = w_1 ... w_L` with letters in `S^(+-1)`.
   Let `W_r` consist of:
   - the pairs `(g, g^-1)` for `g = pi(s)` with `s^-1` occurring in `r`;
   - the pairs `(pi(w_1 ... w_(i-1)), pi(w_i))` for `2 <= i <= L`.
4. **Collapse.**  Let `V_r` be the word evaluated through
   `s -> U(pi(s))`, `s^-1 -> U(pi(s))^*`.  For unitaries,
   `||A_1...A_L - B_1...B_L|| <= sum ||A_i - B_i||`.
   - Replacing each `U(pi(s))^*` by `U~(iota(s)^-1)` costs at most
     `delta` per inverse letter.
   - Collapsing the product of `L` factors `U~(iota(w_i))` costs at most
     `(L - 1) delta`.
   - In `Gamma~` the collapsed element is `iota(r) = (k_r, e)`, and
     `U~(k_r, e) = e(theta k_r) I`.

   Therefore

   ```text
   ||V_r - e(theta k_r) I|| <= L_r delta,   L_r = 2L - 1.       (W)
   ```

## Step 2: determinants give (DC1) and (DC3)

1. **Eigenvalue bound.**  Write the eigenvalues of the unitary
   `e(-theta k_r) V_r` as `e(phi_i)` with `|phi_i| <= 1/2`.  By (W),
   `|e(phi_i) - 1| <= L_r delta`.  Also
   `|e(phi) - 1| = 2 sin(pi |phi|) >= 4 |phi|` for `|phi| <= 1/2`.
   So `|phi_i| <= L_r delta / 4`.
2. **Integrality.**  `V_r` is the image of `r` under the homomorphism
   `F -> U(d)` determined on generators, and `r in [F,F]`.  So
   `det V_r = 1`.  Hence `e(d theta k_r + sum_i phi_i) = 1`, that is,
   `d theta k_r + sum_i phi_i` lies in `Z`.
3. **Conclusion for (DC1).**  Since `|sum_i phi_i| <= d L_r delta / 4`,
   (DC1) follows.  At `theta = 1/3` or `2/3` with `3` not dividing
   `d k_r`, the left side of (DC1) is at least `1/3`, which gives the
   stated lower bound.
4. **Conclusion for (DC3).**
   `(1/2 pi i) tr_d Log(e(-theta k_r) V_r) = (1/d) sum_i phi_i`.  So
   `tau_r(U) = (d theta k_r + sum_i phi_i)/d` lies in `(1/d) Z` and is
   within `L_r delta / 4` of `theta k_r`.  For `d_n -> infinity`, the
   nearest integers `m_n` to `d_n theta k_r` satisfy
   `|m_n/d_n - theta k_r| <= 1/(2 d_n) -> 0`.
5. **The corona.**  For a projection `p = (p_n)` in `Q`,
   `tau_omega(p) = lim_omega rank(p_n)/d_n`.  When `d_n -> infinity` along
   `omega`, this takes every value in `[0, 1]`.  So `tau_omega(K_0(Q)) = R`.

## Step 3: (DC2)

1. **(i) implies (ii).**  A homomorphism `chi : F -> T` kills `[F,F]`.
   So `e(d theta k_r) = chi(r) = 1` for `r in R'`.
2. **(ii) implies (i).**  The map `r -> e(d theta k_r)` is a homomorphism
   `R -> T`, and by (ii) it kills `R'`.  So it factors through the subgroup
   `R/R'` of `Z^S`.  Since `T` is divisible, it extends to `Z^S`.
   Composing with `F -> Z^S` gives `chi`.
3. **At one third.**  At `theta = 1/3` or `2/3`, condition (ii) holds
   when `3 | d`.  When `3` does not divide `d`, the word `r` of (DC0)
   violates it.
4. **The diagonal tuple.**  For the tuple `U(s) = diag(chi(s), 1, ..., 1)`,
   the induced homomorphism `F -> U(d)` has determinant `chi`.

## Step 4: the class kill

1. **Unnormalized members.**  An unnormalized linear-characteristic
   argument obtains its contradiction from the integrality of determinants
   of words.
   - By Step 3, the exact constraints are simultaneously satisfiable
     whenever `3 | d`.
   - By Step 2, the approximate constraints are implied by the exact ones
     up to `d L_r delta / 4`.
   - Replacing `U_n` by `U_n tensor I_3` keeps every defect and multiplies
     the dimension by three.
   - So no such argument excludes a model sequence.
2. **Normalized members.**  A normalized argument compares values in
   `R / tau(K_0)`, which is zero in the corona by Step 2.
3. **What remains.**  The surviving inequality `d delta >= 4/(3 L_r)` for
   `3` not dividing `d` tends to zero with `1/d`.
