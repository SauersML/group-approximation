---
rg: 2
id: integral-leavitt-unit-group-contains-q-proof
kind: route
title: Integer matrices on cone configurations refine by Kronecker products, so block rotations give compatible roots of a transvection
target: integral-leavitt-unit-group-contains-q
requires: []
---

Notation as in the target claim. For words `u, w`: `y_u x_w = 0` if `u, w` are
incomparable, and `y_u x_{u w'} = x_{w'}`. For any complete prefix code `(w_j)`,
`sum_j x_{w_j} y_{w_j} = 1`.

**Step 1: matrices on cone configurations.** Let `Gamma = (g_1, ..., g_r)` be
pairwise incomparable words, `e_Gamma = sum_a x_{g_a} y_{g_a}` and
`E_ab = x_{g_a} y_{g_b}`. Then `E_ab E_cd = delta_bc E_ad`, and
`E_11 != 0` (since `y_{g_1} E_11 x_{g_1} = 1`). The map `M -> sum M_ab E_ab` is
therefore a ring homomorphism `M_r(Z) -> e_Gamma L e_Gamma`. It is injective:
- `E_1a (sum M_cd E_cd) E_b1 = M_ab E_11`;
- `L` is a free `Z`-module (Leavitt normal form), so it is torsion-free;
- hence `M_ab E_11 = 0` forces `M_ab = 0`.

Put `u(Gamma, M) = 1 - e_Gamma + sum_{a,b} M_ab E_ab`. Then `M -> u(Gamma, M)` is an
injective homomorphism `GL_r(Z) -> U(L)`.

**Step 2: refinement.** Let `W = (w_1, ..., w_s)` be a complete prefix code, and
let `Gamma*W` be the tuple of words `g_a w_j` indexed by `(j, a)`, with `j` the outer
index. Then `x_{g_a} y_{g_b} = sum_j x_{g_a w_j} y_{g_b w_j}`, and
`e_Gamma = e_{Gamma*W}`. Hence `u(Gamma, M) = u(Gamma*W, I_s (x) M)`, where
`I_s (x) M` is block-diagonal with `s` copies of `M`.

**Step 3: V acts on configurations.** Let `g in V` map the cones of the complete
prefix code `(e_i)` canonically onto those of `(d_i)`. If every `g_a` extends some
`e_i` (say `g_a = e_i w`), write `g(g_a) = d_i w`. Then
`v_g x_{g_a} = x_{g(g_a)}` and `y_{g_a} v_g^{-1} = y_{g(g_a)}`, so
`v_g u(Gamma, M) v_g^{-1} = u(g(Gamma), M)`.

Now let `Gamma`, `Gamma'` be two `r`-tuples of pairwise incomparable words, each
with a nonempty complement (`e_Gamma != 1`). Then some `g in V` maps each `g_a`
canonically onto `g'_a`: the complements are finite unions of cones, which can be
split until both have the same number of cones. So `u(Gamma, M)` and
`u(Gamma', M)` are conjugate in `V`. Also `u(Gamma, P)` lies in `V` for every
permutation matrix `P`: it is the permutation unit of the element permuting the
cones of `Gamma` canonically and fixing the complement.

**Step 4: the roots.**
- *Matrices.* Put `T_1 = [[1,0],[1,1]]` and `r_1 = 2`. For `k >= 1` put
  `r_{k+1} = (k+1) r_k`, let `P` be the cyclic `(k+1) x (k+1)` permutation matrix,
  let `D = diag(T_k, I, ..., I)` (`k+1` blocks of size `r_k`), and put
  `T_{k+1} = (P (x) I_{r_k}) D`.
- *The power identity.* `P^i D P^{-i}` is block-diagonal with `T_k` in block `i`
  and identity elsewhere. These commute, and `P^{k+1} = I`, so
  `T_{k+1}^{k+1} = prod_{i=1}^{k+1} (P^i D P^{-i}) P^{k+1} = I_{k+1} (x) T_k`.
- *Configurations.* Put `Gamma_1 = (00, 01)` and `Gamma_{k+1} = Gamma_k * W_{k+1}`,
  where `W_{k+1} = (0, 10, 110, ..., 1^{k-1}0, 1^k)` is a complete prefix code of
  size `k+1`. Every word begins with `0`, so the complement always contains the
  cone `1` and is nonempty.
- *The elements.* Put `a_k = u(Gamma_k, T_k)`. Then `a_1 = t`, and by Steps 1–2
  `a_{k+1}^{k+1} = u(Gamma_{k+1}, I_{k+1} (x) T_k) = u(Gamma_k, T_k) = a_k`.

**Step 5: injectivity.** Since `a_{k+1}^{k+1} = a_k`, the rule `m/k! -> a_k^m` is a
well-defined homomorphism `phi: Q -> U(L)`: every rational is `m/k!` for large `k`,
and `a_{k'}^{m k'!/k!} = a_k^m`. Its kernel `H` meets `Z` trivially. Indeed
`t^m = 1 + m x_{01} y_{00}`, because `(x_{01} y_{00})^2 = 0`, and this differs from
`1` for `m != 0` since `x_{01} y_{00} != 0` and `L` is torsion-free. A nonzero
`a/b in H` would give `a = b (a/b) in H ∩ Z`, a contradiction. So `H = 0` and `phi`
is injective.

**Step 6: finite generation.** `a_{k+1} = u(Gamma_{k+1}, P (x) I) u(Gamma_{k+1}, D)`.
- The first factor lies in `V` by Step 3.
- The second is `u(Gamma^0_{k+1}, T_k)`, where `Gamma^0_{k+1}` is the sub-tuple
  of words `g_a w_1` (`w_1 = 0`); off that sub-tuple it is the identity.
- Both `Gamma^0_{k+1}` and `Gamma_k` have nonempty complements, so by Step 3 the
  second factor is `V`-conjugate to `a_k`.

By induction every `a_k` lies in `<V, t>`, and `V` is finitely generated.

**Step 7: coefficients.** `L_A(1,2) = A (x)_Z L`. `L` is a free `Z`-module, so
`L -> L_A(1,2)` is injective when `Z -> A` is, that is, when `A` has characteristic
0. It maps `U(L)` into `U(L_A(1,2))`.

**The consequences stated in the claim.**
- *`GL_r(Z)`.* `<V, t>` contains `u(Gamma, e_ab(1))` for every proper `Gamma`,
  since this is `V`-conjugate to `t` by Step 3. With the permutation units, it
  therefore contains `u(Gamma, GL_r(Z))`.
- *Distortion.* `u(Gamma, SL_3(Z))` contains `Z^2 x| SL_2(Z)`, in which elementary
  unipotents are exponentially distorted. Distortion passes to the finitely
  generated overgroup `<V, t>`.
- *Non-conjugacy of `t` and `t^p`.* On `M = LC(C, Z)`, `L` acts faithfully: it acts
  faithfully on `LC(C, Q)`, since `L_Q(1,2)` is simple, and `LC(C, Z)` is
  `L`-invariant. There `x_{01} y_{00}` maps `M` onto the functions supported on the
  cone `01`, a direct summand. So `M / (t - 1)M` is torsion-free, while
  `M / (t^p - 1)M` contains `(Z/p)`-torsion. Conjugate automorphisms of `M` have
  isomorphic cokernels of `(. - 1)`. ∎
