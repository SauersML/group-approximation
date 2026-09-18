---
rg: 2
id: deligne-flexible-subgroup-exact-sector-models-proof
kind: route
title: Split the cover virtually, compress regular representations of finite quotients to the omega-part, and read off traces
target: deligne-flexible-subgroup-restrictions-carry-exact-sector-models
requires: [deligne-triple-cover-finite-residual-is-center, deligne-maslov-sector-traces-are-central-regular, deligne-multiplier-trivial-on-sl2xsl2-and-parabolics]
---

Notation of the target.


**(F1).**
- Since `Gamma` is linear over `Z`, every `A <= Gamma` is residually finite. Hence `Res_fin(A~) <= <z>`, and so
  `Res_fin(A~)` is `1` or `C_3`.
- Suppose `N <= A~` has finite index and `N cap <z> = 1`. Then `N` maps isomorphically onto a finite-index
  `A' <= A`. The inverse of this map is a homomorphic section of `A'~ -> A'`, so `alpha|_(A')=0`.
- Conversely, suppose `alpha|_(A')=0`. The central extension `A'~` splits, hence `A'~ = A' x C_3`, which is
  residually finite. A group with a residually finite finite-index subgroup is residually finite: intersect the
  conjugates of the finite-index subgroups separating points. So `A~` is residually finite, and since `z != 1`, `z`
  survives in a finite quotient.
- Finally, if `z` survives in a finite quotient then `z notin Res_fin(A~)`, so `Res_fin(A~)=1`.

**(F2).**
- Let `A` be flexible. By (F1) there is a finite-index normal `N_0 <= A~` with `z notin N_0`, so `N_0 cap <z>=1`.
- `A~` is countable and residually finite. Enumerate `A~ \ {1} = {g_1, g_2, ...}` and choose finite-index normal
  `M_i` with `g_i notin M_i`. Put `N_k = N_0 cap M_1 cap ... cap M_k` and `Q_k = A~/N_k`. The image of `z` is central
  of order 3.
- On `l^2(Q_k)` put `p_k = (1/3) sum_j omega^(-j) lambda(z^j)`. This is a central projection of rank `|Q_k|/3` with
  `lambda(z) p_k = omega p_k`. Let `rho_k` be `lambda` compressed to `p_k l^2(Q_k)`, so `D_k = |Q_k|/3`.
- For `g in A~`, `tr rho_k(g) = (3/|Q_k|) Tr(lambda(g) p_k) = sum_j omega^(-j) [g z^j in N_k]`.
  - If `g = z^i`, only `j = -i` contributes, giving `omega^i`.
  - If `g notin <z>`, the three elements `g, gz, gz^2` are nontrivial. Since the `N_k` decrease with trivial
    intersection, none of them lies in `N_k` for `k` large, so the trace is `0`.
- For several flexible `A_1,...,A_r`, replace `rho^(i)_k` by `rho^(i)_k (x) 1` on `C^(D^(1)_k ... D^(r)_k)`. This
  changes neither the normalized traces nor exactness.

**(F3).**
- **Finite `A`.** `A~` is finite.
- **Virtually free `A`.** A free finite-index `F` has `H^2(F;Z/3)=0`.
- **Virtually polycyclic `A`.** Take a polycyclic finite-index `P`. Then `P~` is an extension of the cyclic group
  `C_3` by `P`, hence polycyclic, so `A~` is virtually polycyclic. Virtually polycyclic groups are residually finite
  (Hirsch; recalled, not re-read). Now apply (F1).
  - For an amenable `A <= GL_4(Z)`: by the Tits alternative `A` is virtually solvable, and solvable subgroups of
    `GL_n(Z)` are polycyclic (Mal'cev). Both are recalled, not re-read.
- **Virtually a closed orientable surface group.** Let `S` have finite index in `A`, with genus `g >= 1`.
  - `H_1(S) = Z^(2g)` surjects onto `Z/3`, so `S` has an index-3 subgroup `S'`.
  - For `x in H^2(S;Z/3)`, `<res x, [S']> = <x, p_*[S']> = 3 <x, [S]> = 0`.
  - `H^2(S';Z/3) = Z/3` is detected by evaluation on `[S']`, so `alpha|_(S') = 0`.
  - The non-orientable case passes to an orientable finite-index subgroup first.
- **`B x C` with `B` and `C` virtually free.**
  - Choose free finite-index `B'` and `C'`. `B' x C'` is of finite type over `F_3` (a product of two graphs), so
    Kunneth gives `H^2(B' x C'; F_3) = H^1(B') (x) H^1(C')`.
  - Write `alpha|_(B' x C') = sum_i a_i x b_i`. On `B'' x C''` with `B'' = cap_i ker a_i` and `C'' = cap_i ker b_i`
    (finite index, since `H^1` is finite), every `a_i` and `b_i` restricts to `0`.
  - By naturality of the cross product, `alpha|_(B'' x C'') = 0`.

**(F4).**
- The model `(rho_k)` of (F2) is an exact, hence operator-norm asymptotic, representation of `A~` with
  `rho_k(z) = omega` and trace limit `tau_omega`. The same facts hold for the restriction of any sector model.
- Any statement deduced about such sequences from those facts, together with finite-dimensionality, therefore holds
  for `(rho_k)`, and so it is satisfiable.
- By the common-dimension clause of (F2), the same holds for a finite family of flexible subgroups whose data are
  used separately.
- Data that are used jointly, meaning relations mixing `A_1, ..., A_r`, give restriction data for the subgroup they
  generate. That subgroup must be rigid, or else (F2) applies to it.

**Addendum (maximal parabolics).**
- Let `H` be `SL_2(Z) x SL_2(Z)`, the Siegel parabolic or the Klingen parabolic.
- By `deligne-multiplier-trivial-on-sl2xsl2-and-parabolics` there is a homomorphism `phi : H~ -> T` with
  `phi(z)=omega`.
- The image `phi(H~)` is a finitely generated abelian group containing the torsion element `omega`. So some finite
  quotient of it separates `omega` from `1`, and `z` survives in a finite quotient of `H~`.
- By (F1), `H` and all its subgroups are flexible.
