---
rg: 2
id: toms-overlap-window-drops-need-not-coincide-proof
kind: route
title: Joint coprime divisibility over all vertex slices forces one drop; a node carrying the constant bundle of its leaf maxima absorbs a neighbour's overlap, so the drops stagger to depth ceil(N/2); split targets cannot do better, by Part 3 node by node
target: toms-overlap-window-drops-need-not-coincide
requires: [toms-transit-windows-fill-unless-their-ranks-overlap]
---

Notation is as in the target. Fix `z_0 in Z`. On `S x Y x {z_0}` the ancestor classes
`A_nu` vanish, and `L_(nu,+)`, `L_(nu,-)` restrict to `pr_nu^* O(alpha)` and `pr_nu^* O(beta)`
on `Y = prod_nu Y_nu`. Write `u_nu` for the hyperplane class of `Y_nu`. Every copy lies under
its own vertex, so the part of the pushforward outside the `N` node blocks has lines pulled
back from factors outside `Y`. It is therefore a trivial bundle `C^(g')` on each slice
`{s} x Y x {z_0}`, and it is constant in `s`. The node block of `nu` at `s` is
`a_n(x(s)) ⊗ p_(nu,+) ⊕ a_n(x(1-s)) ⊗ p_(nu,-)`, where `p_(nu,±)` is the projection onto
`L_(nu,±)`. Its support has rank `R_nu(s) + R_nu(1-s)`.

**Lemma (comparison over the window).** Let `E_1, ..., E_m` be projections over `Y x Z`, and
let `a_i, b_i in (C(I) ⊗ K)_+` satisfy `rank a_i(s) <= rank b_i(s)` for every `s in I`. Then
`⊕_i a_i ⊗ E_i <~ ⊕_i b_i ⊗ E_i` in `C(I x Y x Z) ⊗ K`.

*Proof.* For an interval, rank determines the Cuntz class:
`Cu(C(I)) ≅ Lsc(I, N ∪ {∞})` (L. Robert, *The Cuntz semigroup of some spaces of dimension at
most two*, C. R. Math. Rep. Acad. Sci. Canada 35 (2013); `dim I = 1` and `H^2(I) = 0`). So
`a_i <~ b_i`. The map `x ↦ (x ∘ pr_I) ⊗ E_i` is a `*`-homomorphism
`C(I) ⊗ K -> C(I x Y x Z) ⊗ K`, so it preserves `<~`. Orthogonal sums preserve `<~`. ∎

The same argument, with `m` summands from several windows, applies to products of windows,
because each factor depends on its own coordinate.

**Part 1.** Suppose that `N D <= min_nu j_nu` and that `rank Q = U` on all of
`S x Y x {z_0}`. As in Step 3 of `toms-transit-windows-fill-unless-overlap-proof`, `Q` has a
continuous support projection there, onto a bundle `V` of rank `U = g' + N D`. The box `S`
is contractible, so all slices `V_s = V|_({s} x Y)` are isomorphic.

The functions `R_nu` are integer valued and bounded, so their maxima are attained. Choose
`s^+ = (s^+_nu)` with `R_nu(s^+_nu) = Pbar_nu` for every `nu`, and `s^-` with
`R_nu(1 - s^-_nu) = Qbar_nu` for every `nu`. At `s^+`, the pushforward on `{s^+} x Y` is Cuntz
equivalent to the projection onto

```text
W^+ = C^(g') ⊕ ⊕_nu ( Pbar_nu O_nu(alpha) ⊕ R_nu(1 - s^+_nu) O_nu(beta) ).
```

For projections, Cuntz subequivalence is Murray-von Neumann subequivalence. So
`V_(s^+) ≅ W^+ ⊕ C^+`, and likewise `V_(s^-) ≅ W^- ⊕ C^-`. In
`H^*(Y) = Z[u_1, ..., u_N] / (u_nu^(j_nu + 1))`, the class `c_i(C^±)` vanishes for
`i > rank C^±` and lies in `H^(2i)`, which is spanned by monomials of total degree `i`.
Represent every class by its polynomial with each exponent at most `j_nu`. Then

```text
c(V) = prod_nu (1 + alpha u_nu)^(Pbar_nu) (1 + beta u_nu)^(R_nu(1 - s^+_nu)) · c(C^+)
     = prod_nu (1 + beta u_nu)^(Qbar_nu) (1 + alpha u_nu)^(R_nu(s^-_nu)) · c(C^-).
```

Both right sides have total degree at most `rank V - g' = N D <= min j_nu`. So no exponent
reaches the truncation. Monomials of total degree `<= min j_nu` are linearly independent in
the quotient ring, so both products are equal in `Q[u_1, ..., u_N]`.

Hence one polynomial `c`, with `c(0) = 1` and `deg c <= N D`, is divisible by
`Pi^+ = prod_nu (1 + alpha u_nu)^(Pbar_nu)` and by `Pi^- = prod_nu (1 + beta u_nu)^(Qbar_nu)`.
The linear polynomials `1 + alpha u_nu` and `1 + beta u_mu` are irreducible and pairwise
non-associate, since `alpha`, `beta` are non-zero and distinct. So `Pi^+` and `Pi^-` are
coprime in the UFD `Q[u_1, ..., u_N]`, and `Pi^+ Pi^-` divides `c`. But

```text
deg Pi^+ Pi^- = sum_nu (Pbar_nu + Qbar_nu) = N D + sum_nu kappa_nu = N D + N  >  N D  >=  deg c,
```

so `c = 0`, which contradicts `c(0) = 1`. Since `rank Q <= U`, it follows that
`rank Q <= U - 1` somewhere. The argument only uses `sum_nu kappa_nu >= 1`. ∎

**Part 2.** There are three node targets over `I_nu x Y_nu x Z`, each of the form
`F_+ ⊗ p_(nu,+) ⊕ F_- ⊗ p_(nu,-)` with `F_± in (C(I_nu) ⊗ K)_+`. By the Lemma, each one
dominates the node block as soon as `rank F_+(s) >= R_nu(s)` and
`rank F_-(s) >= R_nu(1-s)` for every `s`.

- *Bare:* `F_+ = a_n(x(s))`, `F_- = a_n(x(1-s))`. The rank is `D - 1` on the chambers and
  `D - 2` on the walls.
- *Absorbing:* `F_+ = 1_(Pbar)`, `F_- = 1_(Qbar)`. The rank is constantly `Pbar + Qbar = D + 1`.
- *Ramp:* fix `s*` in the interior of `B` and `delta > 0` with `[s* - delta, s* + delta] ⊂ B`.
  Put `h_+(s) = min(1, (s - s*)_+ / delta)` and `h_-(s) = min(1, (s* - s)_+ / delta)`, and
  `F_+ = 1_k ⊕ h_+`, `F_- = 1_(D-1-k) ⊕ h_-`. Then `rank F_+ = k + [s > s*]` and
  `rank F_- = D - 1 - k + [s < s*]`. These dominate `R(s)`, which is `k - 1` on `A` and `w_1`,
  `k` on `B` and `w_2`, and `k + 1` on `C`. They also dominate `R(1-s)`, which is `D - k` on `A`
  and at most `D - 1 - k` from `w_1` on. The rank is `D`, except `D - 1` at `s*`.

For the target take `G` equal to the pushforward outside the nodes, and let `Q` be the direct
sum of `G` and one node target per node, each pulled back from its own window.

- *Even `N`:* pair the nodes as `(2i-1, 2i)`, with node `2i-1` bare and node `2i` absorbing.
- *Odd `N`:* do the same for the first `N - 1` nodes and give the last node the ramp.

The pushforward is dominated componentwise, hence as a sum. The rank at `(s, y, z)` is
`g'` plus the node ranks. Each pair contributes at most `(D - 1) + (D + 1) = 2D`, and at least
`2D - 1`, with the minimum exactly when the bare node sits on a wall. The ramp contributes `D`,
or `D - 1` at `s*`. So `rank Q <= U` everywhere, with equality when every bare node is in a
chamber (and the ramp is off `s*`).

The box is a product, so there is a point where every bare node sits on a wall and the
ramp node sits at `s*`. There `rank Q = U - floor(N/2) - (N mod 2) = U - ceil(N/2)`.
Hence the depth is exactly `ceil(N/2)`. For `N = 2` this is
`Q = G ⊕ psi_1 ⊕ (Pbar_2 L_(2,+) ⊕ Qbar_2 L_(2,-))`, with rank `U - 1` exactly on
`{s_1 in {w_1, w_2}}`. Node 2 never drops. ∎

More generally, the pairing works whenever
`kappa_(2i) <= D - max_(I_(2i-1)) (R + R(1 - .))`. By Part 1 of
`toms-transit-windows-fill-unless-their-ranks-overlap`, this always holds when
`kappa_(2i) = 1`.

**Part 3.** Let `Q = G ⊕ ⊕_nu Q_nu` be split, with `G` of constant rank `g'`. Write
`r_nu(s_nu, y_nu) = rank Q_nu(s_nu, y_nu, z_0)` and `M_nu = max r_nu` over `I_nu x Y_nu`. Each `r_nu`
depends on its own coordinates only. So the maximum and the minimum of
`rank Q = g' + sum_nu r_nu` over the product `S x Y x {z_0}` are `g' + sum M_nu` and
`g' + sum min r_nu`. In particular `sum_nu M_nu <= N D`.

Since `Q_nu` dominates the node block, `r_nu >= D - 1` on the chambers, so `M_nu >= D - 1`.

- If `M_nu <= D`, then `M_nu <= j_nu` and `Pbar_nu + Qbar_nu = D + 1 > M_nu`. Step 3 of
  `toms-transit-windows-fill-unless-overlap-proof`, applied to `Q_nu` on the slice
  `I_nu x Y_nu x {z_0}` with `g_0 = 0` and `r = M_nu`, shows that `r_nu` is not identically `M_nu`.
  So `min r_nu <= M_nu - 1`.
- If `M_nu >= D + 1`, then `min r_nu <= M_nu`.

Let `x` be the number of nodes with `M_nu >= D + 1`. Then
`N D >= sum M_nu >= x (D + 1) + (N - x)(D - 1)`, so `x <= N/2`. The depth is

```text
U - min rank Q  =  N D - sum_nu min r_nu  >=  N D - sum_nu M_nu + (N - x)  >=  N - x  >=  ceil(N/2).  ∎
```

**The token model.** The split model of `token_depth.py` also allows carries between nodes.
Bins `(a_nu, b_nu)` count the lines of node `nu` above the common part. The needs are
`A:(0,2)`, `g_1:(0,1)`, `B:(1,1)`, `g_2:(1,0)` and `C:(2,0)`, and `T = 3N` tokens are
available. There is also a free bin. Depth `d` means a simplicial map into
`{sum floor >= T - d}`. The recorded results are in `results.json`. A SAT answer is a
staggered target built from depth-one transports, which is a genuine upper bound. An UNSAT
answer bounds split-with-carry targets only. It is evidence, not a proof, for general
targets.
