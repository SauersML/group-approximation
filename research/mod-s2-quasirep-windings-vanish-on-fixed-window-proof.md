---
rg: 2
id: mod-s2-quasirep-windings-vanish-on-fixed-window-proof
kind: route
title: Take Tr log of the defect cocycle identity, fill each 2-cycle of Mod(S_2) by a 3-chain using torsion H_2, and propagate by paths and block-diagonal restriction
target: mod-s2-quasirep-windings-vanish-on-fixed-window
requires:
  - genus-two-mapping-class-group-homology-and-symplectic-quotient
---

Notation as in the claim. The (inhomogeneous, unnormalized) bar complex of a group `G` has
`d [g|h] = [h] - [gh] + [g]` and `d [g|h|l] = [h|l] - [gh|l] + [g|hl] - [g|h]`. The coboundary of a function `beta`
on pairs is `delta beta(g,h,l) = beta(h,l) - beta(gh,l) + beta(g,hl) - beta(g,h)`, so `<beta, d u> = <delta beta, u>`
for every finite 3-chain `u`. This complex computes `H_*(G; Z)` and `H_*(G; R)`.

## Step 1: Tr log is additive near the identity

**Lemma TL.** Let `U, V` be unitary `d x d` matrices with `||U - I|| + ||V - I|| < 2`, and let `log` be the principal
branch, defined on unitaries without eigenvalue `-1`, that is, with `||W - I|| < 2`. Then:

1. `Tr log (UV) = Tr log U + Tr log V`;
2. `Tr log (X U X^*) = Tr log U` for every unitary `X`;
3. `Tr log U^* = - Tr log U`.

*Proof.*
- Item 1. Put `U_t = exp(t log U)` and `V_t = exp(t log V)` for `t` in `[0,1]`. The eigenvalues of `U_t` are
  `e^(i t phi)` with `|phi| < pi`. So `||U_t - I|| <= ||U - I||`, and likewise for `V_t`. Hence

  ```text
  ||U_t V_t - I||  <=  ||U_t (V_t - I)|| + ||U_t - I||  <  2 ,
  ```

  so `Tr log (U_t V_t)` is defined and continuous in `t`. The function
  `f(t) = Tr log(U_t V_t) - Tr log U_t - Tr log V_t` takes values in `2 pi i Z`, because `det` is multiplicative
  and `exp Tr log = det`. It is continuous, and `f(0) = 0`. So `f(1) = 0`.
- Items 2 and 3. The principal logarithm is a spectral function: `log(X U X^*) = X (log U) X^*` and
  `log U^* = (log U)^*` = `-log U`, because `log U` is skew-adjoint. Take traces. `QED`

## Step 2: windings on integral cycles are integers

Let `z = sum_j n_j [g_j | h_j]` be an integral 2-cycle, and let `pi` have defect below `2` on its support. Choose
real `theta(g)` with `det pi(g) = exp(2 pi i theta(g))`. Then `det D(g,h) = exp(2 pi i (delta theta)(g,h))` with
`(delta theta)(g,h) = theta(g) + theta(h) - theta(gh)`. So

```text
exp(2 pi i kappa_z(pi)) = prod_j det D(g_j,h_j)^(n_j) = exp(2 pi i <delta theta, z>) = exp(2 pi i <theta, d z>) = 1 .
```

Hence `kappa_z(pi)` is an integer. It is a continuous function of the finitely many matrices
`pi(g_j), pi(h_j), pi(g_j h_j)` on the set where each `D(g_j, h_j)` has no eigenvalue `-1`.

## Step 3: the determinant cochain is a local cocycle

For every `g, h, l`,

```text
D(g,h) D(gh,l) = pi(g) pi(h) pi(l) pi(ghl)^* = [ pi(g) D(h,l) pi(g)^* ] D(g,hl) .
```

(Expand both sides. On the right, `pi(g)^*` cancels against `pi(g)`, and `pi(hl)^*` against `pi(hl)`.)

Suppose the defect is below `1` at the four pairs `(g,h), (gh,l), (h,l), (g,hl)`. Then each side is a product of
two unitaries whose distances to `I` add up to less than `2`, since conjugation preserves `||D(h,l) - I||`. Apply
Lemma TL to both sides:

```text
Tr log D(g,h) + Tr log D(gh,l) = Tr log D(h,l) + Tr log D(g,hl) ,
```

that is, `delta beta_pi (g,h,l) = 0`. If one of `g, h, l` is `e`, the same holds trivially, because
`D(e,x) = D(x,e) = I` for unital `pi`.

## Step 4: proof of (W1)

By `genus-two-mapping-class-group-homology-and-symplectic-quotient`, `H_2(M; Z) = Z/2`, and `H_1(M; Z) = Z/10` is
finitely generated. By universal coefficients,

```text
H_2(M; R) = H_2(M; Z) (x) R  (+)  Tor(H_1(M; Z), R) = 0 .
```

Let `z` be a finite real 2-cycle of `M`. Since `H_2(M;R) = 0`, there is a finite real 3-chain
`u = sum_k r_k [g_k | h_k | l_k]` with `d u = z`. Let `W(z)` be the union of:
- the support of `z`;
- the four face pairs `(g_k,h_k), (g_k h_k, l_k), (h_k,l_k), (g_k, h_k l_k)` of every simplex of `u`.

This finite set depends only on `z` and on the chosen `u`, not on `d`. If `pi` has defect below `1` on `W(z)`, then
`beta_pi` is defined on `W(z)`, and by Step 3 `delta beta_pi` vanishes on every simplex of `u`. So

```text
<beta_pi, z> = <beta_pi, d u> = <delta beta_pi, u> = sum_k r_k delta beta_pi (g_k, h_k, l_k) = 0 .   QED (W1)
```

(For integral `z` one may take `u` with `d u = 2 z` and integral coefficients, because `H_2(M;Z) = Z/2`. Then the same
computation gives `2 kappa_z(pi) = 0`.)

## Step 5: proof of (W2)

Let `ab = ba`. The chain `c = [a|b] - [b|a]` is a cycle:

```text
d c = [b] - [ab] + [a] - [a] + [ba] - [b] = [ba] - [ab] = 0 .
```

Put `W_(a,b) = W(c)` from Step 4; it contains `(a,b)` and `(b,a)`. Since `ab = ba`,

```text
D(a,b) D(b,a)^* = pi(a) pi(b) pi(ab)^* pi(ab) pi(a)^* pi(b)^* = [pi(a), pi(b)] .
```

With defect below `1` at both pairs, `||[pi(a),pi(b)] - I|| <= ||D(a,b) - I|| + ||D(b,a) - I|| < 2`. So `-1` is not
an eigenvalue. By Lemma TL (items 1 and 3),

```text
Tr log [pi(a), pi(b)] = Tr log D(a,b) - Tr log D(b,a) = 2 pi i d <beta_pi, c> = 0
```

by (W1). `QED (W2)`

## Step 6: proof of (W3)

Suppose, for contradiction, that `eta := max_{h in F} ||pi(h) - phi(h)|| < 1/12`. For `t` in `[0,1]` and `h` in `F`,
put `X_t(h) = t phi(h) + (1-t) pi(h)`. Then `||X_t(h) - pi(h)|| <= eta < 1`, so `X_t(h)` is invertible. Let `U_t(h)`
be its unitary polar part. Two facts are used:
- the polar part is a nearest unitary, so `||U_t(h) - X_t(h)|| <= ||pi(h) - X_t(h)|| <= eta`, and hence
  `||U_t(h) - pi(h)|| <= 2 eta`;
- it depends continuously on `t`.

Also `U_0 = pi|_F`, `U_1 = phi|_F`, and `U_t(e) = I` if `e` is in `F`.

For each pair `[g|h]` of `z`, the elements `g, h, gh` lie in `F`, and

```text
|| U_t(g) U_t(h) - U_t(gh) ||  <=  || pi(g) pi(h) - pi(gh) || + 6 eta  <=  1/2 + 6 eta  <  1 .
```

So along the whole path the defect is below `1` on the support of `z`. By Step 2, `kappa_z(U_t)` is then an integer
that depends continuously on `t`, so it is constant. Now `kappa_z(U_0) = kappa_z(pi)`: the cycle `z` of `H` is also
a cycle of `M`, and it uses the same matrices. Since `pi` has defect at most `1/2 < 1` on `W(z)`, (W1) gives
`kappa_z(pi) = 0`. On the other hand `kappa_z(U_1) = kappa_z(phi) != 0`. This is a contradiction. `QED (W3)`

## Step 7: proof of (W4)

- *Unitarity.* For fixed `g` and `j`, exactly one `i` has `g_i^-1 g g_j` in `H`. So `Ind phi (g)` is a block
  permutation matrix with unitary blocks, hence unitary. At `g = e` it is `I`.
- *Restriction to `H`.* For `h` in `H`, normality gives `g_i^-1 h g_j = (g_i^-1 h g_i)(g_i^-1 g_j)`. This lies in
  `H` if and only if `i = j`. So `Ind phi (h) = diag_i phi(c_i h)` with `c_i(x) = g_i^-1 x g_i`.

Hence, for `g, h` in `H`, `D_(Ind phi)(g,h) = diag_i D_phi(c_i g, c_i h)`. The trace of the logarithm of a block
diagonal matrix is the sum over the blocks, so

```text
kappa_z(Ind phi) = sum_i kappa_(c_i z)(phi) ,     c_i z = g_i^-1 z g_i .
```

The left side vanishes by (W1), applied to `Ind phi` with `z` viewed as a cycle of `M`. `QED (W4)`

## Remarks (context only; not used by the theorem and not pinned)

- **R1: the virtual test is non-vacuous.** The level-two subgroup `M[2]` (the kernel of `M -> Sp_4(Z/2)`)
  contains the hyperelliptic involution `iota` centrally. By Birman--Hilden, `M[2]/<iota> ~= PMod(S_(0,6))`, which
  is `pi_1` of the aspherical space `M_(0,6)`. The Poincare polynomial of `M_(0,n)` is `prod_(k=2)^(n-2) (1 + k t)`.
  For `n = 6` the coefficient of `t^2` is `2*3 + 2*4 + 3*4 = 26`. Since the kernel is finite, `b_2(M[2]) = 26`. So
  finite-index subgroups of `M` carry many non-torsion 2-cycles. Any quasi-representation of `M[2]` that is
  nonzero on one of them is covered by (W3) and (W4).
- **R2: consequence for Voiculescu pairs, conditional.** Suppose one imports the dimension-free theorem that a pair
  of unitary matrices with small commutator and zero Exel--Loring invariant is close to a commuting pair (Lin's
  almost-commuting-unitaries theorem). Then (W2) shows that on every commuting pair `(a,b)` of `M`, every model of
  `M` with small defect on `W_(a,b)` restricts to a pair that is close to commuting. So the instability of
  `Z^2 < M` never propagates to `M`, which answers the concern recorded in `mod-s2-is-point-norm-matricially-stable`.
  This remark is not pinned in the graph.
- **R3: other degrees.** Harer gives the virtual cohomological dimension of `M` as `4g - 5 = 3`, so `H_k(M;Q) = 0` for
  `k >= 4`. Degree two is therefore the only positive even rational degree. The same Tr log mechanism has no
  higher-degree analogue here that would need checking.
- **Where the proof would fail for `Sp_4(Z)`.** Step 4 uses `H_2 (x) R = 0`. For `Sp_4(Z)` the Maslov class makes
  `H_2(Sp_4(Z); R)` nonzero, and the relator cycle `c_r` of `sp4-quasirep-windings-budget-and-saturation` has no
  filling. That is why windings there can be linear in the defect, while on `M` they vanish identically.
