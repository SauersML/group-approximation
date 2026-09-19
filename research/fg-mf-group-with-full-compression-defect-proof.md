---
rg: 2
id: fg-mf-group-with-full-compression-defect-proof
kind: route
title: Double the central sign, split corona unitaries into balanced symmetries, and chain them by dihedral relations
target: fg-mf-group-with-full-compression-defect
requires:
  - finite-order-central-compression-defect-survives-mf
  - compression-defects-die-in-rigid-targets
  - locally-residually-finite-targets-kill-compression-defects
artifacts:
  - experiments/full-defect-symmetries-2026-09-17/check_symmetry_chains.py
---

Throughout, `[x,y]=xyx^-1y^-1`. For a sequence `k=(k_n)`, write
`Q_k = prod_n M_(k_n)(C) / sum_n M_(k_n)(C)` for the norm matrix corona.
Here `sum` is the ideal of norm-null sequences. A *balanced symmetry* in
`U(2m)` is a self-adjoint unitary of trace zero, that is, one with `+1` and
`-1` eigenspaces of dimension `m`.

## Step 0. Input

`finite-order-central-compression-defect-survives-mf` (ESTABLISHED) gives,
verbatim:

> There is a three-generated countable MF group `G=<a,t,c>` with
> `ord(a)=infinity`, `t<a>t^(-1)=<a^2><<a>`, `c^2=1`, `[a,c]=1`, and
> `d=[tct^(-1),a]` a nonidentity central involution. In the explicit
> norm-corona embedding, `d=-I`.

Write `G_0` for this group, viewed inside `U(Q_k)` for some dimension
sequence `k=(k_n)`, with `[tct^-1,a]=-1`.

**Amplification.** The map `x=(x_n) |-> (x_n tensor 1_n)` sends
`prod M_(k_n)` to `prod M_(n k_n)`. It is a unital *-homomorphism, it maps
null sequences to null sequences, and it preserves norms coordinatewise.
So it induces an injective unital *-homomorphism `Q_k -> Q_(n k_n)`, which
sends `-1` to `-1`. Hence, replacing `k_n` by `n k_n`, we may assume
`k_n -> infinity`.
Injectivity holds because the quotient norm is `limsup_n ||x_n||`, and the
amplification does not change any `||x_n||`.

## Step 1. Doubling

Put `M = M_2(Q_k)`. This is `Q_(2k)`, the norm corona for the dimensions
`2k_n -> infinity`, by `M_2(prod A_n / sum A_n) = prod M_2(A_n) / sum M_2(A_n)`.
In `U(M)` define

```text
a' = a (+) a,   t' = t (+) t,   c' = c (+) 1,   e = (-1) (+) 1 .
```

- `x |-> x (+) x` is an injective homomorphism on `G_0`. So `a'` has
  infinite order, and `t' a' t'^-1 = a'^2`. For every group `G` containing
  `a'` and `t'`, with `L=<a'>`, this gives `t' L t'^-1 = <a'^2>`, a
  proper subgroup of `L`.
- `c' a' = ca (+) a = ac (+) a = a' c'`, so `c'` lies in `C_G(L)`.
- `t' c' t'^-1 = tct^-1 (+) 1`, so
  `[t' c' t'^-1, a'] = [tct^-1,a] (+) [1,a] = (-1) (+) 1 = e`.

Hence **for every subgroup `G` of `U(M)` containing `a', t', c'`, the
element `e` lies in `D_G(<a'>)`.** Moreover `e` lifts exactly to the
coordinatewise balanced symmetries `e_n = diag(-I_(k_n), I_(k_n))`.

## Step 2. Every corona unitary is a product of four balanced symmetries

**Lemma A (finite dimensions).** Every `v` in `SU(2m)` is a product
`S_1 S_2 S_3 S_4` of balanced symmetries.

*Proof.* Diagonalize `v = W Lambda W^*` with `W` unitary and
`Lambda = diag(l_1,...,l_2m)`, where `l_1 l_2 ... l_2m = 1`. Put
`pi_j = l_1 ... l_j`, so `pi_2m = 1`. Define diagonal unitaries:

- `Lambda_1` has entries `pi_(2i-1)` at position `2i-1` and `pi_(2i-1)^-1` at position `2i`;
- `Lambda_2` has entries `pi_(2i)` at position `2i` and `pi_(2i)^-1` at position `2i+1`, indices mod `2m`.

The entry of `Lambda_2` at position 1 is `pi_2m^-1 = 1`. Then:

- position 1 of `Lambda_1 Lambda_2` is `pi_1 = l_1`;
- position `2i` is `pi_(2i-1)^-1 pi_(2i) = l_(2i)`;
- position `2i+1` is `pi_(2i)^-1 pi_(2i+1) = l_(2i+1)`.

So `Lambda = Lambda_1 Lambda_2`.

Each `Lambda_r` is conjugate, by a permutation matrix, to `diag(D, D^-1)`
with `D` a diagonal unitary of size `m`. Also

```text
diag(D, D^-1) = S S',   S = [[0, D], [D^-1, 0]],   S' = [[0, 1], [1, 0]].
```

Both `S` and `S'` are self-adjoint, square to `1`, and have zero trace
(zero diagonal), so they are balanced symmetries. Conjugating back by
permutation matrices and by `W` gives the four factors. QED.

**Lemma B (corona).** Let `u` be in `U(M)`. Then there are elements
`R_1, ..., R_4` of `U(M)` with `u = R_1 R_2 R_3 R_4`. Each `R_i` is the
image of a sequence `(R_(i,n))` of balanced symmetries of size `2k_n`.

*Proof.*

1. **Unitary lift.** Lift `u` to any bounded sequence `(y_n)`. Since
   `y^*y - 1` and `yy^* - 1` are null, the polar decomposition
   `y_n = w_n |y_n|`, with `w_n` in `U(2k_n)` (finite dimensions), satisfies
   `||y_n - w_n|| <= || |y_n| - 1 || -> 0`. So `(w_n)` is a unitary lift
   of `u`.
2. **Determinant.** Write `det w_n = exp(i theta_n)` with `theta_n` in
   `[0, 2pi)`, and put `v_n = exp(-i theta_n / (2k_n)) w_n`. Then `v_n` is
   in `SU(2k_n)`, and `||v_n - w_n|| <= pi / k_n -> 0` because
   `k_n -> infinity`. So `(v_n)` is still a lift of `u`.
3. **Assembly.** Apply Lemma A to each `v_n`. The factor sequences are
   unitary, hence bounded, and their coordinatewise product is `(v_n)`.
   Passing to `M` gives the claim. QED.

Applying Lemma B to `a'`, `t'` and `c'` gives twelve elements
`R_1, ..., R_12` of `U(M)`, each liftable to coordinatewise balanced
symmetries, with

```text
a' = R_1 R_2 R_3 R_4,   t' = R_5 R_6 R_7 R_8,   c' = R_9 R_10 R_11 R_12 .
```

## Step 3. Dihedral chains of balanced symmetries

**D3 identity.** If `x^2 = y^2 = (xy)^3 = 1` in a group, then

```text
(xy) x (xy)^-1 = x y x y^-1 x^-1 = x y x y x = (xy)^3 y^-1 = y .
```

So `y` is conjugate to `x` by the element `xy` of `<x,y>`.

**Lemma C (finite dimensions).** Let `E` and `R` be balanced symmetries in
`U(2m)`. Then there are balanced symmetries `P_1, P_2, P_3` such that,
with `P_0 = E` and `P_4 = R`, we have `(P_j P_(j+1))^3 = 1` for
`j = 0, 1, 2, 3`.

*Proof.*

**(i) Block form.** Let `V = C^2m` and `U = ER`. Then `EUE = RE = U^-1`,
so `E` maps the `zeta`-eigenspace `V_zeta` of `U` onto `V_(conj zeta)`.

- For `zeta` not in `{1,-1}` with `Im zeta > 0`, take an orthonormal basis
  `x_1, ..., x_r` of `V_zeta`. The vectors `Ex_i` form an orthonormal basis
  of `V_(conj zeta)`, and the two spaces are orthogonal.
- Each plane `span{x_i, Ex_i}` is invariant under `E` and `U`, hence under
  `R = EU`. On it, `E` has trace 0. `R` has determinant
  `det E det U = -1`, so it is a symmetry with eigenvalues `+1` and `-1`.
- On `V_1` and `V_-1`, `R = +E` or `R = -E`. So `E` and `R` are
  simultaneously diagonal there, with lines of type `(E,R) = (s,s')` for
  `s, s'` in `{+1,-1}`. Let `N_(s s')` be the number of lines of each type.
- The planes contribute zero to both traces. So `tr E = tr R = 0` gives
  `N_(++) + N_(+-) = N_(-+) + N_(--)` and `N_(++) + N_(-+) = N_(+-) + N_(--)`.
  Hence `N_(++) = N_(--)` and `N_(+-) = N_(-+)`.
- Pair each `(+,+)` line with a `(-,-)` line, and each `(+,-)` line with a
  `(-,+)` line.

So `V` is an orthogonal sum of planes `B_1, ..., B_m`. Each plane has an
orthonormal basis `(f_1, f_2)` with `E f_1 = f_1` and `E f_2 = -f_2`. In
that basis, `E|B_j = sigma_z` and `R|B_j = r_j . sigma`, a trace-zero
self-adjoint unitary. Here `r_j` is a unit vector in `R^3` and `sigma` is
the vector of Pauli matrices.

**(ii) Pauli products.** For unit vectors `p, q`,

```text
(p.sigma)(q.sigma) = (p.q) 1 + i (p x q).sigma .
```

- If `p = q`, the product is `1`.
- If `p.q = -1/2`, put `k = (p x q)/|p x q|`, with `|p x q| = sqrt(3)/2`.
  The product is `exp(i (2pi/3) k.sigma)`, whose cube is
  `exp(2 pi i k.sigma) = 1`.

**(iii) Sphere chains.** Call unit vectors `p, q` *linked* if `p = q` or
`p.q = -1/2`.

*Midpoint.* If `n.m >= -1/2`, some `p` is linked to both `n` and `m`.
Proof:

- Put `u = (n+m)/|n+m|` and `g = n.u = m.u = sqrt((1+n.m)/2)`, so `g >= 1/2`.
- Let `w` be a unit vector orthogonal to `n` and `m`.
- Take `p = -u/(2g) + sqrt(1 - 1/(4g^2)) w`. Then `p.n = p.m = -1/2`.

*Far pair.* If `n.m < -1/2`, write `m = cos(Phi) n + sin(Phi) v` with `v`
a unit vector orthogonal to `n` and `Phi` in `(2pi/3, pi]`. Put
`p_1 = -n/2 + (sqrt 3/2) v`. Then:

- `p_1.n = -1/2`;
- `p_1.m = cos(Phi - 2pi/3) >= 1/2`, so the midpoint construction applies
  to `(p_1, m)`.

*Chains.* So for all unit vectors `n, m` there is a chain
`n = q_0, q_1, q_2, q_3, q_4 = m` with consecutive members linked:

- `(n, mid, m, m, m)` in the first case;
- `(n, p_1, mid(p_1,m), m, m)` in the second.

**(iv) Assembly.** On each `B_j`, take such a chain from `(0,0,1)`, which
corresponds to `sigma_z = E|B_j`, to `r_j`. Let `P_i` act on `B_j` as
`q_i^(j) . sigma`.

- Each `P_i` is self-adjoint and unitary, with trace 0 on every plane, so
  it is a balanced symmetry.
- `P_0 = E` and `P_4 = R`.
- Each `P_i P_(i+1)` is block diagonal with blocks whose cube is `1`, by
  (ii). QED.

## Step 4. The group

For each `i = 1, ..., 12`, apply Lemma C coordinatewise to the pair
`(e_n, R_(i,n))`. Both are balanced symmetries of size `2k_n`. The output
sequences are unitary, hence bounded. Their images in `M` are elements
`P_(i,0) = e, P_(i,1), P_(i,2), P_(i,3), P_(i,4) = R_i` with

```text
P_(i,j)^2 = 1,    (P_(i,j) P_(i,j+1))^3 = 1     (j = 0, 1, 2, 3).
```

These identities hold exactly in `prod M_(2k_n)`, hence in `M`. Define

```text
G = < e, R_1, ..., R_12, P_(i,j) : 1 <= i <= 12, 1 <= j <= 3 > <= U(M),
```

a group generated by 49 involutions.

1. **All generators are conjugate to `e`.** By the D3 identity,
   `P_(i,j+1) = (P_(i,j) P_(i,j+1)) P_(i,j) (P_(i,j) P_(i,j+1))^-1`, and
   the conjugating element lies in `G`. By induction on `j`, every
   `P_(i,j)` is `G`-conjugate to `P_(i,0) = e`, including
   `P_(i,4) = R_i`. Hence `G = <<e>>_G`.
2. **The compression data lie in `G`.** `a'`, `t'` and `c'` lie in `G` as
   products of the `R_i`. By Step 1 applied to this `G`, with `L = <a'>`:
   `L` is infinite cyclic, `t' L t'^-1 = <a'^2> < L`, `c'` lies in
   `C_G(L)`, and `e = [t' c' t'^-1, a']` lies in `D_G(L)`.
3. **Full defect.** `D_G(L)` is normal in `G` and contains `e`, so it
   contains `<<e>>_G = G`. Hence `D_G(L) = G`.
4. **MF.** `G` is a finitely generated, hence countable, subgroup of
   `U(Q_(2k))`. By the definition in `non_mf_groups_exist.tex` ("Equivalently,
   `G` embeds in the unitary group of the norm matrix corona"), `G` is MF.
   The identity map is an injective homomorphism to an MF group, so
   `Rad_MF(G) = 1`. It is not `G`, because `e != 1`.

This proves items 1-4 of the target. For every `P` containing `(G, L)`,
(FDC_P) would force `Rad_MF(G) = G`, which is false.

## Step 5. Consequences

Let `f: G -> H` be a surjective homomorphism. A generator
`[u c u^-1, l]` of `D_G(L)` maps to `[f(u) f(c) f(u)^-1, f(l)]`. Here
`f(u) f(L) f(u)^-1 <= f(L)` and `f(c)` centralizes `f(L)`, so
`H = f(D_G(L)) <= D_H(f(L))`. So every quotient has full defect.

- Abelian quotients are trivial, since their commutators are trivial. So
  `G` is perfect.
- Nontrivial finite and linear quotients are excluded by
  `compression-defects-die-in-rigid-targets`.
- Nontrivial locally residually finite quotients are excluded by
  `locally-residually-finite-targets-kill-compression-defects`, since
  `f(L)` is finitely generated.

These consequences are side remarks. Items 1-4 of the target use only
Steps 0-4.

## Verification

`experiments/full-defect-symmetries-2026-09-17/check_symmetry_chains.py`
implements Lemma A and Lemma C over 200 random pairs in `U(2m)` for
`m <= 6`, and checks the degenerate sphere angles 0, 60, 120, 150 and 180
degrees. It reports a maximum residual of `2e-14` for:

- `S_1 S_2 S_3 S_4 = v`;
- `(P_j P_(j+1))^3 = 1`;
- the D3 conjugation identity.
