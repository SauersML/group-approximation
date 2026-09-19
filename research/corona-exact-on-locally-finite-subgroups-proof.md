---
rg: 2
id: corona-exact-on-locally-finite-subgroups-proof
kind: route
title: Exactify finite-group lifts through Wedderburn matrix units, average intertwiners, and read off the simple-tower dichotomy
target: corona-representations-are-exact-on-locally-finite-subgroups
requires:
  - opnorm-packet-exactification-is-dimension-free
  - binary-leavitt-elementary-group-is-simple
---

## Step 1: a finite group is exactly stable, dimension-free

Let `F` be finite and `V:F->U(d)` satisfy `||V(gh)-V(g)V(h)||<=delta` for
all `g,h`.  Write `C[F]=directSum_i M_(n_i)(C)` and fix Wedderburn matrix
units `e^(i)_(ab)=sum_g c^(i)_(ab)(g) g` with `sum_g|c^(i)_(ab)(g)|<=C_F`.
The linear extension `v(sum a_g g)=sum a_g V(g)` satisfies
`||v(xy)-v(x)v(y)||<=delta||x||_1||y||_1`, so the family `v(e^(i)_(ab))` is
a `C_F^2 delta`-approximate system of matrix units of total size `|F|`, and
`v(sum_(i,a) e^(i)_(aa))=V(1)=1`.  By
`opnorm-packet-exactification-is-dimension-free` there are exact matrix
units `f^(i)_(ab)` of the same type with
`||f^(i)_(ab)-v(e^(i)_(ab))||<=eps_(|F|)(C_F^2 delta)`.  Their sum
`P=sum f^(i)_(aa)` is a projection within `|F| eps` of `1`, hence equal to
`1` once that is `<1`.  Fourier inversion `g=sum_(i,a,b) pi_i(g)_(ab)
e^(i)_(ab)` in `C[F]` shows that

```text
rho(g)=sum_(i,a,b) pi_i(g)_(ab) f^(i)_(ab)                              (1)
```

is a unitary representation of `F` (it is the composite of the Wedderburn
isomorphism with an exact `*`-homomorphism of `directSum M_(n_i)`), and
`||rho(g)-V(g)||<=|F| eps_(|F|)(C_F^2 delta)=:omega_F(delta)->0`.  Nothing
depends on `d`.

## Step 2: exact lifts along a growing radius

Choose any unitary lifts `U_k(g)` of `Theta(g)`.  For each fixed `m`, the
coordinate defect `delta_k(m)=max_(g,h in F_m)||U_k(gh)-U_k(g)U_k(h)||`
tends to `0` as `k->infinity`, since only finitely many pairs occur.
Diagonalize: pick `m_k->infinity` so slowly that `delta_k(m_k)->0`.  Apply
Step 1 to `U_k|F_(m_k)` and set `rho_k=rho` on `F_(m_k)`, `rho_k=U_k`
elsewhere.  For a fixed `g in Lambda`, `g in F_(m_k)` for large `k` and
`||rho_k(g)-U_k(g)||<=omega_(F_(m_k))(delta_k(m_k))`; slowing `m_k`
further if necessary makes this tend to `0`, so `rho_k` lifts `Theta`.
This is item 1.

## Step 3: exact intertwiners and exact commutants

Let `gamma F gamma^-1<=Lambda` with `F` finite, and take `k` large so that
`F cup gamma F gamma^-1<=F_(m_k)`.  Let `T_k` lift `Theta(gamma)`; then
`eps_k=max_(g in F)||T_k rho_k(g)T_k^*-rho_k(gamma g gamma^-1)||->0`.  Put

```text
S=(1/|F|) sum_(g in F) rho_k(gamma g gamma^-1) T_k rho_k(g)^*.          (2)
```

Then `||S-T_k||<=eps_k` and `S rho_k(h)=rho_k(gamma h gamma^-1)S` for all
`h in F` by reindexing.  For `eps_k<1`, `S` is invertible, `S^*S` lies in
`rho_k(F)'`, and the polar part `T'_k=S(S^*S)^(-1/2)` is a unitary
satisfying `(CEL1)` exactly with `||T'_k-T_k||=O(eps_k)`; so `T'_k` still
lifts `Theta(gamma)`.  This is item 2.  For item 3, lift `x in Theta(F)'`
to `(x_k)`; the commutators `[x_k,rho_k(g)]` tend to `0` for the finitely
many `g in F`, and the average `(1/|F|)sum_g rho_k(g)x_k rho_k(g)^*` lies in
`rho_k(F)'` and differs from `x_k` by `o(1)`.

## Step 4: regular satisfiability

For `F,F'<=G` finite with `alpha:F->F'` an isomorphism, `Res_F lambda_G`
and `(Res_(F') lambda_G) o alpha` are both `[G:F]` copies of the regular
representation of `F`, hence unitarily equivalent; the intertwiner `T`
exists.  Given any finite tower `F_0<=...<=F_M` inside `Lambda` and any
finite list of partial conjugations `gamma_j` with
`gamma_j F_(m_j) gamma_j^-1<=F_M`, the regular representation of `F_M`
therefore carries exact intertwiners for all of them at once.  Since items
1--3 assert only equivalences of restrictions to isomorphic finite
subgroups and exact commutants, all of them hold in that model, which is
faithful on `F_M`.  This is item 4.

## Step 5: the simple-tower dichotomy

`SL_N(F_2)` is simple for `N>=3`, so each `rho_k|SL_(3*2^(m_k))(F_2)` is
trivial or faithful.  If faithful, then for `1!=g` of order `n` in that
group, `rho_k(g)` is a nontrivial unitary of order `n`, so it has an
eigenvalue `zeta!=1` with `zeta^n=1`, whence
`||rho_k(g)-1||>=|zeta-1|>=2 sin(pi/n)`, with value `2` when `n=2`.  If
`Theta` is nontrivial on `L_0`, faithfulness holds for all large `k` (a
fixed `1!=g in L_0` has `Theta(g)!=1`, so `rho_k(g)` is not eventually
`1`), and the lower bound passes to `Theta(g)` because `rho_k(g)` lifts it
and the bound is uniform in `k`.  If `Theta` is trivial on `L_0` it is
trivial on `H`, since `L_0!=1` and `H` is simple by
`binary-leavitt-elementary-group-is-simple`.  This is `(CEL2)`, and the
reformulation of `Rad_MF(H)=H` follows by reading the two branches.
