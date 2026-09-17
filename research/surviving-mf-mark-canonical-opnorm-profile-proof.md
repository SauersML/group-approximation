---
rg: 2
id: surviving-mf-mark-canonical-opnorm-profile-proof
kind: route
title: Take a nontrivial MF character, confine its scalar kernel to the center, and realize its Diracization by conjugate tensor powers
target: surviving-mf-mark-diracizes-to-canonical-opnorm-profile
requires:
  - torsion-normal-generator-mf-character-criterion
  - character-diracization-limit
  - finite-group-opnorm-support-profile
---

Notation: `Delta` finitely generated and perfect, `C<=Z(Delta)`,
`pi:Delta->H=Delta/C` with `H` simple, `a` of finite order with
`pi(a)!=1`.  An **MF character** is a pointwise limit of normalized traces of
operator-norm asymptotic unitary representations.

**Step 0: the mark normally generates.**  Let `N` be the normal closure of
`a`.  Then `pi(N)` is a nontrivial normal subgroup of the simple group `H`, so
`NC=Delta`.  Because `C` is central, `[nc,n'c']=[n,n']`, hence

```text
Delta=[Delta,Delta]=[NC,NC]=[N,N]<=N.
```

**Step 1: a nontrivial MF character.**  By
`torsion-normal-generator-mf-character-criterion` (which needs only a
finite-order normal generator of a finitely generated group), `Rad_MF(Delta)!=Delta`
gives an MF character `chi!=1`, realized by operator-norm asymptotic
representations `V_k:Delta->U(n_k)` with `tr V_k(g)->chi(g)`.  A pointwise
limit of normalized traces of asymptotic representations is a normalized
positive-definite class function: the positivity and conjugation-invariance
defects are bounded by the representation defects, which tend to zero.  So
`chi` is a character.

**Step 2: the scalar kernel is central.**  By `character-diracization-limit`,
`K_chi={g:|chi(g)|=1}` is normal, and `u_g` is the scalar `chi(g)1` in the
GNS algebra exactly for `g in K_chi`.  The image `pi(K_chi)` is normal in
`H`.  If `pi(K_chi)=H`, then `K_chi C=Delta` and Step 0's commutator
computation gives `K_chi=Delta`.  Then every `u_g` is a scalar, so `chi` is a
homomorphism `Delta->T`, which is trivial because `Delta` is perfect.  This
contradicts `chi!=1`.  Hence `pi(K_chi)=1`, that is, `K:=K_chi<=C`.

**Step 3: operator-norm realization of the Diracization.**  For fixed `j`,
put

```text
W^(j)_k = V_k^(tensor j) tensor conj(V_k)^(tensor j) : Delta -> U(n_k^(2j)).
```

These are unitary.  By telescoping through the `2j` unitary tensor factors,

```text
||W^(j)_k(gh)-W^(j)_k(g)W^(j)_k(h)||_op
   <= 2j ||V_k(gh)-V_k(g)V_k(h)||_op,
```

and the normalized trace is multiplicative on tensor products, so

```text
tr W^(j)_k(g)=|tr V_k(g)|^(2j) -> |chi(g)|^(2j)      (k -> infinity).
```

Enumerate `Delta={g_1,g_2,...}`.  For each `j` choose `k(j)` so that the
multiplicative defect of `W^(j)_k(j)` on all pairs from `g_1,...,g_j` is at
most `1/j`, and `|tr W^(j)_k(j)(g_i)-|chi(g_i)|^(2j)|<=1/j` for `i<=j`.  Then
`W_j:=W^(j)_k(j)` is an operator-norm asymptotic representation, and by
`character-diracization-limit`

```text
tr W_j(g) -> lim_j |chi(g)|^(2j) = 1_K(g).
```

This proves `(DCP1)` and item 1.

**Step 4: packet profile.**  Let `F` be finite with `F intersect K=1`.
`finite-group-opnorm-support-profile` gives exact representations
`rho_j:F->U(d_j)` with `max_f ||rho_j(f)-W_j(f)||_op -> 0`, so
`tr rho_j(f)->1_K(f)=delta_e(f)` on `F`.  With
`e_lambda=(dim lambda/|F|) sum_f conj(lambda(f)) f`,

```text
tr rho_j(e_lambda) -> (dim lambda/|F|) dim lambda = dim(lambda)^2/|F|,
```

which is `(DCP2)`.  For `F=<a>` with `<a> intersect K=1` the irreducibles are
the `m` characters of the cyclic group, so each eigenvalue fraction tends to
`1/m`.  An involution `a` lies outside `C`, hence outside `K`, and so
`<a> intersect K=1` holds automatically.

**Step 5: survival.**  `||W_j(a)-1||_2^2=2-2 Re tr W_j(a)`.  For an
involution, `tr W_j(a) -> 0`, so this tends to `2`.  Operator norm dominates
normalized HS norm.  Therefore the corona homomorphism defined by `(W_j)`
retains `a`.

Every step is internal: tensor algebra, the GNS computation behind
Diracization, normal generation from perfectness and simplicity, and
fixed-finite-group operator-norm correction.  No Property `(T)` or external
theorem is used.
