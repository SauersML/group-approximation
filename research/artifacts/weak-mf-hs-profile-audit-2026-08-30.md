# Weak norm-corona MF versus hyperlinear: exact boundary and a sharper hinge

Date checked: 2026-08-30.

## Outcome

The root `mf-implies-hyperlinear` is not closed here.  Under Cairn's weak
norm-corona convention it remains a genuine open implication, and neither
the primary literature nor the repository's current corner machinery
supplies the missing trace selection.  This audit contributes two exact
results:

1. the phase-cancelled amplifier only needs the intrinsic normalized
   Hilbert--Schmidt profile `eta_n^2/kappa_n -> 0`, a weaker rate condition
   on any fixed model sequence than the current Cairn hole
   `epsilon_n^2/kappa_n -> 0` involving operator-norm defect; and
2. an explicit faithful weak-MF embedding of the binary lamplighter group
   in which **every** invariant corner is intrinsically trace-blind to the
   rank-one lamp.  Thus arbitrary-realization corner extraction is false;
   the existential corner claim must select a different realization.

The first result gives a sharper live hinge.  The second closes a proof
strategy, not the root: the lamplighter is residually finite and has other
models which see the lamp with trace zero.

## 1. The convention split in the primary literature

There are two inequivalent uses of “MF group.”

### Weak norm-corona MF

Blackadar--Kirchberg's matrix-field formulation for a separable C-star
algebra is embedding into

```text
prod_k M_(n_k) / directSum_k M_(n_k),
```

where `directSum` is the operator-norm `c_0` ideal.  Carrión--Dadarlat--
Eckhardt, Definition 2.7, define a group to be MF when it embeds in the
unitary group of this quotient.  Korchagin, Definition 1, uses the same
group convention and explicitly warns that the resulting representation
can become nonfaithful after passage to normalized Hilbert--Schmidt norm.
Dadarlat's 2021 asymptotic formulation is equivalent: multiplication defect
tends to zero in operator norm and each nonidentity `g` satisfies only

```text
limsup_n ||phi_n(g)-I||_op > 0.
```

Shulman, Definition 3 (2026), again uses the norm-corona convention and
separates it by a footnote from the stronger trace-controlled usage.

Primary sources:

* Blackadar--Kirchberg, *Generalized inductive limits of finite-dimensional
  C-star algebras*, Theorem 3.2.2,
  <https://doi.org/10.1007/s002080050039>.
* Carrión--Dadarlat--Eckhardt, *On groups with quasidiagonal C-star
  algebras*, Definition 2.7, <https://arxiv.org/abs/1210.4050>.
* Korchagin, *MF-property for countable discrete groups*, Definition 1 and
  the warning immediately following it,
  <https://arxiv.org/abs/1704.06906>.
* Dadarlat, *Obstructions to matricial stability of discrete groups and
  almost flat K-theory*, <https://arxiv.org/abs/2007.12655>.
* Shulman, *The MF property for amalgamated free products*, Definition 3,
  <https://arxiv.org/abs/2603.13564>.

For the quotient map `q`,

```text
||q((x_n))|| = limsup_n ||x_n||.
```

The multiplication relations vanish by a **full limit**, while separation
is a positive limsup.  Reblocking can arrange simultaneous lower bounds on
successive finite sets, but supplies no normalized trace mass.

There is no alternate quotient obtained by declaring a sequence zero when
its norm has liminf zero.  That set is not even closed under addition: for
alternating scalar sequences

```text
x=(1,0,1,0,...),       y=(0,1,0,1,...),
```

both have norm-liminf zero while `x+y=1` does not.  A fixed ultrafilter
gives a valid ideal, but does not repair trace collapse.

### Strong or trace-preserving MF

Schafhauser, Definition 1.1, additionally requires

```text
|tr_d(u_g)| < epsilon        for g != 1
```

and reduced group-C-star norm control.  Proposition 2.2 identifies this
with the canonical trace on `C*_lambda(G)` being an MF trace.  Gao--
Kunnawalkam Elayavalli--Manzoor--Patchell use the same strong/trace-
preserving convention in 2026.

* Schafhauser, *Finite dimensional approximations of certain amalgamated
  free products of groups*, Definition 1.1 and Proposition 2.2,
  <https://arxiv.org/abs/2306.02498>.
* Gao--Kunnawalkam Elayavalli--Manzoor--Patchell, *A new source of purely
  finite matricial fields*, <https://arxiv.org/abs/2603.24502>.

Under this convention the implication to hyperlinearity is immediate:

```text
||u_g-I||_(2,norm)^2 = 2-2 Re tr_d(u_g) -> 2,
```

and normalized Hilbert--Schmidt defect is bounded by operator-norm defect.
That proof cannot be imported into the weak convention.

## 2. Exact failure of the canonical norm-to-trace passage

The matrix

```text
v_n = diag(-1,1,...,1) in U(n)
```

satisfies

```text
||v_n-I||_op=2,
||v_n-I||_(2,norm)=2/sqrt(n)->0,
tr_n(v_n)=1-2/n->1.
```

Thus the canonical map from a norm matrix ultraproduct to the corresponding
tracial ultraproduct can kill a nonidentity unitary.  Natural ultralimits of
the normalized coordinate traces on the norm corona are not faithful.

A spectral projection of `v_n` detects its `-1` eigenspace, but for a group
table it need not commute even approximately with the other letters.  The
new lamplighter theorem below shows that this is not merely a failure of the
first spectral cut: every invariant projection can fail.

## 3. A hostile faithful realization: exact corner no-go

For the binary lamplighter

```text
L=(directSum_Z C_2) semidirect Z,
```

map the shift to the cyclic shift `S_n` and the lamp at zero to

```text
A_n=I_n-2|e_0><e_0|.
```

These are exact representations through finite cyclic lamplighter
quotients and give a faithful norm-corona representation.  If a projection
lift `q_n` represents any `P in u(L)' cap Q`, set

```text
r_n=rank(q_n),
delta_n=||[q_n,S_n]||_op->0,
t_(n,j)=<q_n e_j,e_j>.
```

For each fixed `K` and all `n>K`,

```text
|t_(n,j)-t_(n,0)| <= j delta_n,
r_n >= sum_(j=0)^(K-1) t_(n,j),
```

so

```text
t_(n,0)/r_n <= 1/K + delta_n (K-1)/2.                (A1)
```

Let `I_q={n:q_n!=0}`.  It is infinite when `P!=0`.  Letting `n` tend to
infinity through `I_q` and then letting `K` tend to infinity gives
`t_(n,0)/r_n->0`, uniformly over the positive ranks of the corners.
Therefore

```text
lim_(n->infinity, n in I_q) tr_(r_n)(q_n A_n q_n)=1. (A2)
```

The compressed matrices are asymptotically unitary, and polar-unitary
corrections have the same normalized-trace limit.

This disproves the stronger statement

> every faithful weak-MF realization contains a detecting invariant corner.

It does not disprove Cairn's `mf-invariant-corner-visibility`, whose
existential quantifier may replace the realization.  Indeed residual
finiteness gives regular finite-quotient models of `L` in which the lamp has
trace zero.  The exact conclusion is that realization selection is load
bearing even after corners are allowed.

## 4. The padding-invariant analytic hinge

Let `phi_n` be operator-norm local models, let

```text
eta_n = max tested normalized-HS multiplication defect,
kappa_n = 1-Re tr(phi_n(g)).
```

The phase-cancelled table

```text
theta_n(x)=phi_n(x) directSum conjugate(phi_n(x))
           directSum 1 directSum 1
```

has relative multiplication trace

```text
r_n(a,b)=1-delta_n(a,b)^2/4 in [0,1]
```

and marked trace `1-kappa_n/2`.  If

```text
eta_n^2/kappa_n->0,                                  (A3)
```

choose `L_n` with `L_n eta_n^2->0` and
`L_n kappa_n->infinity`.  For `Psi_n=theta_n^(tensor L_n)`,

```text
||Psi_n(a)Psi_n(b)-Psi_n(ab)||_2^2
 <= L_n delta_n(a,b)^2/2 ->0,

tr(Psi_n(g))
 <= exp(-L_n kappa_n/2)->0.                          (A4)
```

This is sufficient for elementwise tracial visibility and hence for
hyperlinearity.

The current Cairn claim `mf-trace-gap-defect-ratio-models` assumes the
stronger `epsilon_n^2/kappa_n->0`, where `epsilon_n` is the operator-norm
defect.  Only `eta_n` occurs in `(A4)`.  This distinction matters under
identity padding.  If

```text
phi_n'(x)=phi_n(x) directSum 1_(m_n),
rho_n=d_n/(d_n+m_n),
```

then exactly

```text
eta_n'^2=rho_n eta_n^2,
kappa_n'=rho_n kappa_n,
eta_n'^2/kappa_n'=eta_n^2/kappa_n.                   (A5)
```

The operator defect `epsilon_n` does not scale, so its ratio to `kappa_n`
can be made arbitrarily bad by padding even when the amplifier's true ratio
is unchanged.  The proposed node `mf-hs-defect-gap-profile` is therefore the
right weaker frontier between invariant-corner visibility and the root.

## 5. What remains mathematically open

Weak MF controls the largest singular value of the marked deviation and the
largest singular value of every relation error.  The new profile `(A3)`
compares their normalized second moments.  Neither separability nor passage
to an ultrafilter forces this comparison.  Central support in a bidual does
not provide a projection in the norm corona, and an orbit-generated hull can
dilute a rank-one mark through an arbitrarily large irreducible sector.

Consequently no proof of `mf-implies-hyperlinear`, no proof of universal
invariant-corner visibility, and no counterexample to the universal
implication is asserted here.  The honest advance is the sharp
padding-invariant profile and the exact arbitrary-realization corner
countermodel.
