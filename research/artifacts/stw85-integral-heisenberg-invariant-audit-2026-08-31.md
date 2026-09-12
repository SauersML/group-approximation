# STW LXXXV audit: the integral Heisenberg tower

## Result audited

For every `n>=1`, let

```text
H_(2n+1)(Z)=<x_1,y_1,...,x_n,y_n,z |
 z central, y_j x_j=z x_j y_j,
 [x_i,x_j]=[y_i,y_j]=[x_i,y_j]=1 for i!=j>.
```

If `pi` is irreducible, Schur's lemma gives
`pi(z)=exp(2 pi i theta)1`.  The audit proves the exact dichotomy

```text
theta irrational:
  dim(H_pi)=infinity,
  C*_pi(H_(2n+1)(Z)) = A_theta tensor ... tensor A_theta  (n factors);

theta=p/q rational in lowest terms:
  dim(H_pi)=q^n,
  C*_pi(H_(2n+1)(Z)) = M_(q^n).
```

For irrational `theta`, put `B_(n,theta)=A_theta^(tensor n)`.  Its
complete `KT_u` invariant is

```text
K_0(B_(n,theta)) = exterior-even Z^(2n),
K_1(B_(n,theta)) = exterior-odd  Z^(2n),
[1]                = 1 in exterior-degree zero,
T(B_(n,theta))     = {tau},
rho_tau            = exp_wedge(Theta_(n,theta)),
```

where `Theta_(n,theta)` is the block diagonal skew form with `n`
blocks `[[0,theta],[-theta,0]]`.  Both K-groups have rank
`2^(2n-1)`.

## 1. Central fibres and the sign convention

Write `A_theta=C*(U,V | VU=exp(2 pi i theta)UV)`.  The displayed
presentation sends `x_j` to `U_j`, `y_j` to `V_j`, and `z` to
`exp(2 pi i theta)`.  Therefore

```text
C*(H_(2n+1)(Z))/(z-exp(2 pi i theta)1)
   = A_theta max-tensor ... max-tensor A_theta.
```

Rotation algebras are nuclear, so maximal and minimal tensor products
agree.  This fixes the common sign ambiguity: changing the commutator
convention replaces `theta` by `-theta`, which gives an isomorphic
rotation algebra but changes formulas if it is left unstated.

## 2. The rational boundary is finite-dimensional only after taking an irreducible fibre

Let `theta=p/q` in lowest terms and set
`omega=exp(2 pi i p/q)`.  In an irreducible representation,
`U_j^q` and `V_j^q` are central, hence scalar.  After multiplying
`U_j,V_j` by scalar q-th roots, one has

```text
U_j^q=V_j^q=1,     V_j U_j=omega U_j V_j.
```

The monomials `U_j^a V_j^b`, `0<=a,b<q`, span the resulting algebra.
The q-by-q clock and shift matrices satisfy the relations and make these
`q^2` monomials linearly independent.  Thus one pair generates
`M_q`; the `n` commuting pairs generate `M_q^(tensor n)=M_(q^n)`.
Every irreducible representation with this central character consequently
has dimension exactly `q^n`.

This does **not** assert `A_(p/q)=M_q`.  The rational rotation algebra
has nontrivial centre; only each of its irreducible fibres is `M_q`.

Conversely, a d-dimensional representation of one Heisenberg pair would
give, after taking determinants,

```text
det(VU)=exp(2 pi i d theta)det(UV),
```

so `exp(2 pi i d theta)=1`.  Hence finite dimension forces rational
`theta`.

## 3. Irrational fibres are faithful

For irrational `theta`, the block skew form
`Theta_(n,theta)` is nondegenerate: if an integer vector pairs
integrally with every standard basis vector, each of its coordinates
times the irrational number `theta` is an integer, so the vector is
zero.  Phillips' simplicity criterion therefore makes
`A_(Theta_(n,theta))` simple with a unique trace.  Any irreducible
representation of the central fibre is nonzero and hence faithful.  Its
norm-closed image is consequently the entire abstract algebra
`A_theta^(tensor n)`.  The determinant argument shows that its Hilbert
space is infinite-dimensional.

No uniqueness of the irreducible Hilbert-space representation is claimed.
Different faithful irreducible representations can have the same generated
C-star algebra.

## 4. K-groups and the pairing

Pimsner--Voiculescu gives

```text
K_0(A_theta)=Z[1] direct-sum Z[p_theta],
K_1(A_theta)=Z[U] direct-sum Z[V],
tau([1])=1,  tau([p_theta])=theta
```

for `0<theta<1`, where `p_theta` is a Powers--Rieffel projection.
All groups are free, so the graded Kunneth theorem has no Tor terms.
Equivalently, repeated PV identifies the groups with the even and odd
exterior powers of `Z^(2n)`.

Elliott's trace formula, recorded as Phillips Theorem 3.9, is exactly

```text
rho_tau = exp_wedge(Theta_(n,theta))
        = product_(j=1)^n (1+theta a_j wedge b_j).
```

Thus on the standard exterior basis it is `theta^|S|` on
`wedge_(j in S)(a_j wedge b_j)`, and zero on every other even basis
monomial.  This is the whole pairing, not merely its range.

In the graded tensor-word basis, choose from
`{1_j,p_j,U_j,V_j}` in each factor, with the last two symbols odd.
Even-parity words form a K0 basis and odd-parity words a K1 basis.  On an
even word `w`,

```text
rho_tau([w]) =
  theta^(number of p_j symbols),  if every symbol is 1_j or p_j;
  0,                              if any U_j or V_j occurs.
```

Phillips' real-rank-zero theorem and trace determination of projection
order give

```text
K_0(B_(n,theta))_+
 = {0} union {g : rho_tau(g)>0}.
```

For every `k>=2`, freeness also gives
`K_i(B_(n,theta);Z/k)=(Z/k)^(2^(2n-1))`; the coefficient reductions are
coordinatewise and the Bockstein maps into integral K-theory vanish.

## 5. Hostile checks

* **Rational fibre versus rational rotation algebra:** separated above;
  confusing them would make the main dichotomy false.
* **Faithfulness:** irreducibility alone does not imply faithfulness; the
  irrational central fibre's simplicity is the necessary step.
* **Tensor norm:** the group presentation initially gives commuting
  universal copies, hence a maximal tensor product; nuclearity is used
  before writing the spatial tensor product.
* **Trace range versus trace map:** the exterior-exponential functional
  is recorded on a basis, so infinitesimal K0 classes for `n>=2` are not
  lost.
* **Ordinary versus total invariant:** the theorem computes the
  `KT_u=(K_0,[1],K_1,T,rho)` requested in Problem LXXXV.  The displayed
  coefficient groups are an additional torsion-free consequence; no claim
  about the Hausdorffized algebraic-K1 part of the larger total invariant
  is needed.
* **Scope:** this closes every standard integral Heisenberg group, not all
  groups of polynomial growth and not higher-step nilpotent groups.

## Primary-source boundary

* Schafhauser--Tikuisis--White,
  [Nuclear C-star algebras: 99 problems](https://arxiv.org/abs/2506.10902),
  Problem LXXXV.
* N. Christopher Phillips,
  [Every simple higher dimensional noncommutative torus is an AT algebra](https://arxiv.org/abs/math/0609783):
  Theorems 1.9 and 1.10 give simplicity/unique trace and the rank-one
  Heisenberg fibre; Theorems 3.8 and 3.9 give real rank zero, the K-ranks,
  and Elliott's exterior-exponential pairing.
* M. Pimsner and D. Voiculescu,
  [Exact sequences for K-groups and Ext-groups of certain cross-product
  C-star algebras](https://www.theta.ro/jot/archive/1980-004-001/1980-004-001-005.pdf),
  J. Operator Theory 4 (1980), 93--118.
* Wayne M. Lawton,
  [Tutorial on Rational Rotation C-star Algebras](https://arxiv.org/abs/2111.02932),
  for the rational matrix-bundle model.
* Stuart White,
  [Abstract classification theorems for amenable C-star algebras](https://arxiv.org/abs/2307.03782),
  for the precise `KT_u` convention.
