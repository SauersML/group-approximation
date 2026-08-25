---
rg: 2
id: selector-baumslag-orbits-overlap-or-prepay
kind: claim
title: Selector-dressed Baumslag orbits either overlap stationarily or prepay their orthogonality
distinct_from:
  baumslag-address-geometric-stationary-profile: That computes the geometric prefix law for a structural payload; this keeps the genuine selector square-root phase and proves that it does not alter either the raw-orbit overlap or the first-hit capacity ledger.
  independent-address-capacity-cannot-drive-selected-atom-growth: That is the abstract trace-capacity inequality for independent address projections; this supplies exact unbounded finite quotients of the finitely presented Baumslag host realizing both sides of the dichotomy with the selected Clifford atom positive.
  one-dimensional-address-rules-have-periodic-models: That treats finite-alphabet finite-window shift rules; the Baumslag binomial action is not such a local rule, and here is handled by its finite-field affine quotients.
---

**ESTABLISHED SELECTOR/INFINITE-ADDRESS FIREWALL.**  Let

```text
Lambda_2=<a,b,c | a^2=1,[b,c]=1,[a^b,a]=1,a^c=a^b a>
```

and put `B_n=b^n a b^(-n)`.  Tensor this address host with the shared BCS
and its one-bit Clifford selector.  On a forbidden assignment atom `E`, write

```text
R=(1+p)/2,                 A=ER,                 d=pq.
```

The selector relations give `Ed^2=JE=-E` on the marked sector, while `d`
commutes with the independent address factor.  In particular, the raw phase
is genuinely present on `E`; it is not a projective-gauge artifact.

For every terminal depth `N`, there is nevertheless an **exact finite
dimensional** model with `A!=0` and all the address and selector relations at
zero defect in which the following alternative is sharp.  For `0<=n<N`, set

```text
L_n=A(1-B_n)/2,                                             (SBO1)

Y_n=A product_(k<n)(1+B_k)/2 (1-B_n)/2.                    (SBO2)
```

Then, for distinct `n,k<N`,

```text
tau(L_n)=tau(A)/2,          tau(L_n L_k)=tau(A)/4,          (SBO3)

Y_n Y_k=0,                 tau(Y_n)=2^(-(n+1))tau(A).      (SBO4)
```

Thus the untranslated binary orbit cuts retain a fixed fraction but overlap
with the stationary Bernoulli value.  The first-hit cuts are pairwise
orthogonal, but only after the source prefix has already paid exactly the
geometric factor `2^(-n)`.  Multiplication of any address transport by `d`
does not change this conclusion: `d` preserves `E`, exchanges `ER` with
`E(1-R)`, and commutes with every `B_n`, so it preserves all support traces
and address overlaps in `(SBO3)--(SBO4)`.

Here is the finite model.  Choose `m>N` and an element `alpha` of degree `m`
over `F_2`.  On `ell^2(F_(2^m))`, represent `a` by translation by `1`, `b` by
multiplication by `alpha^(-1)`, and `c` by multiplication by
`(1+alpha)^(-1)`.  With `x^y=y^(-1)xy`, this gives
`a^b=T_alpha` and `a^c=T_(1+alpha)=a^b a`, so the Baumslag relations hold.
The translation vectors of `B_0,...,B_(N-1)` are linearly independent.
Consequently their joint character law in the permutation representation is
uniform on `C_2^N`, which gives `(SBO3)--(SBO4)`.  Tensor this representation
with any scalar BCS assignment.  Some forbidden assignment atom is then one;
on its selector factor use the Pauli realization `p=Z,q=X`.  Hence `A` has
positive trace and `d^2=-1` there, exactly as required.

The fixed presentation robustly authenticates the finite prefix, but does
not improve its trace profile.  By the quadratic filling bound for
`Lambda_2`, for fixed `N` every pairwise lamp commutator has normalized-HS
defect `O(N^2 sqrt(E))`.  Reordering the finite products in `(SBO2)` therefore
makes distinct first-hit products `O_N(sqrt(E))`-orthogonal: for `n<k`, move
the `B_n` factors together and use `(1-B_n)(1+B_n)=0`.  The two-row prefix
centralizer has the established polynomial `O_N(sqrt(E))` cost as well.
The exact finite-field models show that no such robustness estimate can turn
the geometric trace in `(SBO4)` into persistent mass.

There is also a representation-independent capacity statement.  If
`P_j=U_j P U_j^*`, `0<=j<N`, are pairwise orthogonal translates in any finite
tracial algebra, then

```text
N tau(P)=tau(sum_j P_j)<=1.                               (SBO5)
```

So an orbit construction that really preserves the selected source trace
must pay at least `1/N` before it can name `N` orthogonal destinations.  The
binary first-hit realization pays the sharper depth-wise amount `2^(-n)`.
The selector phase supplies no exception to `(SBO5)`.

In the exact perfect tracial BCS model the forbidden atom `E` is zero, so all
of `(SBO1)--(SBO2)` is vacuous, as desired.  What fails is finite-matrix
soundness: the scalar-assignment/Pauli/finite-field model above has `E!=0`
and zero presentation energy.  Therefore a successful infinite-address
return must contain a new payload-dependent relation that excludes this
finite-field multiplicity profile.  Infinite orbit naming, polynomial prefix
authentication, and the raw selector square-root do not supply that relation.

DERIVATION
selector-baumslag-finite-field-orbit-proof
