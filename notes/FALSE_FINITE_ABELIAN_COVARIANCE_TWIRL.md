# Finite abelian subgroup twirling exactly rounds averaged covariance

Date: 2026-08-12

## 1. Outcome

The genuinely approximate tangent-covariance gate left by
`FALSE_KAZHDAN_CYCLIC_SEED_TRACIAL_EXTENSION.md` has an exact finite Fourier
decomposition.

Let `W` be a finite abelian group, let `K<=W`, and let `(M,tau)` be a finite
tracial von Neumann algebra.  For two representations

```text
Phi_i:W->U(M),       i=0,1,                           (FAT1)
```

and `T in L^2(M,tau)`, define the subgroup-averaged intertwining defect

```text
E_K(T)^2=(1/|K|) sum_(k in K)
              ||Phi_0(k)T-T Phi_1(k)||_2^2.          (FAT2)
```

Write `p_i(chi)` for the spectral projection of `Phi_i` at
`chi in dual(W)`.  Then

```text
E_K(T)^2
 =2 sum_(chi|K != psi|K)
       ||p_0(chi) T p_1(psi)||_2^2.                  (FAT3)
```

Equivalently, if

```text
Q_K(T)=sum_(chi|K=psi|K) p_0(chi)T p_1(psi),         (FAT4)
```

then `Q_K` is the orthogonal projection onto the exact `K`-intertwiner
space and

```text
||T-Q_K(T)||_2=E_K(T)/sqrt(2).                       (FAT5)
```

The identity has no minimum root-spacing, exponent, dimension, or matrix
condition-number loss.  In matrices, if the two restricted character
multiplicity vectors agree, every unitary `T` is within distance at most
`E_K(T)` of an exact unitary `K`-intertwiner.

Thus full-subgroup averaged covariance is stable with a universal constant.
The surviving Frobenius construction must exploit the strict weakness of
generatorwise covariance: it must put its defect on labels escaping every
fixed tested window.  If its estimates can be upgraded to an average over
the generated finite tangent subgroup, the construction collapses to exact
covariance immediately.

## 2. Spectral projections

For `chi in dual(W)`, put

```text
p_i(chi)=|W|^(-1) sum_(w in W) conjugate(chi(w))Phi_i(w).
                                                               (FAT6)
```

These are pairwise orthogonal projections with sum `1`, and

```text
Phi_i(w)p_i(chi)=chi(w)p_i(chi).                     (FAT7)
```

The rectangular `L^2` blocks

```text
p_0(chi)L^2(M,tau)p_1(psi)                           (FAT8)
```

are mutually orthogonal.  Therefore

```text
T=sum_(chi,psi) p_0(chi)T p_1(psi)                  (FAT9)
```

orthogonally in `L^2`.

On the `(chi,psi)` block, the `k`th intertwining difference is multiplication
by the scalar `chi(k)-psi(k)`.  Hence

```text
E_K(T)^2
 =sum_(chi,psi) ||p_0(chi)T p_1(psi)||_2^2
    (1/|K|)sum_(k in K)|chi(k)-psi(k)|^2.            (FAT10)
```

Character orthogonality on `K` gives

```text
(1/|K|)sum_(k in K)|chi(k)-psi(k)|^2
 =0,  if chi|K=psi|K,
 =2,  otherwise.                                    (FAT11)
```

Equations `(FAT10)--(FAT11)` prove `(FAT3)`.  The range of `(FAT4)` is
exactly the set of `X in L^2(M,tau)` satisfying

```text
Phi_0(k)X=X Phi_1(k),       k in K.                  (FAT12)
```

Thus `(FAT4)` is its orthogonal projection and `(FAT5)` follows.

## 3. Matrix multiplicities and unitary rounding

Now take `M=M_d(C)` with normalized trace and let `T` be unitary.  Group the
spectral projections by restricted character `theta in dual(K)`:

```text
P_i(theta)=sum_(chi|K=theta)p_i(chi),
a_theta=rank(P_0(theta))/d,
b_theta=rank(P_1(theta))/d.                          (FAT13)
```

Let

```text
off_K(T)=sum_(theta!=omega)
             ||P_0(theta)T P_1(omega)||_2^2
         =E_K(T)^2/2.                                (FAT14)
```

The diagonal block at `theta` has squared Hilbert--Schmidt mass at most
`min(a_theta,b_theta)`.  Since the total mass is one,

```text
off_K(T)
 >=1-sum_theta min(a_theta,b_theta)
 =1/2 sum_theta |a_theta-b_theta|.                   (FAT15)
```

Consequently

```text
sum_theta |a_theta-b_theta|<=E_K(T)^2.               (FAT16)
```

So small averaged covariance forces the two restricted multiplicity vectors
to agree after deleting a corner of normalized dimension at most
`E_K(T)^2/2` from each side.

Suppose now that `a_theta=b_theta` for every `theta`.  For every diagonal
block

```text
A_theta=P_0(theta)T P_1(theta),                      (FAT17)
```

choose a unitary polar completion

```text
V_theta:P_1(theta)C^d -> P_0(theta)C^d               (FAT18)
```

maximizing `Re Tr(V_theta^* A_theta)`, and put

```text
V=sum_theta V_theta.                                 (FAT19)
```

Then `V` is a unitary exact `K`-intertwiner.  All singular values of
`A_theta` lie in `[0,1]`, so its nuclear norm is at least its squared
Hilbert--Schmidt norm.  Hence

```text
Re tau(V^*T)
 =d^(-1)sum_theta ||A_theta||_1
 >=sum_theta ||A_theta||_2^2
 =1-off_K(T).                                        (FAT20)
```

It follows that

```text
||T-V||_2^2
 =2-2 Re tau(V^*T)
 <=2 off_K(T)=E_K(T)^2,                              (FAT21)
```

and therefore

```text
||T-V||_2<=E_K(T).                                   (FAT22)
```

This proves the asserted unitary rounding theorem.

## 4. Twisted covariance

Let `alpha in Aut(W)`.  Replacing `Phi_0(k)` in `(FAT2)` by
`Phi_0(alpha(k))` gives the identical formula with the matching condition

```text
chi o alpha|K=psi|K.                                 (FAT23)
```

Thus, for a proposed implementer `U` of `alpha`, the full-subgroup RMS
covariance defect is exactly twice its mass outside the Fourier blocks
permitted by `alpha`.  If the corresponding restricted multiplicities
match, `(FAT22)` rounds `U` to an exact implementer of `alpha|K`.

This is the finite-abelian analogue of the full Weyl twirl, but it applies
to arbitrary character multiplicities and produces the nearest exact
intertwiner rather than only a scalar commutant estimate.

## 5. Consequence for the current FALSE gate

The paired Fourier/Frobenius proposal tests covariance only on the fixed
positive presentation window.  The inverse Laurent label is absorbed in
each finite quotient by a positive word whose length tends to infinity.
The subgroup twirl proves the precise obstruction to promoting those local
estimates:

* if the covariance error tends to zero after averaging over the whole
  finite tangent subgroup generated by the tested labels, exact covariance
  follows on a `1-o(1)` corner by `(FAT5)--(FAT16)`;
* when the restricted multiplicities match, the implementer itself rounds
  to an exact covariant unitary by `(FAT22)`;
* the cyclic-seed Kazhdan theorem then propagates common-positive agreement
  to the inverse fold and kills the marked discrepancy.

Therefore a successful model must have a genuine local-to-global failure:
generatorwise covariance tends to zero, but the subgroup-averaged quantity
`(FAT2)` stays macroscopic on the growing tangent subgroup.  This is a
finite, exactly computable statistic for candidate Frobenius models and a
sharper target than raw word-length distortion alone.
