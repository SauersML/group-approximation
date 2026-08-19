# Finite regular normalizers round without dimension loss

Date: 2026-08-13

## 1. Purpose

The relative Burton--Kun--Thom program needs to convert coherent unitary
normalizers of finite lamp models into combinatorial normalizers.  This note
proves the finite-dimensional part of that conversion with constants
independent of both the number and the multiplicity of the spectral blocks.

The theorem removes a possible analytic loss: once one has a *single finite
elementary abelian lamp group* which is approximately normalized by all the
required quotient matrices, block normalizer rounding and coherence are
automatic.  The remaining issue is the global recovery of such a common
finite lamp group from increasing, non-invariant lamp windows.

Throughout,

```text
||T||_(2,d)^2 = Tr(T* T)/d.
```

## 2. Rounding one block transport

Let

```text
1 = sum_(i in I) p_i = sum_(i in I) q_i
```

be two orthogonal decompositions of `C^d`, with

```text
rank(p_i)=rank(q_(alpha(i)))
```

for a permutation `alpha` of `I`.  Let `U` be unitary and set

```text
eta^2 = sum_i ||U p_i U* - q_(alpha(i))||_(2,d)^2.      (FRN1)
```

**Theorem 1 (dimension-free block rounding).**  There is a unitary `V` such
that

```text
V p_i V* = q_(alpha(i))                    for every i, (FRN2)
||U-V||_(2,d) <= eta.                                  (FRN3)
```

**Proof.**  Put

```text
T = sum_i q_(alpha(i)) U p_i.
```

The summands occupy mutually orthogonal matrix corners.  If

```text
ell_i = tr_d((1-q_(alpha(i))) U p_i U*),
```

then the projection identity gives

```text
||U p_i U* - q_(alpha(i))||_2^2 = 2 ell_i,             (FRN4)
||U-T||_2^2 = sum_i ell_i = eta^2/2.                   (FRN5)
```

Take the polar decomposition of each square block
`q_(alpha(i)) U p_i`, and extend its polar partial isometry across its kernel
to a unitary map from `p_i C^d` onto `q_(alpha(i)) C^d`.  The direct sum of
these maps is a unitary `V` satisfying `(FRN2)`.  If the singular values of a
block are `s_j in [0,1]`, its contribution to `||T-V||_2^2` is
`sum_j(1-s_j)^2/d`, whereas its leakage is
`sum_j(1-s_j^2)/d`.  Hence

```text
||T-V||_2^2 <= sum_i ell_i.                            (FRN6)
```

Moreover, `U-T` is Hilbert--Schmidt orthogonal to `T-V`: the former lies in
the off-matching corners and the latter in the matching corners.  Combining
`(FRN5)--(FRN6)` gives

```text
||U-V||_2^2
 = ||U-T||_2^2 + ||T-V||_2^2
 <= 2 sum_i ell_i = eta^2.
```

This proves the theorem.  End proof.

## 3. Fourier form for a finite abelian lamp group

Let `B` be a finite abelian group and let `rho` be a multiple of its regular
representation,

```text
rho = lambda_B tensor 1_r.
```

In Fourier coordinates its minimal spectral projections `p_chi`,
`chi in B^`, all have rank `r`.  For `beta in Aut(B)`, put

```text
beta^(chi)=chi composed with beta^(-1).
```

For a unitary `U`, vector-valued Fourier Parseval gives the exact identity

```text
sum_(chi in B^) ||U p_chi U* - p_(beta^(chi))||_2^2
 = (1/|B|) sum_(b in B)
     ||U rho(b) U* - rho(beta(b))||_2^2.                (FRN7)
```

Indeed both sides are Parseval norms of the Fourier transform of the family

```text
Delta_b = U rho(b) U* - rho(beta(b)).
```

Apply Theorem 1 to `(FRN7)`.

**Corollary 2 (regular normalizer rounding).**  If

```text
epsilon^2 = (1/|B|) sum_(b in B)
  ||U rho(b) U* - rho(beta(b))||_2^2,
```

then there is a unitary `V` with

```text
V p_chi V* = p_(beta^(chi))             for every chi,
||U-V||_2 <= epsilon.                                   (FRN8)
```

Thus `V` is block monomial in Fourier coordinates.  The estimate has no
factor depending on `|B|`, `r`, or `d=r|B|`.

If covariance is known only on a generating set
`b_1,...,b_m` of an elementary abelian `2`-group, and every generator has
defect at most `delta`, telescoping gives defect at most `m delta` on every
element.  Consequently `(FRN8)` holds with

```text
epsilon <= m delta.                                    (FRN9)
```

This loss is harmless in a diagonal microstate construction, where the
accuracy can be chosen after the finite lamp rank `m` is fixed.

## 4. Coherence descends to Hamming coherence

Return to a fixed equal-rank block decomposition

```text
C^d = direct_sum_(i in I) H_i,
dim(H_i)=r.
```

Every block-monomial unitary `V` has a block permutation
`bar(V) in Sym(I)`.  If `V,W` are block monomial, then

```text
bar(VW)=bar(V)bar(W).                                  (FRN10)
```

For block-monomial `V,W`, orthogonality of distinct target blocks gives

```text
||V-W||_(2,d)^2
 >= 2 d_H(bar(V),bar(W)),                              (FRN11)
```

where `d_H` is normalized Hamming distance on `I`.  Therefore rounded
normalizers `V_g` satisfy

```text
d_H(bar(V_g)bar(V_h),bar(V_(gh)))
 <= (1/2)||V_g V_h-V_(gh)||_2^2.                       (FRN12)
```

If `||U_g-V_g||_2<=epsilon_g`, telescoping yields

```text
||V_g V_h-V_(gh)||_2
 <= ||U_g U_h-U_(gh)||_2
      +epsilon_g+epsilon_h+epsilon_(gh).               (FRN13)
```

Thus coherent unitary multiplication becomes coherent permutation
multiplication with no dimension-dependent constant.

For `B=(C_2)^m`, the block labels form the vector space `B^`.  The block
permutation induced by an automorphism is linear.  Two distinct linear maps
`L_1,L_2:B^->B^` agree on the kernel of the nonzero linear map `L_1-L_2`, a
subspace of codimension at least one.  Hence

```text
L_1 != L_2  ==>  d_H(L_1,L_2) >= 1/2.                 (FRN14)
```

Consequently any defect in a prescribed finite multiplication table which
is strictly below `1/2` is actually zero.  If the quotient group is finitely
presented, rounded linear images of its generators whose relators have
Hamming defect below `1/2` define an exact homomorphism into a finite general
linear group.

## 5. What this proves in the Kun--Thom program

Suppose a hypothetical hyperlinear model of the Kun--Thom wreath product
supplied, at each coordinate, one finite elementary abelian group `B_n` with
regular multiplicity, together with quotient matrices `U_(g,n)` such that:

1. every required `U_(g,n)` approximately normalizes `rho_n(B_n)`;
2. its induced action on `B_n` agrees with the prescribed lamp conjugations
   on the finite test window;
3. the `U_(g,n)` satisfy the quotient relators in normalized Hilbert--Schmidt
   norm.

Corollary 2 and `(FRN12)--(FRN14)` then produce an exact finite linear
quotient model.  In the explicit Kun--Thom pair, the distinguished lamp is
fixed by the image of `Gamma` but moved by an element of the normal closure
of `Gamma`; this contradicts their finite-quotient normality theorem.  In
particular, there is no additional obstruction coming from block phases,
large multiplicities, or accumulation of a dimension-dependent rounding
constant.

The hypotheses above are not yet recovered from the known Burton theorem.
Burton--Chaudkhari--Juschenko--Muliarchyk permutationize the amenable lamp
restriction on each prescribed finite set.  A finite lamp patch is not
invariant under the quotient generators, and adjoining its generator images
repeatedly generally produces an infinite orbit.  The missing statement is
therefore precisely:

> recover a common finite elementary abelian coordinate model which is
> approximately normalized by the finite quotient generating set, while
> preserving the canonical lamp trace.

This is the global relative-normalizer recovery gate.  The present theorem
shows that once that gate is crossed, the rest of the passage to an exact
finite quotient is dimension-free and elementary.

## 6. Audit against false shortcuts

- Individual unitary equivalence of arbitrary permutation representations is
  not enough because of Gassmann equivalence.  The regular-character
  hypothesis is essential.
- Rounding separately on different finite lamp patches does not produce a
  common block decomposition, so `(FRN10)` cannot be invoked.
- A Folner exhaustion of coordinate lamps cannot repair this: adding one
  independent `C_2` coordinate changes half of the regular character blocks.
- Abstract finite-von-Neumann-algebra normality is insufficient.  The proof
  uses equal finite ranks and the discrete block label set at each matrix
  coordinate.

The result is therefore a proved finite-dimensional lemma, not a claim that
the relative Burton gate has already been solved.

## 7. Why finite-dimensional saturation does not close the gate

There is a tempting but invalid last step: start with a finite lamp window,
adjoin all of its translates under the quotient generators, and argue that
finite matrix dimension makes this process stop.  Hyperlinear approximation
does not provide a dimension bound before the test window is chosen.  A lamp
window of rank `m` has an exact regular model in dimension `2^m`, with an
arbitrary further multiplicity.  On the next diagonal coordinate the model
may simply use a much larger dimension and keep every newly exposed lamp
independent.  Thus no individual coordinate is required to contain the whole
infinite orbit, and there is no pigeonhole closure uniform in the microstate
index.

Equally, stopping after the generated finite-dimensional algebra ceases to
grow only produces a coordinate-dependent relation among lamps outside the
protected trace window.  Canonical trace separation says that each *fixed*
nontrivial lamp word eventually has trace zero; it gives no uniform control
over relations whose word length grows with the coordinate.  Treating such a
moving relation as a genuine relation in `A` interchanges the two quantifiers
in the definition of a hyperlinear approximation.

Accordingly, any successful saturation proof needs a uniform ingredient--for
example a dimension-independent Kazhdan recovery theorem which turns the
pointwise invariant ultraproduct lamp algebra into coordinatewise invariant
finite lamp algebras.  That is exactly the global gate, not a consequence of
finite dimensionality alone.
