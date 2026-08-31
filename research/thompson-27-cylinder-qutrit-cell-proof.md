---
rg: 2
id: thompson-27-cylinder-qutrit-cell-proof
kind: route
title: Realize the extraspecial packet by affine permutations of 27 prefix leaves
target: thompson-27-cylinder-qutrit-cell-is-fd-invisible
requires:
  - two-qutrit-controlled-bases-give-proper-multipath-marginal
  - finite-type-partitions-obey-support-phase-balance
  - thompson-v-has-no-nontrivial-fd-unitary-representation
  - leavitt-cylinder-swaps-generate-thompson-in-el
  - leavitt-gl-equals-el-and-perfect-unit-group
  - thompson-v-lifts-through-binary-leavitt-steinberg-cover
  - finite-support-corner-localizes-obstruction
---

## 1. The fixed prefix packet

The words

```text
0, 10, 110, ..., 1^25 0, 1^26
```

are prefix-free.  Their Kraft sum is

```text
sum_(r=0)^25 2^(-(r+1)) + 2^(-26)=1,
```

so they form a maximal binary prefix code `D_27`.  Any permutation of
these words, followed by the identity on the infinite tail, is an element of
Thompson's `V`.  These elements form a subgroup
`Sym(D_27) isomorphic to S_27`.

Label the leaves by `Omega=F_3^2 x F_3` and use the permutations in
`(TVQ2)`.  They visibly have order three, `J` is central, and generators
with different subscripts commute.  On a point `(u,s)` one has

```text
X_i Z_i(u,s)   =(u+e_i,s-u_i),
J Z_i X_i(u,s)=(u+e_i,s-u_i),
```

so `X_i Z_i=J Z_i X_i`.

Every word in these generators rewrites to a normal form

```text
J^c X_1^(r_1) X_2^(r_2) Z_1^(t_1) Z_2^(t_2).           (TVQ10)
```

Its action determines `r=(r_1,r_2)` from the translation of `u`, then
determines `t=(t_1,t_2)` and `c` from the affine function added to
`s`.  Thus the `3^5` normal forms give distinct permutations.  The
presentation in `(TVQ3)` gives at most `3^5` forms, so the generated
group is exactly the claimed extraspecial group `F), faithfully embedded
in `V).

## 2. The nine finite types

For `C=<J,Z_1>`, let `chi_a(J)=omega` and
`chi_a(Z_1)=omega^a`.  Direct Fourier expansion gives

```text
p_(a,b)
 =(1/27) sum_(j,k,t in F_3)
   omega^(-j-ak-bt) J^j Z_1^k B_a^t.                  (TVQ11)
```

For fixed `a`, summing over `b` kills the terms with `t!=0`:

```text
sum_b p_(a,b)
 =(1/9) sum_(j,k in F_3) omega^(-j-ak)J^j Z_1^k
 =z_(C,chi_a).                                         (TVQ12)
```

Summing `(TVQ12)` over `a` then kills the terms with `k!=0` and
leaves

```text
sum_(a,b) p_(a,b)
 =(1/3) sum_(j in F_3) omega^(-j)J^j
 =q.                                                   (TVQ13)
```

For fixed `a), the three `p_(a,b)` are distinct character idempotents
of the abelian group `A_a` and are orthogonal.  For `a!=c), the
projections `p_(a,b)` and `p_(c,d)` lie below the distinct orthogonal
character idempotents `z_(C,chi_a)` and `z_(C,chi_c)).  This proves all
of `(TVQ5)`.

The group `K=<J,X_1,Z_1>` is the order-27 Heisenberg group.  Its unique
three-dimensional irreducible representation with central character
`omega` has central idempotent `e_(<J>,omega)), proving
`q=z_(K,pi_omega)`.  Likewise, in `F` the `omega`-central block is
the unique nine-dimensional spin block, so

```text
q C[F] q isomorphic to M_9(C).                          (TVQ14)
```

Each `p_(a,b)` has canonical trace `1/27`.  Hence `P` has trace
`1/9`, while `q` has trace `1/3`; both `P` and `q-P` are
nonzero.  Since a nontrivial proper projection in the full matrix algebra
`(TVQ14)` is not central, `P` remains noncentral after the inclusion
`C[F] subset C[V]`.  This proves `(TVQ6)--(TVQ7)`.

The earlier two-qutrit classification also shows that `P` is not a marked
central type of any subgroup of this finite packet `F`.  We do not need,
and do not assert, the stronger statement that no unrelated finite subgroup
of all of `V` could rename `P`; the load-bearing conclusions here are
its explicit three-chart expression and noncentrality.

## 3. Exact three-phase support balance

For different `a,c` one has

```text
A_a intersect A_c=C,                  C subset K.        (TVQ15)
```

Also `A_a intersect K=C`.  Therefore every support element outside `K`
belongs to exactly one `A_a` and has the unique form in `(TVQ8)` with
`t!=0`.  Formula `(TVQ11)` shows that its coefficients in the only
three incident atoms are

```text
(omega^(-j-ak)/27) (1,omega^(-t),omega^(-2t)).          (TVQ16)
```

Because multiplication by nonzero `t in F_3` permutes the three cube-root
phases, these coefficients have equal modulus and sum to zero.  Thus the
outside-`K` cancellation is an exact three-way collision, not hidden
pairing.  This is the strict local alternative left open by support phase
balance.

## 4. Finite-dimensional invisibility in the three hosts

Let `rho` be a finite-dimensional unitary representation of `V).
The Thompson minimal-almost-periodicity theorem makes its restriction
trivial.  In particular `rho(J)=I), and hence

```text
rho(q)=(1/3)(1+omega^(-1)+omega^(-2))I=0.               (TVQ17)
```

The cylinder-swap embedding puts this copy of `V` in the binary Leavitt
unit group.  Prefix-code self-similarity identifies that unit group with
`GL_4(L_(F_2)(1,2))`, and `GL_4=EL_4`.  Therefore any
finite-dimensional representation of `EL_4` restricts to a
finite-dimensional representation of the embedded `V`, and the same
calculation proves `(TVQ17)`.

For `n>=5`, the established splitting of the Steinberg central extension
gives an injective lift `V->St_n(L_(F_2)(1,2))`.  Restricting any
finite-dimensional representation to this lifted copy again proves
`(TVQ17)`.  Since every `p_(a,b)` and `P` lies below `q`, all of
them are annihilated as well.

## 5. Why the construction stops locally

All coefficients in `q`, the nine `p_(a,b)), and `P` belong to
`C[F]`, where `F` is finite.  The left regular representation of `F`
is an exact finite-dimensional model; its canonical trace gives
`tau(q)=1/3`, so it does not annihilate the selected corner.  It need not
extend to a representation of `V), and this is precisely the difference
between ambient fd-invisibility and a support-level obstruction.

More generally, if all projections and overlap coefficients of a proposed
completed atlas remain in the group algebra of the fixed code-permutation
group `Sym(D_27)`, their support subgroup is finite and hence hyperlinear.
The finite-support localization theorem then rules out a no-CE atlas there.
The first potentially load-bearing extension must therefore use an element
outside this fixed symmetric group and must impose a mixed equality, not just
transport one copy of `P` to another.  That is the next object stated in
the claim.
