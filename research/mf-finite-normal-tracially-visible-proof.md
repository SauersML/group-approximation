---
rg: 2
id: mf-finite-normal-tracially-visible-proof
kind: route
title: Isotypic corner of the corona and its intrinsic trace
target: mf-finite-normal-tracially-visible
requires: [countable-group-mf-conventions]
artifacts:
  - GroupApproximation/Sofic/MFDefinitions.lean
  - non_mf_groups_exist.tex
---

## Why sufficient

By `countable-group-mf-conventions` the MF property of the countable group
`G` is a faithful homomorphism

```text
u : G -> U(Q),   Q = prod_n M_(d_n) / directSum_n M_(d_n),   (T1)
```

and conversely a homomorphism into the unitary group of any such corona is
the same thing as a sequence of operator-norm local models.  Everything below
happens inside `Q`, where `u` is an *exact* homomorphism; no stability theorem
for almost representations of finite groups is needed.

### 1. Isotypic projections

Because `K` is finite, `u|_K` is a genuine unitary representation of `K` in
the C-star algebra `Q`.  For `sigma in dual(K)` put

```text
P_sigma = (sigma(1)/|K|) sum_(h in K) conj(chi_sigma(h)) u(h) in Q.  (T2)
```

The central-idempotent identities of `C[K]` are algebraic consequences of
`u(h)u(h')=u(hh')`, so the `P_sigma` are pairwise orthogonal projections
summing to `1`, each commuting with `u(K)`.

`u` is injective, hence `u|_K` is faithful, hence
`intersect{ker sigma : P_sigma != 0} = 1`.  Fix `g != 1` in `K` and choose
`sigma` with `P_sigma != 0` and `sigma(g) != 1`.

### 2. An exactly invariant corner

`K` is normal in `G`, so `G` acts on `dual(K)` by `sigma^a(h)=sigma(a h a^(-1))`,
and `(T2)` gives the *exact* relation `u(a) P_sigma u(a)^* = P_(sigma^(a^(-1)))`.
Let `O` be the `G`-orbit of `sigma` and

```text
P = sum_(sigma' in O) P_(sigma') != 0,   u(a) P u(a)^* = P  (a in G). (T3)
```

Thus `a |-> P u(a)` is a homomorphism `G -> U(PQP)`.

### 3. The corner is again a matrix corona

`P` is a projection in a quotient of `prod_n M_(d_n)` by the ideal
`directSum_n M_(d_n)`.  Any self-adjoint lift `x_n` satisfies
`||x_n^2-x_n|| -> 0`, so the spectrum of `x_n` is eventually contained in
two shrinking neighbourhoods of `0` and `1`, and continuous functional
calculus produces projections `p_n in M_(d_n)` lifting `P`.  Since `P != 0`,
`p_n != 0` for infinitely many `n`; restrict to those indices and put
`r_n = rank(p_n) >= 1`.  Then

```text
PQP = prod_n M_(r_n) / directSum_n M_(r_n),                     (T4)
```

so by `countable-group-mf-conventions` the compressed homomorphism is
carried by operator-norm local models `v_n : G -> U(r_n)` whose
multiplicative defect on any prescribed finite set tends to `0`.  Note that
the corner is used with its *own* normalized trace `tr_(r_n)`: this
renormalization is the entire content of the step.

### 4. The intrinsic trace of the corner

Let `omega` be a free ultrafilter and `tau(x) = lim_omega tr_(r_n)(x_n)`, a
tracial state on `PQP`.

*Equal weights.*  For `sigma',sigma'' in O` there is `a in G` with
`(Pu(a)) P_(sigma') (Pu(a))^* = P_(sigma'')`; `Pu(a)` is a unitary of the
corner and `tau` is a trace, so `tau(P_(sigma'))=tau(P_(sigma''))`.  As
`sum_(sigma' in O) P_(sigma') = P` is the unit of the corner,

```text
tau(P_(sigma')) = 1/|O| for every sigma' in O.                  (T5)
```

*Character extraction.*  In the corner, `P_(sigma')(PQP)P_(sigma')` carries a
`sigma'`-isotypic representation of `K`: the image of the group algebra is a
copy of `M_(sigma'(1))` with `u(h)P_(sigma')` corresponding to
`sigma'(h) tensor 1`.  A trace restricted to `M_k tensor 1` is the
normalized matrix trace scaled by the total weight, so

```text
tau(u(g) P_(sigma')) = tau(P_(sigma')) chi_(sigma')(g)/sigma'(1).  (T6)
```

Summing `(T6)` over the orbit and using `(T5)`,

```text
tau(P u(g)) = (1/|O|) sum_(sigma' in O) chi_(sigma')(g)/sigma'(1). (T7)
```

Every term of `(T7)` has modulus at most `1`, and the term at `sigma'=sigma`
has real part at most `1-c(K)` because `sigma(g) != 1`.  Hence

```text
Re tau(P u(g)) <= 1-c(K)/|O| <= 1-c(K)/|K|.                     (T8)
```

The bound `(T8)` holds for every free ultrafilter, so the bounded sequence
`Re tr_(r_n)(v_n(g))` has limit superior at most `1-c(K)/|K|`.

### 5. Conclusion

Discard finitely many indices so that
`Re tr_(r_n)(v_n(g)) <= 1-c(K)/(2|K|)` and the operator-norm defect of `v_n`
on the prescribed finite set is at most the prescribed `delta`; the
normalized Hilbert--Schmidt defect is dominated by the operator-norm defect.
This is exactly tracial visibility of `g` with `c_g=c(K)/(2|K|)`, a constant
depending only on `K`.  Finally, a tracially visible element is not in the
hyperlinear residual: by `hyperlinear-elementwise-visibility` (step 1--2 of
its proof) the models above produce a homomorphism of `G` into the unitary
group of a tracial matrix ultraproduct which does not kill `g`, and that
image is a hyperlinear group.  End proof.

## Scope

The proof uses two features of the norm corona that have no tracial
analogue: a nonzero projection may be compressed to no matter how small its
rank fraction is, and compression does not increase operator-norm defects.
See `corner-renormalization-cost`.
