# Exact counterexample to arbitrary traced-coordinate Kazhdan transport

**Date:** 2026-08-19  
**Status:** direct consequence of the established nine-leaf Leavitt configuration.  This note corrects an overgeneralized Cairn theorem; it does **not** refute the finite-matrix/operator-norm Kazhdan transport theorem.

## 1. The claimed generalization

`finite-traced-kazhdan-transport` currently asserts the following for arbitrary tracial coordinates, allowing the multiplicative defect in normalized `L^2`:

- `Gamma` has property `(T)`;
- `s iota(Gamma) s^{-1} <= iota(Gamma)`;
- `U_k : H -> U(A_k)` is asymptotically multiplicative;
- `x_k` asymptotically commutes with `U_k(iota(Gamma))`.

It concludes that

```text
U_k(s) x_k U_k(s)^*
```

also asymptotically commutes with the original `Gamma` image.

For arbitrary finite tracial von Neumann coordinates this statement is false even at **zero defect**.

## 2. The nine-leaf exact counterexample

Use the established configuration `openai-nine-leaf-leavitt-configuration` over
`R=L_(F_2)(1,2)`:

```text
G      = EL_D(R),
Gamma  = EL_alpha(R),
J      = V_(1000),
u in G,
```

with

```text
Gamma has property (T),
u Gamma u^{-1} <= Gamma,
[Gamma,J]=1,
u J u^{-1}=V_(0001) <= Gamma,
J ~= V.
```

The subgroup `uJu^{-1}` is nonabelian because it is a copy of Thompson's `V`.  Choose

```text
w,gamma in uJu^{-1}
```

with `[w,gamma] != 1`, and put

```text
j=u^{-1} w u in J.
```

Then `j` commutes with every element of `Gamma`, whereas `w` does not commute with `gamma`.

Let

```text
M=L(G)
```

with its canonical finite trace, and let `lambda:G->U(M)` be the left regular representation.  Take the constant coordinate family

```text
A_k=M,
U_k=lambda,
x_k=lambda(j),
s=u.
```

Every multiplicative defect is exactly zero and `x_k` is uniformly bounded.  Since `[j,Gamma]=1`,

```text
[x_k, U_k(Gamma)]=0
```

exactly.  But

```text
U_k(u) x_k U_k(u)^* = lambda(u j u^{-1})=lambda(w),
```

and

```text
[lambda(w),lambda(gamma)] != 0
```

because the left regular representation is faithful and `[w,gamma] != 1` in `G`.

Thus the conclusion of `finite-traced-kazhdan-transport` fails with zero input defect.

## 3. Where the printed proof breaks

The route `finite-traced-kazhdan-transport-proof` puts the Kazhdan fixed-space projection in the operator algebra generated on `L^2(M)` by left and right multiplication and then invokes finiteness to turn

```text
P <= Ad(lambda(u)) P Ad(lambda(u))^*
```

into equality.

For a finite factor `M`, however,

```text
M' = J M J,
M vee J M J = B(L^2(M)),
```

because `(M vee M')' = M' cap M = Z(M)=C`.  The generated **von Neumann algebra** is therefore not finite when `L^2(M)` is infinite-dimensional.  The recent formal tracial-commutation work in the repository records this same mechanism: for a factor the left and right actions generate all of `B(H)`.

This does not contradict the valid finite-coordinate argument.  In a matrix coordinate, the adjoint Hilbert space is finite-dimensional and equal-rank spectral projections can be compared.  The missing issue for hyperlinearity is that normalized-HS multiplicative defect only controls the adjoint action on average; exceptional operator-space directions of vanishing relative dimension can carry the obstruction.  This is exactly the finite-multiplicity problem isolated by the atlas one-cut and spectral-shrinkage lanes.

## 4. Correct scope after the repair

What survives:

1. `kazhdan-asymptotic-commutant-transport` in its finite-matrix/operator-norm form;
2. its finite-stage equal-rank proof;
3. the atlas finite-multiplicity and spectral-range-Hall programmes, whose purpose is precisely to recover enough finite-coordinate structure under normalized-HS defects.

What does not survive is the unrestricted statement that the same transport holds in arbitrary tracial coordinates, or that an arbitrary 2-norm asymptotic representation can be passed to a finite tracial ultraproduct and closed by finiteness of `M vee JMJ`.

The counterexample is useful beyond graph hygiene: it proves that any successful hyperlinear argument must retain a genuinely finite-coordinate invariant.  There is no abstract finite-von-Neumann-algebra transport theorem waiting to replace the current matrix extraction gate.
