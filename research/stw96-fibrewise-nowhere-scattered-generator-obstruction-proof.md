---
rg: 2
id: stw96-fibrewise-nowhere-scattered-generator-obstruction-proof
kind: route
title: Central characters localize irreducible representations to fibres
target: stw96-fibrewise-nowhere-scattered-generator-obstruction
requires:
  - stw96-extension-lifts-generator-obstruction
---

Let `pi:E -> B(H)` be irreducible.  Since the structure map sends `C(X)` into
the centre of `E`, Schur's lemma gives a point `x in X` such that

```text
pi(fa) = f(x)pi(a)       (f in C(X), a in E).
```

Thus `C_0(X minus {x})E` is contained in `ker(pi)`, and `pi` factors as an
irreducible representation `pi_x` of the fibre `E_x`.

By Thiel--Vilalta, [Theorem
3.1(6)](https://doi.org/10.4171/JNCG/526), a C*-algebra is nowhere scattered if
and only if it has no nonzero irreducible GCR representation.  Since `E_x` is
nowhere scattered, `pi_x(E_x)` has zero intersection with `K(H)`.  The equality
`pi(E)=pi_x(E_x)` therefore shows that `pi` is not GCR.  This holds for every
irreducible `pi`, so the same characterization proves that `E` is nowhere
scattered.

The fibre quotient `q_x:E -> E_x` and
`stw96-extension-lifts-generator-obstruction` show that any
finite obstruction in one fibre lifts to a finite obstruction in `E`.

For the stated family, every fibre of `C(X) tensor_min A` is `A`, which is
nowhere scattered, and evaluation at any `x` sends `1 tensor F` to the fixed
Elliott--Li--Niu obstruction.  Separability follows from metrizability of `X`,
and nuclearity follows because both `C(X)` and the AH algebra `A` are nuclear.
Finally, an element central in `C(X,A)` takes values in `Z(A)=C1`, since `A` is
unital and simple; hence the centre is exactly `C(X) tensor 1`.
