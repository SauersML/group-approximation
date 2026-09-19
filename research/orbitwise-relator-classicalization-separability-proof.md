---
rg: 2
id: orbitwise-relator-classicalization-separability-proof
kind: route
title: Use the finite observable orbit and kill the finite normal relators on every branch
target: orbitwise-relator-classicalization-separates-mihailova-kernel
requires:
  - mihailova-coset-wreath-sofic-action-boundary
  - mihailova-nonseparable-coset-stabilizer
---

Since scalar defects disappear under conjugation, `Ad V_j` is an exact
homomorphism.  Clause `(ORC4)` says that for every `r in R` and `e in E`,

```text
Ad(V_j(e^(-1) r e))(A_j)=A_j.                          (ORP1)
```

Those conjugates generate `N=normal_closure_E(R)`, so

```text
Ad(V_j(n))(A_j)=A_j          (n in N).                 (ORP2)
```

Fix `g in L-N`.  From `(ORC2)`, for all sufficiently large `j`,

```text
Re tr(A_j Ad(V_j(g))(A_j)) < 1/2.
```

As `A_j` and its conjugate are unit vectors in normalized Hilbert--Schmidt
norm,

```text
||A_j-Ad(V_j(g))(A_j)||_2^2
 =2-2 Re tr(A_j Ad(V_j(g))(A_j)) >1.                  (ORP3)
```

Thus `g` moves the seed `A_j`.  If

```text
K_j={l in L:Ad(V_j(l))(A_j)=A_j},                      (ORP4)
```

then `K_j` has finite index in `L` because `O_j^L` is finite.  Equation
`(ORP2)` gives `N<K_j`, and `(ORP3)` gives `g notin K_j`.  This is subgroup
separability of `N` in `L`.

For completeness, it contradicts the intended input without using an
undecidable-membership argument.  If `N` were separable in `L`, then for
each `e in E-N` there would be finite-index `K<L` containing `N` but not
`e`.  The core of `K cap E` in `E` still contains `N` (normality of `N`) and
excludes `e`, so it gives a finite quotient of `E/N` separating `eN`.
Hence `Q` would be residually finite, contrary to its choice.

## Why seed fixing is strictly weaker

Take `E_0=F(x,y)`, `R_0={x}`, and the exact permutation representation

```text
x |-> (12),       y |-> (23)       in Sym({1,2,3}).    (ORP5)
```

On `C^3`, let `A=diag(1,1,-1)`.  The relator `x` fixes `A`, but
`yxy^(-1)=(13)` does not.  All actor products are exact, the orbit of `A` is
finite, and distinct branches have a fixed positive normalized-HS distance.
Nevertheless the normal closure of `x` is not in the stabilizer of `A`.
Thus no dimension-free estimate depending only on actor defect and
seed-relator defect can manufacture `(ORC4)`; both defects in `(ORP5)` are
already zero.

The established exact `SL_3` projective trace-square transfer closes a
different gap.  It controls an auxiliary unitary once it projectively
commutes with a Kazhdan co-dense subgroup, and its open approximate version
would at most help replace actor matrices by exact projective ones.  Exact
projective lifting makes `O_j^L` finite, but it does not say that a
Mihailova relator fixes every conjugate lamp branch.  The Kac--Moody regular
overlap machinery likewise targets simultaneous correction of actor tables;
its multiplicity/classicalization boundary does not impose `(ORC4)`.  The
finite counterpacket `(ORP5)` shows that this missing clause is algebraic,
not an unoptimized Hilbert--Schmidt constant.
