---
rg: 2
id: sl3-atomic-ambient-absorption-proof
kind: route
title: Match finite atomic block families by one lattice element and exhaust their trace weights
target: sl3-atomic-ambient-is-absorbed-by-lattice
requires:
  - kazhdan-generated-amenable-algebra-is-atomic
  - sl3-overlap-full-in-fd-ambient-images
---

The S-arithmetic group `A=SL_3(Z[1/p])` has property `(T)`.  Apply
`kazhdan-generated-amenable-algebra-is-atomic` to the representation `pi`
and the amenable algebra `Q=pi(A)''`.  There are pairwise inequivalent
finite-dimensional irreducible representations `sigma_j:A->U(d_j)` and
positive weights `lambda_j`, `sum_j lambda_j=1`, such that

```text
Q = direct_sum_j M_(d_j)(C),
pi(a) = direct_sum_j sigma_j(a),
tau|_Q = sum_j lambda_j tr_(d_j).                       (1)
```

Fix `a in A` and a finite set of block indices `F`.  The direct sum

```text
sigma_F = direct_sum_(j in F) sigma_j
```

is one finite-dimensional unitary representation of `A`.  By
`sl3-overlap-full-in-fd-ambient-images`,

```text
sigma_F(C)=sigma_F(A).
```

Consequently there is one element `c_F in C` -- the same element on every
block in `F` -- such that

```text
sigma_j(c_F)=sigma_j(a)                 (j in F).        (2)
```

Choose increasing finite sets `F_n` with
`sum_(j notin F_n)lambda_j->0`.  Since two unitaries are at normalized
Hilbert--Schmidt distance at most `2`, `(1)--(2)` give

```text
||pi(c_(F_n))-pi(a)||_2^2
 = sum_(j notin F_n) lambda_j
       ||sigma_j(c_(F_n))-sigma_j(a)||_(2,d_j)^2
 <= 4 sum_(j notin F_n)lambda_j
 -> 0.                                                   (3)
```

Thus `pi(a)` belongs to the `L2` closure of `pi(C)`.  A von Neumann
subalgebra of a finite tracial algebra is `L2` closed, so
`pi(a) in pi(C)''`.  Since `a` was arbitrary,

```text
pi(A)'' <= pi(C)''.
```

The reverse inclusion is immediate from `C<=A`, proving `(AA1)`.

If `N=R`, then `Q<=R` is amenable because finite von Neumann subalgebras are
the ranges of trace-preserving conditional expectations and amenability
passes to expected subalgebras.  Finally `(AA1)` makes every `pi(g)` an
element of `P=pi(C)''`, so conditional expectation fixes it and `(AA2)`
follows.  This contradicts `(EXT)` for every `g outside C` and invalidates
the proposed exterior atomic model.
