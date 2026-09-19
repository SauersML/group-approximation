---
rg: 2
id: canonical-free-double-escapes-uniform-exact-projective-folding
kind: claim
title: Uniform exact projective folding does not compactify on canonical double microstates
distinct_from:
  exact-fd-invisibility-has-no-general-hs-robustification: that treats one invisible central mark in one sofic group; this builds the adjacent-vertex double calibration and shows failure even after imposing the full canonical character of the double and a zero-constant exact projective-transfer inequality.
  sl3-arithmetic-double-finite-representations-fold: that proves exact folding for the arithmetic amalgam and leaves its canonical approximate promotion open; this is a nonarithmetic sofic counterexample to promoting exact folding by compactness alone.
  finite-swap-conjugate-moments-do-not-fold-arithmetic-double: that realizes each finite swap-moment table using residual finiteness of finite lamp products; this supplies one fixed finitely presented canonical double whose complete microstates escape exact folding.
---

**ESTABLISHED.**  Let `K` be the finitely presented sofic group and `c` its
nontrivial central involution from
`exact-fd-invisibility-has-no-general-hs-robustification`.  Thus every
finite-dimensional unitary representation `pi` of `K` satisfies

```text
pi(c)=1.                                                (CFD1)
```

Put

```text
A=K,                 C={1},
D=A *_C A=K*K,
w=i_0(c)i_1(c)^(-1).                                  (CFD2)
```

Then all of the following hold.

1. For the pair `(C<A,h=c)`, the exact projective transfer inequality has
   the strongest possible uniform constant: for every exact finite-
   dimensional `pi:A -> U(d)` and every `U in U(d)`,

   ```text
   1-|tr([U,pi(c)])|^2=0.                              (CFD3)
   ```

2. Every exact finite-dimensional representation `sigma` of the full
   double kills the fold word: `sigma(w)=1`.

3. Nevertheless `D` is sofic, hence it has full canonical normalized-HS
   microstates, and those microstates satisfy

   ```text
   tr(sigma_n(w))->0,
   |tr(sigma_n(w))| not->1.                            (CFD4)
   ```

In particular, an exact dimension-independent projective-transfer theorem,
exact folding of every finite-dimensional representation of an adjacent-
vertex double, and the full canonical character of that double do **not**
combine with compactness to yield approximate fold collapse.  Such a
promotion requires an arithmetic matrix-coordinate input absent here, for
example a correctable vertex, relative-embeddability obstruction, or a
mixed-word inequality charging the outlier sector to presentation defect.
