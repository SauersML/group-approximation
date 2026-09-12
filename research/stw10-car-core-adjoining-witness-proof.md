---
rg: 2
id: stw10-car-core-adjoining-witness-proof
kind: route
title: Extract a finite norm obstruction and adjoin one generator for the weakly dense CAR core
target: stw10-x2-reduces-to-finitely-generated-weakly-dense-witnesses
requires: []
artifacts:
  - research/artifacts/stw10-amenable-trace-frontier-2026-08-30.md
---

Quasidiagonality passes to C-star subalgebras, so assertion 1 implies 2, and
2 implies 3.  For the converse, it is useful first to prove the norm-local
statement directly.  Suppose every finitely generated unital subalgebra of
`R` is quasidiagonal.  Given a finite set `F subset R` and `epsilon>0`, put

```text
B=C*(1,F).
```

Choose a u.c.p. matrix map on the quasidiagonal algebra `B` which is
`epsilon`-multiplicative and `epsilon`-isometric on the finite set needed for
`F`.  Arveson's extension theorem extends this map to a u.c.p. map on `R`
without changing its values on `B`.  Hence the same operator-norm estimates
hold on `F`.  Voiculescu's finite-set characterization makes `R`
quasidiagonal.  This proves `2=>1`, including for the norm-nonseparable
algebra `R`.

Now argue contrapositively and keep the obstruction finite.  If `R` is not
quasidiagonal, the preceding paragraph gives a finite `F subset R` for which
`B=C*(1,F)` is not quasidiagonal.  Realize `R` as the tracial weak closure of
its canonical CAR algebra `D`.  Topping's single-generation theorem for UHF
algebras, recalled in Thiel--Winter, [*The generator problem for Z-stable
C-star algebras*, Section 1](https://arxiv.org/abs/1201.3879), supplies
`g in D` with `D=C*(1,g)`.  Set

```text
A=C*(B,g)=C*(1,F,g).
```

Then `A` is finitely generated and contains `D`, so its weak closure is `R`.
It contains the nonquasidiagonal subalgebra `B`; since quasidiagonality passes
to subalgebras, `A` is not quasidiagonal.  This proves the contrapositive of
`3=>1` and the claimed normal form.

It remains to audit the trace assertions.  The restriction
`tau=tau_R|A` is faithful, and its GNS closure is `R` because `A` is weakly
dense.  The trace of `R` is amenable, with u.c.p. models multiplicative in
normalized Hilbert--Schmidt norm; restricting those maps to `A` preserves
amenability.  If `tau` were a quasidiagonal trace, its faithfulness and
Brown's Proposition 4.1.3 argument would make `A` quasidiagonal, a
contradiction.  Thus `tau` is amenable but not quasidiagonal.  Finiteness of
`R` makes every unital C-star subalgebra, including `A`, stably finite.

Finally, the faithful-amenable-trace theorem of
Tikuisis--White--Winter/Gabe says that a faithful amenable trace on a
separable exact UCT C-star algebra is quasidiagonal.  Since `A` is finitely
generated and `tau` is not quasidiagonal, `A` cannot be both exact and UCT.

**Trust boundary.**  The CAR algebra is weakly dense, not norm dense.  Its
finite-dimensional stages therefore provide the amenable trace's `2`-norm
models but do not approximate the added obstruction set `F` in operator
norm.  No inference from hyperfiniteness to quasidiagonality is made; the
claim only packages the exact form a failure of that inference must take.
