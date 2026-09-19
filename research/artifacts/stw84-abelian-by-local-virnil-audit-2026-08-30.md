# STW Problem LXXXIV: abelian-by-local-virtually-nilpotent audit (2026-08-30)

## Result

For a countable finite-rational-rank abelian group `A` acted on by a
countable uniformly locally virtually nilpotent group `H`, the group algebra
of `A rtimes H` has finite nuclear dimension.  If the uniform local Hirsch
bound is `s>=1` and `rank_Q(A)=r`, the explicit estimate is

```text
2 * s! * 9^(s^2) * (r+1)^2.
```

For locally finite `H` the estimate improves to `r`; for locally cyclic `H`
it improves to `2r^2+6r+4`.  Thus `C*(BS(1,n))` has nuclear dimension between
`1` and `12` for every `n>=2`.

## Dependency audit

1. **Dual dimension.**  Countability of `A` makes `A_hat` compact metrizable.
   Fourier transform gives `C*(A)=C(A_hat)`, and the Pontryagin dimension
   formula gives `dim(A_hat)=rank_Q(A)=r`.
2. **Crossed-product identification.**  Both factors are amenable and
   amenability is extension-closed, so full and reduced group and crossed
   products coincide.  The standard covariant presentation gives
   `C*(A rtimes V)=C(A_hat) rtimes V` for every subgroup `V<=H`.
3. **Published analytic bound.**  Hirshberg--Wu, arXiv:2308.12504v2,
   Corollary 10.6, gives exactly
   `2 h(V)! 9^d(V) (r+1)^2` for every action of a finitely generated
   virtually nilpotent `V` on an `r`-dimensional compact space.
4. **Uniform group parameter.**  Bass--Guivarc'h gives
   `d(V)=sum i*a_i`, while `h(V)=sum a_i` and the nilpotency class is at most
   `h(V)`.  Hence `d(V)<=h(V)^2<=s^2`.
5. **Limit passage.**  An increasing finitely generated subgroup exhaustion
   of `H` induces an increasing subgroup exhaustion of `A rtimes H`.  Reduced
   subgroup algebra maps are injective, so nuclear dimension upper
   semicontinuity applies with the uniform bound.
6. **Cyclic and finite refinements.**  Hirshberg--Wu, Advances in Mathematics
   304 (2017), Theorem 5.1, gives `2r^2+6r+4` for every `Z`-action.  Their
   Theorem 3.4 and Proposition 1.6 give dimension at most `r` for every
   finite-group action, not merely a finite cyclic action.
7. **Lower bound.**  Direct commutator calculation gives
   `(A rtimes H)_ab=(A/[A,H]) direct_sum H_ab`; the established abelianization
   obstruction then gives the stated lower bound.

## Boundary and novelty

This is a closure theorem, not a solution of unrestricted Problem LXXXIV.
It is outside the existing local-virtual-polycyclic route: `BS(1,n)` itself
is finitely generated but not virtually polycyclic.  It is also outside the
locally-finite-kernel and wreath-product routes because its normal kernel is
the torsion-free, infinitely generated finite-rank group `Z[1/n]` and the
action is expanding.

The argument does not cover an acting group whose local Hirsch lengths are
unbounded, nor an abelian kernel of infinite rational rank.  Both failures
are real failures of uniformity in the displayed estimates, not hidden uses
of finite generation.
