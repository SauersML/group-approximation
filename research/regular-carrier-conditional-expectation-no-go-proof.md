---
rg: 2
id: regular-carrier-conditional-expectation-no-go-proof
kind: route
title: Regular characters and global frame motion defeat commutant projection
target: presentation-defect-does-not-control-off-commutant-mass
requires:
  - toeplitz-folner-compressions-cannot-retain-jacobson-head
---

Equip `B(H)` with the normalized Hilbert--Schmidt inner product. Averaging
the adjoint action of a finite group is the orthogonal projection onto its
fixed space, which is `rho(F)'`. Hence

```text
(1/|F|) sum_g ||rho(g)Xrho(g)^*-X||_2^2
 = 2||X||_2^2-2||E_comm(X)||_2^2
 = 2||X-E_comm(X)||_2^2.
```

Unitary invariance identifies the summand with
`||[X,rho(g)]||_2^2` and proves `(PDC1)`.

Now use the left regular representation on `ell^2(F)`. Its group
unitaries are orthonormal:

```text
tr(lambda(x)^*lambda(y))=1_(x=y).
```

For `a in F`, conjugation averaging gives

```text
E_comm(lambda(a))
 = (1/|F|) sum_g lambda(gag^(-1))
 = (1/|a^F|) sum_(h in a^F) lambda(h).                  (RCE1)
```

Therefore

```text
||E_comm(lambda(a))||_2^2=1/|a^F|,
||lambda(a)-E_comm(lambda(a))||_2^2=1-1/|a^F|.          (RCE2)
```

For the trivial tuple `U_s=I`, every presentation relator is exactly one
and `Z_s=lambda(theta(s))^*`. Inversion preserves conjugacy-class size, so
`(RCE2)` is precisely `(PDC2)`.

A transvection over `F_2` has the unique form

```text
I+u phi,
```

where `u` is a nonzero vector, `phi` is a nonzero linear functional, and
`phi(u)=0`. There are `2^M-1` choices for `u` and
`2^(M-1)-1` nonzero choices for `phi` in its annihilator. There is no
nontrivial scalar rescaling over `F_2`, and all these matrices form one
conjugacy class in `GL_M(F_2)`. This proves `(PDC3)`.

The global-frame obstruction is purely algebraic. For any word
`q=s_1^(epsilon_1)...s_l^(epsilon_l)`,

```text
q((W A_s W^*)_s)=W q(A) W^*.
```

Thus all relator distances and all marked-word distances are unchanged.
On the other hand,

```text
A_s^*(W A_s W^*)=A_s^* W A_s W^*
```

need not commute with the carrier.

This freedom survives a frozen proper core in the regular representation.
Let `K<F` be proper and let `f:F->S^1` be a nonconstant function constant
on left `K`-cosets. The diagonal unitary `W=M_f` commutes with every
`lambda(k)`, `k in K`, but not with all of `lambda(F)`. Consequently
`U_k=Wlambda(k)W^*=lambda(k)` for every frozen core element, while the
other gauges are genuine coboundaries outside the full commutant. If the
section values generate `F`, at least one is outside: otherwise all the
ratios defining the diagonal coboundaries would be scalar, making `f` a
scalar multiple of a one-dimensional character along the generated
action. For `GL_M(F_2)` with `M>=3` there is no nontrivial character, so
`f` would be constant.

A uniform adjoint spectral gap for a generating set `S_F` would yield an
estimate of the form

```text
||X-E_comm(X)||_2^2
 <= kappa^(-1) sum_(s in S_F)||[X,rho(s)]||_2^2.        (RCE3)
```

The counterexample does not contradict `(RCE3)`: its commutators are
large. It proves that `delta(U)` does not bound the right side. Therefore
finite-group expansion is usable only after a separate argument supplies
the commutator tests; it cannot extract them from the Jacobson relators.
