---
rg: 2
id: perfectness-kills-the-two-sheet-pauli-parity-proof
kind: route
title: Off-diagonal relators have fixed Hilbert--Schmidt cost
target: pauli-swap-coherence-reduces-to-the-commutant-gate
requires:
  - bounded-coherence-toeplitz-gauges-cannot-retain-head
  - unbounded-commutant-coherence-is-the-original-gate
---

Let `p_0,p_1` be the projections onto `H_0,H_1`. Call a matrix even if it
is block diagonal and odd if it is block off-diagonal. Products obey the
exact parity law

```text
parity(VW)=parity(V)+parity(W) mod 2,                    (PTP1)
```

and inversion preserves parity. Every `A_s` and `D_s` is even, while the
fixed swap `X` is odd. Therefore the parity of a word `q(U)` is

```text
epsilon(q)=sum_s exponent_sum_s(q) epsilon_s mod 2.     (PTP2)
```

This remains true although the diagonal factors need not commute with
`X`: conjugating an even matrix by `X` is still even.

Every odd unitary `V` has zero trace, because its two diagonal blocks
vanish. Consequently

```text
||V-I||_2^2
 = tr((V-I)^*(V-I))
 = 2-2 Re tr(V)
 = 2.                                                   (PTP3)
```

If `delta(U)<sqrt(2)`, no defining relator can evaluate to an odd
unitary. Thus `epsilon(r)=0` for every `r in R`. The assignment
`s|->epsilon_s` therefore descends from the free group on `Sigma` to a
homomorphism

```text
epsilon:G->C_2.                                         (PTP4)
```

The elementary group `G=EL_28(J)` is perfect. Indeed, for every ring
element `a` and distinct indices `i,j,k`, the Steinberg commutator
identity gives

```text
x_ij(a)=[x_ik(a),x_kj(1)].                              (PTP5)
```

The elementary transvections generate `G`, so every generator of `G`
lies in its commutator subgroup. Any homomorphism from `G` to the abelian
group `C_2` is therefore trivial. Equation `(PTP4)` implies
`epsilon_s=0` for every presentation generator.

It follows from `(PSC1)` that `Z_s=D_s in rho(F_N)'` for every `s`. The
bounded-multiplicity conclusion is now exactly
`bounded-coherence-toeplitz-gauges-cannot-retain-head`. Without a
multiplicity bound, `unbounded-commutant-coherence-is-the-original-gate`
identifies the residual problem with the unrestricted Jacobson head
modulus.

The proof also explains why it does not touch a continuous Pauli rotation.
A unitary with both diagonal and off-diagonal blocks has no exact
`C_2`-grading, so `(PTP3)` supplies no threshold and `(PTP4)` cannot be
formed.
