---
rg: 2
id: single-context-v4-exit-capacity-is-already-nonhyperlinearity
kind: claim
title: An unconditional one-context V4 exit-capacity cell is already a nonhyperlinear group
distinct_from:
  finite-subgroup-type-exclusion-is-already-nonhyperlinearity: that excludes one finite-subgroup type in every microstate; this allows every packet type but assumes a matrix-only capacity return for its three failure projections.
  exact-five-fourths-projection-return-collapses-the-packet: that rules out imposing the return as exact group-algebra conjugacy; this shows that even a finite-dimensional-only unconditional return is the whole nonhyperlinearity theorem, not a local compiler lemma.
  multiplicity-surplus-is-blind-to-the-non-ce-input: that uses substitution of an unrelated constraint system to detect loss of contextual data; this gives a direct canonical-trace proof from one embedded V4 packet.
---

Let `Gamma` be finitely presented and contain the finite full-V4 packet `T_f`
injectively.  Let `P_f,F_00,F_01,F_11 in C[T_f]` be the projections of
`(VOF4)`.  Suppose there are constants `C<infinity` and a modulus
`eta(epsilon)->0` such that every normalized-HS `epsilon`-representation of
the defining presentation admits projections `E_b` and unitary transports
`U_b` satisfying

```text
sum_b ||U_bF_bU_b^*-E_b||_2^2 <= C epsilon+eta(epsilon), (LCN1)
sum_b tau(E_b) <= tau(P_f)+C epsilon+eta(epsilon).        (LCN2)
```

Here packet words are interpreted after the standard fixed-finite-group
flexible exactification; absorbing its discarded mass into `eta` does not
change the statement.  Then `Gamma` is nonhyperlinear.

If `Gamma` were hyperlinear, take canonical microstates.  Their restrictions
to the fixed subgroup `T_f` converge to its normalized regular character, so

```text
tau_d(P_f)->tau_(T_f)(P_f)>0.                            (LCN3)
```

Apply `five-fourths-projection-surplus-pays-linear-hs-energy` with the
capacity slack from `(LCN2)`.  It gives

```text
(1/4)tau_d(P_f)
 <= sum_b ||U_bF_bU_b^*-E_b||_2^2
    +C epsilon+eta(epsilon)
 <=2C epsilon+2eta(epsilon),                             (LCN4)
```

contradicting `(LCN3)` as `epsilon->0`.

Therefore an unconditional one-context theorem of the form `(SCA1)--(SCA2)`
does not simplify the construction problem: it already constructs a
nonhyperlinear group before the BCS, PCP, or contextual gluing is used.  A
non-circular intermediate must make the capacity law conditional on a
genuinely global shared-context observable and must use that observable in
the derivation, rather than passing only local forbidden masses into copies
of the same cell.
