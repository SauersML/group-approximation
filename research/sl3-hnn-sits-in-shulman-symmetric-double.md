---
rg: 2
id: sl3-hnn-sits-in-shulman-symmetric-double
kind: claim
title: The arithmetic centralizer HNN group embeds in a symmetric amalgamated double
artifacts:
  - research/artifacts/sl3-hnn-symmetric-double-mf-firewall-2026-08-21.md
distinct_from:
  hnn-hyperlinearity-is-amalgamated-free-haar-unitary: that gives the exact tracial matrix-ultraproduct criterion for hyperlinearity of the HNN group; this is an operator-norm C-star permanence firewall obtained by embedding the whole group in a larger symmetric double.
  sl3-hnn-admits-no-amalgamated-free-haar-unitary: that is the open negative canonical-trace matrix-model statement which would prove non-hyperlinearity; the MF conclusion here is trace-blind and therefore neither proves nor refutes that statement.
  shulman-symmetric-double-has-no-stable-trace-upgrade: that prevents a nonexistent Hilbert--Schmidt stable-trace shortcut from being cited; this uses only Shulman's genuine operator-norm MF theorem, under its actual MF hypothesis.
---

Let `C <= A` be arbitrary groups and

```text
G = < A, t | [t,C]=1 > = A *_C (C x Z).
```

Put `H=A x Z` and form the symmetric amalgamated double

```text
D = H *_C H,
```

where `C` is embedded as `C x {0}` in both copies.  Then `G` embeds in
`D`: use the copy of `A` in the first factor and the central `Z` generator
of the second factor.  The relations hold, and an alternating reduced word
in `A *_C (C x Z)` remains reduced in `H *_C H`, so the normal-form theorem
gives injectivity.

Consequently, if the full group C-star algebra `C*(A x Z)` is MF, then
Shulman's symmetric-double theorem makes

```text
C*(D) = C*(A x Z) *_(C*(C)) C*(A x Z)
```

MF.  Hence `D`, and therefore its subgroup `G`, is MF in the group sense
used by operator-norm approximation theory.

For the arithmetic lane

```text
C=SL_3(Z),       A=SL_3(Z[1/2]),
```

this does **not** imply that `G` is hyperlinear.  Shulman's embedding need
not carry the canonical group trace to a matrix-limit trace, and group-MF
in this operator-norm sense does not imply canonical-trace hyperlinearity.
Thus the tempting chain

```text
C*(D) MF  ==>  D hyperlinear  ==>  G hyperlinear
```

is invalid at its first arrow.  The embedding theorem is nevertheless an
exact firewall against trying to close the HNN lane with Shulman's
symmetric-double MF theorem: that theorem controls the wrong approximation
topology and no selected trace.  A usable upgrade would have to prove that
the **canonical trace** on this particular double is MF/hyperlinear, which
is exactly the missing nonamenable-amalgam trace problem.
