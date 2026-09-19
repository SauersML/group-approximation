---
rg: 2
id: first-partial-inverse-whitehead-face-has-haar-mf-character
kind: claim
title: The first partial-inverse Whitehead face admits the full Haar row MF character
artifacts:
  - research/first-partial-inverse-whitehead-haar-proof.md
distinct_from:
  haar-root-character-vanishes-off-parabolic-action-kernel: that derives regular-character values on the parabolic from a Haar root restriction; this adjoins a genuine non-diagonal opposite-root word containing `s_0,t_0` and constructs exact finite operator-norm models.
  finite-positive-root-fragments-have-marked-regular-models: that fences every finite positive-root fragment but explicitly stops before an opposite root; this crosses the boundary with the shortest partial-inverse Whitehead involution.
  full-depth-one-leavitt-menu-has-finite-clifford-model: that gives a finite occurrence-label model of a broad depth-one menu; this retains the literal full infinite row module and realizes its Haar character by finite subgroup exhaustions.
  binary-leavitt-haar-row-profile-is-not-mf-character-restriction: that asks whether Haar can extend to an MF character of the whole Steinberg group; this proves only that the first `s_0,t_0` opposite-root face cannot exclude such an extension.
---

Let `R=L_(F_2)(1,2)`, let `n>=4`, and use the full first-row root module

```text
N=<x_(1j)(a):2<=j<=n, a in R> ~= (R,+)^(n-1).
```

On coordinates `2,3` put the literal partial-inverse Whitehead word

```text
omega=x_23(s_0) x_32(t_0) x_23(s_0).
```

After projection to the elementary group its active block is

```text
W=[[q,s_0],[t_0,0]],             q=1-s_0t_0=s_1t_1,
```

and `W^2=1`.  It normalizes the elementary image of `N`; on the two displayed
row coefficients its action is

```text
(a,b) |-> (a q+b t_0, a s_0),                         (PIW1)
```

and it fixes the other coordinates.  Thus the elementary image of
`<N,omega>` is

```text
(R,+)^(n-1) semidirect C_2.                            (PIW2)
```

This group is locally finite.  Its regular character pulls back to an MF
character of `<N,omega>` whose restriction to `N` is exactly Haar:

```text
chi(v)=0                         for every 1!=v in N.  (PIW3)
```

In particular the manuscript mark `x_13(q)` remains nonidentity, has trace
zero, and is represented at operator-norm distance two from the identity in
every sufficiently large finite regular model.

Consequently neither the relation `t_0s_0=1`, the reverse idempotent
`s_0t_0`, nor their first genuine opposite-root Whitehead occurrence can
exclude the Haar row profile.  A successful Haar-row obstruction must couple
this face to another noncommuting coefficient occurrence or to a global
return relation.  The claim makes no assertion that `(PIW3)` extends from
this subgroup to the whole Steinberg group.

DERIVATION
first-partial-inverse-whitehead-haar-proof
