---
rg: 2
id: damped-cloud-face-return-has-an-exact-scalar-fixed-sheet
kind: claim
title: Damped cloud averaging followed by sign-first face return has an exact scalar fixed sheet
distinct_from:
  damped-cloud-averaging-contracts-from-exact-faces: that proves strict descent before returning to the exact-face sheet; this computes that the standard Loewner return can spend exactly all of that gain.
  face-exactify-cloud-majority-has-a-remote-scalar-fixed-point: that gives one remote fixed point for the opposite order of projections; this applies to every inconsistent scalar point of the exact-face sheet and to the damp-then-return order.
  parity-charge-or-green-divergence-has-strict-descent: that permits a globally coordinated parity repair or a different Lyapunov function; this rules out closing its sparse branch by the existing sign-first local face exactifier.
---

ESTABLISHED SHARP RETURN FENCE.  Let `(A_(f,i))` be a scalar exact-face
tuple, so every `A_(f,i)` is a sign, every face has its prescribed sign
product, and different occurrences of one logical coordinate need not agree.
For each cloud put

```text
 S_i=sum_v lambda_(i,v) A_(i,v),
 X_(f,i)(t)=(1-t)A_(f,i)+tS_i.                         (DCF1)
```

If `0<t<1/2`, then

```text
 sign(X_(f,i)(t))=A_(f,i)                              (DCF2)
```

at every occurrence.  Consequently the explicit sign-first construction in
`fixed-parity-faces-exactify-with-loewner-row-square-control` returns the
original tuple exactly: after the first sign operation the old commuting
parity face has already been recovered, so none of its later pinching or
last-coordinate steps changes it.

This is not only a peculiarity of that explicit tie-breaking rule.  On a
fixed scalar face, `|X_(f,i)(t)-A_(f,i)|<=2t`.  Its symmetrized Loewner face
square is at most `C_q' t I`: the positive involution defects are `O(t)`,
and the commutator and word squares are `O(t^2)`.  If another exact scalar
face tuple `B_f` differs from `A_f`, then at one coordinate

```text
 (X_(f,i)(t)-B_(f,i))^2 >=(2-2t)^2 I.                  (DCF2a)
```

Hence, for `t<t_*(q)` fixed sufficiently small, **every** facewise return
satisfying the local Loewner movement bound `(LFE2)` is forced to choose
`B_f=A_f`.  Improving the implementation or its tie breaking while retaining
only that local cost certificate cannot remove the fixed sheet.

This gives nontrivial fixed points in the balanced pair-sum presentation.
For example, take the length-three repetition code with original rows
`12,23`, repeat each original row twice, and include the pair-sum row `13`.
On each indexed two-coordinate face choose independently either the scalar
assignment `(+1,+1)` or `(-1,-1)`, with at least two incident faces given
different choices.  All local faces are exact, while at least one equality
cloud has positive energy.  Damping by any `0<t<1/2` and then applying the
established local Loewner exactifier leaves this inconsistent occurrence
tuple fixed.

There is also a fixed instance for every nonterminal damping parameter
`0<t<1`.  Take two indexed copies of each of the three rows `12,23,13`, put
`(+1,+1)` on one copy and `(-1,-1)` on the other, and use regular equality
cloud weights.  Every logical cloud then has mean `S_i=0`, so

```text
 X_(f,i)(t)=(1-t)A_(f,i),
 sign(X_(f,i)(t))=A_(f,i)       for every t<1.          (DCF2b)
```

This constant repetition changes none of the balanced-overlay parameters.
In particular it covers the optimized value `t_0=1/(1+C_0)` in `(DCA3)`
without needing any estimate on `C_0`.

The obstruction is precisely the uncontrolled equality cross term.  Write

```text
 R_(i,v)=A_(i,v)-X_(i,v)(t)=t(A_(i,v)-S_i).             (DCF3)
```

For every equality edge `(u,v)` in cloud `i`,

```text
 X_u-X_v=(1-t)(A_u-A_v),
 R_u-R_v=t(A_u-A_v).                                   (DCF4)
```

Thus the equality energy after return is

```text
 ||(X_u-X_v)+(R_u-R_v)||_2^2
  =(1-t)^2||A_u-A_v||_2^2
   +2t(1-t)||A_u-A_v||_2^2
   +t^2||A_u-A_v||_2^2
  =||A_u-A_v||_2^2.                                    (DCF5)
```

The positive first-order cross term in `(DCF5)` consumes exactly the gain in
`(DCA2)`.  Therefore a movement bound for local face exactification, even in
Loewner order, cannot imply a strict two-step sparse contraction: it has no
sign information on this term.

Taking a direct sum of this scalar packet with any exact shared code tuple,
with packet trace `alpha`, makes the balanced defect and the fixed-sheet mass
both `Theta(alpha)`.  Hence the failure persists at arbitrarily small
normalized energy; it is not only a remote constant-defect pathology.

This does not refute a dimension-independent rounding modulus.  The scalar
packet can be repaired by a cloud-majority choice coordinated across faces at
cost `Theta(alpha)`.  It proves that the missing step must make such a
coherent global branch choice (or use a Lyapunov cross term with a verified
negative sign); independent sign-first Loewner returns cannot close it.
