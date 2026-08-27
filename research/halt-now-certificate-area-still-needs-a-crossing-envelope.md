---
rg: 2
id: halt-now-certificate-area-still-needs-a-crossing-envelope
kind: claim
title: Computing the halt-now certificate area does not remove the Kleene threshold crossing
distinct_from:
  dimension-kleene-threshold-needs-amplification-envelope: that treats a threshold depending on the reported dimension; this allows the threshold and derived word window to depend on the candidate, discovery stage, hypothetical halt transcript, and its computed Higman/Clifford certificate area.
  threshold-free-reverse-kleene-higman-diagonal: that genuinely avoids matrix thresholds by enumerating a word-triviality proof in the reverse semantic orientation; this proves that the proposed forward matrix-search scheduling remains thresholded.
  posthalt-clifford-cannot-power-reverse-kleene: that rules out post-halt Clifford activation as a source of qualitative hyperlinear-radical collapse; this rules out using a computed post-halt area to force the forward fixed-point search to halt.
---

Consider a dimension-matched Kleene search which, upon examining a candidate
matrix tuple `U`, computes the finite certificate that would be produced if
the source machine halted **now** on `U`.  Let

```text
A(U)>=1
```

be a computable Lipschitz/van-Kampen cost for that certificate, and suppose
the soundness argument is valid when

```text
Def(U) < b/A(U)                                         (HNA1)
```

for a fixed `b>0`.  Allow `A(U)` to depend on the dimension, the code of the
algebraic tuple, the discovery stage, the complete hypothetical halt
transcript, and the chosen Clifford/Higman payload.

Computing `A(U)` before halting makes `(HNA1)` semidecidable, but it does not
make the diagonal sound.  The fixed-point contradiction proves only

```text
the search cannot halt.                                 (HNA2)
```

To contradict hyperlinearity one still needs the independent **crossing
property**

```text
some canonical separated candidate U satisfies
Def(U) < b/A(U).                                        (HNA3)
```

Hyperlinearity gives no such candidate-dependent rate.  If the best legal
window (including all tensor amplifications and alternative halt-now
payloads) tends to zero along the dimensions where canonical microstates
occur, an abstract hyperlinear defect profile can tend to zero while staying
above every window.  For a window `theta_n->0`, for example,

```text
epsilon_n=sqrt(theta_n)
```

has `epsilon_n->0` but `epsilon_n>theta_n` for all large `n`.

Therefore halt-now area computation is valid only under the same kind of
positive/crossing envelope already isolated for dimension-dependent
thresholds.  Runtime self-reference does not manufacture that envelope.

There is a second, equivalent failure if the program avoids the area estimate
and evaluates the entire derived Clifford table directly.  Hyperlinear
microstates converge on every **fixed** finite word window, but the table
window now changes after seeing the candidate dimension.  Pointwise
convergence does not imply convergence on this diagonal moving window.  The
elementary triangular array

```text
x_(n,m)=0 if n>m, and x_(n,m)=1 if n<=m
```

satisfies `x_(n,m)->0` for every fixed `m`, while `x_(n,n)=1`.  Thus direct
post-candidate table testing does not bypass `(HNA3)`.

The only genuine threshold-free scheduling currently available is the
reverse-Kleene proof-enumeration orientation, which requires qualitative
NONHALT mark collapse rather than a post-candidate finite capacity breaker.
