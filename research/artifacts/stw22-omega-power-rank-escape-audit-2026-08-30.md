# STW XXII: the first limit-rank escape core

## Model

For the trivial UHF field over `[0,omega^omega]`, let `I_n` be the top fibre
gap after `n` Cantor--Bendixson derivatives.  Successor restriction has a
trace-free kernel, but there are infinitely many successor steps before the
top point becomes isolated.

Close the union of the kernels of all finite restriction maps and quotient:

```text
Q_omega=I_0/closure(union_n ker(I_0 -> I_n)).
```

All bounded traces on `I_0` factor uniquely through `Q_omega`, and every
trace on `Q_omega` pulls back.  Thus this quotient is the exact limit-rank
obstruction.

## Why it is not a formal zero

Choose clopen ordinal packets converging to `omega^omega`, with the `k`-th
packet containing a rank-`k` point, and put a projection of trace tending to
zero on each packet.  The resulting section is uniformly `2`-norm
continuous but remains norm one on every finite derived tail.  Its distance
from every finite-layer kernel, and from the closure of their union, is one.
Hence `Q_omega` is nonzero.

## What is nevertheless ruled out

Every bounded trace on `Q_omega` kills these cofinal clopen projection
packets: their shrinking factor traces permit arbitrarily many orthogonal
equivalent copies, implemented by clopen-constant partial-isometry sections.
Therefore the nonzero quotient itself is not evidence for a counterexample.
A singular trace, if one exists, must detect an element whose norm support
jumps through unbounded Cantor--Bendixson ranks in a way not reducible to
clopen projection packets.
