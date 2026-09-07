---
rg: 2
id: lifted-trace-bounds-unital-matrix-parts
kind: claim
title: The p-adic valuation of a corner trace bounds the p-part of every unital matrix block
distinct_from:
  finite-subgroup-corners-have-invariant-basis-number: that forbids unequal numbers of copies of the same projective; this bounds divisibility of one identity into mutually equivalent summands, which invariant basis number alone does not forbid.
  leavitt-matrix-amplification-in-unit-group-algebra: that constructs arbitrarily large matrix copies with changing supported identities; this proves that changing the identity is necessary for the binary powers beyond the first inside the designated cubic corner.
  lifted-trace-detects-finite-subgroup-projectives: that constructs the lifted trace; this uses its integral codomain to obtain a quantitative matrix-divisibility obstruction.
---

Let S=F_p[G], let e in M_k(S) be idempotent, and write
a=t_p([eS^k]) in Z_p. If eM_k(S)e admits a unital ring homomorphism
from M_n(F_p), then

    a in n Z_p.                                        (LMD1)

If a!=0, this implies v_p(n)<=v_p(a). In particular, if the same
corner contains unital matrix blocks M_(p^r)(F_p) for arbitrarily
large r, then a=0. Compatibility between those matrix blocks is not
needed for this necessary condition.

For e=[g]+[g^2] in the binary Leavitt unit group algebra, a=2/3 and
v_2(a)=1. This corner contains a unital M_2(F_2), by the established
S_3 packet construction, but no unital M_n(F_2) when 4 divides n.
Thus its maximum binary matrix size is exactly two. In particular it
does not contain a unital M_4(S).

The existing injections j_(2^r):M_(2^r)(S)->S remain valid. For r>=2,
their identity cannot equal this fixed e; even when their image lies
inside eSe, they must be nonunital there.

Vanishing lifted trace alone is not asserted to imply a one-sided
inverse, a zero K_0 class, or failure of surjunctivity. This theorem is
a necessary capacity constraint for a construction with a fixed corner
identity, not a construction of a counterexample.
