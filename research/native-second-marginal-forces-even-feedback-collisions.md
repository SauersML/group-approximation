---
rg: 2
id: native-second-marginal-forces-even-feedback-collisions
kind: claim
title: A native six-address second marginal forces explicit collisions in every even feedback cycle
distinct_from:
  nonlinear-certificate-fibers-are-all-surjective-or-all-strict: that derives a surjectivity dichotomy under injectivity; this produces a literal collision for a specified native marginal and requires no injectivity hypothesis.
  forward-memory-lifts-exclude-strict-cellular-sections: that excludes strict pairs by a surjunctive cover matching one composition table; this disproves injectivity of an entire encoder family before any decoder is chosen.
artifacts:
  - research/artifacts/gottschalk-native-second-marginal-collision-2026-09-08.md
---

Let Q be the binary Leavitt unit group. Use its native atlas b_1,b_2
on the ordered charts (01,1,000,001) and (00,1,010,011), and roots
y=q32(e*), w=q32(f*), u=q32(1). Define the binary linear rule

    L(U)(g)=U(g)+U(gb_1)+U(gb_2)+U(gy)+U(gw)+U(gu).

For an even number m>=2 of tracks, consider any finite-memory bilinear
operations B_i and the cyclic rule

    F_i(X)=X_i+B_i(X_(i+1),X_(i+2)),       i modulo m.

If B_i(1,U)=L(U) for every U and every odd i, then F is noninjective.
The even output operations and all first-argument addresses are
otherwise unrestricted. In particular this excludes the six-term
four-track encoder in Section 6 of the forward-memory artifact,
regardless of decoder degree or memory.

An explicit nonzero mask is U(g)=lambda(g^-1 e_(110^infinity)) in
the natural eventually-zero boundary module, where lambda sums
coefficients on the disjoint cylinders 11,010,0111. It satisfies
L(U)=U and U(1)=1. Put U on odd tracks and 1 on even tracks. The
output has all odd tracks zero and hence is fixed by F; it differs
from the input. This is a literal full-shift collision, with no
finite-support assertion.
