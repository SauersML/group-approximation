---
rg: 2
id: literal-unsquared-defect-finite-packet-holonomy-proof
kind: route
title: Exactify the eight-lamp packet and close its one-sided carrier return
target: literal-unsquared-defect-finite-packet-holonomy
requires:
  - literal-sign-free-eight-lamp-packet
  - finite-noncommutative-packet-compression-collapse
  - finite-packet-multiplicity-certificates-detect-mf-radicals
  - finite-corona-dimension-certificate-calculus
artifacts:
  - research/artifacts/literal-eight-lamp-finite-packet-holonomy-2026-08-26.md
  - notes/FINITE_PACKET_SELF_COPY_COLLAPSE.md
---

Apply `finite-noncommutative-packet-compression-collapse` to

```text
W=E/<w>,  L=q(B),  s=q(t),  K~=(C_2)^8,  k=q(tct^-1).
```

All hypotheses are supplied by `literal-sign-free-eight-lamp-packet`.
Therefore every corona representation identifies `k` with every
`L`-conjugate, including its conjugate by `q(v_1)`, and kills their
commutator.  The two orientations `[q(v_1),k]` and `q([k,v_1])` are
inverse-conjugate, so it kills `q(u)`.

For this literal abelian packet, the general proof has an exact finite
terminal certificate.  Simultaneous diagonalization makes every nonzero
singular value of `V_n(a k a^-1)-V_n(k)` equal to `2`; hence the unnormalized
Hilbert--Schmidt generator energy is `4W_n`, where `W_n` is its integer
displacement rank.  Scaled
Kazhdan transport through the common packet carrier makes the same energy
`o(W_n)`.  On a tail this is `4W_n<=2W_n`, forcing `W_n=0`.  This is the
nonlinear common-carrier row that defeats the otherwise positive regular
character profile.

In the language of
`finite-packet-multiplicity-certificates-detect-mf-radicals`, the summands of
`W_n` are the multiplicities of the active spectral types of the packet
differences.  The rational rank calculus of
`finite-corona-dimension-certificate-calculus` checks the final implication:
after adjoining a nonnegative slack rank, the integer row is
`4W_n+S_n=2W_n`, so `2W_n+S_n=0`.  The homogeneous
restriction/conjugacy rows organize the 256 character sectors; the extra
common-carrier return row is what annihilates them.
