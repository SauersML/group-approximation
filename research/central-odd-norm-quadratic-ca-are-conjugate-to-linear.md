---
rg: 2
id: central-odd-norm-quadratic-ca-are-conjugate-to-linear
kind: claim
title: Central odd-cycle quadratic norm rules are reversibly conjugate to arbitrary linear cellular automata
artifacts:
  - research/artifacts/gottschalk-central-odd-norm-conjugacy-direct-finiteness-2026-09-08.md
---

Let G=Gamma x C_n for odd n>=3, let t generate C_n, and write
T=R_t, E=I+T+...+T^(n-1), Q_t(x)=xTx over F_2. For any scalar
linear CA B on Gamma, lift B independently to the cyclic coordinates
and define

    F_B(x)=x+(B-I)E Q_t(x),
    Psi(x)=(I-E)x+E Q_t(x).

Then Psi is a reversible CA with Psi^2=I and

    Psi F_B Psi=(I-E)+BE.

Consequently F_B preserves the injectivity and surjectivity status
of B, and F_B F_C=F_(BC). For each Gamma, surjunctivity of all these
norm rules is equivalent to direct finiteness of F_2[Gamma].

Adding a finite factor S_3^k encodes any finite-track F_2-linear CA
in a scalar block, so the same quadratic family also contains all
matrix linear surjunctivity problems on enlarged groups. No inverse
pair or counterexample is constructed; direct finiteness over F_2
remains an open input to a universal positive conclusion.
