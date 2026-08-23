---
rg: 2
id: authenticated-opnorm-challenge-compiler
kind: claim
title: Compile computation into an authenticated operator-norm support challenge
distinct_from:
  hs-pcp-boone-compiler: that needs a positive-density normalized-HS carrier and runtime-independent soundness; this needs only support of a nonzero operator-norm sector and permits arbitrary depth-dependent loss.
  reverse-kleene-operator-norm-collapse-gives-non-mf: that is the fixed-point implication after a compiler with finite quantitative semantics is supplied; this is the missing construction and has a recursively enumerable qualitative MF-radical output.
  threshold-free-reverse-kleene-mf-higman: that is the abstract fixed-point theorem consuming HALT survival and NONHALT MF-radical collapse; this constructs those two semantics from finite CPU challenges.
---

**OPEN.**  There is a total computable map from a Turing-machine index `e` to
a finite alphabet, a uniformly recursively enumerable ordinary group
presentation

```text
Gamma_e=<S_e|R_e>,
```

and a marked word `w_e`, such that

```text
e halts     => w_e!=1 in Gamma_e,
e nonhalts  => w_e lies in Res_MF(Gamma_e).
```

The compiler uses finite signed-permutation CPU sectors, discrete exactified
support profiles, group-word authentication, and a depthwise same-mark
challenge return.  It never reads a candidate matrix dimension and imposes
no computable finite-coordinate error modulus.

## Attempts

The active decomposition is `authenticated-opnorm-compiler-assembly`.
Finite-predicate CPU realization, fixed-finite-group operator-norm
exactification, the depthwise MF-radical limit, and the threshold-free fixed
point are established.  The attack is presently deferred at exactly two
open inputs: `opnorm-support-profile-challenge-library` must authenticate and
defeat every marked finite support type while preserving an infinite marked
model, and `opnorm-depthwise-same-mark-return` must send those terminal
violations back to one word.  Searching matrix microstates is not a fallback:
it reintroduces the dimension-dependent threshold-crossing problem.
