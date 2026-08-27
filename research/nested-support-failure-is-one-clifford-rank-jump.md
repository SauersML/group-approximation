---
rg: 2
id: nested-support-failure-is-one-clifford-rank-jump
kind: claim
title: The forbidden child-without-parent support atom is detected by one extra Clifford rank
distinct_from:
  boolean-predicate-is-one-rank-jump: that compiles an arbitrary Boolean predicate by an algebraic branching program; this is the minimal two-idempotent matrix already present in the Steinberg pairing.
  predicate-rank-gate-doubles-restriction-multiplicity: that turns a rank jump into restriction multiplicity; this identifies the specific support-containment failure whose jump should enter that packet construction.
---

Let `f<=e` be nested idempotents and let `ell` be a binary additive character
evaluated on them.  On `span{e,f}`, consider the binary Steinberg pairing
matrix

```text
C(e,f) = [[ell(e), ell(f)],
          [ell(f), ell(f)]].                           (NSR1)
```

Its rank over `F_2` is

```text
(ell(e),ell(f)) = (0,0)  -> 0,
                  (1,0)  -> 1,
                  (1,1)  -> 1,
                  (0,1)  -> 2.                        (NSR2)
```

Thus exactly the support-containment failure "the child `f` survives while
its parent `e` disappears" contributes one rank above every nonzero allowed
atom.  After Schur--Clifford compilation this is one additional Pauli
multiplicity coordinate, rather than a scalar relation attempting to delete
the forbidden character.
