---
rg: 2
id: mikhailova-profinite-pinch-is-mf-visible
kind: claim
title: A profinitely invisible Mikhailova pinch remains visible in the positive rope's norm corona
distinct_from:
  mikhailova-positive-rope-is-not-lef: that proves the whole rope is not LEF from nonseparability of its inner edge; this exhibits one nontrivial word killed by every finite quotient but separated by a norm-matrix-corona model.
  centralizing-hnn-sofic-via-regular-edge-centralizer: that proves quotient permutation models kill closure-point pinches and leaves soficity open; this proves that the same pinch survives in operator-norm matrix approximations, so the quotient obstruction cannot be promoted from permutations to MF.
  matricial-stability-identifies-radicals: that compares the MF radical with the residual over all finite-dimensional unitary representations under matricial stability; this separates the MF radical from the smaller class of finite-image representations without assuming stability.
---

ESTABLISHED.  Let `R` be the fixed positive Mikhailova rope and let

```text
Gamma=<K,v | [v,L]=1> <= R                                (MPMV1)
```

be its inner centralizing HNN stage.  There are `k in K\L` and

```text
w=[v,k] in Gamma <= R                                     (MPMV2)
```

such that

```text
w != 1,
phi(w)=1 for every homomorphism phi:R->F to a finite group,
Theta(w)!=1 for some injective norm-matrix-corona map Theta:R->U(Q). (MPMV3)
```

Equivalently, the finite residual of `R` is nontrivial while its MF radical
is trivial.  The same explicit *type* of word witnesses both facts: a
profinite-closure pinch is invisible to finite quotients and macroscopically
visible in the compiler's faithful operator-norm microstates.

This is a complete firewall against upgrading
[[mikhailova-positive-rope-is-not-lef]] to non-MF.

1. **Finite-presentation compactness stops at exact charts.**  Finite
   presentation promotes a LEF chart to a finite quotient because the chart
   satisfies the relators exactly.  An MF tuple only makes their operator
   norms tend to zero.  If finite presentation alone corrected those tuples
   to finite-image representations, `(MPMV3)` would force the corrected
   value of `w` simultaneously to be `1` and to stay a positive distance
   from `1`.
2. **Profinite nonclosure has the opposite MF outcome here.**  It supplies
   `w` in the finite residual, but the faithful corona model proves
   `w notin Rad_MF(R)`.  Thus no principle of the form "a closure-point pinch
   is MF-invisible" can hold, even for this finitely presented torsion-free
   HNN rope.
3. **Ordinary matricial stability would not repair the argument.**  It
   corrects norm microstates to arbitrary finite-dimensional unitary
   representations, whose images may be infinite; non-LEF excludes only
   finite-image separation.  If `R` happened to be matricially stable, then
   [[matricial-stability-identifies-radicals]] and MF would instead produce
   a finite-dimensional representation detecting `w`.  Its image would
   necessarily be infinite by `(MPMV3)`.  This is compatible with non-LEF,
   not a contradiction.

Consequently a stability-based non-MF proof would need an independent
hypothesis forcing the correcting representations to have finite image (or
forcing all finite-dimensional representations to kill `w`).  Neither
finite presentation nor profinite nonclosure provides that hypothesis.

DERIVATION
[[mikhailova-profinite-pinch-mf-visibility-proof]]
