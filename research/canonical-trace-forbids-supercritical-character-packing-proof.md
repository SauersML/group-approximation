---
rg: 2
id: canonical-trace-forbids-supercritical-character-packing-proof
kind: route
title: Proof of the canonical character-packing ceiling
target: canonical-trace-forbids-supercritical-character-packing
requires: []
---

Choose `i_0` with maximal `tau(e_i)`.  From `(CTP2)`,

```text
tau(e_(i_0))>=beta a/M.                                (CTQ1)
```

Conjugation preserves the canonical trace.  If the `K` conjugates of
`e_(i_0)` are pairwise orthogonal and lie below `q_-`, their sum is a
projection below `q_-`; therefore

```text
K tau(e_(i_0))<=tau(q_-)=h.                            (CTQ2)
```

Combining `(CTQ1)--(CTQ2)` gives `(CTP3)`.

If all conjugates are pairwise orthogonal across both indices, their sum is
again a projection below `q_-`, and now

```text
K sum_i tau(e_i)<=h.                                   (CTQ3)
```

Using `(CTP2)` gives `(CTP4)`.  Substitution of `(CTP5)` gives
`(CTP6)--(CTP7)`.

For the Pauli seed, `q=q_-(1+B)/2` where the central-sign seed has the
two-dimensional irreducible representation on the `J=-1` sector.  Its
canonical character gives `tau(q_-)=1/2` and `tau(q)=1/4`.  In the finite
uniform structural model, every context character has its uniform weight.
The robust soundness inequality at zero defect therefore reads

```text
sum_i tau(e_i)>=beta tau(q)=beta/4.                    (CTQ4)
```

When the finite seed-context groups embed in `G`, their canonical trace is
the same uniform character trace, so `(CTQ4)` is precisely `(CTP2)` for the
canonical trace of `G`.  The proposed strict thresholds contradict
`(CTP6)` or `(CTP7)`, completing the proof.
