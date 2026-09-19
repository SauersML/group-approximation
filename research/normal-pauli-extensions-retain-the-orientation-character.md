---
rg: 2
id: normal-pauli-extensions-retain-the-orientation-character
kind: claim
title: Every normal two-qubit Pauli extension retains the controlled orientation character
distinct_from:
  orientation-graded-mixed-returns-have-a-balanced-double: that exploits a supplied C2 grading; this proves the grading is automatic as long as the marked Pauli packet remains normal.
  packet-dressed-shared-implementer-requires-one-outer-class: that compares two packet-dressed normalizers in one outer class; this extracts the global sign character of every packet normalizer.
  odd-selector-row-balances-or-kills-outer-action: that analyzes the first relation which can make the packet nonnormal; this proves nonnormality is necessary before any such relation can break the grading.
---

**ESTABLISHED.**  Let `P` be the two-qubit extraspecial Pauli group with
central involution `J`, and let `Gamma` be any group in which `P` is normal
and `J` remains central.  Conjugation gives

```text
Gamma -> Out_J(P) ~= O_4^+(F_2)
                    ~= (S_3 x S_3) semidirect C_2.     (NPO1)
```

Inner automorphisms, hence every element of `P`, map trivially to the outer
group.  The product of the two `S_3` sign characters is invariant under the
factor swap and hence extends to `O_4^+(F_2)`.  The controlled-Z automorphism
maps to `(transposition,1)` in the displayed product.  Therefore composition
with this product-sign character gives a homomorphism

```text
chi_P:Gamma -> C_2                                      (NPO2)
```

which vanishes on `P` and takes value one on every controlled-Z
transvection implementer `t`.

Consequently **no collection of additional relations which keeps this copy
of `P` normal can break the orientation grading**.  Whenever one marked
finite-dimensional representation survives, tensoring it with the two
characters of `(NPO2)` gives the exact balanced double of
`orientation-graded-mixed-returns-have-a-balanced-double`.

Thus a viable odd Whitehead coupling must make the coarse Pauli packet
nonnormal by transporting it into a genuinely different self-similar scale.
Merely enlarging its normalizer—even by an infinite group—or imposing more
relations among normalizing actuators cannot select the literal controlled
reflection.  This is stronger than the finite-packet gauge observation: the
obstruction follows functorially from the outer action and survives every
normal extension.
