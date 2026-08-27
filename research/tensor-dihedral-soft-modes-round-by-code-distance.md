---
rg: 2
id: tensor-dihedral-soft-modes-round-by-code-distance
kind: claim
title: Arbitrarily many tensor-dihedral soft modes round at the code-distance scale
distinct_from:
  tanner-separated-codewords-create-dihedral-soft-mode: that constructs one noncentral soft factor and only observes that it is individually roundable; this permits arbitrarily many factors, unbounded tensor participation, and unbounded generated-algebra type, and proves one uniform correction bound for their product.
  bounded-participation-tensor-networks-are-not-diffuse-far: that reduces bounded-participation bounded-bond networks to bounded generated type; this has two-dimensional bonds but allows every coordinate to participate in arbitrarily many nonabelian factors, so its generated type can diverge.
  central-clifford-parity-sectors-round-uniformly: that uses scalar central commutator signs; the dihedral commutators here are genuinely noncentral whenever the angle is nonzero.
---

Let `C<=F_2^L` have relative distance at least `delta>0`, with any
homogeneous parity presentation.  For every `t` choose codewords
`0!=c_t,d_t in C` with disjoint supports such that no parity face meets
both supports.  On one copy of `C^2`, put

```text
S=diag(1,-1),
T_t=R_(theta_t) S R_(theta_t)^*,       0<=theta_t<pi/8.  (TDS1)
```

Define a factorwise-exact tensor tuple by

```text
Q_i=tensor_t q_i^(t),
q_i^(t)=S       if c_t(i)=1,
          T_t   if d_t(i)=1,
          I     otherwise.                              (TDS2)
```

Arbitrarily many finite factors are allowed.  Coordinates may participate in
arbitrarily many factors, and the generated matrix type may therefore grow
without bound.  Nevertheless there are commuting reflections `Q_i'` which
satisfy every parity face exactly and obey

```text
(1/L)sum_i||Q_i-Q_i'||_2^2
 <=(1/delta L^2)sum_(i,j)||[Q_i,Q_j]||_2^2.              (TDS3)
```

Hence neither parallel repetition nor tensor accumulation of the exact
dihedral soft mode can realize the diffuse far sector.  If all pair
commutators tend uniformly or on average to zero, this entire unbounded-type
tuple approaches one commuting code representation with the same modulus.

The face-separation hypothesis is exactly what makes each factor an exact
dihedral quotient of the parity presentation.  The result does not handle
factors in which a face contains several genuinely different commuting
reflection directions, non-tensor cancellations between factors, or a
noncentral moving direct-integral decomposition.  Those remain possible
forms of the basin-capture obstruction.
