---
rg: 2
id: native-fanizza-join-tree-prescribed-word-realization
kind: claim
title: Realize the semantically reduced native Fanizza join tree on its prescribed machine words
distinct_from:
  join-tree-bcs-has-explicit-signed-hecke-atlas: that constructs compatible algebraic context partitions for abstract join-tree variables; this must identify their marginal involutions with the prescribed native machine words while preserving the marked exact representation.
  hs-groupify-self-referential-bcs-signal: that asks for a compiler for the fully flattened BCS menu; this uses the four native contexts after the Pauli guard removes their only additive cycle.
---

OPEN.  Keep the native multiplicative relations as ordinary group relations.
After `pauli-guard-collapses-c18-to-three-bit-recurrence`, the nonlinear
contexts form the join tree

```text
          C_X
           |
C_Z ---- C_D ---- C_R',                               (NFJ1)
```

where `C_R'` is the three-bit recurrence context and all separators are
binary or elementary abelian of fixed rank.

Use `join-tree-bcs-has-explicit-signed-hecke-atlas` to construct one common
signed corner and compatible local partitions.  Couple each marginal
involution in that corner to the literal prescribed word

```text
O_Q, O_P, X_(m,0), X_tilde, Z_(m,0), Z_tilde,
X_tilde O_P X_tilde, U O_P U^*.                       (NFJ2)
```

The coupling must satisfy:

1. every finite-dimensional microstate decodes the four native contexts with
   total forbidden mass bounded by a computable vanishing modulus;
2. no commutation is added between prescribed words not sharing a native
   context;
3. after gauge-orbit covariantization and countable amplification, every
   exact marked HALT representation extends while retaining the native signal;
4. the selected signed corner has fixed canonical trace mass, or equivalent
   finite trace side tests, so spectator representations cannot erase it; and
5. the construction is finite and effective in the machine index.

No cycle-holonomy or arbitrary atlas coherence theorem remains.  The
load-bearing issue is now local **word/corner realization**: the signed-Hecke
partition observables are finite group-algebra expressions, while `(NFJ2)`
are ordinary group words.  Literal algebraic equality is unavailable as a
group relator, and a functorial tracial decoder would violate the regular-
representation firewall.  A successful cell must use finite packet
exactification and finite-dimensional multiplicity coordinates while the
exact marked model extends by infinite amplification.

This is strictly smaller than the former groupification target: four fixed
contexts, a join tree, and no nonlinear six-bit guard.
