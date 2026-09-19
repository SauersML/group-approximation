---
rg: 2
id: finite-graph-packet-compression-wandering-no-go
kind: claim
title: A finite graph-of-packets word cannot be both a fixed corner reflection and wandering
distinct_from:
  fanizza-coherent-verifier-wandering-promotion: that asks for one ordinary wandering word whose selected compression is the finite verifier; this rules out the proposed finite graph/HNN/free-product implementation.
  finite-normalizer-star-no-go: that uses induction and finite-dimensional type flow to defeat a finite star; this is the direct group-algebra normal-form obstruction for one corner-compressed word.
  compressed-reflection-kills-even-cesaro-mark: that derives the analytic consequence once the compression exists; this proves the compression cannot exist in a finite Bass--Serre packet while the word wanders.
---

Let `G` be the fundamental group of a finite graph of finite groups, let `K`
be one vertex group, let `0!=q in C[K]` be a projection, and let

```text
0!=V=qVq in q C[K] q.                                  (FGP1)
```

For every ordinary group element `w in G`, exactly one of the following
applies.

1. If `w notin K`, then

   ```text
   supp(qwq) subseteq K w K,
   K w K intersect K = empty.                          (FGP2)
   ```

   Hence `qwq` and `V` are orthogonal in the regular `L^2` space and

   ```text
   ||q(w-V)q||_(2,L(G))^2
      =||qwq||_2^2+||V||_2^2
      >=||V||_2^2>0.                                  (FGP3)
   ```

2. If `w in K`, then `w` has finite order, so neither the powers `w^k` nor
   the marked powers `d w^k` can be pairwise distinct.

Therefore a cyclically reduced product of packet conjugates such as

```text
w=product_i t_i a_i t_i^(-1)                           (FGP4)
```

cannot satisfy both the corner approximation `(FCW1)` and the wandering
normal-form clause of `fanizza-coherent-verifier-wandering-promotion`.

The obstruction persists for approximate/canonical finite models.  Finite
graphs of finite groups are virtually free and residually finite.  Choose
finite quotients injective on the finite support of `q(w-V)q`; their regular
representations are exact canonical microstates and their normalized
Hilbert--Schmidt compression error converges to, and eventually equals after
support separation, the positive value in `(FGP3)`.  Thus no microstate
modulus can make that error tend to zero.

## Where the multiplicity gauge argument breaks

On one selected finite type, an edge transporter has the form

```text
T=J tensor U_mult.
```

If `a` acts as `A tensor 1` on the transported type, the multiplicity gauge
does cancel in `T a T^(-1)`.  But a representation-independent full carrier
return requires the corresponding finite type idempotents to be transported
exactly.  In an HNN packet this has two possible outcomes:

- if `a` lies in the identified edge algebra, the HNN relation reduces
  `t a t^(-1)` to a vertex-group element; repeating this for all factors
  puts `w` in a finite vertex group and destroys wandering;
- if `a` lies outside the edge algebra, Britton reduction preserves the
  stable letters.  The compression is then a genuine Hecke double-coset
  operator, not the fixed vertex reflection, and `(FGP3)` detects it in the
  regular representation.

There is no intermediate finite Bass--Serre case.  Exact cancellation of the
stable-letter gauge on the whole selected carrier also cancels the stable
letter from the group normal form; retaining the normal form retains a
positive Hecke compression error.

The countably amplified HALT representation is not the obstruction: its
infinite multiplicities can implement the edge equivalences and can choose
gauges making a selected compression look like `V`.  The failure is
NONHALT/canonical soundness -- finite regular graph quotients choose the
regular Hecke transport and violate `(FCW1)`.  A successful promotion must
therefore use a non-Bass--Serre matrix-only return whose corner equality is
forced on canonical finite models without becoming an equality in the
ambient group algebra.
