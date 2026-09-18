---
rg: 2
id: fg-cremona-subgroups-have-arithmetic-linear-part
kind: claim
title: In a finitely generated subgroup of Bir(P^m_Q) the linear elements lie in PGL_{m+1}(Z[1/N]), so no linearizable copy of (Q,+), and no linear copy of GL_n(Q) for n >= 2, lies in one
distinct_from:
  kazhdan-subgroups-of-cremona-groups-are-residually-finite: that proves a whole finitely generated Kazhdan subgroup residually finite through partial actions on finite point sets; this makes no Kazhdan assumption and controls only the linear (or linearizable) part of an arbitrary finitely generated subgroup, by good reduction of birational maps.
  fg-automorphism-hosts-contain-no-divisible-subgroup: that treats regular automorphisms, where every finitely generated subgroup is residually finite; this treats birational maps, where that is open.
  piecewise-commutative-linear-hosts-miss-linear-gl-n-q: that excludes finitely-piecewise hosts through the finite generation of their piece group; this excludes Cremona hosts, whose elements are not piecewise linear, through reduction modulo primes.
  gl-n-q-explicit-natural-fp-overgroup: that is the open Problem 2.7; this closes the Cremona groups over Q with their natural linear copies of GL_n(Q).
artifacts:
  - research/artifacts/gq-gq-explicit-2-aut-comm-hosts.md
---

**ESTABLISHED** through `fg-cremona-subgroups-have-arithmetic-linear-part-proof`.
Lane proof, not independently reviewed. No priority is claimed; the method is
reduction modulo primes of birational maps.

## Statement

Let `m >= 1` and let `Γ <= Bir(P^m_Q)` be finitely generated. Then there is an
integer `N >= 1` such that

    Γ ∩ PGL_{m+1}(Q)  ⊆  PGL_{m+1}(Z[1/N]),

the image of `GL_{m+1}(Z[1/N])`. In particular `Γ ∩ PGL_{m+1}(Q)` is residually
finite, and so is `Γ ∩ φ PGL_{m+1}(Q) φ^{-1}` for every `φ ∈ Bir(P^m_Q)`, because
`φ^{-1} Γ φ` is again finitely generated.

## Consequences

1. **No linearizable copy of `(Q,+)`.** If `D ≅ (Q,+)` lies in a finitely generated
   `Γ <= Bir(P^m_Q)`, then `D` is not conjugate in `Bir(P^m_Q)` into
   `PGL_{m+1}(Q)`. Residually finite groups contain no nontrivial divisible
   subgroup (root obstruction O1).
2. **No natural Cremona host for Problem 2.7.** For `n >= 2` and `m >= n`, the
   standard copy `g -> diag(g, 1, ..., 1)` of `GL_n(Q)` in
   `PGL_{m+1}(Q) ⊆ Bir(P^m_Q)` (injective because `m + 1 > n`) lies in no finitely
   generated subgroup of `Bir(P^m_Q)`. The same holds for every copy conjugate into `PGL_{m+1}(Q)`, and for
   `SL_n(Q)`, `Aff(Q)`, `U_3(Q)` and `B_n(Q)`, which all contain `(Q,+)` linearly.
3. **What a Cremona host would need.** A finitely generated subgroup of some
   `Bir(P^m_Q)` containing `GL_n(Q)` would have to contain a copy of `(Q,+)` that
   is not linearizable. Its existence would give a finitely generated subgroup of a
   Cremona group that is not residually finite. Whether all finitely generated
   subgroups of Cremona groups are residually finite is recorded in the literature
   as an open question of Cantat (the wording and primary source were not read
   here). So a Cremona answer to Problem 2.7 would also answer that question in the
   negative.

## Scope

- The proof uses unique factorization in `Z` for primitive representatives. The
  same argument should work over a number field `K`, after enlarging `N` so that
  `O_K[1/N]` is a principal ideal domain; this is not checked here.
- Over `C` the argument gives nothing directly: a finitely generated subgroup is
  defined over a finitely generated ring, but primitive representatives need not
  exist.
