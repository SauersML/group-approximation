---
rg: 2
id: lifted-trace-detects-finite-subgroup-projectives
kind: claim
title: Lifted p-adic trace detects every nonzero finite-subgroup projective in the ambient group algebra
distinct_from:
  subgroup-supported-one-sided-inverse-rigidity: that confines one of the inverse factors to a directly finite subgroup; this confines only an idempotent defect or projective summand, allowing both inverse factors arbitrary ambient support.
  padic-c0-direct-finiteness-equivalence: that transfers the direct-finiteness question between two coefficient rings; this constructs an additive invariant and evaluates it on finite-subgroup projectives.
---

Let p be prime and G any group. There is an additive lifted coefficient
trace

    t_p : K_0(F_p[G]) -> Z_p.

For every finite subgroup H <= G and every idempotent
e in M_n(F_p[H]), it satisfies

    t_p([e F_p[G]^n]) = dim_(F_p)(e F_p[H]^n) / |H|.     (LFT1)

The rational number on the right belongs to Z_p. In particular, the
class of any nonzero such projective has infinite order in K_0(F_p[G]).

Consequences, with no approximation assumption on G:

1. If f < e are idempotents in one M_n(F_p[H]), their induced ambient
   projectives are not stably isomorphic, even after adding the same
   arbitrary finitely generated projective F_p[G]-module.
2. If BA=I in M_n(F_p[G]) and d=I-AB != 0, the support of the entries
   of d cannot be contained in any finite subgroup of G.
3. More generally, this defect module cannot be isomorphic to a nonzero
   finite direct sum of projectives induced from finite subgroups.

This does not prove direct finiteness: positivity or faithfulness of t_p
on arbitrary ambient projectives is not asserted. The explicit nonzero
formula (LFT1) concerns finite-subgroup projectives.

The construction is a coefficient-at-identity instance of the established
lifted-trace method; see Farrell--Linnell, *Whitehead groups and the Bass
conjecture*, Section 5, https://arxiv.org/abs/math/0301205. The accompanying
route gives a self-contained proof for the exact prime-field statement
used here.
