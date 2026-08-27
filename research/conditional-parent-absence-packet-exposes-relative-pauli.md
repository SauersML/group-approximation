---
rg: 2
id: conditional-parent-absence-packet-exposes-relative-pauli
kind: claim
title: On a named child carrier, parent absence exposes a fixed relative Pauli pair
artifacts:
  - experiments/minimal_rank_one_support_compiler.py
  - research/artifacts/relative-rank-one-fanizza-synthesis-2026-08-20.md
distinct_from:
  support-failure-has-fixed-pivot-rank-one-compiler: that isolates the full two-variable atom but leaves the extra Pauli coordinate unnamed by a second fixed pivot; this detects parent absence conditionally and makes the extra pair fixed words.
  two-by-two-support-compiler-has-unique-fixed-pivot: that no-go applies to an exact global predicate profile; this deliberately allows extra rank on the harmless parent-absent/child-inactive sector and later restricts to the child carrier.
---

For a parent selector bit `e`, put

```text
C(e) = [[0,   1],
        [1+e, 0]].                                    (CPA1)
```

Then `rank C(e)=1` for `e=1` and `rank C(e)=2` for `e=0`.  In the associated
class-two packet, after fixing `J=-1` and `z_e=(-1)^e`, the named pairs

```text
core:     (p_1,q_2),
relative: (p_2,q_1)
```

commute across pairs.  The core pair always anticommutes.  The relative pair
satisfies

```text
[p_2,q_1]=J z_e,
```

so it commutes when the parent is present and is a second Pauli pair when the
parent is absent.  Hence the fixed-sector algebra is

```text
e=1: M_2(C) tensor C[(C_2)^2],
e=0: M_2(C) tensor M_2(C).                             (CPA2)
```

On a separately named child-active carrier `f=1`, the second tensor factor is
therefore present exactly on the forbidden support event `(e,f)=(0,1)`.

The gain over the exact compiler is word-level accessibility: both generators
of the relative pair are fixed group words.  The cost is that the packet also
has the second Pauli factor on `(e,f)=(0,0)`; a valid holonomy must be compressed
to, or switched by, the child carrier rather than charge parent absence
globally.
