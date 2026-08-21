---
rg: 2
id: atlas-a4-four-cycle-dirichlet-ceiling
kind: claim
title: The exact A4 network keeps the minimal four-cycle Dirichlet energy below one over 1536
distinct_from:
  atlas-a4-four-cycle-dirichlet-compiler: that stronger target makes the four-cycle energy vanish at a rate controlled by packet and collision defect; this target asks only for one fixed numerical ceiling along the normalized necessity sequence.
  atlas-a4-holonomy-coherence-gap: that target bounds the two raw S3 covariance directions; this target bounds the four minimal A8 cycle directions before the exact finite transfer to the raw S3 detector.
---

For a normalized exact-regular A4 context-network sequence, put

```text
E_n = sum_(t in {t01,t12,t23,t30})
        (1-Re tau_n(V_n(t))).
```

Prove the strictly weaker numerical statement

```text
limsup_n E_n < 1/1536.                                  (A4-DIR-CEIL)
```

No modulus tending to zero is required.  The constant is chosen so that the
exact transfer `atlas-a8-four-cycle-controls-raw-s3-energy` gives

```text
limsup_n (a_n^2+b_n^2)
 <= 48 limsup_n E_n
 < 48/1536
 = 1/32,
```

which is already the complete holonomy-coherence gap needed by the direct
nonhyperlinear route.

Thus the new highest-level analytic target is a **finite constant-gap energy
ceiling**, not synchronization, reconstruction, or asymptotic chart-frame
collapse.

## Attempts

- **Search a finite constant-gap SOS, not a vanishing estimate.**  A cyclic
  sum-of-squares certificate only has to leave slack `1/1536`; it need not
  dominate the four-cycle energy by the small residual norm with a uniform
  Lipschitz modulus.
- **Optimize the constant before the proof.**  The current `24` transfer comes
  from one exact eight-letter word for `t21`.  Any lower weighted word-energy
  certificate, or direct finite-group Dirichlet comparison from the four-cycle
  to `{t21,t12}`, enlarges the admissible ceiling automatically.
- **Use tracial compactness qualitatively.**  It is enough to rule out limiting
  exact A4/collision models carrying four-cycle energy at least `1/1536`.
  Quantitative stability of every intermediate gauge is unnecessary.
- **Dual-search bad multiplicity modes.**  If the ceiling fails in a finite
  truncation, keep the maximizing tracial/multiplicity mode as a concrete dual
  obstruction and enlarge only the packet residuals that see it.
- **Audit the abstract packet-collision quotient first.**
  `atlas-a4-packet-collision-quotient-audit` shows that a finite quotient gives
  a decisive fork: a collapsed chart factor closes the exact-regular lane by
  finite-group HS stability, while two surviving factors return an exact
  regular-margin multiplicity mode on which the proposed ceiling can be tested
  directly.
