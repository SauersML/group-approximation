---
rg: 2
id: sl3-canonical-double-replication-escapes-every-frobenius-basin
kind: claim
title: Canonical arithmetic-double microstates can be replicated outside every unnormalized Frobenius basin
artifacts:
  - research/artifacts/sl3-double-frobenius-normalization-audit-2026-08-21.md
distinct_from:
  exact-fd-invisibility-has-no-general-hs-robustification: that uses an external sofic group to refute a universal exact-to-HS principle; this is the exact replication calculus inside canonical microstates of the SL3 arithmetic double.
  bounded-degree-two-primitives-for-higher-rank-lattices: that asks for an operator-bounded cohomological primitive capable of running a normalized Newton iteration; this proves why the existing unnormalized Frobenius basin cannot be reached merely from canonical trace.
---

Let `D=A*_C A` be the `SL_3` arithmetic double and fix a finite
presentation.  Suppose `sigma_n` is any canonical-character normalized-HS
microstate sequence of `D`, in dimensions `d_n`.  Given arbitrary positive
numbers `L_n`, there are multiplicities `m_n>=1` such that the block replicas

```text
sigma_n^(rep) = sigma_n direct_sum ... direct_sum sigma_n   (m_n copies)
                                                                    (RFB1)
```

have all of the following properties.

1. Every normalized trace of every word is unchanged.
2. Every normalized-HS word defect is unchanged.
3. The maximum UNNORMALIZED Frobenius defect of the fixed defining relators
   is at least `L_n`.

In particular, even the full canonical character of the double supplies no
entry into a dimension-independent unnormalized Frobenius stability basin.
Any use of 2-Kazhdan/cohomological Frobenius stability must first prove a
global correction estimate homogeneous under replication; canonical trace,
bounded generation, and qualitative Frobenius stability do not provide that
normalization upgrade.

