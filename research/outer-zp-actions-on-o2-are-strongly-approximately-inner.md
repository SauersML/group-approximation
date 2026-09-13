---
rg: 2
id: outer-zp-actions-on-o2-are-strongly-approximately-inner
kind: claim
title: For every prime p, every outer Z/p-action on O_2 is strongly approximately inner
distinct_from:
  o2-z2-actions-fix-a-cartan-subalgebra: that asks for an invariant Cartan subalgebra and assumes strong approximate innerness; this asks whether strong approximate innerness is automatic for outer actions.
  zp-o2-action-kkg-trivial-iff-invariant-asymptotic-inner: that proves the implication from detection and the phantom consequence of failure; this is the open dynamical statement itself.
---

**OPEN.** Let `p` be prime and `α : Z/p ↷ O_2` pointwise outer. Are there
unitaries `u_n ∈ O_2^α` with `α_ω = lim_n Ad(u_n)` pointwise in norm?

**Literature status.** Barlak–Li II (arXiv:1704.04939v2), Remark 4.14(2), as
recorded in `izumi-rokhlin-approximately-representable-duality`: "it is not
known whether all Z_2-actions on O_2 are strongly approximately inner." The
remark does not single out outer actions.

**Why it matters.**
- **Implied by detection.** It follows from
  `zp-restriction-and-crossed-product-detect-kk-g-contractibility`, via
  `zp-o2-action-kkg-trivial-iff-invariant-asymptotic-inner`.
- **A counterexample is a phantom.** An outer action failing it gives a nonzero
  equivariant phantom, and so a negative answer to the Meyer–Nadareishvili
  converse at `p`.
- **Proved on the bootstrap layer.** It holds for every action in `B^G`,
  asymptotically and with invariant unitary paths (item 2 of that node).
- **Consequence for Barlak–Li.** Where it holds, the hypothesis "strongly
  approximately inner" in Barlak–Li Theorem 4.16 is automatic for outer actions.
- **Up to a sign at `p = 2` (lane ex2-uct-dual-action-transfer, unreviewed).**
  Let `α` be an outer `Z/2`-action on `O_2` whose crossed product is `O_2`.
  By `z2-o2-actions-anti-inner-and-o3-rokhlin-criterion`:
  - `α` is approximately inner by anti-invariant unitaries;
  - it is strongly approximately inner iff `2[1] = 0` in `K_0` of the fixed
    central sequence algebra, iff that algebra contains a unital `O_3`.

  For general `p`, the forms twisted by characters are the fixed points of the
  unit class in `o2-central-sequence-k-theory-bi-cyclotomic-transfer`.

Route: `outer-zp-actions-on-o2-strongly-approx-inner-via-detection`.

## Attempts

- Through `outer-zp-actions-on-o2-strongly-approx-inner-via-detection`, waiting on `zp-restriction-and-crossed-product-detect-kk-g-contractibility`. The only route into that claim, `zp-detection-from-strong-approximate-innerness`, needs this claim back, so the pair is an equivalence rather than an attack. The live attempt is the `p = 2` criterion `z2-o2-actions-anti-inner-and-o3-rokhlin-criterion` above.
