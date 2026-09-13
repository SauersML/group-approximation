---
rg: 2
id: recursive-amenable-classes-have-uniform-folner-bounds-citation
kind: route
title: Import Cavaleri's Theorem 3.1 and Corollary 3.6 on Følner functions of recursively presented amenable groups
target: recursive-amenable-classes-have-uniform-folner-bounds
requires: []
---

Citation import of M. Cavaleri, arXiv:1703.04133v2, Theorem 3.1 and Corollary
3.6, quoted in the claim. The statements were read from the arXiv PDF, pages
1--9, on 2026-09-12 by lane `ex-complexity-amenable`.

**The argument there.** The proof was read and is recorded here; nothing is
re-proved.
- **The Reiter search.** For a candidate finitely supported function on the free
  group, enumerate the relators and merge the partition of its support as trivial
  words appear. The ratio `M_Q(f)` of Cavaleri's equation (5) only decreases
  toward the true invariance defect, so the search halts exactly when the
  pushforward is `n`-invariant.
- **Theorem 3.1.** Amenability guarantees that some characteristic function
  halts.
- **Corollary 3.6.** Run the uniform search over a c.e. list of presentations and
  take the maximum of the first `n` resulting bounds.
