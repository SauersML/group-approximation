---
rg: 2
id: fpbs-dead-fiid-hutchcroft-pete-limit-recursion
kind: route
title: Run the Hutchcroft--Pete thinning recursion inside the factor-of-iid class and pass to its non-ergodic limit
target: fpbs-kazhdan-sparse-spines
requires: []
artifacts:
  - research/artifacts/fpbs/docs/normal-subgroup-fixed-price.md
---

Dead: the attempt keeps every stage of the Hutchcroft--Pete union-of-thinned-copies
recursion a factor of i.i.d. (arXiv:1810.11015, Section 2.2). It then argues as
they do: the marginal stays `p` while neighbour disagreement tends to zero, the
stages converge weakly to `p delta_V + (1-p) delta_empty`, and the Glasner--Weiss
closedness of ergodic measures forces a positive-frequency cluster, hence a
sparse factor-of-i.i.d. spine.

Every factor of i.i.d. is ergodic, so
fpbs-kazhdan-ergodic-percolation-disagreement-floor bounds its neighbour
disagreement below by `kappa^2 p (1-p)`. The recursion therefore cannot converge
to the non-ergodic limit inside that class. Within the class, the limit argument
shows only that exact thinning of clusters fails at some stage, and that gives
no cluster of positive frequency. A quantitative condensation theorem at
disagreement bounded below would be needed instead.
