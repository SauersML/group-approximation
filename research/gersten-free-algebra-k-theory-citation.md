---
rg: 2
id: gersten-free-algebra-k-theory-citation
kind: route
title: Import Weibel, The K-book, Chapter V Theorem 6.5 (Gersten) and Chapter IV Corollary 1.7.1
target: gersten-free-algebra-k-theory
requires: []
---

Citation import. C. Weibel, *The K-book: an introduction to algebraic K-theory* (Grad. Stud. Math. 145,
AMS, 2013). Read 2026-09-20 from the author's chapter PDFs
`https://sites.math.rutgers.edu/~weibel/Kbook/Kbook.V.pdf` and `Kbook.IV.pdf`, text extracted with
pypdf. Every quoted word is verbatim.

- **V, Theorem 6.5.** "(Gersten) Let A = k{X} be a free k-algebra on a set X, where k is noetherian
  regular. Then K∗(k{X})∼= G∗(k{X})∼= K∗(k)."
  - The proof there ends: "The proof of 6.4 goes through (Exercise 6.13) to prove that
    G∗(k)∼= G∗(A), as desired." The map in 6.4 is the one induced by `k ⊂ R`, so the isomorphism
    is induced by the inclusion `k -> k{X}`.
  - Next paragraph: "As remarked in IV.1.9(iv), the calculation K∗(Z{X}) = K∗(Z) was used by
    Anderson".
- **IV, before and at Corollary 1.7.1.** "Recall from Theorem III.5.5 that the Steinberg group St(R)
  is the universal central extension of the perfect group E(R). Thus we have: Corollary 1.7.1. The
  group K2(R) = π2BGL(R)+ is isomorphic to the group K2(R)∼=H2(E(R); Z) of chapter III."

So in degree 2 the theorem is about `K_2(R) = ker(St(R) -> E(R))`.

Primary source (not read): S. M. Gersten, *K-theory of free rings*, Comm. Algebra 1 (1974), 39–64.
