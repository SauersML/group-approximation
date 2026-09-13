---
rg: 2
id: non-ascending-hnn-extensions-lack-bvc-citation
kind: route
title: Import von Puttkamer–Wu Lemma 2.4
target: non-ascending-hnn-extensions-lack-bvc
requires: []
---

Citation import, read on 2026-09-13 from the PDF of arXiv:1607.03790v2, page 8:

"Lemma 2.4. Let H be a group and let θ: A → B be an isomorphism between two subgroups of H.
If [H : A], [H : B] ≥ 2, then the corresponding HNN extension G = H∗θ does not have BVC."

Proof there: pick `a in H \ B` and `b in H \ A` and put `w_n = t^{-1} a t^{n+1} b`. These are
cyclically reduced of length `n + 2`. Collins' lemma and the stable-letter exponent sum show
that no two `w_n` have conjugate nonzero powers, which BVC forbids (their Lemma 1.6).
