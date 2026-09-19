---
rg: 2
id: fpbs-hermon-hutchcroft-anchored-expansion-citation
kind: route
title: Import Hermon--Hutchcroft's anchored expansion corollary for supercritical clusters
target: fpbs-hermon-hutchcroft-anchored-expansion
requires: []
---

Citation import, not a reproof. J. Hermon and T. Hutchcroft, *Supercritical
percolation on nonamenable graphs: Isoperimetry, analyticity, and exponential
decay of the cluster size distribution*, arXiv:1904.10448v3 (Invent. Math.
2021), Section 1.2, read from the arXiv PDF on 2026-09-18. Verbatim:

> Benjamini, Lyons, and Schramm [10] defined the anchored Cheeger constant of
> a connected, locally finite graph `G = (V,E)` to be
> `Phi*_E(G) := lim_{n->infinity} inf { |d_E K| / sum_{u in K} deg(u) :
> K ⊆ V connected, v in K, and n <= |K| < infinity }`, where `v` is a vertex
> of `G` whose choice does not affect the value obtained, and said that `G`
> has anchored expansion if `Phi*_E(G) > 0`.

> **Corollary 1.4.** Let `G` be a connected, locally finite, nonamenable,
> transitive graph, and let `p_c < p <= 1`. Then every infinite cluster in
> Bernoulli-`p` bond percolation on `G` has anchored expansion almost surely.

The same paper, Section 3.3 (proof of Corollary 1.5), also states the
consequence used downstream, verbatim: "Since `K_v` has anchored expansion
a.s. on the event that it is infinite by Corollary 1.4, it must trivially also
have exponential growth a.s. on the event that it is infinite." The
downstream proof `fpbs-intrinsic-growth-rate-positive-above-pc-proof` does not
rely on that sentence; it rederives the growth from Corollary 1.4 in a few
lines.

The abstract of arXiv:1904.10448 states the same corollary: "Every infinite
cluster in supercritical percolation on a transitive nonamenable graph has
anchored expansion almost surely. This answers positively a question of
Benjamini, Lyons, and Schramm (1997)."

This route asserts only that the cited corollary says what the target records.
