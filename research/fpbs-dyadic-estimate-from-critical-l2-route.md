---
rg: 2
id: fpbs-dyadic-estimate-from-critical-l2-route
kind: route
title: Derive the dyadic projection estimate from Hutchcroft's critical l2 conjecture
target: fpbs-critical-dyadic-projection-estimate
requires:
  - fpbs-nonamenability-bounds-critical-connectivity-operator
  - fpbs-critical-l2-equivalent-to-dyadic-projection-estimate
---

SUFFICIENT and, graph by graph, NECESSARY route. Item 2 of
`fpbs-critical-l2-equivalent-to-dyadic-projection-estimate` turns a bounded
critical connectivity operator on a nonamenable Cayley graph into
`||Q_k|| <= C 2^(-3k/2)`, hence Q2. Item 3 shows no route to Q2 can avoid
proving that bound, because Q2 already implies it.

Consequence for `fpbs-universal-dyadic-route`: its only open prerequisite is
equivalent to `fpbs-nonamenability-bounds-critical-connectivity-operator`, so
that route is a reformulation of the direct l2 route and not an independent
decomposition of `fpbs-benjamini-schramm-universal`. Work on the size shells is
work on Hutchcroft's l2 conjecture and should be scored as such.
