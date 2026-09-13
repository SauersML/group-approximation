---
rg: 2
id: tensor-tower-tails-feed-nontrivial-w-star-bundle
kind: route
title: A tensor tower with unsplittable tails gives a nontrivial W*-bundle with R fibres
target: nontrivial-w-star-bundle-with-r-fibres-exists
requires: [some-tensor-tower-has-unsplittable-tails, tensor-tower-bundle-trivial-iff-tails-softly-split]
---

The implication is the one written in `some-tensor-tower-has-unsplittable-tails`:
"By `tensor-tower-bundle-trivial-iff-tails-softly-split`, this is equivalent to the
nontriviality of the R-fibre bundle of `⊗_k End(W_k)` over `Π_k Y_k`. So it would answer
BBSTWW Question 3.14 (`nontrivial-w-star-bundle-with-r-fibres-exists`)."

So a tower whose tails admit no soft half splitting has a nontrivial R-fibre bundle, and that is
the existence statement of the target. This route records that step and adds no argument beyond
the two claims it requires. While `some-tensor-tower-has-unsplittable-tails` is open it establishes
nothing. Wired by ex-steward on 2026-09-13.
