---
rg: 2
id: sofic-universal-envelope-forces-non-lef-simple-kazhdan
kind: claim
title: A universal sofic embedding theorem would produce a sofic infinite simple Kazhdan group that is not LEF
distinct_from:
  gap-sofic-approximations-are-local-embeddings: that says which sofic approximations are automatically local embeddings; this says what a universal embedding statement would cost, namely a sofic simple Kazhdan group outside the LEF class.
---

**ESTABLISHED (unreviewed).** Suppose every finitely generated sofic group embeds in an infinite
simple group with property (T) that is sofic. Then there is an infinite simple Kazhdan group that is
sofic and not LEF.

**Proof in one line.** LEF passes to subgroups, and there are finitely generated sofic groups that
are not LEF, for instance `BS(2,3)`: it is finitely presented, sofic and not residually finite, and a
finitely presented LEF group is residually finite (Vershik--Gordon). An envelope of such a group
cannot be LEF.

**Why it matters.** The note's groups `EL_3(LC(X,F_2) ⋊ Z)` are LEF, so they cannot serve as
envelopes for non-LEF inputs. Every sofic simple Kazhdan group currently on this graph is LEF, so the
universal statement is at least as hard as producing one sofic non-LEF example. That existence
question is open, and `gap-sofic-approximations-are-local-embeddings` shows the usual algebraic
models cannot produce it: through `GL_N(F_q)` acting on vectors, on affine spaces or on lines, a
sofic approximation is automatically a local embedding.

Route: `sofic-universal-envelope-forces-non-lef-simple-kazhdan-proof`.

**Review (sk-verify-4, 2026-09-13): PASS.** LEF passes to subgroups; `BS(2,3)` is finitely presented, sofic and not residually finite; finitely presented LEF groups are residually finite. It does not use the swap double. See `research/artifacts/sk-review-4-2026-09-13-part4.md` §1.
