---
rg: 2
id: rsg-equicontinuity-program-cannot-exclude-gl-n-q
kind: claim
title: The equicontinuity test for proper-power conjugates cannot exclude GL_n(Q), SL_2(Q) or Aff(Q) from finite-nucleus RSGs
distinct_from:
  finite-nucleus-rsg-proper-power-conjugates-are-equicontinuous: that is the OPEN claim that proper-power conjugates in a finite-nucleus RSG have equicontinuous cyclic groups; this shows that its conclusion, applied to the unipotents of GL_n(Q), is realized by a faithful action and so yields no exclusion.
  dyadic-affine-bs12-model-lies-in-no-finite-nucleus-rsg: that excludes one explicit non-equicontinuous copy of BS(1,2) from finite-nucleus RSGs; this is about every copy of Aff(Q) and the equicontinuous dynamics any such copy would have to have.
  gl-n-q-embeds-in-fp-simple-group: that is the root; this calibrates the rational-similarity-group route to it (BBMZ full contracting RSGs embed in finitely presented simple groups).
  germ-extensions-omit-standard-gl-n-q: that kills the standard linear adelic copies inside germ extensions of V by a piece-group argument; this uses the same adelic action only as a dynamical model, not as a host.
---

**ESTABLISHED** through `rsg-equicontinuity-program-cannot-exclude-gl-n-q-proof`
(lane proof, not independently reviewed).

**Setting.** `A_f` is the ring of finite adeles, `X_n = A_f^n ∪ {∞}` its one-point
compactification. `X_n` is a Cantor set: `A_f^n` is locally compact, second countable,
totally disconnected, non-compact and has no isolated points. `GL_n(Q)` acts on `X_n`
by `x ↦ gx`, `∞ ↦ ∞`, and `Aff(Q) = Q ⋊ Q^x` acts on `X_1` by `x ↦ ax + b`.

**Statement.**
1. **What the open test would give.** Suppose `H` is one of `Aff(Q)`, `SL_2(Q)`,
   `GL_n(Q)` (`n ≥ 2`) and `H ≤ G`, where `G` is a rational similarity group with finite
   nucleus (Belk–Bleak–Matucci–Zaremsky, arXiv:2309.06224v3). Every nontrivial root
   element `u = e_12(q)` (in `Aff(Q)`: `x ↦ x + q`) is conjugate in `H` to a proper power:
   `d u d^-1 = u^k` with `k = p` (`d = x ↦ px` in `Aff(Q)`) or `k = p^2`
   (`d = diag(p, 1/p)`). So if `finite-nucleus-rsg-proper-power-conjugates-are-equicontinuous`
   holds, every root cyclic group `<e_ij(q)>` acts equicontinuously on the RSG's space.
2. **That dynamics exists.** In the adelic actions above, every root cyclic group
   `{e_ij(mq) : m ∈ Z}` of `GL_n(Q)`, and every `{x ↦ x + mq : m ∈ Z}` in `Aff(Q)`, is an
   equicontinuous family of homeomorphisms of the Cantor set `X_n` (resp. `X_1`), and the
   actions are faithful. So the conclusion of item 1 is consistent with faithful actions
   of all these groups on Cantor sets. The equicontinuity claim, even if proved, excludes
   none of them. A proof that `GL_n(Q)` lies in no finite-nucleus RSG needs a further invariant.
3. **What any such copy must still satisfy.** The whole root group `(Q,+)` never acts
   equicontinuously: no nontrivial divisible abelian group acts faithfully as an
   equicontinuous family on a compact zero-dimensional metrizable space. So in any copy
   as in item 1 (with the open claim), each `<u(q)>` is equicontinuous while the family
   `{u(q) : q ∈ Q}` is not. The moduli of equicontinuity of `<u(1/m)>` must degrade
   along the divisibility chain `u(1/m!)`, exactly as in the adelic model, where
   `x ↦ x + 1/m!` carries the compact `Ẑ` towards `∞`.

**Use.** Lanes testing the RSG route (critic mechanism M5) should compare a candidate copy
with the adelic model of item 2. A kill must use the finite nucleus uniformly along the chain
`u(1/m!)`, as in item 3, not only per cyclic group.
