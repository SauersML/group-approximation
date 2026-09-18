---
rg: 2
id: rsg-equicontinuity-program-cannot-exclude-gl-n-q-proof
kind: route
title: Proof that the equicontinuity test cannot exclude GL_n(Q) from finite-nucleus RSGs
target: rsg-equicontinuity-program-cannot-exclude-gl-n-q
requires: []
---

Complete direct proof. Lane gq-deep-free-3, 2026-09-17. Not independently reviewed.

**Item 1.** In `Aff(Q)`, with `d(x) = px` and `u(x) = x + q`, `d u d^-1 (x) = p(x/p + q) = x + pq`,
so `d u d^-1 = u^p`. In `SL_2(Q)`, `diag(p, 1/p) e_12(q) diag(p, 1/p)^-1 = e_12(p^2 q) = e_12(q)^(p^2)`.
`GL_n(Q)` contains `SL_2(Q)` and every `e_ij(q)` is conjugate to some `e_12(q')`. In each case
`|1| ≠ |k|`, so the hypothesis of the open claim holds with `f = d`, `g = u`, exponents `1, k`,
and its conclusion is that `{u^m}` is equicontinuous.

**Item 2, the space.** `A_f = Q ⊗ Ẑ` is locally compact, second countable, totally
disconnected, non-compact and has no isolated points; so is `A_f^n`. Its one-point
compactification `X_n` is compact, metrizable, totally disconnected and perfect, hence a
Cantor set. `GL_n(Q)` acts on `A_f^n` by continuous linear automorphisms. These are proper
maps, so they extend to homeomorphisms of `X_n` fixing `∞`. The action is faithful because
`Q^n ⊂ A_f^n`. The same holds for `Aff(Q)` on `X_1`.

**Item 2, equicontinuity.** Fix `q = a/b` and let `S = closure of {mq : m ∈ Z} ⊆ (1/b)Ẑ`,
which is compact. Put `Φ(s, x) = x + s x_j e_i` on `S × A_f^n` and `Φ(s, ∞) = ∞`. `Φ` is
continuous on `S × A_f^n`. It is continuous at `S × {∞}`: if `x_k → ∞`, `s_k ∈ S` and
`Φ(s_k, x_k) = y_k` stayed in a compact `C`, then `x_k = Φ(-s_k, y_k)` would lie in the
compact `Φ(-S × C)`, a contradiction. So `Φ` is continuous on the compact space `S × X_n`,
hence uniformly continuous. Therefore `{Φ(s, ·) : s ∈ S}`, which contains every
`e_ij(mq)`, is equicontinuous on `X_n`. The same argument with `Φ(s, x) = x + s` handles
`Aff(Q)` on `X_1`.

**Item 3.** Let a divisible abelian group `D ≠ 1` act faithfully on a compact
zero-dimensional metrizable space `E` as an equicontinuous family. By Arzelà–Ascoli the
closure `K` of `D` in `Homeo(E)` (uniform topology) is a compact group acting faithfully
on `E`. The identity component `K_0` has connected orbits in the totally disconnected `E`,
so it acts trivially, and `K_0 = 1`. Thus `K` is profinite, with open normal subgroups `U`
such that `K/U` is finite and `∩U = 1`. The image of `D` in a finite group `K/U` is a
finite divisible group, hence trivial, so `D ⊆ ∩U = 1`, a contradiction. For `(Q,+)` in the
adelic model the failure is visible at `∞`: points `x = -1/m!`, which tend to `∞`, are sent
by `x ↦ x + 1/m!` to `0`, while `∞` is fixed.
