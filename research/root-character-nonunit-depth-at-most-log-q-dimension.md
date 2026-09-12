---
rg: 2
id: root-character-nonunit-depth-at-most-log-q-dimension
kind: claim
title: In a congruence representation of EL_r(F_q[x]), a root character of non-unit depth k needs a constituent of dimension at least q^k
distinct_from:
  pure-nonunit-root-mass-is-log-scale-folner: that bounds finite depths crudely by dim_(F_p) A_nu <= r(r-1)n' to count d-adic scales; this proves the exponentially sharper bound q^(depth) <= constituent dimension, unconditionally, by a Heisenberg count.
  nonunit-component-root-mass-is-log-scale-folner: that is the transport-defect bound on non-unit mass above depth one; this is an unconditional statement about genuine congruence representations that caps the non-unit depth any occurring root character can have.
  nonunit-projection-bounded-by-root-spectral-mass: that bounds the non-unit projection by root spectral mass; this bounds the depth of the characters carrying that mass by the dimension of their constituents.
artifacts:
  - research/artifacts/nh-h1-quantitative-2026-09-12.md
---

**ESTABLISHED.** Setup:
- `r >= 3`, `R_+ = F_q[x_1..x_d]`, `z = x_1 ⋯ x_d`, and `B = R_+/I` a finite quotient, split as `B = A_u × A_nu`
  into unit-type and non-unit local factors with idempotents `e_u`, `e_nu`.
- `π : St_r(B) -> U(N)` a unitary representation, and `μ` the normalized spectral measure of
  `f -> π(x_12(f))` on the characters of `(B, +)`.
- `χ_nu(f) = χ(e_nu f)` and `depth_nu(χ) = min{k >= 0 : χ_nu trivial on z^k R_+}`, as in
  `nonunit-component-root-mass-is-log-scale-folner`.
- `J_χ = {b ∈ B : χ(bB) = 1}`, the largest ideal of `B` inside `ker χ`.

1. **Annihilator codimension.** If `depth_nu(χ) = k`, then `e_nu, e_nu z, ..., e_nu z^(k-1)` are
   `F_q`-linearly independent modulo `J_χ`. So `|B/J_χ| >= q^k`.
2. **Heisenberg count.** Let `V_χ` be the `χ`-eigenspace of `π(x_12(B))`. If `V_χ ≠ 0`, then
   `dim V_χ >= |B/J_χ|`. The same holds for every irreducible constituent of `π` whose `x_12`-spectrum
   contains `χ`.
3. **Depth bound.** Every `χ` with `μ({χ}) > 0` satisfies

   ```text
   q^(depth_nu(χ))  <=  |B/J_χ|  <=  N·μ({χ})  <=  N.
   ```

   So `D(π) = max{depth_nu(χ) : μ({χ}) > 0}` is at most `log_q` of the largest dimension of an irreducible
   constituent of `π`, hence at most `log_q N`.

**Reading.**
- **Sharper scale count.** Item 4 of `pure-nonunit-root-mass-folner-proof` and of
  `nonunit-component-root-mass-folner-proof` bounds finite depths by `dim_(F_p) A_nu <= r(r-1)N`. Item 3
  is exponentially sharper, so the number of d-adic depth scales in the log-scale Følner bounds drops from
  about `log N` to about `log log N`. See `nonunit-root-mass-log-depth-scale-bound`.
- **Intrinsic.** `D(π)` does not change under amplification `π -> π ⊗ 1_m`, while `N` does.
- Nothing about stability or rounding is used.

No root is affected. Derivation: `root-character-depth-log-dimension-proof`.
