---
rg: 2
id: local-annihilation-implies-stepanov-condition-b
kind: claim
title: Does local annihilation of a simple ring imply Stepanov's linear-dependence condition (b)?
distinct_from:
  division-rings-satisfy-stepanov-b-not-local-annihilation: that is the converse direction, which fails (simple Artinian rings); this asks whether local annihilation implies (b).
artifacts:
  - research/artifacts/un-stepanov-credit-2026-09-13.md
---

**OPEN.** Let `R` be a unital simple ring with local annihilation (`LocalAnnihilation R` in
`GroupApproximation/Pestov91/SimpleModCentre.lean`), and `n ≥ 3`. Question: does Stepanov's condition (b) of
`stepanov-linear-dependence-standard-normal-structure` hold for `R`? That is, does every `a ∈ GL(n,R)` have some
`c = a^b` (`b ∈ E(n,R)`) and a nonzero column `α` with `α_i = (cα)_j = 0`?

A yes would make `local-annihilation-makes-projective-el-simple` a special case of Stepanov's Theorem 4.4. The converse
implication fails, by `division-rings-satisfy-stepanov-b-not-local-annihilation`.

## Attempts
- **Zero-divisor entry.** If some entry `c_(jk)` of an `E(n,R)`-conjugate of `a` has a nonzero right annihilator `x`,
  then `α = e_k x` with any `i ≠ k` gives (b). Local annihilation supplies left annihilators instead: `t ≠ 0` with
  `ts = 0` and `t a_(pq) s = 0`. That is the wrong side and gives no zero entry. Dies here.
- **No conjugation.** At `b = 1`, (b) for `a` asks for a nontrivial right linear relation among `n − 1` entries of one
  row of `a`. In `L_k(1,2)` the orthogonal isometries `s_0, s_1` satisfy no relation `s_0 x + s_1 y = 0` with
  `(x,y) ≠ 0`, since multiplying by `t_0` and `t_1` kills it. So for Leavitt-type rings (b) must use a nontrivial `b`.
  Dies at controlling all conjugates.
- **Opposite ring.** `LocalAnnihilation(R^op)` is the right-annihilator form, and Steinberg algebras have an involution,
  so both forms hold there. It still yields `s a_(pq) t = 0`, a two-sided annihilation, not a zero entry of a conjugate.
  Dies here.
- **What is known instead.** The criterion's proof does not pass through (b). Local annihilation produces a noncentral
  `ρ ∈ H` with `t(ρ − 1) = 0` entrywise and `t ≠ 0`, and Stepanov's Lemma 4.3 then forces a transvection in `H`
  (artifact §3).
