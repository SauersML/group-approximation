---
rg: 2
id: sl2-pq-flexibility-from-sl2-p-flexibility
kind: route
title: "Stabilize the two vertex groups of the q-adic amalgam separately, pad, and glue by exact vertex-pair repair"
target: sl2-z-inverse-pq-is-flexibly-hs-stable
requires:
  - sl2-z-inverse-p-is-flexibly-hs-stable
  - sl2-pq-exact-vertex-pairs-have-uniform-linear-repair
  - flexible-hs-metric-controls-words-and-padding
---

Let `p` be a prime for which `sl2-z-inverse-p-is-flexibly-hs-stable` holds,
and `q ≠ p` any other prime. The route proves the target for the pair
`(p,q)`. That is the instance consumed by
`non-hyperlinear-from-hnn-over-sl2-pq-flexible-stability`.

**The presentation.** Use the amalgam `(VR0)` from
`sl2-pq-exact-vertex-pairs-have-uniform-linear-repair`, `A = C *_D C'`.
- `C` and `C' = gCg^(-1) ≅ C` are finitely presented.
- `D` has finite index in `C`, so it is finitely generated.
- `A` is presented by the generators `S_C ⊔ S_(C')`, with three families of relators:
  - relators `R_C` of `C`;
  - relators `R_(C')` of `C'`;
  - for each `s ∈ S_D`, the edge relator `w_s = w'_s`, where `w_s` and `w'_s` are words for `s` in `S_C` and in `S_(C')`.

Flexible HS stability does not depend on the finite presentation, so it is
enough to treat this one.

**Step 1: stabilize each vertex group.** Let `φ_n` be unitary tuples on
`V_n`, of dimension `d_n`, whose defect on all relators tends to `0`.
- `φ_n|_(S_C)` is an asymptotic representation of `C`. Flexible stability of `C` gives an exact `ρ_n` on `V_n ⊕ E_0` with `dim E_0 = o(d_n)` and `||P ρ_n(s) P - φ_n(s)||_2 → 0`.
- `C'` is isomorphic to `C`, so the same argument gives an exact `ρ'_n` of `C'` on `V_n ⊕ E_1`.

**Step 2: the off-diagonal blocks are small.** `ρ_n(s)` is unitary and its
`V`-corner is `o(1)`-close to the unitary `φ_n(s)`. So

```text
||P^⊥ ρ_n(s) P||_F^2 = d_n - ||P ρ_n(s) P||_F^2 = o(d_n).
```

The same holds for `P ρ_n(s) P^⊥`.

**Step 3: pad.** Put `W = V_n ⊕ E_0 ⊕ E_1` and `Φ_n = φ_n ⊕ 1`. Let
`σ_0 = ρ_n ⊕ 1_(E_1)` and let `σ_1` be `ρ'_n` on `V_n ⊕ E_1`, extended by `1_(E_0)`.
- By Step 2, and because the padding blocks are `o(dim W)`, `σ_0 ≈ Φ_n` on `S_C` and `σ_1 ≈ Φ_n` on `S_(C')`, with `o(1)` errors in normalized norm on `W`.
- Word Lipschitz (`flexible-hs-metric-controls-words-and-padding`), together with the edge relators of `φ_n`, gives

  ```text
  δ_n = max_(s ∈ S_D) ||σ_0(w_s) - σ_1(w'_s)||_2
      <= |w_s| o(1) + ||φ_n(w_s) - φ_n(w'_s)||_2 + |w'_s| o(1) → 0.
  ```

**Step 4: glue.** `sl2-pq-exact-vertex-pairs-have-uniform-linear-repair`
gives an exact `π_n` of `A` on `W` with the following errors:
- at most `K δ_n` from `σ_0` on `S_C`;
- at most `K δ_n` from `σ_1` on `S_(C')`.

**Step 5: compress.** On `s ∈ S_C`,

```text
||P π_n(s) P - φ_n(s)||_(2,V) <= √(dim W/d_n) · K δ_n + ||P ρ_n(s) P - φ_n(s)||_(2,V) → 0.
```

The same holds on `S_(C')`. Since `dim W/d_n → 1`, `π_n` is a flexible repair
of `φ_n`. ∎

**What this changes.**
- The two-prime node is no harder than the one-prime node.
- The q-adic tree contributes no obstruction at all. It cannot supply one,
  because every exact vertex pair is linearly repairable.
- A refutation of `sl2-z-inverse-pq-is-flexibly-hs-stable` for a pair
  `(p,q)` therefore also refutes flexible stability of the vertex group
  `SL_2(Z[1/p])`, and of `SL_2(Z[1/q])` by symmetry.
