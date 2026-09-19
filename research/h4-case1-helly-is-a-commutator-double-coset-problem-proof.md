---
rg: 2
id: h4-case1-helly-is-a-commutator-double-coset-problem-proof
kind: route
title: Applying ρ_Y to an N-conjugate inside P_Y shows it is unchanged, which solves the conjugate-membership problem and turns (*) into an equality of commutators
target: h4-case1-helly-is-a-commutator-double-coset-problem
requires:
  - h4-case1-pure-centre-iff-px-conjugate-of-f-holds-triple
artifacts:
  - experiments/h4-commutator-helly-2026-09-18/chelly.py
  - experiments/h4-commutator-helly-2026-09-18/C13.log
  - experiments/h4-commutator-helly-2026-09-18/C23.log
  - experiments/h4-commutator-helly-2026-09-18/C33.log
---

We use only three facts:
- `ρ_Y : P → P_Y` is a homomorphism that is the identity on `P_Y`;
- `F` is normal in `P_Y`, being the kernel of the homomorphism `ρ_X|P_Y`;
- `P_Z ≤ P_Y`, so `P_Z` normalises `F`.

**(R).** Let `γ ∈ N`, `g ∈ P_Y` and `h = γgγ^{-1} ∈ P_Y`.
- Since `ρ_Y` is the identity on `P_Y`, `ρ_Y(h) = h`.
- Since `ρ_Y` is a homomorphism with `ρ_Y(γ) = 1` and `ρ_Y(g) = g`, also `ρ_Y(h) = ρ_Y(γ)gρ_Y(γ)^{-1} = g`.

So `h = g`.

For the second statement:
- If `f ∈ F ∩ γFγ^{-1}`, then `γ^{-1}fγ ∈ F ⊂ P_Y`, so (R) applied to `γ^{-1} ∈ N` gives `γ^{-1}fγ = f`, i.e. `f ∈ C_F(γ)`.
- Conversely, `C_F(γ) ⊂ F ∩ γFγ^{-1}`.
- The statement for `γ^{-1}Fγ` is the same with `γ` replaced by `γ^{-1}`. ∎

**(H′).** By (H) of `h4-case1-pure-centre-iff-px-conjugate-of-f-holds-triple`, the pure bounds are the `γA_Y` with
`γ ∈ P_X` and `e_0 = α_1, e_1 = β_1α_2β_1^{-1} ∈ γFγ^{-1}`. (Then `e_2 = (e_0e_1)^{-1}` is in it as well.)

*Reduction to `γ ∈ N`.* Write `γ = nz` with `n ∈ N` and `z ∈ P_Z`. Then `γFγ^{-1} = nFn^{-1}`, because `z` normalises `F`.
Also `γA_Y = nA_Y`, because `z ∈ A_Y`. So we may assume `γ ∈ N`.

*The corner `e_0`.* `α_1 ∈ γFγ^{-1}` iff `γ^{-1}α_1γ ∈ F`. By (R) this happens iff `γ^{-1}α_1γ = α_1`, i.e. iff
`γ ∈ C_N(α_1)`.

*The corner `e_1`.* Put `δ = γ^{-1}β_1 ∈ N`. Then `e_1 ∈ γFγ^{-1}` iff `δα_2δ^{-1} ∈ F`. By (R) this happens iff
`δ ∈ C_N(α_2)`, i.e. iff `γ ∈ β_1C_N(α_2)`.

So the pure bounds are the `γA_Y` with `γ ∈ C_N(α_1) ∩ β_1C_N(α_2)`. This set is nonempty iff
`β_1 ∈ C_N(α_1)C_N(α_2)`. ∎

**(K).** First, `(*)` is `[u, a] = [v, b]`. Expand the right side:
`[v, b] = β_3β_1α_2β_1^{-1}β_3^{-1}α_2^{-1}`.
Now transform the equation `[u, a] = β_3α_1^{-1}β_3^{-1}α_1 = [v, b]` in three steps:
1. multiply on the left by `β_3^{-1}`;
2. multiply on the right by `α_2β_3`;
3. multiply on the left by `α_1`.

The result is exactly `(*)`.

*Where `k` lives.* `ρ_X` kills `a` and `ρ_Y` kills `u`. Hence `ρ_X(k) = uu^{-1} = 1` and `ρ_Y(k) = aa^{-1} = 1`.

*Pure bounds as solutions `w`.* For `x, y ∈ N` and any `f`, `[x, f] = [y, f]` iff `xfx^{-1} = yfy^{-1}` iff
`x^{-1}y ∈ C_N(f)`. Let `w ∈ N` and put `γ = u^{-1}w`.
- `[w, a] = k = [u, a]` iff `γ ∈ C_N(a) = C_N(α_1)`.
- `[w, b] = k = [v, b]` iff `v^{-1}w ∈ C_N(b)`, i.e. iff `γ^{-1}β_1 = w^{-1}v ∈ C_N(α_2)`.

So `w` solves both equations iff `γ ∈ C_N(α_1) ∩ β_1C_N(α_2)`, and (H′) applies.

*The three vertices.* The vertex witnesses `γ = β_3^{-1}, 1, β_1` of the w12 node correspond to `w = 1, u, v`. For each,
one of the two equations holds automatically:
- `w = 1` solves both iff `k = 1`;
- `w = u` solves both iff `[u, b] = k`;
- `w = v` solves both iff `[v, a] = k`. ∎

**(D).** If `α_1 = α_2`, then `C_N(α_1)C_N(α_2) = C_N(α_1)` is a subgroup. So (H′) holds iff `β_1 ∈ C_N(α_1)`, and this is
exactly the witness `γ = β_1`, i.e. the vertex `y_2`. ∎

**Remark (what is left, and the tree route).** Case 1 of the target is now equivalent to the following statement about
the concrete groups `N` and `F`.

> `(H″)`: for `a ≠ b` in `F` and `u, v ∈ N`, `[u, a] = [v, b]` implies `u^{-1}v ∈ C_N(a)C_N(b)`.

- **The step (R) cannot supply.** Neither retraction sees `(*)`: `ρ_X` and `ρ_Y` both map `(*)` to a tautology.
  A proof of `(H″)` needs an invariant of `⟨N, F⟩` finer than the pair `(ρ_X, ρ_Y)`. This pair maps `⟨N, F⟩` onto
  `N × F`, and `k` lies in its kernel.
- **If `⟨N, F⟩` were the free product `N * F`.** Then `[u, a]` would be reduced of length 4 whenever `u, a ≠ 1`. So
  `k ≠ 1` would force `u = v` and `a = b`, and `(H″)` would be immediate.
- **But it is not.** By (T), `x_0 = s_4^2` commutes with `p_2` and `p_3`.
- **Coincidences that do occur are resolved at a vertex.** Take `u = v = x_0`, `a = p_1` and `b = p_1p_2`. Then
  `k = [x_0, p_1] ≠ 1`, and the witness `w = u = v` works.
- **A tree action is exactly what is needed.** Suppose `ker ρ_X` acted on a tree with the `P_X`-conjugates of `F` among
  its vertex stabilisers. Then Serre's lemma, applied to the elliptic elements `e_0`, `e_1` and `e_0e_1`, would give
  `(H″)`. By (R), the edge groups at `F` would have to include the `C_F(n)` for `n ∈ N`. In particular `⟨p_2, p_3⟩`
  would be an edge group, since it lies in `C_F(x_0)`.

**Computation.** `chelly.py LA LB` builds two balls:
- `NB`: the elements of `N` of length ≤ `LB` in `x_0, …, x_11`, deduplicated by Garside normal form;
- `FB`: the elements of `F` of length ≤ `LA` in `p_1, p_2, p_3`.

For each `f ∈ FB` it stores the 64-bit hash of `[u, f]` for every `u ∈ NB`. For each ordered pair `(α_1, α_2)`, the
common nontrivial hash classes of `a = α_1^{-1}` and `b = α_2` give all candidate tuples in the box. Each candidate is
re-verified exactly, and false hash hits are counted separately. Then (K) classifies every genuine tuple: VC,
non-vertex pure centre inside the ball (`HBALL`), or undecided (`HCAND`).

| run | F-ball | N-ball | pairs | tuples with `k ≠ 1` | VCFAIL | HBALL | HCAND | time |
|---|---|---|---|---|---|---|---|---|
| `C13.log` (`LA = 1`, `LB = 3`) | 7 | 13273 | 30 | 0 | 0 | 0 | 0 | 36 s |
| `C23.log` (`LA = 2`, `LB = 3`) | 37 | 13273 | 1260 | 32548 | 0 | 0 | 0 | 179 s |
| `C33.log` (`LA = 3`, `LB = 3`; **partial**, stopped by the 1200 s timeout) | 187 | 13273 | 10175 | 134352 | 0 | 0 | 0 | 1200 s |

`C13.log` also records the selftest of (R). For the first 7 elements of `FB` and the first 400 of `NB`, the independent
test `fmem.in_F` (w12) found 142 conjugates `ufu^{-1}` in `F`. Each was equal to `f`: **0 violations**.

The `LA = 1` box contains the two diagonal pairs `α_1 = α_2 = p_i^{±1}` that w12's `vsearch3` could not finish. By (D),
they no longer need a search.
