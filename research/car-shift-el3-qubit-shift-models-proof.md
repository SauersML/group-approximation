---
rg: 2
id: car-shift-el3-qubit-shift-models-proof
kind: route
title: Qubit-shift finite models make EL_3 of the Bernoulli CAR crossed product a marked limit of SL_{3·2^N}(F_2)
target: car-shift-el3-is-marked-limit-of-qubit-shift-sl-groups
requires: [car-bernoulli-crossed-product-is-lamplighter-ring, elementary-groups-over-fg-rings-have-property-t]
artifacts:
  - research/artifacts/sk-strong-5-second-family-2026-09-13.md
---

Notation: `A_n = ⊗_{[−n,n]} M_2(F_2) ⊆ B`, and `x^{(t)}` denotes `x ∈ M_2(F_2)` placed at site `t`.

1. **Generation and (T).** `e_11 = e_12e_21`, `e_22 = e_21e_12` and `1 = e_11 + e_22` give `M_2(F_2)` at site 0.
   Conjugation by `s^t` moves it to site `t`, and the sites generate `B`. So `R` is finitely generated and `EL_3(R)`
   has (T) (EJZ). Since `e_ij(xy) = [e_ik(x), e_kj(y)]` and `e_ij(x+y) = e_ij(x)e_ij(y)`, the `e_ij(g)` with `g` among the
   four generators generate `EL_3(R)`.
2. **Models.** For `N ≥ 4L+1`, let `ι_N: A_{2L} → End(V_N)` place site `t` at `t mod N` and tensor with the identity
   elsewhere. It is a unital algebra homomorphism. For `y = Σ_{|j|≤L} b_j s^j` with `b_j ∈ A_L`, put
   `φ_N(y) = Σ_j ι_N(b_j) π_N^j`. Since `π_N ι_N(x^{(t)}) π_N^{-1} = ι_N(x^{(t+1)})`, and
   `(b s^i)(b' s^j) = b σ^i(b') s^{i+j}` with `σ^i(b') ∈ A_{2L}`, we get `φ_N(yz) = φ_N(y)φ_N(z)` whenever
   `y, z, yz` are of this form.
3. **Onto.** `ρ_N(t_1), ρ_N(t_2)` generate `M_2` on factor 0. Conjugation by `π_N` gives every factor, and the factors
   generate `End(V_N) = M_{2^N}(F_2)`.
4. **Agreement.** A monomial of length `≤ L` in `t_1, t_2, t_±` maps under `π` to `b s^j` with `|j| ≤ L` and `b ∈ A_L`,
   since each `s^{±1}` moves sites by one. By induction with step 2, `φ_N ∘ π = ρ_N` on elements of degree `≤ L`.
5. **Injectivity.** Let `y = Σ_{|j|≤L} b_j s^j ≠ 0` with `b_j ∈ A_L`, pick `b_{j_0} ≠ 0`, and let `N > 8L+4` and
   `p = ⌊N/2⌋`.
   - Take a configuration `c ∈ {0,1}^{Z/N}` with an arbitrary pattern on `[−2L,2L]`, a single `1` at `p`, and `0`
     elsewhere.
   - Then `π_N^j δ_c = δ_{σ^j c}`, and `ι_N(b_j)` changes only the coordinates in `W = [−L,L]`. So `ι_N(b_j) π_N^j δ_c`
     is a combination of basis vectors that agree with `σ^j c` off `W`.
   - Off `[−3L,3L]` these basis vectors have exactly one `1`, at `p+j`, and `p+j` is at distance `> L` from `[−3L,3L]`.
     So the terms for distinct `j` have disjoint supports.
   - Hence `φ_N(y)δ_c = 0` forces `ι_N(b_{j_0}) δ_{σ^{j_0}c} = 0`.
   - As the pattern on `[−2L,2L]` varies, `σ^{j_0}c` restricted to `W` runs over all of `{0,1}^W`, while
     `ι_N(b_{j_0}) = b_{j_0} ⊗ 1`. So `b_{j_0} = 0`, a contradiction.
6. **Marked limit.** Let `w` be a word of length `L` in the `e_ij(t)`. The entries of `π(w) − I_3` have degree `≤ L`. By
   steps 4 and 5, for `N > 8L+4`, `w = 1` in `EL_3(R)` iff these entries vanish, iff `ρ_N(w) = I`. The image of `EL_3(F)`
   under `ρ_N` is `EL_3(M_{2^N}(F_2)) = SL_{3·2^N}(F_2)`: transvections generate it, and transvections inside one block
   are commutators of transvections between blocks. Over `F_2` it equals `PSL`, which is simple. So `EL_3(R)` is the
   marked limit of these finite simple groups, and in particular it is LEF.
7. **Expanders.** `EL_3(F)` has (T), and property (T) of a group passes to its finite quotients with a uniform Kazhdan
   constant for the image generating set. So the Cayley graphs of `SL_{3·2^N}(F_2)` for the images of the 24 generators
   form an expander family. ∎
