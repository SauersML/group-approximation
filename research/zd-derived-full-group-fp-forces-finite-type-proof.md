---
rg: 2
id: zd-derived-full-group-fp-forces-finite-type-proof
kind: route
title: Nested commutators of 3-cycles act as occurrence 3-cycles on every configuration with legal small windows, so a finite presentation cuts out the subshift
target: zd-derived-full-group-fp-forces-finite-type
requires:
  - minimal-z2-subshift-derived-full-groups-are-fg-simple
---

**Case `d = 1`.** An infinite minimal `Z`-subshift is not of finite type, and its derived full
group is not finitely presented by Matui (arXiv:math/0404117, the theorem after TeX line 1104). The
implication holds vacuously. Assume `d >= 2` below.

**Notation.**
- `Omega = Z^d` with a colouring `c : Z^d -> A`. A pattern `pi` on a finite `P` *occurs at* `w` if
  `c(w + p) = pi(p)` for `p ∈ P`, and `Occ_c(pi)` is the set of such `w`.
- For distinct `t_1, t_2, t_3 ∈ Z^d` with the three sets `Occ_c(pi) + t_i` pairwise disjoint, let
  `tau_c(pi; t_1, t_2, t_3)` be the permutation of `Z^d` that sends `w + t_1 -> w + t_2 -> w + t_3 -> w + t_1`
  for `w ∈ Occ_c(pi)` and fixes everything else.
- For `c = x ∈ X` this is the action on the orbit of `x` of ChJN's element `T_(pi,(t_1,t_2,t_3))`
  (arXiv:1602.04255, lines 136–142).
- `R_1` is ChJN's radius (line 166): no legal `B(R_1)`-pattern is compatible with its translate by
  a vector `u` with `0 < |u|_1 <= 3`. Fix `R >= R_1 + 2`.
- Call `c` **`m`-legal** if every pattern of `c` on a translate of `B(m)` occurs in `X`.
- **Generators.** For a legal `pi` on `B(R)` and `e ∈ S_d = {±e_1, ..., ±e_d}`, let `s = s(pi, e)` be
  the homeomorphism `x -> sigma^(kappa(x)) x` of `X`, where `(sigma^u x)(p) = x(p + u)` and
  `kappa(x) = e`, `-2e`, `e` or `0` according as `0 ∈ Occ_x(pi)`, `Occ_x(pi) + e`,
  `Occ_x(pi) - e`, or none of these.
  - On the orbit `v <-> sigma^v x` it acts as `tau_x(pi; 0, e, -e)`.
  - `S` is the set of all `s(pi, e)`. It contains ChJN's `𝒯_R` up to inverses, so it generates
    `G = D([[Z^d ~ X]])` (ChJN, Proposition at line 171 and the Proposition after line 206;
    `minimal-z2-subshift-derived-full-groups-are-fg-simple`).
- **Rule action.** On any colouring `c`, `s(pi, e)` acts by `s_c = tau_c(pi; 0, e, -e)`.

**Lemma 0 (disjointness).** Let `c` be `(R_1 + 3)`-legal. Let `P, P'` be finite sets containing
`B(R_1)`, and `pi, pi'` patterns on them that agree on `B(R_1)`. If `a, b ∈ Z^d` with
`0 < |a - b|_1 <= 3`, then `(Occ_c(pi) + a) ∩ (Occ_c(pi') + b) = ∅`.
- *Proof.* A common point gives `w, w'` with `w' = w + a - b`, and the pattern
  `pi_0 = pi|B(R_1)` occurs at both. The union of the two windows lies in `B(R_1 + 3) + w`, so it
  is legal. Then `pi_0` is compatible with its translate by `a - b`, which contradicts the choice of
  `R_1`.
- In particular each `s_c` is a well-defined permutation.

**Lemma A (ChJN, Lemma before Corollary `cor:patchesunion`, source lines 144–158, read from
source).**
- *Setting.* `A_i, B_i` (`i = 1, 2, 3`) are subsets of a set, and only `A_1, B_1` may intersect.
  `a` has order 3, cycles `A_1 -> A_2 -> A_3 -> A_1` and fixes the rest. `b` does the same for the
  `B_i`.
- *Conclusion.* `[[b^(-1), a^(-1)], [b, a]]` acts as `a` on `C ∪ aC ∪ a^2 C`, with `C = A_1 ∩ B_1`,
  and fixes everything else.

**Words.** For `r >= R`, every pattern `q` on `B(r)` (legal or not) and every `e ∈ S_d = {±e_i}`
gets a word `W(q, e)` in the free group on `S`.
- **Base, `r = R`.** `W(q, e) = T_(q,(0,e,-e))` if `q` is legal, and the empty word otherwise.
- **Step, from radius `r` to `r+1`.** Let `q` be a pattern on `B(r+1)`.
  - Enumerate `S_d = {h_1, ..., h_(2d)}` and put `Q_0 = q|B(r)`, `Q_j = q|(B(r) ∪ ∪_(k <= j) (B(r) + h_k))`.
  - For `h ∈ S_d` let `q_h` be the translate to `B(r)` of `q|(B(r)+h)`: `q_h(p) = q(p + h)`.
  - Choose a perpendicular direction `e^⊥` to `e`.
  - Define `W(Q_j, e) = [[b^(-1), a^(-1)], [b, a]]` with `a = W(Q_(j-1), e)` and:
    - (i) `b = W(q_(h_j), h_j)` if `h_j ⊥ e`;
    - (ii) `b = W(q_(h_j), e^⊥)` if `h_j = ±e`.
  - Put `W(q, e) = W(Q_(2d), e)`. The words `W(Q_j, ·)` with `0 < j < 2d` are auxiliary.

**Lemma B.** Let `c` be `N`-legal with `N >= max(R, R_1 + 3)`. Then for every pattern `q` on `B(r)`,
`r >= R`, and every `e`, the word `W(q, e)` evaluated through the rule action equals
`tau_c(q; 0, e, -e)`. The same holds for the auxiliary `Q_j`.

*Proof.* By induction on `r` and `j`.
1. **Base.** For legal `q` this is the definition of the rule action. For illegal `q` there are no
   occurrences, since `N >= R`, so `tau_c` is the identity.
2. **Setup for the step.** Put `pi = Q_(j-1)` (support `P ⊇ B(r)`) and `pi' = q|(B(r) + h)`,
   `h = h_j`. Both contain `pi_0 = q|B(R_1)`, because `r >= R_1 + 1`. We have
   `Occ(Q_j) = Occ(pi) ∩ Occ(pi')`, and `Occ(q_h) = Occ(pi') + h`.
3. **Case (i).**
   - The blocks of `a = tau(pi; 0, e, -e)` are `Occ(pi) + {0, e, -e}`.
   - The blocks of `b = tau(q_h; 0, h, -h)` are `Occ(pi') + {h, 2h, 0}`, since
     `tau(q_h; 0, h, -h)` sends `w'+h -> w'+2h -> w' -> w'+h` for `w' ∈ Occ(pi')`.
   - Take `A_1 = Occ(pi) + 0` and `B_1 = Occ(pi') + 0`.
   - Every other pair of blocks has offset `u = a' - b' ≠ 0` with `a' ∈ {0, ±e}` and
     `b' ∈ {0, h, 2h}`. Since `h ⊥ e`, `u = 0` only for `a' = b' = 0`, and `|u|_1 <= 3`. Lemma 0
     makes all those pairs disjoint, and within each triple the offsets have length `<= 2`.
   - Lemma A gives `a` on `C = Occ(Q_j)` and its images, which is `tau(Q_j; 0, e, -e)`.
4. **Case (ii), `h = ±e`.**
   - The blocks of `a = tau(pi; 0, e, -e)` are `Occ(pi) + {0, e, -e}`, cycled `0 -> e -> -e -> 0`.
     Take `A_1 = Occ(pi) + h`, then the next two blocks in that cycle.
   - The blocks of `b = tau(q_h; 0, e^⊥, -e^⊥)` are `Occ(pi') + h + {0, e^⊥, -e^⊥}`, since
     `Occ(q_h) = Occ(pi') + h`. Take `B_1 = Occ(pi') + h`.
   - Every other offset `a' - b'`, with `a' ∈ {0, ±e}` and `b' ∈ h + {0, ±e^⊥}`, is nonzero:
     it vanishes only for `a' = b' = h`, which is the pair `(A_1, B_1)`. It also has length at
     most 3. Lemma 0 applies.
   - Lemma A gives `a` on `C = Occ(Q_j) + h` and its two images, which are the three blocks
     `Occ(Q_j) + {0, e, -e}` in the cyclic order `0 -> e -> -e`. That is `tau(Q_j; 0, e, -e)`. ∎

**Corollary C.** In `G`, `W(q, e) = 1` for every illegal `q`.
- *Proof.* Apply Lemma B to `c = x`, for each `x ∈ X` (legal at every radius). `Occ_x(q) = ∅`, so
  `W(q, e)` fixes every orbit, and `G` acts faithfully on `X`. ∎

**Theorem.** Suppose `G = <S | ℛ>` with `ℛ` finite and relators of length `<= L`. Put
`N = max(2L + R + 1, R_1 + 3)` and `Y = {z ∈ A^(Z^d) : z is N-legal}`. Then `Y = X`.

*Proof.*
1. **The relators hold on legal colourings.** Let `z ∈ Y` and `c = z`.
   - Each rule permutation moves points by vectors of length `<= 2`, and whether it moves `u` is
     read from `c` on `u + B(R+1)`. So evaluating a relator `r` at `v` reads `c` only on
     `v + B(2L + R + 1)`.
   - That window occurs in some `x ∈ X`. The two trajectories agree, so `r_c(v) = v + kappa_r(x)`,
     where `sigma^(kappa_r(x)) x = r(x) = x`. Freeness gives `kappa_r(x) = 0`.
2. **Every relation of `G` holds.** The map `F(S) -> Sym(Z^d)` given by the rule action kills `ℛ`,
   so it factors through `G`.
3. **An illegal pattern contradicts this.** If `z ∉ X`, some pattern of `z` on a translate of a
   ball is not in `L(X)`.
   - Shifting, and enlarging the ball, gives an illegal `q` on `B(M)` occurring at `0`, with
     `M > N >= R`.
   - By Lemma B, `W(q, e)` acts as `tau_c(q; 0, e, -e)`, which moves `0`.
   - By Corollary C, `W(q, e) = 1` in `G`. This contradicts step 2.
4. **Conclusion.** So `Y = X`. `Y` is the SFT whose forbidden patterns are the illegal patterns on
   `B(N)`. ∎
