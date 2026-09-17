# Cancellative pattern firewall: independent re-derivation, and the quadrangle-closure mod-3 invariant

Lane a-gs-pull-12, swarm-0917, 2026-09-17.

- **Under check:** `research/artifacts/right-cancellative-pattern-firewall-2026-09-12.md`, by w7-inf-cancellative, for
  claim `cancellative-incidence-patterns-do-not-force-domination`.
- **Machine check:** `experiments/cancellative-firewall-2026-09-17/verify_gadget.py`, output in `verify_gadget.json`
  in the same folder. It is deterministic and runs in about 2 minutes.
- **Conventions:** logs base 2, `q = 2`, `k = 2^t`. A **pattern** is a full rectangle `w : F x E -> sites` with
  - (L) each row `w_f = w(f, .)` injective;
  - (R) each column `w(., e)` injective.

  For a codeword `f` and positions `S ⊆ E`, write `fS = w_f(S)`.

## 0. Verdict

- **Theorem A:** PASS. The residual equals `k (1 - 1/k)^R` exactly, not only as an upper bound (Section 1).
- **Theorem B:** PASS. The proof is correct, and the loop realization was built explicitly for `k = 4`: a loop of
  order 530 with identity `o` that carries the gadget pattern (Section 2).
- **Theorem C:** PASS (Section 3).
- **Node consequences:** PASS.
  - The count on a closed finite index set gives only average domination (artifact Section 5).
  - Numbers in the tree star 6.1: PASS.
  - Free-monoid domination 6.2 uses `sofic-radical-localizes-bernoulli-deficit-witnesses` (Section 5).
- **New, Theorem C':** associativity enters only through the finite quadrangle closure of the pattern itself, and
  the invariant is `|W_1 E Δ W_2 E Δ W_3 E| mod 3` (Section 4).
  - This replaces the group-ring step of Theorem C by a count.
  - It shows that every shared-pointer triple parity gadget dies at a checkable finite condition, not at global
    embeddability.

The one remaining gap between the loop firewall and INF is recorded in Section 6.

## 1. Theorem A, re-derived

**Pattern.** Take `n = 2m + 1 >= R` and `E = {P1, P2, P3} ⊔ Z/n`. Each gadget `g < R` has fresh sites
`a, b, c, alpha_1..m, beta_1..m, gamma_1..m+1`, and the shared site `x0 = o`. The position table is exactly the one in
artifact Section 2.

**Machine check.** For `k = 4, 8, 16, 32`, with `R = ceil(2 k ln k)` and `n` the least odd integer `>= R`:

| k | R | n | \|F\| | \|E\| | sites | (L) | (R) | `V_1 Δ V_2 Δ V_3 = {o}` | shared pointer set | readers of `o` |
|---|---|---|---|---|---|---|---|---|---|---|
| 4 | 12 | 13 | 36 | 16 | 265 | yes | yes | yes | yes | 12 |
| 8 | 34 | 35 | 102 | 38 | 1871 | yes | yes | yes | yes | 34 |
| 16 | 89 | 89 | 267 | 92 | 12105 | yes | yes | yes | yes | 89 |
| 32 | 222 | 223 | 666 | 226 | 74815 | yes | yes | yes | yes | 222 |

Here `V_i = W_i^g(Z/n)` is the value window of codeword `W_i^g`. The hand check of (R) agrees with the program:
- `gamma_l` sits at `g+m+l-1` and at `g+l-2`, which differ by `m+1`, and `m + 1 != 0 mod n`;
- `W_3` covers `g-1 = g+2m` through `gamma_1`;
- `x0` is read only by `W_1^g`, at position `g`, and the `R <= n` values of `g` are distinct.

**Exact entropy of the code.**
- The pointer `j` is a sum mod `k` of uniform `t`-bit prefixes, so `j` is uniform.
- Given `j`, the output bit is the parity of `n >= 1` independent uniform bits, so it is uniform and independent of
  `j`.
- Hence `H(psi) = t + 1`. The program confirms this by convolution for `n = 13, 35, 89, 223`.

**The residual is exact.** Let `J = (j_g)_g`. `J` is a function of the pointer sites only, and these are independent
of `x0`. In gadget `g` put `A_g = XOR_i alpha_i[j_g]`, `B_g = XOR_i beta_i[j_g]` and `C_g = XOR_l gamma_l[j_g]`. The
outputs are:

    b_1 = x0[j_g] + A_g + B_g,   b_2 = A_g + C_g,   b_3 = B_g + C_g.

- Given `J` and `x0`, the triple `(A_g, B_g, C_g)` is uniform on `F_2^3`, because the mask sites are fresh.
- So `(b_2, b_3)` is uniform on `F_2^2`, and `b_1 = x0[j_g] + b_2 + b_3`.
- Distinct gadgets use disjoint mask and pointer sites.

Therefore `y_F` and `(J, (b_2^g, b_3^g)_g, (x0[j_g])_g)` determine each other. The first two components are
independent of `x0` and of each other. Since `x0` is uniform on `F_2^k`:

    H(x0 | y_F) = E_J [ k - |{j_g : g < R}| ] = k (1 - 1/k)^R     (exact).

- **Exact enumeration:** it reproduces this value on every instance small enough to enumerate:
  - `k=2, R=1`: `1.0` (13 bits);
  - `k=2, R=2`: `0.5` (24 bits);
  - `k=4, R=1`: `3.0` (26 bits).
- **Monte Carlo decoding** of the full instances:
  - `k = 4`, 4000 trials: 0 decoding errors, mean unrevealed `0.12725` against `0.12671`;
  - `k = 8`, 1000 trials: 0 errors, `0.087` against `0.0854`.

So `Phi = (t + 1 + k (1 - 1/k)^R)/k` exactly:

| k | exact `Phi` | general bound `(t + 1 + 1/k)/k` |
|---|---|---|
| 4 | 0.78168 | 0.8125 |
| 8 | 0.51067 | 0.5156 |
| 16 | 0.31570 | 0.3164 |
| 32 | 0.18837 | 0.1885 |

The node's "k = 4 gives Phi <= 0.782" is the exact value, and the bound `(log2 k + 1 + 1/k)/k -> 0` holds because
`k e^(-R/k) <= 1/k`.

## 2. Theorem B, re-derived and built

- **Evans.** T. Evans, *Embedding incomplete latin squares*, Amer. Math. Monthly 67 (1960) 958-961: an incomplete
  latin square of order `n` can be embedded in a complete latin square of order `2n`.
- **Padding.** Pad the pattern to a partial square of order `N = max(|F|, |E|, #sites)`, with rows `F`, columns `E`
  and symbols the sites.

**Built instance.** For the `k = 4` gadget, `N = 265`. The program completes the square in three steps:
1. greedily fill the `N x N` block with symbols from `[2N]`, which is possible since at most `2N - 2` symbols are
   forbidden in any cell;
2. edge-colour rows against missing symbols with `N` colours (König), giving the columns `N..2N-1`;
3. edge-colour columns against missing symbols, an `N`-regular bipartite graph, with `N` colours, giving the rows
   `N..2N-1`.

The result is a latin square `A` of order 530 containing the pattern.

**Loop isotope.** With `u = 0` and `v = u \ o`, put `x ∘ y = (x / v) · (u \ y)`. The program checks that:
- `∘` is latin with identity `o`;
- the relabelling `f -> f · v`, `e -> u · e` preserves the whole incidence, with distinct labels;
- 1982 of 2000 random triples are non-associative.

## 3. Theorem C, re-derived

Suppose `c_1 P = c_2 P = c_3 P` in a group and `c_1 E_val Δ c_2 E_val Δ c_3 E_val = {x0}`.
1. `delta = c_1^-1 c_2` stabilizes `P`.
2. The stabilizer of a 3-set acts freely on it, so it has order 1 or 3. So `c_2 = c_1 delta` and
   `c_3 = c_1 delta^2` with `delta^3 = 1`.
3. In `F_2[G]` this gives `c_1 (1 + delta + delta^2) Ê = x0`.
4. Multiply on the left by `c_1 (1 + delta) c_1^-1`. The left side becomes `c_1 (1 + delta^3) Ê = 0`. The right side
   becomes `x0 + (c_1 delta c_1^-1) x0 != 0`, since `c_1 delta c_1^-1 != 1`.

Correct as written.

## 4. Theorem C': the quadrangle closure alone kills the gadget, with a mod-3 invariant

**Quadrangle closure (Q)** of a pattern: if `c e = c' e'`, `c r = c' r'` and `d e = d' e'`, then `d r = d' r'`, for
all codewords and positions of the pattern. Every group pattern satisfies (Q):

    c'^-1 c = e' e^-1 = r' r^-1 = d'^-1 d.

Equivalently, the shift relations `S_(c,c') = {(e, e') : c e = c' e'}` are pairwise equal or disjoint.

**Theorem C'.** Let a pattern satisfy (L), (R) and (Q), and let `W_1, W_2, W_3` be distinct codewords with a
**coherent cyclic shift**: positions `u, u'` with

    W_1 u = W_2 u',   W_2 u = W_3 u',   W_3 u = W_1 u'.

Then `|W_1 E Δ W_2 E Δ W_3 E| ≡ 0 (mod 3)`.

**Proof.** Indices are mod 3.
1. **The three shift forms agree.** For positions `e, r`, the three statements `W_2 e = W_1 r`, `W_3 e = W_2 r` and
   `W_1 e = W_3 r` are equivalent. For the first implication apply (Q) with:
   - `(c, c') = (W_1, W_2)` and the instance `(u, u')`;
   - `(r, r')` taken as `(r, e)`;
   - `(d, d') = (W_2, W_3)`, using `W_2 u = W_3 u'`.

   The other two implications are the cyclic shifts.
2. **A partial permutation.** Write `pi(e) = r` when these hold. By (L), `pi` is a partial injective map
   `E -> E`. By (R) it has no fixed points: `W_2 e = W_1 e` is excluded.
3. **Pairwise intersections.** The pairs (site `s`, pair `{i, i+1}` with `s ∈ W_i E ∩ W_(i+1) E`) are in bijection
   with (arrow `e -> pi(e)`, type `i`). The site is `W_(i+1) e = W_i pi(e)`, and (L) recovers `e` and `pi(e)` from the
   site. So `sum_(i<j) |W_i E ∩ W_j E| = 3A`, where `A` is the number of arrows.
4. **Triple sites.** Suppose `s = W_1 e_1 = W_2 e_2 = W_3 e_3`. The three forms give `pi(e_2) = e_1`, `pi(e_3) = e_2`
   and `pi(e_1) = e_3`, so `e_1, e_2, e_3` lie on a 3-cycle of `pi`. They are distinct because `pi` has no fixed
   points and is a function.
   - Conversely, take `x` on a 3-cycle with `x = pi(y)`. Then `W_1 x = W_2 y`, and the third form with
     `(e, r) = (x, pi(x))` gives `W_1 x = W_3 pi(x)`. So `W_1 x` is a triple site.
   - Hence `s -> W_1^-1(s)` is a bijection from triple sites onto the positions lying on 3-cycles, and `T = 3C`, where
     `T` is the number of triple sites and `C` the number of 3-cycles.
5. **Inclusion-exclusion.** For three sets, `|X_1 Δ X_2 Δ X_3| = sum |X_i| - 2 sum |X_i ∩ X_j| + 4 |X_1 ∩ X_2 ∩ X_3|`.
   This gives

       |Δ| = 3|E| - 6A + 4T ≡ T = 3C ≡ 0 (mod 3).   ∎

**Corollary C'1 (shared pointer sets).** Let a pattern satisfy (L), (R) and (Q). Suppose `W_1 P = W_2 P = W_3 P` as
site sets, with `|P| = 3`, and put `E_val = E ∖ P`. Then `|W_1 E_val Δ W_2 E_val Δ W_3 E_val| ≡ 0 (mod 3)`. In
particular it is never `{o}`.

*Proof.*
1. **Coherent shift.** Define `sigma_ij : P -> P` by `W_i sigma_ij(p) = W_j p`; it is well defined by (L).
   - By (R) each `sigma_ij` is fixed-point-free, so it is a 3-cycle `tau` or `tau^-1`.
   - `sigma_13 = sigma_12 sigma_23` must also be fixed-point-free, which forces `sigma_12 = sigma_23`, and then
     `sigma_31 = sigma_12` as well.
   - So `(u, u') = (tau(p), p)` is a coherent cyclic shift. This step uses only (L) and (R).
2. **Removing the pointers.** The three pointer sites lie in all three windows, and by (L) they lie in no value
   window. So `|Δ_val| = |Δ| - 3 ≡ 0`. ∎

Theorem C follows, since group patterns satisfy (Q). The loop pattern of Theorem A violates (Q). For gadget `0` at
`k = 4`, six pairs of shift relations meet without being equal, for example `S_(W_1,W_2)` and `S_(W_2,W_3)`, which share
`(P2, P1)` but differ at `(v4, v3)`. Its full-window symmetric difference is `{a, b, c, x0}`, of size `4 ≢ 0`.

**Exhaustive check.** All 3-row patterns with (L) and (R) and `|E| <= 4` were enumerated, up to relabelling sites:
1, 18, 588 and 30240 patterns.

| \|E\| | with (Q) and a coherent shift | `\|Δ\|` values there | `\|Δ\|` values with a coherent shift but without (Q) |
|---|---|---|---|
| 2 | 2 | {0} | none |
| 3 | 8 | {3} | {3} |
| 4 | 32 | {0, 6} | {2, 4, 6} |

In 3000 random group patterns in `Z/3 x Z/n`, (Q) holds and every residue is `0`. So the residues `2` and `4` occur
only without (Q): the invariant is sharp and (Q) is the step where it is forced.

**Obstruction statement.**
- **Proof side.** A domination proof must use (Q). Theorems A and B give (L), (R), identity, both divisions,
  finiteness and a closed finite index set with `Phi -> 0`, and the gadget fails (Q).
- **Counterexample side.** Every attempt to build a group Rokhlin deficit from shared-pointer triple parity gadgets
  dies at (Q) of its own finite pattern, with invariant `|Δ_val| mod 3`. This holds before any question of
  embeddability or soficity.

## 5. Consequences listed in the node

- **Section 5 count.** Put codewords at every `c` of the finite loop `Q`. Then
  `N k = H(x_Q) <= H(y_Q) + sum_s H(x(s) | y_Q) <= N H(psi) + sum_s H(x(s) | y_Q)`, which is average domination. It
  says nothing at `o`. Correct.
- **6.1, tree star.**
  - Site `o` has `2^i` depth-`i` descendants, which read it at position `i` through iid pointers.
  - The reveal count is `2^(d+1) - 2`. For `k = 256`: `2 k ln k = 2839.1`, so `d = 11` (`2^12 - 2 = 4094`), and
    `Phi <= (8 + 11 + 1/256)/256 = 0.0742 <= 0.075`.
  - (R) fails at every `i >= 1`. Correct.
- **6.2, downward windows.** Take addresses relative to a common ancestor, then translate by `address(o)^-1`. This
  realizes the pattern in the free group with `o -> 1` and no extra coincidences, because the free monoid embeds in
  the free group. By `sofic-radical-localizes-bernoulli-deficit-witnesses` (consequence "Sofic groups. With
  `Rad(K) = 1` no witness exists, so every sofic group is Rokhlin-maximal at every `q`"), `Phi >= log q`. Correct.

## 6. What stays open

- **The (Q)-firewall question.** Do (L), (R) and (Q) together force `Phi >= log q` for finite patterns?
  - Theorem C' removes every triple shared-pointer gadget.
  - The surviving local mechanism is a coherent shift of order `r >= 5` with `sigma = sum_(K') kappa` a unit of
    `F_2[Z/r]`, as for `Z/5` with `{1, s, s^2}`.
  - In groups Section 8 of the artifact bounds `|E_val| <= |K|` there. It is not known whether (Q) alone gives that
    bound.
  - A (Q)-closed, non-group-realizable pattern with `Phi < 1` would push the firewall to global embeddability. A proof
    that (Q) forces domination would be INF for all groups, since group patterns satisfy (Q).
- **Cousin-type tree windows** (artifact 6.2) are still undecided.
