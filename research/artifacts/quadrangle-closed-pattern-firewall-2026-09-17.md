# Quadrangle-closed patterns do not force domination: the rotation-pointer gadget

Agent swarm-0917-w5-pull2-gottschalk-1, 2026-09-17.
Target: `quadrangle-closed-patterns-do-not-force-domination`.
Answers the open question recorded in `quadrangle-closure-kills-shared-pointer-parity-gadgets`:
"It is open whether (L), (R) and (Q) force domination."

**Answer: no.** For every `k = 2^t >= 4` there is a finite abstract pattern satisfying (L), (R) and (Q),
with a code of `H(psi) = t + 1` bits and

    Phi = (t + 1 + k (1 - 1/k)^R) / k  <=  (log2 k + 1 + 1/k) / k  ->  0,      R = ceil(2 k ln k).

So `Phi < log q = 1` bit already at `k = 4` (`Phi = 0.7817`). No group realizes the pattern. The axiom that
fails is a **holonomy** condition (H): a composite of row-pair classes that fixes one position fixes every
position of its domain. A proof of `rokhlin-window-transport-is-dominated` must use more than (L), (R), (Q).
One route is through (H).

Machine check: `experiments/quadrangle-firewall-2026-09-17/verify_rotation_gadget.py`, output
`verify_rotation_gadget.json`.

## 1. Setting

A **pattern** is a full rectangle `w : F x E -> S` (sites), written `(c, e) -> c e`, with a special site `o`.
Inputs `x(s)` are iid uniform on `{0,1}^k` over sites. A code `psi : ({0,1}^k)^E -> Y` gives outputs
`y_c = psi((x(c e))_(e in E))` and

    Phi = (1/k) [ H(y_c) + H( x(o) | (y_c)_(c in F) ) ]      (bits; every y_c has the same law).

This is `Phi` of `bernoulli-rokhlin-deficit-has-a-finitary-witness`, read on the abstract pattern. Axioms:

- **(L)** rows injective: `c e = c e'` implies `e = e'`;
- **(R)** columns injective: `c e = c' e` implies `c = c'`;
- **(Q)** if `c e = c' e'`, `c r = c' r'` and `d e = d' e'`, then `d r = d' r'`.

For rows `c, c'` put `R(c, c') = {(e, e') : c e = c' e'}`.

**Lemma 1.1.** Under (L) and (R), (Q) holds iff any two classes `R(c, c')`, `R(d, d')` with `c != c'` and
`d != d'` are disjoint or equal.

*Proof.* (Q) says: if `(e, e')` lies in `R(c, c') ∩ R(d, d')`, then `R(c, c') ⊆ R(d, d')`. Applied twice, it
gives equality, and conversely. If `c = c'`, then `R(c, c)` is the diagonal, by (L). A diagonal pair
`(e, e)` lies in `R(d, d')` only when `d = d'`, by (R). So a class with `c = c'` meets only diagonal classes,
and those are equal. □

**Holonomy (H).** Each class is a partial injection of `E`, by (L). Say (H) holds if every composite
`R(c_1, c_1') ∘ ... ∘ R(c_r, c_r')` that fixes one position is the identity on its domain.

*Every group pattern satisfies (H).* In a group `R(c, c')` is the restriction of `e -> c'^-1 c e`. A
composite is the restriction of `e -> g e` for one element `g`. A fixed point forces `g = 1`.

## 2. The construction

**Parameters.**
- `q = 2`, `k = 2^t >= 4`, `R = ceil(2 k ln k)` gadgets, indexed `rho = 0, ..., R-1`.
- `n` prime with `n >= R^2 + R + 1` (value positions), `m = (n - 1)/2`.
- `L` prime with `L > 16 R` (pointer positions). For the non-realizability remark also `L ∤ 3m + 2`.
- Shifts `a_rho in Z/L` with the sets `S_rho = {a_rho, -a_rho, 2a_rho, -2a_rho}` of size 4 and pairwise
  disjoint. Greedy choice works. `S_rho` meets `S_(rho')` only if `a_(rho') in S_rho · {±1, ±1/2}`, which
  excludes at most 16 values each time, and `L - 1 > 16(R - 1)`.
- Steps `c_rho = rho + 1` and isolated points `z_rho = rho (R + 1)` in `Z/n`.

**Positions.** `E = {u_y : y in Z/L} ∪ {v_x : x in Z/n}`. For gadget `rho`, write `c = c_rho`, `z = z_rho` and

    s_i = v_(z + (2i-1)c),   t_i = v_(z + 2ic)     (i = 1..m),     z-position  v_z .

Since `n` is prime and `1 <= c <= R < n`, the walk `z + c, z + 2c, ..., z + nc = z` visits every value position once. So
`s_1, t_1, s_2, t_2, ..., s_m, t_m, v_z` is the Hamiltonian cycle `x -> x + c` of `Z/n`, in this order.

**Sites.** Per gadget: pointer sites `p(rho, y)` for `y in Z/L`, value sites `A_i(rho), B_i(rho)`
(`i = 1..m`), `C_i(rho)` (`i = 1..m-1`), `D(rho)`, `Ep(rho)`. The single shared site is `o`.

**Rows.** Gadget `rho` has three codewords `W_0, W_1, W_2` (written without `rho`), with `a = a_rho`:

    W_i u_y = p(rho, y + i a)                         (i = 0, 1, 2)
    W_0 :  s_i -> A_i,   t_i -> C_i (i < m),   t_m -> D,        v_z -> Ep
    W_1 :  s_i -> B_i,   t_i -> A_i,                            v_z -> o
    W_2 :  t_i -> B_i,   s_(i+1) -> C_i (i < m),   v_z -> D,    s_1 -> Ep

Each row reads every position exactly once (the three lists are bijections of the value positions), so
`w` is a full rectangle.

**Code.** With `lo(x) = sum_(b < t) 2^b x[b]`:

    psi(x|_E) = ( j, XOR_(x in Z/n) x(v_x)[j] ),      j = sum_(y in Z/L) lo(x(u_y)) mod k .

## 3. (L) and (R)

**(L).** Pointer sites and value sites are of different kinds. A row reads the `L` distinct pointer sites
`p(rho, y + i a)`. By the three lists it reads `2m + 1 = n` distinct value sites.

**(R).** Rows of different gadgets share only `o`. The rows reading `o` are the `W_1^rho`, at the
positions `v_(z_rho)`. These are distinct because `z_rho - z_(rho') = (rho - rho')(R + 1)` is nonzero mod
`n`, as `0 < |rho - rho'|(R + 1) <= R^2 - 1 < n`. Within one gadget:
- column `u_y` gives `p(y)`, `p(y + a)`, `p(y + 2a)`, which are distinct since `a, 2a != 0`;
- column `s_i` gives `A_i, B_i, C_(i-1)` (or `Ep` when `i = 1`);
- column `t_i` gives `C_i` (or `D` when `i = m`), `A_i, B_i`;
- column `v_z` gives `Ep, o, D`.

## 4. The classes and (Q)

Write `T_b = {(u_(y+b), u_y) : y in Z/L}`. Also write `N_c(X) = {(v_x, v_(x+c)) : v_x in X}` for a set `X` of
value positions. Put `Sg = {s_1, ..., s_m}` and `Tg = {t_1, ..., t_m, v_z}`, which partition the value
positions of gadget `rho`.

**Within gadget `rho`.** Compare which sites two rows share.
- `W_0, W_1` share every pointer site and the `A_i`. `W_0 u_x = W_1 u_y` iff `x = y + a`, and
  `W_0 s_i = A_i = W_1 t_i` with `t_i = s_i + c`. So `R(W_0, W_1) = T_a ∪ N_c(Sg)`.
- `W_1, W_2` share every pointer site and the `B_i`. `W_1 u_x = p(x + a)` and `W_2 u_y = p(y + 2a)`, so
  again `x = y + a`, and `W_1 s_i = B_i = W_2 t_i`. So `R(W_1, W_2) = T_a ∪ N_c(Sg) = R(W_0, W_1)`.
- `W_0, W_2` share every pointer site and `C_i, D, Ep`. `x = y + 2a`. The value pairs are `(t_i, s_(i+1))`,
  `(t_m, v_z)` and `(v_z, s_1)`, each of the form `(v_x, v_(x+c))` with `v_x in Tg`, because
  `z + 2mc + c = z + nc = z`. So `R(W_0, W_2) = T_(2a) ∪ N_c(Tg)`.
- The reversed pairs give the inverse relations: `T_(-a) ∪ N_c(Sg)^-1` and `T_(-2a) ∪ N_c(Tg)^-1`.

**Across gadgets.** `R(W_1^rho, W_1^(rho')) = {(v_(z_rho), v_(z_(rho')))}`, and every other cross class is
empty.

**Disjoint or equal.** The nonempty classes with distinct rows are:

    tau_rho = T_(a_rho) ∪ N_(c_rho)(Sg_rho),     sigma_rho = T_(2a_rho) ∪ N_(c_rho)(Tg_rho),
    their inverses,   and   kappa_(rho,rho') = {(v_(z_rho), v_(z_(rho')))}  (rho != rho').

Two different ones are disjoint.
- *Pointer parts.* These are translations `T_b` with `b in S_rho`. The `4R` values of `b` are distinct.
  So two classes with pointer parts are either built on the same `b`, hence the same gadget and the same
  one of the four types, or have disjoint pointer parts. The `kappa` have no pointer part.
- *Value parts.* A value pair `(v_x, v_(x'))` has difference `x' - x`. `tau_rho` and `sigma_rho` use
  `+c_rho`, the inverses use `-c_rho`, and `kappa_(rho,rho')` uses `(rho' - rho)(R + 1)`. Since `n > 2R`, the
  `2R` residues `±c_rho` are distinct. Also `0 < |rho' - rho|(R + 1) <= R^2 - 1` and `n - (R^2 - 1) > R`, so no
  `kappa` difference is some `±c_rho`.
- The same difference means the same gadget and the same sign. Then `tau_rho` and `sigma_rho` differ in
  their first coordinates (`Sg` versus `Tg`), and so do their inverses in their second coordinates.
- Two `kappa` classes are equal or disjoint because the `z_rho` are distinct.

By Lemma 1.1, (Q) holds. □

## 5. Entropy

**`H(y_c) = t + 1`.** The `L` values `lo(x(u_y))` are iid uniform on `Z/k`, so `j` is uniform. Given the
pointer inputs, the output bit is the XOR of `n` fresh uniform bits, so it is uniform.

**Residual.** Let `J = (j_rho)_rho`, where `j_rho` is the common `j` of the three rows of gadget `rho`. By §2
their pointer windows are the same set `{p(rho, y)}`. The `j_rho` are iid uniform, and independent of all
value inputs and of `x(o)`. For gadget `rho` put

    alpha = XOR_i A_i[j_rho],   beta = XOR_i B_i[j_rho],   gamma = XOR_(i<m) C_i[j_rho] + D[j_rho] + Ep[j_rho] .

Then the three outputs are

    y_(W_0) = (j_rho, alpha + gamma),   y_(W_1) = (j_rho, x(o)[j_rho] + alpha + beta),   y_(W_2) = (j_rho, beta + gamma).

The bits `alpha, beta, gamma` are uniform and independent of each other, of the other gadgets, of `J` and of
`x(o)`. So `y_F` is in bijection with `(J, (alpha_rho + gamma_rho, beta_rho + gamma_rho)_rho, (x(o)[j_rho])_rho)`.
The mask pairs are uniform and independent of `(J, x(o))`. Hence

    H(x(o) | y_F) = H(x(o) | J, (x(o)[j_rho])_rho) = E #{ j in Z/k : j != j_rho for all rho } = k (1 - 1/k)^R .

**Phi.** `Phi = (t + 1 + k(1 - 1/k)^R)/k`, and `k(1 - 1/k)^R <= k e^(-R/k) <= k e^(-2 ln k) = 1/k`. Values:

| `k` | `R` | `Phi` |
|---|---|---|
| 4 | 12 | 0.7817 |
| 8 | 34 | 0.5107 |
| 16 | 89 | 0.3157 |
| 32 | 222 | 0.1884 |

These are the same numbers as the loop firewall, whose gadget has the same coupon structure.

## 6. Where the pattern leaves the groups

**Holonomy fails.** Take gadget `rho` and the word that follows the value cycle once, starting at `s_1`:

    s_1 -tau-> t_1 -sigma-> s_2 -tau-> ... -tau-> t_m -sigma-> v_z -sigma-> s_1 .

It uses `m` copies of `tau_rho` and `m + 1` copies of `sigma_rho`, so it fixes `s_1`. Every pointer position
lies in the domain of every `tau_rho` and `sigma_rho`, and there the word is the translation by
`-(m a + 2(m + 1) a) = -(3m + 2) a`. That is nonzero mod the prime `L` when `L ∤ 3m + 2`. So the word fixes
`s_1` and moves all `L` pointer positions, and (H) fails.

**Direct group computation.** Suppose a group `G` and a map of rows and positions into `G` send equal sites
to equal products, with `W_0 u_0 != W_1 u_0`. Put `g = W_1^-1 W_0`.
- `(e, e') in R(W_0, W_1)` gives `e' = g e`.
- The pair `(u_a, u_0)` lies in `R(W_1, W_2)` too, so `W_2^-1 W_1 = u_0 u_a^-1 = g` and `W_2^-1 W_0 = g^2`.
- **Pointers.** `u_y = g u_(y+a)`, so `u_y = g^L u_(y + La) = g^L u_y` and `g^L = 1`.
- **Values.** `t_i = g s_i`, `s_(i+1) = g^2 t_i`, `v_z = g^2 t_m` and `s_1 = g^2 v_z`. Hence
  `s_1 = g^(3m+2) s_1`, and `g^(3m+2) = 1`.
- With `gcd(L, 3m + 2) = 1` this gives `g = 1`, so `W_0 u_0 = W_1 u_0`, a contradiction.

So no group realizes the pattern, even through a map that only preserves the coincidences and keeps
`p(rho, 0) != p(rho, a)`. This is consistent with `coset-local-decoders-force-gated-domination`.

**Relation to the mod-3 theorem.** `quadrangle-closure-kills-shared-pointer-parity-gadgets` needs a *coherent*
cyclic shift: `R(W_1, W_2) ∩ R(W_2, W_3) ∩ R(W_3, W_1)` must be nonempty.
- Here `R(W_0, W_1) = R(W_1, W_2) = tau`, but `R(W_2, W_0) = sigma^-1` is built on `T_(-2a) != T_a`, because
  `3a != 0`. Every ordering of the three rows meets a `tau`/`sigma` type pair, which is disjoint. Across gadgets
  the classes are singletons that avoid the within-gadget classes.
- So the pattern has no coherent 3-shift, and the theorem does not apply.
- With `L ≡ 1 (mod 3)`, the full windows have `|W_0 E Δ W_1 E Δ W_2 E| = L + 1 ≡ 2 (mod 3)`, outside the
  invariant.
- The gadget beats the invariant by leaving the pointer rotation **open**. `W_0 -> W_1 -> W_2` rotates by
  `a`, but `W_2 -> W_0` rotates by `-2a`, not by `a`. In a group the rotation closes up through holonomy.

## 7. Consequences

1. **The open question is answered negatively.** (L), (R) and (Q) do not force `Phi >= log q`. The
   abstract `Phi` tends to 0, and it lies within a `(log k)^2` factor of the read-degree bound, as for the
   loop firewall.
2. **Proof side (class kill).** Some proofs of `rokhlin-window-transport-is-dominated`, or of
   `bernoulli-rokhlin-entropy-maximal-for-every-group`, use the pattern only through its finite incidence
   axioms. Examples are counting, double counting, Shearer-type or entropy-inequality arguments valid on
   every partial Latin rectangle with quadrangle closure. All of these fail. A proof must use a
   compositional property of the class maps through words of unbounded length. Here the failing word has
   length `2m + 1 = n` and runs around a value cycle. The finite axiom (Q) only compares two classes at a time.
   (H) is the natural candidate. It is what the group-level arguments use: coset projection in
   `coset-local-decoders-force-gated-domination`, and the group ring in Theorem C of
   `cancellative-incidence-patterns-do-not-force-domination`.
3. **Counterexample side.** A search for Bernoulli Rokhlin deficits that filters candidate patterns by
   (L), (R) and (Q) will return false positives of this kind. The extra filter is (H), which can be checked
   by breadth-first search over the partial action of the classes. Here the certificate is a class word
   that has a fixed point but acts with nonzero displacement elsewhere.
4. **Refined question (OPEN).** Do (L), (R), (Q) and (H) force domination? (H) is necessary for group
   patterns. Whether (L)+(R)+(Q)+(H) imply exact realizability in a group (the canonical host of
   `bernoulli-rokhlin-deficit-has-a-finitary-witness`) is not decided here. If they do, the refined
   question is equivalent to the transport claim. If they do not, a pattern with (H) and a deficit would be
   the next firewall.
5. **Scale.** In this construction the escape uses long words: the value cycle has length `n >= R^2 + R + 1`. Whether
   (Q) plus holonomy for words of length at most some `f(k)` already forces domination is open.

## 8. Machine checks

`experiments/quadrangle-firewall-2026-09-17/verify_rotation_gadget.py` writes `verify_rotation_gadget.json`
(5 s).

- **Small instance** (`k = 2`, `R = 3`, `L = n = 13`, shifts `1, 3, 4`):
  - full rectangle, (L), (R), value XOR `= {o}`;
  - (Q) by classes;
  - **literal (Q) by brute force** over all rows including `c = c'`: 65826 instances, 0 violations;
  - no coherent 3-shift, `|Δ| = 14 ≡ 2 (mod 3)`;
  - (H) fails: the word of length 13 fixes `s_1` and moves all 13 pointers.
  - **Negative control:** the same pattern with one shift for all gadgets keeps (L) and (R) but has 4836
    literal (Q) violations, the flaw of the first design.
- **`k = 4`** (`R = 12`, `L = 61`, `n = 157`):
  - (L), (R), value XOR, pointer invariance;
  - (Q) by classes (180 distinct nonempty classes = `48` within gadgets + `132` singletons);
  - 0 coherent 3-shift triples, `|Δ| = 62 ≡ 2 (mod 3)`;
  - (H) fails, with displacement 8 on all 61 pointers;
  - `Phi = 0.78168`;
  - Monte Carlo, 3000 trials: 0 decoding errors, mean unrevealed `0.1257` against the exact `0.1267`.
- **`k = 8`** (`R = 34`, `L = 157`, `n = 1193`):
  - all checks pass, (Q) with 1258 distinct classes;
  - `Phi = 0.51067`;
  - Monte Carlo, 300 trials: 0 errors, mean unrevealed `0.100` against `0.0854`.
