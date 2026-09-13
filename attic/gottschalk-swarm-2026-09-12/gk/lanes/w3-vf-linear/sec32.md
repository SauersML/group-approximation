
## 32. Rank functions on V are trivial plus regular on cylinder groups (w7-v-cycle-c2; ce8be16cd1, artifact `thompson-v-rank-functions-regular-on-cylinder-groups-2026-09-12.md`)

Re-derived at tip ee57920cb. Since ce8be16cd1, neither the artifact nor the three nodes it touches have changed.

**Inputs.**
- [TS] Theorem 1.3 in its abstract form (§30.1).
- [FR] Theorem 1.2 (§30.2).
- The scalar extension `rk'` (§30.1).
- All are ESTABLISHED, and every step below uses only the Sylvester axioms.

### 32.1 Theorem 1.1: PASS

* **(S3′).** `diag(a, b) = (f; 1−f)(a+b)(f, 1−f)`. The off-diagonal entries vanish because `a(1−f) = 0` and `f b = 0`.
* **(S7).** `(a + 1−f)(b + 1−f) = ab + 1−f`, since `a(1−f) = (1−f)b = 0`.
  * Start from `[[A, 0], [1, B]]`.
  * Row operation `R1 − A·R2`, then column operation `C2 − C1·B`, gives `[[0, −AB], [1, 0]]`, of rank `rk(AB) + 1`.
* **Step 1.**
  * **Well defined.** `g^-1 g'` is in `G` and maps `[u]` onto `[u]` by `uw -> uw`. So it is the identity on `[u]`,
    fixes `[u]` setwise, and commutes with `c_u`.
  * **Conjugates.** `g` sends `u0bw -> v0bw`, so `c_v` is a clopen `p`-cycle on the cylinders `g(B_k) ⊆ [v0]`. Also
    `h c_v h^-1 = (hg) c_u (hg)^-1 = c_(h[v])`.
  * **Products.** Take `q = prod_(v in T) c_v^(a_v)`.
    * On `supp c_v`, `q = c_v^(a_v)`. Since `a_v` is a unit mod `p`, `c_v^(j a_v)(B_v)` for `j in Z/p` runs over the
      `p` cylinders moved by `c_v`.
    * So the `C_j` are disjoint and nonempty, and they cover `union_(v in T) supp c_v`.
    * `q` fixes the complement, which contains every `[v1]`, and `q^p = 1`. This matches the [TS] definition exactly.
  * **Faithful.** An element fixing every `[u] in Pi` is the identity on each of them, so `G -> Sym(Pi)` is injective.
* **Step 2.**
  * **`phi_V` unchanged.** The rows `1 − [s]` are over `F`, so `phi_V(rk') = phi_V(rk)`. [FR] Theorem 1.2 for `rk'`
    on `F'[V]` gives `a_p(rk') = phi_V`.
  * **Conjugation.** `[g] e_chi [g]^-1 = |Q|^-1 sum_q chi(q)^-1 [g q g^-1] = e_(g chi)`.
  * **`f_O`.** `f_O` is central in `F'[Q]` and `G`-invariant.
* **Step 3.** Recomputed; the author asked for (b)–(c).
  * **(a)** The augmentation ideal is the left ideal of the `1 − [s]`, by `1 − [gh] = (1−[g]) + [g](1−[h])` and
    `1 − [g^-1] = −[g^-1](1−[g])`. Then apply (S5) and delete rows: `rk A = rk((I 0)(A; B)) <= rk(A; B)`.
  * **(b)**
    * `G` normalizes `Q`, so `(1−[g])e = e(1−[g])`, and `e(1−[g]) = (1−[g]) − (1−[g])(1−e)`.
    * `1 − e = |Q|^-1 sum_q (1 − [q])`.
    * `(1−[c_v])e = 0` gives `1 − [c_v] = (1−[c_v])(1−e)`, and `1 − [g] = e(1−[g]) + (1−[g])(1−e)`.
    * Applying (S5) in both directions gives `rk col(Y) = rk col(Y ∪ Y') = rk col(Y')`.
  * **(c)** The rows of `C (1−e, e)`:
    * `(1−e, 0)`;
    * `(e(1−[g])(1−e), e(1−[g])e) = (0, e(1−[g]))`, because `e(1−[g])(1−e) = (1−[g])e(1−e) = 0`.
    * So `C(1−e, e) = diag`, and `diag·(1; 1) = C`. The ranks agree, and block additivity finishes.
  * **(d)** follows by (S3).
  * **Consequence.**
    * `A − eps(A) = −sum_x a_x (1 − [x])`, so `B` has `F`-entries `−(a_x)_(ij)` in column `(j, x)`.
    * `rk(e·eps A) = r·rk(e)` via `eps A = U diag(I_r, 0) W` over `F`.
    * So `|rk'(eA) − phi r| <= n(1−phi)p^(−|Pi|) + r(1−phi)p^(−|Pi|) <= 2n(1−phi)p^(−|Pi|)`.
* **Step 4.** Recomputed; the author asked for `f_O ~ I_|G| ⊗ e_chi`.
  * **Orthogonality.** `e_chi [x] = [x] e_(x^-1 chi)`. By freeness, `e_(x^-1 chi) e_chi = 0` for `x != 1`.
  * **`Rr Cc`.** `Rr Cc = sum_g e_(g chi) = f_O`, since `g -> g chi` is a bijection `G -> O` on a free orbit.
  * **`Cc Rr`.** `Cc Rr = (e_chi [g^-1 h] e_chi)_(g,h) = I ⊗ e_chi`.
  * **Entries of `Â`.** The entry is `e_chi [g]^-1 (sum_x (a_x)_(ij) [x]) [h] e_chi = (a_(g h^-1))_(ij) e_chi`. This
    matches `Reg`: the coefficient of `[g] ⊗ ε_i` in `A([h] ⊗ ε_j)` is `(a_(g h^-1))_(ij)`.
  * **Equal ranks.** `Cc f_O = Cc Rr Cc = Cc`, so `Â = (I⊗Cc)(f_O A)(I⊗Rr)`. Also `(I⊗Rr) Â (I⊗Cc) = f_O A f_O = f_O A`.
    `rk'(Reg(A) ⊗ e_chi) = rank_F Reg(A) · rk'(e_chi)`, as in Step 3.
* **Step 5.** Recomputed; the author asked for the count.
  * **Non-free characters.** Characters are `chi_b` with `b in (Z/p)^Pi`, and `(g chi_b)(c_v) = chi_b(c_(g^-1[v]))`.
    So `g chi_b = chi_b` iff `b` is constant on the `<g>`-orbits of `Pi`. There are at most `|Pi| − 1` such orbits
    for `g != 1`, hence at most `p^(|Pi|−1)` fixed characters. The union bound gives `(|G| − 1)p^(|Pi|−1)`.
  * **Error terms.**
    * Free orbits: at most `(p^|Pi| − N_free) p^(−|Pi|) (1−phi) rank Reg(A)/|G| <= n(|G|−1)/p`.
    * Non-free nontrivial orbits: between `0` and `n(|G|−1)/p`, via `rk'(f_O A) <= n rk'(f_O)`.
    * Trivial orbit: at most `2n/p`.
    * Total: at most `2n|G|/p`, inside the stated `4n|G|/p`. There are infinitely many odd primes `p != char F`.
* **Scope.** The canonical partition `P_H` of the ESTABLISHED
  `finite-subgroups-of-thompson-v-permute-a-canonical-partition` makes every finite `H <= V` a cylinder group.
* **Consistency, rechecked against the nodes.**
  * **`thompson-v-rank-models-through-displacing-sym-reps-are-trivial`.** Its hypothesis factors the stage maps
    `sigma_k = pi_k o phi_k` through `S_(m_k)` with positive 3-cycle displacement. Theorem 1.1 restricts `sigma` to
    finite subgroups of `V` and yields no such factorization. No conflict.
  * **`thompson-v-rank-models-displace-every-element-uniformly`.** For `z` of order `m` in a finite subgroup,
    `rank Reg(1−[z])/|G| = (m−1)/m` in every characteristic: the invariants of `F[Z/m]` are the norm line, and
    `F[G]` is free over `F[<z>]`. So `rk(1 − [z]) = (1−phi)(m−1)/m >= (1−phi)/2 >= d_3/4 = (1−phi)/6`. Consistent.

### 32.2 Corollary 1.2 (order-char law, every prime): PASS

* **Cylinder model.** Use pieces `[w_k]` and let `Pi` be `{[w_k]}` plus a cylinder partition of `D`. Then
  `<s_0>` is a cylinder group.
* **Conjugacy for every prime.** This includes `p = 2` and `p = char F`. [TS] Lemma 1.1 uses only `g^p = 1` and prefix
  bijections, re-derived for clopen `n`-cycles in §31.5.
* **Ranks.** In characteristic `p`, `x^p − 1 = (x − 1)^p`, so `F[Z/p] = F[y]/(y^p)`. `y^j F[y]/(y^p)` has dimension
  `p − j`, and `eps((1−[s])^j) = 0`.
  * The drops are `d_0 = phi + (1−phi)/p` and `d_i = (1−phi)/p`, matching the law node's display.
  * The values lie under both bounds of §31.3(c).

### 32.3 Section 2 (characteristic-two dihedral cross-check): PASS

* **The pair.** `t` swaps `union_(1<=i<=(q−1)/2) [w_i]` with `union [w_(−i)]` and fixes `[w_0] ∪ D`. Also
  `t c t(w_i x) = w_(i−1) x`.
* **The idempotent.** `q = 1` in `F` gives `e^2 = q e = e`, and `[t] e [t] = e`.
* **Lower bound.** `u x + x u' = u + u' + 2u[t] = e + 1`, with `rk(1−e) = (1−phi)(q−1)/q`.
* **Upper bound.**
  * `x^2 = 2(1 + [t]) = 0`, so `y = (1−e)x` has `y^2 = 0`.
  * (S7) in `(1−e)R(1−e)` gives `0 >= 2 rk y − rk(1−e)`.
  * `e x (1−e) = 0` and `e x e = e x`, so `rk(ex) <= (1−phi)/q`.
* **Limit.** The bounds `(1−phi)(q−1)/(2q) <= r <= (1−phi)(q+1)/(2q)` give `r = (1−phi)/2`. This agrees with 32.2 at
  `p = 2`, independently of the character count.

### 32.4 Section 3 (λ-model) and Section 4: PASS

* **Homomorphism.** `(1 + λN)(1 + μN) = 1 + (λ+μ)N`, since `N^2 = 0` and the characteristic is 2. It is injective.
* **Invariance.**
  * `sigma` is injective iff the `S_i` are linearly independent.
  * Then the `mu_i` are independent linear forms, hence algebraically independent after an invertible linear
    substitution, and `lambda_(Δ S_i) = sum mu_i`.
* **Fixed ranks.**
  * `phi_(E_k)(rk_λ) = 1 − rank col(λ_i N)/2 = 1/2`.
  * A trivial-plus-regular function has `rk(1 + [t_1]) = (1−α)/2` and `phi_(E_k) = α + (1−α)2^−k`, since the
    kernel of `col Reg(1 + [t_i])` is the norm line.
  * So `α = 0`, and then `2^−k != 1/2` for `k >= 2`. No extension to `F_2[V]` exists.
* **Section 4.**
  * **Local formula.** It holds.
  * **Convexity.** Use block sizes `floor(β n_k)`. `phi_V` is affine, and a nontrivial model with `phi_V = 0` gives
    intermediate values, so the gate is equivalent to `phi_V ∈ {0,1}`.
  * **Reduced models.** They cite [FR] Corollary 1.3(5), correctly marked matricial (§30.2), and "abstract
    compression is open" is stated honestly.
  * **4.4.** `phi_V = 1` forces `rk(1−[g]) = 0` for all `g`, which is the augmentation rank.

### 32.5 Scan and verdict

* **Scan.** I scanned every node mentioning `F[V]` or V rank models, and the trivial-plus-regular / regular-rank
  vocabulary across `research/`, without truncation. No ESTABLISHED node already states Theorem 1.1. The nearest are:
  * `v-rank-models-are-trivial-plus-free-on-odd-cycle-trees`, the special case with `|P|` invertible;
  * `finite-subgroup-data-cannot-force-defect-submultiplicativity` and
    `perfect-group-augmentation-quotient-ranks-are-fixed-point-free`, which concern other groups or properties;
  * Proposition 0.1 of the binary-cyclic dichotomy artifact, which is about fullness, not ranks.
  * The claim node's `distinct_from` entries are accurate.
* **Node displays.** The claim node (Setting, Claim, Scope, Consequences, Attempts), the law node's display, and the
  binary gate's new Attempts entries all match the artifact.
* **Precision notes (non-blocking).**
  * (i) For `G = 1` the trivial character counts as "free", so Step 5 should read "free nontrivial orbits". For
    `|G| >= 2` it is as written.
  * (ii) The Step 5 total is `2n|G|/p`.
  * (iii) The claim node's dihedral bullet writes `p` for the odd prime, where the artifact writes `q`.
* **Not decision-level.** None of these is claimed: a Cohn family, a lift, a direct-finiteness failure, a nonpositive
  unit class, a rank-model construction, or an identity proof. The λ-model lives on `F_2[E_∞]` and provably does not
  extend to `V`.
* **Verdict.**
  * PASS: Theorem 1.1, Corollary 1.2, and Sections 2–3. The claim
    `v-rank-functions-are-trivial-plus-regular-on-cylinder-groups` and the law
    `v-rank-order-char-cycles-are-trivial-plus-regular` may land ESTABLISHED through the author's planned routes.
  * PASS as a reorganization: Section 4.
  * OPEN, undecided: `thompson-v-has-no-nontrivial-f2-rank-model` and
    `thompson-v-ternary-rank-functions-are-augmentation`.
