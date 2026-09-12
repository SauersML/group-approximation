# The ternary anti-central summand: matrix amplification and an idempotent-free Cohn form

Lane `gk-l3-units`, 2026-09-12. Supports the Cairn claims
`anti-central-ternary-summand-contains-its-matrix-ring` and
`ternary-anti-central-summand-has-cohn-family`, and the routes
`anti-central-cohn-family-gives-swap-corner-fullness` and
`swap-corner-fullness-gives-anti-central-cohn-family`.

Nothing here claims a solution of the ternary corner equation. The results remove the swap
idempotent from the target, show the anti-central summand contains matrix rings over itself, and
put the search in a form that explicit unit lifts can address.

## 0. Notation

`k = F_3`, `R = L_k(1,2)`, `G = R^x`, `S = k[G]`, and `z = -1` in `G`, which is central of order
two. `eps_(+-) = 2(1 +- [z])` are the central idempotents of
`ternary-leavitt-swap-problem-splits-at-central-involution`, `S_- = eps_- S` has unit
`1_- = eps_-`, and `[z] = -1_-` in `S_-`. `pi : S -> R` is the evaluation. It kills `S_+`, so its
restriction `pi_-` maps `S_-` onto `R`, and `K_- = ker pi_-`.

`w = s0 t1 + s1 t0`, `d = s0 t0 - s1 t1`, `e = 2(1 + [w])` and `e_- = eps_- e`. The matrix units of
Lemma 7.2 of `research/artifacts/invariant-output-descent-and-sensitivity-2026-09-12.md` are

```text
E_11 = e_-,   E_22 = 1_- - e_-,   E_12 = e_- [d],   E_21 = [d] e_-,
```

with `[d] e_- [d] = 1_- - e_-`, `e_- [d] e_- = 0` and `[d] = E_12 + E_21`.

## 1. The diagonal endomorphism

**Lemma 1.1.** `delta(g) = s0 g t0 + s1 g t1` is an injective group endomorphism of `G` with
`delta(z) = z`, and every `delta(g)` commutes with `w` and with `d`.

*Proof.* `t_i s_j = delta_ij` gives
`delta(g) delta(h) = s0 g t0 s0 h t0 + s0 g t0 s1 h t1 + s1 g t1 s0 h t0 + s1 g t1 s1 h t1 = delta(gh)`,
and `delta(1) = s0 t0 + s1 t1 = 1`, so `delta(g)` is a unit with inverse `delta(g^-1)`. Injectivity
follows from `t0 delta(g) s0 = g`. Also `delta(-1) = -(s0 t0 + s1 t1) = -1`. Finally

```text
w delta(g) = s0 g t1 + s1 g t0 = delta(g) w,
d delta(g) = s0 g t0 - s1 g t1 = delta(g) d.       QED
```

The linear extension `delta_* : S -> S` is an injective unital algebra homomorphism. Since
`delta_*([z]) = [z]`, it fixes `eps_-` and restricts to an injective unital endomorphism of `S_-`.
It is compatible with evaluation: `pi delta_* = delta_R pi`, with `delta_R(r) = s0 r t0 + s1 r t1`.

**Lemma 1.2.** `Q = span_k{1_-, [w], [d], [wd]}` is a subalgebra of `S_-` isomorphic to `M_2(k)`,
with matrix units `E_ij`.

*Proof.* In `G`, `w^2 = d^2 = 1` and `d w d = z w`, so in `S_-`, `[w]^2 = [d]^2 = 1_-` and
`[d][w] = -[w][d]`. Hence `Q` is closed under products. Its four spanning elements are linearly
independent, because `1, w, d, wd` have distinct images in `PG = G/<z>`. The `E_ij` lie in `Q`,
satisfy `E_ij E_kl = delta_jk E_il` (Lemma 7.2), and sum on the diagonal to `1_-`. Four linearly
independent matrix units in a four-dimensional algebra give `Q ~= M_2(k)`. QED

**Theorem 1.3 (matrix amplification).** `B = delta_*(S_-)` commutes with `Q`, and

```text
J : M_2(S_-) -> S_-,     J((x_ij)) = sum_(i,j) E_ij delta_*(x_ij)
```

is an injective unital algebra homomorphism with `J(E_11 (x) 1) = e_-`.

*Proof.* By Lemma 1.1 every `[delta(g)]` commutes with `[w]` and `[d]`, so `B` centralizes `Q`. For a
central simple subalgebra `Q` of a `k`-algebra and any subalgebra `C` of its centralizer, the
multiplication map `Q (x)_k C -> S_-` is injective. To see this, apply the elementary operators
`x -> sum_r a_r x b_r` (which realize all of `Q (x) Q^op ~= End_k(Q)`) to `sum_i q_i c_i`, with `q_i`
a basis of `Q`, and isolate each coefficient `c_i`. With the matrix units of Lemma 1.2,
`Q (x) B ~= M_2(B)`. Composing with `delta_* : S_- ~= B` gives `J`. It is multiplicative because the
`E_ij` commute with `B`, and unital because `E_11 + E_22 = 1_-` and `delta_*(1_-) = 1_-`. QED

**Corollary 1.4.** For every `n >= 0`, `M_(2^n)(S_-)` embeds unitally in `S_-`. So `S_-` is directly
finite if and only if it is stably finite.

*Proof.* Iterate `J`, using `M_2(M_(2^n)(S_-)) = M_(2^(n+1))(S_-)`. A pair `BA = I != AB` in some
`M_m(S_-)` pads with an identity block to `M_(2^n)(S_-)`. The unital injective embedding carries it
to `ba = 1_- != ab` in `S_-`. QED

## 2. The idempotent-free form of the swap corner

**Theorem 2.1.** The following are equivalent.

- (a) There are `b, c` in `S_-` with `c e_- b = 1_-`. This is `ternary-anti-invariant-swap-corner-is-full`.
- (b) `S_-` contains a unital two-pair Cohn family: `sigma_1, sigma_2, tau_1, tau_2` with
  `tau_i sigma_j = delta_ij 1_-`.
- (c) `S_-^2` is isomorphic to a direct summand of `S_-` as a right `S_-`-module.
- (d) Some `sigma_1, sigma_2, tau_1, tau_2` in `S_-` have Gram matrix `M = [tau_i sigma_j]` invertible
  in `M_2(S_-)`.

*Proof.*

**(b) implies (a).** `phi(x) = e_- delta_*(x)` is a unital algebra homomorphism `S_- -> T = e_- S_- e_-`,
because `delta_*(x)` commutes with `e_-`. Put

```text
b = e_- delta_*(sigma_1) + e_- [d] delta_*(sigma_2),
c = e_- delta_*(tau_1)   + [d] e_- delta_*(tau_2).
```

Since `delta_*(S_-)` commutes with `[d]` and `e_-`, write `D_i = delta_*(sigma_i)` and
`C_i = delta_*(tau_i)`. Then

```text
c e_- b = e_- C_1 D_1 + e_- [d] ... (cross)
        = e_- C_1 D_1 + e_- e_-[d] C_1 D_2 + [d] e_- e_- C_2 D_1 + [d] e_- [d] C_2 D_2
        = e_- delta_*(tau_1 sigma_1) + E_12 delta_*(tau_1 sigma_2)
          + E_21 delta_*(tau_2 sigma_1) + (1_- - e_-) delta_*(tau_2 sigma_2)
        = e_- + 0 + 0 + (1_- - e_-) = 1_-.
```

**(a) implies (b).** Given (a), put `beta_j = e_- b [d]^(j-1) e_-` and `gamma_i = e_- [d]^(i-1) c e_-`,
all in `T`. Then

```text
gamma_i beta_j = e_- [d]^(i-1) (c e_- b) [d]^(j-1) e_- = e_- [d]^(i+j-2) e_- = delta_ij e_-,
```

by `[d]^2 = 1_-` and `e_- [d] e_- = 0`. The four products
`v_1, v_2, v_3, v_4 = beta_1 beta_1, beta_1 beta_2, beta_2 beta_1, beta_2 beta_2` and
`u_1, u_2, u_3, u_4 = gamma_1 gamma_1, gamma_2 gamma_1, gamma_1 gamma_2, gamma_2 gamma_2` satisfy
`u_p v_q = delta_pq e_-`, since `(gamma_j gamma_i)(beta_k beta_l) = delta_ik delta_jl e_-`. Put

```text
sigma_1 = v_1 + [d] v_2 [d],   sigma_2 = v_3 + [d] v_4 [d],
tau_1   = u_1 + [d] u_2 [d],   tau_2   = u_3 + [d] u_4 [d].
```

For `x, y` in `T`, `x [d] y = x e_- [d] e_- y = 0`. So every cross term vanishes, and

```text
tau_a sigma_b = u_(2a-1) v_(2b-1) + [d] u_(2a) v_(2b) [d] = delta_ab (e_- + [d] e_- [d]) = delta_ab 1_-.
```

These are the diagonal matrices `diag(v_1, v_2)`, ... of `S_- ~= M_2(T)`.

**(b) iff (c).** `(x_1, x_2) -> sigma_1 x_1 + sigma_2 x_2` is a split injection `S_-^2 -> S_-` with
retraction `x -> (tau_1 x, tau_2 x)`, and every split injection has this form.

**(b) iff (d).** (b) gives (d) with `M = I`. Conversely, `tau'_i = sum_k (M^-1)_ik tau_k` satisfies
`tau'_i sigma_j = delta_ij 1_-`. QED

**Remark 2.2 (lifts and the Gram defect).** `pi_-` carries a Cohn family of `S_-` to one of `R`. If
the `sigma_j` lift `s_j` and the `tau_i` lift `t_i`, then `M` lies in `I + M_2(K_-)`. By (d), the
target is to choose such lifts with `M` invertible. `M - I` nilpotent is sufficient. Invertibility
of `M` in `M_2(S_-)` is invertibility of `J(M)` in `S_-`. `K_-` contains nonzero idempotents (lane
`gk-l3-kernel`), so `I + M_2(K_-)` is not automatically invertible.

**Remark 2.3 (no augmentation obstruction).** The augmentation `[g] -> 1` sends `eps_-` to
`2(1 - 1) = 0`, so no unital map `S_- -> k` extends it. Proposition 6 of
`research/artifacts/leavitt-inverse-defect-normal-forms-2026-09-12.md` forbids a unital binary
Leavitt family in `k[G]`, but that obstruction does not apply inside `S_-`. The canonical trace
does apply, and it forbids unital binary Leavitt families in `S_-` (Proposition 2.5). It does not
forbid quaternary ones, and it forbids no Cohn family.

**Proposition 2.4 (support filter).** Suppose (b) holds with all four elements supported on a finite
set `F` in `G`. Then `H = <F, z>` is not `F_3`-linear sofic, so in particular it is nonsofic.

*Proof.* The family lies in `eps_- k[H]`, a direct factor of `k[H]`. `sigma_1 tau_1 != 1_-`: otherwise
`tau_2 = tau_2 sigma_1 tau_1 = 0`, contradicting `tau_2 sigma_2 = 1_-`. So
`(tau_1 + eps_+)(sigma_1 + eps_+) = 1 != (sigma_1 + eps_+)(tau_1 + eps_+)` in `k[H]`, and
`linear-sofic-group-algebra-is-stably-finite` applies. QED

**Proposition 2.5 (the canonical trace).** For a conjugacy class `C` of `G`, put
`tau_C(sum x_h [h]) = sum_(h in C) x_h`, and write `tau = tau_({1})`. Each `tau_C` is a trace on `S`,
since `gh` and `hg` are conjugate, and hence a trace on the direct factor `S_-`. Moreover

```text
tau_C(1_-) = tau_C(2[1] - 2[z]) = 2 [C = {1}] - 2 [C = {z}],
```

so `tau(1_-) = 2 != 0`.

- (i) If `sigma_1, ..., sigma_n, tau_1, ..., tau_n` in `S_-` satisfy `tau_i sigma_j = delta_ij 1_-` and
  `sum_j sigma_j tau_j = 1_-`, then `n = 1 mod 3`. So `S_-` contains no unital binary Leavitt family,
  but a quaternary family is not excluded.
- (ii) For a two-pair Cohn family with defect idempotent `p = 1_- - sigma_1 tau_1 - sigma_2 tau_2`,
  `tau_C(p) = -tau_C(1_-)`. So `tau(p) = 1`, `tau_({z})(p) = -1`, and `tau_C(p) = 0` for every other
  class. For comparison, `tau(e_-) = tau(4(1 - [z])(1 + [w])) = 1`.
- (iii) A unital quaternary Leavitt family in `S_-` contains a two-pair Cohn family: take
  `sigma_1, sigma_2, tau_1, tau_2`.

*Proof.*
- (i) `tau(1_-) = sum_j tau(sigma_j tau_j) = sum_j tau(tau_j sigma_j) = n tau(1_-)`. So
  `(n - 1) 2 = 0` in `F_3`, and `3` divides `n - 1`.
- (ii) `tau_C(p) = tau_C(1_-) - sum_(j <= 2) tau_C(tau_j sigma_j) = tau_C(1_-) - 2 tau_C(1_-)`.
- (iii) Immediate.

QED

In `R` the words `s_i s_j` and `t_j t_i` form a unital quaternary Leavitt family. Lifting that family
exactly into `S_-` is trace-compatible and sufficient. Lifting the binary family `(s_i, t_i)`
exactly is impossible.

## 3. Honest idempotent lifts in characteristic three

**Lemma 3.1.** For every idempotent `p` of `R`, `1 + p` is an involution in `G`, and
`P_p = 2(1 - [1 + p])` is an idempotent of `S` with `pi(P_p) = p`.

*Proof.* `(1 + p)^2 = 1 + 3p = 1`. For `x^2 = 1`, `(2(1 - x))^2 = 4(2 - 2x) = 2(1 - x)`. And
`pi(P_p) = 2(1 - 1 - p) = -2p = p`. QED

For example `1 + s1 t1 = d` and `1 + s0 t0 = -d`, so in `S_-` the Leavitt projections `s0 t0` and
`s1 t1` lift to `2(1 + [d])` and `2(1 - [d])`. These are the two diagonal matrix units of the
quaternion subalgebra conjugated by the Hadamard-type change of basis. For a cylinder projection
`p_beta = S[beta] T[beta]`, `P_(p_beta)` lies in the group algebra of the signed Thompson units.

**Lemma 3.2.** For incomparable words `alpha, beta`, the cylinder transposition

```text
g_(alpha beta) = S[alpha] T[beta] + S[beta] T[alpha] + 1 - S[alpha] T[alpha] - S[beta] T[beta]
```

is an involution in `G`, and `P_(p_alpha) [g_(alpha beta)] P_(p_beta)` lifts the partial isometry
`S[alpha] T[beta]`.

*Proof.* Incomparability gives `T[alpha] S[beta] = 0`, so `g^2 = 1`. And
`p_alpha g p_beta = S[alpha] T[alpha] S[alpha] T[beta] S[beta] T[beta] = S[alpha] T[beta]`. QED

**Lemma 3.3 (equivariance and the XOR law).** For `g` in `G` and every idempotent `p` of `R`,
`[g] P_p [g^-1] = P_(g p g^-1)` exactly in `S`. If `p` and `q` commute, then
`1 + (p + q + pq) = (1 + p)(1 + q)`, so `p -> 1 + p` is a group homomorphism from commuting idempotents
under symmetric difference `p xor q = p + q + pq` (characteristic three) into an elementary abelian
2-subgroup of `G`. Also `P_(p xor q) = P_p + P_q + P_p P_q`.

*Proof.* Conjugation fixes `1` and sends `1 + p` to `1 + g p g^-1`. The product identity is a direct
expansion, and the last identity follows by expanding `2(1 - [(1+p)(1+q)])` against
`P_p P_q = 4(1 - [1+p] - [1+q] + [1+p][1+q])`. QED

Examples in `S_-`:
- `1 + s0 t0 = -d`, so `P_(s0 t0) = 2(1 + [d])`.
- `1 + pi(e) = -w`, so the swap idempotent `e_-` is the honest lift `P_(pi(e))`.
- The Hadamard unit `h_H = s0 t0 + s0 t1 + s1 t0 - s1 t1` has `h_H^2 = z` and conjugates `pi(e)` to
  `s0 t0`. So `[h_H] e_- [h_H]^-1 = P_(s0 t0)` (compare lane `gk-l3-free`).

So the corner target is equivalently the fullness of `P_(s0 t0)`, and every conjugation by a unit
sends honest lifts to honest lifts.

**The natural lift of `(s0, t0)` and its exact defect.** Consider the Thompson units
`g = S[00]T[0] + S[01]T[10] + S[1]T[11]` and `h = S[01]T[1] + S[1]T[01] + S[00]T[00]` (an involution).
Then `s0 = g p_0 + h p_1` and `t0 = g^-1 p_00 + h p_01`, with `p_U = S[U]T[U]`. The lifts

```text
a = [g] P_0 + [h] P_1,          c = [g^-1] P_00 + [h] P_01,        P_U := P_(p_U),
```

satisfy `pi(a) = s0` and `pi(c) = t0`. By Lemma 3.3, using `g^-1 p_00 g = p_0`, `h p_01 h = p_1`,
`h p_00 h = p_00` and `g^-1 p_01 g = p_10`:

```text
c a = P_0 + P_1 + [g^-1 h] P_00 P_1 + [h g] P_10 P_0 = 1_- + [g^-1 h] P_00 P_1 + [h g] P_10 P_0.
```

Every defect term is a unit times a product `P_U P_V` of honest lifts of disjoint cylinders. Such a
product is a nonzero idempotent in `K_-`, because `1, 1 + p_U, 1 + p_V, 1 + p_U + p_V` have distinct
images in `PG`.

In the same way, `c [w] a` is a sum of four such terms, for example `[g^-1 w g] P_110 P_0`, because
`w g` maps `11x` to `0x`.

**The mass dichotomy for monomial lifts.**
- Fix a cylinder partition `{U_1, ..., U_n}`. Its involutions `x_U = 1 + p_U` generate `C_2^n`, whose
  product is `z`. So in `S_-` their span is the algebra of functions on the odd characters `chi`
  (an odd number of `-1` values).
- Characters with one `-1` at `U` map to `p_U` under `pi`. Characters with three or more `-1` values
  map to `0`: that is the kernel mass `m`.
- Honest lifts `P_U` carry parts of `m`, and their products `P_U P_V` are exactly the mass terms
  above.
- The orthogonal lifts `f_U` (single-minus characters) kill every cross term, but
  `sum_U f_U = 1_- - m` misses the mass.
- So a monomial lift pays either in cross terms or in missing mass. In `R` the mass is invisible.
- This is the finite shadow of the invariant-measure obstruction of lane `gk-l3-free`. It is recorded
  as a diagnostic, not a theorem: non-monomial units, or mod-3 overlaps between different partitions,
  are exactly what escapes it.

**Where monomial lifts stop.** Every finite decomposition of `s_0` into partial isometries between
cylinders, over a complete prefix code, contains a piece `S[0^(k+1)] T[0^k]` whose cylinders are
comparable. Lemma 3.2 does not cover such a piece: it is itself a conjugate of `s_0`. So products of
Lemmas 3.1 and 3.2 give lifts of every disjoint piece and never of the isometry itself. Lane
`gk-l3-free` reports a crossed-product model of the signed Thompson group algebra, in which an
invariant measure rules out honest monomial compressions. Witnesses must therefore use mod-3
overlaps between monomial terms, or leave that group through non-monomial units such as
`1 + s_i r t_j` (i != j) with non-monomial `r`, or a Hadamard unit.

## 4. The depth-two Hadamard involution, and why constant units cannot help

*Corrected 2026-09-12 (lanes gk-l3-free and gk-vf-linear).* The first version of this section made
three claims, all withdrawn below:
- a Hadamard frame cancels every cross term (withdrawn Proposition 4.2);
- the kernel mass lives at infinite depth;
- the result is a dichotomy between finite and infinite support.

What survives: Lemma 4.1, Proposition 4.3 with a corrected containment, its extension to all constant
units (Corollary 4.5), and Remark 4.4.

**Lemma 4.1 (the level-two Hadamard is an involution over `F_3`).** Realize a unit by its action on
`R ~= R^(V)`, `V = {00, 01, 10, 11}`, through `x -> (T[v] x)_v`: a matrix `N` over `F_3` indexed by
`V` gives the unit `u_N = sum_(v,v') S[v] N_(v v') T[v']`, with `u_N u_(N') = u_(N N')`. Let
`M = [[1,1],[1,-1]]` and `N = M (x) M`, the `4 x 4` Hadamard matrix. Then `u_N` is a unit of `G` with
`u_N^2 = 1`.

*Proof.* `u_N u_(N') = u_(N N')` is the computation `T[v] S[w] = delta_(vw)` done blockwise at depth
two. `M^2 = [[2,0],[0,2]] = -I` over `F_3`, so `N^2 = M^2 (x) M^2 = (-I)(x)(-I) = I_4`. Hence
`u_N^2 = u_(I_4) = 1`. QED

So over `F_3` itself, with no passage to `F_9`, `H_2 = u_N` is an honest involution, and
`f_(+-) = 2(1 +- [H_2])` are non-monomial idempotents of `F_3[G]`, lying in `S_-` after multiplying
by `eps_-`. (Over `F_9` the depth-one `h` of Lemma 3.3 already gives order-four spectral idempotents
`2(1 -+ i[h])`; the depth-two picture needs neither `i` nor `F_9`, because `4 = 1` in `F_3`.)

**Withdrawn Proposition 4.2.** The first version asserted `sigma_v, tau_v` supported on a finite
subgroup with `tau_v sigma_(v') = delta_(v v') 1_-` and `sum_v sigma_v tau_v = 1_-`. That is false.

- **Why it fails.** Such a family is a unital quaternary Leavitt family in the finite-dimensional
  algebra `A = eps_- F_3[H]`. It forces `A ~= A^4` as right modules, so `dim A = 4 dim A` and `A = 0`,
  although `1_- != 0`. Proposition 4.3 excludes it as well.
- **What was not shown.** No Hadamard unit was shown to cancel the Section 3 cross terms.
- **What is true at a fixed depth** is only what Section 3 already records: the orthogonal character
  lifts `f_U` of the cylinder projections are pairwise orthogonal, but they sum to `1_- - m` and miss
  the kernel mass `m`.

**Proposition 4.3 (finite supports).** Let `H` be a finite subgroup of `G` containing `z`. No unital
two-pair Cohn family of `S_-` is supported on `H`.

*Corrected containment.* Fix a depth `k`. The group generated by `H_2`, the depth-`k` permutation units
`u_P` and the involutions `1 + p_u` with `|u| <= k` is finite, but it is not a `2`-group.
- It lies in `u(GL_(2^K)(F_3))` with `K = max(2, k)`, by level coherence
  `u_N = u_(N (x) I_2)` (expand `1 = s0 t0 + s1 t1` between `S[v]` and `T[v']`).
- `GL_4(F_3)` has order divisible by `3`.
- The first version called this group a signed-permutation `2`-group, but `H_2` is not a signed
  permutation. Only finiteness is used.

*Proof.* A family supported on `H` lies in `eps_- F[H]`, a finite-dimensional `F`-algebra. Such an
algebra is Dedekind-finite: if `tau_1 sigma_1 = 1_-`, then left multiplication by `sigma_1` is
injective on the finite-dimensional `eps_- F[H]` (``sigma_1 x = 0`` gives `x = tau_1 sigma_1 x = 0``),
hence surjective, so `sigma_1` is a unit with inverse `tau_1`. Then `tau_1 sigma_2 = 0` forces
`sigma_2 = sigma_1 (tau_1 sigma_2) = 0`, contradicting `tau_2 sigma_2 = 1_-`. QED

This is the finite-support case of
`swap-separated-pairs-avoid-finitely-represented-supports` (lane gk-kdf-structure): a finite `H`
has a finite-dimensional representation sending `z` to `-1`, namely the regular one restricted to
`eps_-`.

**Corollary 4.5 (all constant units).** The constant units `C = union_k u(GL_(2^k)(F_3))` form a
locally finite subgroup of `G` containing `z = u(-I)`. So no unital two-pair Cohn family of `S_-` is
supported on `C`. By level coherence, finitely many constant units lie in one finite
`u(GL_(2^K)(F_3))`, and Proposition 4.3 applies. Equivalently, `eps_- F_3[C]` is a directed union of
finite-dimensional algebras. The same holds over every finite field. (Also lanes gk-l3-free and
gk-l3-corner.)

**Withdrawn dichotomy.** The first version said the kernel mass lives at infinite depth, so that a
witness needs infinite support. Both halves are wrong.

- **The kernel mass is at finite depth** (lane gk-l3-free).
  - At depth `n` the cylinder involutions generate `C_2^(2^n)`, whose odd characters are the
    `2^(2^n - 1)` odd-weight vectors of `F_2^(2^n)`. Haar measure on the odd character space pushes
    forward to the uniform measure on these vectors.
  - The visible characters are the `2^n` vectors of weight one. So the kernel clopen of weight at
    least three has Haar measure `1 - 2^(n + 1 - 2^n)`: `0` at depth one, `1/2` at depth two and
    `15/16` at depth three.
  - What sits at infinite depth is the Dirac set, the spectrum of `R`, and it is Haar-null.
- **"Needs infinite support" is not a no-go.** Elements of a group algebra are finitely supported, so
  that statement is equivalent to the nonexistence of a family, which is the open question. The
  finite-versus-infinite reading was a heuristic, not a theorem.

**What is proved about supports.**
- Proposition 4.3 and Corollary 4.5 exclude constant supports.
- Inside the signed Thompson crossed product, lane gk-l3-free shows that the Thompson projection of
  the support subgroup must be nonamenable, because an abelian-by-amenable support group has a stably
  finite group algebra.
- Nothing here excludes non-constant, finitely supported families. For example, Hadamard constants
  combined with the non-constant Thompson units `g, h` of Section 3.

**Remark 4.4 (`F_9` is not a cheaper target).** A witness over `F_9` would already refute Gottschalk
over the alphabet `F_9`, and `F_9`-linear soficity of `G` would refute the claim over `F_9`. `G`
nonsofic does not decide `F_9`-linear soficity. So enlarging the field buys non-monomial idempotents
at depth one but lowers neither the stakes nor the wall.

## 5. Scope

- Theorem 1.3 and Corollary 1.4 are unconditional.
- Theorem 2.1 is an exact equivalence. It moves the ternary corner problem to the idempotent-free
  target (b) or (d), and changes neither side's truth value.
- No certificate is claimed. The rank gate (`projective-ternary-group-is-f3-linear-sofic` through
  the corner embedding) still covers this summand: `F_3`-linear soficity of `G` makes `S_-`
  directly finite, which refutes (b).
