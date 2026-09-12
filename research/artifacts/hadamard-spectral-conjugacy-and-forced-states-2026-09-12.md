# The Hadamard spectral half is the swap idempotent, and states are forced on the signed Thompson group

Lane `w4-hadamard-f3`, 2026-09-12. Supports:
- `hadamard-spectral-half-is-constant-conjugate-to-swap-idempotent` (Section 1), with route
  `hadamard-spectral-half-constant-conjugacy-proof`;
- the route `f9-hadamard-fullness-from-swap-corner-fullness` into `f9-hadamard-spectral-idempotent-is-full`
  (Corollary 1.4);
- `anti-central-k0-states-equal-lifted-trace-on-signed-thompson` (Section 2), with route
  `anti-central-k0-states-lifted-trace-proof`.

Directive: decide `f9-hadamard-spectral-idempotent-is-full` (w3-corner-cohn-b, e5b4731bcd), either by a
design `c f_+ b = 1_-` or by a state that sees `h`. Outcome: the target is the swap corner itself,
conjugated by a constant `F_9` unit (Section 1). The state side is rigid on every finite subgroup of the
signed Thompson group, and the only place a state can see `h` is one block split (Section 2).

## 0. Notation

- `R = L_(F_3)(1,2)`, `G = R^x`, `z = -1`, `S_- = eps_- F_3[G]` with `eps_- = 2(1 - [z])` and unit `1_- = eps_-`,
  `S_-^(9) = F_9 (x) S_-`, `i^2 = -1` in `F_9`. In characteristic three `2 = -1` and `4 = 1`.
- `M : R -> M_2(R)`, `x -> (t_i x s_j)`, is an algebra isomorphism. A matrix `a` in `GL_2(F_3)` names the
  constant unit `sum_ij s_i a_ij t_j` of `G`, and `a -> sum s_i a_ij t_j` is an injective homomorphism.
- `w = [[0,1],[1,0]]`, `d = [[1,0],[0,-1]]`, `h = [[1,1],[1,-1]]`, `u = [[1,0],[1,-1]]`.
- `e_- = 2 eps_- (1 + [w])` (the swap idempotent) and `f_+ = 2(1_- + i[h])`, `f_- = 1_- - f_+`
  (`f9-hadamard-spectral-idempotents-are-half-idempotents`).
- `Q = span_(F_3){1_-, [w], [d], [wd]}`, a unital copy of `M_2(F_3)` (Lemma 1.2 of
  `ternary-anti-central-cohn-reformulation-2026-09-12.md`). Evaluation `pi` is injective on `Q`.
- `H = E x| V`, the signed Thompson group, with `F_3[H] eps_- = C(M_-, F_3) x| V`
  (`signed-thompson-algebra-is-odd-measure-crossed-product`), `lambda` the Haar measure on `M_-`.

## 1. The spectral half is a constant conjugate of the swap idempotent

**Lemma 1.1.** Put `c = [[-1,0],[1,1]] = -s0 t0 + s1 t0 + s1 t1`, a constant unit of `G`. Then

```text
c^2 = 1,     c d c = u,     c (wd) c = h,     c w c = hu = [[-1,-1],[0,1]].
```

*Proof.* Matrix arithmetic over `F_3`.
- `c^2 = [[1,0],[-1+1,1]] = I`.
- `c d = [[-1,0],[1,-1]]`, and `(c d) c = [[1,0],[-2,-1]] = [[1,0],[1,-1]] = u`.
- `wd = [[0,-1],[1,0]]`, `c (wd) = [[0,1],[1,-1]]`, and `(c wd) c = [[1,1],[-2,-1]] = [[1,1],[1,-1]] = h`.
- `c w c = c (wd) d c = (c wd c)(c d c) = h u`, and `h u = [[2,-1],[0,1]] = [[-1,-1],[0,1]]`. QED

**Lemma 1.2.** `Q' = [c] Q [c]^(-1) = span_(F_3){1_-, [h], [u], [hu]}` is a unital subalgebra of `S_-`
isomorphic to `M_2(F_3)`, evaluation is injective on it, and `Q'_9 = F_9 (x) Q'` is a unital copy of `M_2(F_9)`
inside `S_-^(9)`. It contains `f_+`, `f_-` and `E'_11 = [c] e_- [c]^(-1) = 2 eps_- (1 + [hu])`.

*Proof.* Conjugation by the group element `[c]` is an algebra automorphism of `S_-` fixing `1_-`, and it carries
`[w], [d], [wd]` to `[hu], [u], [h]` by Lemma 1.1. `pi([c] x [c]^(-1)) = c pi(x) c^(-1)`, so injectivity of `pi` on
`Q` passes to `Q'`, and `pi(Q') = M_2(F_3)` by dimension. Tensor with `F_9`. QED

**Theorem 1.3.** Put `p = f_+`, `q = E'_11`, and

```text
v  = p q + (1_- - p)(1_- - q),        v' = q p + (1_- - q)(1_- - p).
```

Then `v` is a unit of `Q'_9` with `v^(-1) = -v'`, and

```text
f_+ = W e_- W^(-1),      W = v [c].
```

*Proof.*
- *Intertwining.* For idempotents in any ring, `v q = p q = p v`, and
  `v v' = v' v = 1 - (p - q)^2`, and `(p - q)^2` commutes with `p` and `q`. (Expand:
  `(1-p)(1-q)(1-p) = 1 - p - q + pq + qp - pqp`, add `pqp`, and compare with `(p-q)^2 = p + q - pq - qp`.)
- *The matrices.* Under `pi`, `q = 2(I + hu) = 2 [[0,-1],[0,2]] = [[0,1],[0,1]]` and
  `p = 2(I + i h) = [[-1-i, -i],[-i, -1+i]]`. Both are idempotents of rank one; `p^2 = p` because
  `(-1-i)^2 + (-i)^2 = 2i - 1 = -1 - i` and `(-1-i)(-i) + (-i)(-1+i) = 2i = -i`.
- *The square.* `p - q = [[-1-i, -1-i],[-i, 1+i]]` and `(p - q)^2 = -I`: the diagonal entries are
  `(-1-i)^2 + (-1-i)(-i) = 2i + (i - 1) = -1` and `(-i)(-1-i) + (1+i)^2 = (i - 1) + 2i = -1`, and the
  off-diagonal entries are `2i - 2i = 0` and `(i - 1) + (-i + 1) = 0`.
- *Transfer.* `pi` is injective on `Q'_9` (Lemma 1.2), so `(p - q)^2 = -1_-` in `Q'_9`, and
  `v v' = v' v = 2 . 1_- = -1_-`. Hence `v^(-1) = -v'`, and `v q v^(-1) = p v v^(-1) = p`.
- *Conclusion.* `f_+ = v [c] e_- [c]^(-1) v^(-1)`. QED

**Corollary 1.4.** For `b, c'` in `S_-^(9)`, `c' f_+ b = 1_-` iff `(c' W) e_- (W^(-1) b) = 1_-`. Hence
`f9-hadamard-spectral-idempotent-is-full` holds iff `ternary-anti-invariant-swap-corner-is-full` holds.

*Proof.*
- *If.* A solution `c e_- b = 1_-` in `S_-` lies in `S_-^(9)`, and `(c W^(-1)) f_+ (W b) = c e_- b = 1_-`.
  This is route `f9-hadamard-fullness-from-swap-corner-fullness`.
- *Only if.* This direction is already on main as a chain: `hadamard-spectral-fullness-gives-f9-cohn-family`,
  `f9-cohn-family-descends-to-anti-central-summand`, `anti-central-cohn-family-gives-swap-corner-fullness`.
  Corollary 1.4 gives a one-step version over `F_9`: conjugate by `W`, then descend with Theorem 1.1 of
  `f9-hadamard-spectral-cohn-attempt-2026-09-12.md` and Theorem 2.1 of the Cohn reformulation. QED

**Remark 1.5 (supports).** `v` and `v'` are `F_9`-combinations of `eps_- [g]` with `g` in the dihedral group
`<h, u>` of order eight, so `supp W` lies in `<h, u> c`. A design for `f_+` with supports `S_b`, `S_c` is a
design for `e_-` with supports `c^(-1) <h,u> S_b` and `S_c <h,u> c`, and conversely.

**Remark 1.6 (what this does to the F_9 line).**
- Section 3.4 of the F_9 artifact kept one surviving idea: `h` in the support escapes the signed Thompson
  crossed product. The swap corner already has that escape: `q_[0] = [h] e_- [h]^(-1)` lies in
  `C(M_-, F_3) x| V` (`hadamard-unit-conjugates-swap-idempotent-to-cylinder`), and every swap design is a
  `q_[0]` design with supports translated by `h`. So the F_9 Hadamard target is not a separate problem, and no
  room is gained or lost by passing to it.
- The filters coincide. Part 5 of the half-idempotent claim (a rank model moving `z` on a subgroup containing
  `h`, `u` and the supports) is the swap corner's filter `anti-central-rank-models-kill-ternary-corner-witnesses`
  transported by `[c]`, with `(h, u) = [c](wd, d)[c]^(-1)`.
- w3-corner-crossed (4647e9e53f) shows that every Sylvester rank function on `C(M_-, F_3) x| V` kills
  `eps_- <~ q_[0]`. So any `f_+` design makes `eps_-` properly infinite in `S_-`, and it must defeat every rank
  function on every subalgebra containing its supports together with `H`.

## 2. Every state is forced on the finite subgroups of the signed Thompson group

Fix `Gamma` with `H <= Gamma <= G`, and put `S_Gamma = eps_- F_3[Gamma]`. A *state* is an additive map
`s : K_0(S_Gamma) -> R` that is nonnegative on classes of idempotent matrices and has `s([eps_-]) = 1`. For
`Gamma = G`, a state exists iff the swap corner fails (`twisted-leavitt-corner-fullness-equals-absence-of-k0-states`).

For a finite subgroup `K <= G` with `z in K` and an idempotent `p` in `M_n(eps_- F_3[K])`, put

```text
trl_K(p) = 2 dim_(F_3)(p F_3[K]^n) / |K|.
```

It is additive over orthogonal idempotents, invariant under algebraic equivalence and under conjugation by `G`,
unchanged when `K` is enlarged (`F_3[K']` is free over `F_3[K]`), and `trl_K(eps_-) = 1`. It is the lifted trace
`dim/|K|` of `lifted-trace-detects-finite-subgroup-projectives`, normalized at `eps_-`.

**Theorem 2.1.** Let `s` be a state on `(K_0(S_Gamma), [eps_-])`.
- (a) `s([1_U]) = lambda(U)` for every clopen `U` of `M_-`.
- (b) For every finite subgroup `K` of `H` containing `z`, and every idempotent matrix `p` over `eps_- F_3[K]`,
  `s([p]) = trl_K(p)`. The same holds for every `Gamma`-conjugate of such a `K`.

*Proof of (a).* This is the argument of Theorem 4.1 of `ternary-leavitt-char-three-rank-model-gate-2026-09-12.md`
with `s` in place of a rank; it uses only additivity and conjugation invariance.
- *Half split.* For a proper nonempty clopen `C`, `tau_(X \ C) = z tau_C` gives `Q_(X\C) = eps_- - Q_C`. Some `g`
  in `V` has `gC = X \ C`, and `[g] Q_C [g]^(-1) = Q_(X\C)`. So `s(Q_C) = 1/2`.
- *Atoms.* For a complete prefix code `c_1, ..., c_n`, put `a_eps = s([1_(A_eps)])` on the atoms
  `A_eps = {mu : mu(c_i) = eps_i}` (odd `eps`), and `a_eps = 0` for even `eps`. Then
  `sum_eps a_eps chi_S(eps) = 1 - 2 s(Q_(c_S))`, which is `1`, `-1`, `0` for `S` empty, full, or otherwise.
- *Inversion.* `a_eps = 2^(-n)(1 - chi_([n])(eps)) = 2^(1-n) = lambda(A_eps)` for odd `eps`. Clopens are finite
  disjoint unions of atoms. QED

Equivalently: the restriction of `s` to clopen indicators is a `V`-invariant finitely additive probability on
`M_-`, and `lambda` is the only one.

*Proof of (b).*
1. *Split form.* Write `k = e_k f_k` with `e_k in E`, `f_k in V`. The `f_k` form a finite subgroup `F` of `V`. Let
   `E_2` be generated by `z` and the translates `f e_k f^(-1)` (`f in F`). It is finite and `F`-invariant, and
   `K <= E_2 x| F`. Enlarging `K` changes neither side, so assume `K = E_2 x| F`.
2. *Levels.* For `m >= 0` let `E^(m)` be generated by `E_2` and the `F`-translates of `tau_beta` over words `beta` of
   length `m`. It is finite and `F`-invariant, and `K_m = E^(m) x| F` contains `K` for large `m`. With `O_m` the odd
   characters of `E^(m)`, `eps_- F_3[K_m] = C(O_m, F_3) x| F`. The indicator `1_chi` is `1_(U_chi)` for the clopen
   `U_chi = {mu : mu restricts to chi}`, and `lambda(U_chi) = 2 / |E^(m)|`.
3. *Orbit blocks.* An `F`-orbit `O` of `O_m` gives a central idempotent `1_O`, and
   `C(O, F_3) x| F ~= M_|O|(F_3[Stab])`.
   - *Free orbits.* The block is `M_|F|(F_3)` and each `1_chi` (`chi in O`) is a rank-one diagonal matrix unit. An
     idempotent matrix over the block of rank `r` has class `r [1_chi]`, so `s = r lambda(U_chi)` by (a). The block
     occurs `|F|` times in the regular module, so `dim p F_3[K_m]^n = r |F|` and `trl = 2 r |F| / (|E^(m)| |F|)`,
     the same value.
   - *Other orbits.* `p 1_O` is an idempotent below `1_O (x) I_n`, so both `s` and `trl` lie in
     `[0, n |O| lambda(U_chi)]` on it.
   - So `|s(p) - trl(p)| <= n lambda(N_m)`, where `N_m` is the union of the `U_chi` with nontrivial stabilizer.
4. *Non-free points are rare.* Fix `g != 1` in `F` and a cylinder `[alpha]` with `g[alpha] ∩ [alpha] = ∅`. For
   `m >= |alpha|` the elements `tau_beta tau_(g beta)`, over words `beta` of length `m` in `[alpha]`, have pairwise
   disjoint supports. So `(1 - g) E^(m)` has `F_2`-dimension at least `2^(m - |alpha|)`. Characters fixed by `g` are
   trivial on it, so they are a fraction at most `2^(-2^(m-|alpha|))` of all characters and at most twice that of the
   odd ones. Summing over `g in F`, `lambda(N_m) -> 0`.
5. *Conclusion.* Neither `s(p)` nor `trl(p)` depends on `m`, so `s(p) = trl(p)`. Both sides are conjugation
   invariant. QED

**Remark 2.2 (rank models).** An anti-central characteristic-three rank model of `Gamma` gives a state on
`(K_0(S_Gamma), [eps_-])` (Theorem 2.1 of `ternary-corner-state-sources-2026-09-12.md`). So such a model has the
lifted-trace law on every finite subgroup of `H`. This extends `anti-central-rank-models-see-haar-measure-on-signed-diagonal`
from clopen indicators to all idempotent matrices over finite subgroups of `H`, and from rank models to states.

**Remark 2.3 (where a state can see `h`).**
- *The semidihedral group.* `SD = <w, d, h>`. `hw = [[1,1],[-1,1]]`, `(hw)^2 = wd`, `(hw)^4 = z`, and `h` swaps
  `w` and `d` by conjugation. So `SD` has order sixteen with centre `<z>`, and `eps_- F_3[SD] = B_1 x B_2` with
  `B_1 ~= B_2 ~= M_2(F_3)`: the evaluation, and its twist by the sign character with kernel `<w, d>`.
- *Blocks.* `c_2 = -eps_-(1 + [wh] + [dh])` is the unit of `B_2`. It evaluates to `-(I + h^2) = 0`, and to
  `-(I - h^2) = I` in the twist. `c_1 = eps_- - c_2`, and `trl(c_1) = trl(c_2) = 1/2`.
- *Not conjugate into `H`.* Suppose `g a g^(-1) = hw` with `a = e f` in `H`. Then `a^4 = z`, so `f^4 = 1`, and in
  additive notation `a^4 = z` says the lamp sum `sum_(k<4) e(f^(-k) x)` equals `1` at every `x`. At a point with
  `f^2 x = x` that sum is `2 e(x) + 2 e(f^(-1) x) = 0`. So `f^2` has no fixed point, and `<f>` acts freely. Take a
  clopen fundamental domain `D_0` and `D = D_0 ∪ f^2 D_0`. Then `tau_D a tau_D = e tau_(D + fD) f = z a`. So `hw` would be conjugate to
  `-hw` in `G`. The characteristic polynomial of `[[1,1],[-1,1]]` over `F_3` is `x^2 + x - 1`, so both `(hw)^2 + hw - 1`
  and `(hw)^2 - hw - 1` would vanish in `R`, giving `hw = 0`.
- *So `t = s(c_1)` is free* as far as Theorem 2.1 is concerned: its restriction to `<w, d>` is forced, but the split
  between `B_1` and `B_2` is not. A state that sees `h` is a choice of `t`, together with the analogous block splits on
  other finite subgroups not conjugate into `H`, extending the forced values. Whether every state has `t = 1/2` is open.
  Section 3 shows `t` can always be normalized to `1/2`.

## 3. The transpose-inverse automorphism, and where it stops

Let `*` be the involution of `R` with `s_i^* = t_i`: an `F_3`-linear anti-automorphism with `(xy)^* = y^* x^*`.

**Proposition 3.1.** `alpha(g) = (g^*)^(-1)` is an automorphism of `G` with the following properties.
1. `alpha` fixes `H = E x| V` pointwise.
2. `alpha` fixes `z`, `w` and `d`, and `alpha(delta(g)) = delta(alpha(g))`, where `delta(g) = s0 g t0 + s1 g t1`.
3. On constants, `M(alpha(g)) = (M(g)^T)^(-1)`. So `alpha(h) = h^(-1) = zh` and `alpha(hw) = -hw`, and on
   `SD = <w, d, h>` it is the sign twist `g -> z^(chi(g)) g`, where `chi` has kernel `<w, d>`.
4. The linear extension `alpha_*` is a unital automorphism of `S_-` fixing `eps_-` and `e_-`. It exchanges the
   blocks `c_1` and `c_2` of Remark 2.3.

*Proof.*
- *Automorphism.* `((gk)^*)^(-1) = (k^* g^*)^(-1) = (g^*)^(-1)(k^*)^(-1)`.
- *Part 1.* `P_C^* = P_C`, so `tau_C^* = tau_C` and `alpha(tau_C) = tau_C^(-1) = tau_C`. A monomial unit
  `g = sum S[alpha_i] T[beta_i]` has `g^* = sum S[beta_i] T[alpha_i] = g^(-1)`, so `alpha(g) = g`.
- *Part 2.* `z^* = z`, `w^* = w = w^(-1)`, `d^* = d = d^(-1)`, and `delta(g)^* = delta(g^*)`.
- *Part 3.* `t_i g^* s_j = (t_j g s_i)^*`, and scalars are fixed. For the symmetric `h`, `alpha(h) = h^(-1)`.
  `hw = [[1,1],[-1,1]]` has transpose `[[1,-1],[1,1]]`, and `[[1,-1],[1,1]] [[1,1],[-1,1]] = [[2,0],[0,2]] = -I`,
  so `alpha(hw) = -hw`.
- *Part 4.* `alpha_*([h]) = [z][h] = -[h]` in `S_-`, `[w]` and `[d]` are fixed. So `rho_1 o alpha_* = rho_1 (x) chi = rho_2`
  on `eps_- F_3[SD]`, and `alpha_*(c_1) = c_2`. QED

**Corollary 3.2.** If `(K_0(S_-), [eps_-])` admits a state, it admits a state `s` with:
- `s o alpha_* = s`;
- `s o F_* = s / 2`, for the halving map `F` of `twisted-leavitt-k0-states-can-be-chosen-halving-invariant`;
- `s(c_1) = s(c_2) = 1/2`.
Every such state also satisfies Theorem 2.1.

*Proof.*
- *Commuting.* `alpha_*` fixes `e_-`, `[d]` and the matrix units `e_-, e_-[d], [d]e_-, 1_- - e_-`, and commutes with
  `delta_*`. So it commutes with `psi(x) = e_- delta_*(x)`, with `Phi = M_2(psi)`, and with the Morita identification
  `M_2(T) ~= S_-`. Hence `alpha_*` and `F_*` commute on `K_0(S_-)`.
- *Fixed point.* `s -> s o alpha_*` and `s -> 2 s o F_*` are commuting continuous affine self-maps of the compact
  convex state space (step 3 of the halving artifact). A commuting family of such maps has a common fixed point
  (Markov–Kakutani).
- *Values.* `s(c_1) = s(alpha_* c_1) = s(c_2)`, and `c_1 + c_2 = eps_-`. QED

**Remark 3.3 (what the normalization says).**
- The one free datum of Remark 2.3 is exchanged by an automorphism fixing all the forced data. So no argument that
  only uses `H`, `delta` and `e_-` can force `t`. Averaging makes it agree with the lifted trace.
- Other finite subgroups escape `H` as well. The unipotent constant `n = [[1,1],[0,1]]` has order three and
  `(n - 1)^2 = 0` in `R`. An element `a = e f` of order three in `H` has `f^3 = 1` and `f != 1` (if `f = 1` then `a = e`
  has order at most two). `R` acts on locally constant functions `X -> F_3` by `(s_i phi)(x) = [x_1 = i] phi(x_2 x_3 ...)`
  and `(t_i phi)(x) = phi(i x)`, so `a` acts as `phi -> (-1)^e . (phi o f^(-1))`. Take a clopen `U` with `U`, `fU`, `f^2 U`
  pairwise disjoint and `phi = 1_U`. Then `(a - 1)^2 phi = a^2 phi + a phi + phi` is nonzero on `U`. So `n` is not
  conjugate into `H`, `GL_2(F_3)` is not either, and its modular blocks carry further unforced splits.
- *The natural candidate.* The lifted trace is additive, conjugation invariant, positive, `alpha`-invariant, and
  compatible with Theorem 2.1 on the union of all finite-subgroup algebras of `G`. A state on `(K_0(S_-), [eps_-])`
  extending it would refute the swap corner. No extension is known, and no `K_0` relation between finite-subgroup
  projectives with different lifted traces is known either.

**Where it stops.**
- *Design side.* No candidate. The F_9 Hadamard line is the swap corner (Section 1), and every design must break the
  lifted trace between finite-subgroup projectives of `H`, through elements outside finite subgroups (Theorem 2.1).
- *State side.* A state, if one exists, can be taken `alpha`- and halving-invariant, equal to the lifted trace on the
  finite subgroups of `H` and on `SD`. Its existence is the negation of the corner and remains open.
