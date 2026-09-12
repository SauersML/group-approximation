# The binary cyclic corner and states on its complement corner

Lane `w5-binary-upg`, 2026-09-12. Supports `binary-cyclic-corner-full-iff-complement-corner-has-no-state`.
Later sections support `binary-complement-corner-rank-functions-pull-back-to-units` and the open
`binary-complement-corner-states-give-sylvester-rank-functions`.

This is the characteristic-two counterpart of family UPG (the ternary state upgrade). Section 2 proves a
binary Theorem E: the binary cyclic corner is full iff the complement corner has no `K_0` state.

## 0. Setup

- `R = L_(F_2)(1,2)`, `G = R^x`, `A = F_2[G]`, `pi : A -> R` the evaluation.
- The ternary family: `s_1 = s0`, `s_2 = s1 s0`, `s_3 = s1 s1`, with `t_1, t_2, t_3` dual. So
  `t_i s_j = delta_ij` and `s_1 t_1 + s_2 t_2 + s_3 t_3 = 1`.
- `g = s_2 t_1 + s_3 t_2 + s_1 t_3`, of order three. `e = 1 + [g] + [g²]` is an idempotent, since
  `1/3 = 1` in `F_2`. Put `f = 1 - e`.
- `D(h) = s_1 h t_1 + s_2 h t_2 + s_3 h t_3` is an injective unital endomorphism of `G`. It commutes with
  every permutation unit of the ternary family, in particular with `g`. Extend it `F_2`-linearly to a
  unital algebra endomorphism of `A`.
- `A_9 = ⟨g, D(g)⟩ ≅ C_3²` translates the nine cylinders `s_i s_j`: `g` moves the first letter, `D(g)`
  the second. The nine-cylinder permutation units `π_M` (`M` in `GL_2(F_3)`) satisfy
  `π_M [τ_a] π_M^(-1) = [τ_(Ma)]`, so they normalize `A_9` and act transitively on its four subgroups
  of order three (`w4-binary-cyclic`, Section 3.1 of
  `research/artifacts/binary-cyclic-corner-rank-function-dichotomy-2026-09-12.md`).
- `F_2[A_9]` is commutative and semisimple. For each subgroup `K` of order three, `f_K = e_K - e_(A_9)`
  is the primitive idempotent of the two Galois-conjugate characters with kernel `K`. So
  `1 = e_(A_9) + Σ_K f_K`. Write `K_1 = ⟨g⟩`, `K_2 = ⟨D(g)⟩`, and `K_3`, `K_4` for the diagonals. Then
  `e = e_(K_1) = e_(A_9) + f_(K_1)` and `f = f_(K_2) + f_(K_3) + f_(K_4)`.
- `T = f A f` is a unital ring with unit `f`, the complement corner.
- For a unital ring `S`: `V(S)` is the monoid of isomorphism classes of finitely generated projective
  right `S`-modules, and `K_0(S)` is its Grothendieck group, preordered by the image of `V(S)`, with
  order unit `[S]`. A state is an additive `s : K_0(S) -> ℝ`, nonnegative on the cone, with
  `s([S]) = 1`.
- In `V(A)`: `u = [A]`, `p = [eA]`, `v = [fA]`, so `u = p + v`.

## 1. Two halving homomorphisms and the tower

**Lemma 1.1.** `ψ(x) = e D(x)` is a unital ring homomorphism `A -> eAe`, and `ψ'(x) = f D(x)` is a
unital ring homomorphism `A -> T`.

*Proof.* `D(x)` commutes with `e` and `f`, because `[D(h)]` commutes with `[g]`. So
`e D(x) e D(y) = e D(xy)`, `ψ(1) = e`, and likewise for `f`. QED

Applying `ψ` entrywise to idempotent matrices, and then including `eAe` in `A`, gives a monoid
homomorphism `F : V(A) -> V(A)` with `F(u) = p`. Likewise `ψ'` gives `F' : V(A) -> V(T)` with
`F'(u) = [T]`. The corner inclusion gives `ι_T : V(T) -> V(A)` with `ι_T([T]) = v`.

Put `C_3^k = ⟨g, D(g), ..., D^(k-1)(g)⟩`. It translates the `3^k` cylinders of length `k` freely. Put
`E_k = e_(C_3^k)` (`E_0 = 1`), `p_k = [E_k A]` and `d_k = [(E_k - E_(k+1)) A]`. So `p_1 = p` and `d_0 = v`.

**Lemma 1.2 (tower).**
- (a) `ψ(E_k) = E_(k+1)`. Hence `F(p_k) = p_(k+1)` and `F(d_k) = d_(k+1)`.
- (b) `v = 3 d_1` in `V(A)`. Hence `d_k = 3 d_(k+1)` and `v = 3^k d_k` for every `k`.
- (c) `p = p_(k+1) + ((3^k - 1)/2) d_k` for every `k >= 1`. So `p >= N d_k` whenever `N <= (3^k - 1)/2`.
- (d) `ψ'(f) = f_(K_3) + f_(K_4)`, and `ψ'(1 - [g]) = (f_(K_3) + f_(K_4))(1 - [D(g)])`.

*Proof.*
- (a) `e D(E_k) = e_(⟨g⟩) e_(D(C_3^k))`. The group `D(C_3^k) = ⟨D(g), ..., D^k(g)⟩` commutes with `g`
  and meets `⟨g⟩` trivially (free translations of the cylinders of length `k+1`), so the product is
  `E_(k+1)`. The differences follow by linearity.
- (b) `f` is the orthogonal sum of `f_(K_2)`, `f_(K_3)`, `f_(K_4)`. Conjugation by `π_M` carries `f_K` to
  `f_(MK)`, and conjugate idempotents have isomorphic right ideals. So `v = 3[f_(K_1) A]`, and
  `f_(K_1) = e - e_(A_9) = E_1 - E_2`. Apply `F^k` for the rest.
- (c) `e = E_(k+1) + Σ_(l=1..k) (E_l - E_(l+1))` is an orthogonal decomposition, because the `E_l`
  are nested commuting idempotents. By (b), `d_l = 3^(k-l) d_k`, and `Σ_(l=1..k) 3^(k-l) = (3^k - 1)/2`.
- (d) `D(e) = e_(K_2)`, and `f e_(K_2) = f_(K_2)` in `F_2[A_9]`. So `ψ'(f) = f - f_(K_2)`. The characters
  with kernel `K_2` are trivial on `D(g)`, so `f_(K_2)[D(g)] = f_(K_2)`. QED

**Lemma 1.3 (fullness as a class inequality).** `c e b = 1` is solvable in `A` iff `u <= p` in `V(A)`,
that is, iff `A` is isomorphic to a direct summand of `eA`.

*Proof.* If `c e b = 1`, then `x -> e b x` is a split injection `A -> eA` with retraction `y -> c y`.
Conversely, let `A -> eA` be split, with `1 -> m` and retraction `φ`. Put `c = φ(e)`. Then
`c = φ(e e) = c e`, and `1 = φ(m) = φ(e m) = c m = c e m`. Take `b = m`. QED

## 2. Theorem B: the binary Theorem E

**Theorem B.** The following are equivalent.
1. `c e b = 1` is solvable in `A = F_2[G]`: the binary cyclic corner is full.
2. `u <= p` in `V(A)`.
3. `[f] <= 0` in `K_0(A)`.
4. Every state on `(K_0(A), [1])` vanishes on `[f]`, equivalently gives `[e]` the value `1`.
5. `(K_0(T), [T])` admits no state.
6. `T` fails the rank condition: `T ⊕ Q ⊕ T^N ≅ T^N` for some `N >= 0` and some projective `Q`.

When they hold, `F_2[G]` is not directly finite and `G` is not surjunctive
(`binary-cyclic-corner-fullness-gives-kaplansky-failure`).

The proof uses only `g`, `D`, the units `π_M`, and `D(H) ⊆ H`. So Theorem B holds verbatim for
`A = F_2[H]` for every subgroup `H <= G` that contains `g` and the `π_M` and is `D`-stable.

*Proof.*
- **1 <=> 2.** Lemma 1.3.
- **2 => 3.** `u + x = p` gives `p + v + x = p`, so `v + x = 0` in `K_0(A)`.
- **3 => 4.** For a state `s`, `s(v) >= 0`, and `s(v) = -s(x) <= 0`.
- **4 => 5.** Suppose `s_T` is a state on `(K_0(T), [T])`. Since `ψ'` is unital, `s = s_T ∘ K_0(ψ')` is a
  state on `(K_0(A), u)`. By Lemma 1.2(d), `s(v) = s_T([f_(K_3) T]) + s_T([f_(K_4) T])`.
  - The idempotents `f_(K_2)`, `f_(K_3)`, `f_(K_4)` are orthogonal with sum `f`.
  - They are pairwise equivalent inside `T`: with `x = π_M f_K` and `y = f_K π_M^(-1)`, we have
    `x` in `f_(MK) A f_K ⊆ T`, `y` in `f_K A f_(MK) ⊆ T`, `xy = f_(MK)` and `yx = f_K`.
  - So each has `s_T`-value `1/3`, and `s(v) = 2/3 != 0`, contradicting 4.
- **5 <=> 6.** State criterion for a unital ring with order unit `[T]`: a state exists iff `[T]` is not
  `<= 0` (census Theorem A(b), a Hahn–Banach argument valid for every unital ring;
  `research/artifacts/ternary-anti-central-invariant-census-2026-09-12.md`). And `[T] <= 0` in `K_0(T)`
  iff `T ⊕ Q ⊕ T^N ≅ T^N` for some `N` and `Q`.
- **6 => 2.**
  - In `V(T)`: `(N+1)[T] + [Q] = N[T]`. Push along `ι_T`: `N v + v + q = N v` in `V(A)`. Adding the
    relation to itself repeatedly gives `N v + j v + j q = N v` for every `j >= 1`.
  - Apply `F^k`. By Lemma 1.2(a),(b), `N d_k + j d_k + j F^k(q) = N d_k`. With `j = 3^k`,
    `N d_k + v + x = N d_k`, where `x = 3^k F^k(q)`.
  - Choose `k` with `(3^k - 1)/2 >= N`. By Lemma 1.2(c), `p = N d_k + c` for some class `c`.
  - Then `p + v + x = (N d_k + v + x) + c = N d_k + c = p`. So `u + x = p`, and `u <= p`. QED

**Remark 2.1 (what is new compared with Theorem E).**
- **Theorem E needs a twist.** It needs `m | q - 1`, so that the visible factor is a matrix algebra over
  its cyclic corner and the augmentation vanishes on the factor.
- **Over `F_2` there is no twist.** No scalar character removes the augmentation: `(K_0(A), u)` always
  has the augmentation state, which gives `[e]` the value `1` and obstructs nothing.
- **What Theorem B does instead.** It passes to the complement corner `T`, whose unit has augmentation
  zero. It replaces the matrix structure by the halving tower of Lemma 1.2. And it uses the second
  halving homomorphism `ψ'`, which turns every state of `T` into a state of `A` that sees `[f]`.

**Remark 2.2 (calibration).** Let `L_3 = ∪_k Sym(3^k)` be the group of finitary permutation units of the
ternary cylinders. It contains `g` and the `π_M`, and it is `D`-stable, so Theorem B applies to
`F_2[L_3]`. The normalized regular rank of the finite stages is compatible along the inclusions. It gives
`T` a state with value `[f] -> 1` after normalizing by `2/3`. So statement 5 fails, and so does 1, as it
must, because group algebras of locally finite groups are directly finite. Only a nonsofic `D`-stable host
can carry a solution.

## 3. Rank functions on the complement corner

**Proposition C.** Let `G = R^x` and `A = F_2[G]`.
- (a) Let `N` be a Sylvester matrix rank function on `T` with `N(f) = 1`. Then `rk_N = N ∘ ψ'` is a Sylvester
  matrix rank function on `A` with `rk_N(1 - [g]) = 2/3`. So `rk_N != rk_ε`, and `rk_N` detects every
  nontrivial group element (`simple-group-rank-functions-are-augmentation-or-detecting`).
- (b) Conversely, if `rk` is a Sylvester matrix rank function on `A` other than `rk_ε`, then `rk(f) > 0`, and
  `N(X) = rk(X)/rk(f)`, for matrices `X` over `T`, is a Sylvester matrix rank function on `T` with `N(f) = 1`.

So `F_2[R^x]` carries a rank function other than the augmentation rank iff `T` carries a normalized
Sylvester matrix rank function.

*Proof.*
- (a) Rank functions pull back along unital ring homomorphisms. By Lemma 1.2(d),
  `ψ'(1 - [g]) = (f_(K_3) + f_(K_4))(1 - [D(g)])`. The characters with kernel `K_3` or `K_4` are nontrivial
  on `D(g)`. So this element is invertible in the commutative algebra `(f_(K_3) + f_(K_4)) F_2[A_9]`, which
  is `F_4 × F_4`, and its `N`-rank equals `N(f_(K_3) + f_(K_4))`. For a Sylvester rank function, orthogonal
  idempotents add and equivalent idempotents have equal rank (`w4-binary-cyclic`, Section 2.1). The
  `f_K` inside `f` are equivalent in `T` (proof of Theorem B, 4 => 5), so each has rank `1/3`, which gives
  `2/3`.
- (b) `(1 - [g]) f = 1 - [g]`, because `[g] e = e`. If `rk(f) = 0`, then `rk(1 - [g]) = 0`, so `g` lies in the
  normal subgroup `N_rk`. `G` is simple (`binary-leavitt-unit-group-is-simple`), so `N_rk = G` and
  `rk = rk_ε`. The Sylvester axioms for `N` are inherited, because matrices over `T` are matrices over `A`.
  QED

**Corollary C.1 (the binary chain).** Consider three statements.
- (NR) Every Sylvester matrix rank function on `F_2[R^x]` is `rk_ε`. Equivalently, every one kills the
  two-root defect `D` (`leavitt-rank-functions-killing-two-root-defect-are-augmentation`). This is
  `sylvester-rank-functions-on-leavitt-units-kill-two-root-defect`.
- (NR_T) `T` carries no Sylvester matrix rank function with `N(f) = 1`.
- (NS_T) `(K_0(T), [T])` admits no state.

Here is how they relate.
- **(NR) <=> (NR_T).** Proposition C.
- **Fullness <=> (NS_T).** Theorem B.
- **(NS_T) => (NR_T).** A normalized rank function restricts to a state on idempotent classes.
- **The missing step, U1_T.** (NR_T) => (NS_T), that is, every state on `(K_0(T), [T])` is realized by
  some normalized Sylvester matrix rank function on `T`. This is
  `binary-complement-corner-states-give-sylvester-rank-functions`.
- **With U1_T.** The Sylvester two-root gate gives fullness, hence Kaplansky failure and a Gottschalk
  counterexample (route `binary-counterexample-from-rank-kill-and-state-realization`). All four statements
  (fullness, (NS_T), (NR_T), (NR)) then coincide.

**Remark C.2 (comparison with the ternary chain).**
- **Ternary.** Family UPG needs the same step for the central factor `S_- = eps_- F_3[G_3]`
  (`ternary-anti-central-states-give-sylvester-rank-functions`), and a further step to pass from rank
  functions to the characteristic-three gate.
- **Binary.**
  - No character splits the augmentation off, so the corner `T` is not central.
  - Theorem B and Proposition C replace the central splitting with the halving homomorphism `ψ'`.
  - In return, the binary gate needs no extra step: (NR) is already the Sylvester form of the gate.
- **One question behind both.** For a unital ring `S` satisfying the rank condition, is some state on
  `(K_0(S), [S])` realized by a Sylvester matrix rank function? The general answer was not checked against
  the literature here; lane `w4-upg-kill` holds that search.

## 4. Where it stops

**Proposition 4.1 (states on `T` can be normalized).** Restricted to `T`, `ψ'` is a ring endomorphism
`x -> f D(x)` of `T`, with `ψ'(f) = f_(K_3) + f_(K_4)`. For a state `s_T`, the functional
`(3/2) s_T ∘ K_0(ψ'|_T)` is again a state. The state space is compact and convex, and this map is affine
and continuous, so Markov–Kakutani gives a state with `s_T ∘ K_0(ψ'|_T) = (2/3) s_T` whenever any state
exists. This normalizes a state but does not produce one. Compare `twisted-leavitt-k0-states-can-be-chosen-halving-invariant`.

**Corollary 4.2 (division rings give nothing).** `T` admits no unital ring homomorphism into `M_n(D)` for a
division ring `D` of characteristic two.
- *Proof.* Composing with `ψ'` gives a unital homomorphism `A -> M_n(D)` whose normalized rank is not
  `rk_ε`, by Proposition C(a). That contradicts Section 2.2 of the binary cyclic artifact: an element of
  `R^x` of order `2^k > 2n` would map to a unipotent matrix of smaller order. QED
- *Consequence.* So U1_T cannot come from Cohn–Malcolmson localizations into division rings. A rank function
  on `T` must be non-division and non-matricial of bounded size, like the rank-ultraproduct models behind
  linear soficity.

**The additive shadow.** On `K_0(T)` the 2-adic lifted trace (`lifted-trace-detects-finite-subgroup-projectives`),
normalized by `3/2`, gives `[T] -> 1`, `[f_K T] -> 1/3` and `d_k -> 3^(-k)`. It satisfies every relation of
Lemma 1.2 and the invariance of Proposition 4.1. It is additive but not positive, so it is not a state.
The criterion of `anti-central-state-exists-iff-lifted-trace-relatively-positive` has an obvious binary
analogue, which was not worked out here.

**Open, in order of cost.**
1. U1_T for `T`, and its ternary twin for `S_-`. The literature search belongs to `w4-upg-kill`.
2. The Sylvester gate (NR), where the binary gate lanes work.
3. A direct state on `T`. By Theorem B it refutes the corner, and by Proposition C, given U1_T, it gives a
   detecting rank function on `F_2[R^x]`.
