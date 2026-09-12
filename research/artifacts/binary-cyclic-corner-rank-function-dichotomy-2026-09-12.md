# The binary cyclic corner and Sylvester rank functions on simple group algebras

Lane `w4-binary-cyclic`, 2026-09-12. Supports `simple-group-rank-functions-are-augmentation-or-detecting`
and `binary-leavitt-units-carry-nonaugmentation-rank-function`, and records where the lift attempts on
`binary-cyclic-averaging-idempotent-is-full-on-leavitt-units` stop.

## 0. Setup and the permutation-module form

- `R = L_(F_2)(1,2)`, `G = R^x`, `A = F_2[G]`, `pi : A -> R` the evaluation.
- The ternary family: `s_1 = s0`, `s_2 = s1 s0`, `s_3 = s1 s1`, with `t_1, t_2, t_3` dual.
- `g = s_2 t_1 + s_3 t_2 + s_1 t_3`, of order three, and `e = 1 + [g] + [g²]`.
- The target (open): `c e b = 1` for some `b, c` in `A`.

**Proposition 0.1 (permutation-module form).** Let `K` be a field, `Γ` a group, `H <= Γ` finite with
`|H|` invertible in `K`, and `e_H = |H|^(-1) Σ_(h in H) [h]`. The following are equivalent.
1. `c e_H b = 1` for some `b, c` in `K[Γ]`.
2. The free module `K[Γ]` is a direct summand of the right permutation module `K[H\Γ]`.
3. `K[H\Γ]` has a unimodular element: some `m` and a module map `φ : K[H\Γ] -> K[Γ]` with `φ(m) = 1`.

*Proof.* `e_H [x]` depends only on the coset `Hx`, and over a set of coset representatives these
elements have disjoint supports. So `Hx -> e_H [x]` is an isomorphism of right modules
`K[H\Γ] ≅ e_H K[Γ]`. A module map `e_H K[Γ] -> K[Γ]` is left multiplication by its value at `e_H`,
which lies in `K[Γ] e_H`. So (3) reads `c e_H b = 1` with `m = e_H b` and `φ = c e_H ·`, which is (1).
From (1), `1 -> e_H b` is a split injection with retraction `c e_H ·`, which is (2), and (2) gives (3).
QED

A single coset is never unimodular: `c e_H [x] = 1` would give `c e_H = [x^(-1)]`, which is not
invariant under right multiplication by `H`.

**Proposition 0.2 (monotonicity).** If `H <= H'` are finite of invertible order, then
`e_(H') = e_(H') e_H`, so `c e_(H') b = 1` gives `(c e_(H')) e_H b = 1`. Conjugate subgroups give
conjugate idempotents. Every nontrivial `H` contains an element `h` of prime order, and fullness of
`e_H` gives fullness of `e_(⟨h⟩)`. So among averaging corners of finite subgroups containing `g`, the
order-three target is the weakest.

## 1. Sylvester rank functions on group algebras

A *Sylvester matrix rank function* on a ring `S` assigns to every rectangular matrix a number
`rk >= 0` with `rk(0) = 0`, `rk(1) = 1`, `rk(XY) <= min(rk X, rk Y)`, `rk(diag(X, Y)) = rk X + rk Y`
and `rk([[X, Z], [0, Y]]) >= rk X + rk Y`. Standard consequences used below:
- `rk(X + Y) <= rk X + rk Y`, since `X + Y = [1 1] diag(X, Y) [1 1]^T`;
- `rk(uXv) = rk X` for invertible `u, v`;
- an `n x m` matrix has rank at most `min(n, m)`, since `X = I_n X = X I_m`;
- a matrix all of whose entries have rank `0` has rank `0` (it is a sum of single-entry matrices);
- for an idempotent `f`, `rk(f) + rk(1 - f) = 1`: `>=` by subadditivity, and `<=` because
  `diag(f, 1 - f) = [f; 1 - f] [f, 1 - f]` factors through a `1 x 2` matrix.

On `K[Γ]` the *augmentation rank* is `rk_ε(X) = rank_K(ε(X))`, with `ε` the augmentation.

**Theorem 1.1.** Let `K` be a field, `Γ` a group, and `rk` a Sylvester matrix rank function on `K[Γ]`.
1. `N_rk = {x in Γ : rk(1 - [x]) = 0}` is a normal subgroup of `Γ`.
2. Matrices with the same image over `K[Γ/N_rk]` have the same rank, so `rk` descends to a Sylvester
   matrix rank function on `K[Γ/N_rk]`.
3. If `N_rk = Γ`, then `rk = rk_ε`.
4. If `Γ` is simple, then either `rk = rk_ε`, or `rk(1 - [x]) > 0` for every `x != 1`.

*Proof.*
1. `1 - [xy] = (1 - [x]) + [x](1 - [y])`, so `rk(1 - [xy]) <= rk(1 - [x]) + rk(1 - [y])`. Also
   `1 - [x^(-1)] = -[x^(-1)](1 - [x])` and `1 - [y x y^(-1)] = [y](1 - [x])[y^(-1)]` have rank at most,
   respectively exactly, `rk(1 - [x])`.
2. The kernel of `K[Γ] -> K[Γ/N_rk]` is spanned by the elements `[y](1 - [n])` with `y in Γ` and
   `n in N_rk`. Each has rank at most `rk(1 - [n]) = 0`, so every kernel element and every matrix with
   kernel entries has rank `0`. Then `|rk X - rk X'| <= rk(X - X') = 0` for two lifts. The axioms pass to
   the quotient, because products, block sums and triangular blocks of lifts are lifts.
3. Then `K[Γ/N_rk] = K` and the quotient map is `ε`. Every matrix over a field is equivalent to
   `diag(I_r, 0)`, so the only Sylvester matrix rank function on `K` is the normalized rank.
4. `N_rk` is `1` or `Γ`. QED

**Remark 1.2 (every rank function is a rank model).** `I_rk = {x : rk(x) = 0}` is a two-sided ideal,
and `rk` descends to `K[Γ]/I_rk` with `rk(x) > 0` for `x != 0`. So `Γ -> (K[Γ]/I_rk)^x` is a rank model
as in `full-averaging-idempotent-kills-its-element-in-rank-models`, and that theorem covers every
Sylvester rank function. Directly: `c e_H b = 1` gives `rk(e_H) >= 1`, so `rk(1 - e_H) = 0`, and
`1 - [h] = (1 - [h])(1 - e_H)` has rank `0` for each `h in H`.

**Corollary 1.3 (the binary targets force a unique rank function).** `R^x` is simple
(`binary-leavitt-unit-group-is-simple`). If `c e_H b = 1` in `F_2[R^x]` for one nontrivial finite
subgroup `H` of odd order, then `rk_ε` is the only Sylvester matrix rank function on `F_2[R^x]`.
Equivalently, a single Sylvester matrix rank function on `F_2[R^x]` other than `rk_ε` refutes every
averaging corner in `F_2[R^x]` at once. This includes `binary-cyclic-averaging-idempotent-is-full-on-leavitt-units`
and `thompson-v-order-three-averaging-idempotent-is-full`, because a witness in `F_2[V]` is a witness
in `F_2[R^x]`.

*Proof.* Remark 1.2 gives `rk(1 - [h]) = 0` for `h in H \ {1}`, and Theorem 1.1(4) gives `rk = rk_ε`. QED

**Corollary 1.4 (support filter).** If `c e_H b = 1` with `b, c` supported in a subgroup `Γ` containing
`H`, of any ambient group, then `H` lies in the normal subgroup `⋂_rk N_rk` of `Γ`. So `H` maps
trivially to every quotient `Q` of `Γ` whose group algebra has a rank function detecting the image of
`H`. Examples:
- finite `Q`, with normalized rank on the regular representation (`rk(1 - [q]) = 1 - 1/ord(q)`);
- sofic `Q`, through permutation matrices (a permutation moving a fraction `d` of the points has
  `rk(P - 1) >= d/2`, and Hamming defects bound rank defects);
- `K`-linear sofic `Q`.

On a simple group such as `R^x` the only proper quotient is trivial, so Corollary 1.3 is the whole
content there. On proper supports the filter is live.

## 2. Which rank functions can exist on F_2[R^x]

By Corollary 1.3 the binary averaging targets stand or fall with one question: does `F_2[R^x]` carry a
Sylvester matrix rank function other than `rk_ε`? By Theorem 1.1(4) any such function detects every
nontrivial element. The known sources are as follows.

**2.1 Through the evaluation: none.** `R` has no Sylvester rank function.
- Orthogonal idempotents add: `diag(f_1, f_2) = [f_1; f_2] [f_1, f_2]` and
  `[f_1, f_2] = (f_1 + f_2)[f_1, f_2]` give `rk f_1 + rk f_2 <= rk(f_1 + f_2)`.
- Equivalent idempotents `f = xy`, `f' = yx` (with `x = f x f'`, `y = f' y f`) have equal rank, since
  `y = y(xy)` and `f = xy`.
- `s0 t0` and `s1 t1` are orthogonal with sum `1`, and each is equivalent to `t_i s_i = 1`. So
  additivity would give `1 = 2`. No rank function on `A` factors through `pi`.

**2.2 Matrix algebras over division rings: none.** Let `φ : F_2[R^x] -> M_n(D)` be a ring
homomorphism, with `D` a division ring of characteristic two, and `rk(X) = rank_D(φ(X))/n`. Suppose
`rk != rk_ε`.
1. By Theorem 1.1(4), `φ` is injective on `R^x`.
2. Take `x` in `R^x` of order `2^k` with `2^k > 2n`, for example the permutation unit cycling the `2^k`
   cylinders of length `k`.
3. `(φ(x) - 1)^(2^k) = φ(x)^(2^k) - 1 = 0`, so `N = φ(x) - 1` is nilpotent. The kernels `ker N^i` form a
   chain of `D`-subspaces that increases strictly until it reaches `D^n`, so `N^n = 0`.
4. With `2^j` the least power of two `>= n`, `φ(x)^(2^j) = 1 + N^(2^j) = 1`. So `φ(x)` has order at most
   `2^j < 2n < 2^k`, a contradiction.

This covers every homomorphism to a division ring. Compare Lemma 1 of
`research/artifacts/el3-rank-model-extensions-2026-09-12.md`, where triangular models of bounded length
die through the nilpotency class.

**2.3 Monomial and Hamming models: none.** Rank models into monomial matrix groups are Hamming models
(`monomial-rank-models-are-hamming-models`). A detecting one would embed `R^x` into a metric
ultraproduct of symmetric groups, which is ruled out by `openai-leavitt-unit-nonsofic`.

**2.4 Linear soficity: sufficient, open.** Suppose `R^x` is linear sofic over `F_2`.
- Embedding it into the units of a rank ultraproduct `prod_ω M_(n_i)(F_2)/ker` and extending linearly
  gives a ring homomorphism.
- The ultraproduct rank pulls back to a Sylvester rank function with `rk(1 - [x]) >= κ > 0` for `x != 1`.

The same holds for a nontrivial rank model of `R^x` over any field of characteristic two, restricted
to `F_2[R^x]`. So if `rk_ε` is the only rank function, every characteristic-two rank model of `R^x`
is trivial. The converse is not available, because a Sylvester rank function need not be matricial.

**2.5 Characteristic zero, for contrast.** Over `C`, von Neumann dimension gives a detecting rank function
on `C[Γ]` for every group `Γ`. This is literature (Kaplansky's positivity of the trace), not re-read here,
and no node depends on it. The open claim asks for a characteristic-two substitute on one simple nonsofic
group.

**2.6 Twisted hosts (remarks, not claims).**
- *Ternary host.* Over `F_3`, `eps_- = (1 - [z])/2`. So a rank function on `F_3[G_3]` with
  `rk(1 - [z]) > 0` normalizes to a state on `S_-` and kills the ternary corner. `N_rk` is then a normal
  subgroup of `G_3` not containing `z`.
- *Quaternary host `(4, 2, 3)`.* Let `Ψ` be the `F_4`-linear extension of coefficientwise Frobenius on `L`.
  It swaps `eps_iota` and `eps_(iota²)`. Averaging `rk` with `rk o Ψ` gives `rk(eps_iota) > 0` whenever
  `rk(1 - [ω]) > 0`, because `1 - [ω] = (1 - [ω])(eps_iota + eps_(iota²))`.
- *A symmetry of the quaternary factor* (checked at the suggestion of `w4-hadamard-f3`).
  - *Definition.* Let `*` be the `F_4`-linear anti-automorphism of `L` with `s_i* = t_i`, and let
    `τ(x) = (x*)^(-1)` on `G`.
  - *Action.* `τ` inverts the scalars, and `g* = s_1 t_2 + s_2 t_3 + s_3 t_1 = g^(-1)`, so `τ(g) = g`.
    Since `δ* = δ`, `τ(δ) = δ^(-1)`.
  - *The composite.* `θ = Ψ ∘ τ`, extended `F_4`-linearly, is an involutive ring automorphism of
    `F_4[G]`. It fixes every scalar (`λ -> λ^(-2) = λ`), `g`, `δ = φ(δ^(-1))`, `eps_iota` and `e_1`.
  - *States.* `θ` preserves `A_iota` and the unit class, so any state on `(K_0(A_iota), [eps_iota])` can
    be averaged into a `θ`-invariant one. This only normalizes a state; it does not produce one.
  - *Binary level.* `θ` restricts to `τ` on `R^x`, which fixes `e`, so the solution set of `c e b = 1`
    is `τ`-stable. The anti-automorphism `[x] -> [x*]` fixes `e` as well, so solutions come in transpose
    pairs: `c e b = 1` gives `b^♯ e c^♯ = 1`.

## 3. Finite-subgroup classes and where the lift stops

**3.1 The nine-cylinder group.**
- Let `D(h) = Σ_i s_i h t_i`. `D` is an injective endomorphism of `G`, and `D(G)` commutes with every
  permutation unit `π` of the ternary family, since `π D(h) π^(-1) = Σ_i s_(π i) h t_(π i)`.
- `A_9 = ⟨g, D(g)⟩ ≅ C_3²` acts on the nine cylinders `s_i s_j` by `(i, j) -> (i + a, j + b)`. Every
  nontrivial element is fixed-point free.
- The permutation units realizing `GL_2(F_3)` on these cylinders normalize `A_9` and act transitively
  on its four subgroups `K` of order three.

`F_2[A_9]` is semisimple. Its primitive idempotents are `e_(A_9)` and, for each `K`, `f_K = e_K − e_(A_9)`,
because the two characters with kernel `K` are Galois conjugate. So `1 = e_(A_9) + Σ_K f_K` and
`e = e_(K_1) = e_(A_9) + f_(K_1)`. The `f_K` are conjugate in `G`, so

    [1 − e] = 3 [e − e_(A_9)]    in K_0(F_2[G]).

**3.2 The halving map.**
- `ψ(x) = e D(x)` is a unital ring homomorphism `F_2[G] -> e F_2[G] e`, because `e` commutes with `D(G)`.
- Followed by the corner inclusion, it acts on `K_0` by `[e_H] -> [e D(e_H)]`.
- For `C_3^k = ⟨g, D(g), ..., D^(k−1)(g)⟩`, which acts freely on the `3^k` cylinders of length `k`, it
  sends `[e_(C_3^k)]` to `[e_(C_3^(k+1))]`.
- Applying it to 3.1, the differences `d_k = [e_(C_3^k)] − [e_(C_3^(k+1))]` satisfy `d_k = 3 d_(k+1)`,
  and `[1] = [e_(C_3^k)] + ((3^k − 1)/2) d_(k−1)`.

**3.3 Consistency.** Every relation above holds for the rational measure `μ(e_(C_3^k)) = 3^(−k)`, which is
what the lifted trace gives (`lifted-trace-detects-finite-subgroup-projectives`). A witness needs
`[e] = [1] + [X]` with lifted trace `t(X) = −2/3`, so `X` is never a finite-subgroup projective. This is
census item 4 of `research/artifacts/quaternary-twisted-corner-census-2026-09-12.md`, seen at the binary
level. Lane `w4-kap-join` reports a sharper filter on candidate defects: laminar combinations of
finite-subgroup idempotents with sofic intersection amalgam have strictly positive lifted trace
(`sofic-amalgam-finite-subgroup-idempotent-traces-are-strict`). So the complement `1 − (e b)(c e)`,
whose class is `0`, cannot be such a combination.

**3.4 Where the lift stops.**
- *Normal form.* Replace `b` by `e b` and `c` by `c e`; the equation becomes `w e z = 1`. Here `e z` is a
  unimodular vector of `F_2[⟨g⟩\G]` and `w e ·` is its retraction. Neither `w` nor `z` can be a single
  group element (Proposition 0.1).
- *Image level.* `b = s_1 + s_2 + s_3` and `c = t_1 + t_2 + t_3` satisfy `π(e) = bc`. In the ternary
  picture `R ≅ M_3(R)` this is the all-ones matrix, and `π(g) b = b`. The kernel of `π` is where every
  correction lives.
- *Support.* By Corollary 1.4, `g` dies in every finite, sofic or linear sofic quotient of
  `Γ = ⟨g, supp w, supp z⟩`. So a candidate built inside a residually finite or virtually free subgroup
  containing `g` is excluded from the start. Compare `leavitt-rank-three-lift-has-no-one-sided-inverse`,
  where the support-three lifts die for the same kind of reason.
- *Open.* No candidate `w, z` is known whose support subgroup passes this filter. The kill direction is
  exactly `binary-leavitt-units-carry-nonaugmentation-rank-function`, and no characteristic-two rank
  function other than the augmentation is known on any simple nonsofic group algebra.
