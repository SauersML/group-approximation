# Weakly finite representations of Thompson's V and the order-three averaging corner

Lane `swarm-thompson-v-order-three-averagi`, 2026-09-16. Supports:
- `thompson-v-has-no-weakly-finite-char-two-representation` (OPEN, new);
- routes `thompson-v-averaging-fullness-from-no-weakly-finite-rep`,
  `thompson-v-no-weakly-finite-rep-from-averaging-fullness`, `thompson-v-rank-gate-from-no-weakly-finite-rep`
  and `binary-cyclic-corner-fullness-ascends-from-thompson-v`.

The result is a reduction, not a solution. The target `thompson-v-order-three-averaging-idempotent-is-full`
is shown equivalent to a representation statement about `V` alone, the argument of Theorem W of [WF] is
transferred from the Leavitt units to `V`, and a support filter is derived from a computer-assisted theorem
of [DHJ].

## 0. Setup, conventions and inputs

- `Ω` is the Cantor space of infinite binary sequences. An element of `V` with prefix codes
  `(a_1, ..., a_q) -> (b_1, ..., b_q)` maps `a_i w -> b_i w`. Maps compose right to left.
- `R = L_(F_2)(1,2)`, `π : F_2[V] -> R` the evaluation, with `x -> Σ S[b_i] T[a_i]` ([TGT] Section 1). On the
  module `M` with basis `δ_w` (`s_i δ_w = δ_(iw)`, [TGT] Section 3), `S[b] T[a]` maps `δ_(aw) -> δ_(bw)`. So
  the embedding turns right-to-left composition into the ring product, and it is injective because `M` is
  faithful for `V`. `V <= R^x` is also `leavitt-cylinder-swaps-generate-thompson-in-el`.
- The target element: `h = (00, 01, 1) -> (01, 1, 00)`, `e_h = 1 + h + h²`.
- The ternary family of [CS] Section 0: `s_1 = s0`, `s_2 = s1 s0`, `s_3 = s1 s1`. Its permutation unit
  `g = s_2 t_1 + s_3 t_2 + s_1 t_3` is the image of `(0, 10, 11) -> (10, 11, 0)`, so `g ∈ V`.
- `D(x) = Σ s_i x t_i`, `A_9 = ⟨g, D(g)⟩ ≅ C_3²`, the nine-cylinder permutation units `π_M`
  (`M ∈ GL_2(F_3)`), and the idempotents `f_K`, as in [CS] Section 0.
- `A_V = F_2[V]`, `e = e_g = 1 + g + g²`, `f = 1 - e`, `T_V = f A_V f`, `ψ'(x) = f D(x)`.
- A ring `W` is **directly finite** if `xy = 1` implies `yx = 1` in `W`. It is **weakly finite** if the same
  holds for square matrices of every size. `W` has characteristic two if `2·1 = 0` (the zero ring included).

Inputs, at the status recorded on their nodes:
- [CS] `research/artifacts/binary-cyclic-corner-complement-states-2026-09-12.md`: Lemma 1.1, Lemma 1.2,
  Theorem B, and the scope sentence after its statement: "The proof uses only `g`, `D`, the units `π_M`,
  and `D(H) ⊆ H`. So Theorem B holds verbatim for `A = F_2[H]` for every subgroup `H <= G` that contains
  `g` and the `π_M` and is `D`-stable." (`binary-cyclic-corner-full-iff-complement-corner-has-no-state`).
- [WF] `research/artifacts/binary-weakly-finite-representations-2026-09-12.md`: Theorem W, Lemmas W.1, W.2.
- Theorem C: `rank-condition-rings-have-weakly-finite-images`. A unital ring has the rank condition iff it
  has a nonzero weakly finite image.
- Simplicity of `V`: `thompson-v-finitely-presented-infinite-simple`.
- `sylvester-rank-function-quotients-are-weakly-finite`.
- `finite-subgroups-of-thompson-v-permute-a-canonical-partition`.
- [TGT] `research/artifacts/thompson-v-linear-counterexample-targets-2026-09-12.md`.
- [GK3] `research/artifacts/gk3-binary-fullness-2026-09-14.md`, Section 4 (`V` is a Theorem B host).
- [DHJ] K. Dykema, T. Heister, K. Juschenko, *Finitely presented groups related to Kaplansky's Direct
  Finiteness Conjecture*, arXiv:1112.1790 (v4). Proposition 4.21 and Remark 4.13 were read in the ar5iv
  HTML on 2026-09-16. The proof of Proposition 4.21 is a computer enumeration that was not re-run here.
- [EXP] `experiments/thompson-v-order-three-averaging-idempot-swarm-2026-09-16/verify_host_and_blocks.py`
  and its `output.txt`. These are finite checks C1–C5 of the combinatorial identities below. The proofs do
  not depend on them.

## 1. The host and the conjugator

**Lemma 1.1.**
1. `h³ = g³ = 1`, and `k = (00, 01, 1) -> (0, 10, 11)` satisfies `k h k^(-1) = g` in `V`, hence in `R^x`.
2. So `e_h = k^(-1) e_g k`, and `c e_h b = 1` iff `(c k^(-1)) e_g (k b) = 1`.
3. `V` is a Theorem B host: it contains `g` and every `π_M`, and `D(V) ⊆ V`.

*Proof.*
1. Trace `k^(-1)`, then `h`, then `k`:
   - `0w -> 00w -> 01w -> 10w`;
   - `10w -> 01w -> 1w -> 11w`;
   - `11w -> 1w -> 00w -> 0w`.

   This is `g`. The order of `h` is visible on its code. [EXP] C1 and C2 check both statements on all
   words of length 12.
2. `k^(-1) g^m k = h^m`. Multiply the equation on the left by `k^(-1)` and on the right by `k`, or back.
3. `g` is a prefix replacement. `π_M` permutes the nine cylinders `s_i s_j` by prefix replacement. If
   `x ∈ V` has codes `(a_i) -> (b_i)`, then `D(x)` maps `p a_i w -> p b_i w` for `p ∈ {0, 10, 11}`, so
   `D(x) ∈ V`. This is [GK3] Section 4. QED

`k` differs from the conjugator used in `brin-thompson-2v-averaging-fullness-ascends-from-v`, which conjugates
`g` to `h^(-1)`. Both are correct, since `e_h = e_(h^(-1))`.

## 2. Theorem W for V

**Theorem W_V.** The following are equivalent.
- (a) `c e_h b = 1` is solvable in `F_2[V]` (the target).
- (a') `c e_g b = 1` is solvable in `F_2[V]`.
- (b) `T_V` has no nonzero weakly finite homomorphic image.
- (c) Every unital ring homomorphism `φ : F_2[V] -> W` into a weakly finite ring has `φ(h) = 1`
  (equivalently `φ(g) = 1`).
- (c_DF) The same as (c), for every directly finite `W`.
- (d) Every group homomorphism from `V` into the unit group of a weakly finite ring of characteristic two
  is trivial.
- (d_DF) The same as (d), for every directly finite ring of characteristic two.

*Proof.*
- **(a) <=> (a').** Lemma 1.1(2). In (c), `φ(h) = φ(k)^(-1) φ(g) φ(k)`, so the two forms are equivalent.
- **(a') => (c_DF).** Let `φ` be unital with `W` directly finite. Put `X = φ(c e)` and `Y = φ(e b)`.
  - `XY = φ(c e b) = 1`, so `YX = 1`.
  - So `φ(e)` has the right inverse `φ(bce)` and the left inverse `φ(ebc)`, and an invertible idempotent is
    `1`.
  - Hence `u + u² = 0` for `u = φ(g)`. Since `2 = 0` in `W`, `u² = u`, and `u` is a unit, so `u = 1`.

  This is [WF] (a) => (c) at matrix size one.
- **(c_DF) => (c).** Weakly finite rings are directly finite.
- **(c) => (b).** Let `q : T_V -> W` be unital, with `W != 0` weakly finite. Lemma W.2 of [WF] gives
  `φ = q ∘ ψ'` with `φ(g) != 1`. Its proof uses:
  - `ψ'` is unital ([CS] Lemma 1.1);
  - `f (1 - D(g)) = (f_(K_3) + f_(K_4)) u` with `u` a unit of the block algebra ([CS] Lemma 1.2(d); [EXP] C5
    exhibits the inverse);
  - the equivalence of `f_(K_2)`, `f_(K_3)`, `f_(K_4)` inside `T_V` through `x = π_M f_(K_3)` and
    `y = f_(K_3) π_M^(-1)`, with `M` fixing `K_1`.

  All of these elements lie in `F_2[V]` by Lemma 1.1(3). So Lemma W.2 holds verbatim over `V`, and `φ`
  contradicts (c).
- **(b) => (a').**
  - By Theorem C, `T_V` fails the rank condition.
  - By Theorem B (6 => 1), applied to the host `V` (Lemma 1.1(3) and the scope sentence of [CS]),
    `c e b = 1` is solvable in `F_2[V]`.
- **(c_DF) => (d_DF).** Let `ρ : V -> W^x` with `W` directly finite of characteristic two. Then `ρ` extends to
  a unital `F_2`-algebra homomorphism `φ : F_2[V] -> W`, and `φ(g) = 1` by (c_DF). So `ker ρ` is a normal
  subgroup containing `g != 1`, and `V` is simple. So `ρ` is trivial.
- **(d_DF) => (d).** Weakly finite rings are directly finite.
- **(d) => (c).** A unital `φ : F_2[V] -> W` gives `2·1_W = φ(2) = 0`, and `φ|_V` is a homomorphism into
  `W^x`. By (d) it is trivial, so `φ(g) = 1`.

These implications close the cycle (a) => (a') => (c_DF) => (c) => (b) => (a') => (a), together with
(c_DF) => (d_DF) => (d) => (c). QED

**What each direction uses.**
- (d) => (a) (the route `thompson-v-averaging-fullness-from-no-weakly-finite-rep`) passes through
  (d) => (c) => (b) => (a') => (a). It uses Theorem C, Theorem B at host `V` and Lemma W.2 at host `V`, but
  not simplicity.
- (a) => (d) (the route `thompson-v-no-weakly-finite-rep-from-averaging-fullness`) passes through
  (a) => (c_DF) => (d_DF) => (d). It uses only matrix-size-one direct finiteness and simplicity of `V`.

**Remark 2.1 (direct versus weak finiteness).** For `V`, "no nontrivial weakly finite representation in
characteristic two" and "no nontrivial directly finite representation in characteristic two" are
equivalent. The chain (d) => (a) => (d_DF) runs through the averaging corner and Theorem B, not through a
general ring-theoretic fact. For `R^x`, the spot-check recorded on
`binary-corner-weakly-finite-unit-representation-proof` notes that (a) => (c) needs only size-one direct
finiteness. The same chain gives the equivalence there.

## 3. Consequences

**Corollary 3.1 (uniformity over odd finite subgroups).**
1. Let `K <= V` be a nontrivial finite subgroup of odd order, and `e_K = Σ_(x ∈ K) x`, an idempotent of
   `F_2[V]`. If `e_K` is full, meaning `c e_K b = 1` for some `b, c`, then the target holds.
2. If the target holds, `e_x` is full in `F_2[V]` for every `x ∈ V` of order three.

So all order-three averaging idempotents of `V` are full, or none is. This covers both cycle types, with and
without fixed pieces, and needs no conjugacy classification.

*Proof.*
1. Let `φ` be unital into a directly finite `W`.
   - As in (a') => (c_DF), `φ(e_K)` is an invertible idempotent, so `φ(e_K) = 1`.
   - For `y ∈ K`, `φ(y) = φ(y) φ(e_K) = φ(y e_K) = φ(e_K) = 1`.
   - So `ker(φ|_V) ⊇ K != 1`, and `φ|_V` is trivial by simplicity. In particular `φ(h) = 1`.

   This is (c_DF), and Theorem W_V gives (a).
2. By `finite-subgroups-of-thompson-v-permute-a-canonical-partition`, `⟨x⟩` permutes a finite cylinder
   partition `P` by prefix replacements. Its orbits on `P` have length 1 or 3. At least one has length 3,
   because an element fixing every piece by the identity prefix replacement is `1`.
   - List the 3-cycles as `a_j -> b_j -> c_j -> a_j` (`j = 1..r`), with `x(a_j w) = b_j w`,
     `x(b_j w) = c_j w`, `x(c_j w) = a_j w`, and put `U_j = [a_j] ∪ [b_j] ∪ [c_j]`.
   - Let `Φ_j : Ω -> U_j` be `00w -> a_j w`, `01w -> b_j w`, `1w -> c_j w`.
   - Define `θ(y) = Φ_j y Φ_j^(-1)` on each `U_j`, and the identity off `∪ U_j`.
   - `θ(y) ∈ V`. Refine a code pair of `y` until both codes refine `(00, 01, 1)`. Then `Φ_j` only changes
     prefixes.
   - `θ : V -> V` is an injective homomorphism, since it is conjugation by a homeomorphism on each piece.
   - `θ(h) = x`: on `U_j`, `a_j w -> Φ_j(h(00w)) = b_j w`, and similarly on the other pieces.
   - So the unital algebra map `θ : F_2[V] -> F_2[V]` sends `e_h` to `e_x`, and `c e_h b = 1` gives
     `θ(c) e_x θ(b) = 1`.

   [EXP] C4 checks multiplicativity of `θ` and `θ(h) = x` on random products of cylinder swaps, for `r = 1`
   and two splittings. QED

**Corollary 3.2 (ascent to the Leavitt units).**
1. The target implies `binary-cyclic-averaging-idempotent-is-full-on-leavitt-units`.
2. (d) for `V` implies (d) of [WF] for `R^x`.

*Proof.*
1. The inclusion `V <= R^x` induces an injective unital algebra map `F_2[V] -> F_2[R^x]`. It sends `g ∈ V` to
   the permutation unit `g = s_2 t_1 + s_3 t_2 + s_1 t_3` of that claim, since `S[10] T[0] + S[11] T[10] +
   S[0] T[11]` is the image of `(0, 10, 11) -> (10, 11, 0)`. Apply it to the (a') solution.
2. A nontrivial `ρ : R^x -> W^x` into a weakly finite ring of characteristic two is injective, by simplicity
   of `R^x` (`binary-leavitt-unit-group-is-simple`). It then restricts to a nontrivial representation of
   `V`. QED

**Corollary 3.3 (rank gate).** (d) implies `thompson-v-has-no-nontrivial-f2-rank-model`.

*Proof.* Let `M = Π_(k -> ω) M_(n_k)(F) / N_rk` with `char F = 2`.
- `N(X) = lim_ω rk(X_k) / n_k` on matrices over `B = Π_k M_(n_k)(F)` is a Sylvester matrix rank function
  with `N(1) = 1`, and `N_rk = ker N`.
- By `sylvester-rank-function-quotients-are-weakly-finite`, `M = B / ker N` is weakly finite, and it has
  characteristic two.
- So (d) makes every homomorphism `V -> M^x` trivial. QED

**Corollary 3.4 (dead hosts, transferred to `V`).** A nontrivial homomorphism `ρ : V -> W^x`, with `W` of
characteristic two, exists for none of the following `W`. So a refutation of (d) cannot use them.
1. **Commutative rings.** `V` is simple and nonabelian, hence perfect.
2. **Division rings.**
   - `ρ` is injective by simplicity.
   - The `F_2`-span of `ρ(A_9)` is a finite commutative subring of a division ring, hence a finite field.
   - A finite field has cyclic multiplicative group, but this one contains `ρ(A_9) ≅ C_3²`. Contradiction.
3. **Rings whose nilpotents have bounded index `N`.** This includes `M_n(D)`, reduced rings,
   finite-dimensional algebras and bounded products of these.
   - `V` contains `2^m`-cycles `x` for every `m`, by permuting a complete prefix code.
   - `(ρ(x) - 1)^(2^m) = ρ(x^(2^m)) - 1 = 0`, so `(ρ(x) - 1)^N = 0`.
   - With `2^j >= N` and `m > j`, `ρ(x^(2^j)) = 1` while `x^(2^j) != 1`, so `ρ` is trivial by simplicity.

   This is the argument of Theorem A of `leavitt-unit-hosts-need-nilpotents-of-unbounded-index`, run inside
   `V`.

## 4. A support filter from [DHJ]

For `x` in a group algebra `F_2[Γ]`, write `|x|` for the size of its support. Over `F_2`, the augmentation
is `ε(x) = |x| mod 2`.

**[DHJ] Proposition 4.21** (verbatim, ar5iv, read 2026-09-16): "Let m and n be odd integers with either (a)
min(m,n)=3 and max(m,n)≤11 or (b) m=n=5. Then Kaplansky's Direct Finiteness Conjecture holds over the field
𝔽₂ of two elements for rank pair (m,n)."
- "DFC for rank pair `(m, n)`" means: for all groups `G` and all `a, b ∈ F_2[G]` with `|a| = m` and
  `|b| = n`, `ab = 1` implies `ba = 1`.
- [DHJ] Remark 4.13: DFC holds for rank pair `(m, n)` iff it holds for `(n, m)`.

**Proposition 4.1 (filter).** Let `Γ` be any group, `h ∈ Γ` of order three, and `c e_h b = 1` in `F_2[Γ]`.
1. `|b|` and `|c|` are odd and at least `3`.
2. If `|c| = 3`, then `|e_h b| >= 13`. If `|b| = 3`, then `|c e_h| >= 13`.
3. If `|c| = 5`, then `|e_h b| != 5`. If `|b| = 5`, then `|c e_h| != 5`.
4. In particular `(|c|, |b|) != (3, 3)`, and more generally `|c| = 3` forces `|b| >= 5`, and `|b| = 3` forces
   `|c| >= 5`.

*Proof.* `e_h != 1`, since `1, h, h²` are distinct. We use one fact repeatedly: if an idempotent `p` has a
one-sided inverse on one side, then `p = 1`. For example, `p q = 1` gives `p = p(pq) = pq = 1`.
1. `ε(c) ε(e_h) ε(b) = 1` and `ε(e_h) = 3 = 1`, so `|b|` and `|c|` are odd.
   - If `b` is a monomial, it is a unit, and `(b c) e_h = b (c e_h b) b^(-1) = 1`, so `e_h = 1`.
   - Symmetrically if `c` is a monomial.
2. Put `Y = e_h b`, so `c Y = 1` and `ε(Y) = 1`, hence `|Y|` is odd.
   - If `|Y| = 1`, then `Y` is a unit and `c = Y^(-1)` is a monomial, contradicting 1.
   - If `|c| = 3` and `|Y| ∈ {3, 5, 7, 9, 11}`, then [DHJ] 4.21(a) at rank pair `(3, |Y|)` gives `Y c = 1`.
     That is, `e_h (b c) = 1`, so `e_h = 1`.
   - The case `|b| = 3` uses `X = c e_h`, `X b = 1`, the rank pair `(|X|, 3)` and Remark 4.13. It gives
     `b X = 1`, so `(b c) e_h = 1`.
3. The same, with [DHJ] 4.21(b).
4. `|e_h b| <= 3|b|`, so `|c| = 3` and `|b| = 3` give `|e_h b| <= 9`, contradicting 2. QED

*Scope.* The filter holds in every group algebra over `F_2`, so it says nothing specific about `V`. It
complements the structural filter on `H = ⟨h, supp b, supp c⟩` recorded on the target, and rests on a
computer-assisted enumeration taken at statement level. An exhaustive search of the next case,
`|c| = 3` with `|b| = 5`, would need rank pairs `(3, 13)` and `(3, 15)`, which [DHJ] does not cover.

## 5. What remains, and where the attacks die

**The reduced problem.** The target is exactly `thompson-v-has-no-weakly-finite-char-two-representation`:
there is no nontrivial homomorphism from `V` into the units of a weakly finite (equivalently, directly finite)
ring of characteristic two. Known refuters of that statement are:
- `thompson-v-is-f2-linear-sofic`, through Corollary 3.3;
- stable finiteness of `F_2[V]` (a case of `thompson-v-modular-group-algebras-are-stably-finite`), since then
  the inclusion `V -> F_2[V]^x` is a nontrivial weakly finite representation;
- any group `Γ ⊇ V` with `F_2[Γ]` directly finite, for the same reason. So the target makes `F_2[Γ]`
  not directly finite for every `Γ` containing `V`, which is the known ascent of direct-finiteness failure.

A proof of the target must therefore show that `F_2[V]` is not directly finite. That is expected to be
false by Kaplansky's conjecture, and it is not excluded by anything known for `V`.

**The evaluation image.** Put `P = π(F_2[V]) ⊆ R`.
- `π(h) != 1`. So if `P` were directly finite, (c_DF) would fail and the target would be refuted.
- So the target forces `P` to be not directly finite.
- [TGT] Lemma 3.1 (stated there over `F_3`; the proof is characteristic-free) shows that every element of `P`
  acts on `M` with all row and column sums equal to its augmentation.

The Leavitt witness `b_0 = s0 + s10 + s11`, `c_0 = t0 + t10 + t11`, with `c_0 π(e_g) b_0 = 1` in `R`
(`binary-cyclic-averaging-idempotent-is-full-on-leavitt-units`, Attempts), is balanced.
- `b_0 δ_w = δ_(0w) + δ_(10w) + δ_(11w)` has column sums `3 = 1`. Every sequence begins with exactly one of
  `0, 10, 11`, so the row sums are `1`.
- Dually for `c_0`.

So Lemma 3.1 does not separate this witness from `P`, unlike the ternary `s0 + s1` of [TGT] Corollary 3.2.
`b_0` is not a sum of three elements of `V`:
- such elements would satisfy `x_1(w) ∈ {0w, 10w, 11w}` pointwise, with no cancellation possible;
- a bijection of that form has `x_1(w) = pw` on a clopen `C_p`, and surjectivity forces `C_0 = C_10 = C_11 = Ω`.

Whether `b_0 ∈ P`, and whether `P` is directly finite, is open.

**Approaches that die, and where.**
- *Theorem W alone.* It is an equivalence and decides nothing without a weakly finite target.
- *The dead hosts of Corollary 3.4.* They leave exactly the noncommutative, non-division rings with nilpotents
  of unbounded index, such as rank ultraproducts and group algebras.
- *Direct small-support search.* It is blocked beyond Proposition 4.1. The next cases need DFC data at rank
  pairs outside [DHJ], and a witness pair `(3, 5)` has `|e_h b| <= 15`.
- *Trace and Hattori–Stallings arguments.* In characteristic two the identity-coefficient trace has no
  positivity, and `τ(e_h) = 1 = τ(1)` ([TGT] Section 9).

