# Invariants on the ternary anti-central summand

Lane `gk-l3-obstruct`, 2026-09-12. Supports the Cairn claims:
- `anti-central-state-obstruction-equals-stable-finiteness`
- `ternary-anti-central-summand-has-no-finite-dimensional-images`
- `finitely-generated-linear-groups-are-residually-finite` (citation)
- `ternary-corner-witnesses-need-non-linear-sofic-support`
- `ternary-anti-central-unit-class-is-nonpositive` (open)
- `twisted-leavitt-corner-fullness-equals-absence-of-k0-states` (Section 7)
- `leavitt-visible-states-are-factorwise-and-colimit-stable` (Section 8)
- `leavitt-visible-colimit-factors-admit-k0-states` (open, Section 8)

The question: which invariant of `S_-` could forbid the target
`ternary-anti-invariant-swap-corner-is-full`?

**Summary, after Section 7.** On `S_-`, and on every twisted Leavitt-visible factor, the following are
equivalent: the corner is full; the factor fails the rank condition at some matrix size; its unit class
is nonpositive in `K_0`; no state exists. So the obstruction side is exactly the existence of a state.

## 0. Notation

- `R = L_(F_3)(1,2)`, `G = G_3 = R^x`, `S = F_3[G]`, `z = -1` central of order two.
- `eps_+- = 2(1 +- [z])` are central orthogonal idempotents, and `S_- = eps_- S = S/(1+[z])`.
- `w = s0 t1 + s1 t0`, `d = s0 t0 - s1 t1`, `e_- = eps_- . 2(1 + [w])`.
- Target: `b, c` in `S_-` with `c e_- b = eps_-`.
- `K_0(S_-)` is the Grothendieck group of finitely generated projective right `S_-`-modules. It is a
  **preordered** abelian group, with cone `K_0^+ = { [P] }`. We write `x <= y` iff `y - x` lies in
  `K_0^+`.
- A **state** is an additive map `s: K_0(S_-) -> R` with `s(K_0^+) >= 0` and `s([eps_-]) = 1`.

## 1. Halving

By `ternary-leavitt-swap-problem-splits-at-central-involution` part 2, `[d]^2 = 1` and
`[d] e_- [d] = eps_- - e_-`. Hence `e_- ~ eps_- - e_-` (conjugate idempotents), and

    [eps_-] = [e_-] + [eps_- - e_-] = 2 [e_-]     in K_0(S_-).                (1.1)

## 2. Theorem A: states, and the unit class

**Order unit.** `u := [eps_-]` is an order unit of `K_0(S_-)`. Every finitely generated projective
`P` is a summand of some `S_-^n`, so `[P] <= n u`. Every `x = [P] - [Q]` then satisfies
`-m u <= x <= n u` for suitable `n, m`.

**Theorem A.**
- (a) If the target holds, then `u <= 0` in `K_0(S_-)`. So `S_-` admits no state, and no Sylvester
  matrix rank function `N` with `N(eps_-) = 1`.
- (b) (state criterion) `K_0(S_-)` admits a state iff `k u` is not `<= 0` for every `k >= 1`,
  equivalently iff `u` is not `<= 0`.
- (c) If `k u <= 0` for some `k >= 1`, then `M_r(F_3[G])` is not directly finite for some `r`, so
  `G` is not surjunctive.

Consequently, a positivity-type obstruction to the target (a state, or any dimension function or
Sylvester rank function normalized at `eps_-`) exists exactly when `[eps_-]` is not `<= 0`. That
condition is the negation of `ternary-anti-central-unit-class-is-nonpositive`, and its failure already
refutes Gottschalk on `G_3`. Section 7 upgrades this: the target holds iff no state exists.

**Proof of (a).**
- Put `f = (e_- b)(c e_-)`. Then `f^2 = e_- b (c e_- b) c e_- = f`, and `f <= e_-` (`e_- f = f e_- = f`).
- `f ~ eps_-`: `(c e_-)(e_- b) = c e_- b = eps_-`.
- So `e_- = f + h` with `h = e_- - f` an idempotent orthogonal to `f`. Hence
  `[e_-] = [eps_-] + [h]`, so `u = [eps_-] <= [e_-]`.
- With (1.1): `2[e_-] = u <= [e_-]`. Subtracting `[e_-]` gives `[e_-] <= 0`, and then
  `u = 2[e_-] <= 0`, since the cone is closed under addition. So `k = 1` works.
- A state would give `1 = s(u) <= 0`, which is impossible.
- A Sylvester matrix rank function is additive on orthogonal idempotents and constant on equivalent
  idempotents, so it induces a state on `K_0` when normalized at `eps_-`. Hence none exists either. QED

**Proof of (b)** (the Goodearl–Handelman state criterion, proved here to keep the trust surface empty).
- *Only if.* If `k u <= 0` for some `k >= 1`, every state satisfies `k s(u) <= 0`, contradicting
  `s(u) = 1`.
- *If.* Assume `k u` is not `<= 0` for any `k >= 1`. On the rational vector space `V = K_0(S_-) (x) Q`
  define

      p(x) = inf { m/n : n >= 1, m in Z, n x <= m u }.

  - *Finite.* `p` is finite, since `x <= N u` gives `p(x) <= N`.
  - *Bounded below.* If `x >= -N u` and `n x <= m u`, then `(m + nN) u >= 0`. If `m + nN < 0`, that
    would give `-(m+nN) u <= 0` with `-(m+nN) >= 1`, which is excluded. So `m/n >= -N`.
  - *Sublinear.* `p` is subadditive (add the inequalities) and positively homogeneous over `Q`.
    Torsion classes `t` satisfy `p(t), p(-t) <= 0`, so `p` is well defined on `V`.
  - *Values at `+-u`.* `n u <= m u` iff `(m - n) u >= 0`, which forces `m >= n`. So `p(u) = 1`.
    Similarly `p(-u) = -1`.
  - *Extension.* On `Q u` put `f(q u) = q <= p(q u)`. Hahn–Banach over `Q`, by the usual Zorn
    argument, extends `f` to an additive `f: V -> R` with `f <= p`.
  - *Positivity.* For `x` in `K_0^+`: `-x <= 0 . u`, so `p(-x) <= 0`, so `f(-x) <= 0` and `f(x) >= 0`.
  - So `f` restricted to `K_0(S_-)` is a state. QED

**Proof of (c).**
- `k u <= 0` means `-k u` lies in `K_0^+`: there is a finitely generated projective `Q` with
  `[Q] + k[eps_-] = 0` in `K_0(S_-)`.
- By the definition of `K_0` there is `N` with `Q (+) S_-^k (+) S_-^N ~= S_-^N`. Put `r = N`: the free
  module `S_-^r` is isomorphic to `S_-^r (+) (S_-^k (+) Q)` with `k >= 1`, a nonzero complement.
- An isomorphism onto a proper summand gives `A, B` in `M_r(S_-)` with `B A = 1_r != A B`.
- Pad with `eps_+ . 1_r`: `A + eps_+ 1_r` and `B + eps_+ 1_r` are a one-sided pair in `M_r(F_3[G])`.
- `stable-finiteness-failure-refutes-surjunctivity` gives an injective, non-surjective automaton on
  `(F_3^r)^G`. QED

**Remark (added later on 2026-09-12).**
- *The multiple is irrelevant.* For `k >= 1`, `k u <= 0` iff `u <= 0`: if `-k u` is in the cone, so is
  `-u = (k-1)u + (-k u)`.
- *Stable finiteness is stronger.* The criterion in (b) is implied by stable finiteness of `S_-` and is
  weaker in general: `B x F`, with `B` properly infinite and `F` a field, has a state but is not stably
  finite.
- *Scope of the proofs.* (b) and (c) use nothing about `S_-` beyond `u` being the class of the unit, so
  they hold for every unital ring.

**Corollaries.**
- (i) The target forces `S_-` to be properly infinite. `f ~ eps_-`, and `f' = [d] f [d]` is an
  idempotent with `f' <= eps_- - e_-` and `f' ~ eps_-`. These are two orthogonal idempotents
  equivalent to the unit.
- (ii) If `[eps_-]` is not `<= 0`, then some state exists, and by (a) the target is false. Section 7
  proves the converse: if `[eps_-] <= 0`, the target holds.

## 3. Theorem B: inert invariants

**(i) No additive invariant refutes the target on its own.**
- *Setting.* Let `phi: K_0(S_-) -> A` be any homomorphism: `K_0` with coefficients, Hattori–Stallings
  traces, the Kaplansky identity-coefficient trace mod 3, or the lifted traces
  `t_(3,k): K_0 -> Z/3^k` of `finite-precision-lifted-trace-obstruction`.
- *What the target imposes.* On classes, the target imposes exactly `[e_-] = [eps_-] + [h]` for one
  unknown idempotent `h`. With (1.1) this reads `phi([h]) = -phi([e_-])`. The class
  `-[e_-] = [e_-] - [eps_-]` exists in `K_0` whether or not the target holds. So `phi` refutes the
  target only together with a constraint on `phi(K_0^+)`. Any such refutation shows that `[e_-]`, hence
  `u = 2[e_-]`, is not `<= 0`, and then Theorem A(b) produces a state.
- *Computed values.* Over `Z_3[H_0]`, `H_0 = <z, w> ~= C_2^2`, the idempotents lift to
  `(1 - z)/2` and `(1 - z)(1 + w)/4`. So `t_(3,2)([eps_-]) = 5` and `t_(3,2)([e_-]) = 7` mod 9, and
  `2 . 7 = 14 = 5` agrees with (1.1).
- *Mod 3 trace.* The mod 3 trace gives `tau(eps_-) = 2`, `tau(e_-) = 1`, and `tau(h) = 2`, with no
  contradiction.
- *Why the precision bound does not apply.* The detection bound of the lifted-trace node needs the
  projective to live in a finite subgroup. `h` need not.

**(ii) No finite-dimensional images.** `ternary-anti-central-summand-has-no-finite-dimensional-images`
proves that `G` has no nontrivial finite-dimensional representation over any field.
- *Proof.* `G` is perfect (`leavitt-gl-equals-el-and-perfect-unit-group`, every field) and
  `PG = G/<z>` is simple (`odd-leavitt-unit-groups-mod-scalars-are-fp-simple`).
  - So the normal subgroups of `G` are `1`, `<z>` and `G`. If `N <| G` and `N<z> = G`, then
    `G = [G,G] = [N<z>, N<z>] = [N,N] <= N`.
  - A finite-dimensional representation has a finitely generated linear image, which is residually
    finite (`finitely-generated-linear-groups-are-residually-finite`).
  - `G` and `PG` are infinite (nonsofic) with no proper normal subgroup of finite index, so neither is
    residually finite. The kernel is therefore `G`, and the representation is trivial.
- *Consequence.* Every ring homomorphism `S_- -> M_n(k)` over a field is zero. The image of `eps_-` is
  an idempotent `p`, and `S_-` acts unitally on `p k^n` through a representation of `G` with `z`
  acting as `-1`, which must be zero. Every rank function, trace, determinant or character that
  factors through a finite-dimensional image vanishes on `S_-`, and so do augmentation-type maps.

**(iii) Properly infinite images are inert.** The Leavitt evaluation `S_- -> R` and anything through
a properly infinite ring carries no state. In `R` the target's image equation already holds, with
`b = s0 + s1` and `c = 2(t0 + t1)`.

**(iv) Sibling invariants, recorded by their lanes.**
- Lane `gk-l3-free`: an F_3-valued average trace on a crossed-product quotient does not obstruct.
- Lane `gk-l3-kernel`: mod-3 traces do not separate kernel idempotents from `eps_-`.
- Lane `gk-l3-units`: the canonical trace forbids unital binary Leavitt families in `S_-`
  (`anti-central-ternary-summand-has-no-binary-leavitt-family`). The target needs only a Cohn family,
  whose defect has trace `1`, so this does not obstruct it.
All of these are additive, and all are covered by (i).

## 4. Theorem C: witness support filter

If `c e_- b = eps_-` in `S_-`, let `H = <z, w, supp b, supp c>`. Then `H` is not `F_3`-linear sofic,
and in particular not sofic (`sofic-implies-linear-sofic-over-every-field`). So it is not amenable,
not residually finite and not linear.

*Proof.*
- The equation involves only products of elements of `H`, so it holds in `F_3[H] eps_-`.
- `e_- != eps_-` in `F_3[H]`, because `1, z, w, zw` are distinct.
- With `A = e_- b + eps_+` and `C = c + eps_+` in `F_3[H]`: `CA = 1` and `AC != 1`, since `AC = 1`
  would make `e_- b` a right invertible element of `e_- S_-`, forcing `e_- = eps_-`.
- So `F_3[H]` is not directly finite, and `linear-sofic-group-algebra-is-stably-finite` excludes
  `F_3`-linear soficity. QED

This is weaker than gk-kdf-structure's support no-go, which excludes supports carrying a
finite-dimensional char-3 representation with `z -> -1`. It applies to every support, though,
including nonsofic ones with no such representation.

## 5. Where the obstruction side stops

By Theorems A and E, the target fails iff `(K_0(S_-), [eps_-])` admits a state. The natural sources of
a state, and why each fails:
- **Sylvester rank functions on `S_-`,** equivalently homomorphisms into regular rings with a rank
  function. Rank-metric approximations of `G` with `z` acting as `-1` on positive normalized rank
  would give one. That is the `F_3`-linear soficity gate for the anti-central sign, and property (T)
  gives no rank rounding over finite fields (`kazhdan-group-rank-models-admit-no-expander-decomposition`).
- **Finite-dimensional images:** none, by Theorem B(ii).
- **Properly infinite images:** inert, by Theorem B(iii).

So disproving the target is exactly proving that `[eps_-]` is not `<= 0`, equivalently that a state
exists.

## 6. The stable target (corrected later on 2026-09-12)

`ternary-anti-central-unit-class-is-nonpositive` (open) asks for `k >= 1` with `k[eps_-] <= 0`, that
is, `S_-^r ~= S_-^r (+) S_-^k (+) Q`. In `R` the isomorphism holds already, since `R ~= R (+) R`.

*Correction.* The first version of this section said the stable target sits strictly between the corner
equation and a Gottschalk counterexample, and that stabilization and the complement `Q` give more room.
That is withdrawn. By Theorem E it is **equivalent** to the corner equation: the diagonal endomorphism
halves the unit class and shrinks any failure of the rank condition to size one (Section 7.2).

## 7. Theorem E: fullness is the absence of states

**Setting.** Take notation from `leavitt-unit-group-algebras-split-over-scalar-characters` and
`cyclic-twist-makes-leavitt-visible-factor-a-matrix-algebra`.
- The host: `q = p^r`, `d >= 2`, `L = L_(F_q)(1,d)`, `G = L^x`.
- The factor: `A = A_iota`, the Leavitt-visible factor of `F_q[G]`, with unit `eps_iota`.
- The twist: `m = 1 + j(d-1) >= 2` with `p` not dividing `m` and `m | q - 1`. Let `s_i, t_i`
  (`0 <= i < m`) be an `m`-ary Leavitt family in `L`, `g = sum_i s_(i+1) t_i`, and
  `e_H = eps_iota (1/m) sum_k [g^k]`.
- The corner: `T = e_H A e_H`, so `A ~= M_m(T)` by part 2 of the matrix-structure claim.
- The monoid: `V(A)` is the monoid of isomorphism classes of finitely generated projective right
  `A`-modules, with `a <= b` iff `b = a + c` for some `c`. Put `u = [A]`, and `p = [e_H A]`, so
  `u = mp`.

**Theorem E.** The following are equivalent.
1. `c' e_H b' = eps_iota` is solvable in `A`: the cyclic corner is full.
2. `A^2` is isomorphic to a direct summand of `A` (`2u <= u`): a unital two-pair Cohn family in `A`.
3. `A` fails the rank condition: `A^(n+1)` is isomorphic to a direct summand of `A^n` for some `n >= 1`.
4. `u <= 0` in `K_0(A)`.
5. `(K_0(A), u)` admits no state.

When they hold, `F_q[G]` is not stably finite and `G` is not surjunctive.

**7.1 The diagonal homomorphism.**
- *Group level.* `D(h) = sum_i s_i h t_i` is an injective group endomorphism of `G`:
  - it is multiplicative, `D(h) D(h') = sum_i s_i h h' t_i`, because `t_i s_j = delta_ij`;
  - it is unital, `D(1) = sum_i s_i t_i = 1`;
  - it fixes scalars, `D(lambda) = lambda`;
  - it commutes with `g`: both `g D(h)` and `D(h) g` equal `sum_i s_(i+1) h t_i`.
- *Algebra level.* `D` extends to a unital algebra endomorphism of `F_q[G]` fixing every `eps_chi`, so
  it maps `A` into `A`, and every `[D(h)]` commutes with `e_H`.
- *Consequence.* `psi(x) = e_H D(x)` is a unital ring homomorphism `A -> T`: `psi(x)psi(y) =
  e_H D(x) e_H D(y) = e_H D(xy)`, and `psi(eps_iota) = e_H`.
- *Instance.* At `q = 3` this is the map `delta` of lane `gk-l3-units`, `delta(h) = s0 h t0 + s1 h t1`,
  which commutes with `w`.

**7.2 Halving.** `Phi = M_m(psi)`, followed by `M_m(T) ~= A`, is a unital ring homomorphism
`M_m(A) -> A`. Through the Morita identification `V(M_m(A)) = V(A)`, which sends `[M_m(A)]` to `mu`, it
induces a monoid homomorphism `F: V(A) -> V(A)` with `F(mu) = u`. Put `x = F(u) = [Phi(e_11) A]`, so
`mx = u`.

**Proof of Theorem E.**
- *1 <=> Cohn form in `T`.* By part 3 of the matrix-structure claim, 1 holds iff `m[T] <= [T]` in
  `V(T)`. Under `V(T) = V(A)` this is `mp <= p`.
- *1 => 2.* Write `p = mp + c = p + (m-1)p + c`.
  - Substituting repeatedly gives `p + k(m-1)p <= p` for every `k`.
  - With `k = m`, adding `(m-1)p` to both sides gives `mp + m(m-1)p <= mp`, that is `mu <= u`.
  - Writing `u = mu + c'` gives `u = 2u + (m-2)u + c'`, so `2u <= u`.
- *2 => 1.* A two-pair Cohn family `y_i x_j = delta_ij eps_iota` in `A` maps under `psi` to a two-pair
  Cohn family in `T`, so `2[T] <= [T]`. Adding `[T]` repeatedly gives
  `m[T] <= (m-1)[T] <= ... <= [T]`.
- *2 => 3.* Take `n = 1`.
- *3 => 2.*
  - Adding copies of `u` to both sides, assume `n = mj`.
  - Applying `F` gives `ju + x <= ju`. Write `ju = ju + x + c`; substituting repeatedly gives
    `ju + kx <= ju` for every `k`, and `k = m` gives `(j+1)u <= ju`.
  - So size `mj` reduces to size `j`. Since `ceil(n/m) < n` for `n >= 2`, repeating reaches `n = 1`.
- *3 <=> 4.* `A^n ~= A^(n+1) (+) Q` gives `[Q] = -u` in `K_0`. Conversely `-u = [Q]` in `K_0(A)` means
  `Q (+) A (+) A^N ~= A^N` for some `N`, which is 3.
- *4 <=> 5.* The state criterion, Theorem A(b), valid for every unital ring by the Remark in Section 2.
- *Surjunctivity.* 4 gives a one-sided pair in some `M_N(A)` by Theorem A(c). Padded by `1 - eps_iota`
  it is a one-sided pair in `M_N(F_q[G])`, and `stable-finiteness-failure-refutes-surjunctivity` gives
  the automaton. QED

**7.3 The ternary instance.** At `(q, d, m) = (3, 2, 2)`: `A = S_-`, `e_H = e_-`, `g = w` and
`psi(x) = e_- delta(x)` (`ternary-anti-invariant-corner-is-the-q3-m2-cyclic-case`).
- *Credit.* Items 1 <=> 2 at this instance are the equivalence recorded on
  `ternary-anti-central-summand-has-cohn-family` (lane `gk-l3-units`). Items 3, 4 and 5 are new here.
- *Consequences:*
  - `ternary-anti-central-unit-class-is-nonpositive` <=> `ternary-anti-invariant-swap-corner-is-full`
    (route `nonpositive-unit-class-gives-anti-invariant-corner`, reversing
    `anti-invariant-corner-gives-nonpositive-unit-class`);
  - the corner is full iff `(K_0(S_-), [eps_-])` admits no state, iff `S_-` fails the rank condition.

**7.4 What Theorem E does and does not say.**
- *Exact dichotomy.* On each twisted factor, either a state exists and the cyclic corner fails, or the
  corner is full.
- *Stable finiteness is not decided.* A state can coexist with a one-sided pair in `M_N(A)` whose
  complement does not dominate `u`. Such a pair still refutes surjunctivity.
- *Trace consistency.* If `A^2 (+) C ~= A` at `q = 3`, the canonical trace gives
  `tau(C) = 2 - 4 = 1 != 0`, so `C != 0`. This matches
  `anti-central-ternary-summand-has-no-binary-leavitt-family`.

## 8. Theorem F: character factors and the field tower

**8.1 Factorwise.** Let `A_q = F_q[L_(F_q)(1,d)^x] = prod_chi A_chi`.
- *Decomposition.* `V(A_q) = prod_chi V(A_chi)` and `K_0(A_q) = (+)_chi K_0(A_chi)` as preordered
  groups, with `[1] = ([eps_chi])_chi`.
- *States of the product.* A state `s` on `(K_0(A_q), [1])` has weights `t_chi = s([eps_chi]) >= 0`
  with sum `1`.
  - Where `t_chi = 0`, `s` vanishes on `K_0(A_chi)`, because every class there lies between
    `-N[eps_chi]` and `N[eps_chi]`.
  - Where `t_chi > 0`, `s / t_chi` is a state on `(K_0(A_chi), [eps_chi])`.
- *The whole algebra always has a state.* The augmentation `F_q[G] -> F_q` kills every `eps_chi` except
  the trivial one, and induces a state carried by the trivial factor. So `(K_0(A_q), [1])` says
  nothing about `A_iota` when `q > 2`. An obstruction to a Leavitt-visible corner must be a state on
  `(K_0(A_iota), [eps_iota])` itself.
- *The binary host.* For `q = 2` the only factor is augmented, so `[1] <= 0` never holds over `F_2`. A
  binary counterexample through `F_2[R^x]` must fail stable finiteness with a complement that does not
  dominate the unit.

**8.2 Ascent along the field.**
- *The map.* The inclusion `L_(F_q)(1,d) ⊂ L_(F_(q^r))(1,d)` gives `G_q <= G_(q^r)`. Since
  `eps_iota(q) eps_iota(q^r) = eps_iota(q^r)` (Proposition 4 of
  `research/artifacts/leavitt-host-survey-scalar-characters-2026-09-12.md`) and `eps_iota(q^r)` is
  central, `phi(x) = x eps_iota(q^r)` is a unital ring homomorphism `A_iota(q) -> A_iota(q^r)`.
- *What it carries.* It sends `e_H(q)` to `e_H(q^r)`, and it induces order-preserving maps on `V` and
  `K_0` sending `u` to `u`.
- *Consequence.* `u <= 0` at `q` implies `u <= 0` at `q^r`, and a state at `q^r` restricts to a state
  at `q`.

**8.3 The colimit factor.** Fix `p` and `d`, and let
`A_iota(infinity) = colim_k A_iota(p^(k!))` along the maps `phi`. Every finite field of characteristic
`p` is a subfield of some stage.
- *Presentation.* Each `A_iota(q)` is `F_q[G_q]` modulo the ideal generated by `[lambda] - lambda`,
  `lambda in F_q^x`: on `A_chi` that element acts as `chi(lambda) - lambda`, which is invertible for
  some `lambda` unless `chi = iota`. So `A_iota(infinity)` is `Fbar_p[L_(Fbar_p)(1,d)^x]` modulo the
  ideal generated by `[lambda] - lambda`, `lambda in Fbar_p^x`.
- *Finiteness.* `V` and `K_0` commute with directed colimits of unital rings, with positive cone the
  union of the images: idempotent matrices, and the matrices realizing isomorphisms, have finitely many
  entries.

**Theorem F.** For fixed `p` and `d`, the following are equivalent.
1. `(K_0(A_iota(infinity)), u)` admits no state.
2. `u <= 0` in `K_0(A_iota(infinity))`.
3. `u <= 0` in `K_0(A_iota(q))` for some finite field `F_q` of characteristic `p`.
4. For some finite field `F_q` of characteristic `p` and some admissible `m` prime to `p`, the cyclic
   corner of `leavitt-visible-cyclic-corner-is-full-on-some-host` is full over `F_q`.

When they hold, some `L_(F_q)(1,d)^x` is not surjunctive.

*Proof.*
- *1 <=> 2.* The state criterion.
- *2 <=> 3.* Finiteness of `V` and `K_0` under colimits, together with 8.2.
- *3 => 4.* Choose an admissible `m` prime to `p`: one of `d` and `2d - 1` works, since both are
  `1 mod (d - 1)` and `p` cannot divide both. Push `u <= 0` to a stage containing a primitive `m`-th
  root of unity; every `m` prime to `p` divides some `p^(k!) - 1`. There Theorem E, 4 => 1, gives the
  corner.
- *4 => 3.* Ascend the corner along 8.2 to a stage with `m | q - 1`, then apply Theorem E, 1 => 4. QED

**8.4 Answers and consequences.**
- *States are checked factorwise.* The whole algebra always has one (8.1).
- *The colimit does not change the question.* The colimit factor has a state iff every finite stage
  has one. One ring per `(p, d)` decides every linear cyclic corner in characteristic `p` and arity `d`.
- *The root.* `leavitt-visible-cyclic-corner-is-full-on-some-host` holds iff, for some `(p, d)`, the
  colimit factor admits no state.
- *The obstruction hypothesis.* `leavitt-visible-colimit-factors-admit-k0-states` (open) says every
  colimit factor admits a state. It would refute every linear cyclic corner, but not the root
  `some-finite-field-leavitt-unit-group-nonsurjunctive`, since a one-sided pair with a non-dominating
  complement escapes it.

## 9. Module-isomorphism lifting: where it stands

The direction: lift an `R`-module isomorphism `R^r ~= R^r (+) R^k (+) Q` to `S_-`, as rectangular
matrices whose products are exact identities.

**9.1 No room from stabilization.** By Theorem E (3 => 2), an exact lift at any size, multiplicity and
complement gives a two-pair Cohn family in `S_-`. The halving map performs the reduction. Searching at
larger sizes is equivalent to searching at size one.

**9.2 Orbit reduction at size one.**
- *Complement types.* Let `Xbar` be a `1 x 2` row over `R` with a left inverse `Ybar`. Its complement
  `(1 - Xbar Ybar) R` is `0` or `~= R`. (For `L(1,2)` the monoid of finitely generated projectives is
  `{0, [R]}`, by the nonstable K-theory of Leavitt algebras [Ara–Moreno–Pardo 2007]. This is a remark;
  no claim uses it.)
- *Orbits.* Two rows with isomorphic complements satisfy `Xbar' = g Xbar h` with `g in GL_1(R) = G`
  and `h in GL_2(R) = EL_2(R)` (`leavitt-gl-equals-el-and-perfect-unit-group`).
- *Lifting the orbit.* The evaluation `S_- -> R` is onto (recorded on
  `ternary-anti-central-summand-has-cohn-family`). So `g` lifts to `[g]` and `h` to a product of
  elementary matrices, both invertible. If `X` lifts `Xbar` with left inverse `Y`, then `[g] X H` lifts
  `Xbar'` with left inverse `H^(-1) Y [g]^(-1)`.
- *Conclusion.* Whether some lift is left invertible depends only on the complement type. It suffices
  to try `Xbar_0 = (s0, s1)`, with complement `0`, and `Xbar_1 = (s0, s1 s0)`, with left inverse
  `(t0; t0 t1)` and complement `s1 s1 t1 t1 R`.

**9.3 The error criterion.** For lifts `X` of `Xbar` and `Y` of `Ybar`, `YX = 1_2 + E` with `E` in
`M_2(K_-)`, `K_- = ker(S_- -> R)`. `X` has a left inverse iff, for some such lifts, `1 + E` is
invertible, and then `(1 + E)^(-1) Y` is one. A nilpotent `E` suffices. This is the Gram form on
`ternary-anti-central-summand-has-cohn-family`.

**9.4 The kernel carries the unit class (remark; no claim rests on it).**
- *Isomorphism.* `K_0(R) = 0` and `K_1(R) = 0` by the `K`-theory sequence of `L_(F_3)(1,2)` (as recorded
  on `leavitt-gl-equals-el-via-purely-infinite-k1`). So the excision sequence
  `K_1(R) -> K_0(K_-) -> K_0(S_-) -> K_0(R)` makes `K_0(K_-) -> K_0(S_-)` an isomorphism.
- *The explicit class.* The involution `Ubar = [[0, Xbar_0], [Ybar_0, 0]]` in `GL_3(R)` has
  `Ubar diag(1, 0, 0) Ubar = diag(0, 1, 1)`. By Whitehead's lemma `Ubar (+) Ubar^(-1)` is a product of
  elementary matrices, so it lifts to `W` in `GL_6(S_-)`. Then
  `[W diag(1,0,0,0,0,0) W^(-1)] - [diag(0,1,1,0,0,0)]` is a kernel class mapping to
  `[eps_-] - 2[eps_-] = -[eps_-]`.
- *Consequence.* The corner holds iff this explicit class lies in the positive cone of `K_0(S_-)`.
  Compare lane `gk-l3-kernel`'s kernel corners.

**9.5 Where it dies.**
- *Reductions so far.* Every size reduces to one Cohn family in `S_-`. Every solution type over `R`
  reduces to lifting `(s0, s1)` or `(s0, s1 s0)`. The obstruction is invertibility of `1 + E` for a
  kernel-valued `E`, equivalently positivity of one explicit kernel class.
- *What is missing.* No lift with invertible `1 + E` is known, and no state on `(K_0(S_-), [eps_-])` is
  known. By Theorem E exactly one of the two exists.
