# Invariants on the ternary anti-central summand

Lane `gk-l3-obstruct`, 2026-09-12. Supports the Cairn claims:
- `anti-central-state-obstruction-equals-stable-finiteness`
- `ternary-anti-central-summand-has-no-finite-dimensional-images`
- `finitely-generated-linear-groups-are-residually-finite` (citation)
- `ternary-corner-witnesses-need-non-linear-sofic-support`
- `ternary-anti-central-unit-class-is-nonpositive` (open)

The question: which invariant of `S_-` could forbid the target
`ternary-anti-invariant-swap-corner-is-full`?

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

## 2. Theorem A: the only possible obstruction is a state, and states exist exactly under stable finiteness of the unit class

**Order unit.** `u := [eps_-]` is an order unit of `K_0(S_-)`. Every finitely generated projective
`P` is a summand of some `S_-^n`, so `[P] <= n u`. Every `x = [P] - [Q]` then satisfies
`-m u <= x <= n u` for suitable `n, m`.

**Theorem A.**
- (a) If the target holds, then `u <= 0` in `K_0(S_-)`. So `S_-` admits no state, and no Sylvester
  matrix rank function `N` with `N(eps_-) = 1`.
- (b) (state criterion) `K_0(S_-)` admits a state iff `k u` is not `<= 0` for every `k >= 1`.
- (c) If `k u <= 0` for some `k >= 1`, then `M_r(F_3[G])` is not directly finite for some `r`, so
  `G` is not surjunctive.

Consequently, a positivity-type obstruction to the target (a state, or any dimension function or
Sylvester rank function normalized at `eps_-`) exists exactly when `k[eps_-]` is not `<= 0` for
every `k >= 1`. That condition is the negation of `ternary-anti-central-unit-class-is-nonpositive`,
and its failure already refutes Gottschalk on `G_3` with no corner equation at all.

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

**Corollaries.**
- (i) The target forces `S_-` to be properly infinite. `f ~ eps_-`, and `f' = [d] f [d]` is an
  idempotent with `f' <= eps_- - e_-` and `f' ~ eps_-`. These are two orthogonal idempotents
  equivalent to the unit.
- (ii) If `S_-` is K_0-stably finite in the sense of (b), then some state exists, and by (a) the
  target is false. There is no cheaper positivity obstruction: whoever produces a state has proved
  that `S_-` carries no counterexample of type (c).

## 3. Theorem B: inert invariants

**(i) Every additive invariant with values in an abelian group is inert.**
- *Setting.* Let `phi: K_0(S_-) -> A` be any homomorphism: `K_0` with coefficients, Hattori–Stallings
  traces, the Kaplansky identity-coefficient trace mod 3, or the lifted traces
  `t_(3,k): K_0 -> Z/3^k` of `finite-precision-lifted-trace-obstruction`.
- *What the target imposes.* On classes, the target imposes exactly `[e_-] = [eps_-] + [h]` for one
  unknown idempotent `h`. With (1.1) this reads `phi([h]) = -phi([e_-])`. The class
  `-[e_-] = [e_-] - [eps_-]` exists in `K_0` whether or not the target holds. So `phi` can refute
  the target only through a positivity statement about which classes are represented by idempotents,
  and that is Theorem A.
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
Both are additive, and both are covered by (i).

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

By Theorem A, an obstruction is a state on `(K_0(S_-), [eps_-])`. Its natural sources, and why each
fails:
- **Sylvester rank functions on `S_-`,** equivalently homomorphisms into regular rings with a rank
  function. Rank-metric approximations of `G` with `z` acting as `-1` on positive normalized rank
  would give one. That is the `F_3`-linear soficity gate for the anti-central sign, and property (T)
  gives no rank rounding over finite fields (`kazhdan-group-rank-models-admit-no-expander-decomposition`).
- **Finite-dimensional images:** none, by Theorem B(ii).
- **Properly infinite images:** inert, by Theorem B(iii).

So proving that the target cannot hold is at least as hard as proving `S_-` K_0-stably finite.

## 6. The stable target

`ternary-anti-central-unit-class-is-nonpositive` (open) asks for `k >= 1` with `k[eps_-] <= 0`, that
is, `S_-^r ~= S_-^r (+) S_-^k (+) Q`.
- *Position.* It sits strictly between the corner equation, which gives `k = 1` by Theorem A(a), and
  a Gottschalk counterexample on `G_3` (Theorem A(c)).
- *Room.* It allows stabilization and any finitely generated projective `Q`. In `R` the isomorphism
  holds already, since `R ~= R (+) R`. So the lift is a matrix-size problem with more freedom than the
  unstable corner equation.
