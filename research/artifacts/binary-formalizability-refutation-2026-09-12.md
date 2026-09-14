# Binary formalizability is false: one-track automata over bi-orderable groups

Lane `gk-fz-bennett` (family F), 2026-09-12. Supports the established claims
`formalizable-binary-pairs-over-biorderable-groups-are-affine` and
`binary-left-inverse-pairs-need-not-be-formalizable`. The second is the negation of
`binary-left-inverse-pairs-are-formalizable`, and it invalidates the route
`formalizable-pairs-reduce-surjunctivity-to-kaplansky`. The target of that route,
`stable-finiteness-forces-binary-surjunctivity`, stays open.

## 0. Conventions

- **Alphabet:** `F_2`, one track (`n = 1`), unless stated otherwise.
- **Automata:** `tau` has finite memory `M` and local rule `mu`, with `tau(x)(g) = mu((x(gm))_(m in M))`.
- **Representative:** a polynomial `mu~` over `F_2`, in variables indexed by a finite set `M' ⊇ M`,
  that agrees with `mu` on `{0,1}`-points.
- **Composite:** for representatives `tau~`, `sigma~`, the composite `sigma~ o tau~` is computed in
  the polynomial ring `F_2[X_h : h in G]`. Products of memory addresses are computed in `G`.
- **Formalizable pair:** some representatives satisfy `sigma~ o tau~ = id` as a polynomial identity.
- **Window:** the window of a polynomial is the set of group elements whose variables occur in it.
- **Pullback:** for a polynomial map `phi` with components `phi_h`, `phi^*` is the substitution
  homomorphism `Y_h -> phi_h`, and `(psi o phi)^* = phi^* o psi^*`.

## 1. Theorem A: formalizable one-track pairs over bi-orderable groups are affine translations

**Theorem A.** Let `G` carry a total order invariant under left and right multiplication. Let
`tau`, `sigma` be automata on `{0,1}^G` with `sigma o tau = id`, and suppose some representatives
satisfy `sigma~ o tau~ = id` formally. Then there are `m in G` and `eps in F_2` with
`tau(x)(g) = x(gm) + eps` for all `x` and `g`.

**Step 1: `F_2[G]` is a domain, hence directly finite.** Take nonzero `a, b`. Let `g₊`, `h₊` be the
largest elements of their supports. If `g <= g₊` and `h <= h₊`, then `gh <= g h₊ <= g₊ h₊`, by left
and then right invariance, with equality only if `g = g₊` and `h = h₊`. So `g₊h₊` occurs in `ab` with
coefficient `a(g₊) b(h₊) = 1`, and `ab ≠ 0`. In a domain, `ab = 1` gives `(ba − 1) b = 0`, so `ba = 1`.

**Step 2: two-sided formal inverse and algebraic independence.**
- Step 1 makes `M_1(F_2[G])` directly finite. So
  `formal-polynomial-strict-pairs-need-unstable-linearization` (`n = 1`, `k = F_2`) gives
  `tau~ o sigma~ = id` formally.
- Hence `sigma~^* o tau~^* = id`, so `tau~^*` is injective.
- `tau~^*` sends `Y_h` to the translate `mu~_h(X) = mu~((X_(hw))_(w in W))`, where `W` is the window
  of `mu~`. So the translates `(mu~_h)_(h in G)` are algebraically independent over `F_2`.

**Step 3: extreme variables.**
- **Setup.** Let `W` and `V` be the windows of `mu~` and `nu~`, the representative rule of
  `sigma~`. Both are nonempty, since the composite is `X_1`.
  - Put `w₊ = max W`, `w₋ = min W`, `v₊ = max V`, `v₋ = min V`.
  - The composite at cell `1` is `nu~((mu~_v)_(v in V))`.
- **The extreme variable enters once.** `X_(v₊ w₊)` occurs in `mu~_v` only if `v w = v₊ w₊` for some
  `w in W`. By the ordering argument of Step 1, that forces `v = v₊` and `w = w₊`. So it occurs in the
  single argument `mu~_(v₊)`.
- **Its degree.**
  - Write `nu~ = Σ_(d=0..D) nu~_d · Y_(v₊)^d`, with `D >= 1`, `nu~_D ≠ 0`, and no `nu~_d` involving
    `Y_(v₊)`.
  - Write `mu~_(v₊) = Σ_(l=0..E) m_l · X_(v₊w₊)^l`, with `E >= 1`, `m_E ≠ 0`, and no `m_l` involving
    `X_(v₊w₊)`.
  - The composite then has degree exactly `DE` in `X_(v₊w₊)`. Its leading coefficient
    `nu~_D((mu~_v)_(v ≠ v₊)) · m_E^D` is nonzero, because `nu~_D` is a nonzero polynomial, Step 2
    makes the `mu~_v` algebraically independent, and `F_2[X]` is a domain.
- **Both windows are single cells.** The composite is `X_1`, which has degree `1` in `X_1` and `0` in
  every other variable. So `DE = 1` and `v₊ w₊ = 1`. Symmetrically, with minima and lowest terms,
  `v₋ w₋ = 1`. Since `v₋ w₋ <= v₊ w₊` with equality only if `v₋ = v₊` and `w₋ = w₊`, we get
  `W = {m}` and `V = {m^-1}`.

**Step 4: univariate automorphism.** Now `mu~` and `nu~` are polynomials in one variable with
`nu~(mu~(t)) = t`. So `deg mu~ · deg nu~ = 1`, and `mu~(t) = t + eps`. On points,
`tau(x)(g) = x(gm) + eps`. ∎

**The one-track hypothesis is essential.** For `n >= 2`, shears between tracks are formal involutions
(Section 6.2 of `research/artifacts/formal-polynomial-strict-pairs-2026-09-12.md`), so formalizable
pairs on several tracks include many non-affine automata.

## 2. Theorem B: a non-formalizable reversible automaton over Z

On `{0,1}^Z`, let `m(x)_i` be `1` exactly when
`(x_(i−3), x_(i−2), x_(i−1), x_(i+1), x_(i+2), x_(i+3)) = (0, 0, 1, 1, 0, 0)`, and put
`tau(x)_i = x_i + m(x)_i`. Write `F(x) = {i : m(x)_i = 1}`.

**Lemma 2.1: markers exclude each other within distance 3.** If `i in F(x)`, then no `j` with
`1 <= |j − i| <= 3` lies in `F(x)`. The marker at `j` would need a value at `i − 1` or `i + 1` that
contradicts `x_(i±1) = 1`:

| `j − i` | requirement of the marker at `j` | contradicts |
|---|---|---|
| `+1` | `x_(j−2) = x_(i−1) = 0` | `x_(i−1) = 1` |
| `+2` | `x_(j−3) = x_(i−1) = 0` | `x_(i−1) = 1` |
| `+3` | `x_(j−2) = x_(i+1) = 0` | `x_(i+1) = 1` |
| `−1` | `x_(j+2) = x_(i+1) = 0` | `x_(i+1) = 1` |
| `−2` | `x_(j+3) = x_(i+1) = 0` | `x_(i+1) = 1` |
| `−3` | `x_(j+2) = x_(i−1) = 0` | `x_(i−1) = 1` |

**Proposition 2.2: `F(tau x) = F(x)`, so `tau o tau = id`.** `tau x` differs from `x` exactly on
`F(x)`, and the marker at `j` reads only the cells `j ± 1`, `j ± 2`, `j ± 3`.
- **`j in F(x)`.** By Lemma 2.1 no cell within distance 3 of `j` flips, so the marker at `j` still holds.
- **`j not in F(x)`, no flipped cell within distance 3.** The marker at `j` reads unchanged values.
- **`j not in F(x)`, some flipped `i` with `1 <= |j − i| <= 3`.** The table shows the marker at `j`
  needs a contradicting value at `i − 1` or `i + 1`. Those cells are at distance 1 from `i`, so by
  Lemma 2.1 they don't flip either, and the marker at `j` is false for both `x` and `tau x`.

So `F(tau x) = F(x)`, and applying `tau` twice flips each cell of `F(x)` twice. ∎

**Proposition 2.3: `tau` is not an affine translation.**
- **It fixes `δ_0`.** `tau` fixes the configuration with a single `1` at `0`, since every marker needs
  two `1`s. An affine translation `x -> x(· + m) + eps` fixing it has `m = 0` and `eps = 0`, so it is
  the identity.
- **It is not the identity.** On the configuration that is `1` exactly at `−1` and `+1`, the marker
  at `0` holds, so `tau` changes cell `0`. ∎

**Corollary 2.4.** `(tau, tau)` is a left-inverse pair of automata on `{0,1}^Z`, and it is not
formalizable, by Theorem A with `G = Z`. So `binary-left-inverse-pairs-are-formalizable` is false.

**Remark.** Hedlund's automorphism group of the full 2-shift is far larger than the translations and
the complement. By Theorem A, every other reversible one-track automaton over `Z` is non-formalizable
too, so non-formalizable pairs are the generic reversible case.

## 3. Lemma C: the Bennett defect can always be pushed to second order

Let `I` be the ideal of `F_2[X_h : h in G, tracks]` generated by the elements `f_h = X_h^2 + X_h`.

**Lemma C.** Every left-inverse pair on `(F_2^n)^G` has representatives whose Jacobians are the
identity at every `{0,1}`-configuration. For those representatives the Bennett defect
`d(X) = X + sigma~(tau~(X))` lies in `I^2`.

*Proof.*
- **Jacobians can be prescribed.** Adding `f_h · P` to a rule changes its partial derivative in `X_h`
  at a `{0,1}`-point `c` by `P(c)`, because `∂f_h/∂X_h = 2X_h + 1 = 1` and `f_h(c) = 0`. With `P` a
  representative of the finite-memory Boolean field `I + J`, the Jacobian becomes `I`, and the rule
  is unchanged on points.
- **The defect is first-order flat.** At `{0,1}`-points, `J_d(c) = I + J_sigma(tau(c)) J_tau(c)`,
  which is `0` for these representatives.
- **So `d` lies in `I^2`.** Since `d` vanishes on points, `d` lies in `I`.
  - `I/I^2` is free over `F_2[X]/I` on the classes of the `f_h`, because the `f_h` form a regular
    sequence in any finite set of variables.
  - Write `d = Σ_h f_h D_h + e` with `e in I^2`. The derivative of `d` at `c` is `(D_h(c))_h`.
  - It vanishes at every `{0,1}`-point, so each `D_h` lies in `I`, and `d` lies in `I^2`. ∎

**What Lemma C and Theorem B show together.** First-order data at `{0,1}`-points never obstructs
formalizability. For the marker involution the obstruction lies in termination: no polynomial
representatives exist (Theorem B), while the first-order defect can always be removed (Lemma C).

**Remark (heuristic, no claim).**
- **The iteration.** With `J_sigma~ = I`, one can remove the order-`k` part of `d` by adding
  corrections of `I`-order `k` to `tau~` at cell `1`, supported on the window of `d`.
- **Why it doesn't terminate.** Each step enlarges the memory of `tau~` by the memory of `sigma~`.
  Theorem B shows that no strategy of this kind can end at finite degree and finite memory for the
  marker involution.
- **The Bennett map does not decide the stable claims** (corrected after gk-vf-nonlinear,
  Section 24).
  - `V` is formally invertible for every pair, but `V` agrees with `tau × id` only functionally,
    and only on `X_0`. It is not a representative of `tau × id`.
  - So this says nothing about gk-free-neg's `injective-binary-automata-are-stably-formalizable`,
    which asks for formal pairs representing `tau × id` with identity ancilla tracks. That claim
    stays open.

## 3A. Every finite field, one track

Asked by gk-fz-alphabets. Theorems A and B hold over every finite field `F_q`, on one track.

**Theorem A over `F_q`.** Let `G` be bi-orderable, and let `tau`, `sigma` be automata on `F_q^G`
with `sigma o tau = id`, formalizable by `F_q`-polynomial representatives. Then
`tau(x)(g) = a x(gm) + b`, with `a in F_q^×`, `b in F_q` and `m in G`.
- **Step 1.** The leading-term argument makes `F_q[G]` a domain.
- **Step 2.** `formal-polynomial-strict-pairs-need-unstable-linearization` holds for any field `k`.
- **Step 3.** The degree count only uses that the polynomial ring is a domain.
- **Step 4.** In `F_q[t]`, an identity `nu~(mu~(t)) = t` forces `mu~ = at + b` with `a ≠ 0`.

**Theorem B over `F_q`.** Swap the values `0` and `1` of cell `i`, leaving every other value fixed,
exactly when the six-cell marker `(0, 0, 1, 1, 0, 0)` holds around `i`.
- **Lemma 2.1 and Proposition 2.2 carry over.** They only compare the required values `0` and `1` at
  the cells `i ± 1`, which never change. So the marked set is invariant, and `tau` is an involution.
- **Not affine.** `tau` fixes the configuration with a single `1`. An affine translation that fixes
  it has `b = 0`, `m = 0` and `a = 1`, so it is the identity, and `tau` is not.

**Consequence.** Over bi-orderable groups, one-track formalizability is rigid at every prime power.
Formalizable pairs there are the affine translations, and non-affine reversible automata are never
formalizable. On one track, stabilization by extra tracks is essential at every characteristic.
This matches gk-fz-alphabets' result on constants, which sees `q >= 4` over every group but says
nothing at `q = 2`.

## 4. Effect on the graph

- `binary-left-inverse-pairs-need-not-be-formalizable` (established) is the negation of
  `binary-left-inverse-pairs-are-formalizable`, which now lists it under `refuted_by`.
- The route `formalizable-pairs-reduce-surjunctivity-to-kaplansky` is invalidated.
- `stable-finiteness-forces-binary-surjunctivity` stays open, with no route through formalizability.
- On `non-surjunctive-group-with-stably-finite-group-algebras`, "a counterexample is exactly a
  non-formalizable strict pair" is still true. It no longer narrows the search, though: every
  non-affine reversible one-track automaton over `Z` is non-formalizable.
