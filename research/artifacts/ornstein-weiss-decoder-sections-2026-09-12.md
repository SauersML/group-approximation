# Ornstein–Weiss decoders have no measurable sections, over any group

Lane `w4-measurable-2`, 2026-09-12. This artifact supports `ornstein-weiss-type-decoders-admit-no-measurable-section`.
It also records where the idea "Ornstein–Weiss radius-one codes along free subgroups, combined along the rigid
defect" dies for `measurable-alphabet-compression-over-leavitt-units`.

## 0. Setting

Notation:
- the left shift is `(h.x)(g) = x(h^-1 g)`, and `mu_A` is the uniform product measure on `A^G`;
- a *code* is a Borel `G`-equivariant map between full shifts;
- `Z/n` is written additively, and `omega = exp(2 pi i/n)`.

The Ornstein–Weiss map over `F_2 = <a, b>` is `phi(y)(g) = (y(g) + y(ga), y(g) + y(gb))` on `(Z/2)^(F_2)`.
It pushes the uniform 2-shift onto the uniform 4-shift, and it is two-to-one (Section 4 of
`research/artifacts/decoder-fiber-flip-lifts-2026-09-12.md`). A measurable equivariant section of it would compress 4
symbols into 2.
- **Over `F_2` itself** maximality excludes such a section.
- **Over `U = L_(F_2)(1,2)^x`** the map ascends coset by coset. The fiber over `x` is then
  `(Z/2)^(U/F_2)`: the primitive can be flipped independently on each left coset of `F_2`. A section is free to
  break the flip symmetry of one coset using data from other cosets, for instance along the rigid defect. So the
  ergodicity argument over `F_2` does not transfer, and maximality over `U` is open.

## 1. Lemma K0: a uniform input functional is never a coboundary along one element

**Lemma K0.** Let `G` be countable, `a` in `G`, `A` finite, `n >= 2`, and `lambda: A -> Z/n` with
`lambda_*(uniform) = uniform`. There is no Borel `p: A^G -> Z/n` with

    p(x) - p(a^-1.x) = lambda(x(1))      for mu_A-almost every x.

*Proof.* Put `S(x) = a^-1.x`, so `(S^k x)(h) = x(a^k h)`, and `f(x) = lambda(x(1))`. Every `S^k` preserves
`mu_A`, so the identity holds almost everywhere at every `S^k x` simultaneously:

    p(S^k x) - p(S^(k+1) x) = lambda((S^k x)(1)) = lambda(x(a^k)).

**Finite order.** Let `N` be the order of `a`. Summing over `k = 0, ..., N-1` telescopes the left side to
`p(x) - p(S^N x) = 0`. So `sum_(k<N) lambda(x(a^k)) = 0` almost everywhere. The points `a^k` are distinct, so the
summands are iid uniform on `Z/n`, the sum is uniform, and it vanishes with probability `1/n < 1`.
Contradiction.

**Infinite order.**
- *Invariant function.* On `A^G x Z/n` with `mu_A x uniform`, let `S_f(x, eps) = (Sx, eps + f(x))`, which is
  measure preserving. If `p` solves the equation then `p(Sx) = p(x) - f(x)`, so `F(x, eps) = omega^(eps + p(x))`
  satisfies `F o S_f = F`. But `F(x, eps + 1) = omega F(x, eps)`, so `F` is not almost everywhere constant. It
  suffices to show `S_f` is ergodic.
- *Splitting.* The coordinates split over the right cosets `<a>h`, each preserved by `S`. So `mu_A = mu_1 ⊗ mu_rest`
  with `mu_1` on `A^(<a>)`, and `S = S_1 x S_rest`. Since `f` reads only the coordinate at `1`,
  `S_f = (S_1)_f x S_rest`.
- *`(S_1)_f` is a Bernoulli shift.* Write `w_k = x(a^k)` for `k` in `Z`; these are distinct coordinates, and `S_1`
  is the shift `w -> (w_(k+1))_k`. Since `lambda_*` of uniform is uniform, every fiber `lambda^-1(j)` has `|A|/n`
  points. So `w_k <-> (lambda(w_k), r_k)` with `r_k` uniform on a set of size `|A|/n`, independent of
  `lambda(w_k)`. Define `s` in `(Z/n)^Z` by `s_0 = eps` and `s_(k+1) = s_k + lambda(w_k)` in both directions.
  - The map `(w, eps) -> (s, r)` is a bijection, since `lambda(w_k) = s_(k+1) - s_k`.
  - It carries `mu_1 x uniform` to the uniform product measure: `s_0` is uniform, and the increments are iid
    uniform and independent of `s_0` and `r`.
  - It conjugates `(S_1)_f` to the shift. Indeed `s'_0 = eps + lambda(w_0) = s_1` and `s'_k = s_(k+1)`, and
    likewise `r'_k = r_(k+1)`.

  So `(S_1)_f` is a Bernoulli shift, hence mixing.
- *`S_rest` is mixing.* It is a product of countably many Bernoulli shifts, or trivial when `G = <a>`.
- *Conclusion.* A product of two mixing transformations is mixing, hence ergodic. So `F` is constant, a
  contradiction. QED

## 2. Theorem K: decoders with a two-term difference row have no measurable sections

**Theorem K.** Let `G` be countable, `A, B` finite, `a` in `G`, `n >= 2`, `lambda: A -> Z/n` with
`lambda_*(uniform) = uniform`, and `beta: B -> Z/n` arbitrary. There is no Borel equivariant `tau: A^G -> B^G`
with

    lambda(x(1)) = beta(tau(x)(1)) - beta(tau(x)(a))      for mu_A-almost every x.

In particular, let `sigma: B^G -> A^G` be any map satisfying
`lambda(sigma(y)(g)) = beta(y(g)) - beta(y(ga))` for all `y` and `g`. Then `sigma` has no measurable equivariant
section: there is no Borel equivariant `tau` with `sigma o tau = id` almost everywhere. So no code that is
injective almost everywhere, of any alphabet size, has such a decoder.

*Proof.* Put `p(x) = beta(tau(x)(1))`. Equivariance gives `tau(x)(a) = tau(a^-1.x)(1)`, so the identity reads
`p(x) - p(a^-1.x) = lambda(x(1))` almost everywhere. Lemma K0 excludes this. QED

**Corollary (Ornstein–Weiss, over every group).** Let `F_2 = <a, b> <= G`, and extend `phi` coset by coset to
`(Z/2)^G`. Then `phi` has no measurable equivariant section, whatever coordinates outside `F_2` the section reads.
Take `A = (Z/2)^2`, `B = Z/2`, `n = 2`, `lambda` the first coordinate and `beta = id`. Only the row along `a` is
used, so the same holds for `phi(y)(g) = (y(g) + y(ga), y(g) + y(gd))` with `d` the rigid defect, or for any
element in place of `b`.

**What sections can and cannot differ by.**
- Two sections of the ascended map would differ by a Borel equivariant map into the coset shift
  `(Z/2)^(G/F_2)`.
- `bernoulli-factors-to-infinite-stabilizer-coset-shifts-trivial` forces that map to be constant, so a section
  would be unique up to a global flip.
- Lemma K0 shows there is none at all.

## 3. Ornstein–Weiss codes inside cascades

- **As an encoding stage.** A stage that is linear with a nonzero kernel element `m` is never injective on a
  conull set for the uniform input: `L(y + m) = L(y)`, and `y -> y + m` preserves the uniform measure. The
  ascended `phi` kills the indicator of every left coset of `F_2`. By Step 0 of Theorem G
  (`non-enlarging-sofic-window-cascades-cannot-compress`), every stage of an almost everywhere injective cascade
  is injective for its input. So such a stage cannot follow routing, measure-preserving or alphabet-keeping
  sofic stages.
- **As a parallel track.** `y -> (y, phi(y))` is injective. It is an enlarging stage with window `{1, a, b}` in
  `F_2`, which is the general enlarging regime of Theorem G (Sections 4–5 of
  `research/artifacts/non-expanding-sofic-cascades-2026-09-12.md`). Its redundancy `phi(y)` must later be spent
  by a shrinking stage reading a non-uniform measure.
- **As a decoder.** Excluded by Theorem K.

So the Ornstein–Weiss idea survives only as redundancy added in parallel, with no special structure left to use.

## 4. Where it stops

- **Rows with three or more terms.** Take decoders such as
  `lambda(x(g)) = beta_1(y(g)) + beta_2(y(ga)) + beta_3(y(gd))`, with `d` the rigid defect and no two-term row.
  The coboundary equation becomes a multi-shift functional equation
  `p_1(x) + p_2(a^-1.x) + p_3(d^-1.x) = lambda(x(1))`. There is no single transformation whose skew product carries
  it, and no obstruction is known.
- **Nonlinear decoders** have no obstruction beyond maximality, which is open over `U`.
