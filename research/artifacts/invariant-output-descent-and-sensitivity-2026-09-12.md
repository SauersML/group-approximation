# Invariant-output automata: normal form, descent through normalizing memory, sensitivity constraints

Lane `gk-invariant-output`, 2026-09-12. Supports the Cairn claims
`normalizing-invariant-output-descends-to-quotient`,
`invariant-output-rules-need-odd-invariant-monomials` and
`right-symmetric-sensitivity-profile-admits-no-decoder`, all aimed at the open
claim `leavitt-units-carry-injective-invariant-output-automaton`.

## 0. Conventions

`G` is a group, `A` a finite alphabet with `|A| >= 2`, and a cellular automaton is

```text
tau(x)(g) = f( (x(g m))_(m in M) ),     M finite,
```

commuting with left shifts `(k.x)(g) = x(k^-1 g)`. Right translation
`(R_c x)(g) = x(g c)` commutes with left shifts. `M` is the effective memory:
the coordinates on which `f` actually depends. For a finite subgroup `H`, the
output is *invariant* when `tau(x)(g h) = tau(x)(g)` for all `x`, `g` and `h in H`.
By `invariant-output-injective-automata-need-invisible-symmetry` this forces
`h M = M` and invariance of `f` under the relabeling `m -> h m`. Left
multiplication by `H` acts freely on `M`, so the orbits `H m` have size `|H|`.

## 1. Normal form

Choose representatives `m_1, ..., m_r` of the left orbits `H m` in `M`, and put

```text
psi(x)(k) = ( x(k m_1), ..., x(k m_r) )  in A^r,
phi_g^x : H -> A^r,     phi_g^x(h) = psi(x)(g h).
```

**Lemma 1.** `tau(x)(g) = F([phi_g^x])`, where `[phi]` is the class of `phi`
under left translation `phi -> phi(h' .)`, and `F` is `f` read through
`x(g h m_i) = phi_g^x(h)_i`. The class depends only on the coset `gH`, because
`phi_(gk)^x(h) = phi_g^x(k h)`.

*Proof.* `x(g h m_i) = psi(x)(g h)_i`, and invariance of `f` under
`(h, i) -> (h' h, i)` is exactly invariance of `F` under left translation of the
`H`-argument. QED.

For `|H| = 2`, `H = {1, h}`, the class is the unordered pair
`{psi(x)(g), psi(x)(g h)}`. So an invariant-output automaton is a column code
`psi`, then symmetrization over each coset `gH`, then a pointwise compression
`F` from `(A^r)^H / H` down to `A`. Injectivity needs the symmetrized column
configuration to determine `x`, and `F` to be injective on the configurations
that actually occur.

## 2. Descent through normalizing memory

**Proposition 2.** Let `tau` be injective with output invariant under `H != 1`,
and let `K = <M>`. Suppose `M` normalizes `H`, so that `H` is normal in `K`
(`H` lies in `K` because `h = (h m) m^-1`). Then `Q = K/H` carries an injective,
non-surjective automaton over the same alphabet, with memory `{mH : m in M}` and
the same local rule. In particular `Q` is not surjunctive, hence not sofic.

*Proof.* On `A^G` the automaton is the product of independent copies over the
left `K`-cosets, so its copy on `A^K` is injective. Put

```text
Fix_K = { x in A^K : x(k h) = x(k) for all k in K, h in H }.
```

Since `H` is normal in `K`, the left cosets `kH` form the group `Q`, and
`x -> xbar`, `xbar(kH) = x(k)`, identifies `Fix_K` with `A^Q`, equivariantly for
left shifts. For `x` in `Fix_K`,

```text
tau(x)(k) = f( (x(k m))_m ) = f( (xbar(kH . mH))_m ),
```

because `k m H = (kH)(mH)`. So `taubar(xbar)(q) = f((xbar(q . mH))_m)` is an
automaton over `Q` with `taubar(xbar) = bar(tau(x))`; the output of `tau` lies in
`Fix_K` by invariance. `taubar` is injective because `tau` is. Since `H != 1` and
`|A| >= 2`, `Fix_K` is a proper subset of `A^K`, so injectivity gives

```text
tau(Fix_K)  proper subset of  tau(A^K)  contained in  Fix_K,
```

that is, `taubar` is not surjective. QED.

**Reading.** When the memory normalizes the symmetry, the invariant output buys
nothing: the automaton is a strict automaton on the quotient memory group in
disguise, and whoever holds it already holds a Gottschalk counterexample on
`K/H`. Only the forward direction is proved. A strict automaton on `Q` does not
give an invariant output on an extension, since that needs halving the
information per coset. The same applies to any nontrivial `H' <= H` normalized
by `M`, since the output is invariant under `H'` too.

**Over the binary Leavitt unit group.** Identify `R = L_(F_2)(1,2)` with
`M_2(R)`, so `R^x = GL_2(R)` and `w = s0 t1 + s1 t0` is `[[0,1],[1,0]]`. Then
`N(<w>) = C(w) = { [[a,b],[b,a]] }`, the units of `R[x]/(x^2 - 1) = R[eps]/(eps^2)`
with `eps = 1 + x`. So `C(w) = R^x semidirect (R, +)`, where `a` acts on `R` by
conjugation and `w = 1 + eps` corresponds to `1 in R`. Designs with `H = <w>`
whose memory commutes with `w` therefore yield strict automata on subgroups of
`C(w)/<w> = R^x semidirect (R / F_2 1)`. That group contains `R^x`, so this is a
reduction, not a kill: such designs are exactly as hard as a strict automaton on
their quotient memory group. A design that genuinely uses the symmetry must have
memory outside `C(w)`.

## 3. Algebraic normal form constraints over `F_2`

Let `A = F_2`, `|H|` even, and `h in H` an involution. Write `f` in algebraic
normal form, `f = c + sum_m a_m x_m + (monomials of degree >= 2)`.

**Proposition 3.** If `tau` is injective with output invariant under `H`, then:

1. `a != 0`, and `a_(h m) = a_m`, so `supp a` has even size.
2. The number of `h`-invariant monomials in `f` is odd. Each has degree at least `2`.
3. In particular a *norm rule*, one all of whose monomials are `h`-invariant
   (products over unions of orbits `{m, hm}`), is never injective.

*Proof.* (1) Injectivity gives `tau(e_1) != tau(0)`, where `e_k` is the
configuration equal to `1` at `k` only. The two outputs differ at some `g`, so
`f(e_m) != f(0)` for some `m`, and in normal form `f(e_m) - f(0) = a_m`.
Relabeling invariance gives `a_(hm) = a_m`, and `m -> hm` has no fixed point.
(2) An injective automaton permutes the constant configurations, so
`f(1,...,1) != f(0,...,0)`. The difference is the number of nonconstant
monomials mod `2`. Relabeling by `h` permutes the monomials; the non-invariant
ones fall into pairs, so the invariant ones are odd in number. No variable
`x_m` is invariant, since `hm != m`. (3) A norm rule has `a = 0`, contradicting (1). QED.

## 4. Right-symmetric sensitivity profiles admit no decoder

This holds over every group and needs no invariant output. Identify `A` with
`Z/n` and fix `b != 0`. The *sensitivity profile* is

```text
p_b : G -> Z/n,     p_b(m) = f(b e_m) - f(0)  for m in M,   p_b(m) = 0 otherwise,
```

where `b e_m` is `b` at `m` and `0` elsewhere on `M`.

**Theorem 4.** Suppose `sigma tau = id` for an automaton `sigma` of any degree.
Then for every `b != 0`, `p_b` is not invariant under right multiplication by any
element `c` whose order is divisible by `n`. (A right symmetry of infinite order
is impossible anyway: `p_b` has finite support and is nonzero by injectivity.)

*Proof.* `tau(b e_k)(g) = f(0) + p_b(g^-1 k)`, so `tau(b e_k) = f(0) + P_k` with
`P_k(g) = p_b(g^-1 k)`. Let `D(k) = sigma(f(0) + P_k)(1) - sigma(f(0))(1)`. Since
`sigma tau = id`, `D(1) = b` and `D(k) = 0` for `k != 1`, so `sum_k D(k) = b`. The
sum is finite: `D(k) = 0` unless `P_k` meets the memory `S` of `sigma`. If
`p_b(m c) = p_b(m)` for all `m`, then `P_(kc) = P_k`, so `D(kc) = D(k)`. The finite
support of `D` is then a union of right `<c>`-orbits, each of size `ord(c)`,
because right multiplication by `c^j != 1` fixes no point. Each orbit contributes
`ord(c) D(k) = 0` in `Z/n`. Hence `sum_k D(k) = 0 != b`. QED.

**Consequences for invariant-output designs over `F_2`.** The linear support
`A_1 = supp a` is a union of left `H`-orbits. By Theorem 4 it must not be a union
of right `<c>`-orbits for any `c` of even order. A single orbit `{k, hk}` is
right-invariant under the involution `k^-1 h k`, so an encoder whose linear
part is `k + hk` has no decoder of any degree. The linear support must spread
over at least two left orbits, arranged with no even-order right symmetry.

For a linear decoder, the same count reads `eps(d) |A_1| = 1`, which is the
augmentation argument of `invariant-output-automata-have-only-nonlinear-decoders`.
Theorem 4 is its right-symmetry analogue for decoders of every degree.

## 5. What remains of the architecture over `R^x`

A candidate for `leavitt-units-carry-injective-invariant-output-automaton`
with an involution symmetry over `F_2` must have:

- effective memory not normalizing `H` (Proposition 2), for `H = <w>` memory outside `C(w)`;
- nonzero linear part of even support, spread over at least two left `H`-orbits,
  with no even-order right symmetry (Proposition 3, Theorem 4);
- an odd number of `h`-invariant monomials of degree at least two (Proposition 3);
- a genuinely nonlinear decoder (`invariant-output-automata-have-only-nonlinear-decoders`);
- product tables presenting a nonsofic group with `x_h` invisible
  (`strict-automaton-tables-present-an-invisible-window-difference`).

None of this constructs an automaton or excludes one over `R^x`.

## 6. The honest-idempotent form in characteristic three

Over `F_2` an involution-invariant output forbids linear rules. Over `F_3` it does
not. By `linear-invariant-output-automata-fail-augmentation` (part 3), for an
involution `w` and `e = 2(1 + w)`, the averaging idempotent in characteristic `3`,
an injective `F_3`-linear automaton with `<w>`-invariant output exists iff
`c e b = 1` for some `b, c` in `F_3[G]`. The automaton is `tau_(eb)`, with left
inverse `tau_c` (`tau_a tau_b = tau_(ab)`). By
`invariant-output-injective-automata-need-invisible-symmetry` it is not surjective.

The natural host is `G_3 = L_(F_3)(1,2)^x`, nonsofic by
`d-ary-leavitt-groups-nonsofic-over-finite-fields`. There
`w = s0 t1 + s1 t0` is an involution: `w^2 = s0 t0 + s1 t1 = 1`.

**The image solves the corner equation.** In `R_3 = L_(F_3)(1,2)` put
`bbar = s0 + s1` and `cbar = 2(t0 + t1)`. Then

```text
cbar bbar = 2(t0 s0 + t0 s1 + t1 s0 + t1 s1) = 2 * 2 = 1,
w s0 = s1,  w s1 = s0,  so  e bbar = 2(2 s0 + 2 s1) = s0 + s1 = bbar,
```

hence `cbar e bbar = 1`, while `(e bbar) cbar = 2(s0 + s1)(t0 + t1)` is an idempotent
below `e`, so it is not `1`. In `M_2(R_3)` coordinates `e = 2[[1,1],[1,1]]` is the
projection onto the diagonal copy of `R_3`, which is isomorphic to `R_3`.

**What this form changes.** Over `F_2` the half projection `s0 t0` is the image of
`(1 + u)(1 + v)`, which is not idempotent in `F_2[G]`. Here `e` is an honest
idempotent of the group algebra. The question is exactly whether the right
permutation module `e F_3[G_3] = F_3[<w>\G_3]` contains `F_3[G_3]` as a direct
summand. Two standard obstructions say nothing here:

- the canonical trace gives `tr(e) = 2` in `F_3`, and traces of idempotents are not
  ordered in characteristic `3`, so the characteristic-zero Kaplansky argument is
  unavailable;
- augmentation gives `eps(e) = 2 * 2 = 1`, with no contradiction.

The obstruction that does bind is soficity: linear soficity forces stable
finiteness (`linear-sofic-group-algebra-is-stably-finite`). So the product
coincidences of any certificate must present a group outside that class. The
lifting problem from `R_3` to `F_3[G_3]` is the same wall as the binary Kaplansky
lift (`direct-finiteness-not-inherited-by-quotients`). No certificate is claimed.
Section 7 shows that this lift addresses only the anti-central half of `F_3[G_3]`,
and that half proves nothing about the full shift.

## 7. The central involution splits the ternary problem

Notation: `k = F_3`, `R = L_k(1,2)`, `G = R^x`, `S = k[G]`, `z = -1` in `G` (central,
order two), `PG = G/<z>`, `w = s0 t1 + s1 t0`, `d = s0 t0 - s1 t1`, `e = 2(1 + [w])`.

**Lemma 7.1 (splitting).** `eps_+ = 2(1 + [z])` and `eps_- = 2(1 - [z])` are central
idempotents with `eps_+ eps_- = 0` and `eps_+ + eps_- = 1`. So `S = S_+ x S_-` with
`S_(+-) = eps_(+-) S`. Also `eps_+ [g] -> [gbar]` gives `S_+ ~= k[PG]`, and
`eps_- [z] = -eps_-`.

*Proof.* `(1 +- z)^2 = 2(1 +- z)`, so `(2(1 +- z))^2 = 8(1 +- z) = 2(1 +- z)`. The sum is
`4 = 1` and the product is `4(1 - z^2) = 0`. `S_+ = S/eps_- S = S/(1 - [z])S = k[PG]`,
and `eps_- z = 2(z - 1) = -eps_-`. QED

**Lemma 7.2 (the sign unit halves the swap idempotent on `S_-`).** In `G`, `w^2 = 1`,
`d^2 = 1` and `d w d = z w`. Put `1_- = eps_-` and `e_- = eps_- e`. Then
`[d] e_- [d] = 1_- - e_-`. So `E_11 = e_-`, `E_22 = 1_- - e_-`, `E_21 = [d] e_-` and
`E_12 = e_- [d]` are matrix units, `S_- ~= M_2(T)` with `T = e_- S_- e_-`, and `S_-`
has no unital ring homomorphism to a nonzero commutative ring.

*Proof.* `d^2 = s0 t0 + 4 s1 t1 = 1`, `w d = s1 t0 - s0 t1` and `d(w d) = -w = z w`. In
`S_-`, `[d][w][d] = [z][w] = -[w]`. So `[d] e_- [d] = 2 eps_-(1 - [w])`, and
`1_- - e_- = eps_-(1 - 2 - 2[w]) = 2 eps_-(1 - [w])`. Since `d = d^-1`,
`E_12 E_21 = e_- d d e_- = e_-` and `E_21 E_12 = d e_- d = E_22`. A unital homomorphism
to a commutative ring gives `E_11` and `E_22` the same image. They sum to `1` and
multiply to `0`, which forces `1 = 0`. QED

**Proposition 7.3 (the anti-central half is a Cohn family).** `c e_- b = 1_-` has a
solution in `S_-` iff `T` contains `beta_1, beta_2, gamma_1, gamma_2` with
`gamma_i beta_j = delta_ij e_-`.

*Proof.* In `S_- = M_2(T)`, `e_- = diag(e_-, 0)`. A solution gives `beta = e_- b`, a
matrix with one nonzero row `(beta_1, beta_2)`, and `gamma = c e_-`, with one nonzero
column `(gamma_1, gamma_2)`. `gamma beta = I` reads `gamma_i beta_j = delta_ij`.
Conversely such a family defines `beta` and `gamma` with `gamma e_- beta = gamma beta = I`. QED

The Leavitt evaluation `pi` maps `S_-` onto `R` and `T` onto `pi(e) R pi(e) ~= R`. There
`b = s0 + s1` and `c = 2(t0 + t1)` from Section 6 give such a family.

**Proposition 7.4 (which half matters).**

(a) `pi(eps_+) = 0`, so `pi` factors through `S_-`.
(b) If `c e b = 1` in `S`, then `cbar ebar bbar = 1` in `k[PG]`, with `ebar = 2(1 + [wbar])`.
(c) If `cbar ebar bbar = 1` in `k[PG]`, then `PG` is not surjunctive.
(d) Put `X_- = {x in k^G : x(gz) = -x(g)}`, a proper closed linear subshift. Every
linear automaton preserves `X_-`, and on `X_-` it depends only on the `S_-` component
of its coefficient. So a solution in `S_-` alone gives at most an injective,
non-surjective self-map of a proper subshift. Such a map carries no surjunctivity
content (`subshift-self-embedding-carries-no-surjunctivity-content`).

*Proof.* (a) `pi(z) = -1`. (b) Multiply by `eps_+` and apply Lemma 7.1. (c) `wbar != 1`
because `w` is not a scalar, so Proposition C(3) and Corollary B apply over `PG`.
(d) `z` is central, so on `X_-`, `tau_a(x)(gz) = sum_m a_m x(g m z) = -tau_a(x)(g)`.
Also `tau_(1 + z)` vanishes on `X_-`, so `tau_(y(1 + z)) = tau_y tau_(1 + z)` vanishes there. QED

So Section 6's lift along `pi` is aimed at the half that proves nothing, and the half
that suffices is invisible to `pi`.

**Remark 7.5 (the adjoint evaluation sees `S_+`).** `rho([g]) = g (x) (g^-1)^op` defines a
unital ring homomorphism `rho : S -> Q = R (x)_k R^op`, because inversion reverses
products and so does `R^op`. `rho([z]) = (-1) (x) (-1) = 1`, so `rho` kills `S_-`. Put

```text
b' = (s0 + s1) (x) (t0 + t1)^op,      c' = (t0 + t1) (x) (s0 + s1)^op.
```

From `w (s0 + s1) = s0 + s1` and `(t0 + t1) w = t0 + t1`,
`rho(ebar) b' = 2(b' + b') = b'`. And `c' b' = (t0 + t1)(s0 + s1) (x) ((t0 + t1)(s0 + s1))^op = 2 (x) 2 = 1`.
So the equation of 7.4(b) holds in `Q`. Whether witnesses can be taken in `rho(S)`, the
span of the `g (x) (g^-1)^op`, and then lifted, is open. This is the right guide for
`projective-ternary-swap-idempotent-is-full`.

**Screening against the team filters.** A certificate for that claim must also satisfy:

- the memory of `c` generates a nonamenable subgroup
  (`amenable-decoder-memory-forces-surjectivity`);
- the forward table of the pair has a nonsofic two-core
  (`forward-relations-of-a-counterexample-have-a-nonsofic-core`);
- `PG` is not linear sofic (`linear-sofic-group-algebra-is-stably-finite`);
- the image lies in the `<wbar>`-invariant configurations, a Bernoulli-null set, as
  `injective-measure-preserving-ca-is-surjective` requires of a strict automaton.

None of these excludes the architecture.
