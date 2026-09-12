# Table realizations, algebraic-subshift rigidity, and the permanence closure

Date: 2026-09-12. Fork `gottschalk-leavitt-ca`. Handwritten proofs; no computation.

This note maps what a counterexample to Gottschalk's conjecture must evade.

- **Theorem A** transports a strict certificate to every group that realizes its
  product tables. Collisions are allowed; only the cells the Garden-of-Eden pattern
  distinguishes must stay apart.
- **Theorem B** shows that a full shift maps only constantly into a linear subshift
  cut out by a two-sided ideal, over an icc group. This closes every design that
  feeds the Leavitt subshift into a full shift.
- **Theorem C** takes the closure of the sofic groups under every surjunctivity
  permanence result now available. No finitely presented infinite simple nonsofic
  group embeds in it, so none of those results can touch the binary Leavitt unit
  group.

No counterexample is constructed here.

## 0. Conventions

The conventions are those of `gottschalk-sofic-radical-localization-2026-09-11.md`.

A cellular automaton over a group `G` has a finite alphabet `A` and a memory
`M = (m_1, ..., m_r)` containing `1`. It computes

    tau(x)(g) = f(x(g m_1), ..., x(g m_r))

and commutes with `(h.x)(g) = x(h^-1 g)`.

A **strict pair** over `G` is a triple `(tau, sigma, p)`:
- `tau` and `sigma` are automata with memories `M` and `S`, both containing `1`,
  and local rules `f` and `d`;
- `sigma tau = id`;
- `p` is a pattern in `A^Omega` on a finite set `Omega`, and no `tau(x)` displays
  `p` on `Omega`.

`G` is surjunctive iff it carries no strict pair
(`leavitt-unit-certificate-predicates-are-decidable`).

The **window data** of a strict pair is the finite set
`F = {1} ∪ M ∪ S ∪ Omega ∪ SM ∪ Omega M`, together with the products `s m`
(`s in S`, `m in M`) and `w m` (`w in Omega`, `m in M`).

## 1. Transport to table realizations

**Definition.** A **realization** of the window data in a group `K` is a map
`phi: F -> K` with

    phi(s m) = phi(s) phi(m)     for s in S, m in M,
    phi(w m) = phi(w) phi(m)     for w in Omega, m in M,
    phi(w) != phi(w')            whenever p(w) != p(w').

Injectivity is not assumed anywhere else: `phi` may identify cells of `SM` or of
`Omega M`. Since `1` lies in both `S` and `M`, we get `phi(1) = phi(1)^2`, so
`phi(1) = 1`.

**Theorem A.** Suppose `G` carries a strict pair and `K` realizes its window data.
Use the same local rules on the memories `phi(M)` and `phi(S)`, and the pattern
`p_K(phi(w)) = p(w)` on `phi(Omega)`. These form a strict pair over `K`. In
particular `K` is not surjunctive.

*Proof.* `p_K` is well defined by the separation condition. Let `tau_K` and
`sigma_K` be the automata over `K` with memories `(phi(m_i))_i` and `(phi(s_j))_j`
and local rules `f` and `d`.

*Decoder identity.* Fix `z` in `A^K` and `k` in `K`. Then

    sigma_K tau_K(z)(k) = d( f( z(k phi(s_j) phi(m_i)) )_i )_j
                        = d( f( z(k phi(s_j m_i)) )_i )_j.

Put `x(c) = z(k phi(c))` for `c` in `SM`. This is a function on the subset `SM` of
`G`, because `phi` is a function; a collision of `phi` only forces two values to
agree. Extend `x` arbitrarily to `A^G`. Since `1 = 1·1` lies in `SM`, we have
`x(1) = z(k)`. Evaluating `sigma tau = id` at `1` gives
`d( f(x(s_j m_i))_i )_j = x(1)`, and the left side is the displayed expression. So
`sigma_K tau_K = id`.

*Garden of Eden.* Suppose `tau_K(z)` displays `p_K` on `phi(Omega)`. For `w` in
`Omega`,

    p(w) = tau_K(z)(phi(w)) = f( z(phi(w) phi(m_i)) )_i = f( z(phi(w m_i)) )_i.

Put `x(c) = z(phi(c))` for `c` in `Omega M` and extend to `A^G`. Then
`tau(x)(w) = p(w)` for every `w` in `Omega`, contradicting the choice of `p`. QED.

Lemma 3.1 of `lef-graph-wreath-surjunctivity-2026-09-12.md` is the case where
`phi` is injective. Dropping injectivity costs nothing, since both halves of the
proof only pull a `K`-configuration back to a `G`-pattern along `phi`. A pullback
along a non-injective map is still a pattern. Injectivity matters only where
`p_K` must be defined, which is the separation condition.

**Corollary A1 (local embeddings).**
- A group is surjunctive if every finite subset of it embeds, as a partial
  multiplication table, into some surjunctive group.
- Equivalently, the surjunctive groups form a closed subset of the space of marked
  groups. A marked group close enough to `G` agrees with `G` on a ball containing
  `F`, which gives an injective realization.

**Corollary A2 (quotient folding).** Let `(tau, sigma, p)` be a strict pair over
`G`, and put `H = <M ∪ S ∪ Omega>`. For every homomorphism `psi: H -> K` into a
surjunctive group, `psi(w) = psi(w')` for some `w, w'` in `Omega` with
`p(w) != p(w')`. In particular, every normal `N` in `H` with `H/N` surjunctive
contains `w^-1 w'` for such a pair.

*Proof.* The restriction of `psi` to `F` is multiplicative, so it realizes the
window data unless it merges a `p`-distinct pair. QED.

**Comparison with `sofic-radical-localizes-garden-of-eden-windows`.** Neither
statement contains the other.
- That theorem folds a window difference in every almost-multiplicative permutation
  model of the memory group. It is finer toward sofic targets.
- Corollary A2 folds one in every exact homomorphism onto any surjunctive group.
  This includes the nonsofic surjunctive groups of `surjunctive-nonsofic-group-exists`
  and everything in the closure of Section 3.

**Corollary A3 (table groups).** Let `U` be the table group of Theorem F of the
localization artifact: generators `x_a`, relators recording the coincidences of
`SM` and of `Omega M`. The assignment `a -> x_a` realizes the window data, and the
same assignment followed by `U -> G` separates `Omega`. So:
- `U` is not surjunctive;
- every homomorphism from `U` into a surjunctive group merges some `p`-distinct pair
  `x_w`, `x_w'`.

For the invariant-output architecture take `Omega = {1, h}`, `p = (0, 1)`, and
relators `x_h x_m = x_(hm)`. There every homomorphism from `U` into a surjunctive
group kills `x_h`.

**Reading.**
- The set of groups carrying a given strict certificate is closed under realizations.
- Non-surjunctivity is an open condition in the space of marked groups, and
  surjunctivity a closed one.
- Corollary A3 gives a rule-independent filter on candidate windows. If some finite
  group, or any group already known to be surjunctive, realizes the products of
  `S x M` and `H x M` with `h != 1`, then no pair of local rules on those windows is
  strict. The rules never need to be examined.

## 2. Full shifts map only constantly into two-sided algebraic subshifts

Let `p` be a prime and `G` a group. For a subset `I` of `F_p[G]` put

    X_I = { x in F_p^G : <x, r> = sum_g x(g) r_g = 0 for all r in I }.

If `I` is a left ideal, `X_I` is closed and invariant, because
`<h.x, r> = <x, h^-1 r>`. If `I` is also a right ideal, `X_I` is invariant under
right translations as well, since `<x(. k), r> = <x, r k^-1>`.

**Theorem B.** Let `G` be icc, meaning every nontrivial element has infinitely many
conjugates. Let `I` be a nonzero two-sided ideal of `F_p[G]` and `A` a finite
alphabet. Then every continuous equivariant map `F: A^G -> X_I` is constant. Its
value is a constant configuration `c` with `c · eps(r) = 0` for all `r` in `I`,
where `eps` is the augmentation.

*Proof.* By Curtis--Hedlund--Lyndon, `F(y)(g) = f( y(g d) )_(d in D)` for a finite
set `D` and a local rule `f`. Take a nonzero `r` in `I`, with support
`{g_1, ..., g_n}` and nonzero coefficients `c_i`. For every `k` in `G`, the element
`rk` lies in `I`, so for every `y`

    (B1)    sum_i c_i f( y(g_i k d) )_(d in D) = 0.

Choose `k` to make the windows disjoint.
- For `i != j` put `a_ij = g_i^-1 g_j`, which is not `1`. The windows `g_i k D` and
  `g_j k D` meet iff `k^-1 a_ij k` lies in `D D^-1`.
- For fixed `a` and `b`, the solutions `k` of `k^-1 a k = b` are empty or a right
  coset of the centralizer `C(a)`. So the bad `k` form a finite union of right
  cosets of the `C(a_ij)`.
- Each `C(a_ij)` has infinite index, because `a_ij` has infinitely many conjugates.
- By B. H. Neumann's lemma, a group is not a finite union of cosets of
  infinite-index subgroups. So some `k` makes the `n` windows `g_i k D` pairwise
  disjoint.

For that `k`, the tuple `(y|_(g_i k D))_i` ranges over all of `(A^D)^n`, and (B1)
reads

    sum_i c_i f(a_i) = 0     for all a_1, ..., a_n in A^D.

Vary `a_1` alone: since `c_1` is invertible, `f` is constant. So `F(y)` is the
constant configuration `c = f`, independent of `y`, and `<c, r> = c · eps(r) = 0`.
QED.

**The right-ideal hypothesis is essential.** Take a left ideal `I = F_p[G] a`.
With the checker's convention `tau_a(x)(g) = sum_(h in supp a) a_h x(gh)`, the
subshift `X_I` is the kernel of `tau_a`. It receives the nonconstant automaton
`tau_b` whenever `ab = 0` and `b != 0`, since `tau_a tau_b = tau_(ab)`. The
Kaplansky lane lives on these one-sided kernels, and Theorem B says nothing
against it.

**Corollary B1 (the Leavitt subshift is invisible from full shifts).**
- *Setting.* Let `G = L_(F_2)(1,2)^x` and `pi: F_2[G] -> L_(F_2)(1,2)` the
  evaluation, with kernel `K`, and put `X = K^perp = X_K`. This is the subshift of
  `leavitt-kernel-annihilator-strict-self-embedding`.
- *Hypotheses of Theorem B hold.* `K` is a two-sided ideal. It is nonzero: the
  standard unit `g = uv` of order three, with `u = 1 + s_0 t_1` and
  `v = 1 + s_1 t_0`, acts on the corner `M_2(F_2)` as `[[0,1],[1,1]]`. That matrix
  satisfies `x^2 + x + 1`, so `[1] + [g] + [g^2]` lies in `K`. `G` is icc because
  it is infinite and simple (`binary-leavitt-unit-group-is-simple`).
- *Conclusion.* Since `eps([1] + [g] + [g^2]) = 1`, the only constant configuration
  in `X` is `0`. So every automaton from any full shift into `X` is identically
  zero.

**Consequences for designs.**
- *No absorption.* `X` carries the strict self-embedding `T_a`, and it would be
  natural to try `A^G ≅ W × X`, which with `X ≅ X × X` would give
  `A^G ≅ A^G × X` and hence a strict automaton. The projection to `X` would be a
  nonzero automaton from a full shift into `X`, so no such conjugacy exists. More
  generally, `X` is not a factor of any full shift, through any nonlinear
  intermediary: composing with a conjugacy onto `X` only gives another automaton
  into `X`.
- *Other quotient rings.* The same holds for the dual subshift of every quotient
  `F_p[G] -> R` with nonzero kernel, over any icc group. The defect of a quotient
  ring, the lesson of `direct-finiteness-not-inherited-by-quotients`, is invisible
  to the full shift, not only uninherited.
- *Scope.* This complements `subshift-self-embedding-carries-no-surjunctivity-content`,
  which shows the subshift embedding exists over free groups too. Theorem B shows
  instead that the full shift cannot reach the subshift at all. It says nothing
  about kernels of one-sided linear automata, or about nonlinear subshifts.
