# Residual finiteness of finite presentations is Pi-zero-two complete: part 2

Lane `ex-complexity-sofic`, 2026-09-12.  Notation from part 1
(`research/artifacts/rf-fp-pumped-minsky-part1-2026-09-12.md`).

> **Review correction (2026-09-13, `ex-verify-logic-quantum`, `0ab2ae254f`).**
> `G = G(P(M))` below means `G_0(P(M))`, the KMS group with the stop relations
> `x_(q_0 w) = 1`.  B4 writes `w in T` in the basis of `T_1`, which needs
> `T -> T_1` to be injective.  That holds for `G_0`
> (`kms-group-with-stop-relations-simulates-all-words`, clause 3) and fails for
> the displayed `G(M)`.  B1--B3 and the invariance of `F` are unaffected and
> were re-derived by the reviewer (PASS).

## 4. Lemma B (halting machines give residually finite groups)

Call a deterministic machine *simple* if each command number carries either
one Add command, or a pair `i; e_n > 0 -> Sub(n); j` and
`i; e_n = 0 -> j'` on a single glass `n`.

**Lemma B.**  Let `M` be simple, deterministic, clocked, and *universally
halting*: every forward computation from every configuration is finite.  Then
`G(P(M))` is residually finite.

### B1. Finite classes in `S(M)`

A nonzero element of `S(M)` with a `q`-letter is represented by a *partial
word* `V = q_i a^l A^al` (`al in {0,1}^K`, Lemma 3.4).  A Minsky relation
applies to `V` modulo commutativity exactly when the corresponding command
applies to the *partial configuration*.

- An Add always applies.
- A Sub on `n` applies when `l_n >= 1`.
- A zero test on `n` applies when `al_n = 1` and `l_n = 0`, because `a_n` and
  `A_n` do not commute.

Along a chain of nonzero words only commutativity and Minsky relations occur,
since Minsky relations map subwords of configuration words to such subwords.
So the words equal to `V` are the partial configurations joined to `V` by
`Sym(M)`.

Simplicity makes the domains of distinct commands disjoint on partial
configurations, so Lemma 2.1 applies: every such word is reached from `V` by
forward steps followed by backward steps.

- *Forward.*  The forward computation from `V` is a prefix of the forward
  computation from the full configuration with the same coin counts (a missing
  `A_n` can only block a zero test).  It is therefore finite.
- *Backward.*  A backward computation of length `L` starting at a word `Y`
  (the end of a forward part) reverses a forward computation of length `L`
  ending at `Y`, which adds at least `floor(L/2)` coins to `tau`.  So
  `L <= 2 l_tau(Y) + 1`.  The forward part has finitely many end words, and
  backward branching is finite, so there are finitely many backward
  computations.

Hence every nonzero element of `S(M)` has finitely many representative words.
Nonzero elements without a `q`-letter admit only commutativity.        (B1)

### B2. The elements of `S(P(M))`

Let `X = q_i a^l a_pi^m a_rho^m' A^al A_pi^be A_rho^be'` be a nonzero partial
word of `P(M)`, and let `pr(X) = q_i a^l A^al` be its `M`-part.

**(i)** If `X = X'` are nonzero in `S(P(M))`, then:

- `pr(X) = pr(X')` in `S(M)`;
- the sets of `A`-letters agree;
- `iota(X) = iota(X')`, where `iota = m - m' - l_tau`.

Every relation along a nonzero chain projects to an `M`-relation or to the
identity (pumps).  A drain produces `q_0`, so it cannot occur in a nonzero
chain.  `A`-letters are never created or destroyed, and `iota` is (INV).

**(ii)** Conversely, suppose `pr(X) = pr(X')` in `S(M)`, the `A`-letter sets
agree, and `iota(X) = iota(X')`.  Then `X = X'` in `S(P(M))`.  Proof:

1. Pump `X` up `p` times, with `p` larger than the length of an `M`-chain from
   `pr(X)` to `pr(X')` and larger than `m'(X')`.  A pump needs only the
   `q`-letter.
2. Lift the chain.  Forward Adds add `a_tau a_pi`.  Backward Adds remove them,
   which is possible because `m >= p` exceeds the number of backward steps.
   Other commands do not involve `pi` or `rho`.
3. At `pr(X')` the exponents are `(m'', m'(X) + p)`, and by (INV)
   `m'' - m'(X) - p = m(X') - m'(X')`.
4. Unpump `m'(X) + p - m'(X')` times.  Both exponents stay `>= 1` before each
   step, and the result is `X'`.

**(iii)** `X = 0` in `S(P(M))` iff either `pr(X) = 0` in `S(M)`, or
`be = be' = 1` and `iota(X) = -l_tau(V')` for some word `V'` equal to
`pr(X)` in `S(M)`.

- *If.*  Lift an `M`-chain to command `0` as in (ii).  Otherwise use (ii) to
  move to `(V'; 0, 0)` and drain.
- *Only if.*  The step producing `q_0` is either an `M`-command into `0`,
  which projects to a chain showing `pr(X) = 0`, or a drain at a word with
  `m = m' = 0`, `be = be' = 1` and `M`-part in the class of `pr(X)`, where
  `iota = -l_tau`.

So a nonzero `q`-element of `S(P(M))` is determined by the class of `pr(X)` in
`S(M)`, its `A`-letter set, and the integer `iota`.                  (B2)

### B3. One finite quotient separating finitely many elements

Let `u_1..u_r` be distinct nonzero `q`-elements of `S(P(M))`, and `v_1..v_k`
distinct nonzero `q`-elements of `Š(P(M))` (normal forms up to commutativity).
By (B1) the class of each `pr(u_s)` is a finite set `C_s` of words.

Choose `R` exceeding every exponent of `a_1..a_K` in the words of the `C_s`
and in the `v_t`.  Choose `D` exceeding `|iota(u_s)| + max_(C_s) l_tau` for
all `s`, the numbers `|iota(u_s) - iota(u_t)|` for all `s, t`, and the
exponents of `a_pi, a_rho` in the `v_t`.

- `S̄` is `S(P(M))` with the extra relations `a_pi^D = a_pi^(2D)` and
  `a_rho^D = a_rho^(2D)`.
- `I_R` is the set of elements of `S̄` represented by some word with an
  exponent `>= R` of some `a_j`, `j <= K`, together with `0`.  It is an ideal.
- `S_fin = S̄ / I_R` is the Rees quotient.
- `Š_fin` is built from `Š(P(M))` the same way.

**(a) Finiteness.**  A nonzero element of `S_fin` has no representative with
an `M`-exponent `>= R`, and its `pi, rho` exponents reduce below `2D`.  There
are finitely many such words, so `S_fin` is finite, and likewise `Š_fin`.

**(b) Nonzero images.**  Along a chain of nonzero words in `S̄`, the `S(M)`
class of the `M`-part, the `A`-letter set, and `iota mod D` are invariant (the
new relations move an exponent by `D`).

- *`u_s notin I_R`.*  Every `S̄`-representative of `u_s` has `M`-part in
  `C_s`, so all its `M`-exponents are `< R`.
- *`u_s != 0` in `S̄`.*  A chain to `q_0` ends with an `M`-command into `0`,
  impossible since `pr(u_s) != 0`, or with a drain at `(V'; 0, 0)` with
  `V' in C_s`.  The drain forces `iota(u_s) = -l_tau(V') mod D`, and since both
  sides are smaller than `D` in absolute value this is an equality.  That
  contradicts (B2)(iii).

**(c) Distinct images.**  If `u_s` and `u_t` have the same nonzero image, they
are equal in `S̄`.  Their `M`-parts then lie in one class, their `A`-letter
sets agree, and `iota(u_s) = iota(u_t) mod D`, hence exactly.  By (B2)(ii),
`u_s = u_t`.  In `Š_fin` there are no Minsky relations and the exponents are
below `R` and `D`, so the `v_t` stay distinct and nonzero.

**(d) Compatibility.**  If `v in Š(P(M))` dies in `Š_fin`, then `vA_0` (an
element of `W_0`) dies in `S_fin`.  If `v = v'` in `Š_fin`, then
`vA_0 = v'A_0` in `S_fin`, because the relations of `Š` are among those of
`S`.

### B4. Transfer to the group

Let `1 != w in G = G(P(M))`.

**Outside `T`.**  `G/T` is a finitely generated metabelian group (Lemmas 4.4,
4.5), hence residually finite (P. Hall, Proc. LMS 9 (1959)), and it separates
`w`.

**Inside `T`.**  Use the injective map `T -> T_1` of Lemma 4.14 and write
`w` as a product of basis vectors `z_(i,u)`.  Let the `u_s in W_0` and
`v_t in W` be the elements that occur in it, and build `S_fin`, `Š_fin` as in
B3.  Let `F <= T_1` be generated by:

- the vectors `z_(i,u)` with `u in W_0 cup W` whose image in `S_fin` or
  `Š_fin` is `0`;
- the quotients `z_(i,u) z_(i,u')^(-1)` of vectors with equal nonzero images.

1. `T_1/F` is finite: it is spanned by the vectors indexed by
   `{1,2,3}^(K+2)` and the nonzero elements of `S_fin` and `Š_fin`.
2. `F` is invariant under every letter automorphism and its inverse.  On
   `u in W_0` a letter acts trivially or through vectors `z_(i',u)` and
   `z_(i',uℓ)`, and the case depends only on the `A`-letter set.  That set is
   constant on nonzero classes, and right multiplication respects both
   quotients.  On `u in W` the same holds, with the insertion for `ã_j`
   compatible with the periodic relations and the exponent ideal, and with
   `A_0` handled by B3(d).
3. The image of `w` in `T_1/F` is nonzero, because the indices occurring in
   `w` have distinct nonzero images by B3(b),(c).
4. Let `A` be the group generated by the letter automorphisms.  It is a
   quotient of the metabelian group `<L_1 cup L_2>`, so it is finitely
   generated metabelian and residually finite.  Then
   `Ḡ/F = (T_1/F) x| A` splits with finite normal subgroup and residually
   finite quotient.  Such a group is residually finite: an element outside
   `T_1/F` survives in `A`, and one inside survives in
   `(T_1/F) x| (A/A_0)`, where `A_0` is the finite-index kernel of
   `A -> Aut(T_1/F)`.

Composing `G -> Ḡ -> Ḡ/F` with a finite quotient separates `w`.  QED

## 5. Why KMS's own semigroup proof is not quoted

In the proof of Theorem 3.9, KMS separate words with different `M`-parts in
`S̃(M_n)`, obtained by adding `a_(K+1)^2 = a_(K+1)` and
`a_(K+2)^2 = a_(K+2)`.  In `S̃` any `q`-word carrying `A_(K+1) A_(K+2)` can be
pumped once, reduced to exponents `(1,1)`, unpumped to `(0,0)`, and drained.
So that quotient kills such words and does not separate them.  Their
conclusion is recovered by the single `D`-periodic quotient of B3, which
handles all cases at once.  The clock supplies the invariant `iota` that makes
B3 work.  This note records a gap in an intermediate display, not a false
theorem: Theorems 4.17--4.19 as stated are not affected.
