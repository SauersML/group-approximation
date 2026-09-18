---
rg: 2
id: solvable-polynomial-automata-reduce-to-kaplansky
kind: claim
title: Injective polynomial automata over a finite solvable alphabet are bijective once the matrix group algebras at its chief factors are directly finite, and for S_3 this is equivalent to direct finiteness of F_2[G] and F_3[G]
distinct_from:
  nilpotent-polynomial-automata-reduce-to-kaplansky: that treats nilpotent alphabets through the lower central series and a unit criterion for alpha; this treats every solvable alphabet through a chief series, where the noncentral layers carry certificate-dependent coefficients, and it corrects that node's Scope, which lists S_3 as a failure because the prime 3 of the constant fibre was missing.
  homomorphic-solvable-alphabet-ca-reduce-to-stable-finiteness: that treats automata that are group homomorphisms of Q^G; this treats arbitrary words with constants, which are not homomorphisms and whose layers are not linear automata but certificate-controlled affine families.
  homomorphic-group-alphabet-ca-reduce-to-stable-finiteness: that peels the socle of a homomorphic automaton; this peels the solvable radical of a polynomial automaton and leaves the quotient Q/Sol(Q) as the only nonlinear residue.
  nonlinear-certificate-fibers-are-all-surjective-or-all-strict: that is the fibre dichotomy for certificate-preserving automata, and it excludes data-dependent or nonreversible certificate updates; this applies it to the certificate-preserving shadow E(a,b)=(L_b a,b) of a polynomial automaton whose certificate update is the quotient automaton, not known to be reversible, and recovers the update's injectivity by a collision argument.
  one-invertible-certificate-fiber-forces-global-invertibility: that is the linear crossed-product statement at fixed matrix size; this needs no crossed-product direct finiteness at all, only the constant-certificate group-ring fibre, and handles an evolving certificate.
  controlled-self-linear-feedback-ca-are-surjunctive: that needs invertible constant parts of self-linear rows; this derives invertibility of every fibre from injectivity and direct finiteness.
artifacts:
  - experiments/solvable-polynomial-automata-2026-09-17/check_fibration.py
  - experiments/solvable-polynomial-automata-2026-09-17/results-seed1.txt
  - experiments/solvable-polynomial-automata-2026-09-17/results-seed2.txt
---

**ESTABLISHED** by `solvable-polynomial-automata-chief-series-peeling-proof` (proposed; referee pending).

**Setting.**
- `G` is any group and `Q` a finite group.
- A **`Q`-polynomial automaton** has memory `m_1, ..., m_k in G` and a rule `w in Q * F_k` (a word with
  constants). It is `tau(x)(g) = w(x(g m_1), ..., x(g m_k))`.
- "`Q`-polynomial surjunctivity over `G`" means every injective `Q`-polynomial automaton on `Q^G` is surjective.

**Theorem 1 (peeling one abelian chief factor).** Let `A` be an abelian minimal normal subgroup of `Q`, so
`A = F_p^d`. Put `B = Q/A`. Let `tau` be a `Q`-polynomial automaton and `taubar` its image, the `B`-polynomial
automaton with the same memory and the rule `w` reduced mod `A`.
1. In section coordinates `x = a q(b)`, `tau(a,b) = (L_b a + d_b, taubar(b))`. Here each `L_b` is an
   `F_p`-linear map of `A^G` whose coefficients lie in the `F_p`-span of the conjugation image of `B` in
   `End(A)`, and they depend locally on `b`.
2. If `tau` is injective and `M_d(F_p[G])` is directly finite, then every `L_b` is bijective and `taubar` is
   injective.
3. Under the same hypotheses, `tau` is surjective if and only if `taubar` is surjective.

**Theorem 2 (solvable radical).** Let `1 = Q_0 < ... < Q_r = Sol(Q)` be chief factors of `Q` below the solvable
radical, with `Q_i/Q_(i-1) = F_(p_i)^(d_i)`. Suppose every `M_(d_i)(F_(p_i)[G])` is directly finite.
- An injective `Q`-polynomial automaton is bijective if and only if its image over `Q/Sol(Q)` is.
- Hence `Q`-polynomial surjunctivity over `G` follows from `(Q/Sol(Q))`-polynomial surjunctivity over `G`.
- In particular, for **solvable `Q`**, every injective `Q`-polynomial automaton over `G` is bijective.
- For **supersolvable `Q`** (every `d_i = 1`: nilpotent groups, `S_3`, dihedral groups, ...), only one-track
  direct finiteness of `F_p[G]` for `p` dividing `|Q|` is used. This recovers part 3 of the nilpotent node.

**Theorem 3 (`S_3`, both directions).** For every group `G`, the following are equivalent:
- every injective `S_3`-polynomial automaton over `G` is surjective;
- `F_2[G]` and `F_3[G]` are directly finite.

The converse direction uses two explicit words, with `S_3 = <t> x| <r>` and `x = t^a r^s`:
- `p(x) = x^3 r x r x` equals `r^s` on all of `S_3`;
- `v(x) = x p(x)` equals `t^a`.

A strict linear automaton `lambda` over `F_3` gives the strict `S_3`-polynomial automaton
`prod_h v(x(gh))^(lambda_h) p(x(g))`, which is `(a,s) -> (a lambda, s)`. A strict `beta` over `F_2` gives
`v(x(g)) prod_h p(x(gh))^(beta_h)`, which is `(a,s) -> (a, s beta)`.

So the brief's question ("reduce `S_3`-polynomial surjunctivity to direct finiteness of `C(2^G,F_3) x| G`, or
find a strict `S_3`-polynomial automaton") resolves as a strict two-way reduction to the group rings
themselves. No crossed-product direct finiteness is needed: the fibre dichotomy transports bijectivity from the
constant certificate to every certificate.

**Why the nilpotent node's `S_3` example fails.** Take `tau(x)(g) = x(g)^2 x(g+1)^-1` over `S_3` on `G = Z/2`.
- The seed invariant `alpha mod 2 = t` is a unit.
- The constant-certificate fibre is `L_0 = 2 + 2t = 2 - t` in `F_3[Z/2]`, and `(2 - t)(2 + t) = 1 - t^2 = 0`.
- So `L_0` is singular, and `tau` has 30 of 36 images.

The criterion must see the prime 3 through the constant fibre, not only `Z/e_ab`.

**New unconditional classes.**
- **Unique-product hosts** (e.g. left-orderable groups): `F_p[G]` is a domain, hence directly finite. So
  over every unique-product group, every injective `Q`-polynomial automaton with `Q` supersolvable is
  surjective.
- **Higman's group `H`**: by `higman-group-algebras-embed-in-division-rings`, every `M_n(F_p[H])` is directly
  finite.
  - Over `H`, every injective `Q`-polynomial automaton with `Q` solvable is surjective.
  - For arbitrary `Q`, a strict `Q`-polynomial automaton over `H` forces a strict `(Q/Sol(Q))`-polynomial
    automaton over `H`.
  - So a witness for `higman-group-nonsurjunctive` is non-polynomial for every solvable group structure on its
    alphabet. The nilpotent node gave this only for nilpotent structures, and the division-ring node only for
    linear rules.

**Where it stops.** `Q/Sol(Q)` has no abelian minimal normal subgroup. If it is nonabelian simple, every
function on it is a word with constants (Maurer–Rhodes, imported). So the residue is Gottschalk's conjecture
at `|Q/Sol(Q)|` symbols, and no chief-factor linearization can act on it. Converse directions for solvable `Q`
other than `S_3` (whether a non-directly-finite `M_d(F_p[G])` gives a strict `Q`-polynomial automaton) are
open. Only `S_3` has both directions here.

**Calibration** (`experiments/solvable-polynomial-automata-2026-09-17/`). The alphabets are `S_3 = F_3 x| Z/2`
and `A_4 = F_2^2 x| Z/3`. The hosts are `Z/n` with `n <= 4` for `S_3` and `n <= 3` for `A_4`. Seeds 1 and 2
cover 560 random words with constants.
- **(F)** The prefix formula for the fibre coefficients matched direct evaluation on every certificate pattern,
  for all 560 words.
- **(B)** "`tau` bijective iff `taubar` is bijective and every fibre `L_b` is bijective" held for all 560
  words. Every bijective `tau` had all constant fibres bijective.
  - For 4 `S_3` words and 20 `A_4` words, `taubar` and the constant fibre `L_0` were bijective but `tau` was
    not.
  - So injectivity of `tau` is genuinely used to reach the nonconstant fibres. On infinite hosts this is the
    dichotomy step.
- **(S)** The seed criterion "`alpha` unit mod `e_ab`" disagreed with the truth on 39 `S_3` words and 73 `A_4`
  words. The example above was reproduced.
- **(R)** `p(x) = r^s` and `v(x) = t^a` hold on all of `S_3`. The realizers `tau_beta` and `tau_lambda`
  computed `(a, s beta)` and `(a lambda, s)` in all 9288 host, coefficient and configuration cases.
