---
rg: 2
id: solvable-polynomially-split-alphabets-two-way-kaplansky
kind: claim
title: For alphabets whose abelian chief factors are polynomially split, polynomial surjunctivity is equivalent to direct finiteness of the matrix algebras over the chief-factor endomorphism fields, and splitting is decided by one nonconstant layer-valued word
distinct_from:
  solvable-polynomial-automata-reduce-to-kaplansky: that proves only "direct finiteness implies polynomial surjunctivity" for solvable alphabets, with hypothesis M_d(F_p[G]), and has both directions only for S_3 through two ad hoc words; this sharpens the hypothesis to M_e(F_q[G]) with F_q = End_Q(A), proves the converse for every polynomially split chief series (all groups of squarefree order, A_4, S_4, SL(2,3), ...), and characterizes splitting by a ring-theoretic idempotent argument.
  homomorphic-group-alphabet-ca-reduce-to-stable-finiteness: that is the homomorphic sub-class, where both directions hold for all alphabets through the socle; this is the polynomial class, not homomorphisms, where the converse needs a word that extracts the chief-factor coordinate, and such a word does not exist for central layers with p dividing the exponent of the quotient's abelianization.
  nilpotent-polynomial-automata-reduce-to-kaplansky: that gives the direction "direct finiteness implies surjunctivity" for nilpotent alphabets; this proves the converse at the non-nilpotent layers, and shows that for nilpotent alphabets layer extraction splits a layer exactly when its Sylow subgroup has prime order. Every layer inside a larger Sylow subgroup is central with `p | exp(B^ab)`, so it is blocked.
artifacts:
  - experiments/solvable-polynomial-automata-2026-09-17/split_layers.py
  - experiments/solvable-polynomial-automata-2026-09-17/results-split.txt
---

**ESTABLISHED** by `polynomially-split-chief-factors-realize-strict-layers-proof` (proposed; referee pending).

**Setting.**
- `G` is any group and `Q` a finite group. A `Q`-polynomial automaton has a rule that is a word with constants,
  `w in Q * F_k`, as in `solvable-polynomial-automata-reduce-to-kaplansky`.
- `A` is an abelian minimal normal subgroup of `Q`, so `A = F_p^d`, and `B = Q/A` acts on `A` by `rho`.
- `E = span_(F_p) rho(B)` inside `End(A)`. Since `A` is an irreducible `F_p[B]`-module, `E = End_D(A)`, where
  `D = End_Q(A) = F_q` is a finite field. Put `e = dim_D A`, so `E = M_e(F_q)`.
- `Pol_1(Q)` is the set of maps `Q -> Q` given by one-variable words with constants.
- `Q` is **polynomially split along `A`** if some `f in Pol_1(Q)` has `f(Q) <= A` and `f(a x) = a f(x)` for all
  `a in A`, `x in Q`.

**Theorem A (splitting criterion).** `Q` is polynomially split along `A` if and only if some `f in Pol_1(Q)` with
`f(Q) <= A` is nonconstant on `A`.
- Sufficient: `p` does not divide `|B|` (use `x^m`, `m = 0 mod exp(B)`, `m = 1 mod p`).
- Sufficient: some `c in Q` with `p` not dividing `exp(B)/o(cbar)` and `sum_(i < o(cbar)) rho(c)^i != 0` (use
  `(x c)^exp(B)`).
- Obstruction: if `A` is central and `p` divides `exp(B^ab)`, `Q` is not split along `A`. Every word that is
  `A`-valued has exponent sum divisible by `exp(B^ab)`, so it is constant on `A`.

**Theorem B (both directions at one layer).**
1. **Forward (sharpened).** If `tau` is an injective `Q`-polynomial automaton and `M_e(F_q[G])` is directly finite,
   then every fibre `L_b` is bijective, the shadow `taubar` over `B` is injective, and `tau` is surjective iff
   `taubar` is. This is Theorem 1 of `solvable-polynomial-automata-reduce-to-kaplansky` with `M_d(F_p[G])`
   replaced by the weaker hypothesis `M_e(F_q[G])` (`M_e(F_q) <= M_d(F_p)`).
2. **Converse.** Suppose `Q` is polynomially split along `A`.
   - If `M_e(F_q[G])` is not directly finite, there is a strict `Q`-polynomial automaton over `G`.
   - If there is a strict `B`-polynomial automaton over `G`, there is a strict `Q`-polynomial automaton over `G`.

**Theorem C (two-way reduction).** Let `1 = Q_0 < Q_1 < ... < Q_r` be normal in `Q` with each
`Q_i/Q_(i-1)` an abelian minimal normal subgroup of `Q/Q_(i-1)`, with invariants `(p_i, q_i, e_i)`. Suppose each
`Q/Q_(i-1)` is polynomially split along `Q_i/Q_(i-1)`. Then, for every group `G`:

    every injective Q-polynomial automaton over G is surjective
    <=>  every M_(e_i)(F_(q_i)[G]) is directly finite, and every injective (Q/Q_r)-polynomial automaton is surjective.

For solvable `Q` with `Q_r = Q` the last condition is empty.

**Theorem D (central layers, where extraction is blocked).** Let `Z = Z/p` be a central subgroup of `Q`, and let
`epsilon(w) = sum_j e_j m_j` in `Z[G]` be the exponent-sum element of a rule.
1. Every fibre operator of a `Q`-polynomial automaton `tau` along `Z` equals the one-track linear automaton
   `alpha(epsilon(w) mod p)`. So if the shadow over `Q/Z` and `alpha(epsilon mod p)` are both injective, `tau` is
   injective. Conversely, `tau` injective implies `alpha(epsilon mod p)` injective.
2. **Lifting criterion.** A strict `(Q/Z)`-polynomial automaton whose rule has `alpha(epsilon mod p)` injective
   lifts to a strict `Q`-polynomial automaton, by lifting the constants arbitrarily.
3. **Tracked realizers.** The realizers of Theorem B.2 have
   `epsilon = sigma_f sum_h n_h h + (1 - sigma_f)` (case ii) and `epsilon = sigma_f + (1 - sigma_f) epsilon(w)`
   (case i), where `sigma_f` is the exponent sum of the splitting word.

Consequences:
- **Nilpotent `Q`, both directions.** `Q`-polynomial surjunctivity over `G` holds iff `F_p[G]` is directly
  finite for every `p | |Q|`. For the converse, take `st = 1 != ts` in `F_p[G]`, and choose integers `n_h` with
  `n_h = t_h mod p` and `n_h = [h = 1] mod |Q|_(p')`. The constant-free rule `prod_h x(gh)^(n_h)` is strict.
- **Split layers under a nilpotent top.** If a chain of polynomially split layers ends at `Q_r` with `Q/Q_r`
  nilpotent, `Q`-polynomial surjunctivity is equivalent to direct finiteness of all `M_(e_i)(F_(q_i)[G])` and of
  `F_p[G]` for `p | |Q/Q_r|`. This covers every solvable group in the computation, including the non-split
  `D_12 = S_3 x Z/2`, `Z/3 x| Z/4`, `F_5 x| Z/4` (`F_3[G]` or `F_5[G]`, and `F_2[G]`) and `S_3 wr Z/2`
  (`M_2(F_3[G])` and `F_2[G]`).
- **`GL(2,3)`.** Its only minimal normal subgroup is the center `Z/2`, over `S_4` with `S_4^ab = Z/2`, so it is not
  split. The `S_4` realizers use splitting words `(xc)^6` and `x^4` of even exponent sum, so they have
  `epsilon = 1 mod 2` and lift by item 2. So `GL(2,3)`-polynomial surjunctivity is equivalent to direct finiteness
  of `M_2(F_2[G])` and `F_3[G]`.

**Classes where both directions now hold.**
- **Squarefree order** (`S_3`, `Z/6`, `D_(2p)`, `F_7 x| Z/3`, ...). Every chief factor is a full Sylow subgroup of
  its quotient, so the first sufficient condition applies at every layer:
  `Q`-polynomial surjunctivity over `G` iff `F_p[G]` is directly finite for every `p | |Q|`.
- **`A_4`.** Layers `F_2^2` (with `End = F_4`, `e = 1`) and `F_3`: equivalent to direct finiteness of `F_4[G]`
  and `F_3[G]`.
- **`S_4`.** Layers `F_2^2` (with `End = F_2`, `e = 2`; split by `(x c)^6`, `c` a transposition), `F_3`, `F_2`:
  equivalent to direct finiteness of `M_2(F_2[G])` and `F_3[G]`.
- **`SL(2,3)`.** Center `F_2`, split by `(x^3 c)^3` with `c` of order 3 (neither sufficient condition applies),
  then `A_4`: equivalent to direct finiteness of `F_4[G]` and `F_3[G]`.
- **`S_3 x Z/3`.** Split along `A_3` by `x^4 r x r x`, then `Z/6`: equivalent to direct finiteness of `F_2[G]`
  and `F_3[G]`.

**Where the method is blocked.** Central layers with `p | exp(B^ab)` are never split. This includes every
non-trivial layer of `Z/4`, `Z/2^2`, `D_8`, `Q_8`, the center of `D_12` and `S_3 x Z/2`, the `Z/4` top of
`F_5 x| Z/4`, the `D_8` quotient of `S_3 wr Z/2`, and the center of `GL(2,3)`. Theorem D recovers both directions
wherever the realizers above such a layer have `epsilon` injective mod `p`.
- Still open: a solvable `Q` with a non-split central layer `Z/p` below a non-nilpotent quotient, for which every
  available strict quotient realizer has `alpha(epsilon mod p)` non-injective.
- When `p | exp(B^ab)`, `epsilon mod p` depends only on the function computed by the shadow rule: read the
  exponents off in `B^ab`. So adding identities of `B` does not help, and such a case needs genuinely different
  realizers. No
chief-factor method acts on `Q/Sol(Q)`: for nonabelian simple `Q` the polynomial automata are all automata on
`|Q|` symbols (Maurer–Rhodes).

**Computation** (`experiments/solvable-polynomial-automata-2026-09-17/split_layers.py`). For 21 groups of order at
most 120, it computes `Pol_1(Q) cap A^Q` along every chief series by Schreier generators and `F_p`-linear
algebra.
- It solves for `f` with `f(ax) = a f(x)` and verifies every solution pointwise: 51 split layers, all verified.
- Over the 68 layer entries printed (51 split, 17 not), "split" agreed with "some layer-valued word is
  nonconstant on `A`" every time, as Theorem A requires.
- Every non-split entry is a central layer with `p | exp(B^ab)`.
