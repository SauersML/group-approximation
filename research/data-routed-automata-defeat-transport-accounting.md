---
rg: 2
id: data-routed-automata-defeat-transport-accounting
kind: claim
title: Every automaton is a data-routed copy rule, and a bijective parity automaton leaves one quarter of its sites unread in every copy presentation, so site-transport accounting cannot see strictness beyond certificate-independent routing
distinct_from:
  certificate-controlled-routing-is-surjunctive: that proves surjectivity when the routing is chosen by a certificate track kept in the output and independent of the routed data; this shows that once the selection reads the routed configuration, the same balance identity holds with a positive defect for a bijective automaton, so its step "an unread site can be changed invisibly" is false, and every automaton admits such a presentation.
  marker-routed-paradoxical-transport-must-collide: that forces collision mass on any site-injective marker compression and names site mixing as the gate; this shows that site mixing is not a separate mechanism, since every automaton is a copy routing whose selection reads the data, and collisions coexist with bijectivity already over an element of order three.
  binary-three-address-strict-automata-are-linear: that classifies strict binary rules on three addresses as parity; this identifies the blind copy rules as hypercube perfect matchings, proves that no parity rule of support at least two is blind, and uses the classification only for a corollary.
  monotone-binary-injective-rules-are-copies: that excludes monotone injective rules through constant backgrounds; this concerns copy presentations of arbitrary rules and the failure of transport accounting for them.
artifacts:
  - experiments/blind-copy-automata-2026-09-17/blind_copy_census.py
---

**ESTABLISHED** by `data-routed-transport-universality-proof` (elementary and self-contained; no novelty
survey). The script checks parts 3 and 4 by exhaustion.

## Setting

`G` is a group, `A` a finite alphabet, and `tau(x)(g) = f((x(gm))_(m in M))` an automaton with memory
`M`, `1 in M`. Write `p_g = (x(gm))_(m in M)`.

- A **data-routed presentation** of `tau` is a map `s : A^M -> M` together with maps
  `pi : A^M -> Sym(A)` such that `f(p) = pi(p)(p(s(p)))`. The **read map** of `x` is
  `r_x(g) = g s(p_g)`, and its indegree is `N_x(h) = #{g : r_x(g) = h}`.
- The presentation is **copy** if every `pi(p)` is the identity, so `tau(x)(g) = x(r_x(g))`.
- A copy presentation is **blind** if `s(p') = s(p)` whenever `p'` differs from `p` only at the address
  `s(p)`. Then whether `g` reads `g m` does not depend on `x(gm)`.
- Certificate-controlled routing is the special case in which `s` and `pi` read only a certificate
  track that the automaton copies to the output unchanged.

## Theorem

1. **Every automaton is data-routed.** Take `s(p) = 1` and `pi(p)` the transposition of `p(1)` and
   `f(p)`, or the identity when they are equal. This presents `tau` with the same memory and radius zero.
2. **Every binary automaton is a copy routing up to one swap.** A binary automaton that fixes both
   constant configurations has a copy presentation with the same memory. An injective binary automaton
   permutes the two constants, so it, or its composite with the global letter swap (a reversible
   automaton), fixes both.
3. **Transport accounting sees a defect in a bijective automaton.** Let `mu` be the uniform Bernoulli
   measure and `N = N_x(1)`.
   - **(a) Presentation-independent defect.** Let `a, b in G` generate a Klein four subgroup
     `V = {1, a, b, ab}`. The parity automaton `L(x)(g) = x(g) + x(ga) + x(gb)` is an involution of
     `{0,1}^G`. Every copy presentation of `L` with memory `M = {1, a, b}` has `mu{N = 0} = 1/4`.
   - **(b) Blind example.** Let `t in G` have order three. The blind copy rule
     `tau(x)(g) = x(g)` if `x(g t^-1) = 0`, and `x(g t)` otherwise,
     with memory `{t^-1, 1, t}`, is a bijection of `{0,1}^G`. Its blind presentation has
     `mu{N = 0} = E_mu (N - 1)_+ = 1/4`. (Other copy presentations of the same rule can have bijective
     read maps; the script finds 36 of the 144 on `Z/3`.)

   In both cases the balance identity of `certificate-controlled-routing-is-surjunctive` holds with a
   positive defect, while the automaton is injective and surjective.
4. **Blind binary copy rules are hypercube perfect matchings, and never linear.** For `A = {0,1}` with
   `|M| = n`:
   - blind copy presentations correspond exactly to perfect matchings of the cube `{0,1}^n`, where each
     edge in direction `m` is labelled `m`, and the rule outputs the matched coordinate;
   - every blind copy rule is balanced;
   - no rule `epsilon + sum_(m in S) x_m` with `|S| >= 2` has a blind copy presentation.
5. **Corollary.** Over every group, an injective blind binary copy automaton whose memory has at most three
   elements is surjective. This uses `binary-three-address-strict-automata-are-linear`.

## What dies, and the gate

- **Killed class of approaches.** Every surjunctivity argument whose invariant is site transport of a
  routing presentation fails beyond certificate-independent selection. Such arguments include:
  - indegree balance under an invariant measure;
  - collision mass;
  - the double count of `marker-routed-paradoxical-transport-must-collide`;
  - the step "an unread input site can be changed invisibly".

  The reason is that, by parts 1 and 2, every automaton, strict or not, admits a data-routed
  presentation. By part 3, the step from "unread site" to "non-injective" is false as soon as the selection
  reads the data. For the Klein parity involution no choice of copy presentation removes the defect, and a
  blind defect already occurs on an element of order three. The invariant that
  controls the dichotomy is not site counts. It is whether the selection is measurable with respect to data
  that the output preserves independently of the routed symbols.
- **Named mechanism for the counterexample lane.**
  - Part 4 isolates the blind copy automata, the hypercube-matching rules. They contain the multiplexers,
    and they are the first routing class that is not certificate-controlled. They contain no linear rule of
    support at least two, so a surjunctivity proof for them would not have to decide Kaplansky direct
    finiteness over `F_2`.
  - By part 5 they are surjunctive at memory at most three. Note that part 3(a) is a linear rule, so it is
    not blind; blindness does not by itself remove the transport defect, as 3(b) shows. From four addresses on, their status is open.
  - A strict automaton whose rules are all blind would be a Hilbert-hotel design in which each output site
    chooses its source without reading it. The cost is paid only through the control reads, as in part 3.
- **Not claimed.** Nothing is said about surjunctivity of blind copy automata at four or more memory
  elements, nor about data-routed rules with non-identity letter permutations. By part 1 the latter are all
  automata.
