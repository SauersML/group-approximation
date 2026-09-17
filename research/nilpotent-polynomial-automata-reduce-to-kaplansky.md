---
rg: 2
id: nilpotent-polynomial-automata-reduce-to-kaplansky
kind: claim
title: Injective polynomial automata over a finite nilpotent group alphabet are bijective once the one-track prime-field group algebras are directly finite
distinct_from:
  formal-polynomial-strict-pairs-need-unstable-linearization: that needs a left-inverse pair whose identity holds formally over a field, without x^q = x, and matrix direct finiteness; this needs only injectivity of one automaton, allows every law of the alphabet group in any identity, and uses one-track direct finiteness, because the lower central filtration of a nilpotent alphabet terminates where the m-adic filtration of a finite field's function ring stabilizes.
  unipotent-automata-over-finite-fields-are-surjective: that is polynomial automata over F_q with invertible linear part and a degree-bounded decoder; this is word maps with constants over a nonabelian nilpotent alphabet, with no decoder and no degree bound, and invertibility of the linear part is derived from injectivity.
  homomorphic-group-alphabet-ca-reduce-to-stable-finiteness: that treats automata that are group homomorphisms of K^G, over any finite K; this treats automata whose rule is an arbitrary word with constants, which are not homomorphisms, over nilpotent K only, and the non-nilpotent case fails (see Scope).
  higman-group-algebras-embed-in-division-rings: that makes every linear automaton over Higman's group surjective; this extends the one-track conclusion from linear rules to every nilpotent-polynomial rule, a nonlinear class.
artifacts:
  - experiments/nilpotent-polynomial-automata-2026-09-17/check_criterion.py
  - experiments/nilpotent-polynomial-automata-2026-09-17/results-seed1.txt
  - experiments/nilpotent-polynomial-automata-2026-09-17/results-seed2.txt
---

**ESTABLISHED** by `nilpotent-polynomial-automata-reduce-to-kaplansky-proof` (proposed; referee pending).

**Setting.**
- `G` is any group and `Q` a finite nilpotent group.
- A **`Q`-polynomial automaton** has memory `m_1, ..., m_k in G` and rule `w`, a word in `k` variables with
  constants from `Q`, that is, an element of `Q * F_k`. It is
  `tau(x)(g) = w(x(g m_1), ..., x(g m_k))`.
- `e_j` is the exponent sum of variable `j` in `w`, and `alpha = sum_j e_j m_j` in `Z[G]`.
- `e_ab` is the exponent of `Q^ab`.

**Theorem.**
1. If `alpha` is a unit of `(Z/e_ab)[G]`, then `tau` is bijective, for every `G`.
2. If `tau` is injective, then `alpha` has a left inverse in `(Z/e_ab)[G]`.
3. So if `F_p[G]` is directly finite for every prime `p` dividing `|Q|`, then:
   - every injective `Q`-polynomial automaton is bijective;
   - `tau` is bijective if and only if `alpha` is a unit of `(Z/e_ab)[G]`.

Only one-track (`1 x 1`) direct finiteness is used. No left inverse is assumed, and the identities of `Q`, such
as `x^exp(Q) = 1`, may be used freely.

**Hosts where the hypothesis is known.**
- Sofic groups (Elek–Szabó), where Gottschalk is already known.
- Unique-product groups, in particular left-orderable groups, where `F_p[G]` is a domain. This covers Higman's
  group `H` (left-orderable by Rivas–Triestino, imported and not re-read) and Thompson's group `F`.
- For `H`, a strict automaton (`higman-group-nonsurjunctive`) must therefore be non-polynomial for every
  nilpotent group structure on its alphabet. Before, it was only known to be nonlinear.

**Calibration.**
- `Q = Z/p`: the `Q`-polynomial automata are the affine one-track automata over `F_p`, and the theorem is the
  known equivalence with direct finiteness of `F_p[G]`.
- Brute force on finite hosts `G = Z/n` (`n <= 4`), where direct finiteness is automatic, found no disagreement
  with "bijective iff `alpha` is a unit". Scripts and outputs are in the artifacts.
  - Alphabets: `Z/4`, `(Z/2)^2`, `Z/6`, `D_4`, `Q_8` and the Heisenberg group mod 3, with random words including
    constants (3840 random rules across seeds 1 and 2, 0 disagreements).
  - The same criterion fails for the non-nilpotent alphabets `S_3` and `A_4`. Example: over `S_3` on `G = Z/2`,
    `tau(x)(g) = x(g)^2 x(g+1)^-1` has `alpha = 2 - t = t` mod 2, a unit, but its image has 30 of the 36 points.
    So nilpotency is where the method lives.

**Scope: where the denial breaks.**
- **Nonabelian simple alphabet.** By Maurer–Rhodes every function `Q^k -> Q` is a word with constants. So
  `Q`-polynomial surjunctivity is the whole conjecture at `|Q|` symbols. The lower central series of the
  polynomial function group stops at a perfect layer, and the argument has nothing to act on.
- **Solvable non-nilpotent alphabet.** The layers that are not central carry a configuration-dependent twist
  (for `S_3`, the sign of the `Z/2` quotient acts on the `Z/3` layer). The fibre maps are linear operators over
  a twisted crossed product of `C(2^G, F_3)` by the bijective sign automaton, not over a group ring.
- **Arbitrary rules.** A polynomial map of a class-`c` group has degree at most `c` in the Lazard sense. A rule
  over `p^n` symbols is `Q`-polynomial only if its degree is bounded by the class of some group structure on
  the alphabet. No stabilization with ancilla tracks is known, because injectivity must hold on all of
  `Q^G`, not only on an embedded binary section.
