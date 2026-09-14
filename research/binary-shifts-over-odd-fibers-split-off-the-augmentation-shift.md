---
rg: 2
id: binary-shifts-over-odd-fibers-split-off-the-augmentation-shift
kind: claim
title: For a finite group P of odd order the binary shift over G × P is the binary shift over G times the augmentation-module shift, whose only fixed symbol is zero
distinct_from:
  passive-fixing-injective-automata-are-surjective: that proves designs keeping reserved symbols in place fail; this changes coordinates so that the two constant fibers become one reserved symbol, the zero vector, which has additive meaning.
  coset-shifts-split-off-full-shifts-at-lifted-alphabets: that splits a coset shift off a full shift by an orbit colouring at a lifted alphabet size; this splits the binary shift over G × P by the linear Maschke complement, at the same size.
  modular-matrix-failures-descend-to-scalars-over-g-times-p: that uses the same complement for linear automata and matrix rings; this records what the complement gives for nonlinear automata, where only one factor may be nonlinear.
  some-nonsurjunctive-group-gives-a-binary-one: that is universal binary descent; this gives a sufficient condition for a binary witness over G × P in terms of P-equivariant automata on the augmentation shift.
artifacts:
  - research/artifacts/gk3-binary-descent-2-2026-09-14.md
---

**ESTABLISHED** by `odd-fiber-augmentation-split-proof`. Elementary; no novelty is claimed.

Let `G` be a group and `P` a finite group of odd order. Configurations on `G × P` are translated by
`((h,u)·x)(g,t) = x(h^(-1) g, u^(-1) t)`. Let `I_P = {v ∈ F_2^P : Σ_t v(t) = 0}`, with `P` acting by
`(u·v)(t) = v(u^(-1) t)`, and let `𝟙 ∈ F_2^P` be the all-ones vector.

1. **Split.** `Θ(x) = (s, z)`, with `s(g) = Σ_t x(g,t)` and `z(g) = x(g,·) + s(g)𝟙`, is a homeomorphism
   `{0,1}^(G×P) → {0,1}^G × I_P^G` with inverse `x(g,·) = z(g) + s(g)𝟙`. It intertwines translation by
   `(h,u)` with `(s, z) ↦ (s(h^(-1)·), u·z(h^(-1)·))`: `G` translates both factors, and `P` acts trivially on
   the first factor and symbolwise on the second.
2. **Transfer.** Let `β` be an automaton on `{0,1}^G` and `θ` an automaton on `I_P^G` commuting with the
   symbolwise `P`-action. Then `Φ = Θ^(-1) (β × θ) Θ` is a binary cellular automaton over `G × P`. It is
   injective iff `β` and `θ` are, and surjective iff both are. In particular a `P`-equivariant injective,
   non-surjective `θ` gives a binary strict automaton over `G × P` (take `β = id`).
3. **One fixed symbol.** The only `P`-fixed vector in `I_P` is `0`. By
   `passive-fixing-injective-automata-are-surjective` with passive set `{0}`, a `P`-equivariant injective
   automaton on `I_P^G` that outputs `0` exactly at `0`-sites is surjective. So a strict `θ` must write a
   nonzero symbol at some `0`-site, or `0` at some nonzero site.
4. **Cyclic fibers.** For `P = C_q` with `q` an odd prime, `F_2[C_q] = F_2[x]/(x^q - 1) ≅ F_2 × R_q` with
   `R_q = F_2[x]/(Φ_q(x))`, and `I_P` is the factor `R_q`, on which the generator acts as multiplication by
   `ζ = [x]`. So the `P`-equivariant automata on `I_P^G` are exactly the automata on `R_q^G` whose local rule
   satisfies `f(ζu) = ζ f(u)`.
   - `R_q` is a product of copies of `F_(2^d)`, where `d` is the order of 2 mod `q`.
   - It is the field `F_(2^(q-1))` iff 2 is a primitive root mod `q`, e.g. `q = 3` (`R_3 = F_4`) or `q = 5`.

**Consequence.** A group `G` and an odd prime `q` with a `ζ`-homogeneous injective, non-surjective automaton
on `R_q^G` give a binary strict automaton over `G × C_q`. In the orbit language of
`research/artifacts/gk3-alphabet-descent-2026-09-14.md` (Section 4), the two constant fibers `0^P`, `1^P`
become one factor `{0,1}^G` that can be left alone, and one reserved symbol `0` in the other factor.

**Calibration** (artifact Section 4). For `G = C_2`, `P = C_3`: `Θ` is a bijection on all 64
configurations, lands in the augmentation module, and intertwines all 6 translations. The only fixed vector
of `I_(C_3)` is `0`.
