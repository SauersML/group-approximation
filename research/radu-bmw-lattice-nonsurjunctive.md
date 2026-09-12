---
rg: 2
id: radu-bmw-lattice-nonsurjunctive
kind: claim
title: Radu's non-residually-finite BMW lattice carries an injective non-surjective cellular automaton
distinct_from:
  strict-automaton-on-lattice-in-product-of-trees: that asks for a strict automaton on some lattice in a product of two trees; this names one explicit irreducible non-residually-finite lattice with a quoted presentation and complete square table, and implies that claim.
  radu-bmw-lattice-nonsofic: that is nonsoficity of the same lattice; this is failure of surjunctivity, which implies it.
artifacts:
  - research/artifacts/radu-lattice-strict-automaton-screens-2026-09-12.md
  - research/artifacts/titz-witzel-radu-sublattice-2026-09-11.md
---

**OPEN.** Let `Gamma_R` be Radu's BMW lattice from `radu-bmw-lattice-embeds-in-titz-witzel-kernel`:

```text
Gamma_R = <a,b,c,x,y,z | a^2,b^2,c^2,x^2,y^2,z^2, axax, ayay, azbz, bxbx, bycy, cxcz>,
```

acting simply transitively on the vertices of a product of two 3-regular trees. Exhibit a finite
alphabet `A` and a cellular automaton on `A^(Gamma_R)` that is injective and not surjective.

**Consequences.**
- It refutes Gottschalk's conjecture, through `strict-automaton-on-lattice-in-product-of-trees`
  (`radu-bmw-nonsurjunctivity-gives-lattice-target`).
- It makes `Gamma_R` nonsofic (`radu-bmw-nonsurjunctivity-gives-nonsoficity`). Through
  `titz-witzel-kernel-nonsofic-from-radu-lattice` it also makes the smallest Titz--Witzel kernel
  `K = Gamma_1^2`, a finitely presented simple Kazhdan group, nonsofic.
- It makes `K` nonsurjunctive. `pi_1(S_R)` has index four in `Gamma_R`
  (`surjunctivity-is-a-commensurability-invariant`) and embeds in `K`
  (`surjunctivity-passes-to-subgroups`).

The claim is equivalent to the same statement for `pi_1(S_R)`.

## Attempts

* **Screens (w3-lattice, 2026-09-12; artifact Sections 1–3).**
  - **No output symmetry.** `radu-bmw-lattice-has-no-invariant-output-injective-automata`. Every
    involution of `Gamma_R` survives in `Gamma_R^ab = (Z/2)^3`, and finite quotients see output
    symmetry, so the swap, Klein and invariant-output architectures have no instance, despite the
    2-torsion.
  - **Factorizations.** `strict-composites-have-strict-factors`: any factorization of a strict
    automaton has a strict factor, and by the coset decomposition that factor's memory generates
    a nonsofic subgroup. Layers whose memory lies in a conjugate of `A = <a,b,c>`, of
    `V = <x,y,z>`, or of a dihedral `<h, v>` add nothing. This covers reading one square, and a
    key automaton reading a key track at two square-joined addresses.
  - **Letter hinges.** Every transposed letter identification holds, because all letters are
    involutions (`s m = s' m'` inverts to `m s = m' s'`).
* **Where it stops.** No candidate layer is known: an automaton over `Gamma_R` whose memory
  involves both factors, generates a nonsofic subgroup, and has no output symmetry. Its linear case
  is a one-sided inverse over `M_n(F_p[Gamma_R])` supported on such a subgroup
  (`stable-finiteness-failure-refutes-surjunctivity`). Odd-characteristic averaging idempotents are
  killed by characters, so the corner-idempotent targets of the Leavitt hosts have no analogue here.
