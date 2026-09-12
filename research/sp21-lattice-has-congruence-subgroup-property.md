---
rg: 2
id: sp21-lattice-has-congruence-subgroup-property
kind: claim
title: Some torsion-free cocompact arithmetic Sp(2,1) lattice has the congruence subgroup property
distinct_from:
  normal-subgroups-of-arithmetic-lattices-are-congruence-open: that is an unconditional fact controlling congruence quotients of quotients; this is the open assertion that there are essentially no other finite quotients
  sp21-lattice-hyperbolic-quotient-without-finite-quotients: that asks for one finite-quotient-free hyperbolic quotient; this is a property of the lattice itself which would make every infinite hyperbolic proper quotient non-residually-finite
---

Let `Γ <= G(O)` be a torsion-free cocompact arithmetic lattice in `Sp(2,1)`,
with `G` as in `normal-subgroups-of-arithmetic-lattices-are-congruence-open`.
Assert that the kernel of the natural map `Γ̂ -> Γ̄`, from the profinite
completion onto the congruence completion, is finite.

By `non-rf-hyperbolic-via-sp21-congruence-property` this assertion gives a
non-residually-finite hyperbolic group.  Contrapositive: if every hyperbolic
group is residually finite, no torsion-free cocompact arithmetic `Sp(2,1)`
lattice has the congruence subgroup property.

## Attempts

- **Settling it either way.**  Not attempted here.  Property (T) passes to
  finite-index subgroups, so every finite-index subgroup of `Γ` has finite
  abelianization.  Failure of the property therefore cannot be shown by a
  finite-index subgroup with infinite abelianization.
- **Literature status (read 2026-09-12 by lit-scout-2 from the PDF on MSI).**
  - **Open.** Lubotzky, *Some more non-arithmetic rigid groups*, Contemp. Math.
    387 (2005), arXiv:1105.4785, §4: "The question whether L satisfies the
    congruence subgroup property ... is still open ... As of now, the answer is
    not known for any single such L." Here `L` is a uniform `Sp(n,1)` lattice.
  - **The payoff is his.** Remark 4.2 there states that one such `L` with CSP
    gives a hyperbolic group without finite-index subgroups.
  - **Related.** Tholozan--Tsouvalas, arXiv:2207.14356, p. 1, tie residual
    finiteness of Kapovich's examples to this conjecture.
- **Weaker hypothesis.** `sp21-lattice-few-alternating-and-large-rank-quotients`
  already suffices; `sp21-simple-quotient-bound-from-congruence-property`
  derives it from this claim.
