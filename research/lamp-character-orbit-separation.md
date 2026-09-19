---
rg: 2
id: lamp-character-orbit-separation
kind: claim
title: Lamp separation by a Hilbert embeddable length is an orbit-counting number
distinct_from:
  hilbert-embeddable-is-representation-realized: that identifies the cone of Hilbert embeddable lengths with representation metrics on any finite group; this computes what that cone does on an abelian normal lamp subgroup, via Clifford theory, and reads off the separation of the mark
  hilbert-embeddable-length-lp-feasibility: that says the witness question is a linear program; this evaluates the program's objective on the lamp coordinates in closed form, which is what tells one whether dilution is a real constraint
  hilbert-embeddable-witness-for-kun-thom-wreath: that asks whether a witness exists for the wreath; this settles which of that node's two recorded constraints is real — dilution is not, the site-distinctness one is
artifacts:
  - notes/TRUE_LAMP_CHARACTER_ORBIT_SEPARATION.md
---

Let `K` be finite with **abelian** normal subgroup `L` (lamps) and quotient
`A = K/L`. Split `Irr(K) ∖ {triv}` into `Irr_I` (those containing `L` in the
kernel, i.e. inflated from `A`) and `Irr_II`, and split every Hilbert
embeddable length accordingly as `ℓ = ℓ_I + ℓ_II`, both nonnegative and
conditionally negative definite.

1. **`ℓ_I|_L ≡ 0`.** For `χ ∈ Irr_I` and `h ∈ L`, `χ(h) = χ(1)`, so
   `ψ_χ(h) = 0`. All lamp separation is carried by `ℓ_II`, and any upper bound
   `ℓ ≤ ε` is inherited by each summand.
2. **Clifford theory computes the relative gap.** For `χ ∈ Irr_II`,
   `χ|_L = e(θ_1 + ⋯ + θ_t)` with the `θ_i` a single `K`-orbit of **nontrivial
   linear** characters of `L` (linear because `L` is abelian; nontrivial because
   a trivial constituent would put `χ` in `Irr_I`), and `χ(1) = et`. Hence for
   `h ∈ L`, `ψ_χ(h)/χ(1) = 1 − (1/t)Σ_i θ_i(h)` — the multiplicity `e` cancels.
3. **For `L = (ℤ/2)^Sites`** characters are subsets and, for a lamp element `a`,
   `ψ_χ(a)/χ(1) = 2·|{S ∈ orbit : |S ∩ supp(a)| odd}|/t`. In particular the
   two-site mark `w = a_p a_q` has normalized separation `2·`(fraction of the
   orbit containing exactly one of `p`, `q`), and a single lamp `a_p` has
   `2·`(fraction of the orbit containing `p`).

**Dilution is not the obstruction.** A generic orbit of subsets separates two
*distinct* sites on a fraction tending to `1/2`, so the mark gets separation
bounded below by an absolute constant with no dependence on the number of
sites. The `1/|A|` decay feared for the normalized support length comes from
choosing the wrong cone generator, not from the problem.

**The obstruction is relocated to site-distinctness.** `(LC5)` needs the model
to keep the two marked sites distinct. In a genuine finite quotient the
compression becomes an equality and the two marked cosets are identified, so
every orbit fraction is zero and the mark has length zero in *every* Hilbert
embeddable length. The character theory therefore reproduces
`finite-quotient-blindness` exactly.

**The character-gap route does not close.** Even granting the full relative gap
of item 1, it constrains `ℓ_II` only on `L`. The two-site rigidity theorem puts
the entire defect on the acting part, off `L`, where the relative gap says
nothing. "A vanishing defect must vanish identically" is then available only
for lamp-supported defects, of which rigidity says there are none. The two
results are consistent, not contradictory, and their combination yields no
obstruction.
