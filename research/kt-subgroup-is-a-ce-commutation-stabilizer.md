---
rg: 2
id: kt-subgroup-is-a-ce-commutation-stabilizer
kind: claim
title: The Kun--Thom polynomial subgroup is an exact commutation stabilizer in some Connes-embeddable target
distinct_from:
  kt-centralizer-normalization-hs: that asks whether every tracial matrix-ultraproduct model normalizes the Kazhdan relative commutant; a positive answer to this claim refutes that normalization, but this claim allows arbitrary Connes-embeddable targets and arbitrary traces and asks for an exact stabilizer rather than a bare wall.
  kt-q2-double-hyperlinear-iff-relative-embeddable: that identifies hyperlinearity of the double with relative embeddability of one vertex inclusion; this is an equivalent but trace-free search formulation of the same property, recorded because it widens the admissible constructions.
  relative-embedding-is-commutant-separation: that is the general canonical-model characterization for any subgroup; this is the concrete open instance for the Kun--Thom pair, stated without any canonical-trace requirement.
---

**OPEN.** For the binary Kun--Thom Theorem E pair

```text
Gamma = EL_r(F_2[x_1,...,x_d]) <= G = EL_r(F_2[x_1^(+-1),...,x_d^(+-1)]) rtimes SL_d(Z),   r,d >= 3,
```

find a Connes-embeddable finite von Neumann algebra `M`, a homomorphism
`sigma : G -> U(M)` (any trace, not necessarily injective), and a countable
family `(x_i) subset M` with

```text
{g in G : [sigma(g), x_i] = 0 for all i} = Gamma.                 (KCS1)
```

By `ce-stabilizer-criterion-needs-no-trace` this is equivalent to
relative embeddability of `L(Gamma) <= L(G)` over the scalars, hence to
hyperlinearity of the Kun--Thom double, wreath and centralizer HNN group.
With `kt-pair-group-double-is-nonsofic` it would answer Pestov's
Question 3.4 negatively. It is recorded as its own node because it lets the
model be non-canonical: the trace, and even injectivity, are free.

## Attempts

- **Haagerup targets.** Hyperfinite algebras, free group factors, amalgams
  over amenable subalgebras. Dead: `haagerup-targets-carry-no-relative-wall`
  proves that no infranormal non-normal Kazhdan subgroup is a commutation
  stabilizer when its image algebra has the Haagerup property. Recorded as
  the invalidated route `kt-ce-stabilizer-from-haagerup-target`.
- **Normalizing witnesses.** Amenable extensions `G rtimes K`, direct factors,
  unitaries implementing automorphisms of `sigma(G)`. Dead:
  `kt-normalizing-witnesses-centralize-compressors` (`C_G(Gamma) = 1`).
  Recorded as the invalidated route
  `kt-ce-stabilizer-from-normalizing-overgroup`.
- **Finite-dimensional isotypic structure.** The finite-dimensional isotypic
  projection `z` of `sigma|Gamma` is fixed by every compressor, hence commutes
  with `sigma(G)`, so each witness splits as `x_i z + x_i (1 - z)` without
  changing its stabilizer. By `fd-isotypic-part-of-a-kazhdan-image-carries-no-wall`
  and step 4 of `haagerup-no-wall-proof`, a family supported on `z` stabilizes
  `t^(-1) Gamma t` for every compressor. So the witnesses that cut the
  stabilizer down to `Gamma` must live on `1 - z`, where `sigma|Gamma` has no
  finite-dimensional subrepresentation, as in the canonical models.
- **Canonical Fell models over Haagerup coefficients.** Tensor a tame
  coefficient `pi` with the regular representation. Dead:
  `kt-fell-models-over-haagerup-coefficients-are-wall-free`. The polynomial
  subgroup has infinite conjugacy classes
  (`kt-polynomial-subgroup-is-icc-in-kt-group`), so the relative commutant of
  `lambda tensor pi` is `1 tensor` that of `pi`
  (`fell-models-inherit-walls-from-coefficients`). Recorded as the invalidated
  route `kt-ce-stabilizer-from-fell-haagerup-model`.
- **Genuine finite-dimensional ultraproducts.** Once the `Gamma`-part is
  exact, dimension counting (`commutant-no-growth`) fixes the commutant; see
  `kt-wreath-relative-canonical-actor-exactification` for where
  exactification itself is open.
- **The universal target.** `M = L(G *_Gamma (Gamma x Z))` works exactly
  when this claim holds, so it proves nothing on its own.

Remaining room: a non-Haagerup Connes-embeddable target that is not a Fell
model over a Haagerup coefficient, for instance a tracial matrix ultraproduct or
`L(H)` for a hyperlinear overgroup `H` of `G`, with a witness that does not
normalize `sigma(G)`.

**A weaker target suffices for Question 3.4.** By
`kt-intermediate-coset-wreaths-are-nonsofic`, any exact stabilizer `K` with
`Gamma <= K` and `EL_r(R)` not contained in `K` gives a nonsofic coset wreath
`W_K`. By `ce-stabilizer-criterion-needs-no-trace` (applied to `K`) and the coset
equivalence, `W_K` is then hyperlinear. The Haagerup, normalizing-witness and
Fell obstructions above still apply to this weaker target, because each forces
every stabilizer containing `Gamma` to contain the normal closure `EL_r(R)`. The
Haagerup and Fell obstructions do this by normalizing the `Gamma`-commutant; the
normalizing-witness obstruction does it by making the witness central in
`sigma(G)`.
