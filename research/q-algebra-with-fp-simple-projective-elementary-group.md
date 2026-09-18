---
rg: 2
id: q-algebra-with-fp-simple-projective-elementary-group
kind: claim
title: Some ring containing Q has finitely presented simple projective elementary groups PE_N(R) for infinitely many N
distinct_from:
  decidable-group-ring-has-fp-projective-simple-host: that asks, for each finitely presented decidable group H, for a finitely presented ring containing the group ring Z[H] with PEL_4 finitely presented and simple; this asks for one ring containing the field Q, with PE_N finitely presented and simple for infinitely many N, and no group ring.
  rational-leavitt-simple-group-embeds-in-fp-simple-group: that asks for a finitely presented simple overgroup of the countable group L_Q(1,2)^x/Q^x; this asks for the host to be itself a projective elementary group over a ring containing Q.
  psl-n-q-maps-nontrivially-to-fp-simple-groups: that is the weakest group-theoretic form of the root; this is a ring-theoretic sufficient condition for it.
  gl-n-q-embeds-in-fp-simple-group: that is the root; this is a sufficient hypothesis for it, through route gl-n-q-via-projective-elementary-hosts.
artifacts:
  - research/artifacts/gq-gq-en-ring-elementary-route.md
---

**OPEN.** There is a nonzero unital ring `R` with a unital map `Q -> R` such that
for infinitely many `N >= 3` the group `PE_N(R) = E_N(R)/Z(E_N(R))` is finitely
presented and simple.

By `q-algebra-elementary-quotients-contain-gl-n-q`, every `GL_n(Q)` then embeds in
one of these `PE_N(R)` (take `N >= n+2`). That is the route
`gl-n-q-via-projective-elementary-hosts` into `gl-n-q-embeds-in-fp-simple-group`.

**Sufficient single-rank form.** If `R ≅ M_2(R)` as unital rings, it is enough that
`PE_N(R)` be finitely presented and simple for **one** `N >= 3`. Part 5 of
`q-algebra-elementary-quotients-contain-gl-n-q` gives `PE_N(R) ≅ PE_(2^j N)(R)`.

## Necessary conditions (from landed nodes)

Let `N >= 3` be one of the ranks.
1. **`R` is finitely generated, simple and noncommutative.**
   - Finite generation: `rational-scalars-obstruct-fp-elementary-hosts`, part 1.
   - Simplicity: a nonzero proper ideal gives a normal congruence subgroup whose
     quotient `E_N(R/I)` is perfect and nontrivial, which contradicts simplicity of
     `PE_N(R)`. The argument is in
     `research/artifacts/boone-higman-projective-finiteness-gate-2026-09-08.md`.
   - Noncommutativity: no finitely generated commutative ring contains `Q`, since
     its residue fields are finite.
2. **`R` has no finitely generated structure constants over any characteristic-0
   field** (`fg-subrings-of-integral-form-algebras-omit-q`). So it is not a
   subring of a Leavitt path, group, Weyl, Cohn or finite-dimensional algebra, and
   its multiplication must create denominators at infinitely many primes.
3. **Rational scalars are almost never elementary.**
   `Λ_N(R) = {λ ∈ Q^x : λI_N ∈ E_N(R)}` is finitely generated
   (`rational-scalars-obstruct-fp-elementary-hosts`, part 2).
   - In particular `GL_N(R) != E_N(R)`.
   - The characteristic-2 Leavitt tensor template, whose key property is
     `K_1 = K_2 = 0`, is excluded (part 3 there).
   - A sufficient certificate is a finitely generated kernel of
     `K_1(Q) -> K_1(R)` (part 5 there).
4. **Finite presentation data.** If `R` is finitely presented and `N >= 4`, then
   `PE_N(R)` is finitely presented if and only if two things hold
   (`projective-elementary-fp-kernel-criterion`):
   - `ker(St_N(R) -> E_N(R))` is finitely normally generated in `St_N(R)`;
   - `Z(E_N(R)) = E_N(R) ∩ Z(R)^x I` is finitely generated.

   Here `Z(R)` is a field containing `Q`, because `R` is simple. So the elementary
   central scalars must form a finitely generated group. Condition 3 is the part of
   this that concerns `Q^x`.

## What is not known

- No finitely generated simple ring containing `Q` with the property of condition 3
  is recorded on main.
- No finite-presentation theorem for `St_N` over finitely presented noncommutative
  rings was read at its primary source by this lane. The statement for `N >= 4` is
  quoted in `research/artifacts/gq-gq-k2-q-uniformity.md` (N4), from
  `steinberg-finite-presentation-and-kazhdan-theorem`.
- No simplicity theorem for `PE_N(R)` over a general simple ring is used here. The
  available ones are:
  - Bass's sandwich classification, under a stable-range bound (to be read at the
    source before use);
  - the Leavitt and Steinberg-algebra results on main, which are over fields
    (`ample-steinberg-el-simple-mod-centre-without-hausdorff`,
    `leavitt-unit-groups-over-every-field-are-simple-mod-scalars`).

## Attempts

1. **Characteristic-0 Leavitt tensor hosts `B ⊗_Q L_Q(1,2)` with `K_1 = K_2 = 0`.**
   Dead, by `rational-scalars-obstruct-fp-elementary-hosts`, part 3. `Q^x I` becomes
   elementary and central, so `Z(E_N)` is not finitely generated. The same holds for
   their unit groups (part 4).
2. **Countable models.** The Weyl algebra `A_1(Q)` meets conditions 1 (except finite
   generation) and 3, if Quillen's `K_1` computation and Bass's theorem apply as
   recalled. This is recorded only as calibration; it is not finitely generated. A
   finitely generated ring with the same `K_1` behaviour is the open core.
3. **The Leavitt resolvent ring `R_L`** (`leavitt-resolvent-ring-is-fp-simple-of-char-zero`,
   a lane proof under review) is finitely presented and simple, contains `Q`, and
   satisfies `R_L ≅ M_2(R_L)`. So it is a candidate for the single-rank form above.
   - Condition 1 holds if that node stands.
   - Condition 3 is undecided: is `Λ_N(R_L)` finitely generated? This is the first
     test. Whitehead's lemma gives
     `λI_(2N) ≡ diag(λ^2 I_N, I_N) mod E_(2N)(R_L)`. So the question is whether
     `R_L` has a `K_1`-type invariant that sees `λ^2`.
   - The unit-group target `leavitt-resolvent-derived-units-mod-centre-fp-simple`
     meets the same test. If `D = [R_L^x, R_L^x]` is perfect or finitely generated,
     then `D/Z(D)` finitely presented forces `Q^x ∩ D` finitely generated. The
     argument is that of `rational-scalars-obstruct-fp-elementary-hosts`, part 4.
