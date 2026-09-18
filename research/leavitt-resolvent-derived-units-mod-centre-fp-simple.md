---
rg: 2
id: leavitt-resolvent-derived-units-mod-centre-fp-simple
kind: claim
title: For the Leavitt resolvent ring R_L, the derived unit group [R_L^x, R_L^x] modulo its centre is finitely presented and simple
distinct_from:
  leavitt-resolvent-ring-is-fp-simple-of-char-zero: that is the ring statement (finitely presented, simple, contains Q); this is the group statement needed to reach the root.
  leavitt-unit-group-finitely-presented: that is Khanh's finite presentation of L_(F_2)(1,2)^x in characteristic two; this is the characteristic-zero analogue for R_L, whose unit group has the non-finitely-generated centre Q^x.
  binary-leavitt-unit-group-is-simple: that is simplicity of L_(F_2)(1,2)^x = EL_3; this asks for simplicity modulo the centre in characteristic zero.
---

**OPEN.** Let `R_L` be the ring of `leavitt-resolvent-ring-is-fp-simple-of-char-zero`,
`D = [R_L^x, R_L^x]`, and `Z(D)` its centre. Then `D/Z(D)` is finitely presented and
simple.

**Why.** `GL_n(Q)` embeds in `D` and meets `Z(D)` trivially, for every `n`
(`leavitt-resolvent-ring-is-fp-simple-of-char-zero`, part 3). So this claim gives
`gl-n-q-embeds-in-fp-simple-group` through `gl-n-q-bh-via-leavitt-resolvent-units`.

## Attempts

1. **Characteristic-two model.** For `L = L_(F_2)(1,2)`:
   - `L^x = GL_3(L) = EL_3(L)` is simple (`binary-leavitt-unit-group-is-simple`);
   - `L^x` is finitely presented by Khanh, arXiv:2609.08428v1, Thm 6.1, through a
     Steinberg comparison and Krstić--McCool (`leavitt-unit-group-finitely-presented`).

   The same two steps are the natural attack here, with two differences, as expected
   (lane `gq-ring-fp-simple`, 2026-09-17):
   - the centre `Q^x` of `R_L^x` must be divided out;
   - the base ring `B = Q[N][(N+c)^(-1)]` is not finitely generated, although `R_L` is
     finitely presented.

   Neither step has been attempted yet. Lanes `gq-en-ring`, `gq-leavitt-units` and
   `gq-k2-q` own the `St`/`K_2` side.
2. **A caution.** `D` need not be finitely generated. The claim asks only for the
   quotient `D/Z(D)`. A weaker sufficient target is any finitely presented simple
   subquotient of `R_L^x` that still contains a copy of `SL_(n+2)(Q)` meeting the
   centre trivially.
3. **Expected obstruction: the rational scalars (conditional, not proved).** This is
   likely FALSE as stated.
   - *Scalars die in `K_1`.* Covariance gives `ψ(λ) = λ I_2` for `λ ∈ Q^x`, so under
     `M_2(R_L) ≅ R_L` the scalar `λ` corresponds to `diag(λ, λ)`, and in `K_1`,
     `[λ] = 2[λ]`, so `[λ] = 0`. The algebraic Pimsner-type sequence (Carlsen--Ortega;
     Ara--Brustenga--Cortiñas type) gives the same answer:
     `(1 - [ψ])[λ] = -[λ]` on `K_1(B)`.
   - *Scalars enter `D`.* If `K_1(R_L) = U(R_L)^ab`, as Ara--Goodearl--Pardo prove for
     purely infinite simple rings, then `Q^x <= D` and `Q^x <= Z(D)`.
   - *Consequence.* If moreover `D` is perfect and `D/Z(D)` were finitely presented, then
     `D` would be a perfect central extension of a finitely presented perfect group. So
     `Z(D)` would be a quotient of the finitely generated Schur multiplier
     `H_2(D/Z(D))`. It would then be finitely generated, but it contains `Q^x`. That is a
     contradiction.

   Unproved inputs: purely infinite simplicity of `R_L` for the AGP theorem, perfectness
   of `D`, and the exact sequence in this generality. The same heuristic applies to every
   Leavitt--Nekrashevych completion of a `Q`-algebra, since `ψ(λ) = λ I_d` always kills
   `(Q^x)^(d-1)` in `K_1`. It is the unit-group form of gq-en-ring's criterion
   `rational-scalars-obstruct-fp-elementary-hosts` (`Λ_N` must be finitely generated).
   **Where this leaves the route.** `R_L` settles the ring question
   (`fp-simple-ring-of-characteristic-zero-exists`). For the group target, any overgroup
   inside `R_L^x` that contains Thompson-type units together with `GL_n(Q)` probably
   contains all of `Q^x` centrally, because `diag(λ,1)` and its `V`-conjugate multiply
   to `λ`. So the finitely presented simple group must come from a subgroup that avoids
   `Q^x`, or from a ring where `ker(Q^x -> K_1)` is finitely generated.
