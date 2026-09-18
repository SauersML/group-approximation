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
   satisfies `R_L ≅ M_2(R_L)`. **Dead** for this claim: `R_L` has a Leavitt `(1,2)`
   family, so `λI_N ∈ E_N(R_L)` for every `λ ∈ Q^x` and every `N >= 2`
   (`ibn-failure-makes-rational-scalars-elementary`, part 3). Hence `PE_N(R_L)` is not
   finitely presented for any `N >= 3`. The unit-group form is refuted separately by
   `leavitt-scalar-commutators-block-fp-central-quotients`. The notes below, written before
   the kill, record the test it failed.
   - Condition 1 holds if that node stands.
   - Condition 3 fails: `Λ_N(R_L) = Q^x`. The Whitehead reduction
     `λI_(2N) ≡ diag(λ^2 I_N, I_N)` noted earlier is superseded by the direct proof.
   - The unit-group target `leavitt-resolvent-derived-units-mod-centre-fp-simple`
     meets the same test. If `D = [R_L^x, R_L^x]` is perfect or finitely generated,
     then `D/Z(D)` finitely presented forces `Q^x ∩ D` finitely generated. The
     argument is that of `rational-scalars-obstruct-fp-elementary-hosts`, part 4.
4. **Class restriction and a countable calibration (2026-09-17).**
   - By `ibn-failure-makes-rational-scalars-elementary`, a host needs `R ≇ R^d` for
     every `d >= 2`. More generally, `R^m ≅ R^(m+k)` kills every rank `m'N` with
     `m' >= m` and `N >= 2`.
   - This is not a no-go for purely infinite simple rings.
     - Take the finite graph `E` with vertices `u, w`: three loops at `u`, one edge
       `u -> w`, two loops at `w`, and two edges `w -> u`. Then `L_Q(E)` is simple and
       purely infinite. `K_0 = Z^2 / <(2,1)>` is `Z`, generated by `[1] = [u] + [w]`, so
       `L_Q(E)` has no Leavitt `(1,d)` family.
     - By Ara–Brustenga–Cortiñas (arXiv:0903.0056v2, Thm 7.6, for regular supercoherent
       coefficients and row-finite `E`), `coker(1 - N_E^t)` on `(Q^x)^(E^0)` embeds in
       `K_1(L_Q(E))`. The image of `1 - N_E^t` is `{(ρ^2, ρ)}`, so `(λ, λ)` is trivial
       only for `λ = 1`.
     - Granting that the map is induced by the vertex inclusions, which is recalled and
       not re-read, `Q^x -> K_1(L_Q(E))` is injective, so `Λ_N(L_Q(E)) ⊆ {±1}`.
     - `PE_N(L_Q(E))` is simple for `N >= 3`
       (`ample-steinberg-el-simple-mod-centre-without-hausdorff`).
     - So this countable ring passes conditions 1–3 except finite generation. A proof that
       no host exists must use finite generation of `R`.
     - **The next cost is in `K_2`.** By `rational-leavitt-path-k1-k2-scalar-dichotomy`
       (lane `gq-malcev-ring`), when `[1]` has infinite order the image of
       `K_2(Q) -> K_2(L_Q(E))` is not finitely generated. For a finitely presented host of
       this type, that is the first thing to test against condition 4, finite normal
       generation of `ker(St_N(R) -> E_N(R))`. It obstructs only if that kernel is
       central or controlled by stable `K_2`.
   - **Spark (not pursued).** Add the resolvent generators `N, A` of `R_L` to `L_Z(E)`,
     using the Cuntz–Toeplitz pair `s_i = e_i + g_i` (loops at `u` plus loops at `w`, so
     `t_i s_j = δ_ij` and `Σ s_i t_i != 1`). That pair is enough for
     `1/m = t_2 t_1^(m-1) A s_1^(m-1) s_2`. Whether the result is simple, and whether
     `[1]` stays of infinite order, is open.
5. **Tracial hosts and the stable symbol lemma (2026-09-17, lane gq-deep-adelic-1).**
   - **Condition 3 can be met.** `tracial-harmonic-ring-keeps-rational-scalars` is finitely
     generated, simple, with centre `Q` and `Λ_N ⊆ {±1}`. It is the harmonic function inside
     `C(X) ⋊_σ Z` over a minimal subshift, and the Fuglede–Kadison determinant keeps the scalars
     out of `E_N`. So conditions 1 and 3 hold together for a finitely generated simple ring.
   - **It dies at condition 4.** `laurent-rational-symbols-block-fp-elementary-groups`: for every
     skew Laurent ring over a base that detects `Q^x` in `K_1`, the symbols `{λ, u}` are
     infinitely generated in `K_2`, so no `E_N` is finitely presented.
   - **The centrality proviso of item 4 is not needed.**
     `infinitely-generated-symbols-block-fp-elementary-groups`: if `E_N(R)` is finitely
     presented, the image of `K_2(N, R)` in stable `K_2(R)` is finitely generated and contains
     every Steinberg symbol. So an infinitely generated image of `K_2(Q) -> K_2(R)` excludes `R`,
     whether or not `K_2(N, R)` is central.
   - **What is left.** A finitely generated simple `R ⊇ Q` with the "UHF K-budget": `Q^x`
     detected in `K_1` up to a finitely generated kernel, and finitely generated rational symbols
     in `K_2`. `U_Q = colim M_(n!)(Q)` has it but is not finitely generated. See
     `research/artifacts/gq-deep-adelic-1-k-budget.md`.
6. **UHF-type groupoid models (2026-09-17, lane gq-deep-adelic-1).** The coordinator's target was a UHF-like host
   built from an odometer-type minimal action. Class verdict in
   `research/artifacts/gq-deep-adelic-1-uhf-class-verdict.md`:
   - **AF groupoids fail at Q.** `af-groupoid-rings-have-no-fg-subring-containing-q`: for the tail groupoid of
     any Bratteli diagram, no finitely generated ring of compactly supported functions contains `Q`, whatever
     the coefficients. The reason is `fg-q-rings-have-no-matrix-representations`.
   - **Z-actions and virtually indicable groups fail at condition 4.**
     `matrix-corner-laurent-rings-block-fp-elementary-groups`: a crossed-product ring over an odometer factor
     whose chain contains an indicable finite-index subgroup is `M_k` of a skew Laurent ring with a tracial
     base. So no `E_N` is finitely presented. Perfection of the acting group does not help.
   - **Remnant.** Acting groups with finite abelianization along the whole chain, e.g. `SL_n(Z)`, `n >= 3`.
     Open risks: non-divisible cylinder corners, and torsion index units whose symbols factor through
     `Q^x ⊗ Z/d`.
7. **The SL_3(Z) remnant: first candidate (2026-09-18, lane gq-deep-adelic-1).**
   `sl3-toeplitz-harmonic-ring-is-simple-and-k1-rational`: a finitely generated simple ring `R_T` over a
   Toeplitz `SL_3(Z)`-subshift (Cecchi Bernales–Cortez–Gómez) with an odometer factor. It has:
   - `Q ⊆ R_T`, by `harmonic-elimination-puts-q-in-odometer-crossed-products`, with no clopen sets
     needed;
   - centre `Q`;
   - `Λ_N ⊆ {±1}`, so conditions 1 and 3 hold, and `GL_n(Q) ⊆ PE_N(R_T)`;
   - `K_2(Q)` killed by matricial divisibility;
   - no Laurent unit on any block;
   - trivial rational symbols on group units and block units
     (`sl3-congruence-transfer-kills-abelianization`: the transfer `Γ(d)^ab -> Γ(d^2)^ab` vanishes).

   Open: the rest of condition 4's K-theoretic necessary part
   (`sl3-toeplitz-harmonic-ring-meets-the-uhf-k-budget`: letter-cylinder corners and general units),
   and then finite presentation and simplicity of `PE_N(R_T)`. See
   `research/artifacts/gq-deep-adelic-1-sl3-remnant.md`.
