# Review of the positive-characteristic Boone–Higman chain, 2026-09-12

Lane `bh-charp-chain-review` (adversarial). Read at tip `5c0603721`.

**Target.** Two claims read ESTABLISHED after 2b19d1c07 and d34e26446:
- `positive-char-linear-groups-satisfy-boone-higman`;
- `char-two-linear-groups-satisfy-boone-higman`.

**Scope.** Every node on both derivations EXCEPT the K-theory vanishing step, which belongs to sibling lane
`bh-charp-laurent-coherence-review`. Out of scope:
- `leavitt-tensor-powers-have-vanishing-k-theory-in-all-degrees`;
- `prime-field-leavitt-tensor-powers-have-trivial-k-theory`;
- `leavitt-tensor-powers-have-trivial-k-theory`;
- the Farrell–Jones and Nil imports.

**Verdicts.** PASS (holds as written, up to stated trust surfaces), GAP (a step is asserted but not proved),
FAIL (false).

## 0. The derivation

Read from front matter at `5c0603721`. The `cairn why` output on MSI is in §7.

**Root `positive-char-linear-groups-satisfy-boone-higman`**, through route
`positive-char-linear-groups-via-leavitt-projective-elementary` (artifact Theorem D). It requires:
1. **Embedding claim.** `char-p-linear-groups-embed-in-projective-leavitt-power-e-groups`, through
   `char-p-linear-embedding-corner-swindle-proof`, which requires:
   - `leavitt-tensor-kills-k1-of-coefficient-matrices`, through `leavitt-tensor-k1-coefficient-swindle-proof`
     (`requires: []`);
   - `leavitt-center-is-coefficient-field`;
   - `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`.
2. **Finite-presentation claim.** `leavitt-power-projective-elementary-groups-finitely-presented`, through
   `leavitt-power-projective-e-fp-from-trivial-k-theory`, which requires:
   - `prime-field-leavitt-tensor-powers-have-trivial-k-theory` (out of scope);
   - `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`.

Both use the host theorem `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`, through
`prime-field-leavitt-tensor-hosts-proof`. That route requires `khanh-acyclicity-and-steinberg-criteria`
(citation) and `leavitt-center-is-coefficient-field`.

**Root `char-two-linear-groups-satisfy-boone-higman`**, through route
`char-two-linear-groups-via-leavitt-tensor-powers` (artifact Corollary 7.4). It requires:
- `leavitt-tensor-powers-have-trivial-k-theory` (out of scope);
- `leavitt-tensor-hosts-acyclic-steinberg-and-fp`, through `leavitt-tensor-hosts-khanh-transfer-proof`, which
  requires the Khanh criteria;
- `central-simple-leavitt-tensor-unit-groups-are-simple`, through `central-simple-leavitt-tensor-simplicity-proof`,
  which requires:
  - `leavitt-tensor-hosts-acyclic-steinberg-and-fp`;
  - `binary-leavitt-elementary-group-is-simple`;
  - `leavitt-center-is-coefficient-field`;
- `char-two-surface-linear-groups-satisfy-boone-higman`.

## 1. Verdicts already on record

| Node | Earlier verdict |
|---|---|
| `char-p-linear-groups-embed-in-projective-leavitt-power-e-groups` (corner-swindle repair) | PASS, review-backlog §16 (the first route FAILed, review-bh-swarm §5) |
| `leavitt-tensor-kills-k1-of-coefficient-matrices` | PASS, review-bh-swarm §11 and review-backlog §16 (re-derived) |
| `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` / `-proof` | PASS, reviewer-2 §3 |
| `leavitt-tensor-hosts-acyclic-steinberg-and-fp` / `leavitt-tensor-hosts-khanh-transfer-proof` | PASS, reviewer-2 §1 |
| `central-simple-leavitt-tensor-unit-groups-are-simple` | PASS, reviewer-2 table |
| `khanh-acyclicity-and-steinberg-criteria` | PASS at statement level, review-bh-swarm §1 |
| `char-two-surface-linear-groups-satisfy-boone-higman` | PASS, review-backlog-2 §7 |
| `leavitt-center-is-coefficient-field` | PASS, several reviews (Lean, every field) |

**What the earlier passes did not cover.**
- The two root routes.
- `leavitt-power-projective-e-fp-from-trivial-k-theory`. It was OPEN at the time, so review-backlog-2 gave it no
  verdict.
- Whether the earlier host passes hold uniformly in the number of tensor factors, now that `B` is itself a tensor
  power with `d - 1 >= 2`.

## 2. New verdicts

### 2.1 `positive-char-linear-groups-via-leavitt-projective-elementary` (Theorem D): PASS

It composes two claims. Given `H`:
- the embedding claim gives `M_0`, with `H` embedded in `P_M = E_M(R_(d+1)) / Z` for every
  `M >= max(M_0, 3)`;
- the finite-presentation claim at `d+1` factors gives `P_M` finitely presented.

The route text asks only for infinitely many `M`, which is all that is needed. The consumed claim in fact gives every
`M >= 2`. Nothing else enters.

### 2.2 `leavitt-power-projective-e-fp-from-trivial-k-theory`: PASS, conditional on the out-of-scope `K`-theory claim

Line by line, with `R_d = R_(d-1) ⊗ L_p`:
1. **`B = R_(d-1)` is simple, central and finitely presented.**
   - By induction on `d`: over a field, a central simple algebra tensored with a simple algebra is simple, and
     `Z(A ⊗ B) = Z(A) ⊗ Z(B)`. `L_p` is central simple (`leavitt-center-is-coefficient-field` plus simplicity of
     `L_p`).
   - Tensor products of finitely presented `F_p`-algebras are finitely presented: take the union of generators, the
     relations, and commutation of the two generating sets. Adding `p = 0` makes it a finitely presented ring, which
     is what Krstić–McCool needs.
   - For `d = 1`, `B = F_p`.
2. **Unit group.** Parts 2 and 3 of the host theorem with this `B`, under `K_1(R_d) = K_2(R_d) = 0`, give
   `GL_m(R_d) = E_m(R_d)` for `m >= 2` and `R_d^x` finitely presented.
3. **Every rank.** `L_p ≅ L_p^2` as right modules by leaf coordinates, so `R_d ≅ R_d^m` and
   `M_m(R_d) ≅ End(R_d^m) ≅ R_d`. So `E_m(R_d) = GL_m(R_d) ≅ R_d^x`, finitely presented for every `m >= 2`.
   Citing Ara–Goodearl–Pardo for `gcd(m, 1) = 1` is correct but not needed.
4. **Centre.** `Z(GL_m(R_d)) = Z(R_d)^x I = F_p^x I` is finite, and a finitely presented group modulo a finite
   central subgroup is finitely presented.

The claim is stated for infinitely many `m`; the route proves every `m >= 2`. No error.

### 2.3 Uniformity of the host theorem in the number of factors: PASS

Parts 1–3 of `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre` are stated for an arbitrary simple unital
`F_p`-algebra `B`. The only property of `B` that enters is its simplicity. Reviewer-2 §1 checked the transfer for
general simple `B`, and I checked the places where the number of factors could matter.

- **`A^2 ≅ A` (Khanh Theorem 2.2).** Holds for `A = B ⊗ L_p`, from `L_p ≅ L_p^2` in the last factor.
- **Simultaneous strong division (artifact Lemma 2.2).** It uses `Σ y_k c z_k = 1`, which is simplicity of `B ⊗ L_p`
  and so of `B`. It also uses same-length distinct Leavitt words in the last factor. No property of `B` beyond
  simplicity.
- **Frame complex (Theorem 5.1 hypothesis (3)).** Simple connectivity comes from Proposition 4.2 over `R`, which
  consumes only Lemma 2.2.
- **Standard inclusions (Proposition 3.1).** The compression `c` and the unit `w` live in `e, f` of the last factor.
  The stable input is exactly the `K`-theory hypothesis on `R`.
- **GE (Menal–Moncasi remark).** It needs a simple ring with strong division. Both hold.
- **Krstić–McCool.** Needs `R` finitely presented. See §2.2 step 1.

No step uses `B = F_p`, `B = L_p`, regularity or coherence of `B`, or any `d = 2` fact.

The out-of-scope `K`-theory claim is where the refuted coherence would have mattered (`leavitt-tensor-powers-are-not-left-coherent`).
The host theorem never assumes coherence. Ara–Cortiñas regular supercoherence entered only the `d <= 2` `K`-theory
input, which is not consumed here.

### 2.4 Simplicity modulo scalars for every `d` (part 4, first bullet): PASS, paper argument

The embedding route applies it with `B = R_d` central simple. The hypotheses of the Lean root-detection theorems, as
reviewer-2 §3 read them, are:
- `3 <= card ι`, true for `M >= 3`;
- a `LeavittFamily`, from `1 ⊗ L_p`;
- `hdiv`, from Lemma 2.2, which is simplicity of `B`;
- `hcentral`, used only to choose a noncentral `g` (`DiagonalNormalExtraction.lean`, line 86). Replacing it by the
  scalar centre `F_p^x` needs only `Z(R_(d+1)) = F_p`, which holds for every `d` by the centre formula.

Nothing depends on `d`. Trust surface unchanged: the odd-`p` and `B ⊗ L` versions are paper applications of Lean
theorems stated for general rings, and no Lean instance of `R_(d+1)` is built.

### 2.5 `char-two-linear-groups-via-leavitt-tensor-powers` (Corollary 7.4): PASS, conditional on the `K`-theory claim

- **Input.** `H <= GL_(nm)(F_2[t_1..t_d][1/h])` (Theorem 7.2, steps 1–3). For `d = 0`, `H` is finite and lies in
  `GL_N(F_2) <= L^x`.
- **Ring embedding.** Lemma 7.1 (§2.6) embeds the coordinate ring in `L^(⊗d)`. Leaf coordinates then give
  `H <= (L^(⊗d))^x`.
- **Finite presentation.** Part 3 of `leavitt-tensor-hosts-acyclic-steinberg-and-fp` with `B = L^(⊗(d-1))`, which is
  simple and finitely presented (§2.2 step 1).
- **Simplicity.** Part 2 of `central-simple-leavitt-tensor-unit-groups-are-simple` with `B` central, so
  `Z(R)^x = F_2^x = 1`.

The prerequisite `char-two-surface-linear-groups-satisfy-boone-higman` is cited only for the `d = 2` step of Lemma 7.1.
It is not logically needed, since Lemma 7.1 is proved for all `d` directly.

### 2.6 Lemma 7.1 and Lemma A (coordinate ring inside `L^(⊗d)` for every `d`): PASS

Re-derived by induction on `d`, characteristic-free.

**Normalization.** Write `h = c t_d^k + (lower)` with `c ∈ C_0 = F_p[t_1..t_(d-1)]` nonzero, and put `C = C_0[1/c]`.
- `f = t_d h / c` is monic of degree `k + 1 >= 1` in `C[t_d]`.
- `c f = t_d h`, so `1/h = t_d / (c f)` lies in `C[t_d][1/f]`.
- So `F_p[t_1..t_d][1/h] ⊆ C[t_d][1/f]`.
- The induction hypothesis is applied to `C_0[1/c]`, which is the statement at `d - 1` with `h' = c`.

**Free presentation.** `T ↦ t_d`, `g ↦ f(t_d)` gives `C[g^±][T]/(f(T) - g) ≅ C[t_d][1/f]`. The inverse sends `1/f`
to `g^-1`. Since `f(T) - g` is monic in `T`, the quotient is free over `C[g^±]` of rank `k + 1`. The multiplication
representation is faithful because the module contains `1`. So `C[t_d][1/f] ↪ M_(k+1)(C[g^±])`.

**Into the tensor power.** Injective maps of `F_p`-vector spaces stay injective after tensoring, and
`F_p[g^±] ↪ L_p` by the Thompson unit (PASS, review-backlog-2 §5). So
`C[g^±] = C ⊗ F_p[g^±] ↪ L^(⊗(d-1)) ⊗ L`, and `M_(k+1)(L^(⊗d)) ≅ L^(⊗d)`.

**Reduction to a coordinate ring.** A finitely generated `H` has a finitely generated entry field, of some finite
transcendence degree `d`. It is a finite extension of `F_p(t_1..t_d)`, so the regular representation and one common
denominator place `H` in `GL_N(F_p[t_1..t_d][1/h])`.

## 3. Statement fidelity: PASS

The root reads: "Let `K` be a field of characteristic `p > 0` and `H <= GL_n(K)` finitely generated. Then `H` embeds
in a finitely presented simple group."
- **Any transcendence degree.** The entry field is finitely generated. Theorem C takes "transcendence degree at most
  `d >= 1`", so `d = 0` is covered by `d = 1`.
- **Every prime, including `p = 2`.** `prime-field-leavitt-tensor-hosts-proof` covers every prime (step 5: at `p = 2`
  the signs are trivial and `z = 1`). The characteristic-two root also has its own route through `(L^(⊗d))^x`.
- **Every `n`.** The regular representation and leaf coordinates handle every `n`.
- **Hidden restrictions.** I found none. The host depends on `H`: it is `E_M(L_p^(⊗(d+1))) / F_p^x` with `M` and `d`
  read off `H`. That is all Boone–Higman asks.

## 4. Consistency with the characteristic-zero obstruction: PASS

`char-zero-algebra-unit-hosts-exclude-unipotents` does not reach characteristic `p`, for three independent reasons.
1. **Its scope.** It is stated for `Q`-algebras.
2. **Hypothesis (D) fails.** (D) needs a subring in which each nonzero element lies in `qB` for only finitely many
   primes `q`. In an `F_p`-algebra every prime `q != p` is invertible, so `qB = B` contains every element, and (D)
   fails.
3. **The mechanism is gone.** The argument reduces modulo infinitely many primes and uses logarithms of torsion-free
   unipotents. In characteristic `p`, `(1 + ν)^(p^k) = 1 + ν^(p^k) = 1`, so unipotents are torsion and no congruence
   quotients exist to separate them.

That claim's own `distinct_from` note records the same contrast.

## 5. Khanh criteria for every `d`: see §7

The import node quotes these statements:
- **Theorem 2.2:** "nonzero unital F_2-algebras" with `A^2 ≅ A`. The odd-`p` form is the graph's own adaptation
  (reviewer-2 §3, PASS).
- **Theorem 5.1:** "a nonzero unital ring of characteristic two", with the signed adaptation for odd `p`.
- **Lemma 5.2:** "any unital ring".
- **Krstić–McCool:** "every finitely presented associative unital ring and every `n >= 4`".

None of them bounds the number of tensor factors or assumes regularity. The re-check against the source text is in §7.

## 6. Literature and novelty: see §7

## 7. MSI results

Pending: the detached job `/scratch.global/sauer354/charp-chain-review/why.sh`.

## 8. Overall verdict, before the MSI results

**PASS**, on the scope reviewed, conditional on:
- the out-of-scope `K`-theory vanishing step;
- the recorded trust surfaces: Khanh arXiv:2609.08428v1 is unrefereed; Menal–Moncasi, Voronetsky and Krstić–McCool
  are quoted through Khanh; the simplicity step applies Lean theorems on paper.

No FAIL or GAP found. Bookkeeping, not errors:
- The `M_0` name mismatch in the embedding route (review-backlog §16).
- The finite-presentation claim says "infinitely many `m`" but proves every `m >= 2`.
