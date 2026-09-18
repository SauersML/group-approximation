# Referee report (citation/hypothesis lens): `resolvent-ring-corner-symbols-survive-in-k2` and the OPEN `resolvent-steinberg-rf-residual-is-infinitely-normally-generated`

Referee: lane gq-referee-b, 2026-09-18. Reviewed: both nodes as landed at e27bd0bd3 (gq-k2-q).

## Verdicts

- **`resolvent-ring-corner-symbols-survive-in-k2`: PASS**, with one wording fix (W1).
- **`resolvent-steinberg-rf-residual-is-infinitely-normally-generated`: the proof is correct modulo (DS) and (vdK).**
  - **I could not confirm (DS) or (vdK) at a source**: the primaries are paywalled, and no open secondary source
    quoting them was found.
  - Both are standard classical results, and the node states them correctly as far as I know. But this report
    does **not** discharge them.
  - See §3 for how to proceed. I did not edit the node; its owner decides.

## 1. The corner-symbol node

**`J` is an ideal. Correct**, given the refereed path normal form.
- Products concatenate middle words.
- `x^c` and `f(u)` act on the end letters.
- The direct-sum decomposition gives `J ∩ D = 0` and `J ∩ span{[a||b]} = 0`.

**The quotient. Correct.**
- `[a||b][a'||b'] = [a||b']` iff `b + a' = 0`, and `0` otherwise, modulo `J`. That is the matrix-unit rule
  `E_{a,−b}E_{a',−b'} = δ_{−b,a'}E_{a,−b'}`, so `(e)/J ≅ M_Z^{fin}(Z_(l))`.
- `R_l/J = D ⊕ M` is split: `D` is a subring meeting `(e)` in `0`, and `R_l/(e) ≅ D`.
- `θ(c) ↦ cE_{0,0}`.

**`K_2`. Correct.**
- `M` is a filtered union of the unital rings `M_S(Z_(l))`, so it has local units, hence is Tor-unital. Suslin's
  excision, as quoted from Tamme on main, applies to the split surjection `R_l/J → D` with kernel `M`. So
  `K_2(R_l/J) ≅ K_2(D) ⊕ K_2(M)`.
- `K_2` commutes with filtered colimits, and Morita invariance gives `K_2(M) ≅ K_2(Z_(l))` through the corner
  `E_{0,0}`.
- The composite `K_2(Z_(l)) → K_2(R_l) → K_2(R_l/J)` is the split inclusion. `θ` is non-unital, so it is used through
  `A ↦ A + (1−e)I_N`, which is correct. So `θ_*` is injective.

**Corner symbols. Correct.** `St_N(θ)` preserves `K_2(N,·)`, and stabilization commutes with it, so the stable class of
`c(λ,μ)` is `θ_*{λ,μ}`.

**Infinite generation. Correct**, apart from W1.
- The tame symbol `∂_q{q, g_q} = g_q^{−1} mod q` (Milnor, §11).
- A finitely generated subgroup of the torsion group `K_2(Q)` is finite, so it has only finitely many nonzero
  components.
- Images of finitely generated groups are finitely generated, so the subgroup of `K_2(Z_(l))` is not finitely
  generated either.

**W1.** "a nonzero tame symbol `∂_q` for every prime `q ≠ l`" should read "for every **odd** prime `q ≠ l`". For `q = 2`,
`F_2^×` is trivial, so `∂_2` vanishes. Infinitely many odd `q` remain, so the conclusion stands.

## 2. The OPEN node: proof given (DS) and (vdK)

- **Step 1.** Finite quotients factor through `St_N(F)` for a finite quotient ring `F`
  (`steinberg-rf-forces-ring-rf`, passed in 982f98fc3). The corner image of `Z_(l)` in `eFe` is `Z/l^r` or `0`.
  **Correct.**
- **Step 2.**
  - (vdK) gives `K_2(N, Z/l^r) ↪ K_2(Z/l^r)` for `N >= 3`, since `Z/l^r` is local.
  - (DS) makes the target `0` for odd `l`, and of order at most `2` for `l = 2`.
  - So every `c(λ,μ)` lies in `K_rf` for odd `l`.
  - For `l = 2`, the kernel of the map to `lim_r K_2(N, Z/2^r)` (order at most `2`) has index at most `2`, and it lies in
    `K_rf`.
  - **Correct**, given (DS) and (vdK).
- **Step 3.**
  - `K_rf ⊆ K_2(N, R_l)`, because `E_N(R_l)` is residually finite (`R_l` is).
  - Kervaire: `K_2(R_l)` is central in `St(R_l)` (Milnor, Theorem 5.1). So the stable image of the normal closure of a
    finite set is finitely generated.
  - **Correct.**
- **Step 4.**
  - A non-finitely-generated subgroup of the abelian group `K_2(R_l)`, from the companion node, lies in `ι(K_rf)`.
  - For `l = 2` this is the index-`2` subgroup, still not finitely generated.
  - So `K_rf` is not finitely normally generated. **Correct.**

## 3. (DS) and (vdK): status and recommendation

- **(DS).** `K_2(Z/l^r) = 0` for `l` odd, and `K_2(Z/2^r)` has order at most `2`. This matches the standard
  statement `K_2(Z/n) ≅ Z/2` if `4 | n`, and `0` otherwise, due to Dennis–Stein (1973/75). Source not read. My earlier
  report ef36a82a9 also recorded it as "not read at source". This is not a verification.
- **(vdK).** Van der Kallen, *Injective stability for K_2*, LNM 551 (1976) 77–154, gives injectivity of
  `K_2(n,R) → K_2(n+1,R)` for `n >= sr(R) + 2`. Local rings have `sr = 1`, so it holds for `n >= 3`. The node's form is
  consistent with that. The title and venue were confirmed by search; the text was not read.
- **Recommendation.**
  - The swarm's convention for classical inputs marked "not re-read" varies. For example, Matsumoto and Tate were
    accepted in `one-steinberg-group-contains-every-gl-n-q`.
  - If that convention applies here, the node may be flipped to ESTABLISHED with (DS) and (vdK) named as trust
    surfaces, citing this report.
  - Under strict RULES §5 (verbatim citations), keep it OPEN until someone reads the primaries. Paywalled PDFs can
    be fetched through the MSI route in the repo's memory notes.
  - The downstream conclusion, that the route `z-localized-fp-rf-via-resolvent-steinberg-rf-quotient` is closed,
    should carry the same caveat.
