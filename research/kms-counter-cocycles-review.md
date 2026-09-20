---
rg: 2
id: kms-counter-cocycles-review
kind: claim
title: Referee review of kms-counter-cocycles-reduce-to-central-lamp-mixing (1a287510d5) — the H^1 computation, the conjugation step and the central-twist step all PASS, so under (V) counter mixing is central lamp mixing up to conjugation; the corollary that for counter-pair domains every lamp's T-component vanishes also passes (for every domain lamp, not only A_0), but "both routes die / does not separate a torsion core" is not proved, because the top core is not normal in G(M) and a G(M)-core involves F on configurations
distinct_from:
  kms-counter-cocycles-reduce-to-central-lamp-mixing: that is the lane node reviewed here.
  kms-lamp-mixing-br-relation-review: that reviews the Step 1 criterion this node's corollary applies.
---

**ESTABLISHED (referee bh-ref-g, 2026-09-19; review of `kms-counter-cocycles-reduce-to-central-lamp-mixing`,
commit 1a287510d5).** The KMS relations G2, G5a–c and G6 are taken as transcribed in
`kms-configuration-lift-needs-non-contracting-counters`. I did not re-verify them against KMS arXiv:1204.6506.

## Verdict

- Lemma 1, Lemma 2 and the Theorem's (i)–(iii): **PASS**.
- The corollary's "`τ = 0`" (every lamp's `T_0`-component vanishes for counter-pair domains): **PASS**, with a
  clarity repair.
- The corollary's "does not separate a torsion core" and "both routes die": **not proved.** The statement needs
  restating.

## Lemma 1: PASS

- **(a)** As refereed at 28f69471d1.
- **(b)** For `A_0 ∉ u`, write `x_u = x_{q_j}∏_{k∈w}(A_k − 1)`. Then:
  - `ã_i` commutes with the `A_k`, `k ≥ 1` (G2), so it can be moved past the product;
  - G6 turns `x_{q_j}ã_i` into `x_{q_j}a_i`;
  - G5b applies to `q_j`, which lacks `A_i`;
  - G6 applies again.

  No commutation of `a_i` with `A_i` is needed. `A_0` acts trivially modulo `T_0`, so every `B_0`-conjugate of
  a lamp, and hence all of `R_K`, acts trivially on `T/T_0`. So `U_0` acts on `T/T_0` through a quotient of
  `F_p[U_0]/(ã_i − 1 − ã_i') = R'_K`. Correct.

## Lemma 2: PASS

- `U_H` acts on `M = T/T_0` through the commutative image of `R'_K`, so `R'_K` acts on `H^n(U_H, M)` by
  functoriality.
- For `g ∈ U_H`, the pair (conjugation by `g`, `m ↦ m·ψ(g)`) induces the identity on `H^n`. Conjugation is
  trivial on the abelian `U_H`, so `ψ(g) − 1` acts as 0, and `I·H^n = 0`.
- **Nullstellensatz.** The maximal ideals of the finitely generated `F_p`-algebra `R'_K` are Galois orbits of
  points of `(F̄_p ∖ {0,1})^K`. So `V_T(ψ) = ∅` gives `I = R'_K` and `H^n = 0`. Correct.
- **The one-coordinate table.** Each case checks:
  - `v^m − 1 = (v^{m'} − 1)^{p^f}` has the single root `v = 1` exactly when `m' = ±1`;
  - `w = v/(v−1)` maps `F̄_p ∖ {0,1}` onto itself and sends `v = ∞` to `w = 1`;
  - for `m = 0`, `v = 2` is a solution when `p` is odd;
  - when `m`, `n`, `m + n` are all nonzero, `τ` takes only the values 0 and ∞ at `{0,1,∞}`, so `τ = 1` has its
    solutions off `{0,1}`.
- **Kochloukova–Sidki shape.** The node writes `ψ(ã_2) = ã_1`. That holds for `K = 2`. For general `K`, the shape
  `ã_1^p ↦ ã_2 ↦ ⋯ ↦ ã_K ↦ ã_1` gives `ψ(ã_K) = ã_1`, and also `ψ(ã_1^p) = ã_2`. Both are good, so (V) holds.
  Fix the wording.

## Theorem (i)–(iii): PASS

- **(i)** The long exact sequence, with `H^0` and `H^1` of `T/T_0` vanishing, gives
  `H^1(U_H,T_0) ≅ H^1(U_H,T)`. `ψ(U_H)` fixes `T_0` by Lemma 1(a), so `H^1(U_H,T_0) = Hom(U_H,T_0)`. Correct.
- **(ii)** Conjugating by `s` changes the cocycle by `δs`. `F''(A_0) = f̄(A_0)·s(f̄(A_0) − 1)` up to sign, and
  `s(f̄(A_0) − 1) ∈ T_0` because `R_K` acts trivially on `T/T_0`. `T_0` is central in `T ⋊ B_0`, since `T` is
  abelian and `B_0` fixes `T_0`. Conjugation preserves the core. Correct.
- **(iii)** `χ = t'∘pr_{U_H}` is a homomorphism into the centre, so `F_B = χ^{-1}F''` is a homomorphism. `χ`
  vanishes on `H ∩ (T ⋊ R_K)`, so invariance of subgroups there is the same for `F''` and `F_B`. Correct.

## The corollary

**What is proved (PASS).** After conjugation, each domain lamp `λ ∈ M = H ∩ R_K` has `F''(λ) = τ_λ·f̄(λ)`, with
`τ_λ = s(f̄(λ) − 1) ∈ T_0` central.
- The Step 1 criterion applies to every `λ`, not only to `A_0`. Because `R_K` is a domain, the annihilator of a
  nonzero `λ` in `F_p[U_H]` is the kernel of `F_p[U_H] → R_K`, the same ideal for every `λ`.
- A counter pair `(u, 1 − u)` gives the annihilator `u + (1 − u) − 1`, of augmentation 1. So `τ_λ = 0` for all
  `λ ∈ M`.
- The node states this only for `A_0`. Add the one line that extends it.

**What is not proved.** It does not follow that such a lift "does not separate a torsion core".
- The top core `𝔟 ⊆ R_K` is an ideal, normal in `B_0`, but it is **not normal in `G(M)`**. Lamps act nontrivially
  on `T`: for example `x_u(A_0 − 1) = x_{uA_0} ≠ 0`. So `b^x = b·x(b − 1)` with `x(b − 1) ∈ T_0 ∖ 0`.
- A core of the self-similar action of `G(M)` is a normal subgroup of `G(M)`, contained in `H` and
  `F`-invariant. Any such subgroup containing a nonzero `b ∈ 𝔟` also contains `T(b − 1)`.
- `F` on `T(b − 1) ∩ H` is governed by `F` on configurations, i.e. by `F|_{T∩H}`, which neither route (A) nor
  route (B) constrains.
- `F([h, b]) = [F(h), f̄(b)]` handles commutators with `h ∈ H`, but `T(b − 1)` need not be generated by those.

So the corollary shows that **counter or lamp mixing carries no `T`-data on the lamps** for counter-pair
domains. Whether the lift is faithful still depends on `F|_{T∩H}`. The same caveat applies to the framework of
Part D in `kms-lift-must-mix-top-core-into-configurations`, which is refereed only as an attempt record.

## Repairs

1. Restate the corollary: "for counter-pair domains, after conjugation by `T`, every domain lamp's image has zero
   `T`-component (`τ_λ = 0` for all `λ ∈ M`)." Drop "does not separate a torsion core" and "both routes die", or
   make them conditional on a lemma that a lift with top-preserving lamp images has a nontrivial `G(M)`-core.
2. Add the one-line extension from `A_0` to every `λ ∈ M`, via the `λ`-independent annihilator.
3. Correct the Kochloukova–Sidki sentence for general `K` (`ψ(ã_K) = ã_1`).
4. Add to "What is left for KD2_p": **mixing through configuration images `F|_{T∩H}`**. Both routes leave it open,
   and it is exactly what the core question above depends on.

## Priority

This is internal to KD2_p. I found no external issue.
