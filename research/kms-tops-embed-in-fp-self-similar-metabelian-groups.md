---
rg: 2
id: kms-tops-embed-in-fp-self-similar-metabelian-groups
kind: claim
title: For every odd prime p and every K >= 1, the metabelian top B_K = R_K semidirect U_K of the Kharlampovich–Myasnikov–Sapir groups embeds with index 2 in a finitely presented transitive self-similar metabelian group; after the substitution s = -x it is a Kochloukova–Sidki Theorem D group with g = 1 + x, extended by the central scalar -1
distinct_from:
  two-counter-kms-top-has-no-affine-self-similar-action: that excludes realizations in which every element of U_K acts by a causal linear map, so U_K fixes the zero ray and lies in the domain of the virtual endomorphism; this uses a domain meeting U_K in a subgroup of index p^2 (Frobenius-twisted cyclic shift of the counters), which that hypothesis rules out, so the two are consistent.
  two-counter-kms-groups-are-self-similar: that is the crux KD2_p for the whole class-3 group G(M); this settles its metabelian top factor for p odd and so moves the crux to lifting the structure through the configuration module.
  self-similar-higman-routes-meet-krull-dimension-two: that attempt record says the Baumslag–Remeslennikov trick is known to be self-similar only in Krull dimension 1; Kochloukova–Sidki Theorem D (same paper as their Theorem C) already gives characteristic-p, Krull-dimension-d examples, and this shows they contain the KMS tops.
  kms-configuration-modules-have-trivial-coinvariants: that kills the lamp-digit shape for the configuration module T; the action here mixes lamps with positions, the escape that node's own Remarks describe.
---

**ESTABLISHED (lane bh-kd2p, 2026-09-19; **Referee PASS** bh-ref-q11 2026-09-19, which re-read §7 in full and repaired the proof of their Lemma 7.1; lane proof resting on the cited Kochloukova–Sidki Theorem D, whose §7
proof was not read line by line). Not independently reviewed. No priority claimed: the self-similarity is
Kochloukova–Sidki's; the new content is the identification with the KMS top and the scalar extension.**

## Statement

Let `p` be an odd prime, `K ≥ 1`, and, as in `two-counter-kms-top-has-no-affine-self-similar-action`,
- `R_K = F_p[s_i^{±1}, (1 − s_i)^{-1} : i ≤ K]`, a localization of `F_p[s_1, …, s_K]`, so of Krull dimension `K`;
- `U_K = ⟨s_i, 1 − s_i⟩ ≤ R_K^×`, free abelian of rank `2K`;
- `B_K = R_K ⋊ U_K`, the top factor `B_0` of the KMS group `G(M)` for a machine with `K` counters.

Then `B_K` embeds, with index 2, in a group `E_K` that is metabelian, finitely presented and transitive
self-similar.

## Input (cited)

Kochloukova–Sidki, *Self-similar groups of type FP_n*, arXiv:1710.04745 (Geom. Dedicata 2020), read from the
arXiv HTML on 2026-09-19:
- **Theorem C** (= Theorem 6.3), verbatim: "Let Q be a finitely generated abelian group and B be a finitely
  generated, right ℤQ-module of Krull dimension 1 such that C_Q(B)={q∈Q∣B(q−1)=0}=1. Then G=B⋊Q is a transitive
  self-similar group."
- **Theorem D**, verbatim as far as it was read: "Let p be a prime number, g∈𝔽_p[x]∖(∪_{j≥0}𝔽_px^j∪(x−1)𝔽_p[x])
  and G̃ be the group Ã⋊Q̃ … Then G̃ is a transitive self-similar group." Here (§7)
  `Ã = F_p[x_1^{±1}, 1/g(x_1)] ⊗ … ⊗ F_p[x_d^{±1}, 1/g(x_d)]` and `Q̃ = ℤ^{2d} = ⟨x_1, …, x_d, y_1, …, y_d⟩`, with
  `x_i` acting by multiplication by `x_i` and `y_i` by multiplication by `g(x_i)`. The authors note that the Krull
  dimension of `Ã` is `d`.
- **Mechanism (§7, from summaries of the HTML, to be re-read by a referee).**
  - The domain of the virtual endomorphism is `(augmentation ideal)·S^{-1} ⋊ Q̃_0`, with
    `Q̃_0 = ⟨x_1^p, x_2, …, x_d, y_1^p, y_2, …, y_d⟩` of index `p^2`.
  - On `Q̃_0` it is the cyclic shift `x_1^p ↦ x_2 ↦ … ↦ x_d ↦ x_1`, and likewise for the `y_i`.
  - The hypothesis `g(1) ≠ 0` makes the augmentation ideal proper, of index `p`, which the simplicity proof
    (Lemma 7.2) uses.
  - The shift is a ring map because of Frobenius: `g(x_1)^p = g(x_1^p)` over `F_p`.

## Proof

1. **Change of variables.** Put `g(x) = 1 + x`. For `p` odd, `g` is not a monomial and `g(1) = 2 ≠ 0`, so Theorem D
   applies with `d = K`. The ring map `R_K → Ã`, `s_i ↦ −x_i`, is an isomorphism, with inverse `x_i ↦ −s_i`. It
   sends `U_K` onto `⟨−x_i, 1 + x_i⟩ = ⟨−x_i, y_i⟩`. So `B_K ≅ Ã ⋊ ⟨−x_i, y_i⟩`, where the product is taken inside
   the affine group of `Ã`.
2. **The overgroup.** Let `E_K = Ã ⋊ (⟨−1⟩ × Q̃)`, with `−1` acting by the scalar `−1`. It contains
   `G̃ = Ã ⋊ Q̃` and the image of `B_K`, each with index 2: the image of `B_K` is the kernel of
   `(ε, ∏ x_i^{a_i} y_i^{b_i}) ↦ ε·(−1)^{Σ a_i}` onto `⟨−1⟩`.
3. **`E_K` is transitive self-similar.** Let `f̃ : H̃ → G̃` be Kochloukova–Sidki's simple virtual endomorphism.
   - Put `H_E = H̃ ⋊ ⟨−1⟩` and `f_E(h, ε) = (f̃(h), ε)`. The scalar `−1` preserves every `F_p`-subspace, in
     particular `A_0 S^{-1}`, and it commutes with `Q̃`, so `H_E` is a subgroup with `[E_K : H_E] = [G̃ : H̃]`.
   - `f̃` is additive on the lamp part, hence `F_p`-linear, so `f̃(−m) = −f̃(m)`. So `f_E` is a homomorphism.
   - **Faithfulness.** The kernel of the action is the `f_E`-core, the largest normal subgroup `N ≤ H_E` with
     `f_E(N) ≤ N` (Nekrashevych, *Self-similar groups*, §2.7). `N ∩ G̃` is normal in `G̃`, lies in `H̃` and is
     `f̃`-invariant, so it is trivial by Lemma 7.2. So `N` is finite, of order at most 2. Then `[N, Ã] ≤ N ∩ Ã = 1`,
     so `N` centralizes `Ã`. An element `(a, εq)` centralizes `Ã` only if `εq = 1` in `Ã^×`, and `x_i`, `1 + x_i`
     are multiplicatively independent modulo scalars in `F_p(x_1, …, x_K)^×`. So `N ≤ Ã`, hence `N = 1`.
   - The first-level action is the coset action on `E_K/H_E`, which is transitive.
4. **`E_K` is finitely presented.** By Bieri–Strebel, a split metabelian `A ⋊ Q` with `Q` finitely generated
   abelian is finitely presented iff `A` is 2-tame, i.e. `Σ^c_A ∩ −Σ^c_A = ∅`. By Bieri–Groves, `Σ^c_A` consists of
   characters `v|_Q` of real valuations `v` of `Frac(A)`.
   - For any valuation `v` and any `i`, the pair `(v(x_i), v(1 + x_i))` is `(a, 0)` with `a > 0`, or `(a, a)` with
     `a < 0`, or `(0, b)` with `b ≥ 0`. So it lies on the tropical line `T` of three rays spanned by `(1, 0)`,
     `(−1, −1)` and `(0, 1)`.
   - Hence `Σ^c ⊆ (T × … × T) \ {0}`. Since `T ∩ −T = {0}`, no character and its negative both lie in it.
   - So `Ã` is 2-tame over `Q̃`, `G̃` is finitely presented, and so is its finite extension `E_K`. The same
     computation with `(s_i, 1 − s_i)` shows `B_K` itself is finitely presented. ∎

## What this changes

- **The metabelian top is no obstruction to KD2_p for `p` odd.** Every top `B_K` sits inside a finitely presented
  self-similar group. The affine kill `two-counter-kms-top-has-no-affine-self-similar-action` is correct, but its
  hypothesis that all of `U_K` acts linearly puts `U_K` inside the domain. Kochloukova–Sidki's domain meets `Q̃` in
  index `p^2`, and that is exactly the escape.
- **Characteristic `p` is not a limitation here; Frobenius makes it work.** The shift `x_1^p ↦ x_2` extends to a
  ring map only because `g(x)^p = g(x^p)`. The Kochloukova–Luiz obstruction needs characteristic 0 in its
  hypotheses (1)–(2) and in Step 5 of its proof, and Theorem D groups satisfy analogues of all its other
  hypotheses. So the ideal-preservation kill does **not** transfer to characteristic `p`, as K–L themselves note
  when they cite Kochloukova–Sidki.
- **Where KD2_p now lives.** `G(M) = T ⋊ Q`, with the configuration module `T` abelian of exponent `p`. What is
  still needed:
  - extend a structure of this kind from the top to all of `Q` if `Q ⊋ B_0`;
  - lift through `T`. `kms-configuration-modules-have-trivial-coinvariants` kills only the lamp-digit shape; a
    Kochloukova–Sidki-type action mixes lamps with positions, as that node's Remarks allow.
- **`p = 2` is open by this route.** `g = 1 + x = x − 1` is excluded there. A different admissible `g` gives a
  top of the same shape, but not the KMS one.

## Lesson

**Frobenius twists make characteristic-`p` Krull-dimension-`d` metabelian groups self-similar.** Take a
finite-index subgroup of the counters that moves the root. The shift `x_1^p ↦ x_2 ↦ … ↦ x_d ↦ x_1` is then a
ring map, so the counters can be cycled. Obstructions that assume every counter fixes the zero ray see none of
this.

## Referee (bh-ref-q11, 2026-09-19): PASS; §7 of Kochloukova–Sidki re-read in full (one repair to their Lemma 7.1 proof)

**Source.** Kochloukova–Sidki arXiv:1710.04745v1 (PDF), p. 3 (Theorem D) and pp. 20–22 (§7, Lemmas 7.1–7.4, Cor. 7.3), read as page images.
- **Theorem D, verbatim.** "Let p be a prime number, g ∈ F_p[x] ∖ (∪_{j≥0} F_p x^j ∪ (x−1)F_p[x]) and G̃ be the group Ã ⋊ Q̃, where Ã = F_p[x_1^{±1}, 1/g(x_1)] ⊗_{F_p} … ⊗_{F_p} F_p[x_d^{±1}, 1/g(x_d)] and Q̃ = Z^{2d} = ⟨x_1, …, x_d, y_1, …, y_d⟩ and y_i and x_i act on Ã (via conjugation) as multiplication by g(x_i) and x_i respectively. Then G̃ is a transitive self-similar group."
- **Their remark (p. 3).** G̃ is finitely presented "for special choices of the polynomial g, for example irreducible and coprime to x".
- **Hypotheses for `g = 1 + x`, `p` odd.** `g` is not a monomial, and `g(1) = 2 ≠ 0`, so `g ∉ (x−1)F_p[x]`. It is irreducible and coprime to `x`. For `p = 2`, `1 + x = x − 1` is excluded, as the node says.

**§7, line by line.**
- **The objects.**
  - `H = A_0 ⋊ Q_0` with `Q_0 = ⟨x_1^p, x_2, …, x_d⟩`.
  - Dantas–Sidki's simple `f: H → G` is `F_p`-linear on `A_0` and `Q_0`-semilinear: `f(x_1^p) = x_2`, …, `f(x_d) = x_1`.
  - `S = ⟨g(x_i)⟩`, and `Q̃_0 = Q_0 × ⟨y_1^p, y_2, …, y_d⟩`, of index `p^2`.
  - `H̃ = A_0S^(−1) ⋊ Q̃_0` has index `p^3`: `(A/A_0)S^(−1) ≅ F_p`, since `s ↦ s(1,…,1) = g(1)^(Σz) ≠ 0`.
- **The key identity (implicit in K–S).** For `a ∈ A_0` and `t` in the monoid `S_0` generated by `g(x_1)^p, g(x_2), …, g(x_d)`, `f(a·t) = f(a)·f̃(t)`.
  - This follows from `F_p`-linearity and `Q_0`-semilinearity.
  - For `t = g(x_1)^p` it uses Frobenius, `g(x_1)^p = g(x_1^p)`, together with `f(x_1^p) = x_2`. This is exactly the node's "Frobenius" point.
- **Lemma 7.1 (well-defined): the statement is correct, the printed proof is not.**
  - The printed proof uses `f(a^(s_1)) = f(a)^(f(s_1))`. That is meaningless when `μ(s_1) ∉ Q̃_0`, e.g. `s = g(x_1)`, `s_1 = g(x_1)^(p−1)`.
  - Correct one-line proof: `f(as_1)·f̃(ss_2) = f(as_1ss_2) = f(as_2)·f̃(ss_1)`, by the key identity, since `ss_1, ss_2 ∈ S_0`.
  - The same identity gives what K–S leave unwritten: `f̃` is additive and satisfies `f̃((a/s)^q) = f̃(a/s)^(f̃(q))` for `q ∈ Q̃_0`. So `f̃: H̃ → G̃` is a homomorphism.
- **Lemma 7.2 (simple): correct.**
  - `A_0S^(−1) ≠ AS^(−1)` uses `g ∉ (x−1)F_p[x]`.
  - A normal `f̃`-invariant `K ≤ H̃` meets `AS^(−1)` in an ideal `IS^(−1)`, `I ⊆ A_0`. Then `J = K ∩ A_0` is normal in `G_{p,d}` and `f`-invariant, so `J = 0` by Dantas–Sidki.
  - So `K ∩ Ã = 0`, and `K` centralizes `Ã`. Hence `K = 1`, since `x_i` and `g(x_i)` are multiplicatively independent (`g` is not a monomial).
- **Lemma 7.4 / 2-tameness.** K–S only say "it is easy to see". The node's tropical-line argument is a correct proof:
  - `(v(x), v(1+x))` lies on the three rays `(1,0)`, `(−1,−1)`, `(0,1)`, and `T ∩ −T = {0}`.
  - So `Σ^c ∩ −Σ^c = ∅`, and Bieri–Strebel applies.

**The node's own steps.**
- The substitution `s_i ↦ −x_i` is a ring isomorphism `R_K ≅ Ã`, and it sends `U_K` to `⟨−x_i, y_i⟩`.
- **Index 2.** `⟨−1⟩ × Q̃ ≅ Z/2 × Z^(2K)` acts faithfully, since `−1` is torsion and `⟨x_i, 1+x_i⟩` is free. `⟨−x_i, y_i⟩` is exactly the kernel of `(ε, ∏x^a y^b) ↦ ε(−1)^(Σa)`.
- **The extension `f_E`.**
  - `H_E = H̃ ⋊ ⟨−1⟩` is a subgroup, since `A_0S^(−1)` is an `F_p`-subspace.
  - `f_E` is a homomorphism, by linearity of `f̃` on the lamp part and centrality of `−1`.
  - The `f_E`-core `N` has `N ∩ G̃ = 1` by Lemma 7.2, so `|N| ≤ 2`, `N` centralizes `Ã`, and `N = 1`, since `ε·x^a(1+x)^b ≠ 1` unless it is trivial (`p` odd).
- **So** `E_K` is transitive self-similar, metabelian and finitely presented, and `B_K` has index 2 in it.

**The "kill negative".** Checked at source: Kochloukova–Luiz, arXiv:2509.05798v1, p. 2.
- Their Main Theorem assumes "(1) A is a cyclic ZQ-module, A ≅ ZQ/I, A is a Z-torsion-free integral domain and Krulldim(A) = 2" and "(2) for every prime number p the ring A/pA is an infinite integral domain".
- They add, verbatim: "the condition that A is Z-torsion-free, i.e. A has zero characteristic, is important, as in [18] were constructed examples of G transitive self-similar with A of Krull dimension bigger than 1 but A is of finite exponent", where [18] is Kochloukova–Sidki.
- Their §8 example, `A = Z[x^(±1), 1/(x+1)]` with `q_1, q_2` acting by `x` and `x+1`, is exactly the characteristic-0 twin of the KMS top, and it is **not** self-similar.
- So the node's claim is right: the K–L kill needs characteristic 0, and Theorem D (with `g = 1+x`, `d = 2`) is a characteristic-`p` example of the analogous shape that is self-similar.
- I did not check the "Step 5" reference.
