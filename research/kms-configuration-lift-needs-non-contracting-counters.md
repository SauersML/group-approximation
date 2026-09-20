---
rg: 2
id: kms-configuration-lift-needs-non-contracting-counters
kind: claim
title: Lifting a self-similar structure from the KMS top to G(M) = T semidirect Q - the full top is fine for p odd, every faithful transitive self-similar action of B_K (K >= 2) must let some counter move the root, the relations G6 force one coherent counter renormalization, and a renormalization that contracts the counters (like Kochloukova–Sidki's Frobenius shift) would make configuration equality polynomial, so a hard lift needs non-contracting counters
distinct_from:
  kms-tops-embed-in-fp-self-similar-metabelian-groups: that settles the K-variable top factor B_0 for p odd; this records what happens when one tries to lift through the configuration module T.
  two-counter-kms-top-has-no-affine-self-similar-action: that kills affine realizations with every counter linear; Lemma 1 here removes the affine hypothesis, keeping only that the counters lie in the domain of the virtual endomorphism.
  two-counter-kms-groups-are-self-similar: that is the crux KD2_p; this is an attempt record under it, locating where the lift must go.
  finite-recursion-gives-no-computable-depth-bound: that says finite recursion allows any depth; this shows the natural counter renormalizations give logarithmic depth on configuration elements, which is too little.
---

**ESTABLISHED as an attempt record (lane bh-kd2p, 2026-09-19).**
- Part 0 and Lemma 1 are lane proofs.
- Part 2 is a remark; Part 3 is a sketch, and its hypotheses are stated.
- KD2_p stays **OPEN**. Not independently reviewed.

Source for `G(M)`: KMS arXiv:1204.6506v5 §4.1, read in the e-print on MSI (`/scratch.global/sauer354/gq-kms/x/main.tex`,
lines 970–1062).
- **Generators.** `x_u`, for `u = q_j w` with `w` a divisor of `A_0 ⋯ A_K`; `A_0, …, A_K`; and
  `a_i, a_i', ã_i, ã_i'`.
- **Relations.** G1–G4 give the top `Q = B_1 × ⋯ × B_K × B_0` (their Lemma lH). Here
  `B_i = ⟨a_i, a_i', A_i⟩` for `i ≥ 1`, and `B_0 = ⟨ã_i, ã_i', A_0⟩`.
- **G5a.** `[x_u, A_i] = x_{uA_i}`.
- **G5b.** `x_u^{a_i − 1} = x_u^{a_i'}` when `u` lacks `A_i`.
- **G5c.** `x_u` is fixed by `M_i` when `u` contains `A_i`.
- **G6.** On the `x_{q_j}`, `a_i` acts as `ã_i` and `a_i'` acts as `ã_i'`.
- **G8.** The machine relations use `f∗a = f^{-1} f^{a} f^{-a^{-1}} f^{(a')^{-1}}`, in module notation
  `f·D(a)`, where `D(a) = a − 1 − a^{-1} + (a − 1)^{-1}`. By their Theorem 4.3(b), configuration equality is the
  equality of the elements `x_{q A_0}·D(a_1)^{m_1} ⋯ D(a_K)^{m_K}`.

## Part 0. The full top is fine for `p` odd

- Each `B_i`, for `i ≥ 1`, is `R_1 ⋊ ⟨a_i, a_i'⟩`, with `R_1 = F_p[a^{±1}, (a^{-1} − 1)^{-1}]` of Krull dimension 1
  and trivial centralizer. So it is transitive self-similar by Kochloukova–Sidki Theorem C (arXiv:1710.04745). It
  is finitely presented, being Baumslag-type.
- `B_0 ≤ E_K`, an index-2 overgroup that is finitely presented and self-similar
  (`kms-tops-embed-in-fp-self-similar-metabelian-groups`).
- A direct product of self-similar groups is self-similar on the product alphabet. So
  `Q ≤ B_1 × ⋯ × B_K × E_K` is contained in a finitely presented self-similar group.
- For `p = 2`, the factors `B_i` are covered by Theorem C as well, and only `B_0` is open.

## Lemma 1. Some counter must move the root (`K ≥ 2`)

**Statement.** Let `K ≥ 2`, and let `f : H → B_K` be the virtual endomorphism of a faithful transitive
self-similar action of `B_K = R_K ⋊ U_K`. Then `U_K ⊄ H`.

**Proof.** Suppose `U_K ≤ H`, and put `J = H ∩ R_K`.
- `J` is `U_K`-invariant and of finite index, so it is an ideal of finite codimension, since `R_K` is spanned by
  `U_K`.
- The elements of finite order in `B_K` are exactly the elements of `R_K`. So `f(J) ⊆ R_K`, and
  `f(um) = ψ(u)f(m)` for `u ∈ U_K`, where `ψ(u)` is the `U`-part of `f(u)`.
- The kernel of the action is the `f`-core: the largest normal subgroup `N ≤ H` with `f(N) ≤ N`. Every
  `U_K`-invariant subgroup of `R_K` is normal. So faithfulness implies two things:
  - `ker f ∩ J` contains no nonzero ideal, since such an ideal would be killed by `f` and lie in the core;
  - `f(J) ≠ 0`.
- Now run Steps 2–5 of `two-counter-kms-top-has-no-affine-self-similar-action` with `f|_J` in place of `σ`. That
  node's Step 1 (digits) is replaced by the core argument above.
  - `ψ` extends to an injective ring endomorphism `ψ̃`.
  - The unit lemma applies, since `s_i, 1 − s_i ∈ U_K ≤ H`, so `ψ̃^*` has finite fibres.
  - Since `K ≥ 2`, `f|_J = g ψ̃|_J` with `g ∈ R_K`.
  - So there is a nonzero ideal `𝔟 ⊆ J` with `f(𝔟) ⊆ 𝔟`, which lies in the core. Contradiction. ∎

So the affine hypothesis in bh-free-25's node was not needed. What matters is only whether all counters lie in
the domain. Kochloukova–Sidki's domain meets the counters in index `p^2`, which is consistent with this.

## Part 2 (remark). G6 forces one coherent renormalization

- On `x_{q_j}`, the letters `a_i ∈ B_i` and `ã_i ∈ B_0` act identically.
- A lift `F` of a virtual endomorphism `f_Q` of `Q` to `T ⋊ Q` must be `f_Q`-semilinear on its domain in `T`. So
  `F(a_i)` and `F(ã_i)` must act identically on `F(x_{q_j})`.
- **The product structure of Part 0 does not lift.** There `f` fixes `a_i` inside `B_i`, but shifts
  `ã_1^p ↦ ã_2` inside `B_0`.
- **A lift needs one renormalization of the counters used coherently on `B_1, …, B_K` and on `B_0`.** In the
  Kochloukova–Sidki shape that is `a_1^p ↦ a_2 ↦ ⋯ ↦ a_K ↦ a_1`, the same on the `ã_i`, and a matching
  relabelling of the `x_{q_j}`.
- **Compatibility with the machine.** Frobenius gives `D(a)^p = D(a^p)` over `F_p`, so the shift sends the counter
  operator `D(a_1)^{pm}` to `D(a_2)^m`. Such a lift therefore requires `M` to be equivalent to its
  **renormalization** `M'`:
  - residues of counter 1 mod `p` move into the state;
  - the quotient `⌊n_1/p⌋` becomes the last counter, and the other counters rotate;
  - only finitely many such machines may appear, since the recursion is finite.

## Part 3 (sketch). Contracting renormalization is too easy for hard machines

**Hypotheses.** A lift as in Part 2 whose counter renormalization contracts: over one full rotation every counter
is divided by `p`, as in Kochloukova–Sidki.

**Sketch.**
- The level-one sections of `x_{qA_0}·∏ D(a_i)^{m_i}` come from its conjugates by the finitely many coset
  representatives, followed by `F`.
- Each is a bounded combination of the fixed coefficients `ψ̃(s_j)`, times configuration elements of the
  renormalized machine with counters `≈ m/p` in one coordinate. Coefficient degrees stay bounded, because
  `a_1^p ↦ a_2` lowers the `a_1`-degree and the rest only rotates.
- After `O(K log_p m)` levels all counters are below `p`, and the sections lie in a fixed finite set. Their
  triviality is finite data.
- So equality of configuration elements is decidable in time polynomial in `m`, since the tree has depth
  `O(log m)` and bounded branching. That contradicts the hardness of `M` in KMS Theorem 4.3(b) as soon as `M` is
  hard beyond polynomial time. (The group words for these elements have length exponential in `m`, which changes
  nothing: the hard machines can be chosen harder.)

**Conclusion.** A lift giving KD2_p cannot contract the counters. Some counter must be renormalized
isometrically, or expanded. Lemma 1 says some counter moves the root, and the `ψ`-core condition on `ℤ^{2K}`
(Nekrashevych–Sidki: the characteristic polynomial of `ψ ⊗ ℚ` has no monic integral factor) allows eigenvalues
of modulus `≥ 1`. So neither Lemma 1 nor Part 3 kills KD2_p.

**The sharpened crux.** A self-similar structure on `G(M)`, or on a finitely presented overgroup, in which some
counter moves the root while the machine's counters are not contracted. By Part 3 its depth on configuration
elements must be super-polynomial in `m`. Per bh-birget (2222dfd660, lane proof, unreviewed), finite presentation of the overgroup can be weakened: a finitely generated self-similar group whose relator kernel is a finitely generated lift ideal suffices for the Zaremsky endgame.

## Part 4. `p = 2` (spark, not checked)

- The substitution needs `c ∉ {0, 1}`, which fails in `F_2`. Over `F_4`, however, `c` a primitive cube root of
  unity gives `g = 1 − cx` with `g(1) ≠ 0`, and `q`-Frobenius with `q = 4` gives `g(x)^4 = g(x^4)`.
- `R_K(F_2) ⋊ U ≤ R_K(F_4) ⋊ U`. So an `F_4` version of Theorem D, using `x_1^4 ↦ x_2` (not checked), would
  cover `B_0` for `p = 2` too.

## Lesson

**Hardness and contraction are incompatible on the counters.** A self-similar KMS group must renormalize its
machine. If the renormalization shrinks the counters, the tree decides configuration equality in logarithmic
depth. A hard self-similar KMS group needs a counter that moves the root without shrinking.
