---
rg: 2
id: kt-amenable-compressor-clifford-ce-proof
kind: route
title: Separate base stabilizers, climb the Ore telescope, then average over a Folner set
target: kt-amenable-compressor-clifford-crossed-products-are-ce
requires:
  - separable-stabilizer-clifford-crossed-products-are-ce
artifacts:
  - research/artifacts/kt-amenable-compressor-clifford-ce-2026-09-16.md
---

Full proofs are in Sections 2--4 of the artifact.

**Step 1: the base (artifact Lemma B).**  `Gamma` is residually finite, and
every stabilizer `Gamma intersect g Gamma g^(-1)` is separable in `Gamma`.

- Write `g = eL`.  By Suslin's theorem, `SL_r = EL_r` over the polynomial
  ring `k[L N^d]`.  So `gamma` fixes `g Gamma` if and only if every entry of
  `e^(-1) gamma e` has no coefficient outside `L N^d`.
- A coefficient of `e^(-1) A e` depends only on finitely many coefficients
  of `A`, because `e` and `e^(-1)` have finite Laurent supports.
- Suppose `gamma_0` is outside the stabilizer `Stab`.  It has a witnessing
  coefficient.  If `gamma_0 = s n` with `s in Stab` and `n` in the
  congruence kernel mod the coordinate-truncation ideal `I_M`, then
  `gamma_0 - s` has entries in `I_M`.  For `M` large, `gamma_0` and `s`
  therefore share that coefficient, which is a contradiction.

By `separable-stabilizer-clifford-crossed-products-are-ce`, `M_Gamma` is
Connes embeddable.

**Step 2: the telescope (artifact Lemma 4.1 and Lemma C).**

- For `s in L_+`, `s^(-1) Gamma s >= Gamma`.  The left Ore condition makes
  `(s^(-1) Gamma s)_{s in S}` directed: a common left multiple `t = as = bs'`
  dominates both levels.
- Each `M_{s^(-1) Gamma s} = Ad u_{s^(-1)} (M_Gamma)` is Connes embeddable.
- A directed union of Connes embeddable `M_{H_i}` is Connes embeddable, since
  finite windows lie in one level.  So `M_{N_S}` is Connes embeddable for
  `N_S = union_s s^(-1) Gamma s`.
- The Ore condition also gives `s N_S s^(-1) = N_S`: write
  `s s'^(-1) = b^(-1) a`.  So `<Gamma,S> = N_S rtimes <S>`, with
  `N_S = <Gamma,S> intersect E`.

**Step 3: amenable extension (artifact Lemma D).**  Let `N` be a Connes
embeddable subalgebra normalized by a unitary representation of an amenable
`P`, with `tau(x u_p) = 0` for `x in N` and `p != e`.  Then
`(N union u_P)''` is Connes embeddable.

- Model: take a Folner set `F` with `|kF triangle F| <= delta|F|` for all
  words `k` of length at most `n`.  In `M_F(C) tensor N`, send
  `b |-> D(b) = sum_f e_{ff} tensor alpha_{f^(-1)}(b)`, and send `u_p` to a
  permutation completing `f |-> pf` on `F intersect p^(-1) F`.
- Fix a starting point `f`.  Suppose that at every letter of the word the
  model permutation acts on the trajectory of `f` as genuine left
  multiplication.  Then `f` contributes exactly the crossed-product moment.
- If a step fails at the last failing letter `i`, then `k f notin F` for the
  suffix product `k = q_i ... q_m`, which has at most `n` letters.  So at
  most `n delta|F|/2` starting points fail, and every moment of length at
  most `n` is matched within `n delta`.

Apply this with `N = M_{N_S}` and `P = <S>`.  The vanishing condition holds
because `N_S P` is a semidirect product with `E intersect SL_d(Z) = 1`.

**Step 4: instances (artifact Sections 4.3--4.5).**

- A commutative `S` is left Ore.
- Heisenberg `S = <I+E_12, I+E_23>_+`: positive words of length `n` in two
  elements take at most `(nC_0+1)^4 < 2^n` values.  Cancelling the common
  suffix of two equal words yields a common left multiple.
- Actor subgroups `K` with `K intersect E = 1` act freely, because
  `g Gamma g^(-1) <= E`, and are residually finite.  So they are covered by
  the separable-stabilizer theorem directly.
- Lemma 5.2 of the artifact: `E` lies in no conjugate of any `<Gamma,S>`.
  If `E <= N_S`, some `t^(-1) N^d` would contain both `(1,...,1)` and its
  negative, hence `t(1,...,1) = 0`.
