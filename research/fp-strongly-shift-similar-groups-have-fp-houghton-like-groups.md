---
rg: 2
id: fp-strongly-shift-similar-groups-have-fp-houghton-like-groups
kind: claim
title: If a strongly shift-similar group G is finitely presented then every Houghton-like group H_n(G) is finitely presented, for every n >= 1 (the finitely presented case of Mallery-Zaremsky Question 5.13, first and third sentences)
requires:
  - houghton-like-groups-are-strongly-shift-similar
  - houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group
  - strongly-shift-similar-point-stabilizers-are-copies-of-the-group
  - finitary-mixing-of-fp-highly-transitive-groups-is-fp
distinct_from:
  houghton-like-envelopes-lift-finite-presentation-from-germs: that (refuted by free-shift-houghton-like-envelopes-are-not-fp) assumed only a finitely presented germ group; this assumes G itself finitely presented, and proves H_n(G) finitely presented for all n, including n = 1, 2.
  free-shift-houghton-like-envelopes-are-not-fp: that kills H_n(E_nu(P)) for free-shift nu, where E_nu(P) is not finitely presented; this is the positive statement when G is finitely presented.
  fp-strongly-shift-similar-admits-type-a-action: that gives a type (A) action for finitely presented strongly shift-similar G; this gives finite presentation of the Houghton-like groups built from such G.
---

**ESTABLISHED** (lane proof, elementary modulo the cited Mallery--Zaremsky facts and P. Hall's extension lemma;
not independently reviewed; no priority claimed). No literature search for later answers to Question 5.13 was
made. (Correction: an earlier version of this node claimed a bounded arXiv check; none was run.)

**Generalized** by `strongly-shift-similar-type-f-m-passes-to-houghton-like-groups`, which proves the same with
`F_m` in place of finite presentation for every `m`.

**Statement.** Let `G <= Sym(N)` be strongly shift-similar and finitely presented. Then `H_n(G)` is finitely
presented for every `n >= 1`.

This answers the first sentence of Mallery--Zaremsky Question 5.13 (arXiv:2202.00822, "If a shift-similar group
`G` is finitely presented and `n >= 3`, then is `H_n(G)` finitely presented?") positively for strongly
shift-similar `G`. It also answers its third sentence ("If `G` is strongly shift-similar, then do these results
hold for all `n`?") positively for finite presentation. The `F_m` part of the question is not addressed.

**Proof.** Write `X = [n] x N`, `H = H_n(G)`, and `G_k` for the copy of `G` acting on ray `k`
(Observation 5.1).
1. **The subgroup `B = G^n · FSym(X)` is finitely presented.** Each `G_k` is finitely presented, contains
   `FSym(ray k)`, and has finitely generated point stabilizers
   (`strongly-shift-similar-point-stabilizers-are-copies-of-the-group`, items 1–2). Apply
   `finitary-mixing-of-fp-highly-transitive-groups-is-fp`.
2. **`B` is normal in `H`, with `H/B ≅ Z^(n-1)`.** By `houghton-like-envelopes-have-fp-germs-iff-fp-near-shift-group`
   item 1, `H/FSym(X) ≅ Q_n(Ĝ)`, the index-zero tuples in `Ĝ^n` with `Ĝ = Germs(G) ⋊ <s̄>`.
   - The image of `B` is `Germs(G)^n`, which is the kernel of `(eta_1, ..., eta_n) : Q_n(Ĝ) -> Z^n` onto
     `{c : Σ c_k = 0} ≅ Z^(n-1)`.
   - Conversely, an element of `H` whose ray germs all have index 0 has germ `s̄^(a_k) ḡ_k s̄^(-a_k)` on ray `k`.
     That lies in `Germs(G)` (Step 1 of that node's proof), so the element is in `G^n · FSym(X)`.
   - So `B` is the preimage of a normal subgroup, and `H/B ≅ Z^(n-1)`.
3. **Extension.** `B` and `Z^(n-1)` are finitely presented, so `H` is (P. Hall: an extension of a finitely
   presented group by a finitely presented group is finitely presented). ∎

**Calibrations.**
- `n = 1`: `H_1(G) = G`, and the statement is the hypothesis.
- `G = FSym(N)` is not finitely generated, so it is excluded. That is consistent with `H_2 = H_2(FSym)` not being
  finitely presented.
- `G = 1` is shift-similar, finitely presented and not strongly shift-similar, and `H_2(1) = H_2` is not finitely
  presented. So "strongly" is used. It enters through `FSym(N) <= G` and the stabilizer isomorphism of
  `strongly-shift-similar-point-stabilizers-are-copies-of-the-group`, which is exactly where Question 5.13 separates
  the two cases. (Correction: an earlier version called containing `FSym(N)` equivalent to strong shift-similarity.
  Only the forward implication is proved.)
- `G = H_k` with `k >= 3`: `H_n(H_k) ≅ H_(nk)` (Proposition 5.5), finitely presented, as predicted.
- `G = E_nu(P)` with a free-shift `nu`: `G` is not finitely presented, and `free-shift-houghton-like-envelopes-are-not-fp`
  shows every `H_n(G)` fails too. No conflict.

**Corollary (zigzag envelope).** For the zigzag enumeration `nu` of `Z`,
`E_nu(Z)` is finitely presented and strongly shift-similar (`zigzag-cyclic-shift-envelope-is-finitely-presented`).
So `H_n(E_nu(Z))` is finitely presented for every `n >= 1`. This settles the target the coordinator and `bh-map` named
for the Houghton-like route. It gives nothing new for Boone--Higman, since `Z` is already covered.

**What this means for the Houghton-like route to Boone--Higman.**
- **Sufficiency is now free.** Whenever `E_nu(P)` itself is finitely presented, every `H_n(E_nu(P))` is too. But
  then `P` already satisfies Boone--Higman through `fp-strongly-shift-similar-admits-type-a-action`, so `H_n` adds
  nothing in that case.
- **The converse fails, so the route keeps some room.** `H_2 = H_2(FSym)` is strongly shift-similar (Proposition
  5.5) and not finitely presented, while `H_2(H_2) ≅ H_4` is finitely presented. So `H_n(G)` can be finitely
  presented when `G` is not.
- **What the room must look like.** A new Boone--Higman witness along this route is therefore an enumeration `nu`
  with `E_nu(P)` NOT finitely presented but `H_n(E_nu(P))` finitely presented for some `n`. By
  `free-shift-houghton-like-envelopes-are-not-fp` item 3, `nu` must carry rigid near relations, and free-shift
  enumerations are excluded. That is the sharpened open target this node leaves behind.
