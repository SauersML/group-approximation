# Boone–Higman swarm review

Lane `bh-reviewer`, 2026-09-12. One section per reviewed claim, oldest first.

## 0. Bookkeeping from reviewer-2's review (be6dc41fc)

All four gaps listed in `review-boone-higman-leavitt-tensor-hosts-2026-09-12` were
already fixed on main in 301921778 (12:19). No further edit was needed.

1. `leavitt-tensor-hosts-khanh-transfer-proof` now requires the general criteria
   claim `khanh-acyclicity-and-steinberg-criteria`, not the `L`-specific
   conclusions.
2. `prime-field-leavitt-tensor-hosts-proof` requires that criteria claim and
   `leavitt-center-is-coefficient-field`, not the characteristic-two host claim.
3. `ara-cortinas-leavitt-tensor-k-theory-vanishes` is now titled "Over every
   field ...".
4. The odd-`p` simplicity step now says it is a paper argument that reads the
   Lean proof and "is not a Lean theorem".

`cairn check` on MSI at 039c5af15 (real-history clone): EXIT=0, 0 ERROR lines.
`cairn why`:
- OPEN: `boone-higman-conjecture`, `char-two-linear-groups-satisfy-boone-higman`,
  `leavitt-tensor-powers-have-trivial-k-theory`.
- ESTABLISHED: `positive-char-surface-linear-groups-satisfy-boone-higman`
  (reviewed PASS in be6dc41fc), `leavitt-tensor-hosts-acyclic-steinberg-and-fp`,
  `prime-field-leavitt-tensor-hosts-fp-and-simple-mod-centre`,
  `khanh-acyclicity-and-steinberg-criteria`.

No false establishment.

## 1. `khanh-acyclicity-and-steinberg-criteria` (301921778) — PASS, at the level of statements

Every quoted statement was checked against the extracted text of Khanh
arXiv:2609.08428v1 on MSI (`/projects/standard/hsiehph/sauer354/lit-groups/khanh-clean.txt`):

| Item | Line | Text found |
|---|---|---|
| Theorem 2.2 | 106 | "Suppose that A² ≅ A as right A-modules. Assume also that: …" |
| Theorem 5.1 | 640 | "Let B be a nonzero unital ring of characteristic two …" |
| Lemma 5.2 | 774 | "For any unital ring B and m ≥ 3, j_m(N_m(B)) is central in St_(m+1)(B)." |
| GE remark | 804 | "requires no regularity assumption" |
| Voronetsky step | 866 | "requires no hypothesis on stable rank, quasi-finiteness, or centrality of the kernel" |
| Krstić–McCool | 886 | "[10, Theorem 3] prove that St_n(B) is finitely presented for every finitely presented …" |

**Hidden hypotheses.** Items 1 and 2 are stated for `F_2`-algebras and for rings
of characteristic two. The odd-`p` consumer `prime-field-leavitt-tensor-hosts-proof`
re-argues the weight count and the signed transporters itself, and does not
import them. So the scope of the import is not overstated.

**Trust surface.** The primary sources Menal–Moncasi, Voronetsky and Krstić–McCool
are quoted through Khanh and were not re-read. The node's Scope paragraph says
so.

## 2. `hyperbolic-groups-satisfy-boone-higman` (5ebbc4ea8) — PASS

The abstract of arXiv:2309.06224 (fetched 2026-09-12) says: "we show that hyperbolic
groups satisfy this conjecture, that is, each hyperbolic group embeds in some
finitely presented simple group". The proof goes through full contracting
rational similarity groups, and the abstract adds that "all contracting
self-similar groups satisfy the Boone-Higman conjecture". This matches the node.

Not rechecked: the v3 date and the Duke Math. J. citation.

## 3. `baumslag-solitar-and-free-by-cyclic-satisfy-boone-higman` (75257fdab) — PASS

- The node's verbatim quote matches the arXiv:2408.05673 abstract.
- Survey arXiv:2306.16356v3, Remark 5.4 (text extracted on MSI), says that
  items (4) and (8) "are fully handled", and that [40] also handles Euclidean
  triangle Artin groups.

This matches the node. The `distinct_from` keys exist as claims.

## 4. `aut-free-groups-satisfy-permutational-boone-higman` (67494e7f9) — PASS

Checked against the abstract and PDF text of arXiv:2503.21882, extracted on MSI:
- **Theorem A**, permutational form: "the simple group in question can be taken
  to be a twisted Brin-Thompson group".
- **Corollary B** (PDF lines 55–66): the (extended) mapping class groups of
  orientable finite-type surfaces; the braid groups; Artin groups of types
  B_n = C_n, D_n, I_2(m) and Ã_n; loop braid, extended loop braid and ribbon braid
  groups. Survey Remark 5.4 confirms the surface condition "non-empty boundary
  or at least one puncture".
- **Corollary D:** universality among finitely presented simple highly transitive
  groups, more generally among finitely presented simple MIF groups.
- **Corollary F:** the permutational conjecture is closed under free products.
- **Still open**, per survey Remark 5.4: mapping class groups of closed surfaces of
  genus at least 3, Out(F_n) for n ≥ 3, and Artin groups of exceptional spherical
  type and of Euclidean type other than Ã and the triangle cases. The node's
  Scope matches.

The `distinct_from` keys `relative-automorphism-action-is-highly-transitive`,
`twisted-brin-thompson-finite-presentation-criterion` and
`fp-self-similar-groups-embed-in-fp-simple-groups` exist as claims.

## 5. `char-p-linear-groups-embed-in-projective-leavitt-power-e-groups` (925b9eabd) — FAIL, corrected forward in 4ba6fa13b

**Error.** Theorem C of `boone-higman-char-p-all-degrees-2026-09-12`, and step 3
of `char-p-linear-embedding-projective-leavitt-power-proof`, use
`X |-> diag(X, X^-1, 1, ..., 1)` as an injective homomorphism `H -> E_m(R_d)`.
It is not one. `w(X) w(Y) = diag(XY, X^-1 Y^-1)`, while
`w(XY) = diag(XY, Y^-1 X^-1)`. So `w` is multiplicative only on commuting pairs,
and it fails for every nonabelian `H`, for example `SL_3(F_p[t])`.

**What stands:**
- Lemma A: `H <= GL_N(R_d)`, through Noether normalization and free extensions
  over `C[g^±]`, with `M_k(R_d) ≅ R_d`.
- Lemma B: the six-factor identity is correct, and each single `diag(X, X^-1)`
  lies in `E_(2N)`.
- Lemma C: `Z(R_d) = F_p`.
- Simplicity of `E_m(R_d) / Z`, taken from part 4 of the host claim.

**Correction.** The established obstruction
`whitehead-diagonal-map-is-not-multiplicative`, with its `-proof` route,
invalidates the route. The claim now reads OPEN, with `## Attempts` recording
two repair directions:
- `K_1(R_d) = 0`;
- `diag(X, X^-T)` over the commutative coordinate ring, which needs
  `[X^T] = [X]` in `K_1(S)`.

The artifact's statement that `K_1` plays no role is therefore not established.

**Check.** MSI `cairn check` at 80aa1b814, which contains 4ba6fa13b: EXIT=0, 0 ERROR.
- The claim reads OPEN.
- The route reads INVALIDATED.
- The obstruction reads ESTABLISHED.
- `positive-char-linear-groups-satisfy-boone-higman` and
  `boone-higman-conjecture` still read OPEN.

**Repair by lane `bh-char-p-all-degrees` (83fee9c7b) — PASS.** The new route
`char-p-linear-embedding-corner-swindle-proof` replaces the Whitehead map with a
homomorphism and one more tensor factor:
- `H <= GL_N(R_d ⊗ 1) <= GL_N(R_(d+1))`;
- each generator has trivial class in `K_1(R_(d+1))` by
  `leavitt-tensor-kills-k1-of-coefficient-matrices` (§11), so some
  stabilization of it lies in `E_M`;
- the stabilization homomorphism `X |-> diag(X, I_(M-N))` then puts `H` inside
  `E_M(R_(d+1))`.

The centre calculation and the simplicity input carry over with `B = R_d`
central simple. So the claim is established again, now over `R_(d+1)`.
`positive-char-linear-groups-satisfy-boone-higman` still needs the open
finite-presentation premise.

## 6. `rational-linear-groups-satisfy-boone-higman` (103b2b683) — PASS

From the text of arXiv:2405.09722, extracted on MSI:
- Theorem 1.2 reads "Every finitely generated subgroup of GL_n(Q) satisfies the
  Boone–Higman conjecture";
- Theorem 1.1 is the finitely presented self-similar embedding;
- the proof goes through Example 4.7 with `J = pZ[1/m]`.

Not rechecked: the journal reference.

## 7. `algebraic-linear-groups-satisfy-boone-higman` (103b2b683) — PASS

- The entries of the generators and their inverses generate a number field `F`.
- The regular representation `F -> M_d(Q)` is an injective unital ring
  homomorphism.
- Applying it entrywise gives `GL_n(F) -> GL_(nd)(Q)`.
- A finitely generated subgroup of `GL_(nd)(Q)` then satisfies Boone–Higman by §6.

The node claims no novelty.

## 8. `char-zero-leavitt-unit-groups-have-congruence-kernels` (103b2b683) — PASS

- The infinite-word module `A^(X)` satisfies the Leavitt relations: every word
  starts with 0 or 1.
- Residue fields of finitely generated `Z`-algebras at maximal ideals are finite.
- `w = s_0 t_1 + s_1 t_0` is an involution that survives reduction.
- `u = 1 + p s_0 t_1` is a unit in the kernel. It is nontrivial because
  `(u-1) e_(1x) = p e_(0x) != 0` in the free `A`-module.

## 9. `affine-self-similar-coordinate-rings-are-one-dimensional` (103b2b683) — PASS

**Part (a).**
- (SC) applied `e` times to `p` gives an element of valuation 0 and one of
  valuation 1.
- So `P R_P = pi R_P`, and `R_P` is a DVR by Krull's principal ideal theorem.

**Part (b).**
- A minimal prime `Q` over `xR` has height 1.
- `R/Q` is a finite field of characteristic `p`.
- The dimension formula over the universally catenary `Z` (Matsumura 15.6)
  gives `1 = 1 + trdeg - 0`, so `trdeg = 0`.

**Reading of Zaremsky's Example 4.7.** Checked verbatim against the PDF text on
MSI: "a principal left ideal J = Rx of finite index … x is not a zero-divisor …
∩_k R x^k = {0} … R^⊕n ⋊ GL_n(R) is self-similar". The node's commutative,
finitely generated reading matches.

**Section argument.** The digit section of the translation by
`b in R^n ∩ pi O^n` is the translation by `b/pi`.

## 10. `spherical-artin-boone-higman-reduces-to-e6-e7-e8` (d533ae6e6) — PASS

This is a conditional reduction.
- **Crisp.** The text of Paris arXiv:0711.2372, p. 45, extracted on MSI, reads:
  "any spherical type Artin group embeds in a direct product of Artin groups of
  type A_n (n ≥ 1), D_n (n ≥ 4), and E_k (k = 6,7,8) (see [57])", with [57] =
  Crisp, *Injective maps between Artin groups*.
- **Product closure.** The BFHZ arXiv:2503.21882 text reads "PBH is stable under
  commensurability and direct products [Zarb]", citing [Zarb] Propositions 5.5
  and 5.6.
- **Types A and D.** Corollary B covers braid groups and type D_n. Its proofs go
  through PBH by embedding or commensurability.
- **Trust surfaces.** The primary sources, Crisp 1999 and [Zarb], were not
  re-read. No root is established.

## 11. `leavitt-tensor-kills-k1-of-coefficient-matrices` (83fee9c7b) — PASS

The route `leavitt-tensor-k1-coefficient-swindle-proof` checks line by line.
- **The corner endomorphism** `φ(r) = s_0 r t_0 + s_1 r t_1` is unital and
  multiplicative, because `t_0 s_1 = t_1 s_0 = 0`. It fixes `B ⊗ 1`.
- **The block matrices.** `S = (s_0 I, s_1 I)` and `T = (t_0 I; t_1 I)` satisfy
  `ST = I_N` and `TS = I_(2N)`. Then `U = [[S,0],[0,T]]` and `V = [[T,0],[0,S]]`
  satisfy `UV = VU = I_(3N)`, and `U diag(X, X, I_N) V = diag(φ(X), I_(2N))`.
- **Conclusion.** `[X] = [φ(X)] = 2[X]`, so `[X] = 0`.

This is the classical swindle, and the node claims no novelty.

## 12. `boone-higman-implies-relative-permutational-bh` (29dfc60b5) — PASS

Checked against the text of arXiv:2603.24687v2, extracted on MSI:
- **Theorem C (Theorem 5.1)**, verbatim: "If a group satisfies the Boone–Higman
  conjecture then it satisfies the relative permutational Boone–Higman
  conjecture."
- **Conjecture 1.8 (relPBH)** matches: "a group G with a type [A2] action on a
  set S such that Γ sharply embeds in (G, ker(G ↷ S))".
- **Definition 1.6:** its opening matches.
- **Question 5.9:** the remark that a "yes" to its first part gives
  (relPBH) ⟹ (PBH) matches.

The node's definitions were first read through a summarizing fetch. Theorem C
and Conjecture 1.8 are now verified from the PDF text. The definition of type
[A_2] was not re-extracted.

**Open nodes from the same commit** (not established, so no verdict):
- **The permutational statement.** The BFHZ PDF text confirms it (line 132:
  "embeds in a group admitting an action of type (A)").
- **The MIF question.** The BFHZ text states it as Question 3.4 (line 721), which
  the node calls "their question" without the number.
- **Routes.** `boone-higman-via-permutational-boone-higman` and
  `permutational-boone-higman-via-mif-envelopes` form the intended conditional
  cycle, and neither fires.

## Summary

12 PASS, including the repair; 1 FAIL, corrected forward in 4ba6fa13b and
repaired in 83fee9c7b; 0 GAP. The Boone–Higman root stays OPEN.
