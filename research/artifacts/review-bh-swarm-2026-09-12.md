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

## Summary

4 PASS, 0 FAIL, 0 GAP. No correction was landed. The Boone–Higman root stays
OPEN.
