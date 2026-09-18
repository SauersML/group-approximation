# Adversarial re-check: Boone–Higman for finitely presented metabelian groups

Lane `bh-verify-metabelian`, 2026-09-18. The trigger is finding F1 of
`research/artifacts/gq-bh-bh-lit-survey.md` (d7b638fef). Main marks
`fp-metabelian-groups-satisfy-boone-higman` ESTABLISHED, but the literature still lists
BBMZ Problem 5.3(7) as open. So main either proves a new theorem or contains an error.
This report checks the whole chain end to end, re-reading primary sources wherever I
could reach them. I wrote none of the nodes checked.

## Verdict

**The chain holds modulo standard inputs.** I found no gap. Main does not contain an
error here: it contains a new theorem that is so far checked only inside this repository.

The theorem rests on one idea that is not in the literature I could reach: the
parameter-coordinate self-similar action of
`polynomial-parameter-affine-groups-are-self-similar` (char 0) and its char-p analogue.
Combined with Zaremsky's Theorem 1.1, it places every finitely generated linear group, in
any characteristic, inside a finitely presented self-similar group. The metabelian case
then follows from Wehrfritz's quasi-linearity and the product closure of the permutational
class.

The inputs I did not re-read at source, all standard or read by the earlier review:
- **(U1)** Commutative algebra: Noether normalization over `Z[1/m]` and `F_p`, miracle
  flatness, and Quillen–Suslin over a PID or a field.
- **(U2)** Weibel's K-book pages. These are III Rem. 1.2.5, Ex. 1.1.1–1.1.2, Rem. 5.5.2
  and Cor. 6.1.1, and V Thm. 6.3. They were quoted verbatim by
  `review-metabelian-bh-2026-09-13.md` §§3–4. van der Kallen's stability theorem (LNM
  551, Thm 1) was also read at source by gq-k2-q on 09-18.
- **(U3)** Finite presentation of `St_N(R)`. For `N >= 5` this is the refereed
  `steinberg-groups-of-fp-rings-are-fp-in-rank-five`. Only `N = 4` would need the unread
  Krstić–McCool Theorem 3, and every host in the chain can take `N >= 5`. There is an
  independent prior-art source for the finite presentation of `E_n(A)`: Rehmann–Soulé,
  LNM 551, Thm I and §2, as recorded on `elementary-groups-over-polynomial-s-integers-are-fp`.
- **(U4)** Zaremsky, arXiv:2405.18354, Prop. 5.5 (products). The earlier review read it
  from the PDF. BFFHZ l.203, which I re-read, states the same closure with the same citation.
- **(U5)** Remeslennikov's characteristic-zero case, used inside Wehrfritz's Corollary 1.2.

## The chain, step by step

1. **Quasi-linearity.** A f.g. metabelian `G` is isomorphic to a group of matrices over a
   finite direct sum of fields. That is, `G <= Π_i GL_n(K_i)`.
   - *Source, re-read:* Wehrfritz, Canad. J. Math. 27 (1975), p. 1355, Corollary 1.2
     (MSI `bhmeta/wehrfritz1975.pypdf.txt` l.25–27). "If the group G is a finite
     extension, of a finitely generated metabelian group of characteristic π, then G is
     isomorphic to a quasi-linear group of characteristic π." The quasi-linear definition
     is at l.18–20.
   - *Hypotheses match:* yes. It applies to every f.g. metabelian group, and f.p.
     metabelian groups are f.g.
   - Nodes: `fg-metabelian-groups-embed-in-products-of-coprimary-quotients`,
     `fp-metabelian-bh-via-quasi-linear-pbh` step 1.
2. **Coordinates.** Each projection `G_i` is a f.g. linear group over one field `K_i`.
   `G` embeds in `Π G_i`. This is trivial.
3. **Char 0 factor: polynomial coordinates.** `G_i <= GL_M(Z[1/m][s_1..s_k])`
   (`char-zero-linear-groups-embed-in-polynomial-s-integer-groups`). I re-derived it:
   - Restrict scalars to `Q(t)`.
   - Clear denominators: entries lie in `A = Z[1/m][t][1/f]`, a localization of a regular
     ring, hence regular.
   - Apply a Nagata-type substitution after inverting the leading coefficient, so that
     `A` is finite over `P = Z[1/m][s]`.
   - Miracle flatness applies because `A` is Cohen–Macaulay and `P` is regular. So `A` is
     flat, hence projective, hence free by Quillen–Suslin over the PID `Z[1/m]`.
   - The regular representation gives `GL_n(A) -> GL_(nr)(P)`.

   No gap. I checked the one real risk, freeness, which would fail for a non-CM ring:
   the ring used is a localization of a polynomial ring, so it is regular.
4. **Into `E_N`.** `g -> diag(g, (g^T)^-1, I)` is a homomorphism into `SL_N(R)`.
   - `SL_N(R) = E_N(R)` for `N >= k+3`, since `SK_1(R) = SK_1(Z[1/m]) = 0` and `sr(R)`
     is at most `dim R + 1 = k+2`.
   - Inputs: (U2). The transpose-inverse form is a homomorphism, which is the correct
     repair of the `diag(g, g^-1)` slip caught elsewhere on 09-18.
5. **`E_N(R)` is finitely presented for `N >= k+4`**
   (`elementary-groups-over-polynomial-s-integers-are-fp`).
   - van der Kallen gives `K_2(N,R) ≅ K_2(R)` for `N >= d+3` with `d = k+1`.
   - Homotopy invariance gives `K_2(R) = K_2(Z[1/m])`, which is finite (Dennis–Stein §4).
   - The kernel is central: injective stability plus centrality of `K_2(R)` in `St(R)`.
   - So `E_N(R) = St_N(R)/(finite central)` is finitely presented. Inputs: (U2), (U3).
6. **The affine host is finitely presented** (`affine-extension-of-fp-elementary-group-is-fp`).
   I re-derived the proof route A–F4 in outline. The commutator bookkeeping checks: for
   example, in step B, `x_kl(1)` conjugates `x_ik(r)` to `x_il(-r) x_ik(r)`, and the
   identities used hold in any group. It needs `N >= 4`. No gap.
7. **Self-similarity** (`polynomial-parameter-affine-groups-are-self-similar`). I
   re-derived it independently.
   - The group `R^n ⋊ E_n(R)` acts on `Z_p^n × Z_p^k` (`p ∤ m`) by
     `(g,b)(v,s) = (g(s)v + b(s), s)`.
   - At the first-level vertex `(e,a)`, write `v = e + pv'` and `s = a + ps'`. The state
     is `(σ_a g, (σ_a(g)e + σ_a(b) - c)/p)`, with `σ_a: t_j -> a_j + p t_j`.
   - The numerator lies in `pR^n`. Its constant term is `≡ 0 (mod p)` in `Z[1/m]`, and
     `Z[1/m] ∩ pZ_p = pZ[1/m]`. Every higher monomial in `s'` carries `p^(deg)`.
   - `σ_a` is a unital ring endomorphism, so it maps `E_n(R)` into itself.
   - Faithfulness follows by Zariski density of `Z_p^k`.
   - This is Zaremsky's Definition 2.1 (arXiv:2405.09722 l.109–111, re-read). No gap.
8. **Zaremsky's envelope.** "Theorem 1.1. Every finitely presented self-similar group
   embeds in a finitely presented simple group" (arXiv:2405.09722v2, re-read on MSI,
   `bh-reviewer/2405.09722.txt`, abstract and l.30–33). There are no hypotheses beyond
   Definition 2.1 and finite presentation, and `d = p^(n+k) >= 2`.
9. **Permutational class.**
   - Zaremsky's envelope is a finitely presented commutator subgroup of a
     Röver–Nekrashevych group. BFFHZ Remark 3.5 (arXiv:2503.21882v2 l.726–740, re-read)
     says these are highly transitive, citing [Nek18, Thm 4.7].
   - BFFHZ Theorem C (l.168–177, re-read), (iii) ⟹ (i) "as does every subgroup thereof",
     puts every subgroup in `B_A`. Nodes: `fp-self-similar-subgroups-satisfy-permutational-boone-higman`
     (a), `char-zero-linear-groups-satisfy-permutational-boone-higman`.
10. **Char p factor.** This is the same scheme over `R = F_p[s_1..s_k]`, with `O = F_p[[u]]`,
    `s_1 -> u` as the digit variable, and `s_2..s_k` as parameter coordinates
    (`char-p-linear-groups-satisfy-permutational-boone-higman`).
    - I checked the states `σ_α: s_i -> α_i + s_1 s_i` against the review's §2
      derivation. The divisibility by `s_1` is correct.
    - `K_2(N, F_p[s]) = K_2(F_p) = 1` for `N >= k+3`, so `St_N = E_N`. Consistency check:
      `SL_3(F_q[t])` is not finitely presented (Behr), and the chain uses `N >= 4`.
    - The embedding uses Nagata substitution plus miracle flatness plus Quillen–Suslin
      over a field. No gap.
11. **Product.** `B_A` is closed under finite direct products and subgroups.
    - Zaremsky 2405.18354 Prop. 5.5 is (U4). BFFHZ l.203 was re-read: "PBH is stable under
      commensurability and direct products [Zarb]".
    - Node: `boone-higman-type-a-class-closed-under-finite-extensions`. So `G <= Π G_i` is
      in `B_A`.
12. **Conclusion.** BFFHZ Theorem C (i) ⟹ (ii): `G` embeds in a finitely presented simple
    twisted Brin–Thompson group. This answers BBMZ Problem 5.3(7), and the chain gives it
    for all finitely generated metabelian groups.

## Attempts to break it (all failed)

- **Hidden hypotheses in Zaremsky 1.1.** There are none: the abstract and Theorem 1.1 read
  "every finitely presented self-similar group".
- **"Virtually BH ⇒ BH" or finite-extension steps.** None are used. The route
  `fp-metabelian-bh-via-quasi-linear-pbh` uses only subgroups, products inside `B_A`, and
  Theorem C.
- **Char-0/char-p split.** Wehrfritz already provides the mixed product. The open node
  `boone-higman-closed-under-finite-direct-products` is never used.
- **Freeness over the polynomial ring.** This fails for non-CM rings, but the ring used is
  regular (step 3).
- **Rank limits** (Behr, Krstić–McCool on `SL_3(Z[t])`, Bux–Mohammadi–Wortman). The chain
  uses `N >= max(5, k+4)`, outside all of them.
- **Consistency with repo obstructions.** `affine-self-similar-coordinate-rings-are-one-dimensional`
  and `fg-metabelian-groups-have-roots-at-finitely-many-primes` assume constant
  coefficients and restrict divisibility. Neither applies: f.g. linear groups have no
  unbounded roots, and the linear parts vary with the parameter.

## Priority beyond arXiv

- **Searched:** the arXiv API full-text query `"Boone-Higman"`, listing all 16 hits through
  2609.01868 (Almeida–Dantas–Oliveira-Tosti, permutational wreath products of abelian
  groups). No entry claims metabelian or arbitrary-field linear groups; only 2405.09722
  claims f.g. subgroups of `GL_n(Q)`. Queries pairing metabelian with finitely presented
  simple groups returned nothing.
- **Not reachable:** Google Scholar (403) and Semantic Scholar (429). MathSciNet was not
  reached.
- **So:** no priority is claimed. The novelty check is bounded to arXiv.

## Scope notes

- **Transfer to spherical Artin groups.** The same char-0 chain underwrites F1's spherical
  Artin item, since those groups are linear over `Q(q,t)` (Digne, Cohen–Wales). I did not
  re-read the linearity theorem.
- **Not checked:** the affine Artin items `B̃_n` and `C̃_n` of F1.
- **External claim.** This is a strong result (BBMZ 5.3(7), and every f.g. linear group
  in every characteristic). Before any external claim, it needs an expert human read of
  steps 3, 7 and 10 plus a MathSciNet search.
