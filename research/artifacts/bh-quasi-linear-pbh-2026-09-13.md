# Boone–Higman for finitely generated metabelian groups through self-similar hosts in every characteristic

Lane `bh-metabelian`, 2026-09-13. Target: item (7) of Problem 5.3 in
Belk–Bleak–Matucci–Zaremsky (BBMZ), arXiv:2306.16356v3.

**Outcome: solution, landed; independent review PASS (`research/artifacts/review-metabelian-bh-2026-09-13.md`, 2026-09-13).**
- Every finitely generated group of matrices over a finite product of fields, in
  any characteristics, lies in the permutational class `B_A`.
- In particular every finitely generated metabelian group does, so every finitely
  presented metabelian group embeds in a finitely presented simple group.

A reviewer should treat the four new mathematical nodes (§1) as the claims to
check. Everything else was already established and reviewed before this lane.

## 1. The chain

| Node | Role | Commit | Status before review |
|---|---|---|---|
| `positive-char-polynomial-affine-groups-are-self-similar` | host is self-similar | f6aade283 | new, direct proof |
| `elementary-groups-over-polynomial-f-p-rings-are-fp` | `E_N(F_p[s])` finitely presented | e6f83e6c1 | new, textbook imports |
| `char-p-linear-groups-embed-in-polynomial-f-p-groups` | polynomial coordinates | b51c04469 | new, standard algebra |
| `char-p-linear-groups-satisfy-permutational-boone-higman` | composition | b1dd51dfa | new, composition |
| `quasi-linear-groups-satisfy-permutational-boone-higman` | products in `B_A` | this landing | composition |
| `fp-metabelian-bh-via-quasi-linear-pbh` | route into the root | this landing | composition |

Reused, established and reviewed:
- `fg-metabelian-groups-embed-in-products-of-coprimary-quotients` (Wehrfritz);
- `char-zero-linear-groups-satisfy-permutational-boone-higman`;
- `affine-extension-of-fp-elementary-group-is-fp`;
- `fp-self-similar-subgroups-satisfy-permutational-boone-higman` (Zaremsky's
  envelope and BFFHZ Theorem C);
- `boone-higman-type-a-class-closed-under-finite-extensions` (Zaremsky,
  arXiv:2405.18354, Proposition 5.6; the product statement there is Proposition 5.5).

## 2. The one new idea: the uniformizer is a variable

In characteristic zero the parameter-coordinate host of
`polynomial-parameter-affine-groups-are-self-similar` lets `Z[1/m][t_1..t_k]` act on
`Z_p^n x Z_p^k`. The uniformizer is the constant `p`, and the states substitute
`t_j -> a_j + p t_j`.

In characteristic `p` there is no constant uniformizer, so one variable plays that
role:
- `R = F_p[s_1..s_k]` acts on `F_p[[u]]^n x F_p[[u]]^(k-1)`.
- `s_1` goes to `u`, and `s_2..s_k` are evaluated at the parameter point.
- The states substitute `s_i -> α_i + s_1 s_i`.

The carry `σ_α(P) - P(0,α)` is divisible by `s_1` in the polynomial ring, which is
exactly what self-similarity needs.

Zaremsky's principal-ideal criterion needs `R/xR` finite, which forces Krull
dimension one. The recorded obstruction
`affine-self-similar-coordinate-rings-are-one-dimensional` covers digit trees with
constant coefficients, and its own Scope lists parameter coordinates as the
escape. Here the linear part varies with the parameter point.

**Two places where characteristic `p` is easier than characteristic zero.**
- No denominators. The Nagata normalization has a unit leading coefficient.
- `K_2(F_p[s_1..s_k]) = K_2(F_p) = 0`. So in the stable range `E_n = St_n`, and no
  kernel generators have to be pulled back.

## 3. Sources checked

| Source | How read | Used for |
|---|---|---|
| Zaremsky, arXiv:2405.09722 | extracted text on MSI (`bh-reviewer/2405.09722.txt`, l.109–110) | Definition 2.1 (self-similar), quoted in the host proof |
| Weibel, *K-book*, Chapter III | chapter PDF from Weibel's site, downloaded on MSI (`/scratch.global/sauer354/bhcharp/`), page images read locally | Ex. 1.1.1 and 1.1.2 (p. 1–2); Remark 1.2.5, Vaserstein (p. 3); Remark 5.5.2, stability (p. 38); Cor. 6.1.1, `K_2(F_q) = 1` (p. 48) |
| Weibel, *K-book*, Chapter V | same | Theorem 6.3, homotopy invariance for regular noetherian rings (p. 40) |
| Stacks Project | `algebra.tex` on MSI (`/scratch.global/sauer354/bc0/`), statements printed from the labels mapped by the `tags` file | 00OQ, 00OD, 00NQ, 0BC1, 0AFV, 00H8, 00ON, 00R4, 00HT, 00NX |
| Quillen, Invent. Math. 36 (1976) | journal PDF (`bc0/quillen1976.pdf`), page image | Theorem 4 (p. 169) |

**Not re-read here; taken from established nodes:**
- Weibel IV, Cor. 1.7.1: Quillen's `K_1`, `K_2` agree with Chapter III's. It is as
  cited in the reviewed `elementary-groups-over-polynomial-s-integers-are-fp-proof`.
- Krstić–McCool: `St_n` of a finitely presented ring is finitely presented for
  `n >= 4` (`steinberg-finite-presentation-and-kazhdan-theorem`).
- BFFHZ Theorem C, Zaremsky Theorem 1.1 and Proposition 5.5 (products; cited by BFFHZ as 5.6), Wehrfritz Corollary 1.2.

## 4. Adversarial checks

1. **Levels.** `P<a> mod u^j` depends only on `a mod u^j`, since coefficients lie in
   `F_p`. So elements act by tree automorphisms.
2. **Faithfulness.** It uses only that `F_p[s_1] -> F_p[[u]]` is injective and that
   `F_p[[u]]` is an infinite domain.
3. **States stay in the group.** `σ_α` is a unital ring endomorphism, so it
   preserves `E_n` and determinants.
4. **Block map.** `g -> diag(g, (g^T)^-1, I)` is a homomorphism. The non-homomorphism
   `diag(g, g^-1)` (`whitehead-diagonal-map-is-not-multiplicative`) is not used.
5. **`SL_N = E_N`.** Needs `N >= k+2`, `sr(R) <= k+1` and `SK_1(R) = 0`. All three
   hold with `N = max(k+4, 2M)`.
6. **Finite presentation of the host.** `N >= max(4, k+3)` for `E_N`, and `N >= 4`
   with `R` finitely generated for the affine extension.
7. **Compatibility with the non-self-similarity theorems.**
   - Kochloukova–Sidki, arXiv:1710.04745 (TeX l.812), and arXiv:2509.05798 show that
     some Krull-dimension-2 metabelian groups are not self-similar themselves.
   - Here the metabelian group is only a subgroup of a non-metabelian host. The
     characteristic-zero root already uses this, with Baumslag's group
     (`baumslag-char-zero-metabelian-group-is-not-self-similar`).
8. **Products.** They are taken inside `B_A`. The open
   `boone-higman-closed-under-finite-direct-products` is not used.

## 5. Novelty search (bounded, 2026-09-13)

- **Web search.** Four queries on Boone–Higman with metabelian groups, positive
  characteristic linear groups, self-similar affine groups over polynomial rings
  over `F_p`, and 2025–26 arXiv. None returned a paper settling Problem 5.3(7) or
  placing positive-characteristic linear groups of transcendence degree at least 2
  in `B_A`.
  - Hits: the survey v3, Zaremsky arXiv:2405.09722 and arXiv:2405.10234, BFFHZ,
    arXiv:2408.05673, Kochloukova–Sidki arXiv:1710.04745 and arXiv:2509.05798,
    arXiv:2607.21727, arXiv:2507.04347.
- **FFWZ.** arXiv:2603.24687v2, l.145–148, lists the known PBH classes (Q-linear,
  Aut(F_n), hyperbolic, Baumslag–Solitar and free-by-cyclic). No positive
  characteristic appears (quoted on `char-zero-linear-groups-satisfy-permutational-boone-higman`).
- **Kochloukova–Sidki sources on MSI.** Their positive-characteristic self-similar
  metabelian hosts are of Krull dimension one.
- **Not searched:** MathSciNet or zbMATH, and the arXiv API, which returned nothing
  from MSI.
- **No priority is claimed.** Every step is elementary once the characteristic-zero
  host exists. A specialist may know the positive-characteristic host.

## 6. Scope

- **Review.** None of the new nodes has been independently reviewed. The root's
  ESTABLISHED status is computed by Cairn from unreviewed nodes.
- **Still open.** `boone-higman-closed-under-finite-direct-products`, and the
  effective question `no-uniform-metabelian-higman-compiler`.
- **Envelope type.** The conclusion is membership in `B_A`. The simple envelope is
  a finitely presented twisted Brin–Thompson group.
