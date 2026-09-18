# What GL_n(Q) in a finitely presented simple group would give, and which printed questions it answers

Lane `gq-transfer`, 2026-09-17. Root: `gl-n-q-embeds-in-fp-simple-group` (call it G).
Nodes landed with this artifact:
- `number-field-linear-groups-embed-in-gl-n-q` (ESTABLISHED, elementary)
- `number-field-gl-n-embeds-in-fp-simple-group` (OPEN; route from G)
- `prufer-groups-do-not-embed-in-gl-infinity-q` (ESTABLISHED, lane proof)
- `gl-infinity-q-embeds-in-fp-simple-group` (OPEN; route to G)
- `gl-n-qbar-embeds-in-fp-simple-group` (OPEN)
- `countable-char-zero-linear-groups-embed-in-fp-simple-groups` (OPEN; route to the Q̄ claim)

## 1. Kourovka Problem 14.10: verbatim text and status in the latest edition

**Source read.** *Unsolved Problems in Group Theory. The Kourovka Notebook*, No. 21, arXiv:1401.0300v46
(header: "arXiv:1401.0300v46 [math.GR] 01 Sep 2026"). This is the latest version on arxiv.org/abs on 2026-09-17. It
was read from the arXiv HTML rendering, fetched 2026-09-17 23:14 CDT (5,457,493 bytes, md5
de3156c8466d2d75c2ac258f76751699). Mathematics is transcribed as rendered: Γ_n, GL_n(ℚ), ℚ.

**Main list**, section "Problems from the 14th Issue (1999)". Only part c) remains here, and it carries no comment:

> **14.10.** c) Find an explicit and “natural” finitely presented group Γ_n and an embedding of GL_n(ℚ) in Γ_n.
> Another phrasing of the same problems is: find a simplicial complex X which covers a finite complex such that the
> fundamental group of X is ℚ or, respectively, GL_n(ℚ). *P. de la Harpe*

**Archive of Solved Problems.** Parts a) and b), with their solution comments:

> **14.10.** a) (Well-known problem). It is known that any recursively presented group embeds in a finitely
> presented group (G. Higman, Proc. Royal Soc. London Ser. A, 262 (1961), 455–475). Find an explicit and “natural”
> finitely presented group Γ and an embedding of the additive group of the rationals ℚ in Γ.
> b) Find an explicit embedding of ℚ in a finitely generated group; such a group exists by Theorem IV in
> (G. Higman, B. H. Neumann, H. Neumann, J. London Math. Soc., 24 (1949), 247–254). *P. de la Harpe*
>
> a) Such an embedding is found (J. Belk, J. Hyde, F. Matucci, Bull. Amer. Math. Soc., 59, no. 4 (2022), 561–567).
> b) Such an embedding is found (V. H. Mikaelian, Int. J. Math. Math. Sci., 2005, no. 13 (2005), 2119–2123).

**Status as of v46 (2026-09-01): 14.10(c) is OPEN.** It is in the main list with no comment. The introduction
explains the convention:
- the Archive holds problems whose solutions were commented on before the 2022 edition first appeared;
- "all the solutions that appeared in the updates after that day remain in the main part".
So a recent solution of c) would show as a comment in the main list, and there is none.

**Proposer.** The notebook credits P. de la Harpe alone. Its index lists "De la Harpe P. 14.6–10, …, A: 5.2, 14.10",
and "Bridson M." has only 12.41, 16.90, 21.125, 21.145. The BBMZ survey (arXiv:2306.16356v3, §2) and
Belk–Hyde–Matucci's abstract say "Martin Bridson and Pierre de la Harpe". Cite it as Kourovka Problem 14.10(c)
(P. de la Harpe), with the survey's Problem 2.7 attribution noted.

**What c) asks.**
- An explicit, "natural" finitely presented Γ_n with GL_n(ℚ) ≤ Γ_n.
- Simplicity is not asked.
- Γ_n may depend on n. One group for all n also answers it.
- The "another phrasing" is equivalent: for Γ_n = π_1(K) with K a finite complex, the cover of K corresponding to
  GL_n(ℚ) is an X with π_1(X) = GL_n(ℚ). "Natural" is not defined in the notebook.

**Secondary quotations (consistent with v46).**
- Mikaelian, arXiv:2310.10536, quotes a) and b) from the 14th edition (1999).
- Mikaelian, arXiv:2507.04347v8 (2026-06-03) §1.4, quotes c) as "coined as Problem 14.10 (c)" in the current edition.
  He announces, with no construction (ref. [41]), an explicit embedding of GL(n,ℚ) into some finitely presented,
  even 2-generator, Γ_n via his explicit Higman algorithm.
- The BBMZ survey v3 (22 May 2025) prints c) as Problem 2.7 ("For n ≥ 2, find an explicit and natural example of a
  finitely presented group that contains GL_n(Q)") and says it "remains open".

## 2. What G implies

G is inherited by subgroups, so G gives every subgroup of every GL_N(Q). With
`gl-n-q-targets-are-cofinal-in-n` (SL_n, PGL_n, larger n) this includes:
- Aff(Q) = Q ⋊ Q^x ≤ GL_2(Q) (matrices [[a,b],[0,1]]), U_3(Q) ≤ GL_3(Q), SL_2(Q), PSL_2(Q) ≤ PGL_2(Q),
  the Borel subgroups B_n(Q), and Q^n ⋊ GL_n(Q) ≤ GL_(n+1)(Q). So every stepping stone of the swarm is a
  *necessary* condition for G: a proof that Aff(Q) embeds in no finitely presented simple group would refute G.
- GL_n(Q) × GL_m(Q) ≤ GL_(n+m)(Q), and GL_n(Q) ≀ S_k ≤ GL_(nk)(Q) (block permutation matrices).
- GL_n(Z[1/P]) for **every** set P of primes, computable or not. (No contradiction: arbitrary countable subgroups
  of finitely presented groups need not be computably presented; only finitely generated ones must be.)
- **Number fields** (`number-field-linear-groups-embed-in-gl-n-q`): for a number field K of degree d, restriction
  of scalars gives GL_n(K) ≤ GL_(nd)(Q). So G is equivalent to the same statement for every GL_n(K), K a number
  field (`number-field-gl-n-embeds-in-fp-simple-group`).

## 3. What G does not give through linear embeddings

- **Q̄.** `prufer-groups-do-not-embed-in-gl-infinity-q`: Z(p^∞) embeds in no GL_∞(Q) = ⋃_N GL_N(Q), and the same
  proof works over any number field. Q̄^x contains μ_(p^∞) ≅ Z(p^∞), so for every n ≥ 1, GL_n(Q̄) lies in no
  GL_N(K) and no GL_∞(K) with K a number field. So neither G nor its uniform form
  `gl-infinity-q-embeds-in-fp-simple-group` reaches GL_n(Q̄) by restriction. `gl-n-qbar-embeds-in-fp-simple-group`
  is a separate OPEN claim. For n = 1 it is known: Q̄^x is countable abelian, so it lies in VA.
- **Transcendental coefficients.** (Q(t),+) ≤ GL_2(Q(t)) is divisible abelian of infinite rank.
  - A divisible abelian D ≤ GL_N(Q) is unipotent. If d = e_m^m with e_m in D, some eigenvalue μ_m of e_m has
    μ_m^m = λ, degree ≤ N and height h(λ)/m. Northcott then forces h(λ) = 0, and Kronecker makes λ a root of
    unity, of bounded order since its degree is ≤ N. So the semisimple parts, a homomorphic image of D, form a
    divisible group of bounded exponent, which is trivial.
  - log is additive and injective on commuting unipotents, so a unipotent abelian subgroup of GL_N(Q) has rank ≤ N^2.
  - Hence GL_2(Q(t)) lies in no GL_N(Q). Whether it lies in GL_∞(Q) was not decided here.

## 4. The universal characteristic-0 statement

`countable-char-zero-linear-groups-embed-in-fp-simple-groups`: for all n, every countable subgroup of GL_n(K),
K any field of characteristic 0, embeds in a finitely presented simple group. Equivalent form: GL_n(Ω) embeds for
every n, where Ω is the algebraic closure of Q(t_1, t_2, ...). The reason is that the entries of a countable
subgroup generate a countable subfield of transcendence degree ≤ ℵ_0, and it embeds in the algebraically closed Ω.
This statement implies G, the number-field claim and the Q̄ claim. It is implied by the Boone–Higman conjecture
(survey Corollary 3.5). GL_n(Ω) has solvable word problem for a computable enumeration of Ω. Q(t_1, t_2, ...) is
a computable field, and a computable field has a computable algebraic closure (Rabin 1960). The Cairn route from
the conjecture is left to `gq-reform-countable`, which owns the countable-input form of Boone–Higman. The
finitely generated case is established (`char-zero-linear-groups-satisfy-boone-higman`).

## 5. Uniformity in n, and a Leavitt remark

G asks for a host S_n for each n separately. The uniform `gl-infinity-q-embeds-in-fp-simple-group` (one host for
the finitary GL_∞(Q)) implies G. The converse is not evident, because the hosts may grow with n.

**Remark for the ring lanes.** Over any field K, GL_∞(K) embeds in the unit group of the Leavitt algebra
L = L_K(1,2), with generators x_1, x_2, y_1, y_2, y_i x_j = δ_ij, x_1y_1 + x_2y_2 = 1.
- Put s_i = x_2^i x_1 and t_j = y_1 y_2^j for i, j ≥ 0. Then t_j s_i = δ_ij: use y_2x_2 = 1, y_2x_1 = 0 = y_1x_2
  and y_1x_1 = 1. So e_ij = s_i t_j are finitary matrix units.
- With E_N = Σ_(i<N) e_ii, send g ∈ GL_N(K) to Σ g_ij e_ij + (1 − E_N). This is an injective homomorphism into
  L^x, compatible with g ↦ diag(g,1).
- So a finitely presented simple subgroup of L_Q(1,2)^x (or of any purely infinite simple Q-algebra) that contains
  this copy would give the uniform statement at once.

## 6. Which printed questions each statement answers

| Statement | Printed question it answers |
|---|---|
| G (existence) | BBMZ survey v3 Problem 5.3(5) literally, and the p. 7 sentence ("it remains an open question whether GL_n(Q) embeds into a finitely presented simple group") |
| An *explicit and natural* finitely presented (not nec. simple) overgroup | Kourovka 14.10(c) (P. de la Harpe; open and uncommented in v46, 2026-09-01) = survey Problem 2.7 (priority: Mikaelian's announcement, explicit but not natural) |
| An explicit natural finitely presented **simple** host | all of the above |
| number fields, Q̄, universal char 0, GL_∞(Q) | no printed source found in the survey, Kourovka 14.10, or Mikaelian's papers; these are consequences and strengthenings, not posed problems |

## 7. Status honesty

Both ESTABLISHED nodes are elementary. Neither is independently reviewed, and no novelty is claimed. Everything
else is OPEN.
