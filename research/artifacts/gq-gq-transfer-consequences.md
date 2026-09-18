# What GL_n(Q) in a finitely presented simple group would give, and which printed questions it answers

Lane `gq-transfer`, 2026-09-17. Root: `gl-n-q-embeds-in-fp-simple-group` (call it G).
Nodes landed with this artifact:
- `number-field-linear-groups-embed-in-gl-n-q` (ESTABLISHED, elementary)
- `number-field-gl-n-embeds-in-fp-simple-group` (OPEN; route from G)
- `prufer-groups-do-not-embed-in-gl-infinity-q` (ESTABLISHED, lane proof)
- `gl-infinity-q-embeds-in-fp-simple-group` (OPEN; route to G)
- `gl-n-qbar-embeds-in-fp-simple-group` (OPEN)
- `countable-char-zero-linear-groups-embed-in-fp-simple-groups` (OPEN; route to the Q̄ claim)

## 1. Kourovka Problem 14.10: wording and status

Proposers: M. Bridson and P. de la Harpe (14th edition, 1999). Three parts in the current numbering.

- **14.10(a)**, quoted from the 14th edition by Mikaelian, arXiv:2310.10536: "Find an explicit and 'natural'
  finitely presented group Γ and an embedding of the additive group of the rationals Q in Γ".
  Answered by Belk–Hyde–Matucci, *Embedding Q into a finitely presented group*, Bull. AMS 59 (2022) 561–567,
  arXiv:2005.02036. Their abstract: the group of lifts of Thompson's T to the real line "is finitely presented and
  contains the additive group Q of the rational numbers. This gives an explicit realization of the Higman
  embedding theorem for Q, answering a Kourovka notebook question of Martin Bridson and Pierre de la Harpe."
- **14.10(b)**, same source: "Find an explicit embedding of Q in a finitely generated group; such a group exists
  by Theorem IV". Mikaelian (arXiv:2310.10536) gives explicit 2-generator embeddings.
- **14.10(c)**, quoted by Mikaelian, arXiv:2507.04347v8 (2026-06-03) §1.4, "which in the current edition of
  Kourovka is coined as Problem 14.10 (c)": "Find an explicit and 'natural' finitely presented group Γ_n and an
  embedding of GL(n,Q) in Γ_n." The same section announces, with no construction (ref. [41]), an explicit
  embedding of GL(n,Q) into a finitely presented, even 2-generator, group via his explicit Higman algorithm.
- BBMZ survey arXiv:2306.16356v3 (22 May 2025) prints this part as Problem 2.7 ("For n ≥ 2, find an explicit and
  natural example of a finitely presented group that contains GL_n(Q)") and says it "remains open".

**Trust surface.** The 21st edition (arXiv:1401.0300v46, 2026-09-01) was not read at 14.10 itself: the HTML page
is too large for the fetch tool (it returned issues 1–10 only) and the PDF could not be parsed remotely. The
wording above is from Mikaelian's quotations. Whether the 21st edition marks (c) as solved, or adds a comment, is
unverified. Mikaelian's v8 postdates that edition's January 2026 publication and still treats (c) as open.

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
| An *explicit and natural* finitely presented (not nec. simple) overgroup | survey Problem 2.7 = Kourovka 14.10(c) (priority: Mikaelian's announcement, not natural) |
| An explicit natural finitely presented **simple** host | all of the above |
| number fields, Q̄, universal char 0, GL_∞(Q) | no printed source found in the survey, Kourovka 14.10, or Mikaelian's papers; these are consequences and strengthenings, not posed problems |

## 7. Status honesty

Both ESTABLISHED nodes are elementary. Neither is independently reviewed, and no novelty is claimed. Everything
else is OPEN.
