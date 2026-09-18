---
rg: 2
id: leavitt-resolvent-ring-is-fp-simple-of-char-zero
kind: claim
title: The binary Leavitt ring with a number operator and its resolvent is simple, of characteristic zero, contains Q, and is finitely presented as a ring (over Z)
distinct_from:
  q-embeds-in-a-corner-of-a-fp-toeplitz-ring: that is the Toeplitz version, which contains Q but is not simple (its vacuum idempotent is minimal); this glues the vacuum to a Leavitt isometry, so the ring is purely infinite and simple.
  fp-simple-ring-of-characteristic-zero-exists: that is the existence question; this is the explicit ring that answers it.
  leavitt-subalgebra-linear-groups-satisfy-boone-higman: that uses the characteristic-two ring L_(F_2)(1,2), whose finitely generated subrings never contain Q; this is a characteristic-zero ring containing Q.
  leavitt-nekrashevych-completion-simplicity-criterion: that is the general criterion; this applies it to one completion over a non-finitely-generated base.
artifacts:
  - research/artifacts/gq-gq-lit-arxiv-priority.md
  - research/artifacts/gq-referee-a-leavitt-resolvent-ring-is-fp-simple-of-char-zero.md
  - research/artifacts/gq-referee-b-leavitt-resolvent-ring-is-fp-simple-of-char-zero.md
  - research/artifacts/gq-referee-c-leavitt-resolvent-ring-is-fp-simple-of-char-zero.md
---

**ESTABLISHED** through `leavitt-resolvent-ring-is-fp-simple-of-char-zero-proof` (lane
proof). **Refereed PASS three times:** `gq-referee-a` (proof gaps,
`gq-referee-a-leavitt-resolvent-ring-is-fp-simple-of-char-zero.md`, 8f4edc918),
`gq-referee-b` (citations and hypotheses, `gq-referee-b-leavitt-resolvent-ring-is-fp-simple-of-char-zero.md`,
dfd8468b9), and `gq-referee-c` (an independent proof that avoids the completion criterion,
`gq-referee-c-leavitt-resolvent-ring-is-fp-simple-of-char-zero.md`, f7c7c3e04). The
criterion node itself is an unrefereed lane proof; referee b checked the parts used (normal
form and the main direction of part 3), and referee c's proof does not use it. No priority is claimed beyond
a bounded search: no source found states the existence of a finitely presented simple
ring of characteristic zero (lane `gq-lit-arxiv`, artifact `gq-gq-lit-arxiv-priority.md`
§6). The closest known results each give only part of it. `L_(F_p)(1,n)` is finitely
presented and simple, but of characteristic `p`. Bokut (Algebra i Logika 15, 1976) gives
finitely generated simple envelopes. Belyaev (Algebra i Logika 17, 1978) gives finitely
presented envelopes that are not simple. The construction may be folklore among
algebraic Cuntz--Pimsner rings (Carlsen--Ortega).

**Known and credit.** Finitely presented simple *algebras over a field* of characteristic
zero are classical: the Weyl algebra `A_1(Q)`, the Leavitt algebras `L_Q(1,n)`, and
Nekrashevych algebras are finitely presented over `Q` and simple. The point here is finite
presentation *as a ring*, that is, as a `Z`-algebra, which forces all of `Q` to be generated
by finitely many elements. This is the characteristic-zero case of the algebra form of
Boone--Higman (`algebra-boone-higman-conjecture`, with finite presentation over `Z`) for
these inputs. No printed source asks this question, so it is not an answer to an open
problem. A bounded search (web and arXiv; no MathSciNet, zbMATH or Dniester Notebook;
`gq-gq-lit-arxiv-priority.md` §§6, 9) found no prior construction.

**Statement.** Let

    R_L = Z< s_1, s_2, t_1, t_2, N, A |
             t_i s_j = δ_ij,  s_1 t_1 + s_2 t_2 = 1,
             N s_1 = s_1 (N + 1),  N s_2 = 0,  A (N+1) = 1 = (N+1) A >,

a ring with 6 generators and 9 relations. Then:
1. `R_L` is a `Q`-algebra and `Q ⊆ R_L` unitally, with
   `1/m = t_2 t_1^(m-1) A s_1^(m-1) s_2` for `m >= 1`.
2. `R_L` is simple, and nonzero.
3. `R_L ≅ M_n(R_L)` as unital rings for every `n >= 1`. So for every `n`,
   `GL_n(Q) <= GL_n(R_L) ≅ R_L^x`, and in fact `GL_n(Q)` lies in the derived subgroup
   `[R_L^x, R_L^x]`.

**Model.** Let `X` be the tail class of the word `2^∞`, that is, the infinite words over
`{1,2}` that end in `2^∞`. On `Q^(X)`:
- `s_i e_ξ = e_(iξ)`, `t_i e_(iξ) = e_ξ` and `t_i e_(jξ) = 0` for `j ≠ i`;
- `N e_ξ = (number of leading 1's of ξ) e_ξ`, and `A = (N+1)^(-1)`.

By simplicity this representation is faithful. Lane `gq-malcev-ring` proposed the same
operator model, with the harmonic carry `D = A`, on 2026-09-17. This node supplies the
finite presentation and the simplicity proof.

**Structure.** `R_L` is the Leavitt--Nekrashevych completion `O_ψ` over
`B = Q[N][(N+c)^(-1) : c >= 1] ⊂ Q(N)`, with `ψ(f) = diag(f(N+1), f(0))`. Two features
make it work:
- the vacuum relation `N s_2 = 0` makes `(N+m)` act as the integer `m` on the range of
  `s_2`;
- one resolvent, transported along `s_1`, gives every `(N+m)^(-1)`.

`B` is not finitely generated, but `O_ψ` is finitely presented, because the shifts of
`A` are generated inside `O_ψ`.

**Use for `gl-n-q-embeds-in-fp-simple-group`.** `R_L` is a finitely presented,
purely infinite simple ring of characteristic zero that contains every `M_n(Q)`
unitally. That is the characteristic-zero analogue of the host `L_(F_2)(1,2)` in
`leavitt-subalgebra-linear-groups-satisfy-boone-higman`. The open group question is
`leavitt-resolvent-derived-units-mod-centre-fp-simple`: is `[R_L^x, R_L^x]` modulo its
centre finitely presented and simple? A yes gives the root through
`gl-n-q-bh-via-leavitt-resolvent-units`.
