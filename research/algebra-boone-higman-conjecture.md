---
rg: 2
id: algebra-boone-higman-conjecture
kind: claim
title: Every finitely generated associative algebra with solvable word problem embeds in a finitely presented simple algebra
root: true
distinct_from:
  boone-higman-conjecture: that is the group statement; this is the associative-algebra analogue, and no implication between the two is known.
  decidable-group-algebras-have-fp-central-simple-hosts: that asks for central simple hosts of group algebras with vanishing K_1 and K_2 of B ⊗ L, and with those conditions it implies group Boone--Higman; this asks only for a finitely presented simple envelope of an arbitrary decidable algebra.
  simple-inputs-have-fp-elementary-leavitt-tensor-hosts: that needs a group embedding into units plus a Steinberg kernel condition; this asks for an algebra embedding, which that premise does not require.
artifacts:
  - research/artifacts/bh-algebra-envelopes-2026-09-12.md
---

**OPEN.** Let `K` be a computable field, e.g. a finite field. Every finitely
generated associative `K`-algebra with solvable word problem embeds in a
finitely presented simple `K`-algebra.

*Marked `root`: it is the algebra form of Boone--Higman. It sits behind the
Leavitt-host route to the group conjecture, but it is not necessary for that
route.*

## What is known

- **Necessity.** Finitely presented simple algebras have solvable word problem
  (`fp-simple-algebras-have-solvable-word-problem`). So the converse direction of
  the conjectured equivalence holds.
- **No universal envelope.** No single host, and no family with one recursive
  word-problem bound, contains all decidable algebras
  (`no-fp-simple-algebra-hosts-every-decidable-algebra`).
- **Relation to group Boone--Higman.**
  - *Strong forms imply the group conjecture.* A central simple fp host with a
    finitely normally generated Steinberg kernel for `B ⊗ L` implies group
    Boone--Higman (route `infinite-simple-input-bh-via-elementary-leavitt-hosts`).
  - *No converse is known.* The group algebra of a nontrivial fp simple group
    has the augmentation ideal, so it is never simple. Steinberg algebras of
    topological full groups do not contain the group algebra canonically
    (`full-group-algebra-to-steinberg-algebra-not-injective`).

## Attempts

1. **Published algebra analogues.** Evans--Mandelberg--Neff (1975) prove the weak
   form: an algebra with solvable word problem embeds in a simple algebra inside
   a finitely presented algebra. The survey arXiv:2306.16356v3 §3 attributes
   this to them for rings of characteristic `p`. Belyaev (1976--78) gives a
   Higman embedding for associative algebras, and Bokut gives finitely generated
   simple envelopes. Neither theorem provides finite presentation and simplicity
   at once. *Dies*: all three were read from secondary sources only
   (`research/artifacts/boone-higman-frontier-2026-09-12.md` §4).
2. **Maximal-ideal quotient.** Embed in a finitely presented `P`, then pass to
   `P/M` for a maximal ideal `M` missing the input. *Dies*: `P/M` is finitely
   presented only if `M` is finitely generated as an ideal. That is the ring
   form of the finite-normal-generation wall for groups.
3. **Tensoring with a simple algebra.** Tensor with a central simple algebra
   `L`, such as a Leavitt algebra or a Leavitt path algebra. *Dies*: every ideal
   of `B ⊗_K L` has the form `I ⊗ L` for an ideal `I` of `B`, so tensoring never
   creates simplicity.
4. **Fixed Leavitt-type hosts.** *Dies* by
   `no-fp-simple-algebra-hosts-every-decidable-algebra`: a fixed host family has
   one complexity bound.
5. **Leavitt--Nekrashevych completions: construction settled, universality open** (2026-09-13).
   - *Setting:* a finitely presented `B` with a matrix recursion
     `psi : B -> M_d(B)`, and `O_psi = < B, L_d | b = sum_(ij) s_i psi(b)_(ij) t_j >`.
   - *Settled:* `O_psi` is finitely presented and `B -> O_psi` is injective iff `psi`
     is injective (`leavitt-nekrashevych-completion-embeds-and-is-fp`). Graded ideals
     correspond to psi-saturated ideals, and `O_psi` is simple when `B` is psi-minimal
     and the core has no off-degree centralizer
     (`leavitt-nekrashevych-completion-simplicity-criterion`).
   - *Open:* the universal premise `decidable-algebras-embed-in-simple-ln-completions`,
     wired to this root by `algebra-bh-via-simple-leavitt-nekrashevych-completions`.
     Minimality must carry the input's decision procedure.
   - *Why it matters:* this is the algebra analogue of Zaremsky's theorem that
     finitely presented self-similar groups satisfy Boone--Higman, through
     Röver--Nekrashevych groups.
6. **Tensor powers of `L_2`** (2026-09-13). *New class, low complexity.* Every subalgebra of
   `M_n(K<x_1..x_m> ⊗ K[t_1..t_k])` embeds in the finitely presented simple algebra
   `M_n(L_2^{⊗(k+1)})` (`polynomially-representable-algebras-have-fp-simple-envelopes`).
   All covered inputs share one exponential time bound, so the monomial complexity
   benchmark stays untouched.
7. **All representable inputs, over every field** (2026-09-18, lane `bh-algebra`). *New class, low
   complexity.* Every finitely generated subalgebra of `M_N(F ⊗ K<x_1..x_m>)`, `F` any field
   extension of `K`, embeds in some `M_n(L_2^{⊗(k+1)})`
   (`field-representable-algebras-have-fp-simple-envelopes`, lane proof). Noether normalization
   reduces field coefficients to polynomial ones, and Attempt 6 finishes. With Anan'in's
   representability theorem (cited, unread) this covers every finitely generated commutative
   algebra and every finitely generated right noetherian PI algebra. The complexity benchmark is
   still untouched, since the hosts are those of Attempt 6.
8. **A transcendental field in characteristic p** (2026-09-18, lane `bh-algebra`). *Not a
   finitely generated input.* For every prime `p`, the whole field `F_p(t)`, and every
   `F_p(t)<x_1..x_m>`, embeds in one explicit finitely presented simple `F_p`-algebra `R_p` with
   center `F_p` (`char-p-rational-function-field-in-fp-simple-algebra`, lane proof).
   The construction: Horner registers realize every monic polynomial as a vacuum value, one
   resolvent inverts them, and a squaring letter `t ↦ t^2` keeps `t` out of the center. It is the
   characteristic-`p` counterpart of `rational-function-fields-embed-in-fp-simple-rings`, where the
   characteristic-zero nonvanishing device (`N + 1 >= 1`) is unavailable.
9. **Every countable field of characteristic p with finite transcendence degree** (2026-09-18,
   lane `bh-algebra`). Nested Horner registers extend Attempt 8 to `F_p(t_1..t_k)`. With the
   characteristic-free ultramatricial step of `field-envelopes-pass-to-algebraic-closures`, every
   such field embeds in a finitely presented simple `F_p`-algebra with center `F_p`, and so do
   finitely generated fields with their matrix and free-algebra extensions
   (`char-p-rational-function-fields-in-fp-simple-algebras`, lane proof). Together with the
   characteristic-zero nodes, every countable field of finite transcendence degree lies in a
   finitely presented simple ring. What remains is `F(t_1, t_2, ...)`, in both characteristics.
10. **Self-similar quotients escape the complexity fence** (2026-09-18, lane `bh-algebra`). A
    non-injective recursion on a free algebra gives a finitely presented completion whose base is the
    self-similar quotient `B/J` (`noninjective-ln-completions-have-self-similar-bases`).
    The word-problem fence of `ln-completion-word-problem-reduces-to-base-algebra` covers only
    injective recursions. New route `algebra-bh-via-simple-self-similar-completions`, through the open
    premise `decidable-algebras-embed-in-simple-self-similar-completions`, with the monomial benchmark
    as its test case.
