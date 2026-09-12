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
5. **Leavitt--Nekrashevych completions (untried construction).**
   - *Setting:* a finitely presented `B` with a matrix recursion
     `psi : B -> M_d(B)`, and `O_psi = < B, L_d | b = sum_(ij) s_i psi(b)_(ij) t_j >`.
   - *Open:* injectivity of `B -> O_psi`, and simplicity of `O_psi` under a
     minimality condition on `psi`.
   - *Why it matters:* this is the algebra analogue of Zaremsky's theorem that
     finitely presented self-similar groups satisfy Boone--Higman, through
     Röver--Nekrashevych groups.
