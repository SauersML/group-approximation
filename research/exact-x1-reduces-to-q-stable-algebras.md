---
rg: 2
id: exact-x1-reduces-to-q-stable-algebras
kind: claim
title: A trace is quasidiagonal iff its tensor product with the trace of Q is, so exact X(1) reduces to Q-stable algebras and any counterexample must fail the UCT after every UHF stabilization
distinct_from:
  amenable-traces-on-exact-cstar-algebras-are-quasidiagonal: that is the open flagship over all exact algebras; this proves it is equivalent to its restriction to Q-stable algebras and pins down the one part of the UCT that its known positive case uses.
  coprime-uhf-stabilizations-detect-uct: that splits the UCT of one nuclear algebra into UHF-localized halves; this shows exact X(1) sees only whether the UCT-support filter is nonempty, i.e. whether A tensor Q satisfies the UCT, and never its torsion part.
  tww-gabe-schafhauser-af-embedding-theorem: that needs the UCT for A itself; this extends its trace conclusion to every exact A such that A tensor Q (or A tensor C, for some exact C with a faithful amenable trace) satisfies the UCT.
  stw10-homotopy-domination-preserves-amenable-qd: that changes the algebra by homotopy, which preserves and reflects the UCT; this changes it by rationalization, which reflects quasidiagonality of traces but not the UCT.
artifacts:
  - research/exact-x1-reduces-to-q-stable-algebras-proof.md
---

**ESTABLISHED (derivation `exact-x1-reduces-to-q-stable-algebras-proof`).**

Let `A` be a unital C\*-algebra with a tracial state `tau`, let `C` be a
unital C\*-algebra with a tracial state `sigma`, and let `Q` be the universal
UHF algebra with its unique trace `tau_Q`.

**Theorem 1 (rationalization reflects and preserves QD traces).**

1. If `tau ⊗ sigma` is quasidiagonal on `A ⊗_min C`, then `tau` is
   quasidiagonal.
2. If `tau` and `sigma` are quasidiagonal, then `tau ⊗ sigma` is
   quasidiagonal.
3. In particular `tau` is quasidiagonal iff `tau ⊗ tau_Q` is quasidiagonal on
   `A ⊗ Q`.

**Theorem 2 (strict reduction of the flagship).** The following are
equivalent.

- (a) Every amenable trace on every exact C\*-algebra is quasidiagonal (the
  flagship `amenable-traces-on-exact-cstar-algebras-are-quasidiagonal`).
- (b) Every faithful amenable trace on every separable, unital, exact,
  `Q`-stable C\*-algebra is quasidiagonal.

In (b) the algebra has uniquely divisible `K_*`. It is `Z`-stable. Every
trace on it has the form `rho ⊗ tau_Q`.

**Corollary 3 (new positive class: rationally UCT algebras).** Let `A` be
separable and exact, with a faithful amenable trace `tau`. Suppose `A ⊗ C`
satisfies the UCT for some separable exact `C` carrying a faithful amenable
trace; `C = Q` or any `M_{P^∞}` will do. Then `tau` is quasidiagonal. For a
nuclear `A`, in the notation of `coprime-uhf-stabilizations-detect-uct`, this
holds as soon as the UCT-support filter `𝒫(A)` is nonempty.

**Corollary 4 (obstruction on counterexamples).** Let `(A, tau)` be a
separable exact algebra with a faithful amenable non-QD trace. Then:

- `A ⊗ M_{P^∞}` fails the UCT for every set of primes `P`, so `𝒫(A) = ∅`;
- `(A ⊗ Q, tau ⊗ tau_Q)` is again a counterexample.

The previous obstruction, stated in the target, only said "`A` is not UCT".
The new statement kills every candidate whose UCT failure disappears after
some UHF stabilization, i.e. whose failure is torsion-supported and dies
after inverting some set of primes. (For nuclear `A`,
`coprime-uhf-stabilizations-detect-uct` shows such a failure has a proper
UCT-support filter, and at most one prime `p` repairs it by
`M_{p^∞}`-stabilization.) So any mechanism that breaks the UCT only in
torsion can never produce a counterexample.

## Calibration and scope

- **No false positive on the literal group.** Theorem 1 holds for every
  C\*-algebra, but the input theorem needs exactness. The universal X(1)
  counterexample `C*(E)` (`stw99-x1-fails-via-literal-group`) gives the
  non-exact algebra `C*(E) ⊗ Q`, so no step applies to it. This is consistent
  with Theorem 1(3), which transports the failure of quasidiagonality to
  `tau_E ⊗ tau_Q`.
- **The criterion is sufficient, not necessary, for non-nuclear algebras.**
  Moradi--Amini, arXiv:2606.13924v1, Theorem 5.6 (read 2026-09-17, preprint)
  construct an exact, simple, unital, tracially AF algebra `V` with
  `K_0(J_V) ⊗ Q ≠ 0`, where `J_V = ker(V ⊗_max V → V ⊗_min V)`. Then
  `J_{V⊗Q} = J_V ⊗ Q` (tensoring with the nuclear `Q` is exact) has
  `K_0 = K_0(J_V) ⊗ Q ≠ 0`. By Skandalis, a K-nuclear algebra has a
  KK-contractible `J`, so `V ⊗ Q` is not KK-equivalent to a nuclear algebra
  and fails the UCT. Yet tracial AF approximation makes every trace of `V`
  quasidiagonal: compress by the almost central projections `p` of the TAF
  definition, with `tau(1-p)` small, into finite-dimensional algebras. So Corollary 3 does not reach all exact positive
  cases; this remark depends on that unrefereed preprint and nothing above
  relies on it.
- **What remains.** After the reduction, a counterexample is a separable
  exact `Q`-stable algebra `A` with a faithful amenable trace `rho ⊗ tau_Q`.
  For such an algebra `A ⊗ Q ≅ A` fails the UCT. By the Schafhauser framework
  the obstruction is then a class in `KK^1_nuc(A, J)`, where `J` is the
  trace-kernel ideal of `Q_ω`, and that class lies in the kernel of the
  K-theory map. This last sentence is a pointer, not a claim of this node.

Credit: Theorem 1 is an elementary permanence argument and is very likely
folklore. A brief literature search found no printed statement of Theorem 2
or Corollary 4. No priority is claimed for Theorem 1.
