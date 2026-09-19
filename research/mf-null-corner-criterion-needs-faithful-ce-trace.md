---
rg: 2
id: mf-null-corner-criterion-needs-faithful-ce-trace
kind: claim
title: The torsion-corner radical criterion needs only MF-nullity, and over a hyperlinear host MF-nullity must live in a subalgebra of R^U with no CE-null corner
distinct_from:
  agent-leavitt-not-torsion-corner-noce-forces-mf-radical: that needs a corner algebra with no Connes-embeddable trace; this needs only that the algebra has no unital map into any norm matrix corona, which a no-CE algebra satisfies but which is compatible with a faithful CE trace. It also proves that every no-CE certificate, placed in any nonzero corner of the witness, forces nonhyperlinearity.
  nonce-bcs-unital-algebraic-corner-map-forces-nonhyperlinear: that concludes nonhyperlinearity of the host from one no-CE corner map; this uses that fact only as the death step of a class, and its positive part (MF-null corner criterion, stripping to R^U) concerns algebras that do have CE traces.
  corona-k0-positive-arithmetic-is-real-lp-feasibility: that kills K-zero rank certificates of MF-nullity by real LP feasibility under a faithful trace; this kills tracial certificates (no-CE algebras in corners) by compression of a CE trace, and reduces every witness to a unital subalgebra of R^U.
  binary-complement-corner-has-no-weakly-finite-image: that is a characteristic-two ring statement (no weakly finite quotient of a corner of F_2[R^x]); over C every group-algebra corner has a stably finite image in L(G), and this claim records that such algebraic infiniteness certificates are unavailable for MF-nullity.
  stw99-problem-vii-blackadar-kirchberg: that asks whether nuclear stably finite algebras are MF; the MF-null algebras here are required to sit inside R^U and are not assumed nuclear, and nothing is claimed about nuclear ones.
artifacts:
  - research/mf-null-corner-criterion-needs-faithful-ce-trace-proof.md
---

**ESTABLISHED (written proof; not Lean-verified).** This is an obstruction to a class of approaches to
`property-t-free-leavitt-full-mf-radical`. It also reformulates the missing corner step. It is not a refutation of the
goal, and the goal stays OPEN.

## Definitions

- `Q_k = prod_n M_(k_n)(C) / directSum_(||.||) M_(k_n)(C)` is the norm matrix corona, for any sequence `k_n >= 1`.
- A unital star algebra `B` is **MF-null** if there is no unital star homomorphism `B -> Q_k` for any `k`.
- A tracial state on `B` is **CE** if it is `tau_U o pi` for a unital star homomorphism `pi : B -> R^U`.
- `B` is **CE-null** if it has no CE tracial state.
- For `z in G` of finite order `m`, put `q_z = 1 - (1/m) sum_(j<m) z^j` in `C[G]`.

## Statement

**(A0) CE-null implies MF-null.** Every tracial ultraproduct of the normalized traces on `Q_k` is CE.

**(A) MF-null corner criterion.**
- If `B` is MF-null and `Phi : B -> q_z C[G] q_z` is unital, then `q_z C[G] q_z` is MF-null.
- If `q_z C[G] q_z` is MF-null, then `z in Rad_MF(G)`.
- More generally, let `p` be a projection in `M_n(C[G])` with `p M_n(C[G]) p` MF-null. Then every unital star
  homomorphism `C[G] -> Q_k` kills `p`.

`agent-leavitt-not-torsion-corner-noce-forces-mf-radical` is (A) plus (A0).

**(B) Hyperlinear hosts need a CE trace.**
- Let `z != 1` and let `D` be a unital star subalgebra of `q_z C[G] q_z` containing `q_z`.
- The normalized canonical trace `tau_e / tau_e(q_z)` is a faithful tracial state on `D`, and `tau_e(q_z) = 1 - 1/m > 0`.
- If `G` is hyperlinear, that trace is CE.
- More strongly, suppose some unital star homomorphism `sigma : C[G] -> R^U` has `sigma(z) != 1`. Then the normalized
  trace `tau_U o sigma` on `D` is CE, so `D` is not CE-null. In particular, a CE-null corner image forces
  `z in Rad_hyp(G)`.

**(C) Stripping.**
- Let `B` be MF-null with a CE trace `tau = tau_U o pi`.
- Then `pi(B)`, a unital star subalgebra of `R^U`, is MF-null, and its trace is faithful.
- Let `D` be a unital star subalgebra of `R^U` and `p != 0` a projection in `M_n(D)`. Then no CE-null algebra has a
  unital star homomorphism into `p M_n(D) p`.
- Likewise, let `p != 0` be a projection in `M_n(C[G])` for hyperlinear `G`. Then no CE-null algebra maps unitally into
  `p M_n(C[G]) p`.

## Consequence: the class that dies

Consider an approach that proves `z in Rad_MF(G)` or `Rad_MF(G) = G` through the corner criterion (A), and that
certifies MF-nullity of the witness by a CE-null algebra mapped unitally into some nonzero corner `p` of it.

- Examples: `B_loop`, any MIP*=RE-sourced BCS or quantum-graph algebra, and any no-CE gadget.
- Every such approach proves that `G` is nonhyperlinear, and in fact that `sigma(Phi(p)) = 0` for every tracial
  `R^U`-representation `sigma`.
- **Invariant:** the canonical trace `tau_e o Phi`.
- **Step where every member dies:** the normalized compression of a CE trace to a corner of positive trace is CE.
- For `Delta = St_20(L_(F_2)(1,2))`, this covers:
  - `agent-leavitt-not-bcs-negative-root-corner`;
  - the no-CE augmentation-corner family, e.g. `nonhyperlinear-finite-augmentation-corner-kills-mf` and
    `nonhyperlinear-normal-augmentation-corner-kills-mf`.

  Each is therefore at least as hard as `non-hyperlinear-group` for `Delta`.

**What survives.** Suppose `Delta` is hyperlinear, which is not excluded. Then a corner route must exhibit MF-nullity of
a unital subalgebra of `R^U`, namely `P_z C[Delta] P_z` with its faithful CE trace.

- That MF-nullity is invisible to every tracial and 2-norm invariant.
- It is also invisible to K-zero rank arithmetic, by `corona-k0-positive-arithmetic-is-real-lp-feasibility`.
- It cannot come from algebraic infiniteness (a one-sided invertible, non-invertible matrix in some nonzero quotient).
  The algebra `M_n(C[G])` embeds in the finite von Neumann algebra `M_n(L(G))`. So every corner of it has a nonzero
  stably finite image, for any `G`, hyperlinear or not.
- It has to be an operator-norm-only rigidity. This is the role Property `(T)` plays in the Kazhdan routes.

The weakest hole of this form is `leavitt-root-corner-algebra-is-mf-null`.
