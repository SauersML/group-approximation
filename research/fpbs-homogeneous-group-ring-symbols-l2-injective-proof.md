---
rg: 2
id: fpbs-homogeneous-group-ring-symbols-l2-injective-proof
kind: route
title: Rotate eigenspaces by the height circle action and bound the trace by Kaplansky's formula
target: fpbs-homogeneous-group-ring-symbols-l2-injective
requires: []
artifacts:
  - research/artifacts/fpbs-finite-contact-obstruction-2026-09-17.md
---

Artifact §3, Lemma 4.

1. **Circle action.** The unitary `(U_z v)(w) = z^{ht(w)} v(w)` fixes
   `delta_e` and conjugates `lambda(T)` to `z^m lambda(T)`. So it carries
   `ker(lambda(T) - 1)` onto `ker(lambda(T) - z^m)`.
2. **Equal traces.** These kernels are `rho(G)`-invariant, so their
   projections lie in `N(G)`. Their traces `<p delta_e, delta_e>` agree.
3. **Independence.** The eigenspaces for distinct eigenvalues are
   independent: the closure of any `N - 1` of them lies in the kernel of a
   polynomial in `lambda(T)` that acts on the remaining one as a nonzero
   scalar.
4. **Trace bound.** Kaplansky's formula `tau(p ∨ q) + tau(p ∧ q) = tau(p) +
   tau(q)` follows from the polar decomposition of `(1 - q) p`. It gives
   `N tau(p) <= 1` for every `N`. So `p = 0`, since the trace is faithful.
5. **Dense range.** The adjoint `1 - T*` is homogeneous of degree `-m`, so it
   is also injective.
6. **`N(G)` and supergroups.** Injectivity on `N(G)` follows from dense range.
   For a supergroup, `lambda(x)` preserves each `ℓ²(G g)`.

These standard von Neumann algebra facts are used without separate citation:
- faithfulness of the canonical trace on `N(G)`;
- polar decomposition and equivalence of left and right supports.

The proof is self-contained apart from them.
