---
rg: 2
id: identity-phantom-forces-e-contractibility
kind: claim
title: A phantom identity forces E-contractibility, so a UCT witness is never phantom
distinct_from:
  carrion-shape-milnor-detects-kk-hausdorffness: that identifies the closure of zero in KK/E with a derived limit; this uses it to prove that the identity class can lie in that closure only when the algebra is E-contractible.
  trivial-k-theory-kirchberg-algebras-are-o2: that is the open test class; this proves only that a counterexample there is certified by the Hausdorff quotient KL(A,A) at a single finite shape stage.
artifacts:
  - research/identity-phantom-forces-e-contractibility-proof.md
---

**ESTABLISHED (derivation; full proof in
`research/identity-phantom-forces-e-contractibility-proof.md`).**

**Theorem.** Let `A` be a separable C*-algebra and `(C_n, gamma_n)` a shape
system for `P = SA (x) K`, with canonical maps `gamma_{inf,n}: C_n -> P`. The
following are equivalent.

- (a) `A` is E-contractible, i.e. `E(A,A) = 0`. For nuclear `A` this means
  KK-contractible.
- (b) `id_A` lies in the closure of `{0}` in `E(A,A)`, i.e. `EL(A,A) = 0`. For
  nuclear `A` this means `KL(A,A) = 0`.
- (c) every canonical map `gamma_{inf,n}: C_n -> SA (x) K` is null-homotopic
  through *-homomorphisms.

Analogy: in the stable homotopy category the phantom ideal squares to zero
(Christensen–Strickland, Neeman), so a spectrum whose identity map is phantom is
contractible. This is the operator-algebra version for an identity class. It is
proved directly with Carrion's shape Milnor sequence (arXiv:2608.06496,
Theorem 1.1 and Corollary 4.2) and the Carrion–Schafhauser semiprojectivity
calculus (Theorem 2.2(ii),(v)). The key step is a three-step shift that kills
the lim^1 representative of `id_A`.

## Consequences for STW Problem II

1. **Strict reduction, both directions.** Problem II (every separable nuclear
   algebra satisfies the UCT) holds iff for every unital Kirchberg algebra `A`
   with `K_*(A) = 0`, some (equivalently every) shape system for `SA (x) K` has
   all of its canonical maps `gamma_{inf,n}` null-homotopic, i.e.
   `KL(A,A) = 0`.
   - (=>) UCT with `K_* = 0` gives `KK(A,A) = 0`.
   - (<=) By the theorem, `A` is KK-contractible. So `A` is KK-equivalent to `O_2`, and the
     unit classes agree because both are 0. Kirchberg–Phillips then gives
     `A = O_2`. By the existing reduction
     `kirchberg-uct-reduces-to-trivial-k-kirchberg-algebras`, this settles II.
2. **Obstruction: no witness is a phantom.** For a trivial-K Kirchberg `A` not
   isomorphic to `O_2`, `KL(A,A) != 0`. So the failure is always visible in the
   Hausdorff quotient `lim_n [C_n, SA (x) K]`, at one finite stage `n` where
   `gamma_{inf,n}` is essential. Any approach whose would-be witness lives only
   in `lim^1` (phantom, Pext-type, or "invisible to finite stages") is dead
   for the identity class. A counterexample must have a *finite-stage
   certificate*: a semiprojective `C_n` and an essential *-homomorphism
   `C_n -> SA (x) K` that is compatible with the shape tower.
3. **Calibration.** If `A` satisfies the UCT and `id_A` is in `closure{0}`,
   which is `Pext(K_*A, K_{*+1}A)`, then the Hom component `id` of `K_*A` is
   zero. So `K_* A = 0` and `A` is KK-contractible, as the theorem says. The
   theorem never asserts `KL(A,A) = 0` for a K-trivial algebra, so it proves
   nothing known to be false.

**Novelty note (honest).** For Kirchberg `A` the implication
`KL(A,A) = 0 => A = O_2` can also be obtained from classification machinery:
KL-uniqueness up to approximate unitary equivalence (Dadarlat 2005, with
`O_inf`-absorption) plus Elliott intertwining. The new content here has three
parts: the classification-free E-theory statement for *all* separable `A`; the
explicit finite-stage certificate (c); and the framing as an obstruction to
phantom witnesses.

**Open next step.** Is there an unsuspended stage-null triviality? Prove that
for trivial-K Kirchberg `A` some `gamma_{inf,n}` is null-homotopic, using only
`K_*(A) = 0` and `O_inf`-absorption. The general square-zero statement
`Z(B,D) Z(A,B) = 0` for `Z = closure{0}` is not proved here. It would need
naturality of Carrion's boundary map under asymptotic morphisms in the second
variable.
