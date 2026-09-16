---
rg: 2
id: coset-lamp-seed-radical-is-ce-fixed-algebra-rigidity
kind: claim
title: A two-point coset-lamp seed is in the hyperlinear radical iff Connes-embeddable actions have no subgroup-invariant set it moves
distinct_from:
  binary-coset-lamp-coefficient-forces-relative-embedding: that starts from the weakly mixing coefficient tau(u_g^* s u_g s)=1_(g in C) and extracts scalar relative embeddability; this uses any subgroup-invariant set moved by a single element, in any p.m.p. action with Connes-embeddable crossed product, and decides radical membership of one seed.
  random-coset-lamp-correlations-realize-every-irs-character: that realizes IRS characters as four-letter lamp correlations in a direct integral; this is an equivalence between seed radical membership and fixed-algebra rigidity of Connes-embeddable actions.
  coset-bernoulli-ce-refutes-relative-commutant-collapse: that turns Connes embeddability of the coset Bernoulli crossed product into a leak refuting commutant collapse; this turns Connes embeddability of any action with a moved invariant set into a surviving lamp seed, and proves the converse via the dual shift.
  homogeneous-quotient-ce-refutes-arithmetic-commutant-collapse: that consumes a Connes-embeddable homogeneous crossed product to refute relative-commutant collapse for group microstates; this consumes such an action to keep a lamp seed outside the hyperlinear radical of the permutational lamp group.
  sl3-codense-coset-lamp-recursive-host: that proves the exact finite-dimensional invisibility of the SL3 two-point lamp mark; this characterizes the matrix-ultraproduct visibility of the same kind of seed for every countable pair.
  profinite-action-fixed-algebra-invariant: that proves the subgroup-fixed algebra is invariant for profinite actions of compressor-generated pairs; this proves that radical membership of a lamp seed is equivalent to that invariance for all Connes-embeddable p.m.p. actions, where profinite actions are only the degenerate case.
  kt-free-action-hyperlinear-iff-wreath-hyperlinear: that equates hyperlinearity of one Bernoulli-type free action with hyperlinearity of the Kun--Thom wreath; this characterizes radical membership of a single two-point seed through all Connes-embeddable actions, with no freeness assumption.
artifacts:
  - research/artifacts/seed-radical-transfer-2026-09-16.md
---

**ESTABLISHED** by route `coset-lamp-seed-radical-fixed-algebra-proof`.

Let `C <= A` be countable groups, `X = A/C`, `x_0 = C`, and `L = directSum_X F_2` with the permutation action. Let
`L_0` be its augmentation submodule. For `a in A - C` put `m_a = delta_(x_0) + delta_(a x_0)`.

**Theorem.**

- **(C1)** Suppose `A` acts by measure-preserving Borel automorphisms on a standard probability space `(Z, kappa)`,
  the crossed product `L^infinity(Z) rtimes A` is Connes embeddable, and a Borel set `E` has `kappa(cE triangle E) = 0`
  for all `c in C` and `kappa(aE triangle E) > 0`. Then `m_a notin Rad_hyp(L rtimes A)`. The homomorphism is
  `(l,d) -> F_l u_d`, where `F_l(z) = (-1)^(sum_x l(x) Phi(z)(x))` and `Phi(z)(b x_0) = 1_(E')(b^(-1) z)`, with
  `E' = intersect_(c in C) cE`. It sends `m_a` to `1 - 2 . 1_(E' triangle aE')`.
- **(C2)** If `A` is hyperlinear and `m_a notin Rad_hyp(L rtimes A)`, such an action exists. One may take the shift
  on `F_2^X` with an invariant measure and `E = {f : f(x_0) = 1}`.
- **(C3)** If `H <= G` has index two and `G - H` contains an involution, then `Rad_hyp(H) = Rad_hyp(G) cap H`. In
  particular `m_a` is in the radical of `L_0 rtimes A` iff it is in the radical of `L rtimes A`.

Hence, for hyperlinear `A`, the following are equivalent:

1. `m_a in Rad_hyp(L rtimes A)`;
2. `m_a in Rad_hyp(L_0 rtimes A)`;
3. `J in Rad_hyp(P(L rtimes A, m_a))`, by `central-d8-mark-radical-equals-seed-radical`;
4. `J in Rad_hyp(P(L_0 rtimes A, m_a))`;
5. for every p.m.p. action of `A` with Connes-embeddable crossed product,

   ```text
   L^infinity(Z)^C  <=  L^infinity(Z)^(<C,a>).
   ```

**Scope remark.** If every finite quotient of `A` has the same image as `C` (finite-quotient codensity), then every
profinite action satisfies clause 5. Conditional expectations onto the finite levels are equivariant, and a
`C`-invariant function on a finite `A`-set is `A`-invariant. So a separating action must be genuinely
non-profinite. For the Bernoulli measure the crossed product is the group factor `L(L rtimes A)`. There (C1) says
only that a hyperlinear lamp group does not kill a nontrivial seed. The content of (C1) is that any Connes-embeddable
action with a moved invariant set suffices.
