---
rg: 2
id: relation-cover-rational-lifting-over-quotientless-kazhdan
kind: claim
title: Some Kazhdan cover of a sofic quotientless Kazhdan group keeps root powers non-torsion in its relation module and has an induced rational envelope
distinct_from:
  kazhdan-rational-relation-cover-reduction: that is the established reduction theorem and its obstructions; this is the open existence statement that the reduction needs.
  torsion-free-sofic-extrinsic-kazhdan-defect-kernel: that asks for the kernel together with an extrinsic compression defect (EK1); this supplies only the intrinsic clauses (torsion-free, sofic, Kazhdan, no finite quotient).
  titz-witzel-kernel-sofic: that asks soficity of a specific simple lattice; this asks for a different torsion-free quotientless Kazhdan group whose soficity comes from an abelian-by-sofic envelope.
artifacts:
  - research/kazhdan-rational-relation-cover-reduction.md
  - research/kazhdan-rational-relation-cover-reduction-proof.md
---

**OPEN.** Notation is as in `kazhdan-rational-relation-cover-reduction`. The
claim is that the following all exist:

- a sofic Kazhdan group `Q` with no nontrivial finite quotient;
- a finitely generated Kazhdan group `P`;
- a surjection `pi: P ->> Q` with kernel `R`.

They must satisfy:

1. (RLT): for every `f in P` such that `pi(f)` has prime order `l`, the power
   `f^l` is not torsion in `R^ab`;
2. `V = QQ (x)_{ZP} I_P` embeds `QQ`-linearly into `(+)_Q W` for some countable
   `W`.

Then `D = [P/R_sat, P/R_sat]` is a nontrivial torsion-free, sofic, Kazhdan
group with no nontrivial finite quotient. That necessary kernel is not
presently known to exist. The natural choice is
`Q = EL_3(LC(X,F_q) semidirect Z)`, from
`lef-kazhdan-group-without-finite-quotients-exists`.

**Equivalent submodule form.** Write `Q = F/R_F` with `F` free of finite rank,
`E = F/[R_F,R_F]`, and relation module `A_F = R_F/[R_F,R_F]`. By items 2 and 5
of the reduction, clause 1 is equivalent to the existence of a `ZQ`-submodule
`B <= A_F` with:

- `A_F/B` torsion-free;
- `E/B` Kazhdan;
- `E/B` torsion-free.

Indeed, given `P = F/S`, take `B` to be the saturation of the image of `S`;
conversely, take `P = E/B`. The free cover `E` is torsion-free and sofic, so
clause 1 asks to force property (T) by killing a pure submodule of the relation
module without creating torsion.

## Attempts

1. **Steinberg covers (dead).** Suppose `P` is a quotient of `St_n(S)` with
   `n >= 3`. Then `K = P/R_sat` is too. By
   `steinberg-images-die-in-torsion-free-groups`, a torsion-free `K` is
   trivial, but `K` maps onto `Q != 1`. So clause 1 fails. This covers every
   normally elementary `P`, including `EL_3(S)` itself.

2. **Finite-index elementary covers in characteristic p (dead).** Item 6 of
   the reduction, statement (RE), applies with
   `[e_13(pN), e_32(pNu)] = e_12(p^2N^2u) = e_12(pu)^{pN^2}`. It kills every
   finite-index `P <= EL_n(S)`, `n >= 3`, over an infinite characteristic-`p`
   quotient ring `T`, with `pi` induced by `S ->> T`.

   The mechanism is general. Clause 1 fails whenever a root element of `P`
   maps to `l`-torsion, and some integer multiple of its `l`-th power is a
   product of two root elements in `R`. So a linear cover must avoid
   congruence-type root subgroups in `R`. Two options remain:
   - `P` of infinite index, with `R` containing no root pair;
   - `Q` in characteristic zero, where root elements of `Q` have infinite order
     and the torsion comes from Weyl-type or finite subgroups.

3. **Torsion in `P` (dead, trivially).** An element `g` of finite order with
   `pi(g) != 1` violates clause 1. So `P` may be chosen torsion-free, and must
   be torsion-free over the torsion of `Q`.

4. **Hyperbolic covers (untested, live).** Suppose `Q` is a quotient of a
   finitely presented Kazhdan group `Q'`. Apply
   `belegradek-osin-rips-construction` to `Q'` with a torsion-free hyperbolic
   Kazhdan `H`. This gives a torsion-free hyperbolic Kazhdan `G ->> Q' ->> Q`.

   `G` has no root elements, so (RE) does not apply. Clause 1 for `G` is then a
   question about the `Z`-torsion of `R^ab`, for the kernel `R` of `G ->> Q`,
   at `l`-th powers of lifts of torsion. No argument either way is known.

   The existence of `Q'` needs an import, for example Shalom's theorem that
   Kazhdan groups are quotients of finitely presented Kazhdan groups. That
   theorem is not verified in this graph.

5. **Rational detection is impossible.** The obstruction class lives in the
   `l`-torsion group `H^0_hat(C; A)`, which vanishes after tensoring with `Q`.
   So the rational envelope `V semidirect Q` of `(RC2)` cannot see clause 1,
   and clauses 1 and 2 are logically independent inputs.

6. **Soficity.** For free `P`, clause 2 holds with `W = QQ^n`, and `E` is
   sofic. For Kazhdan `P = F/S`, `V` is the quotient of `QQ^n` by the rational
   image of the relation module of `S`. Clause 2 asks that this quotient
   re-embed in an induced module.

   No criterion is known. The alternative, soficity of abelian-by-sofic groups
   in general, is open; see `radu-lattice-is-limit-of-nilpotent-by-arithmetic-groups`.
