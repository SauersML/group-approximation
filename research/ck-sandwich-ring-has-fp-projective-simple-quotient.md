---
rg: 2
id: ck-sandwich-ring-has-fp-projective-simple-quotient
kind: claim
title: The Chatterji--Kassabov sandwich ring has a finitely generated ideal whose rank-four projective elementary quotient is finitely presented and simple
distinct_from:
  ck-envelope-has-a-finitely-normally-generated-maximal-kernel: that asks for any finitely normally generated maximal kernel of the Steinberg cover; this is the congruence-regime form R4 of ck-maximal-kernel-four-regimes, stated purely about ideals of the fixed ring U. It implies that hole, and is equivalent to it under the three normal-structure killers.
  decidable-group-ring-has-fp-projective-simple-host: that allows an arbitrary overring L of Z[H]; this requires a QUOTIENT U/I of the specific sandwich ring, in which only the simple core is guaranteed to survive (in the units), not the group ring.
  simple-inputs-have-fp-elementary-leavitt-tensor-hosts: that asks for a central simple F_2-algebra B with S in its units and a Leavitt tensor; this fixes the ambient ring U and asks for one of its simple quotients, in any characteristic, with no Leavitt factor.
  relative-elementary-fng-iff-level-ideal-fg: that is a finiteness equivalence for relative elementary subgroups; this is an existence question for an ideal.
---

**OPEN.** Let `H` and `T` be finitely presented with `H <= [T,T]`, let
`1 != g in H`, and put `U = Z[T]<p,q>/(p(1-g)q-1)`. The claim is that for
some such choice, with `H` containing the computably presented simple core
`S` as in [[boone-higman-via-ck-maximal-kernel]], there is a finitely
generated two-sided ideal `I != U` such that `PE_4(U/I)` is finitely presented
and simple.

By [[ck-maximal-kernel-four-regimes]], this is equivalent to: some finitely
generated ideal `I` of `U` satisfies all three of the following.

- **(a) Simplicity.** `PE_4(U/I)` is simple. This forces `U/I` to be a simple
  ring ([[projective-elementary-simplicity-forces-simple-ring]]). The core `S`
  then sits in `(U/I)^x` by [[ck-envelope-level-ideal-screen]].
- **(b) Steinberg kernel.** `ker(St_4(U/I) -> E_4(U/I))` is finitely normally
  generated in `St_4(U/I)`.
- **(c) Centre.** `Z(E_4(U/I))` is finitely generated.

No clause is known to follow from the other two:

- (a) is a normal-structure statement;
- (b) is an unstable `K_2` finiteness statement, and by
  [[projective-elementary-fp-kernel-criterion]] it is not supplied by finite
  presentation of the ring;
- (c) concerns the central units, since the centre is `E_4 ∩ {d I_4 : d in Z(U/I)^x}`.

**What it would give.** A finitely presented simple group `PE_4(U/I)`
containing `S`, through [[ck-maximal-kernel-four-regimes]] Step 3. This proves
[[ck-envelope-has-a-finitely-normally-generated-maximal-kernel]] and hence
Boone--Higman along [[boone-higman-via-ck-maximal-kernel]].

**The necessary ring content.** Any witness contains a finitely presented
simple ring `R = U/I`, which is a `Q`-algebra or an `F_p`-algebra, has `S`
in its units, and has `p(1-g)q = 1`. So the claim contains a unit-group form
of the algebra Boone--Higman problem for `S`. The unit group is required
only up to a homomorphism from `T` that is injective on `S`.

## Attempts

1. **Take `I` maximal among ideals missing `S - 1`.** This dies at finite
   generation of `I`, the ring analogue of Attempt 1 of the hole. By Step 3 of
   [[ck-maximal-kernel-four-regimes-proof]], finite generation of `I` is
   forced by, and not weaker than, finite normal generation of the maximal
   kernel in this regime. The reformulation moves no finiteness for free.
2. **Any marking at all.** *Dies for poisoned markings (bus report from c-ckmax,
   swarm-0917, `poisoned-ck-envelopes-have-no-fng-maximal-kernel`).* Suppose `H`
   contains `S` amalgamated along `s` with an inseparable-set Heisenberg shift
   group, whose poisoned central element is `s`. According to that report,
   every nontrivial quotient of the envelope then has unsolvable word problem.
   `PE_4(U/I)` is such a quotient, through the R4 kernel of
   [[ck-maximal-kernel-four-regimes]]. But a finitely presented simple group
   has solvable word problem, which is a contradiction.
   The claim is therefore existential in the marking in an essential way. A
   witness must use a clean marking, for example `H` with solvable word problem
   relative to `S`.
3. **Biography of a witness, turned into a recipe (swarm-0917, inverter).**
   *Reduces the hole to a ring-host premise. The hole stays OPEN.*

   **What any witness must have.** A witness `R = U/I` is a finitely presented
   simple ring. It has `S -> R^x` injective, `p(1-g)q = 1` for one `g in S`, and
   `PE_4(R)` finitely presented and simple. Here `PE_4(R)` already contains `S`.

   **The recipe.** The marking data of the route can be taken from the host
   itself. By [[square-module-ring-hosts-are-sandwich-ring-quotients]], any
   finitely presented ring `R` with the following three properties is a
   witness:
   - `R_R ≅ R_R^2`;
   - `S <= R^x`, with `S` perfect;
   - `PE_4(R)` is finitely presented and simple.

   Take `T = H = E_4(R)` and `g = e_12(1)`. Then `U ->> M_4(R) ≅ R` with a
   finitely generated kernel. Leavitt tensor hosts `B ⊗ L_(F_2)(1,2)` have all
   three properties, so route [[ck-sandwich-quotient-via-elementary-leavitt-hosts]]
   derives this hole from
   [[simple-inputs-have-fp-elementary-leavitt-tensor-hosts]].

   **Where it stops.** The recipe does not give equivalence. The necessary side
   does not force `R ≅ R^2`. A directly finite witness is not excluded: there,
   `p(1-g)q = 1` only makes `1-g` a unit. The open step is to pass from a
   witness ring to a square-module ring without losing finite presentation of
   `PE_4`. Tensoring with `L_2` changes the Steinberg kernel, so it does not
   work. This is posted as a live need.

   **Consequence.** The sandwich ring `U`, and the Clapham and derived-subgroup
   data, impose no obstruction of their own in the congruence regime. An attack
   on this hole through features of `U` is an attack on the ring-host problem.
4. **Weaken the host condition from square-module to "not directly finite"
   (swarm-0917, c-pz1, reframer).** *Narrows the Attempt 3 gap. The hole stays
   OPEN.*

   **The realisation lemma.** By
   [[non-directly-finite-ring-hosts-are-sandwich-ring-quotients]], a finitely
   presented ring `R` is a witness when it has the following properties:
   - `R_R^4` is a direct summand of `R_R`, which holds for every simple ring that
     is not directly finite;
   - `PE_4(R)` is finitely presented and simple;
   - `S <= R^x`, with `S` perfect.

   **The construction.** Take `T = H = E_4(R)` and `g = e_12(1)`.
   - The corner `M_4(R) ≅ eRe`, with `u |-> φ(u) + (1-e)`, embeds `GL_4(R)` in
     `R^x`.
   - `p = -y_1` and `q = x_2` satisfy the relation.
   - `U` maps onto `R` itself, with a finitely generated kernel.

   **The dichotomy.** The hole holds iff there is either
   - a host that is not directly finite, or
   - a directly finite witness. In such a witness `p`, `q` and `1-g` are all
     units.

   **What remains.** The remaining gap is directly finite witnesses only. A
   directly finite host realises the hole only at rank sixteen: take `g` with
   `1-g` a unit, so `U ->> M_4(R)` and the quotient group is `PE_16(R)`.

   **Dead end on the way: kill characteristic 0 through `K_1`.** The
   square-module centre kill of
   [[square-module-elementary-centre-is-central-units]] uses `c^(d-1) I_n in E_n`
   for `R ≅ R^d`. It does not extend to hosts that are not directly finite
   when `[1_R]` has infinite order in `K_0(R)`, because then `K_1` detects
   scalars. So the non-directly-finite branch is not confined to finite centre
   fields by that argument.
