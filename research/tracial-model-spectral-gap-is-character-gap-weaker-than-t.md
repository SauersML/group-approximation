---
rg: 2
id: tracial-model-spectral-gap-is-character-gap-weaker-than-t
kind: claim
title: The tracial rung of the Kesten model spectral gap is a uniform character spectral gap, strictly weaker than property (T) and dependent on the ambient group
distinct_from:
  model-spectral-gap-quantifier-ladder: that decides rung 0 (all unitary representations, equivalent to (T) for L and independent of G) and rung 1 (MF targets, equivalent to the endpoint), and leaves the finite von Neumann rung undecided; this decides that rung, showing it is a uniform spectral gap over GNS representations of characters of G, that it holds for non-Kazhdan L (Thompson V, and F_2 inside V), and that at this rung the ambient group changes the answer.
  kesten-spectral-gap-replaces-kazhdan-projection-per-model: that isolates (MSG) as the only Kazhdan input of the transport and shows the tau-null positive element in delta_e adjoint coronas; this uses that element only to record that the tracial rung is blind to the eigenprojection the transport consumes.
  thompson-v-character-simplex: that imports the Dudko--Medynets classification of characters of V; this consumes it to decide a spectral-gap rung.
artifacts:
  - research/tracial-model-spectral-gap-is-character-gap-weaker-than-t-proof.md
---

**ESTABLISHED (written proof; not Lean-verified).**  This decides the
finite von Neumann rung that `model-spectral-gap-quantifier-ladder` left
undecided.  Notation is that of that node: `G` countable, `L<=G`
finitely generated, `S` a finite symmetric generating set of `L` with
`e in S`, and `h_S=(1/|S|) sum_(s in S) u_s`.  A **character** of `G` is
a normalized positive definite function constant on conjugacy classes.
Write `pi_phi` for its GNS representation.

Say `(G,L)` has the **tracial model spectral gap** `(TMSG)` if every
homomorphism `rho:G->U(M)` into a finite von Neumann algebra `M`
satisfies `(MSG)` on `L`, i.e. `1` is not an accumulation point of
`sp(rho(h_S))`.

1. **Character form.**  `(TMSG)` holds if and only if there is `c>0` with

   ```text
   sp(pi_phi(h_S)) cap (1-c,1) = empty      for every character phi of G.   (CG)
   ```

2. **Strictly weaker than (T), with no Kazhdan subgroup at all.**  Let
   `V` be Thompson's group.  Then `(V,V)` satisfies `(TMSG)` and so does
   `(V,F)` for a free subgroup `F=<a,b>` of rank two in `V`, which exists.
   In both cases `c=1-||lambda_L(h_S)||>0`.  Every subgroup of `V` with
   property `(T)` is finite, so neither `V` nor `F` has `(T)`.
3. **The ambient group matters at this rung.**  The pair `(F_2,F_2)` fails
   `(TMSG)`: finite cyclic quotients give eigenvalues
   `(3+2cos(2 pi/n))/5` converging to `1` inside the finite von Neumann
   algebra `prod_n M_n`.  So the same `L=F_2` has the tracial gap inside
   `G=V` and not inside `G=F_2`.  At rung 0 the answer depends only on
   `L`.  At the tracial rung ambient character rigidity decides it.
4. **Blindness at the endpoint.**  Let `(V_n)` be a `delta_e`-profile
   operator-norm model of `G` with adjoint corona homomorphism
   `sigma~:G->U(B)`, let `tau` be a limit trace on `B`, and let `L` be
   nonamenable.  Then

   ```text
   sp(pi_tau(sigma~(h_S))) subset [-1, ||lambda_L(h_S)||],
   ```

   so `pi_tau o sigma~` satisfies `(MSG)` on `L` with no work.  Moreover,
   whenever `(MSG)` holds for `sigma~` on `L`, the substitute projection
   `P=chi_{1}(sigma~(h_S))` has `tau(P)=0`, i.e. `pi_tau(P)=0`.  So an
   argument carried out in the tracial von Neumann completion sees the
   eigenprojection the transport theorem consumes as zero.

## Consequence for the Property-(T)-free program

The ladder of `model-spectral-gap-quantifier-ladder` now reads:
- rung 0, all representations: equivalent to `(T)` for `L` and blind to `G`;
- tracial rung: a uniform character gap, provable T-free for character-rigid
  ambient groups (item 2), and depending on `G` (item 3);
- MF rung: equivalent to the endpoint.

Item 3 answers the question the ladder left open about removing `(T)`:
ambient data can replace `(T)`, but only through characters, i.e. through
the trace.  Item 4 shows the trace sees exactly `lambda_G` on every
`delta_e` model, where the gap is automatic.  So all remaining content of
`(MSG)` for the goal sits on tau-null spectrum.

A T-free proof for `Delta=St_20(L_(F_2)(1,2))` therefore has to control
tau-null spectrum of one Markov element in the norm corona.
Character-level information cannot supply it: not character rigidity of
`Delta`, which is unknown, and not Thompson `V<=Delta`.  The next
undecided rung is stably finite C-star targets.  Coronas are such targets,
so the MF rung sits below that rung.

Proof route: `tracial-model-spectral-gap-is-character-gap-weaker-than-t-proof`.
