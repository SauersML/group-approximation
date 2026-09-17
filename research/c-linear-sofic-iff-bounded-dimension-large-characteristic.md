---
rg: 2
id: c-linear-sofic-iff-bounded-dimension-large-characteristic
kind: claim
title: A group is complex-linear sofic iff each window has models of one fixed dimension in infinitely many characteristics, tame models lift to C, and no Sylvester-rank certificate separates large characteristic
distinct_from:
  root-splits-into-large-and-fixed-characteristic-witnesses: that splits the root by characteristic; this characterizes the gap between large-characteristic and complex rank models, and names what a proof of the large-characteristic component must control.
  linear-sofic-group-algebra-is-stably-finite: that derives stable finiteness from linear soficity; this shows that in characteristic zero every group algebra carries a separating Sylvester rank function, so that passage can never certify the large-characteristic component.
  non-linear-sofic-group: that is the open root of failure over one field; this is a structure theorem comparing models across characteristics and establishes no failure.
---

**ESTABLISHED (2026-09-17, lane `sw-024`, unreviewed)** by `c-linear-sofic-iff-bounded-dimension-large-characteristic-proof`.

Groups are countable. Models, windows `(W, eps)`, `L_inf` and `S(G)` are as on
`root-splits-into-large-and-fixed-characteristic-witnesses`; separation is `1/4`. Let `m_(W,eps)(l)` be the least
dimension of a `(W, eps)`-model over a finite field of characteristic `l`, or `infinity` if there is none.

**Theorem.**
1. **Dimension gate.** The following are equivalent:
   - (i) `G` is `C`-linear sofic;
   - (ii) for every window there is `n` such that `m_(W,eps)(l) <= n` for infinitely many primes `l`;
   - (iii) for every window there is `n` such that `m_(W,eps)(l) <= n` for all sufficiently large `l`.

   Consequences:
   - `C`-linear soficity implies `L_inf`.
   - `G` lies in `L_inf` but is not `C`-linear sofic iff `G` is in `L_inf` and some window has
     `m_(W,eps)(l) -> infinity` as `l -> infinity`.
2. **Tame lifting.** Let `phi : W -> GL_n(F_q)`, with `q` a power of `p`, and suppose the finite group
   `Q = <phi(W)>` has order prime to `p`. Then there is a representation `psi : Q -> GL_n(C)` with
   `rank(psi(x) - 1) = rank(x - 1)` for every `x` in `Q`.
   - So `psi o phi` is a complex model with exactly the same defects and separations.
   - If `G` is not `C`-linear sofic, some window has only wild models, in every characteristic: the characteristic
     divides `|<phi(W)>|`.
   - A group with tame models for every window in some characteristic is `C`-linear sofic.
3. **No Sylvester certificate in large characteristic.** Large-characteristic models of `H` induce a Sylvester matrix
   rank function on `K[H]` for a field `K` of characteristic zero with `|K| <= 2^aleph_0`, with `rk(g - 1) >= 1/4`.
   - For every group `H` and every such `K`, the von Neumann rank on the affiliated algebra `U(H)` restricts to a
     Sylvester matrix rank function on `K[H]` with `rk(g - 1) = 1 - 1/|<g>| >= 1/2` for `g != 1`. Here `K` embeds
     in `C`.
   - So no argument that refutes the existence of such a rank function, including every stable-finiteness argument
     (Kaplansky), can show that `H` is not in `L_inf`.

**Payoff.** Component (a) of the characteristic split (`non-large-characteristic-linear-sofic-group-exists`) cannot be
proved algebraically. For a group that is not `C`-linear sofic, it is exactly the statement that the wild minimal
model dimensions on some window become infinite rather than merely unbounded.

**Calibration.**
- *Sofic groups.* Permutation models give (iii) with the dimension independent of `l`.
- *Cyclic groups in their own characteristic.* The regular representation of `Z/p` over `F_p` is wild and
  non-semisimple. It still has a complex model, so wildness alone never certifies anything.
- *Item 3 on finite groups.* It gives `rk(g - 1) = 1 - 1/ord(g)`, which is the rank of the regular representation.

**Credit.** The Nullstellensatz and Chevalley spreading-out, Brauer lifting through idempotents over Witt vectors, and
the von Neumann rank are classical. Item 1 refines Arzhantseva--Paunescu's passage from `C` to large finite fields
into an equivalence. The novelty check was bounded, and experts may know the statement.
