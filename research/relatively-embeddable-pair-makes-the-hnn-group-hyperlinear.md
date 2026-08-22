---
rg: 2
id: relatively-embeddable-pair-makes-the-hnn-group-hyperlinear
kind: claim
title: If the subgroup factor sits relatively embeddably in the host factor, the HNN group centralising the subgroup is hyperlinear
distinct_from:
  amenable-edge-hnn-preserves-hyperlinearity: that is permanence for AMENABLE associated subgroups through Brown--Dykema--Jung; this is permanence under Gao's relative-embeddability hypothesis on the inclusion of group factors, which makes no amenability assumption on the subgroup and is exactly what a microstate sequence of the host must violate for the HNN lane to survive.
  hnn-hyperlinearity-is-amalgamated-free-haar-unitary: that characterises hyperlinearity of the HNN group by an amalgamated-free Haar unitary in some model; this gives a concrete sufficient condition on the host's microstates, subgroup-faithfulness, that produces such a unitary through Gao's amalgamated-free-product theorem.
---

Let `C <= A` be countable groups, `B = L(C) subset N = L(A)`, and
`G = <A, t | [t, C] = 1> = A *_C (C x Z)`.  Recall Gao's notion
(arXiv:2012.07940, Definition 1.1): `B subset N` is **relatively
embeddable with respect to `N_1`** (`RE/N_1`) if there are a free
ultrafilter, QWEP finite von Neumann algebras `A_k` with hyperfinite
subalgebras `B_k subset A_k`, and a trace-preserving embedding
`pi : N -> prod_omega A_k (x) N_1` with `pi(B) subset prod_omega B_k (x) N_1`
forming a commuting square, i.e. `E_(prod B_k (x) N_1) o pi = pi o E_B`.

**Theorem.**  Put `D^+ = (A x Z) *_C A`, the amalgam of `A x Z` and `A`
over `C`.  Then:

1. `L(C) subset L(A)` is `RE/C` iff `D^+` is hyperlinear (Gao,
   arXiv:2012.07940, Appendix Theorem 7.1 with `N_1 = C`: `N subset M` is
   `RE/N_1` iff `(M (x) L^infinity(S^1)) *_N M` embeds in `(R (x) N_1)^omega`;
   here `L^infinity(S^1) = L(Z)` and the group amalgam's factor is the
   tracial amalgamated free product).
2. `G` embeds in `D^+` (send `A` to the second copy and `t` to the
   generator of `Z`, which centralises the first copy hence `C`), so
   `D^+` hyperlinear implies `G` hyperlinear.
3. If `L(C) subset L(A)` is `RE/N_1` for some Connes-embeddable `N_1`, then
   `G` is hyperlinear (also directly: Gao's Theorem 1.1 plus a Folner
   construction for the shift, see the proof route).  Consequently, by
   `hnn-hyperlinearity-is-amalgamated-free-haar-unitary`, some regular-trace
   matrix model of `L(A)` carries a Haar unitary in `L(C)'` free from
   `L(A)` with amalgamation over `L(C)`.

Since `RE/C` implies `RE/N_1` for every `N_1` (tensor with `1_(N_1)`), the
chain of targets for a pair is

```text
G non-hyperlinear  =>  not RE/N_1 for every CE N_1  =>  not RE/C  <=>  D^+ non-hyperlinear,
```

and `D^+ = (A x Z) *_C A` is itself an explicit finitely presented witness
whenever `A` and `C` are finitely presented.  So the host-only statement
"`L(C) subset L(A)` is not `RE/C`" is a STRICTLY WEAKER goal target than
non-hyperlinearity of the HNN group, and it closes the goal through
`non-hyperlinear-from-non-relative-embeddability`.

**Microstate form (`N_1 = C`, `A_k = M_(d_k)`).**  Call a regular-trace
microstate sequence `pi_k : A -> U(d_k)` **`C`-faithful** if there are
subalgebras `B_k subset M_(d_k)` with

```text
dist_2(pi_k(c), B_k) -> 0   (c in C),
||E_(B_k)(pi_k(a))||_2 -> 0   (a in A - C);                    (CF1)
```

in particular it suffices that `||E_(W^*(pi_k(C)))(pi_k(a))||_2 -> 0` for
every `a notin C`.  A `C`-faithful sequence makes `L(C) subset L(A)` `RE/C`,
hence makes `G` hyperlinear.  Congruence microstates are maximally
unfaithful: there `pi_k(a) in W^*(pi_k(C))` for every `a in A` by
co-density, so `E(pi_k(a)) = pi_k(a)` has norm one.  Any `C`-faithful
sequence is therefore exotic, and its existence would close the HNN lane
for the pair negatively without constructing the stable letter by hand.

**Position.**  This is the cheapest known way to kill the HNN lane for a
pair: relative embeddability is a property of the host's microstates
alone.  Conversely the lane, through its weakest holes
`sl2-hnn-admits-no-amalgamated-free-haar-unitary` and
`sl3-hnn-admits-no-amalgamated-free-haar-unitary`, asserts that the
arithmetic pairs are NOT relatively embeddable
(`arithmetic-pair-is-not-relatively-embeddable`).  Gao's Theorem 1.2
supplies relative embeddability for normal pairs with amenable quotient
or hyperlinear quotient; the arithmetic pairs are neither normal nor of
that shape, which is exactly why the lane is open.
