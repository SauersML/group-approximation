# Lin, arXiv:2510.07162v1: coRE orientation of the synchronous commuting-value problem (excerpt, 2026-09-17)

Source: Junqiao Lin, arXiv:2510.07162v1, PDF downloaded 2026-09-17 and text
extracted locally. The quotations below are verbatim up to PDF line breaks
and sub/superscript flattening. They are recorded for
`research/artifacts/fixed-decidable-host-corner-models-miss-a-separated-bcs-proof-2026-09-17.md`.

## Section 2.1 (complexity conventions)

> We write D1 <= D2 if there exists a mapping reduction from D1 to D2 ...

> coRE is complete with respect to the non-halting problem. The non-halting
> problem is defined similarly as the halting problem but with the "yes" and
> "no" instances being swapped, or L^coRE_yes = Lnothalt, L^coRE_no = Lhalt.

## Definition 6.2

> Definition 6.2 ((1, 1/2) non-local game value problem). For t in {*, co},
> the (1, 1/2) t non-local game value problem is a decision problem defined
> by the following two sets.
> - L^MIPt_yes = {<G> | omega_t(G) = 1}.
> - L^MIPt_no = {<G> | omega_t(G) <= 1/2}.

## Section 6.3 (synchronous CL class)

> For t in {*, co} and constant k in N, we define a synchronous k-th level CL
> samplable MIPt (k-CLMIPt) as the complexity class MIPt except restricted to
> synchronous games which are also k-th level CL samplable.
> - L^k-CLMIPt_yes = {<G> | omega_t(G) = 1, G is a synchronous k-th level CL
>   samplable game},
> - L^k-CLMIPt_no = {<G> | omega_t(G) <= 1/2, G is a synchronous k-th level CL
>   samplable game}.
>
> Showing that k-CLMIPco (resp. k-CLMIP*) being coRE-complete (resp.
> RE-complete) implies that coRE <= MIPco (resp. RE <= MIP*).

## Section 6.3.1

> By combining Corollary 6.6, Theorem 4.5 and the fact that
> L^k-CLMIPco_yes in coRE this shows that k-CLMIPco = coRE and hence
> coRE in MIPco. This, along with Lemma 6.8, shows the main theorem of this
> paper.
>
> Corollary 6.10. MIPco = coRE

Pseudocode 6 ("The description for V which can be used to show that
coRE <= k-CLMIPco. F is the instance of the halting problem for the
reduction.") begins:

> 1 Input: Integer n.
> 2 Run F for n steps. If F halts in the given steps, return G_reject.

## Reading used downstream

The reduction is a computable map `F |-> G_F` into finite synchronous games
with

```text
F does not halt  =>  omega_co(G_F) = 1,
F halts          =>  omega_co(G_F) <= 1/2.
```

Commuting-operator correlation sets are closed, so value one is attained by a
perfect commuting strategy. Status of the source: preprint, imported in the
repository on the same footing as `lin-explicit-synchronous-bell-gap-game`.
