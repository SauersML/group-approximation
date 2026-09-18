---
rg: 2
id: three-v-contains-aperiodic-rationals
kind: claim
title: The Brin-Thompson group 3V contains a copy of Q none of whose nontrivial elements has a periodic point
distinct_from:
  rationals-embed-in-brin-thompson-group-2v: that copy of Q in 2V contains t x id, which has hyperbolic fixed points; this copy lives in 3V over a periodic-point-free base, so the periodic-exponent obstruction is vacuous on it.
  nv-rational-subgroups-with-power-conjugacy-are-flat: that says which copies of Q could carry the translations of an embedded Aff(Q); this supplies one that passes that test.
  brin-thompson-mv-contains-a-distortion-element: that imports a distortion element of mV built from the SMART machine; this uses the same machine only for its lack of periodic points.
  bs12-embeds-in-brin-thompson-2v: that asks for an element of nV conjugate to its square; this does not provide one.
---

**ESTABLISHED** through `three-v-contains-aperiodic-rationals-proof`. Lane proof,
not independently reviewed. It rests on the cited aperiodicity and minimality of the
SMART machine and on the landed root-tower construction. No priority claimed.

**Statement.**
1. **An aperiodic element of 2V.** Let `S` be the SMART machine of Cassaigne,
   Ollinger and Torres-Avilés: 4 states, 3 tape letters, reversible. Its moving-tape
   homeomorphism of `Σ^Z × Q_S` is conjugate, through complete prefix codes, to an
   element `T ∈ 2V`. `T` has infinite order and no periodic point.
2. **Aperiodic rationals.** In `3V`, acting on `C^2 × C`, the root tower of
   `T × id` built as in `rationals-embed-in-brin-thompson-group-2v-proof` (base in the
   first two coordinates, mixed-radix counter in the third) is a subgroup
   `Q_T ≅ (Q,+)`. No element of `Q_T \ {1}` has a periodic point.
3. **Consequences.** Every element of `Q_T \ {1}` is vacuously exponent-flat, and has
   empty periodic set and aperiodic core `C^3`. So items 1–3 of
   `bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets` and all of
   `nv-rational-subgroups-with-power-conjugacy-are-flat` impose nothing on `Q_T`.
   `Q_T` is the first copy of `Q` on main that could, as far as those tests go, be the
   translation subgroup of an `Aff(Q) <= 3V` or the root subgroup of an
   `SL_2(Q) <= 3V`.

**Source for item 1.** Callard–Salo, arXiv:2208.00685v3, §1, verbatim: "the SMART
machine 𝒮 by Cassaigne, Ollinger and Torres-Avilés, a machine with only four states
and three tape-letters, which is reversible and aperiodic, and whose moving-tape
dynamics is a minimal homeomorphism on the Cantor space". The original is
J. Cassaigne, N. Ollinger, R. Torres-Avilés, *A small minimal aperiodic reversible
Turing machine*, J. Comput. System Sci. 84 (2017) (HAL hal-00975244). Its statement
was not re-read at the source; the HAL and publisher pages refused access. Callard–Salo
§1.2 also state that "All groups of Turing machines in turn embed in the
higher-dimensional Brin-Thompson mV for m≥2". Item 1 is proved here by an explicit
conjugacy, so it does not depend on the form of their embedding.

**Open, and what it would give.** Whether some element of `Q_T \ {1}` is conjugate in
`3V` (or `nV`) to a proper power is open. That would answer
`bs12-embeds-in-brin-thompson-2v` for `n = 3`. It is the first necessary step towards
`aff-q-embeds-in-fp-simple-group` through an `nV` host. The next necessary test is
item 4 of `bs-kl-images-in-brin-thompson-groups-have-open-periodic-sets`:
`|δ_{g^N}| <= c (1 + log N)^2`. Here it amounts to a head-excursion bound for SMART
over `N/(k+1)!` steps. Also needed are the logarithmic table lengths of
`bs12-images-in-nv-have-logarithmic-table-length`. Callard–Salo's distortion bound
`O(log^4 N)` bounds both from above, but does not decide them.
