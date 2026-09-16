# Boone--Higman conjecture: frontier swarm, 2026-09-16

Agent: `hi-fron-boone-higman-conjecture`. Angle: FRONTIER. Map the open holes under
`boone-higman-conjecture`, pick the one with the best leverage and tractability, and
attack it.

Hole worked: `a2-action-kernels-are-recursive`, locked with a 180 minute TTL.

## 1. External gate (checked 2026-09-16)

The conjecture is still open. No source found on 2026-09-16 settles it, and none
studies whether kernels of type `[A_2]` actions are recursive.

- arXiv search "Boone-Higman", newest first, fetched 2026-09-16. The newest hit is
  arXiv:2609.01868 (Almeida, Dantas, Oliveira-Tosti, v1 1 Sep 2026). It gives a new
  family of Boone--Higman groups, lamplighters `Z^d ≀_X G` over contracting
  self-similar `G`. Per its abstract it does not settle the conjecture and does not
  discuss non-faithful actions.
- Belk--Bleak--Matucci--Zaremsky, "Progress around the Boone-Higman Conjecture",
  arXiv:2306.16356 (v1 28 Jun 2023, v3 22 May 2025). The abstract reports the
  conjecture for many classes, not in general.
- Fournier-Facio--Wu--Zaremsky, "Abstract twisted Brin--Thompson groups",
  arXiv:2603.24687 (v1 25 Mar 2026, v2 2 Apr 2026). This is the source of type
  `[A_2]`, Question 5.8 and Question 5.9. The abstract was fetched verbatim on
  2026-09-16. The body was read earlier through an HTML rendering that returned a
  summary, so any statement here about their Definition 1.3 relies on the verbatim
  text already recorded in the graph (`a2-pairs-embed-in-a2-pairs-with-fng-kernels`).
- Zaremsky's arXiv author listing, fetched 2026-09-16. The newest items are
  arXiv:2608.25614 ("Word length, Morse theory, and Vietoris-Rips complexes") and
  arXiv:2605.20564 ("Action graphs, semiconjugacy, and non-embedding in Thompson's
  group V"). Only titles were read. Neither title is about kernels of actions.
- Other hits, abstract pages only:
  - arXiv:2309.06224 (hyperbolic groups);
  - arXiv:2503.21882 (Belk--Fournier-Facio--Hyde--Zaremsky, Aut(F_n) and MCGs);
  - arXiv:2408.05673 (Bux--Llosa Isenrich--Wu, trees);
  - arXiv:2405.18354 (Zaremsky, finite presentability of twisted Brin--Thompson
    groups);
  - arXiv:2405.10234 and arXiv:2405.09722 (self-similar groups);
  - arXiv:2306.14863 (Belk--Bleak);
  - arXiv:2506.02319 (Fournier-Facio--Kropholler--Lyman--Zaremsky, stabilisers of
    oligomorphic actions).

None of these asks whether the kernel of a type `[A_2]` action must be recursive. The
graph node `a2-action-kernels-are-recursive` already says FFWZ do not ask it.

## 2. Map of the subtree and choice of hole

`bin/cairn why a2-action-kernels-are-recursive` (2026-09-16) reports the chain
`permutational-boone-higman-conjecture -> a2-pairs-embed-in-a2-pairs-with-fng-kernels
-> a2-action-kernels-are-recursive`. The hole has no live route in. Its one dependent
is the route `a2-kernel-removal-via-pbh-and-recursive-kernels`.

Nearby holes looked at:
- `a2-pair-with-non-removable-kernel-exists`: the negation of the first part of FFWZ
  Question 5.9. Its only route goes through
  `fp-simple-group-with-nonrecursive-mixed-identities`, which is hard.
- `fp-simple-group-with-nonrecursive-mixed-identities`: needs an undecidability
  construction inside a finitely presented simple group. Low tractability.
- `permutational-boone-higman-conjecture` and the root itself are out of reach.

I chose `a2-action-kernels-are-recursive` for three reasons:
1. It is a clean computability question.
2. Both directions have leverage: a proof feeds a route into Question 5.9, and a
   counterexample settles `a2-pair-with-non-removable-kernel-exists` through
   `a2-kernel-removal-forces-recursive-kernel` (b).
3. The graph has no attempt on it beyond the mixed-identity reduction.

Lock: `CAIRN_AGENT=hi-fron-boone-higman-conjecture bin/cairn lock
a2-action-kernels-are-recursive --ttl 180m`.

## 3. What was proven

## 4. The HNN realization reduction

## 5. Approaches tried and where each dies

## 6. What to try next

## 7. Files
