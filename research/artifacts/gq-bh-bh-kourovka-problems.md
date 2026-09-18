# Kourovka Notebook problems near Boone–Higman (lane bh-kourovka, 2026-09-18)

**Source.** Kourovka Notebook, 21st issue (Lincoln–Novosibirsk, January 2026),
arXiv:1401.0300. It was fetched as an e-print through MSI; the TeX is
`gq/src/kourovka/21tkt.tex` in the swarm scratchpad.

The main part (unsolved problems) runs to TeX line ~14580, and the Archive of Solved
Problems follows. Every problem below is in the main part, i.e. unsolved as of 2026,
unless it is marked "archive". Wording is paraphrased; numbers are exact.

## New results from this lane (lane proofs, not reviewed)

| No. | Problem (paraphrase) | Result | Node |
|---|---|---|---|
| 17.61 (Kohl) | Is CT_P(Z) finitely presented for finite P? | **Yes.** CT_P(Z) = [[G_Λ]] for an explicit one-vertex (\|P\|+1)-graph Λ; it is simple and of type F_∞. | `ct-p-z-is-a-one-vertex-k-graph-full-group` |
| 17.59 (Kohl) | Is CT(Z) the group of all RCWA permutations of Z fixing N_0 setwise? | **Yes.** | `ct-z-is-the-rcwa-group-fixing-the-nonnegative-integers` |
| 17.60 (Kohl) | Are the CT_P(Z) pairwise non-isomorphic? | **Partial.** CT_P ≅ CT_Q implies \|P\| = \|Q\| (isotropy rank via Matui's spatial isomorphism theorem). Sets of equal size are OPEN; a sketched invariant is on the node. | `ct-p-z-isomorphism-type-remembers-the-number-of-primes` |

**The mechanism.** Residue classes with P'-smooth moduli are the cylinders of a
one-vertex k-graph whose infinite-path space is the profinite completion
Ẑ = ∏_{p∈P'} Z_p. A class transposition is a canonical "box swap" bisection.

**Cited inputs, all read at source:**
- Li arXiv:2110.04505v2 Cor. `cor:OneVertex` (F_∞);
- Li arXiv:2209.08087v2 Cor. `cor:AHConj` (Matui's AH conjecture for minimal groupoids
  with comparison, including purely infinite ones);
- Farsi–Kumjian–Pask–Sims arXiv:1808.07807 Thm. `thm:H computation` (the homology of a
  one-vertex k-graph groupoid vanishes when gcd(|Λ^{e_i}| − 1) = 1; here a colour with
  2 edges gives gcd 1);
- Matui arXiv:1210.5800 Thm. `simple2` and Thm. `iso2`.

Not re-read: standard k-graph groupoid facts (Kumjian–Pask), and Li's identification
of the boundary groupoid with the k-graph groupoid [Li21a].

## Problems at the interface with Boone–Higman and embeddings into simple groups

| No. | Proposer | Paraphrase | Status on main / notes |
|---|---|---|---|
| 20.7 | J. Belk (after Boone–Higman) | Does every f.g. group with solvable WP embed in a f.p. simple group? | Root `boone-higman-conjecture` (OPEN); the whole BH swarm. |
| 14.10 c) | P. de la Harpe | Find an explicit "natural" f.p. group containing GL_n(Q). | The gq swarm's `gl-n-q-explicit-natural-fp-overgroup` (St_10(R_L)); naturalness is a matter of taste. Parts a), b) are in the archive (a: Belk–Hyde–Matucci 2022; b: Mikaelian 2005). |
| 5.16 | Cannonito, Miller | Does every countable locally linear group embed in a f.p. group? | Not on main. Observations: all countable locally finite groups embed (Hall's universal group is computable); no computability obstruction is visible. OPEN. |
| 7.19 | Cannonito | Explicit f.p. simple group whose WP is not primitive recursive. | Not on main. Any BH host of an explicit f.g. group with solvable non-p.r. WP answers it. Every BH class currently on main (linear, hyperbolic, automatic, metabelian, contracting self-similar) has p.r. WP, which is presumably why this stays open. Unowned. |
| 21.45 | Fournier-Facio | F.p. infinite simple group needing more than two generators? | Well-known, OPEN. Unowned. |
| 21.46 | Fournier-Facio | F.p. infinite simple group of finite cohomological dimension > 2? | Well-known, OPEN. Burger–Mozes gives cd 2; candidates would be simple torsion-free lattices in products of ≥ 3 trees. Unowned. |
| 20.33 | Grochow (after A. Bauer) | Relativized Higman embedding for X-computable presentations. | Computability; suggested for bh-logic. |
| 17.57 | Kohl | Is Out(CT(Z)) = ⟨n ↦ −n−1⟩ ≅ C_2? | New angle: CT(Z) = ⋃ CT_P(Z) with CT_P = [[G_{Λ_P}]], and Matui/Rubin make automorphisms of each CT_P spatial. Unowned. |
| 17.58 | Kohl | Does CT(Z) have subgroups of intermediate growth? | Unowned; CT(Z) ⊇ V. |
| 21.73, 21.74 | Kohl | Decidability of conjugacy in CT(Z), and of properties of elements. | CT_P = [[G_{Λ_P}]] brings Garside and groupoid tools (Li). Unowned. |
| 15.19 | Grigorchuk et al. | Finite-state (automaton) realizability questions for residually-p groups with solvable WP; e.g. is Z ≀ (Z ≀ Z) in F_2? | Related to bh-self-similar. |
| 10.39 b) | Noskov | Is the WP solvable for the Quillen groups K_i(R), R commutative? | Related to the gq K_2 word-problem work (`st-n-leavitt-resolvent-word-problem-reduces-to-k2`, noncommutative R_L). |
| 17.61, 17.59, 17.60 | Kohl | see the table above | this lane |

## Attempts that did not reach a node

- **7.19.** The most natural creative route is a Li Zappa–Szép full group
  (arXiv:2110.04505 Cor. `intro:ZS`). Its F_n conclusion needs the invertible part
  D^*(w,w) to be F_n.
  - If an F_∞ group with solvable but not primitive-recursive WP acted self-similarly
    on a finite k-graph with finite restriction data, the full group would be F_∞ and
    would contain it.
  - But simplicity of the derived subgroup needs an effective groupoid, and faithful
    self-similar actions with finite data are automaton-like, giving exponential-time
    WP.
  - So the obstruction is the tension between "finite data" and "hard WP". Recorded
    for whoever takes 7.19.
