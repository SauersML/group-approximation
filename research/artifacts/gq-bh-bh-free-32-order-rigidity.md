# bh-free-32 notes: order rigidity of PL groups (2026-09-18)

## The strategy tried

A proof of Boone--Higman must, in particular, produce finitely presented simple groups with word
problems beyond every recursive bound (`fp-simple-groups-with-arbitrarily-complex-word-problem`).
Every classical Thompson-like host shares one bound (`complexity-bounded-host-classes-are-not-universal`),
because its combinatorics is rational. The lane's own idea was to keep the combinatorics of a
Thompson-like group and hide the hardness in **one real parameter**.

Take PL maps whose slopes or breakpoints involve a computable real `λ` whose digits are hard to
compute. If such a group contains Thompson's `F` on a dyadic interval and a bump with support
endpoint `e(λ)`, then deciding whether the commutator `[u, k_r]` of `u` with an `F`-bump on
`(r, 1)` is trivial is exactly deciding `e(λ) < r`. So the word problem is at least as hard as
the digits of `e(λ)`. Commutator-closure tricks, such as Higman's or the Brin--Thompson
derivations, would then aim at simplicity.

## Why it dies

Finite presentation only sees finitely many order relations, and a transcendental parameter can
be moved without breaking them. Moving it breaks some other order relation.

- `fp-pl-groups-with-f-have-no-transcendental-support-endpoints` gives the general criterion for
  data in `Q(λ)`.
- `fp-bieri-strebel-line-groups-are-deformation-rigid` gives the line case via Bieri--Strebel's
  presentation, with a sharper conclusion: slopes algebraic and breakpoints in the slope field.

For algebraic data, exact arithmetic in a real number field decides the word problem, and the bit
sizes grow only linearly with word length. This is standard and not written out here. So **no PL
mechanism of this kind can beat the known bounds**.

## What survives

- **Hardness in the combinatorics, not the numbers.** The known live routes are Attempts 1, 2 and 5
  of the root.
- **Non-PL families** (piecewise projective, piecewise smooth, germs) with hard parameters. The
  deformation argument needs only that relators are decided by finitely many strict inequalities
  among functions that are analytic in the parameter. So it should extend to
  piecewise-`PSL_2(Q(λ))` groups containing `F` or Lodha--Moore-type subgroups. This is not
  written out.
- **Transcendental slopes with algebraic endpoints** outside the line case, i.e. no dyadic `F`
  and no element as in (E). This case is unclear.

## Source and search log

- Bieri--Strebel, arXiv:1411.2868v3, read at source: the preface (pp. i--viii), D13.1--D13.7 and
  13.3c (book pp. 73--84), N3 (Notes). N3.3b: finite presentation of `G(R;A,P)` has only
  necessary conditions (D13.3) and far more demanding sufficient ones (D13.7).
- Web search (2026-09-18) for transcendental- and irrational-slope finite presentability found:
  Cleary's `F_τ`; Burillo--Nucinkis--Reeves (`F_τ`, `T_τ`, `V_τ`); Winstone's 2022 Royal Holloway
  thesis (quadratic slopes, tree pairs); Molyneux--Nucinkis--Santos Rego (Σ-invariants of `F_τ`;
  arXiv:2309.12213, 2602.08748); Gonçalves--Sankaran--Strebel (arXiv:1511.07088). None states a
  deformation or rigidity obstruction. The search was bounded, so no priority is claimed.

## Update 2 (2026-09-18, after the coordinator's follow-up)

**Prior-art check for `G(R; Z[1/2] + Z[1/2]τ, gp(2))`.** The full monograph text
(arXiv:1411.2868v3, via pdftotext) was grepped for irrational, transcendental and `√` examples.
- Every finitely presented example there has `A = Z[P]`: examples 13.3c.1 and 13.3c.2, and N3.3b.
- The irrational examples have `A ⊆ Q(P)`: Cleary's `A = Z[u^{±1}]` with `P = gp(u)`, and the
  `ω = √2 + 1` example of N3.
- The only non-finitely-presented examples named fail D13.3 itself, e.g.
  `G(R; Z[1/6], gp(3/2))` in the preface.
- N3.3b says only necessary and far more demanding sufficient conditions are known. N3.4 says that
  for compact intervals the known necessary conditions for finite generation and for finite
  presentation coincide.
- Cleary, Burillo--Nucinkis--Reeves and Winstone use `A = Z[τ]`, `P = gp(τ)` (so `A ⊆ Q(P)`).
- Related but different: Golan--Sapir (arXiv:1605.05387) show that stabilizers in `F` of finite
  sets containing an irrational are not finitely generated. Those are subgroups of `F` with dyadic
  data.

No appearance of the example was found. D13.5(ii) of the monograph shows that `G/[B,B]` is finitely
presented for it, while `G` is not.

**Generalization.** Two claims generalize this.
- `fp-piecewise-projective-groups-rigidity-criterion` gives a non-finite-presentation test for
  piecewise projective groups (any data field, the line and the circle, Lodha--Moore-type rigid
  subgroups).
- `definable-parameter-hosts-cap-simple-subgroups-at-pspace` gives the general collapse. The proof
  is definable choice (Tarski transfer; Büchi's lasso theorem) instead of deformation. It covers
  semialgebraic actions in any dimension and ω-automatic actions on Cantor space with arbitrary
  addresses, which is the germ-group case the coordinator asked about.

The dictionary is:

| real (Tarski) | Cantor (Büchi) |
|---|---|
| algebraic point | ultimately periodic address |
| `R_alg ≺ R` | nonempty ω-regular sets contain lassos |
| Zariski-generic point | normal (finite-state random) address |
| existential theory of the reals in PSPACE | Büchi nonemptiness on the fly in linear space |

**Lesson.** What finite presentation can see of a host is a first-order condition. Hosts whose
generators are tamely definable therefore collapse to tame members, and all of them are capped at
PSPACE. A Birget or BH host must put the input's algorithm into generators that are not definable
in a decidable tame structure.
