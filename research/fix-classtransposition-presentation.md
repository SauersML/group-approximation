---
id: fix-classtransposition-presentation
kind: route
rg: 2
title: "Fix GroupApproximation.ClassTransposition.Presentation.{Statement,Basic,Presented,ShiftFC}: unprobed (Slurm blocked); Kourovka 17.61 reduced to two open claims"
target: class-transposition-relations-present-ct-p-z
status: OPEN
---

**Modules** (lane bh-pal-kourovka61). None of them is root-wired.
- `GroupApproximation/ClassTransposition/Presentation/Statement.lean`: verbatim v3 copies
  (`P : Set ℕ`) of `IsSmoothModulus`, `IsClassTranspositionOver` and `classTranspositionGroupOver`
  from `Palomar/BooneHigmanChallenge.lean`, and `kourovka1761Statement`, which is the challenge
  statement of `kourovka_17_61`.
- `.../Basic.lean`: swap identities. Squares (`swap_mul_self`), conjugation (`conj_swap`), and
  splitting into `k`-children (`swap_split`).
- `.../Presented.lean`:
  - `TranspGroup P`, the relations (R1)–(R3) plus symmetry as a `PresentedGroup`;
  - `eval P` onto the class transpositions;
  - `eval_range : (eval P).range = classTranspositionGroupOver P`;
  - `ctEquiv`, the isomorphism given injectivity;
  - `kourovka1761Statement_of`.

**Status.** Unprobed. Every sbatch has failed since 09-18 ~20:55 (`$GQ/state/SLURM-BLOCKED`), and
local builds are forbidden. The files are written against Mathlib pin 81a5d257 and the Lean
4.32 core lemma names, checked by reading the sources. There is no first error yet.

**What `kourovka_17_61` still needs** (via `kourovka1761Statement_of`), for every finite set `P`
of odd primes:
1. `Function.Injective (eval P)`, i.e. `class-transposition-relations-present-ct-p-z`. Research
   status: reduced to Thompson's `V` case by the {2,p,q}-cube swindle (lane proof, pass 4). The `V`
   case is Bleak–Quick 1511.02123 (literature, proved via Cannon–Floyd–Parry). An elementary
   `V` proof is open.
2. `Group.IsFinitelyPresented (TranspGroup P)`, i.e.
   `ct-p-z-has-a-finite-class-transposition-presentation`. The truncation is OPEN.

Neither is formalized. So `kourovka_17_61` is **not** provable outright from this lane today.

**Resolve when.** A trusted build (`gqprobe-lean.sh`) of
`GroupApproximation.ClassTransposition.Presentation.Presented` is green and those bytes are on main.
This node then covers only the module. The mathematical debt stays on the two claim nodes.

**Added 09-19: `.../ShiftFC.lean`** (Mathlib only). Lemma FC of
`ct-p-z-is-finitely-presented-by-position-shifting`, abstractly:
- `fc_of_base`: the base far-commutation relations at positions 1–2, together with the shift
  definitions (D), imply every far-commutation relation;
- `window_of_base`: a shift-invariant window family holds at every position once it holds at
  position 2.

This is the group-theoretic core of the elementary finite presentation of `CT_P(Z)`. It does not
depend on the transposition presentation. The module is unprobed and not root-wired.

**Added 09-19 (Stage-1 route, all unprobed):** the formal route to `kourovka_17_61` through the
position-shifting finite presentation.
- `Coxeter`: the Coxeter relations present `Sym(n)`, via the right-transversal normal form.
- `Frac`, `Moves`, `Comb`, `ListId`, `ListBlock`: the concrete side.
  - `frac b c` maps an ordered box partition `b` onto `c` box by box;
  - moves (splits and swaps) on lists of boxes, and the comb bases;
  - the list identities of the relation families (a), (b) and (d).
- `Gens`, `Group`, `Hats`: the finitely presented group `H P`.
  - The generators `Ty P × Bool` are the types at positions 1 and 2, and positions `≥ 3` come
    from the shift definitions.
  - The relators are the bounded valid instances, a finite set (`relSet_finite`).
  - Also: the shift lemma `toH_up`, stabilization `toH_stable`, and the hat evaluations.
- `RelFC`: Lemma FC in `H P` (`fc_all`), from bounded base instances (`fc_base`).
- `WinAux`: bookkeeping for the window relations.

Still to write:
- the window relations at all positions;
- the Coxeter application;
- the full-split normal form;
- injectivity of the evaluation into `Perm ℤ`;
- its range, which is `CT_P(ℤ)`;
- the assembly of `kourovka1761Statement`.
