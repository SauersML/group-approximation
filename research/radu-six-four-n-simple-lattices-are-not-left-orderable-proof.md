---
rg: 2
id: radu-six-four-n-simple-lattices-are-not-left-orderable-proof
kind: route
title: Collapse of every Gamma_{6,4n} modulo Radu's two non-residually-finite commutators through one n-independent window presentation, then transfer from the certified commutator subgroup of Gamma_{4,4}
target: radu-six-four-n-simple-lattices-are-not-left-orderable
requires:
  - radu-simple-six-six-lattices-are-not-left-orderable
artifacts:
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/fig64n.py
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/xcheck64n.py
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/g64n.py
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/mkelim.py
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/mkwin.py
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/verwin.py
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/mktc.py
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/relators-64n.txt
  - experiments/lo-certificate-radu-six-four-n-2026-09-17/run.log
---

Fix n ≥ 2. Write:
- `Γ = Γ_{6,4n}`;
- `c = [a_1^3,a_2^4]` and `d = [a_2^3,a_1^4]` (GAP's `Comm`; the other commutator convention
  conjugates `c` and `d`, so it gives the same normal closures);
- `N = ⟨⟨c,d⟩⟩_Γ`, `Q = Γ/N`, and `Q_c = Γ/⟨⟨c⟩⟩`.

**Step 0: the square datum for general n.** Radu's Figure `picture:64n` has `6n` squares. Written as
relators they are:
- the four `Γ_{4,4}` squares `a_1b_1a_2^{-1}b_1`, `a_1b_2a_2b_2^{-1}`, `a_1b_2^{-1}a_2^{-1}b_1^{-1}`,
  `a_1b_1^{-1}a_2^{-1}b_2`;
- `a_3b_3a_3^{-1}b_2^{-1}`, `a_3b_2a_3^{-1}b_1^{-1}` and `a_3b_1a_3^{-1}b_{2n}^{-1}`;
- `a_2b_3a_2^{-1}b_3` and `a_2b_{2n}a_2^{-1}b_{2n}`;
- `J(j)`, for j = 2,…,n: `a_1b_{2j}a_1b_{2j-1}^{-1}`, `a_1^{-1}b_{2j}a_3^{-1}b_{2j-1}^{-1}`,
  `a_3b_{2j}a_1^{-1}b_{2j-1}^{-1}`;
- `K(j)`, for j = 2,…,n−1: `a_2b_{2j+1}a_2b_{2j}^{-1}`, `a_2^{-1}b_{2j+1}a_3^{-1}b_{2j}^{-1}`,
  `a_3b_{2j+1}a_2^{-1}b_{2j}^{-1}`.

These are 4 + 3 + 2 + 3(n−1) + 3(n−2) = 6n squares.

Checks on the datum:
- `fig64n.py n` reads the squares from the pstricks source under four boundary-reading conventions.
  Exactly one convention makes the first four squares equal to `RADU_44`, the `Γ_{4,4}` squares
  verified in `radu-simple-six-six-lattices-are-not-left-orderable-proof`. `BMW` accepts that datum as
  complete: every pair of a b-letter and an a-letter lies in exactly one square.
- `xcheck64n.py n corrected` and `g64n.py n corrected` rebuild the datum from the local permutations
  printed in Radu's proof. After one misprint (`b_3`, see the claim) is corrected, they recover the
  same datum for n ≤ 8.
- `mkelim.py` re-validates it with `BMW` for n ≤ 24.
- There are no involutions, and no square has the form `(xy)^2`, consistent with torsion-freeness.
- `relators-64n.txt` lists the datum for n ≤ 12.

**Step 1: `N ≤ Γ^{(∞)}`.**
- By the (6,6) proof, Lemma 2, `Γ_{4,4} ≤ Γ` via the identity on letters.
- Radu, Proposition `nonrf`, gives `c, d ∈ Γ_{4,4}^{(∞)}`.
- Every homomorphism `Γ → F` with F finite restricts to a finite quotient of `Γ_{4,4}`, so it kills
  `c` and `d`. Hence `N ≤ Γ^{(∞)}`.

**Step 2: a surjection from one fixed group (n ≥ 3).**
- The *window group* `W = W(5,2)` (`mkwin.py 5 2`) has generators `a_1,a_2,a_3,b_3` and 14 relators.
  Its abbreviations are `b_2 = a_3b_3a_3^{-1}`, `b_1 = a_3b_2a_3^{-1}`, `z = a_3b_1a_3^{-1}`,
  `b_4 = a_1^{-1}b_3a_1^{-1}`, `b_5 = a_2^{-1}b_4a_2^{-1}`, `y_0 = z`, `y_1 = a_1y_0a_1`,
  `y_2 = a_2y_1a_2`.
- Its relators are:
  - the four `Γ_{4,4}` squares;
  - `a_2b_3a_2^{-1}b_3` and `a_2za_2^{-1}z`;
  - `a_1^{-1}b_4a_3^{-1}b_3^{-1}`, `a_3b_4a_1^{-1}b_3^{-1}`, `a_2^{-1}b_5a_3^{-1}b_4^{-1}` and
    `a_3b_5a_2^{-1}b_4^{-1}`;
  - `a_1^{-1}y_0a_3^{-1}y_1^{-1}`, `a_3y_0a_1^{-1}y_1^{-1}`, `a_2^{-1}y_1a_3^{-1}y_2^{-1}` and
    `a_3y_1a_2^{-1}y_2^{-1}`.
- Substitute `z = b_{2n}`, `y_1 = b_{2n-1}` and `y_2 = b_{2n-2}`. Each abbreviation and each relator
  becomes one of the Step 0 squares: the base squares, `J(2)`, `K(2)`, `J(n)` and `K(n-1)`. This
  needs n ≥ 3, so that `K(2)` and `K(n-1)` exist. For n = 3 they coincide, which is harmless. `verwin.py 5 2 3 24` checks this mechanically
  against the figure datum for n = 3,…,24. The general statement is the index bookkeeping above.
- In `Γ`, the Tietze moves `b_2 = a_3b_3a_3^{-1}`, `b_1 = a_3b_2a_3^{-1}`,
  `b_{2j} = a_1^{-1}b_{2j-1}a_1^{-1}` and `b_{2j+1} = a_2^{-1}b_{2j}a_2^{-1}` express every b-letter
  through `a_1,a_2,a_3,b_3` (this is `mkelim.py`). So `a_1,a_2,a_3,b_3` generate `Γ`.
- Hence the identity on `a_1,a_2,a_3,b_3` defines an epimorphism `π_n: W → Γ`. Since `c` and `d`
  are words in `a_1,a_2`, it induces epimorphisms `W/⟨⟨c,d⟩⟩ → Q` and `W/⟨⟨c⟩⟩ → Q_c`.

**Step 3: `Q'` is cyclic.**
- GAP's `CosetTableFromGensAndRels` (HLT) closes on `W/⟨⟨c,d⟩⟩` with 2 cosets of `⟨a_1⟩`, in 26 s
  with at most 12·10^6 cosets (`run.log`, `w52`). A closed coset table proves the index.
- The image of `⟨a_1⟩` in `Q` has index at most 2, so it is normal with abelian quotient. Hence
  `Q' ≤ ⟨a_1⟩`, and `Q'` is cyclic.

**Step 4: `Q'` is perfect, so `Q` is abelian.**
- `W/⟨⟨c⟩⟩` has abelianization `[2,2]`. Reidemeister–Schreier (`IsomorphismFpGroup` on the kernel
  of `MaximalAbelianQuotient`) gives abelian invariants `[]` for its derived subgroup, so that
  subgroup is perfect.
- Under an epimorphism the derived subgroup maps onto the derived subgroup, so `Q_c'` is perfect.
  Its image `Q'` is perfect too.
- A perfect cyclic group is trivial, so `Q` is abelian.
- The same perfectness holds for the smaller windows `W(3,1)` and `W(4,0)`, which map onto every
  `Γ_{6,4n}` with n ≥ 2 (`verwin.py 3 1 2 24`, `verwin.py 4 0 2 24`).

**Step 5: identification.**
- `Γ^{ab}` is a quotient of `W^{ab} = [2,2]`. The parity map (a-letters to the first `C_2`, b-letters
  to the second) is well defined, because every square has two letters of each kind. It is onto
  `(C_2)^2`, so `Γ^{ab} ≅ (C_2)^2`.
- Since `Q` is abelian, `Γ' ≤ N`. Also `N ≤ Γ'`, because `c` and `d` are commutators. So `N = Γ'` and
  `Q ≅ (C_2)^2`.
- `Γ/Γ'` is finite, so `Γ^{(∞)} ≤ Γ'`. With Step 1, `Γ^{(∞)} = N = Γ'`.
- The parity kernel `Γ^+` (the type-preserving subgroup) is normal of index 4 with abelian quotient,
  so `Γ' ≤ Γ^+`, and equal indices give `Γ' = Γ^+`.
- *Simplicity.* Radu, Theorem `64n`, shows `Γ` is just-infinite and virtually simple. His argument in
  §6.1 (a finite-index `Γ^{(∞)}` in such a group is simple) gives that `Γ^{(∞)}` is simple.

**Step 6: not left-orderable.** Apply Part 2 of `radu-simple-six-six-lattices-are-not-left-orderable`
(transfer) with `N = S = Γ^{(∞)}`. `Γ/N` is abelian and `Γ_{4,4} ≤ Γ`, so `Γ_{4,4}' ≤ Γ^{(∞)}`.
`Γ_{4,4}'` is not left-orderable (the 124-triple certificate), so neither is `Γ^{(∞)}`.

**Step 7: type F.** `Γ^+` is torsion-free and acts freely and cocompactly on `T_6 × T_{4n}`. So
`Γ^{(∞)} = Γ^+` is `π_1` of `(T_6 × T_{4n})/Γ^+`. That finite nonpositively curved square complex has
4 vertices and `4·6n = 24n` squares. □

**n = 2.**
- `W(5,2)` does not map onto `Γ_{6,8}`, because `J(2) = J(n)` and `K(n-1) = K(1)` does not exist;
  `verwin.py 5 2 2 2` prints False.
- Steps 3 and 4 are instead run on the full Tietze reduction: `mkelim.py 2 12000000 cd` gives index 2
  and a perfect `Q_c'`.
- Directly, `mktc.py 2` enumerates `Γ_{6,8}/⟨⟨c⟩⟩` over the trivial subgroup and gets 4 cosets.

**Independent per-n confirmation, n = 2,…,24.** `mkelim.py n 12000000 cd` builds the 4-generator
reduction of the full `6n`-square presentation for each n. It reproduces `Γ^{ab} = [2,2]`, index 2
of `⟨a_1⟩` in `Q`, and a perfect `Q_c'`. The times grow from 0.3 s (n = 2) to 78 s (n = 24).

*Review status.* This is a machine computation in GAP 4. There are two independent checks of the
datum (the figure and the printed permutations). No human has checked the coset tables. The trust
points are:
- GAP's HLT enumerator, and `MaximalAbelianQuotient`/`IsomorphismFpGroup`/`AbelianInvariants`;
- the index bookkeeping in Step 2, confirmed mechanically for n ≤ 24;
- Radu's Proposition `nonrf` and his virtual-simplicity theorem;
- the (6,6) node's certificate.
