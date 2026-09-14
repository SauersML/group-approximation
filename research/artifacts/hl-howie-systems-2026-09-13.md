# Symmetric square systems and Kervaire--Laudenbach with torsion (2026-09-13)

Lane `hl-howie-systems`. The target was the square `p`-nonsingular systems over a
torsion-free `H` that `kl-p-power-index-reduces-to-p-nonsingular-square-systems`
(c2807efb5) and `kl-p-square-systems-are-connected-after-localization`
(c57c5e178) produce from one equation over `G = H.Q`, `Q` a finite `p`-group.

**Verdict: partial.** Every single equation and every variable-disjoint
subsystem is solvable over torsion-free `H`
(`kl-p-square-system-equations-are-individually-solvable`). The whole system,
equivalently Kervaire--Laudenbach over torsion-free-by-finite-`p`-group
coefficients at degree prime to `p`, stays OPEN. None of the three directed
routes closes the gap; exact failing steps are in section 3.

## 1. Pins

### 1.1 Mikheenko, arXiv:2309.09096 `main.tex` (MSI: `/scratch.global/sauer354/solve-kl-torsion-car-crash/src/2309.09096/`)

- l.227--232: "The following conjecture is as yet neither proved nor disproved
  ... Howie conjecture [How81]. Any non-singular system of equations over any
  group is solvable."
- l.264--266: "Theorem [How81]. A finite non-singular system of equations over
  a locally indicable group is solvable."
- l.271--274: "Theorem [Kr85]. Let p be a prime. A finite p-nonsingular system of
  equations over a locally p-indicable group is solvable."
- l.280--282: "Theorem [K93]. Any unimodular equation over a torsion-free group
  is solvable." followed by "This result was generalized in [K06]. It is unknown
  if an anologous result is true for non-singular equations."
- l.299--312 (Shmel'kin [Sh67]): nilpotent cases, e.g. "G is nilpotent and there
  is a finite unimodular system of equations over G; ... then the system is
  solvable in G, and the solution in G is unique."
- l.338--349 (KMR24) and l.354--377 (main theorem): groups with a subnormal
  series with abelian factors, all but the last torsion-free (resp.
  `p'`-torsion-free), admit overgroups of the same shape where every
  non-singular (resp. `p`-nonsingular) system is solvable.

So beyond finite groups (Gerstenhaber--Rothaus) the known cases of Howie's
conjecture are locally indicable, locally `p`-indicable, and solvable-type
coefficient groups. A torsion-free `H` with these properties already makes
`G = H.Q` locally `p`-indicable, so Krstic solves the square system outright.
The open case is torsion-free `H` that is not locally `p`-indicable.

### 1.2 Klyachko, arXiv:math/0406382v4 `main.tex` (MSI: `/scratch.global/sauer354/hl-kl-torsion/src/0406382/`)

- l.252--254: "Theorem 1'. Any unimodular generalized equation over a
  torsion-free group is solvable over it."
- l.263--267: "Definition 1. Generalized equation (1') is called unimodular if
  1) the order of \prod t_i in the group T is infinite; 2)
  \gp{\prod t_i}\triangleleft T; 3) T/\gp{\prod t_i} is a group with the strong
  unique product property."
- l.327--336: the Corollary, quoted in `klyachko-multivariable-equation-citation`.
- l.364--365: "Main theorem. If any unimodular equation over any free power of a
  group G is Magnusian, then any unimodular generalized equation over G is
  solvable over G."
- l.382--383: "Lemma 1. Any unimodular equation over a torsion-free group is
  magnusian."
- l.725--750 (concluding remarks): condition 3) replaced by "the group
  T/\gp{\prod t_i} is torsion-free" defines *weakly unimodular*, with "Question
  1. Is it true that any weakly unimodular generalized equation over a
  torsion-free group is solvable over it?"; and "Question 3. Is it true that any
  (weakly) unimodular (or even any nonsingular) generalized equation over a
  finite group is solvable over it?"

## 2. What is proved

`kl-p-square-system-equations-are-individually-solvable`:
1. each `rho_q` conjugates into Klyachko's multivariable form (**) over `H`, with
   content of exponent sum `m`, so it is solvable over `H` when `m = ±1`, and in
   general when the content is not a proper power;
2. equations with pairwise disjoint unknown sets are solved simultaneously in the
   amalgamated free product of their solution groups over `H`;
3. a violation of KL at `m = ±1` over a torsion-free-by-finite-`p`-group sits on
   pairs of equations sharing an unknown, i.e. edges of
   `Cay(Q, Lambda Lambda^(-1) \ {1})`.

## 3. The three directed routes and where each stops

### (a) Equivariant car crash

- **Over `G`.** Klyachko 1993 needs relative freeness `gp(a_i, P) = <a_i> * P`
  for the coefficients (pins in `hl-kl-torsion-pins-2026-09-13.md`). In `G = H.Q`
  a coefficient outside `H` can have finite order. The substitution `t -> x t y`
  changes same-sign coefficients but only conjugates sign-change coefficients,
  whose orders are invariant (`klyachko-kl-holds-when-all-coefficients-have-infinite-order`).
- **Torsion cannot always be substituted away.** In `Z ⋊ Z/2` with inversion,
  every element `g h` outside `Z` satisfies `(gh)^2 = g h g h = h^(-1) h = 1`. So
  every coefficient outside `H` has finite order, whatever the substitution.
- **Over `H`.** On the `Q`-cover every coefficient lies in the torsion-free `H`,
  so relative freeness is available. But the equation becomes a system of `|Q|`
  equations with shared unknowns. Klyachko's crash count is organized around one
  relator, and his 2006 generalization is one generalized equation. The
  `Q`-symmetry permutes the equations but does not reduce their number: the
  symmetric system is the rewrite of `w` itself, so folding it back returns to
  `G`. **Failing step:** a crash count for several relators with shared
  variables. No such theorem is pinned.

### (b) Topological / equivariant degree

- p-nonsingularity gives `det E ≢ 0 (mod p)`, hence `det E != 0`, so a
  Gerstenhaber--Rothaus degree argument solves the system in every compact Lie
  group model of `H`, i.e. whenever `H` embeds in one.
- A torsion-free `H` without matrix models, or not known to be hyperlinear, gives
  no map on which to compute a degree. When `H` is hyperlinear, `G` is hyperlinear
  (finite extension) and main already has KL for `G`
  (`kervaire-laudenbach-holds-for-hyperlinear`).
- Smith theory / `Z/p`-equivariant degree would need a compact `Q`-space
  realizing `H`; none exists for arbitrary torsion-free `H`. **Failing step:** no
  topological model of an arbitrary torsion-free group. This route cannot reach
  past the hyperlinear class.

### (c) Reduction to one equation

- The system is `n = |Q|` relators in `H * F(Y)`. Klyachko's Theorem 1' handles
  one generalized equation over `H` with an arbitrary variable group `T` satisfying
  Definition 1.
- Putting the torsion into the variable group means writing coefficients
  `a_j = h_j q_j` (split case) and taking `T ⊇ Q * <t>`. Two things fail.
  - The conjugation relations `q h q^(-1) = ^q h` are extra relators, so it is not
    one generalized equation.
  - Condition 3) needs `T/<prod t_i>` strong UP. With `Q` inside `T` that
    quotient has torsion unless `Q` dies, and Klyachko's torsion-free relaxation is
    his open Question 1.
- **Failing step:** absorbing torsion into the variable group violates
  Definition 1. The generalizations needed are Klyachko's own open Questions 1
  and 3.

## 4. Exact remaining gap

1. **Pairs sharing unknowns.** Simultaneous solvability of two equations
   `rho_q, rho_q'` with `q^(-1) q' in Lambda Lambda^(-1)`, over an arbitrary
   torsion-free `H` that is not locally `p`-indicable.
2. **Iterative solving.** Solving the equations one at a time would need the
   one-relator solution group `(H * F(U_q))/<<rho_q>>` to be torsion-free, or to
   give relative freeness at the shared unknowns. For locally indicable
   coefficient groups this is the Brodskii--Howie theory (Klyachko 2006,
   l.200--212, cites Theorem B); for torsion-free `H` it is not known. Not re-read
   at source here.
3. **Closing equations.** By `kl-p-square-systems-are-connected-after-localization`,
   any ordering reaches equations introducing no new unknown. These are pure
   compatibility constraints, which neither Klyachko's theorems nor amalgamation
   touch.

No MSI compute was used beyond reading sources. No existing node was edited.
