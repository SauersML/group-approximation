# Juan-Pineda–Leary and von Puttkamer–Wu conjectures: verified known cases (2026-09-13)

Lane z1-07-vc-proof, for `zaremsky-1-07-juan-pineda-leary-conjecture` (Zaremsky, *Some open
problems*, July 12, 2026 version, Section 1, Problem 7).

## Definitions (von Puttkamer–Wu, arXiv:1607.03790v2, pages 1–2)

- `E_VC G` (their E̲̲G): a `G`-CW model whose `H`-fixed set is contractible for every virtually
  cyclic `H` and empty otherwise. *Finite* means finitely many orbits of cells; *finite type*
  means finitely many orbits of cells in each dimension.
- Conjecture A (Juan-Pineda–Leary, Contemp. Math. 407 (2006), Conjecture 1): a group with a
  finite model for `E_VC G` is virtually cyclic.
- (BVC) "G has a finite set of virtually cyclic subgroups {V1, V2, ..., Vn} such that every
  virtually cyclic subgroup of G is conjugate to a subgroup of some Vi." The finite set is a
  witness. The name follows Groves and Wilson.
- Conjecture B (1607.03790, page 2): "Let G be a finitely presented group which has BVC.
  Then G is virtually cyclic."
- Remark (a) there: finite presentation is necessary (Osin's finitely generated torsion-free
  groups with two conjugacy classes have BVC). Remark (b): "We do not know whether
  Conjecture B holds for all elementary amenable groups. Groves and Wilson showed that
  solvable groups satisfy it."

## Results read in the sources

Each item says where it was read. "Read" means the statement was checked on the PDF page;
"via" means it was taken from another paper's account.

1. **Finite model gives BVC and finite presentation.** 1607.03790, Proposition 1.1 (page 3,
   read): (a) BVC; (b) finite model for `E_FIN G`; (c) Weyl groups of finite subgroups
   finitely presented and `FP_infinity`; (d) finite-type model for `EG`, so finitely
   presented; (e) finitely many conjugacy classes of finite subgroups. Lemma 1.3 (read): a
   model with finite 0-skeleton exists if and only if `G` has BVC.
2. **Hyperbolic groups, Conjecture A:** Juan-Pineda–Leary 2006, Corollary 12 (via
   1607.03790, page 1).
3. **Elementary amenable groups, Conjecture A:** Kochloukova–Martínez-Pérez–Nucinkis, Bull.
   London Math. Soc. 43 (2011), arXiv:0903.4079 (via 1607.03790, page 1). Groves–Wilson gave
   a simplified proof. The KMN abstract (read on arXiv) includes: a polycyclic-by-finite
   group with finitely many conjugacy classes of maximal virtually cyclic subgroups is
   virtually cyclic.
4. **Virtually solvable groups with BVC are virtually cyclic:** 1607.03790, Proposition 1.12
   (page 5, read), combining Lemma 1.11 (BVC passes to finite-index subgroups,
   citing KMN 5.6) with Groves–Wilson, *Soluble groups with a finiteness condition arising
   from Bredon cohomology*, Bull. London Math. Soc. 45 (2013) 89–92.
5. **Main theorem of 1607.03790** (page 2, read): the following classes satisfy Conjecture A,
   and in fact any finitely generated group in them has BVC if and only if it is virtually
   cyclic: (a) HNN extensions of free groups of finite rank (2.11); (b) one-relator groups
   (2.12); (c) acylindrically hyperbolic groups (3.2); (d) 3-manifold groups (3.6); (e) CAT(0)
   groups containing a rank-one isometry or `Z^2` (4.13), in particular CAT(0) cube groups
   (4.16).
6. **General lemmas of 1607.03790** (pages 4–7, read):
   - Lemma 1.7: BVC implies finitely many conjugacy classes of finite subgroups, so bounded
     orders.
   - Corollary 1.5: torsion-free `G` has BVC if and only if there are `g_1, ..., g_n` with
     every element conjugate to a power of some `g_i`.
   - Lemma 1.8: a torsion-free group with infinitely many conjugacy classes of primitive
     elements has no BVC.
   - Lemma 1.10: `A * B` with `A, B` nontrivial has BVC if and only if it is virtually
     cyclic.
   - Lemma 1.13 (citing Groves–Wilson 2.2): BVC implies (a) the ascending chain condition on
     normal subgroups; (b) if `M < L` are normal with `L/M` torsion, only finitely many normal
     `K` lie between them; (c) in any normal series the number of non-torsion factors is at
     most the number of infinite groups in a witness.
   - Lemma 1.14: if `G` maps onto a torsion-free group without BVC, `G` has no BVC.
   - Corollary 1.15: BVC implies `H_1(G;Z)` is finitely generated of rank at most one.
   - Lemma 1.17: under the strong Tits alternative, finitely generated subgroups have BVC
     only if virtually cyclic.
   - Corollary 1.18: finitely generated subgroups of Coxeter groups and RAAGs.
   - Lemma 1.19: if `phi` has infinitely many twisted conjugacy classes on `H`, then
     `H ⋊_phi Z` has no BVC.
   - Corollary 1.20: the same when `H` has property `R_infinity`.
   - Lemma 2.4 (page 8, read): if `[H:A], [H:B] >= 2`, the HNN extension `H*_theta` has no
     BVC. So only ascending HNN extensions can have BVC.
7. **Finitely generated linear groups:** von Puttkamer–Wu, *Linear groups, conjugacy growth,
   and classifying spaces for families of subgroups*, arXiv:1704.05304, IMRN 2019 no. 10,
   3130–3168. Theorem I (page 2, read): "A finitely generated linear group has BVC if and only
   if it is virtually cyclic." Corollary 2.12 (read): a finitely generated group with BVC has
   only virtually cyclic linear quotients.
8. **Artin groups, Conjecture A:** von Puttkamer–Wu, arXiv:1807.10095, Algebr. Geom. Topol. 20
   (2020) 2885–2904 (abstract read on arXiv): an Artin group admits a finite model for
   `E_VC G` if and only if it is virtually cyclic.
9. **Residually finite groups:** Barnea–Camina–Ershov–Lewis, *On groups that can be covered by
   conjugates of finitely many cyclic or procyclic subgroups*, arXiv:2210.15746v3 (Mathematische
   Annalen, 2025). Read on the PDF:
   - Theorem 1.1 (page 2): an infinite discrete residually finite group with finite NCC is
     infinite cyclic or infinite dihedral. This confirms von Puttkamer's thesis Conjecture
     5.0.1. Here NCC(G) is the least number of cyclic subgroups whose conjugates cover `G`.
     Finite NCC is property (bCyc) of 1704.05304.
   - Lemma 8.2 (page 28, citing von Puttkamer's thesis, Lemma 5.0.2): a residually finite group
     with (BVC) has a finite-index subgroup with (bCyc).
   - Corollary 8.4 (page 28): for residually finite `G`, (a) the Juan-Pineda–Leary conjecture
     holds and (b) Lück–Reich–Rognes–Varisco Question 4.9 has a positive answer.
   - The proof of 8.4(a) uses only BVC. So every residually finite group with BVC is
     virtually cyclic, with no finite presentation assumed: if `G` is infinite, its
     finite-index subgroup `H` from Lemma 8.2 is residually finite with finite NCC, so `H` is
     `Z` or `D_infinity`.
   - Their page-3 list of earlier classes with finite NCC: virtually solvable, one-relator,
     acylindrically hyperbolic, 3-manifold, CAT(0) cube, finitely generated linear, arbitrary
     linear groups in characteristic zero.
   - Their Corollary 1.2: a group with finite NCC has finite, cyclic or infinite-dihedral
     largest residually finite quotient.
10. **Braid groups:** Flores–González-Meneses, arXiv:1611.02187: the minimal dimension of a
    model for `E_VC` of `B_n` and `P_n` (`n >= 3`) is `n`. This concerns dimension, not
    finiteness.

## Open-status search (bounded)

- arXiv metadata search "Juan-Pineda Leary" (2026-09-13): 1807.10095, 1704.05304, 1607.03790 only.
- Web searches for 2024–2026 progress found Hernández Hernández–León Álvarez, arXiv:2603.13096
  (virtually cyclic dimension of poly-surface groups; nothing on the conjecture) and the
  normally poly-free dimension bound (Bol. Soc. Mat. Mex. 2024).
- No resolution of Conjecture A or B found. Not searched: MathSciNet, zbMATH, von Puttkamer's
  thesis beyond the lemma quoted by Barnea–Camina–Ershov–Lewis.

## Consequences for a counterexample to Conjecture B

A finitely presented, non-virtually-cyclic group with BVC must be:

- not residually finite (item 9);
- not linear (7);
- not virtually solvable (4);
- with `H_1` of rank at most one (6);
- with no non-ascending HNN splitting (6, Lemma 2.4);
- not acylindrically hyperbolic, one-relator, 3-manifold, or CAT(0) with a rank-one
  isometry or `Z^2` (5);
- with bounded orders of finite subgroups (6);
- satisfying the ascending chain condition on normal subgroups, with a bounded number of
  non-torsion factors in normal series (6, Lemma 1.13).
