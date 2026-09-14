# Kervaire--Laudenbach at non-amenable t-shapes: pins and census (2026-09-13)

Lane kl-nonamenable-shapes. TeX sources were fetched on MSI into
`/scratch.global/sauer354/solve-kl-nonamenable-shapes/src/` from
`https://arxiv.org/e-print/<id>`. Quotes are verbatim up to TeX macros; line
numbers refer to the fetched files. The shape definitions and the Main Theorem
of Forester--Rourke are already pinned in
`research/artifacts/kl-torsion-free-asphericity-pins-2026-09-13.md` and are not
repeated.

## 1. Forester--Rourke, arXiv:math/0306088 (`pi-two.tex`)

- **l.213–225.** "It is interesting to note that, whilst the adjunction problem is
  still open for torsion-free groups, and indeed for general groups provided the
  exponent sum of t in w is non-zero, the Main Theorem fails if either hypothesis
  (1) or (2) is dropped. We shall see that in either case there are both
  irreducible diagrams and elements of π_2(L,K) not accessible from π_2(K^+,K).
  This has consequences for a possible proof of the adjunction problem. Fenn and
  Rourke [FR; page 70] suggest that the Klyachko methods should be strong enough to
  prove the 1–generator 1–relator adjunction problem for torsion-free groups for any
  t–shape. While this may be true, this paper shows that the methods will need to be
  extended considerably if they are to work for a t–shape which is a proper power."
- **l.373–375, clump.** "A clump in a t–shape is a maximal connected subsequence of
  the form t^q or t^{-q} where q>1."
- **l.384–385.** "On the other hand, no t–shape which is a proper power is amenable."
- **l.834–837.** "This is in contrast with the adjunction property which is expected
  to hold in much greater generality. The adjunction property holds for the first two
  examples below by [Ho] and [Lev]."
- **Bibliography, l.101–102.** [Lev] Frank Levin, *Solutions of equations over
  groups*, Bull. Amer. Math. Soc. 68 (1962) 603--604. [Ho] James Howie, *The solution
  of length three equations over groups*, Proc. Edinburgh Math. Soc. 26 (1983) 89--96.

## 2. Klyachko--Thom, arXiv:1509.01376 (`main.tex`)

- **l.99–100.** "the only known examples of equations which are not solvable over
  some G are equations whose content is trivial. We call an equation w ∈ G ∗ F_n
  singular if its content is trivial, and non-singular otherwise."
- **l.112–113.** The Gerstenhaber--Rothaus main result, then: "Later, Howie
  [MR614523] proved the same result for locally indicable groups and conjectured it
  to hold for all groups -- we call that Howie's Conjecture."
- **l.120.** "A systematic study of the torsion-free case was started by Levin
  [MR0142643] who conjectured that equations in one variable with coefficients in a
  torsion-free group should always be solvable if w is conjugate to an element in G."
  (Verbatim. The intended hypothesis is presumably that w is *not* conjugate into G;
  this is not load-bearing here.) The same remark continues: "over any torsion-free
  group any several-variable equation whose content is not a proper power (and not
  the neutral element) is solvable [MR2251364]". For one variable the content is
  `t^m`, which is not a proper power only when `m = ±1`, so this adds nothing beyond
  Klyachko at one variable.
- **Bibliography.**
  - l.872–878: MR614523 = J. Howie, *On pairs of 2-complexes and systems of equations
    over groups*, J. Reine Angew. Math. 324 (1981) 165--174.
  - l.894–899: "Solving equations of length at most six over torsion-free groups",
    J. Group Theory 3 (2000) 329--337.
  - l.957–963: MR2251364 = A. A. Klyachko, *How to generalize known results on
    equations over groups*, Mat. Zametki 79 (2006).
  - l.987–993: MR0142643 = F. Levin, *Solutions of equations over groups*, Bull.
    Amer. Math. Soc. 68 (1962) 603--604.

## 3. Not read

- Howie 1981: the publisher PDF fetch from MSI returned an empty file.
- Levin 1962 and Fenn--Rourke 1996/1998: the fetches returned HTML landing pages, not
  PDFs.
- The length-six torsion-free paper: title only.

## 4. Exact shape census

`kl-nonamenable-shapes-2026-09-13/shape_census.py` (md5 `bdb4f5c882a799adf165d0bc23a29802`)
was run on MSI with Python 3.12, giving `census.txt` (md5
`06c7229c43c8d5b6e4d2f093ad62d062`).

- **Method.** It enumerates every cyclic word in `t^(±1)` of length `L <= 12` with
  nonzero exponent sum, up to rotation and inversion. It implements the
  Forester--Rourke definitions literally:
  - `D` deletes each occurrence of `t t^-1` in the cyclic word;
  - the root is `D^(m-1)(T)` for the least `m` with `D^m(T)` a pure power;
  - a clump is a maximal run of length > 1;
  - a shape is amenable when its root is `t t^-1` or has exactly one clump that is not
    the whole shape.
- **Checks.** It asserts, for every shape of length at most 10, that exponent sum ±1
  implies amenable (for non-pure shapes) and that proper powers are not amenable. Both
  assertions pass (`ASSERTS_OK`).
- **Output.** Each row lists the canonical representative (the least rotation or
  inverse, printed with `-` before `+`, so representatives with majority `t^-1`
  appear), the exponent sum, the class, whether it is a proper power, the root, and
  the root's clump count.

The counts are tabulated in `torsion-free-nonsingular-equations-at-nonamenable-shapes-inject`.
The smallest non-amenable representatives:
- **L = 6:** `--+--+`, the inverse class of `(t t t^-1)^2`, a proper power;
- **L = 7:** `---+--+`, the inverse class of `t^3 t^-1 t^2 t^-1`, exponent sum ±3, not
  a proper power;
- **L = 8:** `----+--+`, `---+---+` (a proper power) and `--+--+-+`.

Every non-amenable shape up to `L = 12` is its own root, with at least two clumps.
