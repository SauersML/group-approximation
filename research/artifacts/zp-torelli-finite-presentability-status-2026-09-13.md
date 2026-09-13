# Zaremsky Problem 3.1: status of finite presentability of Torelli groups (2026-09-13)

Lane z3-01-torelli. Root: `zaremsky-3-01-torelli-groups-finitely-presented`.

Problem, verbatim (Zaremsky, *Some open problems*, version of July 12, 2026, §3
Problem 1): "Is the Torelli group of Out(Fn) (or MCG(Sg), or Aut(Fn)) finitely
presented for large enough n or g?"

## 1. Families and the reading

- `T_n = ker(Out(F_n) -> GL_n(Z))`; `IA_n = ker(Aut(F_n) -> GL_n(Z))`;
  `I_g = ker(Mod(S_g) -> Sp_{2g}(Z))`, closed oriented `S_g`.
- Reading: the yes-answer for a family is eventual finite presentability; the
  no-answer is infinitely many members that are not finitely presented.
- Proved equivalences (established nodes with proofs):
  - `ia-n-fp-iff-outer-torelli-fp`: `IA_n` is finitely presented iff `T_n` is
    (`n >= 2`), from `1 -> F_n -> IA_n -> T_n -> 1`. So there are two independent
    questions, not three.
  - `surface-torelli-fp-invariant-under-puncture-and-boundary`: `I_g`, `I_{g,1}`
    and `I_g^1` are finitely presented together (`g >= 2`).

## 2. Status table

| family | small cases | first open case | finite generation | degree-2 homology | top-degree obstruction |
|---|---|---|---|---|---|
| `T_n`, `IA_n` | `T_1 = T_2 = 1`, `IA_2 ≅ F_2`; `T_3`, `IA_3` not finitely presented | `n = 4` | all `n` (Magnus) | `H_2(IA_n)` finitely generated as a `GL_n(Z)`-module (Day–Putman 2017); as an abelian group: not known | `H_{2n-4}(T_n; Z)` infinitely generated for `n >= 3` (BBM 2006) |
| `I_g` | `I_1 = 1`; `I_2` infinitely generated free | `g = 3` | `g >= 3` (Johnson) | `H_2(I_g; Z)` finitely generated for `g >= 4` (Gaifullin, arXiv:2606.13517, Theorem A, preprint) | `H_{3g-5}(I_g; Z)` infinitely generated, `cd I_g = 3g - 5` (BBM 2007) |

No claimed answer to any open case was found. Explicit statements that the problem
is open:

- Kassabov–Putman (Math. Ann. 376 (2020), §1): "it is not known whether I_g^b is
  finitely presentable for g ≥ 3";
- Ershov (arXiv:2601.01377, abstract, January 2026): finite presentability of `IA_n`
  for `n >= 4` is "a long-standing open problem".

## 3. Sources (theorem numbers verified 2026-09-13)

- Bestvina–Bux–Margalit, arXiv:math/0603177, Main Theorem (1)–(3); page 1 (Krstić–
  McCool sentence); page 2 (history: Nielsen, Magnus, Smillie–Vogtmann, the H_2
  fact). PDF pages 1–2 read.
- Bestvina–Bux–Margalit, arXiv:0709.0287, Theorem A (`cd I_g = 3g - 5`), Theorem B
  (Johnson kernel `2g - 3`), abstract (top homology infinitely generated). PDF
  pages 1–2 read.
- Kassabov–Putman, arXiv:1807.01338v3, Theorem A and Definition 1.2 (finite
  `Γ`-equivariant presentations), §1 history. PDF pages 1–2 read.
- Minahan–Putman, arXiv:2504.00211, Theorems A and B (HTML); Minahan,
  arXiv:2307.07082 (`g >= 51`, superseded); Minahan–Putman, arXiv:2504.00224
  (presentations of representations) and arXiv:2504.00215.
- Gaifullin, arXiv:2606.13517, Theorem A (HTML); Gaifullin, arXiv:2011.00295 (genus 3
  spectral sequence, `E^3_{0,2}` infinitely generated; abstract).
- Ershov, arXiv:2601.01377, Theorem 1.1 and introduction (HTML).
- Day–Putman, arXiv:1408.6242 (Geom. Topol. 21 (2017)), abstract.
- Church–Ershov–Putman, arXiv:1711.04779 (Johnson filtration finite generation),
  Putman arXiv:1106.3294 (cubic generating sets), Stylianakis arXiv:2601.05834
  (finite generation, two boundary components), abstracts only.
- Not relevant to presentability: Ragosta arXiv:2607.01872 (growth of stable
  subgroups).

Search log: arXiv listing searches for "Torelli finitely presented", "Torelli second
homology", "Torelli presentation", "IA_n finitely presented", "IA-automorphism
homology", "Torelli group finitely generated Johnson". Web search was unavailable
(session budget exhausted). zbMATH returned 403. MathSciNet was not reached. The
bound: arXiv abstracts through early September 2026.

## 4. Method map: where each approach stops

1. **Brown's criterion with finitely many orbits** (complex of cycles for `I_g`;
   spine of outer space for `T_n`). Torelli groups have infinite index in the ambient
   mapping class group or `Out(F_n)`, so cells fall into infinitely many orbits.
   Presentations obtained this way are finite only modulo the ambient conjugation
   action, which are equivariant presentations in the sense of Kassabov–Putman.
2. **Peak reduction in van Kampen diagrams** (Ershov). This proves
   `IAC_{n,d}`, `IAR_{n,d}` finitely presented for `n >= d + 115`. The endpoint
   `d = n` is `IA_n`, and Ershov says induction on `d` does not reach it.
3. **Homology in degree 2.** It is necessary for a presentation. Now known for
   `I_g`, `g >= 4`, but not sufficient: type `FP_2` requires a finitely generated
   relation module, and finite presentability requires more still.
4. **Abelian-quotient overgroups and Σ-invariants.** `IA_n ⊲ IAC^+_{n,n-1}` has
   quotient `Z^{n-1}`. If the overgroup is finitely presented, then `IA_n` is
   finitely presented iff the characters vanishing on `IA_n` lie in `Σ²` (Renz).
   This is a restatement map, not a reduction, because `d = n - 1` is outside
   Ershov's range.

## 5. Sharpest next targets

- (A) Genus 3, a single case with evidence: is `I_3` finitely presented? Gaifullin's
  2020 spectral-sequence result points toward "no"; `H_2(I_3; Z)` is not covered by
  Theorem A.
- (B) Rank 4: is `T_4` finitely presented? Either answer is new. The BBM `4`-dimensional
  `K(π,1)` and Smillie–Vogtmann's rational Euler characteristic give no degree-2
  information.
- (C) Extending Ershov's peak reduction from `d <= n - 115` to `d = n` (the Aut and
  Out families), where the needed room in the super-Artinian order disappears.
