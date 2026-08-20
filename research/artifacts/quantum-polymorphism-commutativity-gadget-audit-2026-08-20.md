# Quantum polymorphism commutativity gadgets -- focused audit

Source: Culf--van Dobben de Bruyn--Zeman, arXiv:2604.01408v1,
*Quantum polymorphism characterisation of commutativity gadgets in all quantum
models*.

This paper is directly useful for the consistency side of the PCP-to-group
program.  A commutativity gadget is a finite relational structure with two
distinguished variables whose measurements must commute in every relevant
quantum homomorphism.  A robust gadget quantitatively forces the commutator to
be small when the weighted constraint defect is small.

The precise imported statements are:

- Theorems 3.1 and 3.4 in the paper's numbering/labels `basic-char` and
  `orac-basic-char`: existence of a commutativity gadget in a chosen quantum
  model is equivalent to all quantum polymorphisms being classical, and it is
  enough to check arity `|A|^2`.
- Theorems 5.1 and 5.2 (`a-robust-char` and `c-v-robust-char`): robust gadget
  existence is equivalent to stable commutativity of the corresponding
  weighted polymorphism algebra, again at bounded arity `|A|^2`.
- Theorem 5.3 (`implications-equivalences`), items (ix)--(xii): for `qa` and
  `qc`, exact gadget existence is equivalent to the corresponding robust
  gadget existence; in particular a `qa` gadget is equivalent to both a
  robust `qa` gadget and a robust finite-dimensional `q` gadget.

The proof of the robustification is the right kind of anti-dilution argument:
if no uniform modulus existed, a sequence with vanishing weighted defect but
nonvanishing commutator would produce a noncommutative representation in a
tracial ultraproduct, contradicting the exact polymorphism hypothesis.

This can discharge a real obligation in `binary-pcp-coordinate-atlas-in-hs-
microstates`: once a fixed relational template with a `qa` commutativity
gadget is selected, all locally required proof-coordinate commutators can be
forced with a dimension-free modulus.  The paper also explicitly treats
weighted approximate homomorphisms, matching the Mastel--Slofstra weighted
defect formalism already used in Cairn.

It does **not** supply the rest of the groupification:

- one still needs a finite NP-hard template admitting the right gadget and a
  bounded-loss encoding of the chosen PCP verifier into that template;
- relational projection constraints must still be compiled into ordinary
  group words;
- commutativity alone does not impose the three diagonal/crossed endpoint laws
  of the S3 radical payment theorem;
- the modulus is existential for a fixed template, which is enough for an
  existence proof but not automatically an effective uniform machine-indexed
  Boone compiler.

The complete-graph calculation is also a warning: the quantum polymorphisms
of `K_n` contain `S_n^+`, so graph coloring itself is not automatically the
commutative target template needed by this route.
