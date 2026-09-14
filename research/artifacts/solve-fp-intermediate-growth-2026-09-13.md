# solve-fp-intermediate-growth (2026-09-13)

Lane on Grigorchuk's question: is there a finitely presented group of intermediate growth?

## 1. Verbatim pins

Source: Grigorchuk, *Milnor's problem on the growth of groups and its consequences*,
arXiv:1111.0512, e-print fetched on MSI to
`/scratch.global/sauer354/solve-fp-intermediate-growth/src/1111.0512/Grigorchuk10.tex`.

- l.292–293: "we do not know yet if there are finitely presented groups of intermediate growth,
  and this is the main open problem in the field."
- l.644: "All known examples of groups of intermediate growth are infinitely presented groups."
- l.646–649 (Problem `finitepresent`): "Is it true that the growth function of a finitely
  presented group is equivalent either to a polynomial or to the exponential function $2^n$?"
- l.652–658: "In \cite{grigorch-pak:intermediate_growth}, it is conjectured that there are no
  finitely presented groups of intermediate growth. At the same time, the author suggests even a
  stronger conjecture. \begin{conj} A finitely presented group either contains a free
  subsemigroup on two generators or is virtually nilpotent. \end{conj}"
- l.669–672: "The corresponding finitely presented group (which we denote here
  $\tilde{\mathcal{G}_{\xi}}$) is an ascending $HNN-$extension of $\mathcal{G}_{\xi}$. [...]
  Unfortunately (or fortunately), the group $\tilde{\mathcal{G}_{\xi}}$ has exponential growth but
  shares the property of amenability with $\mathcal{G}_{\xi}$."
- l.683–685: "it was observed by P. de la Harpe and the author that any finitely presented group
  $\hat{\mathcal G}$ that can be homomorphically mapped onto $\mathcal{G}$ contains a free subgroup
  on two generators and hence is of exponential growth."
- l.866–868 (Rosset) and l.884–886 (no free subsemigroups, elementary amenable quotient): quoted in
  `research/no-free-subsemigroups-fg-kernels-citation.md`.

Branch groups survey (Bartholdi–Grigorchuk–Šunić, arXiv:math/0510294, `branch.tex`): the only
finite-presentation hit is l.1055, "it is not finitely presented", about one specific group. No
general theorem that branch groups are infinitely presented was found in that file.

## 2. What landed

- `proper-self-conjugate-subgroups-force-free-subsemigroups` (+ proof):
  `t H t^{-1} ⊊ H` ⇒ `t, a t` freely generate a free subsemigroup; so every ascending HNN
  extension along a non-surjective endomorphism has exponential growth.
- `non-automorphic-hnn-extensions-contain-free-subsemigroups` (+ proof): an HNN extension has a
  free subsemigroup unless both associated subgroups equal the base.
- `no-free-subsemigroups-give-fg-kernels-over-ea-quotients` (+ citation): Rosset and
  Longobardi–Maj–Rhemtulla, imported from the survey.
- OPEN root `fp-group-of-intermediate-growth-exists`, and OPEN
  `fp-groups-without-free-subsemigroups-are-virtually-nilpotent`.

## 3. Correction before landing

A draft claim "finitely presented groups without free subsemigroups have finitely generated
kernel over Z" (Bieri–Strebel plus the HNN dichotomy) was withdrawn before landing. It is a
strict special case of the published l.884–886 theorem, which needs only finite generation.
So maps onto `Z` give no obstruction specific to finite presentation.

## 4. Exact gap

Every recorded constraint on a witness except the de la Harpe–Grigorchuk observation holds for
all finitely generated groups of intermediate growth. What is missing is an invariant that uses
finite presentation itself and is incompatible with subexponential growth. Candidates not tried
here: Dehn functions of amenable finitely presented groups, `H_2` and deficiency, and relator
growth compared with ball growth.
