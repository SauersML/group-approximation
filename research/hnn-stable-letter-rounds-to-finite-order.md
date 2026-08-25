---
rg: 2
id: hnn-stable-letter-rounds-to-finite-order
kind: claim
title: The stable letter of a hyperlinear co-dense HNN group rounds to an exact central letter of any finite order
distinct_from:
  hnn-hyperlinearity-is-amalgamated-free-haar-unitary: that is the equivalence between hyperlinearity of the HNN group and one amalgamated-free Haar unitary in the subgroup centraliser; this is a one-way transfer out of that equivalence, spectrally rounding the Haar letter to an exact order-m letter inside the same model, with no block doubling and no defect.
  arithmetic-double-swap-extension-is-binary-coset-wreath: that identifies A *_C (C x C_2) with the swap extension of the double and passes canonical microstates both ways by an explicit two-block construction; this reaches the same m = 2 conclusion from the OTHER side (from a model of the HNN group, not of the double) and yields every finite order m simultaneously from one Haar letter, where the block construction would need an m-fold amalgam power for each m.
  sl3-arithmetic-double-embeds-in-centralizer-hnn: that embeds the double A *_C A into the centralizer HNN group, which combined with the swap identification already gives the m = 2 instance of this transfer at the group level; this is the von Neumann form -- a spectral function of the letter, not a subgroup -- and it produces the order-m letter freely for all m at once, including orders with no embedded amalgam-power avatar recorded in the graph.
---

**THEOREM (established here; proof in
`hnn-stable-letter-rounding-proof`).**  Let `C <= A` be countable groups,
and for `m >= 2` let

```text
G      = < A, t | [t, C] = 1 >          = A *_C (C x Z),
E_m    = < A, s | s^m = 1, [s, C] = 1 > = A *_C (C x C_m).
```

If `G` is hyperlinear then so is `E_m`, for every `m` at once: in any
matrix-ultraproduct model of `G`, the sector function `f_m` of the Haar
stable letter is an EXACT unitary of order `m` in the `L(C)`-centraliser,
centered, balanced (`tau(s^r) = 0` for `r` not divisible by `m`), and
free from `L(A)` with amalgamation over `L(C)`.  There is no
approximation loss, no dimension change and no block doubling: the
order-`m` letter is a Borel function of the Haar letter on the same
space.

For `m = 2` the conclusion also follows at the group level by composing
`sl3-arithmetic-double-embeds-in-centralizer-hnn` with the swap
identification `(DSW4)` of
`arithmetic-double-swap-extension-is-binary-coset-wreath`; the content
here is the uniform-in-`m` von Neumann mechanism and its consequence:
one Haar enemy manufactures a coherent FAMILY `(f_m(k))_(m >= 2)` of
finite-order enemies with commuting values, all functions of one
unitary.

**Consequence for the goal architecture.**  The contrapositive turns the
binary swap group into the universal receiver of the lane: if
`E_2 = A *_C (C x C_2)` is not hyperlinear then neither is `G`, and
`E_2` is itself a finitely presented goal witness whenever `A` is
finitely presented and `C` finitely generated.  The enemy of `E_2` is a
single self-adjoint unitary `s` with

```text
s in L(C)' cap M,   tau(s) = 0,   E_(L(C))(s) = 0,
(L(A), W*(L(C), s)) free with amalgamation over L(C),          (IL1)
```

equivalently one projection `q = (1+s)/2` of trace `1/2` commuting with
the subgroup image whose `A`-translates are trace-independent:
`tau(q a_1 q a_2 ... q a_j) = 2^(-j) tau(a_1 ... a_j)` on words with
letters `a_i in A - C`.

## Attempts

- **Can the involution rebuild the Haar letter?  A descent structure,
  not a converse.**  One involution generates only `C_2`.  But inside a
  model of `E_2` for the arithmetic pair, `s` and `u_h s u_h^*` are
  free self-adjoint unitaries (alternating words reduce in the amalgam),
  so `z = s u_h s u_h^*` is distributed as the generator product of
  `C_2 * C_2 = D_infinity`: a HAAR unitary.  And `z` commutes with the
  group image of `C_0 = C cap hCh^(-1)`, a finite-index congruence
  subgroup that is again co-dense in `A` by strong approximation.  So an
  involution enemy over `(C, A)` appears to manufacture a Haar enemy
  over the deeper co-dense pair `(C_0, A)` -- an infinite descent
  through the congruence lattice which no stability hypothesis sees.
  What is NOT yet verified is the amalgamated freeness of
  `(L(A), W*(L(C_0), z))` over `L(C_0)`, equivalently the marked
  subgroup identification `<A, z> ~= A *_(C') (C' x Z)` inside `E_2`
  with `C'` the exact centraliser; the sample cancellations checked so
  far all terminate harmlessly, and a Bass--Serre argument on the
  `E_2`-tree is the natural proof.  Until that is done the descent is a
  direction, not a theorem.
- **Why not amplify to two mutually free involutions instead?**
  Producing a second involution free from the first over the
  NON-amenable `L(C)` is exactly the relative free-independence
  statement that Popa's theorem (arXiv:1308.3982) provides over amenable
  cores and that is open beyond them, as recorded in
  `hnn-hyperlinearity-is-amalgamated-free-haar-unitary`.  The descent
  bullet above is the substitute: it extracts the second free involution
  from the `h`-translate that the group structure already provides.
