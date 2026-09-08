# The projective ring host retains the presentation problem

The projective ring route remains open. Its finite-presentation requirement
can now be expressed exactly as two pieces of generating data: finite
normal generators of the unstable Steinberg kernel, and finite generators
of the elementary group's center. Projectivization does not make either
requirement disappear.

## Exact criterion

For a finitely presented unital ring R and n>=4, put E=EL_n(R),
P=E/Z(E), and K=ker(St_n(R)->E). Then

    P finitely presented
      iff E finitely presented and Z(E) finitely generated
      iff K finitely normally generated in St_n(R)
          and Z(E) finitely generated.

The new ingredient in this region of Cairn is the standard upward
central-extension fact: if E is finitely generated and E/C is finitely
presented for central C, then C is finitely generated and E is finitely
presented. To see why C is finitely generated, present E/C on images of
a finite generating set of E. The finitely many quotient relators become
central elements generating C; conjugating them contributes no further
generators. A finite abelian presentation of C, centrality relations and
the lifted quotient relators give a finite presentation of E.

This standard implication is explicitly used in Daniel Allcock,
[*Steinberg groups as amalgams*](https://web.ma.utexas.edu/users/allcock/research/steinberg.pdf),
printed page 1841, proof of Theorem 1.4(i). Cairn includes a self-contained
presentation argument in `fg-central-extension-finite-presentation-proof`.
No novelty is claimed for this central-extension fact.

The source St_n(R) is finitely presented by the previously checked
Steinberg theorem, so E is finitely generated. The ordinary quotient-kernel
criterion now supplies the second equivalence. No assumption that K is
central enters the proof. In particular, finite normal generation in the
Steinberg group cannot be replaced by abstract finite generation of K
using an unproved unstable-centrality assertion.

## Simplicity imposes a separate ring condition

If EL_n(R)/Z(EL_n(R)) is nontrivial simple for a nonzero unital R and
n>=3, then R must be simple. Indeed a nonzero proper ideal I gives a
normal congruence kernel C containing a noncentral root e_12(a), a!=0.
Projective simplicity would force E=CZ(E). Reduction modulo I would then
make EL_n(R/I) abelian. It is nontrivial and perfect, a contradiction.

This is only a necessary condition. The argument does not establish the
converse for arbitrary simple rings or prove any finite-presentation
property from ring simplicity.

## Integration and the remaining task

The open claim `decidable-group-ring-has-fp-projective-simple-host` now
states its finite-presentation clause in the equivalent form of explicit
kernel and center generating data. The conditional route
`boone-higman-via-projective-ring-host` uses
`projective-elementary-fp-kernel-criterion` to recover the finitely
presented projective target. Its embedding and simplicity requirements
are unchanged.

A successful construction still has to supply, for every relevant H:

1. A finite ring presentation L and an injection Z[H]->L.
2. Finite normal generators of ker(St_4(L)->EL_4(L)).
3. Finite group generators of Z(EL_4(L)).
4. A proof that EL_4(L)/Z(EL_4(L)) is simple.

These are equivalent to the previous host requirement, not a weaker
substitute. No such universal construction is supplied here. The other
maximal-kernel and action-image routes also remain open.

The arguments above are prose mathematics. Cairn's automated check
validates their graph integration, not an independent formal proof of
these arguments. The earlier Lean replay covered double-coset separation
only. No GPU ran in this analysis and no Civo resources were provisioned.
