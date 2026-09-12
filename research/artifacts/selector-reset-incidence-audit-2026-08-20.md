# Selector-reset incidence audit — 2026-08-20

## Question

After the Fanizza radical chart is restricted to its common symplectic
subgroup, can one renew the Boolean selector tuple merely by sharing that spin
subgroup and adjoining fresh selector characters?

## Exact answer

No.  If `sigma` is the unique common spin type, both old chart types restrict
as one copy of `sigma`.  The two extensions obtained from one fresh Boolean
selector do the same.  Hence both restriction matrices are `[1 1]`, and the
entire incidence equation is

```text
m_-^old + m_+^old = m_-^fresh + m_+^fresh.
```

For every pair of signs, the old and fresh representations can be put on the
same spin space with literally equal action on the shared subgroup.  The
universal property of the amalgam then supplies an exact representation.
Thus all four sign pairs occur.  With `k` selector bits, all `2^(2k)` pairs of
old and fresh characters occur.

The executable certificate is
`experiments/selector_reset_commutant_freedom.py`.  It prints the restriction
matrices and exhausts the exact character pairs for one through four bits.

## Consequence for the live route

The common symplectic reset genuinely removes the four-branch Morita mismatch
and preserves the spin scale.  It does not carry the Fanizza semantics to the
next context.  Stable symplectic congruence, private old-center padding, and
fresh abelian selectors cannot finish the return unless an additional cell
acts nontrivially on the spin multiplicity commutant.  The remaining search is
therefore for a matrix-valued two-cell or compressor, not another ordinary
finite-group restriction edge.

Recorded nodes:

- `selector-free-spin-reset-leaves-contexts-independent` (established),
- `selector-free-spin-reset-independence-proof` (proof route),
- updated `fresh-selector-renewal-after-symplectic-chart-reset` (open).
