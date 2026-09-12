# Why rank-two Garland expansion does not close the dyadic SL3 action fork

The moving charts in a GKEP sofic model can be one-hot encoded.  In the
Hilbert ultraproduct this gives orthonormal vectors indexed by `A/C`, with
the exact quasi-regular action.  The base vector is `C`-fixed and is moved
orthogonally by every `h` outside `C`.

The associated displacement cochain is

```text
b(a)=pi(a)delta_C-delta_C=delta_0(delta_C)(a).
```

It is already an exact coboundary.  Hence:

- property `(T)` / `H^1=0` is satisfied, not contradicted;
- on the two-dimensional affine building, its triangle curl is exactly
  `delta_1 delta_0(delta_C)=0`;
- a Garland cofilling inequality measuring distance to coboundaries has
  value zero on this cochain;
- degree-zero Poincare expansion merely confirms that the base vector has
  positive displacement from the `A`-invariant space.

Thus local spectral expansion cannot promote the exact-action co-density
identity to approximate actions.  The required new input is relative
invariant transfer on the restricted class of permutation-ultraproduct
representations, or equivalently exclusion of the quasi-regular packet
that a sofic atlas would create.  This is stronger than ordinary
cohomology vanishing.

