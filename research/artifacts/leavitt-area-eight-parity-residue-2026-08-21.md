# The exact parity-breaking residue at area eight

The curvature-first eight-cell audit leaves no even-region diagram.  Its 36
shortest length-eight residual coefficient words are nontrivial after the
substitutions

```text
h_1=q_0p_1,   k_2=p_0e_1
```

and free-product/root reduction.  Therefore any remaining diagram must use
an odd coefficient identity.

No length-one label is trivial.  No length-three word is trivial either:
without a bridge it lies in the free product of the two `V_4` gate groups;
with a bridge, a `p_0` or `p_1` syllable survives, except when inverse
bridges enclose one gate, which leaves a conjugate of that nontrivial gate.
Thus an odd internal identity starts at length five.

For eight trivalent vertices the six face lengths total 24.  Odd faces come
in pairs.  If two or more INTERNAL faces are odd, at least one has length at
most seven: two lengths at least nine, three remaining internal lengths at
least two, and an outer length at least two would already total 26.  If only
one internal face is odd, the outer face supplies the parity mate and the
internal length can only be

```text
5, 7, 9, 11, 13, or 15.
```

This identifies the next symbolic calculation exactly.  First classify
length-five and length-seven corner identities.  If neither exists, every
multi-odd-face eight-cell picture is impossible; only the exceptional
one-odd-internal-face configurations of lengths 9 through 15 remain.

There is no formal global parity shortcut.  The four coefficient packets
generate the perfect Leavitt elementary group, so a homomorphism sending
every corner label to the nonzero class in `Z/2` cannot extend to the actual
coefficient subgroup.  Any final area-ten proof must use short root/Leavitt
normal forms, not an asserted parity character.
