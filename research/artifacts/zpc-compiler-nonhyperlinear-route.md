# Perfect-strategy ZPC compiler route (invalidated)

Former Cairn route `zpc-compiler-nonhyperlinear-route`, demoted because
perfect-strategy exclusion does not imply a strict quantum-value gap.

Apply `zpc-selector-sound-lcs-compiler` to the finite tailored game `G` from
`perfect-zpc-irs-quantum-gap-game`. Perfect ZPC-IRS completeness gives a
perfect commuting strategy for `L(G)`. If `L(G)` had a perfect
finite-dimensional strategy, sound decoding would produce a perfect
finite-dimensional strategy for `G`, contradicting `omega*(G)<1/2`. Hence
`L(G)` has commuting value one and finite-dimensional quantum value below one.
`perfect-lcs-gap-implies-nonhyperlinear` then gives a nonhyperlinear solution
group.

The predication claim records that controlled linear equations themselves are
no longer the unknown part of the compiler; selector soundness is.
