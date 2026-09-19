undef $/; $_ = <STDIN>;
s/; the\ncitation review by `gq-referee-b` is pending\)/, and by `gq-referee-b`, citations and hypotheses,\n`gq-referee-b-resolvent-vacuum-rings-have-no-k0-state.md`, 9a2dd39e7)/;
s/(  - research\/artifacts\/gq-referee-a-resolvent-vacuum-rings-have-no-k0-state.md\n)/$1  - research\/artifacts\/gq-referee-b-resolvent-vacuum-rings-have-no-k0-state.md\n/;
s/In particular `R` carries no trace or dimension\n     function normalized at `1`\./In particular `R` carries no trace or dimension\n     function normalized at `1` that is nonnegative on the idempotents of all matrix\n     rings `M_k(R)`. Positivity on those idempotents is what makes it a state./;
s/But the host must be stateless, of the\n  type `O_∞ ⊗ UHF_Q`:/But the host must be stateless. Heuristically it is of the\n  type `O_∞ ⊗ UHF_Q`:/;
print;
