undef $/; $_ = <STDIN>;
s/\(lane\nproof, not independently reviewed; referee requests sent\)/(lane\nproof; refereed PASS by `gq-referee-a`, proof gaps, `gq-referee-a-register-comparison-presentations-are-not-simple.md`, b82951dcd; the citation and\nscope review by `gq-referee-b` is pending)/;
s/(  fp-simple-resolvent-ring-with-divisible-unit-class: [^\n]*\n)---/$1artifacts:\n  - research\/artifacts\/gq-referee-a-register-comparison-presentations-are-not-simple.md\n---/;
print;
