undef $/; $_ = <STDIN>;
s/\(lane proof, not\nindependently reviewed; referee requests sent\)/(lane proof; refereed PASS by `gq-referee-a`, proof gaps,\n`gq-referee-a-capacity-chain-presentation-is-not-simple.md`, b7958da79)/;
s/(  resolvent-vacuum-rings-have-no-k0-state: [^\n]*\n)---/$1artifacts:\n  - research\/artifacts\/gq-referee-a-capacity-chain-presentation-is-not-simple.md\n---/;
s/\*\*Lesson\.\*\* /**Lesson (heuristic, for relations of this shape).** /;
print;
