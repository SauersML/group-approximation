undef $/; $_ = <STDIN>;
s/\(lane proof, elementary; inputs are Baumslag's wreath product theorem and item 1 of\n`prime-shift-hnn-groups-are-not-finitely-presented`; referee requests sent\)/(lane proof, elementary; inputs are Baumslag's wreath product theorem and item 1 of\n`prime-shift-hnn-groups-are-not-finitely-presented`; refereed PASS by `gq-referee-a`,\nproof gaps, `gq-referee-a-prime-shift-affine-group-a1-is-not-finitely-presented.md`;\nreview by `gq-referee-b` pending)/;
s/(  prime-shift-hnn-map-to-a1-is-injective: [^\n]*\n)---/$1artifacts:\n  - research\/artifacts\/gq-referee-a-prime-shift-affine-group-a1-is-not-finitely-presented.md\n---/;
print;
