# Extra simple targets for the follow-up on OPEN classes of the L = 16, 17 run.
# Read AFTER bal.g (or certs.g, which reads bal.g): it only appends to TARGETS, so Classify and CertFor
# keep their verdict semantics ("SIMPLE q=<name>": an epimorphism onto the named group exists).
Append(TARGETS, [ ["PSL(2,27)", PSL(2,27)], ["PSL(2,29)", PSL(2,29)], ["PSL(2,31)", PSL(2,31)],
  ["PSL(2,32)", PSL(2,32)], ["PSL(2,37)", PSL(2,37)], ["PSL(2,41)", PSL(2,41)],
  ["PSL(2,43)", PSL(2,43)], ["PSL(2,47)", PSL(2,47)], ["PSL(2,49)", PSL(2,49)],
  ["PSL(3,4)", PSL(3,4)], ["PSU(3,4)", PSU(3,4)], ["PSp(4,3)", PSp(4,3)],
  ["Sz(8)", SuzukiGroup(IsPermGroup, 8)], ["A9", AlternatingGroup(9)],
  ["PSL(3,5)", PSL(3,5)], ["M12", MathieuGroup(12)] ]);;
