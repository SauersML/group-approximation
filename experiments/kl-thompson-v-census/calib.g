Read("klcx.g");
Tst := function(name, s, expect, maxc) local t0, r;
  t0 := Runtime();
  r := Collapse(s, maxc);
  Print(name, " word=", s, " result=", r, " expect=", expect, " ms=", Runtime() - t0, "\n");
end;;
# C1 positive control, degree 0: t a T = b forces b^2 = b^3 = 1, so b = 1 and V dies;
#    V_w = <t>, index 1.
Tst("C1", "taTB", 1, 400000);
# C2 positive control, degree 0: t a T = c b c forces an involution conjugate to an order-3 element.
Tst("C2", "taTcBc", 1, 400000);
# C3 negative control, degree 1 with coefficients in S4 = <a,b>: injects (finite coefficients); expect overflow.
Tst("C3", "atbTatBt", "overflow", 100000);
# C4 negative control, degree 1 with coefficients in S3 = <a,c>: expect overflow.
Tst("C4", "atcTatct", "overflow", 100000);
# C5 timing on a census-shape word (degree 1, variable length 7, mixed letters): expect overflow.
Tst("C5", "atbTctatBTctcT", "overflow", 100000);
QUIT;
