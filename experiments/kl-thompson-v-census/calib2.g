Read("klcx.g");
Tst := function(name, s, expect, maxc) local t0, r;
  t0 := Runtime();
  r := Collapse(s, maxc);
  Print(name, " word=", s, " result=", r, " expect=", expect, " maxc=", maxc, " ms=", Runtime() - t0, "\n");
end;;
# C6 positive control needing the long Bleak--Quick relators: t(ab)T = c forces (ab)^2 = 1.
#    (ab)^2 != 1 in V and V is simple, so V dies and V_w = <t>: expect index 1.
Tst("C6", "tabTc", 1, 2000000);
# C7 positive control: t(ab)^2 T = b forces an involution conjugate to an order-3 element.
Tst("C7", "tababTB", 1, 2000000);
# C8 positive control: t(bc) T = a ; bc has order? if order != 2 this kills V (checked by expect=1 only
#    when the enumeration closes; the verdict is recorded, not assumed).
Tst("C8", "tbcTa", "record", 2000000);
# C9 negative control at the production budget: degree 1, full support {a,b,c}, fenced by r>=4 light corners? no:
#    a census-shape word; expect overflow at 200000.
Tst("C9", "atbTctatBTctcT", "overflow", 200000);
QUIT;
