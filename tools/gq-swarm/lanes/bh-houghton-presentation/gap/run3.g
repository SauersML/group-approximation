# Lane bh-houghton-presentation, run 3 of 3: targeted search for a Thompson-F prototype inside RCWA+(Z).
# c(g) := nu*g*nu^-1 (right action: n -> g(n+1)-1).  F-prototype: y of index 0 with
#   c(y)^y = c^2(y)  and  c^2(y)^y = c^3(y)  and  y*c(y) <> c(y)*y.
# Calibrations on the same candidate list: relA c(y) = y^-1 (expected hits, e.g. slides);
#   relP c(y) = y^2 or y^-2 with y <> 1 (lemma no-nontrivial-germ-is-shift-conjugate-to-a-proper-power predicts 0 hits).
LoadPackage("rcwa");
out := OutputTextFile("/projects/standard/hsiehph/sauer354/gqsrc/bh-houghton-presentation/run3.out", false);
SetPrintFormattingStatus(out, false);
P := function(arg) CallFuncList(PrintTo, Concatenation([out], arg, ["\n"])); CallFuncList(Print, Concatenation(arg, ["\n"])); end;
t0 := Runtime();
nu := ClassShift(0,1);
c := g -> nu * g * nu^-1;
cps := ClassPairs(4);
cts := List(cps, ClassTransposition);
slides := List(cps, p -> ClassShift(p[1],p[2]) * ClassShift(p[3],p[4])^-1);
G0 := Concatenation(cts, slides, List(slides, s -> s^-1));
P("generators: ", Length(cts), " class transpositions, ", Length(slides), " slides (+inverses); |G0| = ", Length(G0));
cands := ShallowCopy(G0);
for a in G0 do for b in G0 do Add(cands, a*b); od; od;
small := List(ClassPairs(3), ClassTransposition);
for a in small do for b in small do for d in small do Add(cands, a*b*d); od; od; od;
P("candidates: ", Length(cands));
nA := 0; nP := 0; nF := 0; nFmirror := 0; tested := 0;
for y in cands do
  if Runtime() - t0 > 520000 then break; fi;
  tested := tested + 1;
  if IsOne(y) then continue; fi;
  y1 := c(y);
  if y1 = y^-1 then nA := nA + 1; if nA <= 3 then P("relA hit: ", y); fi; fi;
  if y1 = y^2 or y1 = y^-2 then nP := nP + 1; P("relP HIT (contradicts lemma!): ", y); fi;
  if Modulus(y) <= 64 then
    y2 := c(y1);
    if y1^y = y2 and not IsOne(Comm(y, y1)) then
      y3 := c(y2);
      if y2^y = y3 then nF := nF + 1; P("F-PROTOTYPE HIT: y = ", y); fi;
    fi;
    # mirror direction (c^-1): would give c^-1(B) strictly inside B, the wrong direction; recorded only.
    z1 := nu^-1 * y * nu; z2 := nu^-1 * z1 * nu;
    if z1^y = z2 and not IsOne(Comm(y, z1)) then
      z3 := nu^-1 * z2 * nu;
      if z2^y = z3 then nFmirror := nFmirror + 1; if nFmirror <= 3 then P("mirror F hit: y = ", y); fi; fi;
    fi;
  fi;
od;
P("tested ", tested, " of ", Length(cands), " candidates; relA hits ", nA, "; relP hits ", nP,
  "; F-prototype hits ", nF, "; mirror hits ", nFmirror, "; t=", Runtime()-t0, "ms");
CloseStream(out);
QUIT;
