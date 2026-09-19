# Lane bh-houghton-presentation, run 2 (run 1 calibrated; this repeats it): calibration + bounded forward/backward closure search.
# c(g) := nu*g*nu^-1 in GAP's right-action convention, i.e. n -> g(n+1)-1.
LoadPackage("rcwa");
out := OutputTextFile("/projects/standard/hsiehph/sauer354/gqsrc/bh-houghton-presentation/run2.out", false);
SetPrintFormattingStatus(out, false);
P := function(arg) CallFuncList(PrintTo, Concatenation([out], arg, ["\n"])); CallFuncList(Print, Concatenation(arg, ["\n"])); end;
t0 := Runtime();
HASLT := ApplicableMethod(\<, [ClassShift(0,1), ClassShift(0,2)]) <> fail;
nu := ClassShift(0,1);
c := g -> nu * g * nu^-1;
ci := g -> nu^-1 * g * nu;
# --- calibration ---
tau := ClassTransposition(1,2,2,4);
P("cal: 3^tau = ", 3^tau, " (expect 6);  (-2)^c(tau)... 2^c(tau) = ", 2^c(tau), " (expect 2*2+1 = 5)");
x := [tau]; for k in [1..6] do Add(x, c(x[k])); od;   # x[k+1] = x_k
P("cal: x_2 maps 3 to ", 3^x[3], " (expect 2*3+2 = 8)");
P("cal: (x_0*x_2)^3 = 1 ? ", IsOne((x[1]*x[3])^3), " ; x_0*x_2 = 1 ? ", IsOne(x[1]*x[3]));
alpha := ClassShift(1,2) * ClassShift(0,2)^-1;
P("cal: c(alpha) = alpha^-1 ? ", c(alpha) = alpha^-1);
P("cal: c(x_0) = x_1 ? ", c(x[1]) = x[2], " ; c^-1(x_1) = x_0 ? ", ci(x[2]) = x[1]);
# --- bounded search ---
# For a seed g and L, test whether c^(L+1)(g) and c^-1(g) lie in the ball of <g, c(g), ..., c^L(g)>.
ClosureSearch := function(name, g, L, maxel, maxmod)
  local gens, tgtF, tgtB, k, ball, frontier, new, e, s, h, foundF, foundB, i;
  gens := [g]; for k in [1..L] do Add(gens, c(gens[k])); od;
  tgtF := c(gens[L+1]); tgtB := ci(g);
  ball := [One(g)]; frontier := [One(g)]; foundF := false; foundB := false;
  while Length(frontier) > 0 and Length(ball) < maxel and Runtime() - t0 < 480000 do
    new := [];
    for e in frontier do
      for s in gens do
        for h in [e*s, e*s^-1] do
          if Modulus(h) <= maxmod and ((HASLT and not h in ball) or (not HASLT and Position(ball, h) = fail)) then
            if HASLT then AddSet(ball, h); else Add(ball, h); fi; Add(new, h);
            if h = tgtF then foundF := true; fi;
            if h = tgtB then foundB := true; fi;
          fi;
        od;
      od;
    od;
    frontier := new;
  od;
  P(name, " L=", L, " ball=", Length(ball), " forward c^(L+1)(g) found: ", foundF,
    " backward c^-1(g) found: ", foundB, " t=", Runtime()-t0, "ms");
end;
seeds := [ ["CT(1,2,2,4)", ClassTransposition(1,2,2,4)], ["CT(0,2,1,4)", ClassTransposition(0,2,1,4)],
           ["CT(1,2,0,4)", ClassTransposition(1,2,0,4)], ["CT(0,2,3,4)", ClassTransposition(0,2,3,4)],
           ["CT(1,3,0,6)", ClassTransposition(1,3,0,6)], ["CT(0,3,1,6)", ClassTransposition(0,3,1,6)] ];
for sd in seeds do
  for L in [1,2,3] do
    if Runtime() - t0 < 480000 then ClosureSearch(sd[1], sd[2], L, 4000, 2^10); fi;
  od;
od;
P("done t=", Runtime()-t0, "ms");
CloseStream(out);
QUIT;
