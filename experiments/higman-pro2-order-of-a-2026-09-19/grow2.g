# grow2.g: truncated 2-quotient algorithm for G = H4(3)/<<[a,c]^2>> (plus optional EXTRA relators).
# Runs GAP's own p-quotient loop (lib/pquot.gi), but after the relators of each new layer are known it adds
# extra central relations killing a random complement of a KEEP-dimensional part of the new layer.  The part
# kept always contains the new-layer values t_x of x^ord(x) for the generators x (when nonzero), so every
# generator whose order would double in the full class-(cl) quotient still doubles.  Each group produced is the
# quotient of the full class-cl 2-quotient by a central subgroup, hence a finite 2-quotient of G: ord(a) in it
# is a certified lower bound for ord(a) in the 2-quotients of G.  At the end the relators are re-checked in
# the resulting pc group and the orders recomputed there from scratch.
# The class loop is in loop2.g; with CKPT:=true it saves a workspace NAME.ws after each class, and
# `gap -L NAME.ws loop2.g` resumes (run3.sh does this under repeated 1200 s timeouts).
# usage: gap -q -o 2g -c 'EXTRA:=function(a,b,c,d) return []; end;; KEEP:=60;; SEED:=1;; MAXCL:=30;; NAME:="x";;' grow2.g
F := FreeGroup("a","b","c","d"); a:=F.1; b:=F.2; c:=F.3; d:=F.4;
rels := Concatenation([ b^a/b^3, c^b/c^3, d^c/d^3, a^d/a^3, Comm(a,c)^2 ], EXTRA(a,b,c,d));
G := F / rels;
Reset(GlobalMersenneTwister, SEED); t0 := Runtime();
if not IsBound(PRIO) then PRIO := [1,2,3,4]; fi;
qs := QuotientSystem(G, 2, 8192, "combinatorial");
AbelianPQuotient(qs);
ords := [2,2,2,2];   # generator orders in the current quotient (class 1: all 2, checked below)
TailOfPower := function(qs, i, e)
  local n, c, v;
  n := GeneratorNumberOfQuotient(qs); c := qs!.numberOfHighestWeightGenerators;
  v := ListWithIdenticalEntries(n+c, 0);
  while CollectWordOrFail(qs!.collector, v, qs!.images[i]^e) = fail do od;
  if ForAny(v{[1..n]}, x -> x <> 0) then Error("power not in new layer"); fi;
  return v{[n+1..n+c]} * One(GF(2));
end;
cl := 1;
Read("loop2.g");
