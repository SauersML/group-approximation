# Independent GAP count of odometer models of H4(3) (optionally with [a,c]^2) in W_k, k = 1..KMAX.
# Points 1..2^k stand for x = 0..2^k-1; the tree is the 2-adic one (vertex of level r = x mod 2^r).
# a = x -> x+1. Enumerates d in C_W(a)*g, c in C_W(d)*h, b in C_W(c)*y and keeps b^a = b^3.
# Expected (lift.py/rawcount.py): with R: 8, 32, 192, 1536, 11776, 0 ; without R: 8, 32, 288, 4352.
Tree := function(k)
  local N, gens, r, v, L;
  N := 2^k; gens := [];
  for r in [0..k-1] do for v in [0..2^r-1] do
    L := List([0..N-1], function(x) if x mod 2^r = v then return ((x + 2^r) mod 2^(r+1)) + 2^(r+1)*QuoInt(x, 2^(r+1)) + 1; else return x+1; fi; end);
    Add(gens, PermList(L));
  od; od;
  return Group(gens);
end;
Count := function(k, withR)
  local W, a, g, d, h, c, y, b, n, Cd, Cc, cnt;
  W := Tree(k); a := PermList(List([0..2^k-1], x -> ((x+1) mod 2^k) + 1));
  g := RepresentativeAction(W, a, a^3); cnt := 0;
  for d in RightCoset(Centralizer(W, a), g) do
    h := RepresentativeAction(W, d, d^3);
    if h <> fail then
      for c in RightCoset(Centralizer(W, d), h) do
        if (not withR) or Comm(a, c)^2 = () then
          y := RepresentativeAction(W, c, c^3);
          if y <> fail then
            for b in RightCoset(Centralizer(W, c), y) do
              if b^a = b^3 then cnt := cnt + 1; fi;
            od;
          fi;
        fi;
      od;
    fi;
  od;
  return cnt;
end;
for k in [1..KMAX] do Print("k=", k, " withR ", Count(k, true), "\n"); od;
for k in [1..KMAXNOR] do Print("k=", k, " noR ", Count(k, false), "\n"); od;
QUIT;
