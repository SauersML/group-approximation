# Greedy minor-minimisation.  Deletion (x_e -> 1) and contraction (x_e -> product of
# the other generators at one endpoint, times a power of J) are surjections
# Gamma_p(G,b) -> Gamma_p(minor,b') fixing J, so survival of J in a p-quotient of
# class <= c passes UP from a minor to the graph.  We search DOWN for a minimal one.
OnBreak := function() FORCE_QUIT_GAP(3); end;
Read("pq.g"); Read("graphs.g");
Survives := function(nv, E, p, c)
  local G, ne, hom;
  if Length(E) = 0 then return false; fi;
  G := SolGroup(nv, E, p, [1]); ne := G[2]; G := G[1];
  hom := EpimorphismPGroup(G, p, c);
  return not IsOne(Image(hom, GeneratorsOfGroup(G)[ne+1]));
end;
Normalise := function(nv, E)   # drop loops, relabel vertices 1..k, drop isolated vertices
  local used, map, F;
  F := Filtered(E, e -> e[1] <> e[2]);
  used := Set(Flat(F));
  map := function(v) return Position(used, v); end;
  return [Length(used), List(F, e -> [map(e[1]), map(e[2])])];
end;
Contract := function(nv, E, i)
  local u, w, F;
  u := E[i][1]; w := E[i][2];
  F := List(E{Difference([1..Length(E)], [i])}, e -> List(e, function(v) if v = w then return u; else return v; fi; end));
  return Normalise(nv, F);
end;
Delete := function(nv, E, i)
  return Normalise(nv, E{Difference([1..Length(E)], [i])});
end;
Minimise := function(nv, E, p, c)
  local changed, i, H, gr, v;
  gr := Normalise(nv, E);
  if not Survives(gr[1], gr[2], p, c) then Print("start graph does not survive\n"); return fail; fi;
  repeat
    changed := false;
    for i in [1..Length(gr[2])] do
      H := Delete(gr[1], gr[2], i);
      if Survives(H[1], H[2], p, c) then gr := H; changed := true; Print("  delete -> V=", gr[1], " E=", Length(gr[2]), "\n"); break; fi;
    od;
    if not changed then
      for i in [1..Length(gr[2])] do
        H := Contract(gr[1], gr[2], i);
        if Survives(H[1], H[2], p, c) then gr := H; changed := true; Print("  contract -> V=", gr[1], " E=", Length(gr[2]), "\n"); break; fi;
      od;
    fi;
  until not changed;
  Print("minimal (for p=", p, ", class<=", c, "): V=", gr[1], " E=", Length(gr[2]), " degrees ", List([1..gr[1]], v -> Number(gr[2], e -> v in e)), "\n  edges ", gr[2], "\n");
  return gr;
end;
