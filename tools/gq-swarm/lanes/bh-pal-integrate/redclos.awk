# usage: awk -v T=<module> -f redclos.awk failed.txt edges.txt  -> prints closure size and red modules in closure
FNR==NR { red[$1]=1; next }
{ adj[$1]=adj[$1] " " $2 }
END {
  q[1]=T; seen[T]=1; h=1; t=1
  while (h<=t) { m=q[h++]; n=split(adj[m], a, " "); for (i=1;i<=n;i++) if (!(a[i] in seen)) { seen[a[i]]=1; q[++t]=a[i] } }
  r=""; c=0; for (m in seen) if (m in red) { c++; s=m; sub(/^GroupApproximation\.(BooneHigman\.Metabelian|Manuscript\.SimpleKazhdanSofic)\./,"",s); r=r " " s }
  printf "closure=%d red=%d%s\n", t, c, r
}
