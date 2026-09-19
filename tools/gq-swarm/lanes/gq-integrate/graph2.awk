FNR==1 { if (id!="") flush(); id=""; kind=""; tgt=""; root=0; fm=0; inreq=0; req=""; status=""; after=0; inv=""; ininv=0 }
FNR==1 && $0=="---" { fm=1; next }
fm && $0=="---" { fm=0; after=1; next }
fm { if ($1=="id:") id=$2; else if ($1=="kind:") kind=$2; else if ($1=="target:") tgt=$2; else if ($1=="root:" && $2=="true") root=1;
     if ($1=="invalidates:") { ininv=1; inreq=0; if (NF>1 && $2!="[]") { line=$0; sub(/^invalidates:[[:space:]]*/,"",line); gsub(/[\[\],]/," ",line); inv=inv " " line } next }
     if ($1=="requires:") { inreq=1; ininv=0; if (NF>1 && $2!="[]") { line=$0; sub(/^requires:[[:space:]]*/,"",line); gsub(/[\[\],]/," ",line); req=req " " line } next }
     if (inreq && $0 ~ /^[[:space:]]+-[[:space:]]/) { req=req " " $2; next }
     if (ininv && $0 ~ /^[[:space:]]+-[[:space:]]/) { inv=inv " " $2; next }
     if ($0 ~ /^[^[:space:]]/) { inreq=0; ininv=0 } next }
!fm && after && status=="" && NF { status=($0 ~ /^\*\*(ESTABLISHED|Established)/) ? "E" : (($0 ~ /^\*\*(REFUTED|Refuted)/) ? "R" : "O"); after=0 }
function flush() { if (kind=="route") print "R", id, tgt, req; else if (kind=="claim") print "C", id, root, status, "INV" inv }
END { flush() }
