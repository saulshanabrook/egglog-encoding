echo "method,file,status,egraph setup time,full time,sat solution,nodes,classes,sat time,egraph time"

for f in $(find /euf-solver/benchmarks/smt-uf-non-incremental/ -name "*.smt2"); do
  timeout 1s /euf-solver/target/release/euf-solver -s "$f" | tail -n +2 | sed -e 's/^/ee,/'
done

for f in $(find /euf-solver/benchmarks/smt-uf-non-incremental/ -name "*.smt2"); do
  timeout 1s /euf-solver/target/release/euf-solver -s -d "$f" | tail -n +2 | sed -e 's/^/de,/'
done
