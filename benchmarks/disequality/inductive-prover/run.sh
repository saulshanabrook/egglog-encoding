echo "file,ee_node_num,ee_class_num,ee_time,de_node_num,de_class_num,de_time"

for f in /inductive-prover/benchmarks/propel/tip_*; do
  ee=$({ time timeout 60s propel -f $f --variant ee; } 2>&1)
  de=$({ time timeout 60s propel -f $f --variant de; } 2>&1)

  node_num_ee=$(echo "$ee" | grep "^sum" | cut -f 3 -d ';')
  class_num_ee=$(echo "$ee" | grep "^sum" | cut -f 4 -d ';')
  time_ee=$(echo "$ee" | grep "^real" | cut -f 2)

  node_num_de=$(echo "$de" | grep "^sum" | cut -f 3 -d ';')
  class_num_de=$(echo "$de" | grep "^sum" | cut -f 4 -d ';')
  time_de=$(echo "$de" | grep "^real" | cut -f 2)

  echo "$f,$node_num_ee,$class_num_ee,$time_ee,$node_num_de,$class_num_de,$time_de"
done
