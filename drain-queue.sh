#!/usr/bin/env bash
# Submit queued Aristotle jobs while slots are free.
# Usage: drain-queue.sh [max_to_submit]
set -u
QUEUE=/home/kim/erdos-unit-distance/aristotle-queue.txt
TSV=/home/kim/erdos-unit-distance/aristotle-projects.tsv
MAX=${1:-15}
count=0
while [ $count -lt $MAX ]; do
  n=$(head -1 "$QUEUE" 2>/dev/null)
  [ -z "$n" ] && { echo "queue empty"; break; }
  d=/tmp/aristotle-jobs/$n
  [ -d "$d" ] || { echo "missing project dir $d"; break; }
  prompt="Replace the sorry in theorem \`Erdos.$n\` with a complete proof. Its doc comment contains a proof sketch. Keep its statement and all other declarations exactly as they are. Any other sorried theorems in the file are intermediate results of a larger project and are being proven separately: you may use them freely as known results, but do not prove them, do not modify them, and do not introduce axioms or new sorries. This file is part of a formalization of Alpöge's 2026 disproof of the uniform-constant form of the Erdős unit-distance conjecture."
  out=$(aristotle submit "$prompt" --project-dir "$d" 2>&1)
  id=$(echo "$out" | grep -o 'Project created: [a-f0-9-]*' | awk '{print $3}')
  if [ -z "$id" ]; then
    echo "submit failed for $n: $(echo "$out" | tail -1)"
    break
  fi
  echo -e "$id\t$n" >> "$TSV"
  sed -i '1d' "$QUEUE"
  echo "submitted $n -> $id"
  count=$((count+1))
  sleep 3
done
