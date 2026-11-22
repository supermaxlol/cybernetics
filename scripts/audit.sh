#!/bin/sh
# Rebuild everything and print the axioms each audited theorem depends on.
set -e
lake exe cache get
lake build
lake env lean FiveOrgans/Audit.lean > AXIOM_AUDIT.txt
echo "theorems: $(grep -cE 'depends on axioms|does not depend' AXIOM_AUDIT.txt)  sorryAx: $(grep -c sorryAx AXIOM_AUDIT.txt || true)"
