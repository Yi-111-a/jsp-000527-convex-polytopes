#!/usr/bin/env bash
# Structured status for JSP-000527. Prints JSON to stdout.
set -u
cd "$(dirname "$0")/.."
ROOT="$(pwd)"

SORRY_COUNT=$(awk '
  /\/\*/ {inblock=1} /\*\// {inblock=0; next} inblock {next}
  { line=$0; sub(/--.*/,"",line);
    n=gsub(/\bsorry\b/,"&",line); m=gsub(/\badmit\b/,"&",line); c+=n+m }
  END {print c+0}' lean/JSPProblem/*.lean lean/JSPProblem.lean 2>/dev/null)

SHA=$(git rev-parse HEAD 2>/dev/null || echo "")
BRANCH=$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo "")
OLEAN=$(find lean/.lake -name '*.olean' 2>/dev/null | wc -l | tr -d ' ')
SORRY_LEMMAS=$(grep -rEn ':= *sorry|sorry$' lean/JSPProblem lean/JSPProblem.lean 2>/dev/null | wc -l | tr -d ' ')

cat <<EOF
{
  "jsp_id": "JSP-000527",
  "branch": "$BRANCH",
  "commit_sha": "$SHA",
  "sorry_occurrences": $SORRY_COUNT,
  "sorry_sites": $SORRY_LEMMAS,
  "olean_files": $OLEAN,
  "headline": ["convexSubset_forcing_points_exp", "es_three_subexponential"],
  "prize_ready": false
}
EOF
