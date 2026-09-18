#!/usr/bin/env bash
# Harness for JSP-000527: lake build + sorry count + #print axioms.
# Writes/updates HARNESS_LOG.md at repo root. Run from repo root or anywhere:
#   bash scripts/harness.sh
set -u
cd "$(dirname "$0")/.."
ROOT="$(pwd)"
LOG="$ROOT/HARNESS_LOG.md"
TS="$(date -u '+%Y-%m-%d %H:%M:%S UTC')"

echo "# HARNESS_LOG — JSP-000527" > "$LOG"
echo "" >> "$LOG"
echo "Run: $TS" >> "$LOG"
echo "" >> "$LOG"

# --- 1. lake build ---------------------------------------------------------
echo "## lake build" >> "$LOG"
echo '```' >> "$LOG"
BUILD_OUT="$(cd lean && lake build 2>&1)"
BUILD_RC=$?
echo "$BUILD_OUT" | tail -40 >> "$LOG"
echo '```' >> "$LOG"
echo "" >> "$LOG"
echo "exit code: $BUILD_RC" >> "$LOG"
echo "" >> "$LOG"

# --- 2. sorry / admit count ------------------------------------------------
# count actual tactic occurrences on non-comment lines (explicit char-class
# boundaries; `\b` is not portable across awk implementations)
SORRY_COUNT=$(awk '
  /\/\*/ {inblock=1} /\*\// {inblock=0; next} inblock {next}
  { line=$0; sub(/--.*/,"",line);
    n=gsub(/(^|[^A-Za-z0-9_])sorry([^A-Za-z0-9_]|$)/,"&",line);
    m=gsub(/(^|[^A-Za-z0-9_])admit([^A-Za-z0-9_]|$)/,"&",line); c+=n+m }
  END {print c+0}' lean/JSPProblem/*.lean lean/JSPProblem.lean)

echo "## sorry / admit occurrences" >> "$LOG"
echo "" >> "$LOG"
echo "count: $SORRY_COUNT" >> "$LOG"
echo "" >> "$LOG"
echo "| file | occurrences |" >> "$LOG"
echo "|---|---|" >> "$LOG"
for f in lean/JSPProblem/*.lean lean/JSPProblem.lean; do
  c=$(awk '
    /\/\*/ {inblock=1} /\*\// {inblock=0; next} inblock {next}
    { line=$0; sub(/--.*/,"",line);
      n=gsub(/(^|[^A-Za-z0-9_])sorry([^A-Za-z0-9_]|$)/,"&",line);
      m=gsub(/(^|[^A-Za-z0-9_])admit([^A-Za-z0-9_]|$)/,"&",line); c+=n+m }
    END {print c+0}' "$f")
  [ "$c" -gt 0 ] && echo "| $f | $c |" >> "$LOG"
done
echo "" >> "$LOG"

# --- 3. #print axioms ------------------------------------------------------
echo "## #print axioms" >> "$LOG"
echo '```' >> "$LOG"
AXFILE="lean/AxiomCheck.lean"
cat > "$AXFILE" <<'EOF'
import JSPProblem
#print axioms convexSubset_forcing_points_exp
#print axioms es_three_subexponential
EOF
(cd lean && lake env lean AxiomCheck.lean) >> "$LOG" 2>&1
echo '```' >> "$LOG"
rm -f "$AXFILE"
echo "" >> "$LOG"

# --- 4. verdict -------------------------------------------------------------
if [ "$BUILD_RC" -eq 0 ] && [ "$SORRY_COUNT" -eq 0 ]; then
  VERDICT="GREEN (prize_ready candidate — verify axioms list above)"
else
  VERDICT="NOT GREEN (build_rc=$BUILD_RC, sorries=$SORRY_COUNT)"
fi
echo "## verdict" >> "$LOG"
echo "" >> "$LOG"
echo "$VERDICT" >> "$LOG"
echo "" >> "$LOG"
echo "harness: $VERDICT"
