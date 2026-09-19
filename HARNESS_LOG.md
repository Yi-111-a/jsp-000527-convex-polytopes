# HARNESS_LOG — JSP-000527

Run: 2026-09-19 05:08:17 UTC

## lake build
```
⚠ [8928/8935] Replayed JSPProblem.HamSandwich
warning: JSPProblem/HamSandwich.lean:26:8: declaration uses `sorry`
⚠ [8929/8935] Replayed JSPProblem.Separation
warning: JSPProblem/Separation.lean:32:8: declaration uses `sorry`
warning: JSPProblem/Separation.lean:48:8: declaration uses `sorry`
warning: JSPProblem/Separation.lean:62:8: declaration uses `sorry`
warning: JSPProblem/Separation.lean:79:8: declaration uses `sorry`
warning: JSPProblem/Separation.lean:93:8: declaration uses `sorry`
⚠ [8930/8935] Replayed JSPProblem.CupsCaps
warning: JSPProblem/CupsCaps.lean:35:8: declaration uses `sorry`
⚠ [8931/8935] Replayed JSPProblem.PorValtr
warning: JSPProblem/PorValtr.lean:44:8: declaration uses `sorry`
⚠ [8932/8935] Replayed JSPProblem.Caps3D
warning: JSPProblem/Caps3D.lean:33:8: declaration uses `sorry`
⚠ [8933/8935] Replayed JSPProblem.MainTheorem
warning: JSPProblem/MainTheorem.lean:32:8: declaration uses `sorry`
Build completed successfully (8935 jobs).
```

exit code: 0

## sorry / admit occurrences

count: 10

| file | occurrences |
|---|---|
| lean/JSPProblem/Caps3D.lean | 1 |
| lean/JSPProblem/CupsCaps.lean | 1 |
| lean/JSPProblem/HamSandwich.lean | 1 |
| lean/JSPProblem/MainTheorem.lean | 1 |
| lean/JSPProblem/PorValtr.lean | 1 |
| lean/JSPProblem/Separation.lean | 5 |

## #print axioms
```
'convexSubset_forcing_points_exp' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'es_three_subexponential' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

## verdict

NOT GREEN (build_rc=0, sorries=10)

