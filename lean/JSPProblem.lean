import JSPProblem.MainTheorem

/-!
# JSP-000527 — Convex polytopes from fewer points

Formalization of Pohoata–Zakharov, *Convex polytopes from fewer points*
(arXiv:2208.04878): the Erdős–Szekeres number `ES_d(n)` satisfies
`ES_d(n) = 2^{o(n)}` for every `d ≥ 3` — in higher dimensions the number of
general-position points needed to force `n` points in convex position grows
**sub**-exponentially, answering the catalog question in the negative.

Headline theorems:

* `convexSubset_forcing_points_exp` — `ES_d(n) = 2^{o(n)}` for all `d ≥ 3`.
* `es_three_subexponential` — Theorem 1.1 of the paper (`d = 3`).

Module map: `JSPProblem/Defs.lean` (interface), `Checkpoint.lean` (proved
sanity lemmas), `Projection.lean` (Valtr's `ES_d ≤ ES_{d-1}`),
`CupsCaps.lean` (Thm 2.1), `PorValtr.lean` (Thm 2.2), `Kirchberger.lean`
(Thm 2.3), `HamSandwich.lean` (Lemma 2.6), `Separation.lean` (Props
2.2–2.7), `Caps3D.lean` (Prop 2.1), `MainTheorem.lean` (§3 + headline).
-/
