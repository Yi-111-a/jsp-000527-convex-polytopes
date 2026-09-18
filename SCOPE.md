# SCOPE — JSP-000527

## In scope

- Definitions: general position (via `AffineIndependent` of every
  `(d+1)`-subset), convex position (every point outside `convexHull` of the
  rest), the forcing predicate `ForcesConvex d N n`.
- **Headline:** `convexSubset_forcing_points_exp` — `ES_d(n) = 2^{o(n)}` for
  all `d ≥ 3`, i.e. the negative answer to the catalog question.
- **Core theorem:** `es_three_subexponential` — Theorem 1.1 of PoZa22.
- **Projection lemma:** `forcingConvex_mono_dim` — `ForcesConvex (d-1) N n →
  ForcesConvex d N n` (Valtr's argument; the `(1)` inequality chain).
- All intermediate statements mirroring paper items Thm 2.1, 2.2, 2.3,
  Lemma 2.6, Prop 2.1, 2.2, 2.3, Cor 2.4, Prop 2.5, 2.7, Prop 3.1 as named
  lemmas — proved or tracked as explicit remaining `sorry`s.

## Out of scope (for the catalog claim)

- Theorem 1.2 / 1.3 of PoZa22 (the quantitative positive-fraction versions).
  These are strengthenings, not part of the yes/no catalog question, and their
  proof additionally uses the four-colour theorem. They may be added later as
  bonus theorems but are **not** required for `prize_ready`.
- Lower bounds for `ES_d` (the paper only proves the upper bound `2^{o(n)}`;
  the catalog question is answered by the upper bound alone).
- Semialgebraic-Ramsey refinements discussed in the §3 remark.

## Interface decisions (checkpoints)

- `EuclideanSpace ℝ (Fin d)` is the ambient space; dimension enters through
  `d` so the `d ≥ 3` quantification is a single theorem.
- General position is defined per `(d+1)`-subset as affine independence — a
  checkpoint lemma (`generalPosition_iff_forall_affineIndependent`, plus the
  hyperplane reading) freezes the choice.
- Convex position is defined as `x ∉ convexHull ℝ (S ∖ {x})` for all `x ∈ S`;
  checkpoint lemmas relate it to `Set.extremePoints` and to the vertex-set
  reading used in the paper.
