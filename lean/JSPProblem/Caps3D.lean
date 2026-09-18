import JSPProblem.CupsCaps

/-!
# JSP-000527 — Proposition 2.1 (`P`-caps in `ℝ³`)

For a polytope `P` (given by its vertex set) and a finite `P`-free set `X` in
general position, `|X| > (a+b-4 choose a-2)^{e(P)}` forces either a `P`-cap of
size `a` or a convex set of size `b`.  The proof superimposes the `e(P)`
partial orders `≺_e` coming from projections along the edges of `P`, applies
Dilworth to find a large common antichain, and finishes with the planar
cups–caps theorem.

`IsEdgeOf` formalizes "`[u,v]` is an edge of `conv P`": some supporting
hyperplane of `conv P` meets `conv P` exactly in `segment u v`.
-/

noncomputable section

/-- `[u,v]` is an edge of the polytope `conv P` (for `u v ∈ P`, `u ≠ v`):
some linear functional is minimized on `P` exactly along `segment u v`. -/
def IsEdgeOf (P : Finset (Euc 3)) (u v : Euc 3) : Prop :=
  u ∈ P ∧ v ∈ P ∧ u ≠ v ∧
    ∃ f : Euc 3 →ₗ[ℝ] ℝ, ∃ c : ℝ,
      (∀ w ∈ P, c ≤ f w) ∧ (∀ w ∈ P, f w = c → w ∈ segment ℝ u v)

/-- `e(P)`: the number of edges of `conv P`, computed as half the ordered-edge
count on the vertex set `P`. -/
def edgeCount (P : Finset (Euc 3)) : ℕ :=
  ((P ×ˢ P).filter fun p ↦ IsEdgeOf P p.1 p.2).card / 2

/-- **Proposition 2.1.** -/
theorem prop_2_1 (P : Finset (Euc 3))
    {X : Finset (Euc 3)} (hXfree : FreeOf X (convexHull ℝ (P : Set _)))
    (hX : InGeneralPosition (X : Set _))
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hcard : (a + b - 4).choose (a - 2) ^ (edgeCount P) < X.card) :
    (∃ Y ⊆ X, Y.card = a ∧ CapOf Y (convexHull ℝ (P : Set _))) ∨
    (∃ S ⊆ X, S.card = b ∧ InConvexPosition S) := by
  sorry

end
