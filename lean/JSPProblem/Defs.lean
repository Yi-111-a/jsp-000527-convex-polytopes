import Mathlib

/-!
# JSP-000527 — Core definitions

The ambient space is `Euc d := EuclideanSpace ℝ (Fin d)`.

* `InGeneralPosition X` — no `d+1` points of `X` lie on a hyperplane,
  formalized as: every `(d+1)`-element subset of `X` is affinely independent.
* `InConvexPosition S` — every `x ∈ S` lies outside `convexHull (S ∖ {x})`
  (i.e. the points of `S` are the vertices of `conv S`).
* `ForcesConvex d N n` — every general-position set of `≥ N` points in `ℝ^d`
  contains an `n`-element subset in convex position.  (`ES_d(n)` is the least
  such `N`.)
* Supporting notions used by the paper statements: `proj2` (the coordinate
  projection `ℝ³ → ℝ²`), `AboveSeg` (one segment vertically above another
  over an interior crossing), `FreeOf` (`P`-free), `CapOf` (`P`-cap),
  `CollectionConvex` (a collection of sets in convex position) and
  `TwoSeparated`.
-/

noncomputable section

/-- The ambient `d`-dimensional Euclidean space. -/
abbrev Euc (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-- A set `X ⊆ ℝ^d` is in *general position* if no `d+1` of its points lie on a
common `(d-1)`-dimensional hyperplane.  We formalize this as: every
`(d+1)`-element subset of `X` is affinely independent.  For `|X| < d+1` this is
vacuously true (the paper only applies the notion to `|X| ≥ d+1`). -/
def InGeneralPosition (X : Set (Euc d)) : Prop :=
  ∀ s : Finset (Euc d), (s : Set _) ⊆ X → s.card = d + 1 →
    AffineIndependent ℝ (fun x : s ↦ (x : Euc d))

/-- A finite set `S ⊆ ℝ^d` is in *convex position* if its points are the
vertices of `conv S`; equivalently no point lies in the convex hull of the
remaining points. -/
def InConvexPosition (S : Finset (Euc d)) : Prop :=
  ∀ x ∈ S, x ∉ convexHull ℝ ((S.erase x : Finset _) : Set _)

/-- `ForcesConvex d N n`: every finite set `X ⊆ ℝ^d` in general position with
`|X| ≥ N` contains an `n`-element subset in convex position.  The Erdős–Szekeres
number `ES_d(n)` is the least `N` for which this holds. -/
def ForcesConvex (d N n : ℕ) : Prop :=
  ∀ X : Finset (Euc d), InGeneralPosition (X : Set (Euc d)) → N ≤ X.card →
    ∃ S : Finset (Euc d), S ⊆ X ∧ S.card = n ∧ InConvexPosition S

/-- The coordinate projection `ℝ³ → ℝ²` dropping the last coordinate. -/
def proj2 : Euc 3 →ₗ[ℝ] Euc 2 where
  toFun x := WithLp.toLp 2 fun i : Fin 2 ↦ x i.castSucc
  map_add' x y := by ext i; simp [PiLp.add_apply]
  map_smul' c x := by ext i; simp [PiLp.smul_apply, smul_eq_mul]

/-- Segment `ab` lies *above* segment `cd` (paper §2, "above and below in
space"): their projections to `ℝ²` meet at a point over which `ab` has the
larger third coordinate. -/
def AboveSeg (a b c d₂ : Euc 3) : Prop :=
  ∃ s t : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧
    proj2 ((1 - s) • a + s • b) = proj2 ((1 - t) • c + t • d₂) ∧
    (((1 - s) • a + s • b) 2) > ((1 - t) • c + t • d₂) 2

/-- `BelowSeg`: the same with the smaller third coordinate. -/
def BelowSeg (a b c d₂ : Euc 3) : Prop :=
  ∃ s t : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ 0 ≤ t ∧ t ≤ 1 ∧
    proj2 ((1 - s) • a + s • b) = proj2 ((1 - t) • c + t • d₂) ∧
    (((1 - s) • a + s • b) 2) < ((1 - t) • c + t • d₂) 2

/-- `X` is `C`-free (paper §2): for any distinct `x y ∈ X` the line `xy` does
not meet the convex set `C`.  Stated here as: no point of `C` lies on a line
through two distinct points of `X`. -/
def FreeOf (X : Finset (Euc 3)) (C : Set (Euc 3)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ∀ w ∈ affineSpan ℝ ({x, y} : Set _), w ∉ C

/-- `Y` is a `C`-cap (paper §2): each `y ∈ Y` avoids
`conv (C ∪ (Y ∖ {y}))`. -/
def CapOf (Y : Finset (Euc 3)) (C : Set (Euc 3)) : Prop :=
  ∀ y ∈ Y, y ∉ convexHull ℝ (C ∪ ((Y.erase y : Finset _) : Set _))

/-- A collection of sets `X₁,…,X_k ⊆ ℝ^d` is *in convex position* (paper §1):
for every `i`, `conv (X i)` and `conv (⋃ j ≠ i, X j)` are disjoint. -/
def CollectionConvex {k : ℕ} (X : Fin k → Finset (Euc d)) : Prop :=
  ∀ i : Fin k,
    Disjoint (convexHull ℝ (X i : Set (Euc d)))
      (convexHull ℝ (⋃ j : Fin k, ⋃ _ : j ≠ i, (X j : Set (Euc d))))

/-- A collection `X₁,…,X_k ⊆ ℝ^d` is *2-separated* (paper §2): for pairwise
disjoint index pairs `{i,j} ∩ {i',j'} = ∅`,
`conv (Xᵢ ∪ Xⱼ) ∩ conv (Xᵢ' ∪ Xⱼ') = ∅`. -/
def TwoSeparated {k : ℕ} (X : Fin k → Finset (Euc d)) : Prop :=
  ∀ i j i' j' : Fin k, i ≠ i' → i ≠ j' → j ≠ i' → j ≠ j' →
    Disjoint (convexHull ℝ ((X i ∪ X j : Finset (Euc d)) : Set (Euc d)))
      (convexHull ℝ ((X i' ∪ X j' : Finset (Euc d)) : Set (Euc d)))

end
