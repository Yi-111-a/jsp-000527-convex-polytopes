import JSPProblem.Kirchberger
import JSPProblem.HamSandwich

/-!
# JSP-000527 — Above/below separation (Propositions 2.3 and 2.7)

Paper items:

* **Prop 2.3** (`prop_2_3`): the "all `x₁x₃` above `x₂x₄`" configuration forces
  `conv(X₁∪X₃) ∩ conv(X₂∪X₄) = ∅` — via Kirchberger.
* **Prop 2.7** (`prop_2_7`): a 2-separated collection in convex position can be
  re-separated by one plane matching any prescribed sign pattern read off a
  transversal — via Kirchberger + continuity.

Prop 2.2 / Cor 2.4 live in `SeparationRamsey.lean`; Prop 2.5 lives in
`SeparationHalving.lean`.
-/

noncomputable section

/-- **Proposition 2.3.**  If every segment `x₁x₃` (`x₁ ∈ X₁, x₃ ∈ X₃`) lies
above every segment `x₂x₄` (`x₂ ∈ X₂, x₄ ∈ X₄`), then
`conv(X₁∪X₃) ∩ conv(X₂∪X₄) = ∅`. -/
theorem prop_2_3 {X1 X2 X3 X4 : Finset (Euc 3)}
    (hd : Disjoint X1 X2) (hd' : Disjoint X1 X3) (hd'' : Disjoint X1 X4)
    (hd''' : Disjoint X2 X3) (hd'''' : Disjoint X2 X4) (hd''''' : Disjoint X3 X4)
    (hgp : InGeneralPosition ((X1 ∪ X2 ∪ X3 ∪ X4 : Finset (Euc 3)) : Set (Euc 3)))
    (habove : ∀ x1 ∈ X1, ∀ x2 ∈ X2, ∀ x3 ∈ X3, ∀ x4 ∈ X4,
      AboveSeg x1 x3 x2 x4) :
    Disjoint (convexHull ℝ ((X1 ∪ X3 : Finset (Euc 3)) : Set (Euc 3)))
             (convexHull ℝ ((X2 ∪ X4 : Finset (Euc 3)) : Set (Euc 3))) := by
  sorry

/-- **Proposition 2.7.**  For a 2-separated collection `X₁,…,X_k` in convex
position and representatives `xᵢ ∈ Xᵢ`, any plane `H = {f = c}` avoiding all
`xᵢ` can be replaced by a plane `H̃ = {g = c'}` placing each whole `Xᵢ` on the
side dictated by `xᵢ`'s side of `H`. -/
theorem prop_2_7 (X : Fin k → Finset (Euc 3))
    (hsep : TwoSeparated X) (hconv : CollectionConvex X)
    (x : Fin k → Euc 3) (hx : ∀ i, x i ∈ X i)
    (f : Euc 3 →ₗ[ℝ] ℝ) (c : ℝ) (hf : ∀ i, f (x i) ≠ c) :
    ∃ g : Euc 3 →ₗ[ℝ] ℝ, ∃ c' : ℝ,
      ∀ i : Fin k,
        (c < f (x i) → ∀ y ∈ X i, c' < g y) ∧
        (f (x i) < c → ∀ y ∈ X i, g y < c') := by
  sorry

end
