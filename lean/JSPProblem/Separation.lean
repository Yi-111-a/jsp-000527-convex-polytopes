import JSPProblem.Kirchberger
import JSPProblem.HamSandwich

/-!
# JSP-000527 — Above/below and 2-separability (Propositions 2.2–2.7)

Paper items:

* **Prop 2.2** (`aboveBelow_ramsey`): points of `X ⊂ ℝ³` in general position
  whose projections are consecutive vertices of a convex polygon contain a
  `k`-subset on which all crossing pairs `i<i'<j<j'` have `xᵢxⱼ` uniformly
  above (or uniformly below) `xᵢ'xⱼ'`.  Via Ramsey `R₄(k,k)`.
* **Prop 2.3** (`prop_2_3`): the "all `x₁x₃` above `x₂x₄`" configuration forces
  `conv(X₁∪X₃) ∩ conv(X₂∪X₄) = ∅` — via Kirchberger.
* **Corollary 2.4** (`cor_2_4`): the interval-split disjointness conclusion.
* **Prop 2.5** (`prop_2_5`): iterated halving yields a 2-separated
  subcollection keeping a `2^{-k³}` fraction — via Lemma 2.6.
* **Prop 2.7** (`prop_2_7`): a 2-separated collection in convex position can be
  re-separated by one plane matching any prescribed sign pattern read off a
  transversal — via Kirchberger + continuity.
-/

noncomputable section

variable {k : ℕ}

/-- **Proposition 2.2.**  For `k ≥ 4` there is `AB(k)` such that any `N ≥ AB(k)`
points `x₁,…,x_N` of `ℝ³` in general position, whose projections are the
consecutive vertices of a convex polygon, contain a `k`-element index set `S`
on which every crossing pair `i < i' < j < j'` has `xᵢxⱼ` above `xᵢ'xⱼ'`, or
below. -/
theorem aboveBelow_ramsey {k : ℕ} (hk : 4 ≤ k) :
    ∃ AB : ℕ, ∀ N : ℕ, AB ≤ N → ∀ x : Fin N → Euc 3,
      Function.Injective x →
      InGeneralPosition ((Finset.image x Finset.univ : Finset _) : Set _) →
      Function.Injective (proj2 ∘ x) →
      InConvexPosition (Finset.image (proj2 ∘ x) Finset.univ) →
      ∃ S : Finset (Fin N), S.card = k ∧
        ((∀ i i' j j' : Fin N, i ∈ S → i' ∈ S → j ∈ S → j' ∈ S →
            i < i' → i' < j → j < j' → AboveSeg (x i) (x j) (x i') (x j')) ∨
         (∀ i i' j j' : Fin N, i ∈ S → i' ∈ S → j ∈ S → j' ∈ S →
            i < i' → i' < j → j < j' → BelowSeg (x i) (x j) (x i') (x j'))) := by
  sorry

/-- **Proposition 2.3.**  If every segment `x₁x₃` (`x₁ ∈ X₁, x₃ ∈ X₃`) lies
above every segment `x₂x₄` (`x₂ ∈ X₂, x₄ ∈ X₄`), then
`conv(X₁∪X₃) ∩ conv(X₂∪X₄) = ∅`. -/
theorem prop_2_3 {X1 X2 X3 X4 : Finset (Euc 3)}
    (hd : Disjoint X1 X2) (hd' : Disjoint X1 X3) (hd'' : Disjoint X1 X4)
    (hd''' : Disjoint X2 X3) (hd'''' : Disjoint X2 X4) (hd''''' : Disjoint X3 X4)
    (hgp : InGeneralPosition ((X1 ∪ X2 ∪ X3 ∪ X4 : Finset _) : Set _))
    (habove : ∀ x1 ∈ X1, ∀ x2 ∈ X2, ∀ x3 ∈ X3, ∀ x4 ∈ X4,
      AboveSeg x1 x3 x2 x4) :
    Disjoint (convexHull ℝ ((X1 ∪ X3 : Finset _) : Set _))
             (convexHull ℝ ((X2 ∪ X4 : Finset _) : Set _)) := by
  sorry

/-- **Corollary 2.4.**  In the situation of Proposition 2.2 there is a
`k`-element subsequence `x∘σ` whose interval splits
`{σ i : i < a ∨ b ≤ i < c}` and `{σ i : a ≤ i < b ∨ c ≤ i}` have disjoint
convex hulls for every `a ≤ b ≤ c` in `Fin k`. -/
theorem cor_2_4 {N : ℕ} {x : Fin N → Euc 3}
    (hx : Function.Injective x)
    (hgp : InGeneralPosition ((Finset.image x Finset.univ : Finset _) : Set _))
    (hπ : Function.Injective (proj2 ∘ x))
    (hconv : InConvexPosition (Finset.image (proj2 ∘ x) Finset.univ))
    {k : ℕ} (hk : 4 ≤ k) (hN : Classical.choose (aboveBelow_ramsey hk) ≤ N) :
    ∃ σ : Fin k ↪o Fin N, ∀ a b c : Fin k, a ≤ b → b ≤ c →
      Disjoint
        (convexHull ℝ ((Finset.image (x ∘ σ)
          ((Finset.univ.filter (fun i ↦ i < a ∨ (b ≤ i ∧ i < c))) : Finset _)) : Set _))
        (convexHull ℝ ((Finset.image (x ∘ σ)
          ((Finset.univ.filter (fun i ↦ (a ≤ i ∧ i < b) ∨ c ≤ i)) : Finset _)) : Set _)) := by
  sorry

/-- **Proposition 2.5.**  Pairwise disjoint finite sets `X₁,…,X_k ⊆ ℝ³`, each
of size `≥ 2^{k³}`, whose union is in general position, contain subsets
`Yᵢ ⊆ Xᵢ` with `|Yᵢ| ≥ 2^{-k³}|Xᵢ|` forming a 2-separated collection. -/
theorem prop_2_5 (X : Fin k → Finset (Euc 3))
    (hdisj : ∀ i j : Fin k, i ≠ j → Disjoint (X i) (X j))
    (hsize : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition ((Finset.univ.biUnion X : Finset _) : Set _)) :
    ∃ Y : Fin k → Finset (Euc 3),
      (∀ i, Y i ⊆ X i) ∧
      (∀ i, 2 ^ (k ^ 3) * (Y i).card ≥ (X i).card) ∧
      TwoSeparated Y := by
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
