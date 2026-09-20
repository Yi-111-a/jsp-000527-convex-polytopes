import JSPProblem.Separation

/-!
# JSP-000527 — Above/below Ramsey (Proposition 2.2 and Corollary 2.4)

Paper items:

* **Prop 2.2** (`aboveBelow_ramsey`): points of `X ⊂ ℝ³` in general position
  whose projections are consecutive vertices of a convex polygon contain a
  `k`-subset on which all crossing pairs `i<i'<j<j'` have `xᵢxⱼ` uniformly
  above (or uniformly below) `xᵢ'xⱼ'`.  Via Ramsey `R₄(k,k)`.
* **Corollary 2.4** (`cor_2_4`): the interval-split disjointness conclusion,
  combining `aboveBelow_ramsey` with `prop_2_3`.
-/

noncomputable section

/-- **Proposition 2.2.**  For `k ≥ 4` there is `AB(k)` such that any `N ≥ AB(k)`
points `x₁,…,x_N` of `ℝ³` in general position, whose projections are the
consecutive vertices of a convex polygon, contain a `k`-element index set `S`
on which every crossing pair `i < i' < j < j'` has `xᵢxⱼ` above `xᵢ'xⱼ'`, or
below. -/
theorem aboveBelow_ramsey {k : ℕ} (hk : 4 ≤ k) :
    ∃ AB : ℕ, ∀ N : ℕ, AB ≤ N → ∀ x : Fin N → Euc 3,
      Function.Injective x →
      InGeneralPosition ((Finset.image x Finset.univ : Finset (Euc 3)) : Set (Euc 3)) →
      Function.Injective (proj2 ∘ x) →
      InConvexPosition (Finset.image (proj2 ∘ x) Finset.univ) →
      ∃ S : Finset (Fin N), S.card = k ∧
        ((∀ i i' j j' : Fin N, i ∈ S → i' ∈ S → j ∈ S → j' ∈ S →
            i < i' → i' < j → j < j' → AboveSeg (x i) (x j) (x i') (x j')) ∨
         (∀ i i' j j' : Fin N, i ∈ S → i' ∈ S → j ∈ S → j' ∈ S →
            i < i' → i' < j → j < j' → BelowSeg (x i) (x j) (x i') (x j'))) := by
  sorry

/-- **Corollary 2.4.**  In the situation of Proposition 2.2 there is a
`k`-element subsequence `x∘σ` whose interval splits
`{σ i : i < a ∨ b ≤ i < c}` and `{σ i : a ≤ i < b ∨ c ≤ i}` have disjoint
convex hulls for every `a ≤ b ≤ c` in `Fin k`. -/
theorem cor_2_4 {N : ℕ} {x : Fin N → Euc 3}
    (hx : Function.Injective x)
    (hgp : InGeneralPosition ((Finset.image x Finset.univ : Finset (Euc 3)) : Set (Euc 3)))
    (hπ : Function.Injective (proj2 ∘ x))
    (hconv : InConvexPosition (Finset.image (proj2 ∘ x) Finset.univ))
    {k : ℕ} (hk : 4 ≤ k) (hN : Classical.choose (aboveBelow_ramsey hk) ≤ N) :
    ∃ σ : Fin k ↪o Fin N, ∀ a b c : Fin k, a ≤ b → b ≤ c →
      Disjoint
        (convexHull ℝ ((Finset.image (x ∘ σ)
          ((Finset.univ.filter (fun i ↦ i < a ∨ (b ≤ i ∧ i < c))) : Finset (Fin k))) : Set (Euc 3)))
        (convexHull ℝ ((Finset.image (x ∘ σ)
          ((Finset.univ.filter (fun i ↦ (a ≤ i ∧ i < b) ∨ c ≤ i)) : Finset (Fin k))) : Set (Euc 3))) := by
  sorry

end
