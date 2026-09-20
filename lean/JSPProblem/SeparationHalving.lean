import JSPProblem.HamSandwich
import JSPProblem.Separation

/-!
# JSP-000527 — Iterated halving (Proposition 2.5)

* **Prop 2.5** (`prop_2_5`): iterated application of Lemma 2.6
  (`hamSandwich_halves`) yields a 2-separated subcollection keeping a
  `2^{-k³}` fraction of each part.
-/

noncomputable section

/-- **Proposition 2.5.**  Pairwise disjoint finite sets `X₁,…,X_k ⊆ ℝ³`, each
of size `≥ 2^{k³}`, whose union is in general position, contain subsets
`Yᵢ ⊆ Xᵢ` with `|Yᵢ| ≥ 2^{-k³}|Xᵢ|` forming a 2-separated collection. -/
theorem prop_2_5 (X : Fin k → Finset (Euc 3))
    (hdisj : ∀ i j : Fin k, i ≠ j → Disjoint (X i) (X j))
    (hsize : ∀ i, 2 ^ (k ^ 3) ≤ (X i).card)
    (hgp : InGeneralPosition ((Finset.univ.biUnion X : Finset (Euc 3)) : Set (Euc 3))) :
    ∃ Y : Fin k → Finset (Euc 3),
      (∀ i, Y i ⊆ X i) ∧
      (∀ i, 2 ^ (k ^ 3) * (Y i).card ≥ (X i).card) ∧
      TwoSeparated Y := by
  sorry

end
