import JSPProblem.PorValtrBase

open Finset
noncomputable section

-- does DecidableEq (Euc 2) synthesize?
example : DecidableEq (Euc 2) := inferInstance

example (z : Fin 3 → Euc 2) : Finset (Euc 2) := Finset.image z Finset.univ

example (X : Finset (Euc 2)) (σ : Bool) : Finset (Finset (Euc 2)) :=
  (X.powersetCard 2).filter fun S ↦ if σ then IsCap S else IsCup S

example (X : Finset (Euc 2)) (y : Fin 3 → Euc 2) (σ : Bool) (i : Fin 2) :
    Finset (Euc 2) := X.filter (· ∈ supportOf y σ i)

-- does #s notation need open Finset?
example (s : Finset (Euc 2)) : ℕ := #s

-- pvEnum_image fix via coercion
lemma test_pvEnum_image {n : ℕ} {s : Finset (Euc 2)} (h : s.card = n) :
    Finset.image (s.orderEmbOfFin h) Finset.univ = s := by
  apply Finset.coe_injective
  rw [Finset.coe_image, Set.image_univ]
  exact Finset.range_orderEmbOfFin s h

end
