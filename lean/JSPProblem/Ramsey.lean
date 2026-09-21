import JSPProblem.Defs

/-!
# Finite Ramsey theorem for `r`-uniform hypergraphs

Mathlib does not contain Ramsey's theorem, so we prove it here from scratch.

The proof is the classical double induction.  The induction on `r` uses the
"peeling" lemma `ramsey_extract`: given the Ramsey statement for `r`-subsets,
for every `m` and `M` there is `N` such that any coloring of the `(r+1)`-subsets
of an `N`-element linearly ordered finite set admits a chain `V` of `m`
"peeled-off" vertices (each with an attached color `φ x`), and a reservoir `A`
of `M` elements larger than all of `V`, such that every `r`-subset of
`{y ∈ V : x < y} ∪ A` together with `x` has color `φ x`.  Peeling off
`c * M + 1` vertices and applying the pigeonhole principle to `φ` yields a
monochromatic `M`-element set.
-/

noncomputable section

open Finset

universe u

/-- **Peeling lemma** used in the induction step of Ramsey's theorem.

Assuming the Ramsey statement for `r`-subsets (`IH`), for every `m` and `M`
there is `N` such that for every coloring `χ` of subsets of a linearly ordered
`s` with `|s| ≥ N`, there exist

* `V`, an `m`-element subset of `s` (the peeled vertices),
* `φ : α → Fin c`, a color attached to each peeled vertex,
* `A`, an `M`-element subset of `s` (the reservoir),

such that every element of `A` is larger than every element of `V`, and for
every `x ∈ V` and every `r`-subset `T` of `{y ∈ V | x < y} ∪ A` one has
`χ (insert x T) = φ x`. -/
private lemma ramsey_extract {r c : ℕ}
    (IH : ∀ M : ℕ, ∃ N : ℕ, ∀ {α : Type u} [LinearOrder α] (s : Finset α),
      N ≤ s.card → ∀ χ : Finset α → Fin c,
        ∃ S : Finset α, S ⊆ s ∧ S.card = M ∧ ∃ col : Fin c,
          ∀ T : Finset α, T ⊆ S → T.card = r → χ T = col)
    (hc : 0 < c) (m M : ℕ) :
    ∃ N : ℕ, ∀ {α : Type u} [LinearOrder α] (s : Finset α),
      N ≤ s.card → ∀ χ : Finset α → Fin c,
        ∃ V : Finset α, V ⊆ s ∧ V.card = m ∧ ∃ φ : α → Fin c,
          ∃ A : Finset α, A ⊆ s ∧ A.card = M ∧
            (∀ x ∈ V, ∀ a ∈ A, x < a) ∧
            (∀ x ∈ V, ∀ T : Finset α,
              T ⊆ V.filter (fun y ↦ x < y) ∪ A → T.card = r →
                χ (insert x T) = φ x) := by
  induction m generalizing M with
  | zero =>
    refine ⟨M, fun {α} _ s hs χ ↦ ?_⟩
    obtain ⟨A, hAs, hAc⟩ := exists_subset_card_eq hs
    exact ⟨∅, empty_subset _, rfl, fun _ ↦ ⟨0, hc⟩, A, hAs, hAc,
      fun x hx ↦ absurd hx (notMem_empty x),
      fun x hx ↦ absurd hx (notMem_empty x)⟩
  | succ m ihm =>
    obtain ⟨R, hR⟩ := IH M
    obtain ⟨N₀, hN₀⟩ := ihm (R + 1)
    refine ⟨N₀, fun {α} _ s hs χ ↦ ?_⟩
    obtain ⟨V, hVs, hVc, φ, A, hAs, hAc, hlt, hprop⟩ := hN₀ s hs χ
    have hAne : A.Nonempty := card_pos.mp (by omega)
    set a₀ := A.min' hAne with ha₀
    have ha₀A : a₀ ∈ A := min'_mem _ _
    have hB : (A.erase a₀).card = R := by
      rw [card_erase_of_mem ha₀A, hAc]; omega
    obtain ⟨S', hS'B, hS'c, col', hmono⟩ :=
      hR (A.erase a₀) hB.ge (fun T ↦ χ (insert a₀ T))
    have ha₀V : a₀ ∉ V := fun h ↦ (hlt a₀ h a₀ ha₀A).false
    have hS'A : S' ⊆ A := hS'B.trans (erase_subset _ _)
    refine ⟨insert a₀ V, insert_subset (hAs ha₀A) hVs,
      by rw [card_insert_of_notMem ha₀V, hVc],
      Function.update φ a₀ col', S', hS'A.trans hAs, hS'c, ?_, ?_⟩
    · -- Every element of `S'` is larger than every element of `insert a₀ V`.
      intro x hx a ha
      have haA : a ∈ A := hS'A ha
      have hane : a ≠ a₀ := fun h ↦ notMem_erase a₀ A (h ▸ hS'B ha)
      rcases mem_insert.mp hx with rfl | hxV
      · exact lt_of_le_of_ne (min'_le _ _ haA) (Ne.symm hane)
      · exact hlt x hxV a haA
    · -- The peeling property.
      intro x hx T hT hTc
      rcases mem_insert.mp hx with rfl | hxV
      · -- x = a₀ : elements of `insert a₀ V` larger than `a₀` — there are none
        -- in `V`, so `T ⊆ S'` and `χ'` applies.
        have hfilter : (insert a₀ V).filter (fun y ↦ a₀ < y) = ∅ := by
          apply filter_false_of_mem
          intro y hy
          rcases mem_insert.mp hy with rfl | hyV
          · exact lt_irrefl _
          · exact not_lt_of_gt (hlt y hyV a₀ ha₀A)
        rw [hfilter, empty_union] at hT
        rw [Function.update_self]
        exact hmono T hT hTc
      · have hxa : a₀ ≠ x := fun h ↦ ha₀V (h ▸ hxV)
        rw [Function.update_of_ne (Ne.symm hxa)]
        apply hprop x hxV T _ hTc
        intro y hy
        have hy' := hT hy
        rw [mem_union] at hy'
        rcases hy' with hyF | hyS'
        · rw [mem_filter, mem_insert] at hyF
          rcases hyF with ⟨rfl | hyV, hxy⟩
          · exact mem_union_right _ ha₀A
          · exact mem_union_left _ (mem_filter.mpr ⟨hyV, hxy⟩)
        · exact mem_union_right _ ((hS'B.trans (erase_subset _ _)) hyS')

/-- **Finite Ramsey theorem**, over an arbitrary linearly ordered finite set.

For all `r`, `c > 0`, `M` there is `N` such that every coloring of the
subsets of an `N`-element linearly ordered finite set `s` with `c` colors
admits an `M`-element subset `S ⊆ s` whose `r`-subsets all have the same
color. -/
theorem ramsey_mono : ∀ (r c : ℕ), 0 < c → ∀ M : ℕ,
    ∃ N : ℕ, ∀ {α : Type u} [LinearOrder α] (s : Finset α),
      N ≤ s.card → ∀ χ : Finset α → Fin c,
        ∃ S : Finset α, S ⊆ s ∧ S.card = M ∧ ∃ col : Fin c,
          ∀ T : Finset α, T ⊆ S → T.card = r → χ T = col := by
  intro r
  induction r with
  | zero =>
    intro c _ M
    refine ⟨M, fun {α} _ s hs χ ↦ ?_⟩
    obtain ⟨S, hSs, hSc⟩ := exists_subset_card_eq hs
    exact ⟨S, hSs, hSc, χ ∅, fun T _ hTc ↦ by rw [card_eq_zero.mp hTc]⟩
  | succ r ihr =>
    intro c hc M
    obtain ⟨N, hN⟩ := ramsey_extract (ihr c hc) hc (c * M + 1) 0
    refine ⟨N, fun {α} _ s hs χ ↦ ?_⟩
    obtain ⟨V, hVs, hVc, φ, A, hAs, hAc, _, hprop⟩ := hN s hs χ
    obtain ⟨col, -, hcol⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := V) (t := (univ : Finset (Fin c))) (f := φ) (n := M)
      (fun a _ ↦ mem_univ _) (by rw [card_univ, Fintype.card_fin, hVc]; omega)
    obtain ⟨S, hSf, hSc⟩ := exists_subset_card_eq (n := M)
      (show M ≤ (V.filter fun x ↦ φ x = col).card by omega)
    refine ⟨S, hSf.trans ((filter_subset _ _).trans hVs), hSc, col, ?_⟩
    intro T hT hTc
    have hTne : T.Nonempty := card_pos.mp (hTc ▸ Nat.succ_pos r)
    set x := T.min' hTne
    have hxT : x ∈ T := min'_mem _ _
    have hxS : x ∈ S := hT hxT
    have hxV : x ∈ V := (filter_subset _ _) (hSf hxS)
    have hφx : φ x = col := (mem_filter.mp (hSf hxS)).2
    have hsub : T.erase x ⊆ V.filter (fun y ↦ x < y) ∪ A := by
      intro y hy
      rw [mem_erase] at hy
      have hyT : y ∈ T := hy.2
      have hyV : y ∈ V := (filter_subset _ _) (hSf (hT hyT))
      have hxy : x < y := lt_of_le_of_ne (min'_le _ _ hyT) (fun h ↦ hy.1 h.symm)
      exact mem_union_left _ (mem_filter.mpr ⟨hyV, hxy⟩)
    have hcard : (T.erase x).card = r := by
      have hce := card_erase_of_mem hxT; omega
    have h := hprop x hxV (T.erase x) hsub hcard
    rwa [insert_erase hxT, hφx] at h

/-- Finite Ramsey theorem specialized to `Fin N`: every `c`-coloring of the
`r`-subsets of `Fin N` has a monochromatic `M`-element subset, once `N` is
large enough. -/
theorem exists_ramsey (r c M : ℕ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ χ : Finset (Fin N) → Fin c,
      ∃ S : Finset (Fin N), S.card = M ∧ ∃ col : Fin c,
        ∀ T : Finset (Fin N), T ⊆ S → T.card = r → χ T = col := by
  obtain ⟨N, hN⟩ := ramsey_mono r c hc M
  refine ⟨N, fun χ ↦ ?_⟩
  obtain ⟨S, -, hSc, col, hcol⟩ :=
    hN (univ : Finset (Fin N)) (by rw [card_univ, Fintype.card_fin]) χ
  exact ⟨S, hSc, col, hcol⟩

end
