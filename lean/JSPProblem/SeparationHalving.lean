import JSPProblem.HamSandwich
import JSPProblem.Separation

/-!
# JSP-000527 — Iterated halving (Proposition 2.5)

* **Prop 2.5** (`prop_2_5`): iterated application of Lemma 2.6
  (`hamSandwich_halves`) yields a 2-separated subcollection keeping a
  `2^{-k³}` fraction of each part.

## Proof sketch

A *task* is an ordered quadruple `(i, j, i', j')` with `{i,j} ∩ {i',j'} = ∅`,
normalized by `i ≤ j`, `i' ≤ j'`, `i < i'`.  For every task we apply
`hamSandwich_halves` with `r = 2` to the four current sets and replace them by
their `H⁺`- resp. `H⁻`-halves.  The two pairs are then separated by `H`: the
convex hulls can only meet on `H` itself, and there they meet the convex hulls
of the *on-plane* points, which are disjoint because at most `d` points of a
general-position set lie on a hyperplane.

Every unordered pair of disjoint pairs `{i,j}`, `{i',j'}` has a unique
normalized task, so at the end all `TwoSeparated` constraints hold.  Each index
is involved in at most `k³` tasks (an explicit injection into
`Fin k × Fin k × Fin k`), whence `2^{k³} |Yᵢ| ≥ |Xᵢ|`.
-/

noncomputable section

open Finset

variable {k : ℕ}

/-- A **task** is an ordered quadruple `(i, j, i', j')` of indices; applying the
ham-sandwich lemma to `(X i, X j, X i', X j')` with `r = 2` puts halves of the
first pair in `H⁺` and halves of the second pair in `H⁻`. -/
abbrev SepTask (k : ℕ) := Fin k × Fin k × Fin k × Fin k

/-- A task is *valid* if its two index-pairs are disjoint; the conditions
`i ≤ j`, `i' ≤ j'`, `i < i'` make the representation of an unordered pair of
pairs unique. -/
def ValidTask (q : SepTask k) : Prop :=
  q.1 ≤ q.2.1 ∧ q.2.2.1 ≤ q.2.2.2 ∧ q.1 < q.2.2.1 ∧
    q.1 ≠ q.2.2.2 ∧ q.2.1 ≠ q.2.2.1 ∧ q.2.1 ≠ q.2.2.2

/-- `u` is *involved* in `q` if it appears in one of the two pairs. -/
def Involves (u : Fin k) (q : SepTask k) : Prop :=
  u = q.1 ∨ u = q.2.1 ∨ u = q.2.2.1 ∨ u = q.2.2.2

instance (u : Fin k) : DecidablePred (Involves u) := fun q ↦ by
  unfold Involves
  infer_instance

/-- Two disjoint subsets of an affinely independent family have disjoint convex
hulls: a common point would have two distinct barycentric representations. -/
lemma disjoint_convexHull_of_disjoint_affineIndependent {A B : Finset (Euc 3)}
    (hd : Disjoint A B)
    (hai : AffineIndependent ℝ ((↑) : ↥(A ∪ B) → Euc 3)) :
    Disjoint (convexHull ℝ (A : Set (Euc 3))) (convexHull ℝ (B : Set (Euc 3))) := by
  classical
  rw [Set.disjoint_left]
  intro p hpA hpB
  rw [Finset.convexHull_eq] at hpA hpB
  obtain ⟨wA, -, hwA1, hwpA⟩ := hpA
  obtain ⟨wB, -, hwB1, hwpB⟩ := hpB
  have hsum1 : ∑ x ∈ A ∪ B, (↑A : Set _).indicator wA x = 1 := by
    rw [Finset.sum_indicator_subset _ Finset.subset_union_left, hwA1]
  have hsum2 : ∑ x ∈ A ∪ B, (↑B : Set _).indicator wB x = 1 := by
    rw [Finset.sum_indicator_subset _ Finset.subset_union_right, hwB1]
  have hwp1 : ∑ x ∈ A ∪ B, (↑A : Set _).indicator wA x • x = p := by
    have hsc : ∀ x, (↑A : Set _).indicator wA x • x =
        (↑A : Set _).indicator (fun y ↦ wA y • y) x := by
      intro x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_smul]
    rw [Finset.sum_congr rfl (fun x _ ↦ hsc x),
      Finset.sum_indicator_subset _ Finset.subset_union_left, ← hwpA,
      Finset.centerMass_eq_of_sum_1 _ _ hwA1]
    apply Finset.sum_congr rfl
    intro y _
    simp
  have hwp2 : ∑ x ∈ A ∪ B, (↑B : Set _).indicator wB x • x = p := by
    have hsc : ∀ x, (↑B : Set _).indicator wB x • x =
        (↑B : Set _).indicator (fun y ↦ wB y • y) x := by
      intro x
      by_cases hx : x ∈ B
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_smul]
    rw [Finset.sum_congr rfl (fun x _ ↦ hsc x),
      Finset.sum_indicator_subset _ Finset.subset_union_right, ← hwpB,
      Finset.centerMass_eq_of_sum_1 _ _ hwB1]
    apply Finset.sum_congr rfl
    intro y _
    simp
  have heq := hai.eq_of_sum_eq_sum_subtype
    (w₁ := (↑A : Set _).indicator wA) (w₂ := (↑B : Set _).indicator wB)
    (hsum1.trans hsum2.symm) (hwp1.trans hwp2.symm)
  have hz : ∀ x ∈ A, wA x = 0 := by
    intro x hx
    have hxu : x ∈ A ∪ B := Finset.mem_union_left B hx
    have hxx := heq x hxu
    rw [Set.indicator_of_mem hx,
      Set.indicator_of_notMem (Finset.disjoint_left.1 hd hx)] at hxx
    exact hxx
  have h0 : (∑ x ∈ A, wA x) = 0 := Finset.sum_eq_zero hz
  rw [hwA1] at h0
  exact one_ne_zero h0

/-- If `p ∈ conv s` lies on the plane `{f = c}` while `s` sits in the closed
half-space `{f ≥ c}`, then `p` is a convex combination of on-plane points. -/
lemma mem_convexHull_filter_plane {s : Finset (Euc 3)} {f : Euc 3 →ₗ[ℝ] ℝ}
    {c : ℝ} (hs : ∀ y ∈ s, c ≤ f y) {p : Euc 3}
    (hp : p ∈ convexHull ℝ (s : Set (Euc 3))) (hpc : f p = c) :
    p ∈ convexHull ℝ ((s.filter fun y ↦ f y = c) : Set (Euc 3)) := by
  classical
  rw [Finset.convexHull_eq] at hp ⊢
  obtain ⟨w, hw0, hw1, hwp⟩ := hp
  have hfw : ∑ y ∈ s, w y * f y = c := by
    have e : f p = ∑ y ∈ s, w y * f y := by
      rw [← hwp, Finset.centerMass_eq_of_sum_1 _ _ hw1]
      simp only [map_sum, LinearMap.map_smul, smul_eq_mul, id_eq]
    rw [hpc] at e
    exact e.symm
  have hzero : ∀ y ∈ s, w y * (f y - c) = 0 := by
    have hsum : ∑ y ∈ s, w y * (f y - c) = 0 := by
      have e : ∀ y ∈ s, w y * (f y - c) = w y * f y - w y * c :=
        fun y _ ↦ mul_sub ..
      rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.sum_mul,
        hfw, hw1]
      ring
    exact (Finset.sum_eq_zero_iff_of_nonneg fun y hy ↦
      mul_nonneg (hw0 y hy) (sub_nonneg.2 (hs y hy))).1 hsum
  have hzeros : ∀ y ∈ s, y ∉ s.filter (fun y ↦ f y = c) → w y = 0 := by
    intro y hy hnf
    rcases mul_eq_zero.1 (hzero y hy) with h | h
    · exact h
    · exfalso; exact hnf (Finset.mem_filter.2 ⟨hy, sub_eq_zero.1 h⟩)
  refine ⟨w, fun y hy ↦ hw0 y (Finset.mem_filter.1 hy).1, ?_, ?_⟩
  · rw [← hw1]; exact Finset.sum_subset (Finset.filter_subset _ _) hzeros
  · rw [← hwp]; exact Finset.centerMass_subset id (Finset.filter_subset _ _) hzeros

/-- The mirror image of `mem_convexHull_filter_plane` for `{f ≤ c}`. -/
lemma mem_convexHull_filter_plane' {s : Finset (Euc 3)} {f : Euc 3 →ₗ[ℝ] ℝ}
    {c : ℝ} (hs : ∀ y ∈ s, f y ≤ c) {p : Euc 3}
    (hp : p ∈ convexHull ℝ (s : Set (Euc 3))) (hpc : f p = c) :
    p ∈ convexHull ℝ ((s.filter fun y ↦ f y = c) : Set (Euc 3)) := by
  have hs' : ∀ y ∈ s, -c ≤ (-f) y := fun y hy ↦ by
    simp only [LinearMap.neg_apply]
    exact neg_le_neg_iff.2 (hs y hy)
  have hpc' : (-f) p = -c := by simp [LinearMap.neg_apply, hpc]
  have hp' := mem_convexHull_filter_plane (s := s) (f := -f) (c := -c) hs' hp hpc'
  have hflt : (s.filter fun y ↦ (-f) y = -c) = s.filter (fun y ↦ f y = c) := by
    apply Finset.filter_congr
    intro y _
    simp [LinearMap.neg_apply]
  rwa [hflt] at hp'

/-- A general-position set `U` in `ℝ³` has at most `3` points on any affine
plane `{f = c}` with `f ≠ 0`. -/
lemma card_filter_plane_le_three {U : Finset (Euc 3)} {f : Euc 3 →ₗ[ℝ] ℝ}
    {c : ℝ} (hf : f ≠ 0) (hgp : InGeneralPosition (U : Set (Euc 3)))
    (hU4 : 4 ≤ U.card) :
    (U.filter fun y ↦ f y = c).card ≤ 3 := by
  classical
  by_contra hle
  push_neg at hle
  obtain ⟨Q, hQsub, hQcard⟩ :=
    Finset.exists_subset_card_eq (n := 4)
      (show 4 ≤ (U.filter fun y ↦ f y = c).card by omega)
  have hQU : Q ⊆ U := hQsub.trans (Finset.filter_subset _ _)
  have hQf : ∀ y ∈ Q, f y = c := fun y hy ↦ (Finset.mem_filter.1 (hQsub hy)).2
  have hAi : AffineIndependent ℝ ((↑) : ↥Q → Euc 3) :=
    affineIndependent_of_inGeneralPosition hgp hU4 hQU hQcard.le
  obtain ⟨q0, hq0⟩ : Q.Nonempty := Finset.card_pos.1 (by omega)
  have hli := (affineIndependent_iff_linearIndependent_vsub ℝ
    ((↑) : ↥Q → Euc 3) ⟨q0, hq0⟩).1 hAi
  obtain ⟨x0, hx0ne⟩ := Fintype.exists_ne_of_one_lt_card
    (α := ↥Q) (by rw [Fintype.card_coe]; omega) ⟨q0, hq0⟩
  haveI : Nonempty {x : ↥Q // x ≠ ⟨q0, hq0⟩} := ⟨⟨x0, hx0ne⟩⟩
  have hcard : Fintype.card {x : ↥Q // x ≠ ⟨q0, hq0⟩} =
      Module.finrank ℝ (Euc 3) := by
    rw [Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem
      (Finset.mem_univ _), Finset.card_univ, Fintype.card_coe, hQcard,
      finrank_euclideanSpace_fin]
  have hspan := hli.span_eq_top_of_card_eq_finrank hcard
  have hker : LinearMap.ker f = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.2
    rintro v ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub, map_sub]
    rw [hQf _ (i.val).2, hQf _ hq0, sub_self]
  exact hf (LinearMap.ker_eq_top.1 hker)

/-- **Separation step.**  If `A` sits in `{f ≥ c}` and `B` in `{f ≤ c}` while
`A`, `B` are disjoint subsets of a general-position ambient set `U`, then
`conv A` and `conv B` are disjoint: a common point would lie on the plane and
hence in the hulls of the two disjoint on-plane point sets. -/
lemma disjoint_convexHull_of_halves {U A B : Finset (Euc 3)} {f : Euc 3 →ₗ[ℝ] ℝ}
    {c : ℝ} (hf : f ≠ 0) (hA : ∀ x ∈ A, c ≤ f x) (hB : ∀ x ∈ B, f x ≤ c)
    (hdAB : Disjoint A B) (hAU : A ⊆ U) (hBU : B ⊆ U)
    (hgp : InGeneralPosition (U : Set (Euc 3))) (hU4 : 4 ≤ U.card) :
    Disjoint (convexHull ℝ (A : Set (Euc 3))) (convexHull ℝ (B : Set (Euc 3))) := by
  classical
  rw [Set.disjoint_left]
  intro p hpA hpB
  have hconvA : convexHull ℝ (A : Set (Euc 3)) ⊆ {x | c ≤ f x} :=
    convexHull_min (fun x hx ↦ hA x (Finset.mem_coe.1 hx))
      (convex_halfSpace_ge f.isLinear c)
  have hconvB : convexHull ℝ (B : Set (Euc 3)) ⊆ {x | f x ≤ c} :=
    convexHull_min (fun x hx ↦ hB x (Finset.mem_coe.1 hx))
      (convex_halfSpace_le f.isLinear c)
  have hpc : f p = c := le_antisymm (hconvB hpB) (hconvA hpA)
  have hpA' := mem_convexHull_filter_plane hA hpA hpc
  have hpB' := mem_convexHull_filter_plane' hB hpB hpc
  set A' := A.filter (fun y ↦ f y = c) with hA'def
  set B' := B.filter (fun y ↦ f y = c) with hB'def
  have hd' : Disjoint A' B' :=
    hdAB.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsub : A' ∪ B' ⊆ U.filter (fun y ↦ f y = c) := by
    intro x hx
    rcases Finset.mem_union.1 hx with h | h <;>
      · refine Finset.mem_filter.2 ⟨?_, (Finset.mem_filter.1 h).2⟩
        first | exact hAU (Finset.mem_filter.1 h).1 | exact hBU (Finset.mem_filter.1 h).1
  have hcard3 : (A' ∪ B').card ≤ 3 :=
    (Finset.card_le_card hsub).trans (card_filter_plane_le_three hf hgp hU4)
  have hAi : AffineIndependent ℝ ((↑) : ↥(A' ∪ B') → Euc 3) :=
    affineIndependent_of_inGeneralPosition hgp hU4
      (Finset.union_subset (Finset.filter_subset _ _ |>.trans hAU)
        (Finset.filter_subset _ _ |>.trans hBU))
      (by omega)
  have hdis := disjoint_convexHull_of_disjoint_affineIndependent hd' hAi
  exact (Set.disjoint_left.1 hdis) hpA' hpB'

/-- **Main induction.**  Processing a finset `T` of valid tasks one at a time
produces `Z i ⊆ X i` such that each `Z i` has been halved once per task
involving `i`, and all tasks in `T` are separated. -/
lemma exists_thinned (X : Fin k → Finset (Euc 3))
    (hdisj : ∀ i j : Fin k, i ≠ j → Disjoint (X i) (X j))
    (hgp : InGeneralPosition ((Finset.univ.biUnion X : Finset (Euc 3)) : Set (Euc 3)))
    (hU4 : 4 ≤ (Finset.univ.biUnion X).card) :
    ∀ T : Finset (SepTask k), (∀ q ∈ T, ValidTask q) →
      ∃ Z : Fin k → Finset (Euc 3),
        (∀ i, Z i ⊆ X i) ∧
        (∀ i, 2 ^ ((T.filter fun q ↦ Involves i q).card) * (Z i).card ≥ (X i).card) ∧
        (∀ q ∈ T, Disjoint
          (convexHull ℝ ((Z q.1 ∪ Z q.2.1 : Finset (Euc 3)) : Set (Euc 3)))
          (convexHull ℝ ((Z q.2.2.1 ∪ Z q.2.2.2 : Finset (Euc 3)) : Set (Euc 3)))) := by
  intro T
  induction T using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨X, fun _ ↦ Finset.Subset.rfl, fun i ↦ ?_, fun q hq ↦ ?_⟩
    · simp
    · exact (Finset.notMem_empty q hq).elim
  | insert τ T hnot ih =>
    intro hT
    obtain ⟨i, j, i', j'⟩ := τ
    have hτV : ValidTask (i, j, i', j') := hT _ (Finset.mem_insert_self _ _)
    have hTV : ∀ q ∈ T, ValidTask q := fun q hq ↦ hT q (Finset.mem_insert_of_mem hq)
    obtain ⟨Z, hZsub, hZcount, hZsep⟩ := ih hTV
    obtain ⟨f, c, hf, hP, hM⟩ :=
      hamSandwich_halves (d := 3) (by norm_num) (by norm_num) (r := 2)
        ![Z i, Z j, Z i', Z j']
    have hPi : 2 * ((Z i).filter fun x ↦ c ≤ f x).card ≥ (Z i).card := by
      have := hP 0 (by decide); simpa using this
    have hPj : 2 * ((Z j).filter fun x ↦ c ≤ f x).card ≥ (Z j).card := by
      have := hP 1 (by decide); simpa using this
    have hMi : 2 * ((Z i').filter fun x ↦ f x ≤ c).card ≥ (Z i').card := by
      have := hM 2 (by decide); simpa using this
    have hMj : 2 * ((Z j').filter fun x ↦ f x ≤ c).card ≥ (Z j').card := by
      have := hM 3 (by decide); simpa using this
    -- the thinned family
    set Z' : Fin k → Finset (Euc 3) := fun m ↦
      if m = i ∨ m = j then (Z m).filter fun x ↦ c ≤ f x
      else if m = i' ∨ m = j' then (Z m).filter fun x ↦ f x ≤ c
      else Z m with hZ'def
    have hZ'Z : ∀ m, Z' m ⊆ Z m := by
      intro m
      by_cases h1 : m = i ∨ m = j
      · rw [hZ'def]; simp only [h1, if_true]; exact Finset.filter_subset _ _
      · by_cases h2 : m = i' ∨ m = j'
        · rw [hZ'def]; simp only [h1, h2, if_false, if_true]
          exact Finset.filter_subset _ _
        · rw [hZ'def]; simp only [h1, h2, if_false, if_true]
          exact Finset.Subset.rfl
    have hZ'sub : ∀ m, Z' m ⊆ X m := fun m ↦ (hZ'Z m).trans (hZsub m)
    have hZi : 2 * (Z' i).card ≥ (Z i).card := by
      have e : Z' i = (Z i).filter fun x ↦ c ≤ f x := by
        rw [hZ'def]; simp
      rw [e]; exact hPi
    have hZj : 2 * (Z' j).card ≥ (Z j).card := by
      have e : Z' j = (Z j).filter fun x ↦ c ≤ f x := by
        rw [hZ'def]; simp
      rw [e]; exact hPj
    have hZi' : 2 * (Z' i').card ≥ (Z i').card := by
      have hne1 : ¬(i' = i ∨ i' = j) := by
        rcases hτV with ⟨_, _, hlt, -, hj', -⟩
        push_neg
        exact ⟨ne_of_gt hlt, hj'.symm⟩
      have e : Z' i' = (Z i').filter fun x ↦ f x ≤ c := by
        rw [hZ'def]; simp [hne1]
      rw [e]; exact hMi
    have hZj' : 2 * (Z' j').card ≥ (Z j').card := by
      have hne2 : ¬(j' = i ∨ j' = j) := by
        rcases hτV with ⟨_, _, -, h1, -, h2⟩
        push_neg
        exact ⟨h1.symm, h2.symm⟩
      have e : Z' j' = (Z j').filter fun x ↦ f x ≤ c := by
        rw [hZ'def]; simp [hne2]
      rw [e]; exact hMj
    refine ⟨Z', hZ'sub, ?_, ?_⟩
    · intro m
      by_cases hm : Involves m (i, j, i', j')
      · have hcard : ((insert (i, j, i', j') T).filter fun q ↦ Involves m q).card =
            (T.filter fun q ↦ Involves m q).card + 1 := by
          rw [Finset.filter_insert]
          simp only [hm, if_true]
          rw [Finset.card_insert_of_notMem]
          simp only [Finset.mem_filter]
          exact fun hcon ↦ hnot hcon.1
        have h2 : 2 * (Z' m).card ≥ (Z m).card := by
          rcases hm with h | h | h | h <;> subst h
          · exact hZi
          · exact hZj
          · exact hZi'
          · exact hZj'
        calc (X m).card
            ≤ 2 ^ ((T.filter fun q ↦ Involves m q).card) * (Z m).card := hZcount m
          _ ≤ 2 ^ ((T.filter fun q ↦ Involves m q).card) * (2 * (Z' m).card) := by
              exact Nat.mul_le_mul_left _ h2
          _ = 2 ^ (((insert (i, j, i', j') T).filter fun q ↦ Involves m q).card) *
              (Z' m).card := by
              rw [hcard, pow_succ, mul_assoc]
      · have hcard : ((insert (i, j, i', j') T).filter fun q ↦ Involves m q).card =
            (T.filter fun q ↦ Involves m q).card := by
          rw [Finset.filter_insert]
          simp only [hm, if_false]
        have hZ'm : Z' m = Z m := by
          have h1 : ¬(m = i ∨ m = j) := by
            rintro (h | h)
            · exact hm (Or.inl h)
            · exact hm (Or.inr (Or.inl h))
          have h2 : ¬(m = i' ∨ m = j') := by
            rintro (h | h)
            · exact hm (Or.inr (Or.inr (Or.inl h)))
            · exact hm (Or.inr (Or.inr (Or.inr h)))
          rw [hZ'def]; simp [h1, h2]
        rw [hcard, hZ'm]; exact hZcount m
    · intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hqT
      · -- the new task: separated by the plane `f = c`
        refine disjoint_convexHull_of_halves (U := Finset.univ.biUnion X)
          (f := f) (c := c) hf ?_ ?_ ?_ ?_ ?_ hgp hU4
        · intro x hx
          rcases Finset.mem_union.1 hx with h | h
          · have : x ∈ (Z i).filter (fun x ↦ c ≤ f x) := by
              have e : Z' i = (Z i).filter fun x ↦ c ≤ f x := by
                rw [hZ'def]; simp
              rwa [← e]
            exact (Finset.mem_filter.1 this).2
          · have : x ∈ (Z j).filter (fun x ↦ c ≤ f x) := by
              have e : Z' j = (Z j).filter fun x ↦ c ≤ f x := by
                rw [hZ'def]; simp
              rwa [← e]
            exact (Finset.mem_filter.1 this).2
        · intro x hx
          rcases Finset.mem_union.1 hx with h | h
          · have : x ∈ (Z i').filter (fun x ↦ f x ≤ c) := by
              have hne1 : ¬(i' = i ∨ i' = j) := by
                rcases hτV with ⟨_, _, hlt, -, hj', -⟩
                push_neg
                exact ⟨ne_of_gt hlt, hj'.symm⟩
              have e : Z' i' = (Z i').filter fun x ↦ f x ≤ c := by
                rw [hZ'def]; simp [hne1]
              rwa [← e]
            exact (Finset.mem_filter.1 this).2
          · have : x ∈ (Z j').filter (fun x ↦ f x ≤ c) := by
              have hne2 : ¬(j' = i ∨ j' = j) := by
                rcases hτV with ⟨_, _, -, h1, -, h2⟩
                push_neg
                exact ⟨h1.symm, h2.symm⟩
              have e : Z' j' = (Z j').filter fun x ↦ f x ≤ c := by
                rw [hZ'def]; simp [hne2]
              rwa [← e]
            exact (Finset.mem_filter.1 this).2
        · -- disjointness of the two pairs of sets
          have hD : Disjoint (X i ∪ X j) (X i' ∪ X j') := by
            rw [Finset.disjoint_union_left, Finset.disjoint_union_right,
              Finset.disjoint_union_right]
            rcases hτV with ⟨_, _, hlt, h4, h5, h6⟩
            exact ⟨⟨hdisj i i' (ne_of_lt hlt), hdisj i j' h4⟩,
              ⟨hdisj j i' h5, hdisj j j' h6⟩⟩
          exact hD.mono
            (Finset.union_subset_union (hZ'sub i) (hZ'sub j))
            (Finset.union_subset_union (hZ'sub i') (hZ'sub j'))
        · -- `A ⊆ U`
          intro x hx
          rcases Finset.mem_union.1 hx with h | h
          · exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hZ'sub i h⟩
          · exact Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, hZ'sub j h⟩
        · -- `B ⊆ U`
          intro x hx
          rcases Finset.mem_union.1 hx with h | h
          · exact Finset.mem_biUnion.2 ⟨i', Finset.mem_univ _, hZ'sub i' h⟩
          · exact Finset.mem_biUnion.2 ⟨j', Finset.mem_univ _, hZ'sub j' h⟩
      · -- old tasks stay separated since `Z' ⊆ Z`
        have h := hZsep q hqT
        apply Disjoint.mono _ _ h
        · apply convexHull_mono
          rw [Finset.coe_subset]
          exact Finset.union_subset_union (hZ'Z q.1) (hZ'Z q.2.1)
        · apply convexHull_mono
          rw [Finset.coe_subset]
          exact Finset.union_subset_union (hZ'Z q.2.2.1) (hZ'Z q.2.2.2)

/-- **Counting.**  Each index `u` is involved in at most `k³` valid tasks: the
map sending a task involving `u` to `(partner, other-pair)` is injective into
`Fin k × Fin k × Fin k`. -/
lemma card_involves_le (u : Fin k) (T : Finset (SepTask k))
    (hT : ∀ q ∈ T, ValidTask q) :
    (T.filter fun q ↦ Involves u q).card ≤ k ^ 3 := by
  classical
  let φ : SepTask k → Fin k × Fin k × Fin k := fun q ↦
    if u = q.1 ∨ u = q.2.1
    then (if u = q.1 then q.2.1 else q.1, q.2.2.1, q.2.2.2)
    else (if u = q.2.2.1 then q.2.2.2 else q.2.2.1, q.1, q.2.1)
  have hle : (T.filter fun q ↦ Involves u q).card ≤
      (Finset.univ : Finset (Fin k × Fin k × Fin k)).card := by
    apply Finset.card_le_card_of_injOn φ (fun q _ ↦ Finset.mem_univ _)
    intro q₁ hq₁ q₂ hq₂ hφ
    have key : ∀ q ∈ T.filter (Involves u),
        q = (min u (φ q).1, max u (φ q).1, (φ q).2.1, (φ q).2.2) ∨
          q = ((φ q).2.1, (φ q).2.2, min u (φ q).1, max u (φ q).1) := by
      intro q hq
      obtain ⟨hqT, hu⟩ := Finset.mem_filter.1 hq
      have hV := hT q hqT
      obtain ⟨i, j, i', j'⟩ := q
      rcases hu with h | h | h | h
      · -- `u = i`
        left
        have hφe : φ (i, j, i', j') = (j, i', j') := by
          show (if u = i ∨ u = j then (if u = i then j else i, i', j')
              else (if u = i' then j' else i', i, j)) = (j, i', j')
          rw [if_pos (Or.inl h : u = i ∨ u = j), if_pos h]
        rw [hφe]
        have hle : u ≤ j := h ▸ hV.1
        rw [min_eq_left hle, max_eq_right hle]
        exact Prod.ext_iff.2 ⟨h.symm, rfl⟩
      · -- `u = j`
        left
        by_cases hui : u = i
        · have hφe : φ (i, j, i', j') = (j, i', j') := by
            show (if u = i ∨ u = j then (if u = i then j else i, i', j')
                else (if u = i' then j' else i', i, j)) = (j, i', j')
            rw [if_pos (Or.inl hui : u = i ∨ u = j), if_pos hui]
          rw [hφe]
          have hle : u ≤ j := le_of_eq h
          rw [min_eq_left hle, max_eq_right hle]
          exact Prod.ext_iff.2 ⟨hui.symm, rfl⟩
        · have hφe : φ (i, j, i', j') = (i, i', j') := by
            show (if u = i ∨ u = j then (if u = i then j else i, i', j')
                else (if u = i' then j' else i', i, j)) = (i, i', j')
            rw [if_pos (Or.inr h : u = i ∨ u = j), if_neg hui]
          rw [hφe]
          have hle : i ≤ u := h ▸ hV.1
          rw [min_eq_right hle, max_eq_left hle]
          exact Prod.ext_iff.2 ⟨rfl, Prod.ext_iff.2 ⟨h.symm, rfl⟩⟩
      · -- `u = i'`
        right
        have hn : ¬(u = i ∨ u = j) := by
          rcases hV with ⟨_, _, hlt, -, hji', -⟩
          push_neg
          exact ⟨fun hui ↦ (ne_of_lt hlt) (hui.symm.trans h),
            fun huj ↦ hji' (huj.symm.trans h)⟩
        have hφe : φ (i, j, i', j') = (j', i, j) := by
          show (if u = i ∨ u = j then (if u = i then j else i, i', j')
              else (if u = i' then j' else i', i, j)) = (j', i, j)
          rw [if_neg hn, if_pos h]
        rw [hφe]
        have hle : u ≤ j' := h ▸ hV.2.1
        rw [min_eq_left hle, max_eq_right hle]
        exact Prod.ext_iff.2 ⟨rfl, Prod.ext_iff.2 ⟨rfl, Prod.ext_iff.2 ⟨h.symm, rfl⟩⟩⟩
      · -- `u = j'`
        right
        have hn : ¬(u = i ∨ u = j) := by
          rcases hV with ⟨_, _, -, h4, -, h6⟩
          push_neg
          exact ⟨fun hui ↦ h4 (hui.symm.trans h),
            fun huj ↦ h6 (huj.symm.trans h)⟩
        have hφe : φ (i, j, i', j') = (i', i, j) := by
          show (if u = i ∨ u = j then (if u = i then j else i, i', j')
              else (if u = i' then j' else i', i, j)) = (i', i, j)
          rw [if_neg hn]
          by_cases hui' : u = i'
          · have h'' : j' = i' := h.symm.trans hui'
            rw [if_pos hui', h'']
          · rw [if_neg hui']
        rw [hφe]
        have hle : i' ≤ u := h ▸ hV.2.1
        rw [min_eq_right hle, max_eq_left hle]
        exact Prod.ext_iff.2 ⟨rfl, Prod.ext_iff.2 ⟨rfl, Prod.ext_iff.2 ⟨rfl, h.symm⟩⟩⟩
    rcases key q₁ (Finset.mem_coe.1 hq₁) with h1 | h1 <;>
      rcases key q₂ (Finset.mem_coe.1 hq₂) with h2 | h2
    · rw [hφ] at h1
      exact h1.trans h2.symm
    · exfalso
      have e1 : ((min u (φ q₁).1, max u (φ q₁).1, (φ q₁).2.1, (φ q₁).2.2) : SepTask k) ∈ T :=
        h1 ▸ (Finset.mem_filter.1 hq₁).1
      have e2 : (((φ q₂).2.1, (φ q₂).2.2, min u (φ q₂).1, max u (φ q₂).1) : SepTask k) ∈ T :=
        h2 ▸ (Finset.mem_filter.1 hq₂).1
      have l1 := (hT _ e1).2.2.1
      have l2 := (hT _ e2).2.2.1
      rw [hφ] at l1
      exact (lt_irrefl _) (lt_trans l1 l2)
    · exfalso
      have e1 : (((φ q₁).2.1, (φ q₁).2.2, min u (φ q₁).1, max u (φ q₁).1) : SepTask k) ∈ T :=
        h1 ▸ (Finset.mem_filter.1 hq₁).1
      have e2 : ((min u (φ q₂).1, max u (φ q₂).1, (φ q₂).2.1, (φ q₂).2.2) : SepTask k) ∈ T :=
        h2 ▸ (Finset.mem_filter.1 hq₂).1
      have l1 := (hT _ e1).2.2.1
      have l2 := (hT _ e2).2.2.1
      rw [hφ] at l1
      exact (lt_irrefl _) (lt_trans l1 l2)
    · rw [hφ] at h1
      exact h1.trans h2.symm
  have huniv : (Finset.univ : Finset (Fin k × Fin k × Fin k)).card = k ^ 3 := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
      Fintype.card_fin]
    ring
  rwa [huniv] at hle

/-- **Task existence.**  Every disjoint pair of index-pairs has a normalized
valid representative. -/
lemma task_exists (i j i' j' : Fin k)
    (h₁ : i ≠ i') (h₂ : i ≠ j') (h₃ : j ≠ i') (h₄ : j ≠ j') :
    ∃ q : SepTask k, ValidTask q ∧
      ((({q.1, q.2.1} : Finset (Fin k)) = {i, j} ∧
        ({q.2.2.1, q.2.2.2} : Finset (Fin k)) = {i', j'}) ∨
       (({q.1, q.2.1} : Finset (Fin k)) = {i', j'} ∧
        ({q.2.2.1, q.2.2.2} : Finset (Fin k)) = {i, j})) := by
  classical
  set a := min i j
  set b := max i j
  set c := min i' j'
  set d := max i' j'
  have hab : ({a, b} : Finset (Fin k)) = {i, j} := by
    show ({min i j, max i j} : Finset (Fin k)) = {i, j}
    rcases le_total i j with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h]
      exact Finset.pair_comm j i
  have hcd : ({c, d} : Finset (Fin k)) = {i', j'} := by
    show ({min i' j', max i' j'} : Finset (Fin k)) = {i', j'}
    rcases le_total i' j' with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h]
      exact Finset.pair_comm j' i'
  have hac : a ≠ c := by
    show min i j ≠ min i' j'
    rcases min_choice i j with h | h <;> rcases min_choice i' j' with h' | h' <;>
      rw [h, h']
    · exact h₁
    · exact h₂
    · exact h₃
    · exact h₄
  have had : a ≠ d := by
    show min i j ≠ max i' j'
    rcases min_choice i j with h | h <;> rcases max_choice i' j' with h' | h' <;>
      rw [h, h']
    · exact h₁
    · exact h₂
    · exact h₃
    · exact h₄
  have hbc : b ≠ c := by
    show max i j ≠ min i' j'
    rcases max_choice i j with h | h <;> rcases min_choice i' j' with h' | h' <;>
      rw [h, h']
    · exact h₁
    · exact h₂
    · exact h₃
    · exact h₄
  have hbd : b ≠ d := by
    show max i j ≠ max i' j'
    rcases max_choice i j with h | h <;> rcases max_choice i' j' with h' | h' <;>
      rw [h, h']
    · exact h₁
    · exact h₂
    · exact h₃
    · exact h₄
  by_cases hlt : a < c
  · exact ⟨(a, b, c, d), ⟨min_le_max, min_le_max, hlt, had, hbc, hbd⟩,
      Or.inl ⟨hab, hcd⟩⟩
  · have hca : c < a := lt_of_le_of_ne (le_of_not_gt hlt) hac.symm
    exact ⟨(c, d, a, b), ⟨min_le_max, min_le_max, hca, hbc.symm, had.symm, hbd.symm⟩,
        Or.inr ⟨hcd, hab⟩⟩

/-- `({a,b}).biUnion Z = Z a ∪ Z b`. -/
lemma biUnion_pair (Z : Fin k → Finset (Euc 3)) (a b : Fin k) :
    ({a, b} : Finset (Fin k)).biUnion Z = Z a ∪ Z b := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_union]
  constructor
  · rintro ⟨m, hm | rfl, hx⟩ <;> [exact Or.inl (hm ▸ hx); skip]
    exact Or.inr hx
  · rintro (hx | hx)
    · exact ⟨a, Or.inl rfl, hx⟩
    · exact ⟨b, Or.inr rfl, hx⟩

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
  classical
  rcases Nat.lt_or_ge 1 k with hk | hk
  · -- `k ≥ 2`: run the induction over all normalized tasks
    have h0 : (X ⟨0, by omega⟩).card ≥ 4 := by
      have h1 : 2 ^ (k ^ 3) ≤ (X ⟨0, by omega⟩).card := hsize _
      have h2 : 8 ≤ k ^ 3 := by
        calc (8 : ℕ) = 2 ^ 3 := by norm_num
          _ ≤ k ^ 3 := Nat.pow_le_pow_left (by omega) _
      have h3 : (4 : ℕ) ≤ 2 ^ (k ^ 3) := by
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k ^ 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hU4 : 4 ≤ (Finset.univ.biUnion X).card :=
      le_trans h0 (Finset.card_mono
        (Finset.subset_biUnion_of_mem X (Finset.mem_univ _)))
    obtain ⟨Z, hZsub, hZcount, hZsep⟩ := exists_thinned X hdisj hgp hU4
      (Finset.univ.filter ValidTask) (fun q hq ↦ (Finset.mem_filter.1 hq).2)
    refine ⟨Z, hZsub, fun i ↦ ?_, ?_⟩
    · have hmi : ((Finset.univ.filter ValidTask).filter fun q ↦ Involves i q).card
          ≤ k ^ 3 :=
        card_involves_le i _ (fun q hq ↦ (Finset.mem_filter.1 hq).2)
      calc (X i).card
          ≤ 2 ^ (((Finset.univ.filter ValidTask).filter fun q ↦ Involves i q).card)
            * (Z i).card := hZcount i
        _ ≤ 2 ^ (k ^ 3) * (Z i).card := by
            apply Nat.mul_le_mul_right
            exact Nat.pow_le_pow_right (by norm_num) hmi
    · intro i j i' j' h₁ h₂ h₃ h₄
      obtain ⟨q, hqV, hp⟩ := task_exists i j i' j' h₁ h₂ h₃ h₄
      obtain ⟨a, b, c, d⟩ := q
      have hd := hZsep (a, b, c, d)
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hqV⟩)
      rcases hp with ⟨hp1, hp2⟩ | ⟨hp1, hp2⟩
      · have e1 : (Z a ∪ Z b : Finset (Euc 3)) = Z i ∪ Z j := by
          rw [← biUnion_pair Z a b, hp1, biUnion_pair]
        have e2 : (Z c ∪ Z d : Finset (Euc 3)) = Z i' ∪ Z j' := by
          rw [← biUnion_pair Z c d, hp2, biUnion_pair]
        rwa [e1, e2] at hd
      · have e1 : (Z a ∪ Z b : Finset (Euc 3)) = Z i' ∪ Z j' := by
          rw [← biUnion_pair Z a b, hp1, biUnion_pair]
        have e2 : (Z c ∪ Z d : Finset (Euc 3)) = Z i ∪ Z j := by
          rw [← biUnion_pair Z c d, hp2, biUnion_pair]
        rw [e1, e2] at hd
        exact hd.symm
  · -- `k ≤ 1`: no two distinct indices exist, `TwoSeparated` is vacuous
    refine ⟨X, fun _ ↦ Finset.Subset.rfl, fun i ↦ ?_, ?_⟩
    · have h2 : (1 : ℕ) ≤ 2 ^ (k ^ 3) := Nat.one_le_two_pow
      calc (X i).card = 1 * (X i).card := by simp
        _ ≤ 2 ^ (k ^ 3) * (X i).card := Nat.mul_le_mul_right _ h2
    · intro i j i' j' h₁ _ _ _
      exfalso
      apply h₁
      apply Fin.ext
      have h1 : i.val < 1 := lt_of_lt_of_le i.isLt hk
      have h2 : i'.val < 1 := lt_of_lt_of_le i'.isLt hk
      omega

end
