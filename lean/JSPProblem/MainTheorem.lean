import JSPProblem.Projection
import JSPProblem.Separation
import JSPProblem.SeparationRamsey
import JSPProblem.SeparationHalving
import JSPProblem.Caps3D
import JSPProblem.PorValtr

/-!
# JSP-000527 — Theorem 1.1 and the headline `ES_d(n) = 2^{o(n)}`

* `es_three_subexponential` — **Theorem 1.1** of Pohoata–Zakharov verbatim:
  for every `ε > 0` there is `n₀` such that every general-position
  `X ⊆ ℝ³` with `|X| ≥ 2^{ε n}`, `n ≥ n₀`, contains `n` points in convex
  position.  Its proof is the §3 assembly: apply `porValtr_positiveFraction`
  to the projection with `k₀ = n^{1/4}`, thin to a 2-separated collection via
  `prop_2_5`, extract the above/below structure via `cor_2_4`, build the
  two 3-edge polytopes of Proposition 3.1, colour triples by the
  `P¹`-free/`P²`-free dichotomy (Dilworth), Ramsey to a monochromatic clique,
  and apply `prop_2_1` — contradiction with `|X| ≥ 2^{εn}` unless a convex
  `n`-set exists.
* `convexSubset_forcing_points_exp` — the headline: `ES_d(n) = 2^{o(n)}` for
  all `d ≥ 3`, proved from the `d = 3` theorem by iterating
  `forcesConvex_succ` (Valtr's projection argument).
-/

noncomputable section

open Filter

open scoped Classical

section CombinatorialHelpers

variable {α : Type*} [DecidableEq α]

/-- `c` is an `r`-chain inside `s` whose maximum element is `x`: every element
of `c` is `x` itself or `r`-below `x`, and `c` is totally ordered by `r`. -/
private def chainTo (s : Finset α) (r : α → α → Prop) [DecidableRel r]
    (x : α) (c : Finset α) : Prop :=
  c ⊆ s ∧ x ∈ c ∧ (∀ y ∈ c, y = x ∨ r y x) ∧
    ∀ a ∈ c, ∀ b ∈ c, a ≠ b → r a b ∨ r b a

private instance (s : Finset α) (r : α → α → Prop) [DecidableRel r] (x : α) :
    DecidablePred (chainTo s r x) := fun _ ↦ inferInstance

/-- The rank of `x` in `(s, r)`: cardinality of the largest `r`-chain in `s`
whose maximum is `x`.  For `x ∈ s` this is at least `1` (the chain `{x}`). -/
private def chainRank (s : Finset α) (r : α → α → Prop) [DecidableRel r]
    (x : α) : ℕ :=
  (s.powerset.filter (chainTo s r x)).sup Finset.card

private theorem chainRank_pos (s : Finset α) (r : α → α → Prop) [DecidableRel r]
    {x : α} (hx : x ∈ s) : 1 ≤ chainRank s r x := by
  have hmem : {x} ∈ s.powerset.filter (chainTo s r x) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.singleton_subset_iff.mpr hx, ?_⟩
    refine ⟨Finset.singleton_subset_iff.mpr hx, Finset.mem_singleton_self x,
      fun y hy ↦ Or.inl (Finset.mem_singleton.mp hy), ?_⟩
    intro a ha b hb hab
    simp only [Finset.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  calc 1 = ({x} : Finset α).card := (Finset.card_singleton x).symm
    _ ≤ chainRank s r x :=
        Finset.le_sup (f := Finset.card) hmem

private theorem chainRank_le_card (s : Finset α) (r : α → α → Prop)
    [DecidableRel r] (x : α) : chainRank s r x ≤ s.card := by
  refine Finset.sup_le ?_
  intro c hc
  rw [Finset.mem_filter, Finset.mem_powerset] at hc
  exact Finset.card_le_card hc.1

/-- The rank is attained: for `x ∈ s` there is a chain of size `rank x`. -/
private theorem exists_chainTo_card_chainRank (s : Finset α) (r : α → α → Prop)
    [DecidableRel r] {x : α} (hx : x ∈ s) :
    ∃ c : Finset α, chainTo s r x c ∧ c.card = chainRank s r x := by
  classical
  have hne : (s.powerset.filter (chainTo s r x)).Nonempty := by
    refine ⟨{x}, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.singleton_subset_iff.mpr hx, ?_⟩
    refine ⟨Finset.singleton_subset_iff.mpr hx, Finset.mem_singleton_self x,
      fun y hy ↦ Or.inl (Finset.mem_singleton.mp hy), ?_⟩
    intro a ha b hb hab
    simp only [Finset.mem_singleton] at ha hb
    exact absurd (ha.trans hb.symm) hab
  obtain ⟨c, hc, hcs⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  exact ⟨c, (Finset.mem_filter.mp hc).2, hcs.symm⟩

/-- Strictly `r`-comparable elements have strictly increasing rank. -/
private theorem chainRank_lt_of_rel (s : Finset α) (r : α → α → Prop)
    [DecidableRel r] (hirr : ∀ x, ¬ r x x)
    (htr : ∀ ⦃x y z⦄, r x y → r y z → r x z)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) (hxy : r x y) :
    chainRank s r x < chainRank s r y := by
  obtain ⟨c, hcto, hcard⟩ := exists_chainTo_card_chainRank s r hx
  obtain ⟨hcsub, hxc, hbelow, hchain⟩ := hcto
  have hyc : y ∉ c := by
    intro h
    rcases hbelow y h with rfl | h'
    · exact hirr _ hxy
    · exact hirr _ (htr hxy h')
  have hmem : insert y c ∈ s.powerset.filter (chainTo s r y) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.insert_subset hy hcsub, ?_⟩
    refine ⟨Finset.insert_subset hy hcsub, Finset.mem_insert_self y c, ?_, ?_⟩
    · intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hz
      · exact Or.inl rfl
      · rcases hbelow z hz with rfl | hz'
        · exact Or.inr hxy
        · exact Or.inr (htr hz' hxy)
    · intro a ha b hb hab
      rw [Finset.mem_insert] at ha hb
      rcases ha with rfl | ha
      · rcases hb with rfl | hb
        · exact absurd rfl hab
        · rcases hbelow b hb with rfl | hb'
          · exact Or.inr hxy
          · exact Or.inr (htr hb' hxy)
      · rcases hb with rfl | hb
        · rcases hbelow a ha with rfl | ha'
          · exact Or.inl hxy
          · exact Or.inl (htr ha' hxy)
        · exact hchain a ha b hb hab
  calc chainRank s r x = c.card := hcard.symm
    _ < (insert y c).card := by
        rw [Finset.card_insert_of_notMem hyc]; exact lt_add_one _
    _ ≤ chainRank s r y := Finset.le_sup (f := Finset.card) hmem

/-- **Mirsky-type lemma.** In a finite set equipped with a strict order `r`,
either there is an `r`-chain or an `r`-antichain of size at least `√|s|`
(more precisely, of size `t` with `t² ≥ |s|`). -/
theorem exists_isChain_or_isAntichain_sq (s : Finset α) (r : α → α → Prop)
    [DecidableRel r] (hirr : ∀ x, ¬ r x x)
    (htr : ∀ ⦃x y z⦄, r x y → r y z → r x z) :
    ∃ t : Finset α, t ⊆ s ∧ s.card ≤ t.card ^ 2 ∧
      ((∀ x ∈ t, ∀ y ∈ t, x ≠ y → r x y ∨ r y x) ∨
        ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ¬ r x y) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨∅, by simp⟩
  -- `h` = maximum rank occurring in `s`.
  set R := s.image (chainRank s r) with hR
  have hRne : R.Nonempty := Finset.image_nonempty.mpr hs
  set h := R.max' hRne
  obtain ⟨x₀, hx₀, hx₀r⟩ : ∃ x₀ ∈ s, chainRank s r x₀ = h := by
    have : h ∈ R := Finset.max'_mem R hRne
    rw [hR, Finset.mem_image] at this
    obtain ⟨x₀, hx₀, hx₀e⟩ := this
    exact ⟨x₀, hx₀, hx₀e⟩
  have hrank_le : ∀ x ∈ s, chainRank s r x ≤ h := fun x hx ↦
    Finset.le_max' R _ (Finset.mem_image_of_mem _ hx)
  have hrank_pos : ∀ x ∈ s, 1 ≤ chainRank s r x :=
    fun _ hx ↦ chainRank_pos s r hx
  -- Case 1: the longest chain has length `≥ √|s| + 1`-ish; use it directly.
  rcases Nat.lt_or_ge (Nat.sqrt s.card) h with hlt | hge
  · obtain ⟨c, hcto, hcard⟩ := exists_chainTo_card_chainRank s r hx₀
    obtain ⟨hcsub, -, -, hchain⟩ := hcto
    refine ⟨c, hcsub, ?_, Or.inl hchain⟩
    rw [hx₀r] at hcard
    calc s.card ≤ (Nat.sqrt s.card + 1) ^ 2 := (Nat.lt_succ_sqrt' _).le
      _ ≤ c.card ^ 2 := by
          apply Nat.pow_le_pow_left
          rw [hcard]
          exact hlt
  · -- Case 2: all chains short.  The rank fibers partition `s` into at most
    -- `h` antichains, so some fiber is large.
    have hspos : 0 < s.card := Finset.card_pos.mpr hs
    have hhpos : 1 ≤ h := by
      rw [← hx₀r]; exact hrank_pos x₀ hx₀
    -- the fibers of `chainRank`
    set fib := fun i ↦ s.filter (fun x ↦ chainRank s r x = i) with hfib
    have hcover : s ⊆ (Finset.Icc 1 h).biUnion fib := by
      intro x hx
      simp only [Finset.mem_biUnion, Finset.mem_Icc]
      exact ⟨chainRank s r x, ⟨hrank_pos x hx, hrank_le x hx⟩,
        by simp [hfib, hx]⟩
    have hcard_le : s.card ≤ h * (Finset.Icc 1 h).sup (fun i ↦ (fib i).card) := by
      calc s.card ≤ ((Finset.Icc 1 h).biUnion fib).card :=
            Finset.card_le_card hcover
        _ ≤ ∑ i ∈ Finset.Icc 1 h, (fib i).card := Finset.card_biUnion_le
        _ ≤ ∑ _i ∈ Finset.Icc 1 h, (Finset.Icc 1 h).sup (fun i ↦ (fib i).card) :=
            Finset.sum_le_sum fun i hi ↦
              Finset.le_sup (f := fun i ↦ (fib i).card) hi
        _ = h * (Finset.Icc 1 h).sup (fun i ↦ (fib i).card) := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc,
              Nat.add_sub_cancel, Nat.cast_id]
    -- the supremum is attained at some fiber index
    obtain ⟨i₀, hi₀, hi₀eq⟩ :=
      Finset.exists_mem_eq_sup (Finset.Icc 1 h)
        (Finset.nonempty_Icc.mpr hhpos) (fun i ↦ (fib i).card)
    refine ⟨fib i₀, Finset.filter_subset _ _, ?_, ?_⟩
    · calc s.card ≤ h * (fib i₀).card := hi₀eq ▸ hcard_le
        _ ≤ (fib i₀).card * (fib i₀).card := by
            apply Nat.mul_le_mul_right
            -- `h ≤ fib i₀.card`: from `h * fib ≥ |s| ≥ h²`
            have hsqrt : h * h ≤ s.card := by
              calc h * h ≤ (Nat.sqrt s.card) * (Nat.sqrt s.card) := by
                    apply Nat.mul_le_mul <;> exact hge
                _ ≤ s.card := Nat.sqrt_le _
            -- `fib i₀.card ≥ h`: since `h * fib i₀.card ≥ s.card ≥ h²`
            have hge' : h ≤ (fib i₀).card := by
              by_contra hcon
              push_neg at hcon
              have : h * (fib i₀).card < h * h :=
                Nat.mul_lt_mul_of_pos_left hcon hhpos
              have := calc s.card ≤ h * (fib i₀).card := hi₀eq ▸ hcard_le
                _ < h * h := this
                _ ≤ s.card := hsqrt
              exact lt_irrefl _ this
            exact hge'
        _ = (fib i₀).card ^ 2 := (pow_two _).symm
    · right
      intro x hx y hy hxyrel hr
      rw [hfib, Finset.mem_filter] at hx hy
      have := chainRank_lt_of_rel s r hirr htr hx.1 hy.1 hr
      rw [hx.2, hy.2] at this
      exact lt_irrefl _ this

/-- An `r`-chain (totally ordered by `r`) or `r`-antichain of card `≥ √|s|`,
stated with antichain symmetric in both directions. -/
theorem exists_isChain_or_isAntichain_sq' (s : Finset α) (r : α → α → Prop)
    [DecidableRel r] (hirr : ∀ x, ¬ r x x)
    (htr : ∀ ⦃x y z⦄, r x y → r y z → r x z) :
    ∃ t : Finset α, t ⊆ s ∧ s.card ≤ t.card ^ 2 ∧
      ((∀ x ∈ t, ∀ y ∈ t, x ≠ y → r x y ∨ r y x) ∨
        ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ¬ r x y ∧ ¬ r y x) := by
  obtain ⟨t, hts, hcard, h | h⟩ := exists_isChain_or_isAntichain_sq s r hirr htr
  · exact ⟨t, hts, hcard, Or.inl h⟩
  · refine ⟨t, hts, hcard, Or.inr ?_⟩
    intro x hx y hy hxy
    exact ⟨h x hx y hy hxy, h y hy x hx (Ne.symm hxy)⟩

end CombinatorialHelpers

/-- **Theorem 1.1** of Pohoata–Zakharov, *Convex polytopes from fewer points*:
`ES₃(n) = 2^{o(n)}`.  For any `ε > 0` there exists `n₀(ε)` such that for every
`n ≥ n₀`, every set `X ⊆ ℝ³` in general position with `|X| ≥ 2^{εn}` contains
`n` points in convex position. -/
theorem es_three_subexponential (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ X : Finset (Euc 3),
      InGeneralPosition (X : Set (Euc 3)) →
      (2:ℝ) ^ (ε * (n:ℝ)) ≤ (X.card : ℝ) →
      ∃ S ⊆ X, S.card = n ∧ InConvexPosition S := by
  sorry

/-- `2^{ε·n} → ∞` as `n → ∞` for `ε > 0`. -/
theorem tendsto_two_pow (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ (2:ℝ) ^ (ε * (n:ℝ))) atTop atTop := by
  have h1 : (1:ℝ) < (2:ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
  have heq : (fun n : ℕ ↦ (2:ℝ) ^ (ε * (n:ℝ))) = fun n ↦ ((2:ℝ) ^ ε) ^ n := by
    ext n
    rw [← Real.rpow_natCast ((2:ℝ) ^ ε) n, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  rw [heq]
  exact tendsto_pow_atTop_atTop_of_one_lt h1

/-- **Headline theorem — `ES_d(n) = 2^{o(n)}` for all `d ≥ 3`** (the negative
answer to the catalog question "is the forcing number exponential in `n`?").

For every `ε > 0` there exists `n₀` such that for all `n ≥ n₀`, every
general-position set `X ⊆ ℝ^d` with `|X| ≥ 2^{εn}` contains an `n`-element
subset in convex position. -/
theorem convexSubset_forcing_points_exp {d : ℕ} (hd : 3 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ X : Finset (Euc d),
      InGeneralPosition (X : Set (Euc d)) →
      (2:ℝ) ^ (ε * (n:ℝ)) ≤ (X.card : ℝ) →
      ∃ S ⊆ X, S.card = n ∧ InConvexPosition S := by
  obtain ⟨n₀, hn₀⟩ := es_three_subexponential ε hε
  -- choose the effective threshold: `n ≥ n₀` and `2^{εn} ≥ d+2`.
  obtain ⟨m, hm0, hmN⟩ : ∃ m : ℕ, n₀ ≤ m ∧
      (d + 2 : ℝ) ≤ (2:ℝ) ^ (ε * (m:ℝ)) := by
    obtain ⟨m, hm⟩ := ((tendsto_two_pow ε hε).eventually_ge_atTop (d + 2)).and
      (eventually_ge_atTop n₀) |>.exists
    exact ⟨m, hm.2, hm.1⟩
  refine ⟨m, fun n hn X hX hcard ↦ ?_⟩
  have hn₀' : n₀ ≤ n := le_trans hm0 hn
  have hN : (d + 2 : ℝ) ≤ (2:ℝ) ^ (ε * (n:ℝ)) := by
    refine le_trans hmN ?_
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn) hε.le
  set N := ⌈(2:ℝ) ^ (ε * (n:ℝ))⌉₊ with hNdef
  have hNd : d + 2 ≤ N := by
    have : (d + 2 : ℝ) ≤ (N : ℝ) := le_trans hN (Nat.le_ceil _)
    exact_mod_cast this
  have hNcard : N ≤ X.card := (Nat.ceil_le).2 hcard
  -- `ForcesConvex 3 N n` is exactly the `d = 3` theorem.
  have hfc3 : ForcesConvex 3 N n := fun Y hY hNY ↦
    hn₀ n hn₀' Y hY (le_trans (Nat.le_ceil _) (by exact_mod_cast hNY))
  -- iterate the projection inequality up to dimension `d`.
  have iter : ∀ k ≤ d, 3 ≤ k → ForcesConvex k N n := by
    intro k hkd hk3
    induction k, hk3 using Nat.le_induction with
    | base => exact hfc3
    | succ k' hk3' ih =>
        exact forcesConvex_succ (d := k') (N := N) (n := n)
          (by omega) (by omega) (ih (Nat.le_of_succ_le hkd))
  exact iter d le_rfl hd X hX hNcard

end
