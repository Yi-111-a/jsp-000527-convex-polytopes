import JSPProblem.Projection
import JSPProblem.Separation
import JSPProblem.SeparationHalving
import JSPProblem.Caps3D
import JSPProblem.PorValtr
import JSPProblem.PlanarDichotomy
import JSPProblem.SeparationRamsey

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

  Status: the theorem is reduced to the single geometric-core lemma
  `card_le_capBound_mul_exp` (which packages the whole chain above), and the
  final asymptotic estimate is fully proved in `capBound_eventually`.  The
  support-region analysis (`pv_region_inner_side`, `collectionConvex_of_regions`)
  and the projection normalization (`exists_normalization`) needed by the
  geometric core are already formalized below.
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

section GeometricInfrastructure


private abbrev supportOf {k : ℕ} (x : Fin (k + 1) → Euc 2) (σ : Bool) (i : Fin k) :
    Set (Euc 2) :=
  SupportRegion
    (x ⟨(i.val + k) % (k + 1), Nat.mod_lt _ (by omega)⟩)
    (x ⟨i.val, by omega⟩)
    (x ⟨i.val + 1, by omega⟩)
    (x ⟨(i.val + 2) % (k + 1), Nat.mod_lt _ (by omega)⟩) σ
/-- Twice the signed area of the oriented triangle `u v w` (the same quantity
as `CupsCaps.cross`, which is private there). -/
private def pvCross (u v w : Euc 2) : ℝ :=
  (v 0 - u 0) * (w 1 - u 1) - (v 1 - u 1) * (w 0 - u 0)

/-- The slope of the directed segment `u v`. -/
private noncomputable def pvSl (u v : Euc 2) : ℝ := (v 1 - u 1) / (v 0 - u 0)

/-- The height at abscissa `t` of the line through `u` and `v`. -/
private noncomputable def pvHgt (u v : Euc 2) (t : ℝ) : ℝ :=
  u 1 + pvSl u v * (t - u 0)

/-- The sign distinguishing cap (`σ = true`, `ε = 1`) from cup
(`σ = false`, `ε = -1`) in the uniform statements. -/
private def pvSgn (σ : Bool) : ℝ := if σ then 1 else -1

private lemma pvCross_self (u v : Euc 2) : pvCross u u v = 0 := by
  unfold pvCross; ring

private lemma pvCross_left (u v : Euc 2) : pvCross u v u = 0 := by
  unfold pvCross; ring

private lemma pvCross_right (u v : Euc 2) : pvCross u v v = 0 := by
  unfold pvCross; ring

private lemma pvCross_swap (u v w : Euc 2) : pvCross v u w = -pvCross u v w := by
  unfold pvCross; ring

private lemma pvCross_cyc (u v w : Euc 2) : pvCross u v w = pvCross v w u := by
  unfold pvCross; ring

private lemma mem_LeftOf_iff (u v p : Euc 2) : p ∈ LeftOf u v ↔ 0 < pvCross u v p :=
  Iff.rfl

private lemma mem_RightOf_iff (u v p : Euc 2) : p ∈ RightOf u v ↔ pvCross u v p < 0 := by
  show 0 < pvCross v u p ↔ pvCross u v p < 0
  rw [pvCross_swap]; constructor <;> intro h <;> linarith

/-- Membership in a support region, expressed uniformly in `σ` as sign
conditions on `pvCross`. -/
private lemma mem_supportOf_iff {k : ℕ} {x : Fin (k + 1) → Euc 2} {σ : Bool}
    {j : Fin k} {p : Euc 2} :
    p ∈ supportOf x σ j ↔
      0 < pvSgn σ * pvCross (x ⟨j.val, by omega⟩) (x ⟨j.val + 1, by omega⟩) p ∧
      pvSgn σ * pvCross (x ⟨(j.val + k) % (k + 1), Nat.mod_lt _ (by omega)⟩)
        (x ⟨j.val, by omega⟩) p < 0 ∧
      pvSgn σ * pvCross (x ⟨j.val + 1, by omega⟩)
        (x ⟨(j.val + 2) % (k + 1), Nat.mod_lt _ (by omega)⟩) p < 0 := by
  cases σ
  · -- `σ = false` (cup): region = `RightOf e ∩ LeftOf l ∩ LeftOf r`
    have e : supportOf x false j =
        (RightOf (x ⟨j.val, by omega⟩) (x ⟨j.val + 1, by omega⟩) ∩
          LeftOf (x ⟨(j.val + k) % (k + 1), Nat.mod_lt _ (by omega)⟩)
            (x ⟨j.val, by omega⟩)) ∩
        LeftOf (x ⟨j.val + 1, by omega⟩)
          (x ⟨(j.val + 2) % (k + 1), Nat.mod_lt _ (by omega)⟩) := rfl
    rw [e, Set.mem_inter_iff, Set.mem_inter_iff, mem_RightOf_iff,
      mem_LeftOf_iff, mem_LeftOf_iff, show pvSgn false = (-1 : ℝ) from rfl]
    exact ⟨fun h ↦ ⟨by linarith [h.1.1], by linarith [h.1.2], by linarith [h.2]⟩,
      fun h ↦ ⟨⟨by linarith [h.1], by linarith [h.2.1]⟩, by linarith [h.2.2]⟩⟩
  · -- `σ = true` (cap): region = `LeftOf e ∩ RightOf l ∩ RightOf r`
    have e : supportOf x true j =
        (LeftOf (x ⟨j.val, by omega⟩) (x ⟨j.val + 1, by omega⟩) ∩
          RightOf (x ⟨(j.val + k) % (k + 1), Nat.mod_lt _ (by omega)⟩)
            (x ⟨j.val, by omega⟩)) ∩
        RightOf (x ⟨j.val + 1, by omega⟩)
          (x ⟨(j.val + 2) % (k + 1), Nat.mod_lt _ (by omega)⟩) := rfl
    rw [e, Set.mem_inter_iff, Set.mem_inter_iff, mem_LeftOf_iff,
      mem_RightOf_iff, mem_RightOf_iff, show pvSgn true = (1 : ℝ) from rfl]
    exact ⟨fun h ↦ ⟨by linarith [h.1.1], by linarith [h.1.2], by linarith [h.2]⟩,
      fun h ↦ ⟨⟨by linarith [h.1], by linarith [h.2.1]⟩, by linarith [h.2.2]⟩⟩

/-- The signed area expressed through the height function of the edge line. -/
private lemma pvCross_eq_hgt {u v : Euc 2} (h : v 0 ≠ u 0) (p : Euc 2) :
    pvCross u v p = (v 0 - u 0) * (p 1 - pvHgt u v (p 0)) := by
  unfold pvCross pvHgt pvSl
  field_simp
  ring

/-- The height function recomputed at the right endpoint. -/
private lemma pvHgt_at_right {u v : Euc 2} (h : v 0 ≠ u 0) (t : ℝ) :
    pvHgt u v t = v 1 + pvSl u v * (t - v 0) := by
  unfold pvHgt pvSl
  field_simp
  ring

/-- The height function is affine in `t` with slope `pvSl u v`. -/
private lemma pvHgt_affine (u v : Euc 2) (t t₀ : ℝ) :
    pvHgt u v t = pvHgt u v t₀ + pvSl u v * (t - t₀) := by
  unfold pvHgt; ring

/-- From the cup/cap condition: in a cap every increasing-`x` triple has
negative signed area (and the mirror statement for cups). -/
private lemma pvCross_neg_of_isCap {P : Finset (Euc 2)} (hP : IsCap P)
    {u v w : Euc 2} (hu : u ∈ P) (hv : v ∈ P) (hw : w ∈ P)
    (huv : u 0 < v 0) (hvw : v 0 < w 0) : pvCross u v w < 0 := by
  obtain ⟨a, b, hvb, hbelow⟩ := hP v hv
  have hu' : u 1 < a * u 0 + b := hbelow u hu (fun e ↦ (by rw [e] at huv; exact lt_irrefl _ huv))
  have hw' : w 1 < a * w 0 + b := hbelow w hw (fun e ↦ (by rw [e] at hvw; exact lt_irrefl _ hvw))
  have h1 : w 1 - v 1 < a * (w 0 - v 0) := by linarith
  have h2 : v 1 - u 1 > a * (v 0 - u 0) := by linarith
  have e : pvCross u v w = (v 0 - u 0) * (w 1 - v 1) - (v 1 - u 1) * (w 0 - v 0) := by
    unfold pvCross; ring
  have hstep : pvCross u v w <
      (v 0 - u 0) * (a * (w 0 - v 0)) - (a * (v 0 - u 0)) * (w 0 - v 0) := by
    rw [e]
    apply sub_lt_sub
    · exact mul_lt_mul_of_pos_left h1 (sub_pos.mpr huv)
    · exact mul_lt_mul_of_pos_right h2 (sub_pos.mpr hvw)
  have heq : (v 0 - u 0) * (a * (w 0 - v 0)) - (a * (v 0 - u 0)) * (w 0 - v 0) = 0 := by ring
  linarith

/-- The mirror statement for cups: increasing-`x` triples have positive
signed area. -/
private lemma pvCross_pos_of_isCup {P : Finset (Euc 2)} (hP : IsCup P)
    {u v w : Euc 2} (hu : u ∈ P) (hv : v ∈ P) (hw : w ∈ P)
    (huv : u 0 < v 0) (hvw : v 0 < w 0) : 0 < pvCross u v w := by
  obtain ⟨a, b, hvb, habove⟩ := hP v hv
  have hu' : u 1 > a * u 0 + b := habove u hu (fun e ↦ (by rw [e] at huv; exact lt_irrefl _ huv))
  have hw' : w 1 > a * w 0 + b := habove w hw (fun e ↦ (by rw [e] at hvw; exact lt_irrefl _ hvw))
  have h1 : w 1 - v 1 > a * (w 0 - v 0) := by linarith
  have h2 : v 1 - u 1 < a * (v 0 - u 0) := by linarith
  have e : pvCross u v w = (v 0 - u 0) * (w 1 - v 1) - (v 1 - u 1) * (w 0 - v 0) := by
    unfold pvCross; ring
  have hstep : pvCross u v w >
      (v 0 - u 0) * (a * (w 0 - v 0)) - (a * (v 0 - u 0)) * (w 0 - v 0) := by
    rw [e]
    apply sub_lt_sub
    · exact mul_lt_mul_of_pos_left h1 (sub_pos.mpr huv)
    · exact mul_lt_mul_of_pos_right h2 (sub_pos.mpr hvw)
  have heq : (v 0 - u 0) * (a * (w 0 - v 0)) - (a * (v 0 - u 0)) * (w 0 - v 0) = 0 := by ring
  linarith

/-- The signed area factors through a slope difference (chord vs. first
edge). -/
private lemma pvCross_eq_mid {u v w : Euc 2} (huv : u 0 < v 0) (huw : u 0 < w 0) :
    pvCross u v w = (v 0 - u 0) * (w 0 - u 0) * (pvSl u w - pvSl u v) := by
  unfold pvCross pvSl
  have h1 : v 0 - u 0 ≠ 0 := ne_of_gt (sub_pos.mpr huv)
  have h2 : w 0 - u 0 ≠ 0 := ne_of_gt (sub_pos.mpr huw)
  field_simp

/-- The signed area factors through a slope difference (second edge vs.
chord). -/
private lemma pvCross_eq_left {u v w : Euc 2} (hvw : v 0 < w 0) (huw : u 0 < w 0) :
    pvCross u v w = (w 0 - v 0) * (w 0 - u 0) * (pvSl v w - pvSl u w) := by
  unfold pvCross pvSl
  have h1 : w 0 - v 0 ≠ 0 := ne_of_gt (sub_pos.mpr hvw)
  have h2 : w 0 - u 0 ≠ 0 := ne_of_gt (sub_pos.mpr huw)
  field_simp
  ring

/-- Cancelling a positive middle factor inside a `pvSgn`-scaled product. -/
private lemma pv_mul_neg_of_pos_factor {ε P c : ℝ} (hP : 0 < P) (h : ε * (P * c) < 0) :
    ε * c < 0 := by
  rw [mul_left_comm] at h
  exact Right.neg_of_mul_neg_right h hP.le

/-- Cancelling a positive middle factor inside a `pvSgn`-scaled product,
`0 <` version. -/
private lemma pv_mul_pos_of_pos_factor {ε P c : ℝ} (hP : 0 < P) (h : 0 < ε * (P * c)) :
    0 < ε * c := by
  rw [mul_left_comm] at h
  exact pos_of_mul_pos_right h hP.le

/-- The cup/cap shape condition on a left-to-right chain, in uniform
`pvSgn`-scaled form: every increasing triple has interior-side signed
area. -/
private def pvShaped {k : ℕ} (x : Fin (k + 1) → Euc 2) (σ : Bool) : Prop :=
  ∀ a b c : Fin (k + 1), a < b → b < c → pvSgn σ * pvCross (x a) (x b) (x c) < 0

private lemma pvShaped_of_capOrCup {k : ℕ} {x : Fin (k + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (x i) 0) {σ : Bool}
    (h : if σ then IsCap (Finset.image x Finset.univ)
         else IsCup (Finset.image x Finset.univ)) : pvShaped x σ := by
  intro a b c hab hbc
  have mem : ∀ t : Fin (k + 1), x t ∈ Finset.image x Finset.univ :=
    fun t ↦ Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩
  cases σ
  · -- `σ = false` (cup)
    have h' : IsCup (Finset.image x Finset.univ) := h
    have hc := pvCross_pos_of_isCup h' (mem a) (mem b) (mem c) (hmono hab)
      (hmono hbc)
    rw [show pvSgn false = (-1 : ℝ) from rfl]
    linarith
  · -- `σ = true` (cap)
    have h' : IsCap (Finset.image x Finset.univ) := h
    have hc := pvCross_neg_of_isCap h' (mem a) (mem b) (mem c) (hmono hab)
      (hmono hbc)
    rw [show pvSgn true = (1 : ℝ) from rfl]
    linarith

/-- In a `pvShaped` chain the `pvSgn`-scaled edge slopes strictly decrease
with the edge index (concavity of cap / convexity of cup slopes). -/
private lemma pvSl_edge {k : ℕ} {x : Fin (k + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (x i) 0) {σ : Bool} (hshape : pvShaped x σ)
    {a b : ℕ} (hab : a < b) (hb : b + 1 ≤ k) :
    pvSgn σ * pvSl (x ⟨b, by omega⟩) (x ⟨b + 1, by omega⟩) <
      pvSgn σ * pvSl (x ⟨a, by omega⟩) (x ⟨a + 1, by omega⟩) := by
  set u := x ⟨a, by omega⟩ with hu
  set u' := x ⟨a + 1, by omega⟩ with hu'
  set z := x ⟨b, by omega⟩ with hz
  set w := x ⟨b + 1, by omega⟩ with hw
  have muu' : (u : Euc 2) 0 < (u' : Euc 2) 0 := hmono (Fin.mk_lt_mk.mpr (by omega))
  have muw : (u : Euc 2) 0 < (w : Euc 2) 0 := hmono (Fin.mk_lt_mk.mpr (by omega))
  have mzw : (z : Euc 2) 0 < (w : Euc 2) 0 := hmono (Fin.mk_lt_mk.mpr (by omega))
  have h1 : pvSgn σ * pvCross u u' w < 0 :=
    hshape ⟨a, by omega⟩ ⟨a + 1, by omega⟩ ⟨b + 1, by omega⟩
      (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
  have key1 : pvSgn σ * (pvSl u w - pvSl u u') < 0 := by
    rw [pvCross_eq_mid muu' muw] at h1
    exact pv_mul_neg_of_pos_factor (mul_pos (sub_pos.mpr muu') (sub_pos.mpr muw)) h1
  have h2 : pvSgn σ * pvCross u z w < 0 :=
    hshape ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨b + 1, by omega⟩
      (Fin.mk_lt_mk.mpr hab) (Fin.mk_lt_mk.mpr (by omega))
  have key2 : pvSgn σ * (pvSl z w - pvSl u w) < 0 := by
    rw [pvCross_eq_left mzw muw] at h2
    exact pv_mul_neg_of_pos_factor (mul_pos (sub_pos.mpr mzw) (sub_pos.mpr muw)) h2
  linarith

/-- The first defining half-plane of a support region: `p` is strictly on
the interior side of its own edge line. -/
private lemma mem_supportOf_inner {k : ℕ} {x : Fin (k + 1) → Euc 2} {σ : Bool}
    {j : Fin k} {p : Euc 2} (hp : p ∈ supportOf x σ j) :
    0 < pvSgn σ * pvCross (x ⟨j.val, by omega⟩) (x ⟨j.val + 1, by omega⟩) p :=
  (mem_supportOf_iff.mp hp).1

/-- The second defining half-plane, specialized to `j ≥ 1`: `p` is on the
interior side of the previous edge line `x_{j-1} xⱼ`. -/
private lemma mem_supportOf_left {k : ℕ} {x : Fin (k + 1) → Euc 2} {σ : Bool}
    {j : Fin k} {p : Euc 2} (hp : p ∈ supportOf x σ j) (hj : 1 ≤ j.val) :
    pvSgn σ * pvCross (x ⟨j.val - 1, by omega⟩) (x ⟨j.val, by omega⟩) p < 0 := by
  have h := (mem_supportOf_iff.mp hp).2.1
  have e : (⟨(j.val + k) % (k + 1), Nat.mod_lt _ (by omega)⟩ : Fin (k + 1)) =
      ⟨j.val - 1, by omega⟩ :=
    Fin.ext_iff.mpr (show (j.val + k) % (k + 1) = j.val - 1 by
      rw [show j.val + k = j.val - 1 + (k + 1) by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt (by omega)])
  rw [e] at h
  exact h

/-- The third defining half-plane, specialized to `j + 2 ≤ k`: `p` is on the
interior side of the next edge line `x_{j+1} x_{j+2}`. -/
private lemma mem_supportOf_right {k : ℕ} {x : Fin (k + 1) → Euc 2} {σ : Bool}
    {j : Fin k} {p : Euc 2} (hp : p ∈ supportOf x σ j) (hj : j.val + 2 ≤ k) :
    pvSgn σ * pvCross (x ⟨j.val + 1, by omega⟩) (x ⟨j.val + 2, by omega⟩) p < 0 := by
  have h := (mem_supportOf_iff.mp hp).2.2
  have e : (⟨(j.val + 2) % (k + 1), Nat.mod_lt _ (by omega)⟩ : Fin (k + 1)) =
      ⟨j.val + 2, by omega⟩ := Fin.ext_iff.mpr (Nat.mod_eq_of_lt (by omega))
  rw [e] at h
  exact h

/-- **Key geometric lemma**: in a shaped left-to-right chain, the support
region `Tⱼ` lies strictly on the interior side of every *other* edge line
`xᵢxᵢ₊₁`.

For `i < j` the argument is: `p ∈ Tⱼ` lies below (in `ε`-sense) the previous
edge line `x_{j-1}xⱼ` and above the own edge line `xⱼxⱼ₊₁`; since
`ε·(s_{j-1} - sⱼ) > 0` the two lines meet strictly left of `p`, i.e.
`xⱼ₀ < p₀`.  The line `xᵢxᵢ₊₁` passes above `xⱼ` and has larger scaled slope
than `x_{j-1}xⱼ`, so it dominates `x_{j-1}xⱼ`'s height on all of
`[xⱼ₀, p₀]` — in particular it is above `p`.  The case `i > j` is the mirror
image. -/
private theorem pv_region_inner_side {k : ℕ} {x : Fin (k + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (x i) 0) {σ : Bool} (hshape : pvShaped x σ)
    {i j : Fin k} (hij : i ≠ j) {p : Euc 2} (hp : p ∈ supportOf x σ j) :
    pvSgn σ * pvCross (x ⟨i.val, by omega⟩) (x ⟨i.val + 1, by omega⟩) p < 0 := by
  have hA : 0 < pvSgn σ * pvCross (x ⟨j.val, by omega⟩) (x ⟨j.val + 1, by omega⟩) p :=
    (mem_supportOf_iff.mp hp).1
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · -- `i < j`: the previous edge `x_{j-1} xⱼ` bounds `Tⱼ` from below
    have hB : pvSgn σ * pvCross (x ⟨j.val - 1, by omega⟩) (x ⟨j.val, by omega⟩) p < 0 :=
      mem_supportOf_left hp (by omega)
    by_cases hjj : i.val + 1 = j.val
    · -- the previous edge IS the `i`-th edge
      have e1 : (⟨i.val, by omega⟩ : Fin (k + 1)) = ⟨j.val - 1, by omega⟩ :=
        Fin.ext_iff.mpr (show i.val = j.val - 1 by omega)
      have e2 : (⟨i.val + 1, by omega⟩ : Fin (k + 1)) = ⟨j.val, by omega⟩ :=
        Fin.ext_iff.mpr (show i.val + 1 = j.val by omega)
      rw [e1, e2]
      exact hB
    · -- `i + 1 < j`: apex bound then height domination
      set u := x ⟨i.val, by omega⟩ with hu
      set u' := x ⟨i.val + 1, by omega⟩ with hu'
      set z := x ⟨j.val - 1, by omega⟩ with hz
      set w := x ⟨j.val, by omega⟩ with hw
      set w' := x ⟨j.val + 1, by omega⟩ with hw'
      have hzw : (z : Euc 2) 0 < (w : Euc 2) 0 := hmono (Fin.mk_lt_mk.mpr (by omega))
      have hww' : (w : Euc 2) 0 < (w' : Euc 2) 0 := hmono (Fin.mk_lt_mk.mpr (by omega))
      have huu' : (u : Euc 2) 0 < (u' : Euc 2) 0 := hmono (Fin.mk_lt_mk.mpr (by omega))
      have hB1 : pvSgn σ * (p 1 - pvHgt z w (p 0)) < 0 := by
        rw [pvCross_eq_hgt (ne_of_gt hzw)] at hB
        exact pv_mul_neg_of_pos_factor (sub_pos.mpr hzw) hB
      have hA1 : 0 < pvSgn σ * (p 1 - pvHgt w w' (p 0)) := by
        rw [pvCross_eq_hgt (ne_of_gt hww')] at hA
        exact pv_mul_pos_of_pos_factor (sub_pos.mpr hww') hA
      -- wedge bound: `p` is strictly to the right of the apex `w`
      have hpx : (w : Euc 2) 0 < p 0 := by
        have hB1w : pvSgn σ * (p 1 - (w 1 + pvSl z w * (p 0 - w 0))) < 0 := by
          have h := hB1
          rw [pvHgt_at_right (ne_of_gt hzw)] at h
          exact h
        have hA1w : 0 < pvSgn σ * (p 1 - (w 1 + pvSl w w' * (p 0 - w 0))) := hA1
        have hsl : 0 < pvSgn σ * (pvSl z w - pvSl w w') := by
          have h' := pvSl_edge hmono hshape (show j.val - 1 < j.val by omega)
            (show j.val + 1 ≤ k by omega)
          have e : (⟨j.val - 1 + 1, by omega⟩ : Fin (k + 1)) = ⟨j.val, by omega⟩ :=
            Fin.ext_iff.mpr (show j.val - 1 + 1 = j.val by omega)
          rw [e] at h'
          have h : pvSgn σ * pvSl w w' < pvSgn σ * pvSl z w := h'
          linarith
        have hd : 0 < pvSgn σ * (pvSl z w - pvSl w w') * (p 0 - w 0) := by
          have e : pvSgn σ * (pvSl z w - pvSl w w') * (p 0 - w 0) =
              pvSgn σ * (p 1 - (w 1 + pvSl w w' * (p 0 - w 0))) -
              pvSgn σ * (p 1 - (w 1 + pvSl z w * (p 0 - w 0))) := by ring
          rw [e]
          linarith
        exact sub_pos.mp (pos_of_mul_pos_right hd hsl.le)
      -- domination: the line `u u'` stays strictly above `z w`'s height on
      -- `[w₀, p₀]`
      have hdom : 0 < pvSgn σ * (pvHgt u u' (p 0) - pvHgt z w (p 0)) := by
        rw [pvHgt_affine u u' (p 0) (w 0), pvHgt_at_right (ne_of_gt hzw)]
        have hbase : 0 < pvSgn σ * (pvHgt u u' (w 0) - w 1) := by
          have hc : pvSgn σ * pvCross u u' w < 0 :=
            hshape ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩ ⟨j.val, by omega⟩
              (Fin.mk_lt_mk.mpr (by omega)) (Fin.mk_lt_mk.mpr (by omega))
          rw [pvCross_eq_hgt (ne_of_gt huu')] at hc
          have hlt' := pv_mul_neg_of_pos_factor (sub_pos.mpr huu') hc
          linarith
        have hslope : 0 < pvSgn σ * (pvSl u u' - pvSl z w) := by
          have h' := pvSl_edge hmono hshape (show i.val < j.val - 1 by omega)
            (show j.val - 1 + 1 ≤ k by omega)
          have e : (⟨j.val - 1 + 1, by omega⟩ : Fin (k + 1)) = ⟨j.val, by omega⟩ :=
            Fin.ext_iff.mpr (show j.val - 1 + 1 = j.val by omega)
          rw [e] at h'
          have h : pvSgn σ * pvSl z w < pvSgn σ * pvSl u u' := h'
          linarith
        have hprod : 0 ≤ pvSgn σ * (pvSl u u' - pvSl z w) * (p 0 - w 0) :=
          mul_nonneg hslope.le (sub_nonneg.mpr hpx.le)
        have e : pvSgn σ * (pvHgt u u' (w 0) + pvSl u u' * (p 0 - w 0) -
            (w 1 + pvSl z w * (p 0 - w 0))) =
            pvSgn σ * (pvHgt u u' (w 0) - w 1) +
              pvSgn σ * (pvSl u u' - pvSl z w) * (p 0 - w 0) := by ring
        rw [e]
        linarith
      -- assemble: `ε·(p₁ - hᵢ(p₀)) < 0`, then unscale
      have key : pvSgn σ * (p 1 - pvHgt u u' (p 0)) < 0 := by
        have e : pvSgn σ * (p 1 - pvHgt u u' (p 0)) =
            pvSgn σ * (p 1 - pvHgt z w (p 0)) -
              pvSgn σ * (pvHgt u u' (p 0) - pvHgt z w (p 0)) := by ring
        rw [e]
        linarith
      rw [pvCross_eq_hgt (ne_of_gt huu')]
      have e : pvSgn σ * ((u' 0 - u 0) * (p 1 - pvHgt u u' (p 0))) =
          (u' 0 - u 0) * (pvSgn σ * (p 1 - pvHgt u u' (p 0))) := by ring
      rw [e]
      exact mul_neg_of_pos_of_neg (sub_pos.mpr huu') key
  · -- `i = j` is excluded
    exact absurd (Fin.ext_iff.mpr heq) hij
  · -- `i > j`: the next edge `x_{j+1} x_{j+2}` bounds `Tⱼ` from below
    have hC : pvSgn σ * pvCross (x ⟨j.val + 1, by omega⟩) (x ⟨j.val + 2, by omega⟩) p < 0 :=
      mem_supportOf_right hp (by omega)
    by_cases hjj : i.val = j.val + 1
    · -- the next edge IS the `i`-th edge
      have e1 : (⟨i.val, by omega⟩ : Fin (k + 1)) = ⟨j.val + 1, by omega⟩ :=
        Fin.ext_iff.mpr (show i.val = j.val + 1 by omega)
      have e2 : (⟨i.val + 1, by omega⟩ : Fin (k + 1)) = ⟨j.val + 2, by omega⟩ :=
        Fin.ext_iff.mpr (show i.val + 1 = j.val + 2 by omega)
      rw [e1, e2]
      exact hC
    · -- `i ≥ j + 2`: apex bound then height domination
      set u := x ⟨i.val, by omega⟩ with hu
      set u' := x ⟨i.val + 1, by omega⟩ with hu'
      set w := x ⟨j.val, by omega⟩ with hw
      set w' := x ⟨j.val + 1, by omega⟩ with hw'
      set w'' := x ⟨j.val + 2, by omega⟩ with hw''
      have huu' : (u : Euc 2) 0 < (u' : Euc 2) 0 := hmono (Fin.mk_lt_mk.mpr (by omega))
      have hww' : (w : Euc 2) 0 < (w' : Euc 2) 0 := hmono (Fin.mk_lt_mk.mpr (by omega))
      have hw'w'' : (w' : Euc 2) 0 < (w'' : Euc 2) 0 := hmono (Fin.mk_lt_mk.mpr (by omega))
      have hA1 : 0 < pvSgn σ * (p 1 - pvHgt w w' (p 0)) := by
        rw [pvCross_eq_hgt (ne_of_gt hww')] at hA
        exact pv_mul_pos_of_pos_factor (sub_pos.mpr hww') hA
      have hC1 : pvSgn σ * (p 1 - pvHgt w' w'' (p 0)) < 0 := by
        rw [pvCross_eq_hgt (ne_of_gt hw'w'')] at hC
        exact pv_mul_neg_of_pos_factor (sub_pos.mpr hw'w'') hC
      -- wedge bound: `p` is strictly to the left of the apex `w'`
      have hpx : p 0 < (w' : Euc 2) 0 := by
        have hA1w : 0 < pvSgn σ * (p 1 - (w' 1 + pvSl w w' * (p 0 - w' 0))) := by
          have h := hA1
          rw [pvHgt_at_right (ne_of_gt hww')] at h
          exact h
        have hC1w : pvSgn σ * (p 1 - (w' 1 + pvSl w' w'' * (p 0 - w' 0))) < 0 := hC1
        have hsl : 0 < pvSgn σ * (pvSl w w' - pvSl w' w'') := by
          have h : pvSgn σ * pvSl w' w'' < pvSgn σ * pvSl w w' :=
            pvSl_edge hmono hshape (show j.val < j.val + 1 by omega)
              (show j.val + 1 + 1 ≤ k by omega)
          linarith
        have hd : pvSgn σ * (pvSl w w' - pvSl w' w'') * (p 0 - w' 0) < 0 := by
          have e : pvSgn σ * (pvSl w w' - pvSl w' w'') * (p 0 - w' 0) =
              pvSgn σ * (p 1 - (w' 1 + pvSl w' w'' * (p 0 - w' 0))) -
              pvSgn σ * (p 1 - (w' 1 + pvSl w w' * (p 0 - w' 0))) := by ring
          rw [e]
          linarith
        exact sub_neg.mp (Right.neg_of_mul_neg_right hd hsl.le)
      -- domination: the line `u u'` stays strictly above `w' w''`'s height on
      -- `[p₀, w'₀]`
      have hdom : 0 < pvSgn σ * (pvHgt u u' (p 0) - pvHgt w' w'' (p 0)) := by
        rw [pvHgt_affine u u' (p 0) (w' 0),
          show pvHgt w' w'' (p 0) = w' 1 + pvSl w' w'' * (p 0 - w' 0) from rfl]
        have hbase : 0 < pvSgn σ * (pvHgt u u' (w' 0) - w' 1) := by
          have hc : pvSgn σ * pvCross u u' w' < 0 := by
            have h := hshape ⟨j.val + 1, by omega⟩ ⟨i.val, by omega⟩
              ⟨i.val + 1, by omega⟩ (Fin.mk_lt_mk.mpr (by omega))
              (Fin.mk_lt_mk.mpr (by omega))
            rwa [pvCross_cyc] at h
          rw [pvCross_eq_hgt (ne_of_gt huu')] at hc
          have hlt' := pv_mul_neg_of_pos_factor (sub_pos.mpr huu') hc
          linarith
        have hslope : pvSgn σ * (pvSl u u' - pvSl w' w'') < 0 := by
          have h : pvSgn σ * pvSl u u' < pvSgn σ * pvSl w' w'' :=
            pvSl_edge hmono hshape (show j.val + 1 < i.val by omega)
              (show i.val + 1 ≤ k by omega)
          linarith
        have hprod : 0 ≤ pvSgn σ * (pvSl u u' - pvSl w' w'') * (p 0 - w' 0) :=
          mul_nonneg_of_nonpos_of_nonpos hslope.le (sub_nonpos.mpr hpx.le)
        have e : pvSgn σ * (pvHgt u u' (w' 0) + pvSl u u' * (p 0 - w' 0) -
            (w' 1 + pvSl w' w'' * (p 0 - w' 0))) =
            pvSgn σ * (pvHgt u u' (w' 0) - w' 1) +
              pvSgn σ * (pvSl u u' - pvSl w' w'') * (p 0 - w' 0) := by ring
        rw [e]
        linarith
      have key : pvSgn σ * (p 1 - pvHgt u u' (p 0)) < 0 := by
        have e : pvSgn σ * (p 1 - pvHgt u u' (p 0)) =
            pvSgn σ * (p 1 - pvHgt w' w'' (p 0)) -
              pvSgn σ * (pvHgt u u' (p 0) - pvHgt w' w'' (p 0)) := by ring
        rw [e]
        linarith
      rw [pvCross_eq_hgt (ne_of_gt huu')]
      have e : pvSgn σ * ((u' 0 - u 0) * (p 1 - pvHgt u u' (p 0))) =
          (u' 0 - u 0) * (pvSgn σ * (p 1 - pvHgt u u' (p 0))) := by ring
      rw [e]
      exact mul_neg_of_pos_of_neg (sub_pos.mpr huu') key

/-- Support regions of distinct edges are disjoint: a point of `T_j` lies
strictly on the interior side of the `i`-th edge line for `i ≠ j`, while
points of `T_i` lie strictly on the other side. -/
private lemma supportOf_disjoint {k : ℕ} {x : Fin (k + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (x i) 0) {σ : Bool} (hshape : pvShaped x σ)
    {i j : Fin k} (hij : i ≠ j) :
    Disjoint (supportOf x σ i) (supportOf x σ j) := by
  rw [Set.disjoint_left]
  intro p hpi hpj
  have h1 := mem_supportOf_inner hpi
  have h2 := pv_region_inner_side hmono hshape hij hpj
  linarith

/-- The linear functional on `ℝ³` whose level `edgeFuncC` is the vertical
plane over the edge line `uv` in `ℝ²` (scaled by `pvSgn σ`). -/
private def edgeFunc (σ : Bool) (u v : Euc 2) : Euc 3 →ₗ[ℝ] ℝ where
  toFun z := pvSgn σ * ((v 0 - u 0) * z 1 - (v 1 - u 1) * z 0)
  map_add' x y := by
    simp only [PiLp.add_apply]; ring
  map_smul' c x := by
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- The value of `edgeFunc` at any point of the edge line `uv`. -/
private def edgeFuncC (σ : Bool) (u v : Euc 2) : ℝ :=
  pvSgn σ * ((v 0 - u 0) * u 1 - (v 1 - u 1) * u 0)

private lemma sgn_pvCross_proj2 (σ : Bool) (u v : Euc 2) (z : Euc 3) :
    pvSgn σ * pvCross u v (proj2 z) =
      edgeFunc σ u v z - edgeFuncC σ u v := by
  simp only [pvCross, edgeFunc, edgeFuncC, LinearMap.coe_mk, AddHom.coe_mk]
  have e0 : (proj2 z) 0 = z 0 := rfl
  have e1 : (proj2 z) 1 = z 1 := rfl
  rw [e0, e1]; ring

/-- Fibers over the support regions of a shaped chain form a collection in
convex position: the vertical plane over the `i`-th edge line strictly
separates the `i`-th fiber from all the others. -/
private lemma collectionConvex_of_regions {k : ℕ} {x : Fin (k + 1) → Euc 2}
    (hmono : StrictMono fun i ↦ (x i) 0) {σ : Bool} (hshape : pvShaped x σ)
    {B : Fin k → Finset (Euc 3)}
    (hB : ∀ i : Fin k, ∀ z ∈ B i, proj2 z ∈ supportOf x σ i) :
    CollectionConvex B := by
  intro i
  set u : Euc 2 := x ⟨i.val, by omega⟩ with hu
  set v : Euc 2 := x ⟨i.val + 1, by omega⟩ with hv
  set L : Euc 3 →ₗ[ℝ] ℝ := edgeFunc σ u v with hL
  set c : ℝ := edgeFuncC σ u v with hc
  have hpos : ∀ z ∈ (B i : Set (Euc 3)), c < L z := by
    intro z hz
    have h := mem_supportOf_inner (hB i z (Finset.mem_coe.1 hz))
    rw [sgn_pvCross_proj2] at h
    simp only [hL, hc] at h ⊢
    linarith
  have hneg : ∀ z ∈ ⋃ j : Fin k, ⋃ _ : j ≠ i, (B j : Set (Euc 3)), L z < c := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨j, hji, hz⟩ := hz
    have h := pv_region_inner_side hmono hshape hji.symm (hB j z (Finset.mem_coe.1 hz))
    rw [sgn_pvCross_proj2] at h
    simp only [hL, hc] at h ⊢
    linarith
  have hcvx1 : Convex ℝ {z : Euc 3 | c < L z} :=
    (convex_Ioi c).linear_preimage L
  have hcvx2 : Convex ℝ {z : Euc 3 | L z < c} :=
    (convex_Iio c).linear_preimage L
  have hd : Disjoint ({z : Euc 3 | c < L z}) ({z : Euc 3 | L z < c}) := by
    rw [Set.disjoint_left]
    intro z h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    linarith
  exact Set.disjoint_of_subset (convexHull_min hpos hcvx1)
    (convexHull_min hneg hcvx2) hd


/-! ### Lifting planar maps to `ℝ³` -/

/-- Lift of a planar linear map `f : ℝ³ → ℝ²` to a linear self-map of `ℝ³`
preserving the last coordinate; satisfies `proj2 ∘ liftPlanar f = f`. -/
private def liftPlanar (f : Euc 3 →ₗ[ℝ] Euc 2) : Euc 3 →ₗ[ℝ] Euc 3 where
  toFun x := WithLp.toLp 2 ![f x 0, f x 1, x 2]
  map_add' x y := by
    apply PiLp.ext; intro i; fin_cases i <;> simp [PiLp.add_apply]
  map_smul' c x := by
    apply PiLp.ext; intro i; fin_cases i <;>
      simp [PiLp.smul_apply, smul_eq_mul]

private lemma liftPlanar_apply_two (f : Euc 3 →ₗ[ℝ] Euc 2) (x : Euc 3) :
    (liftPlanar f x) 2 = x 2 := rfl

private lemma proj2_liftPlanar (f : Euc 3 →ₗ[ℝ] Euc 2) (x : Euc 3) :
    proj2 (liftPlanar f x) = f x := by
  apply PiLp.ext; intro j; fin_cases j <;> rfl

private lemma liftPlanar_injective {f : Euc 3 →ₗ[ℝ] Euc 2}
    (hf : ∀ z : Euc 3, f z = 0 → z 2 = 0 → z = 0) :
    Function.Injective (liftPlanar f) := by
  intro x y hxy
  have h0 : f x 0 = f y 0 := congrArg (fun p ↦ p 0) hxy
  have h1 : f x 1 = f y 1 := congrArg (fun p ↦ p 1) hxy
  have h2 : x 2 = y 2 := congrArg (fun p ↦ p 2) hxy
  have hfx : f x = f y := by
    apply PiLp.ext; intro j; fin_cases j <;> assumption
  have hz : f (x - y) = 0 := by rw [map_sub, hfx, sub_self]
  have hz2 : (x - y) 2 = 0 := by simp [PiLp.sub_apply, h2]
  exact sub_eq_zero.1 (hf _ hz hz2)

/-- General position is preserved by an injective linear map. -/
private lemma inGeneralPosition_image_linear {X : Finset (Euc 3)}
    (hX : InGeneralPosition (X : Set (Euc 3))) (hXcard : 4 ≤ X.card)
    {T : Euc 3 →ₗ[ℝ] Euc 3} (hT : Function.Injective T) :
    InGeneralPosition ((X.image T : Finset (Euc 3)) : Set (Euc 3)) := by
  intro s' hs' hcard'
  set s : Finset (Euc 3) := X.filter (fun x ↦ T x ∈ s') with hsdef
  have hsX : s ⊆ X := Finset.filter_subset _ X
  have hsimage : s.image T = s' := by
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hxs, rfl⟩
      exact (Finset.mem_filter.1 hxs).2
    · intro hz
      have hzX : z ∈ X.image T := hs' (Finset.mem_coe.2 hz)
      rw [Finset.mem_image] at hzX
      obtain ⟨x, hxX, rfl⟩ := hzX
      exact ⟨x, Finset.mem_filter.2 ⟨hxX, hz⟩, rfl⟩
  have hscard : s.card = 4 := by
    have hc := Finset.card_image_of_injOn
      (hT.injOn.mono (Finset.coe_subset.2 hsX))
    rw [hsimage, hcard'] at hc
    exact hc.symm
  have hsi : AffineIndependent ℝ (fun x : ↥s ↦ (x : Euc 3)) :=
    affineIndependent_of_inGeneralPosition hX hXcard hsX (by omega)
  have hmap : AffineIndependent ℝ
      (T.toAffineMap ∘ fun x : ↥s ↦ (x : Euc 3)) :=
    AffineIndependent.map' hsi _
      (by rw [LinearMap.coe_toAffineMap]; exact hT)
  rw [LinearMap.coe_toAffineMap] at hmap
  have hbij : Function.Bijective
      (fun x : ↥s ↦ (⟨T x, by
        rw [← hsimage]; exact Finset.mem_image.2 ⟨x, x.2, rfl⟩⟩ : ↥s')) := by
    constructor
    · intro x y hxy
      have : T x = T y := congrArg Subtype.val hxy
      exact Subtype.ext (hT this)
    · intro y
      have : (y : Euc 3) ∈ s.image T := by rw [hsimage]; exact y.2
      rw [Finset.mem_image] at this
      obtain ⟨x, hx, hxe⟩ := this
      exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
  let e : ↥s ≃ ↥s' := Equiv.ofBijective _ hbij
  have hcomp : (fun y : ↥s' ↦ (y : Euc 3)) ∘ e =
      T ∘ fun x : ↥s ↦ (x : Euc 3) := rfl
  rw [← affineIndependent_equiv e]
  rw [hcomp]
  exact hmap

/-- Convex position pulls back along an injective linear map. -/
private lemma inConvexPosition_preimage_linear {X S' : Finset (Euc 3)}
    {T : Euc 3 →ₗ[ℝ] Euc 3} (hT : Function.Injective T)
    (hsub : S' ⊆ X.image T)
    (hconv : InConvexPosition S') :
    InConvexPosition (X.filter (fun x ↦ T x ∈ S')) := by
  classical
  intro x hxS hc
  have hxS' : T x ∈ S' := (Finset.mem_filter.1 hxS).2
  have h1 : T x ∈
      T '' convexHull ℝ ((X.filter (fun y ↦ T y ∈ S')).erase x : Set (Euc 3)) :=
    ⟨x, hc, rfl⟩
  rw [LinearMap.image_convexHull] at h1
  have h2 : T '' ((X.filter (fun y ↦ T y ∈ S')).erase x : Set (Euc 3)) =
      ((S'.erase (T x) : Finset _) : Set (Euc 3)) := by
    ext z
    simp only [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
      Set.mem_image, Finset.mem_coe]
    constructor
    · rintro ⟨y, ⟨hyS, hyx⟩, rfl⟩
      refine ⟨(Finset.mem_filter.1 hyS).2, ?_⟩
      intro hzyx
      apply hyx
      exact hT hzyx
    · intro hz
      rcases hz with ⟨hzS', hzne⟩
      have hzX : z ∈ X.image T := hsub hzS'
      rw [Finset.mem_image] at hzX
      obtain ⟨y, hyX, rfl⟩ := hzX
      have hyS : y ∈ X.filter (fun w ↦ T w ∈ S') :=
        Finset.mem_filter.2 ⟨hyX, hzS'⟩
      have hyx : y ≠ x := fun h ↦ hzne (congrArg _ h)
      exact ⟨y, ⟨hyS, hyx⟩, rfl⟩
  rw [h2] at h1
  exact hconv _ hxS' h1

/-- A direction `a` generic for `X`: nonzero last coordinate, avoiding every
secant line direction and every `3`-point vector span of `X`. -/
private lemma exists_direction {X : Finset (Euc 3)} (hXne : X.Nonempty) :
    ∃ a : Euc 3, a ≠ 0 ∧ a (Fin.last 2) ≠ 0 ∧
      (∀ x ∈ X, ∀ y ∈ X, a ∉ ℝ ∙ (x - y)) ∧
      (∀ s : Finset (Euc 3), s ⊆ X → s.card = 3 →
        a ∉ vectorSpan ℝ (s : Set (Euc 3))) := by
  classical
  set F : Finset (Submodule ℝ (Euc 3)) :=
    ((X ×ˢ X).image fun p : Euc 3 × Euc 3 ↦ ℝ ∙ (p.1 - p.2)) ∪
    ((X.powersetCard 3).image fun s : Finset (Euc 3) ↦
      vectorSpan ℝ (s : Set (Euc 3))) ∪
    {LinearMap.ker (EuclideanSpace.projₗ (Fin.last 2) : Euc 3 →ₗ[ℝ] ℝ)}
    with hFdef
  have hF : ∀ U ∈ F, U ≠ ⊤ := by
    intro U hU
    rw [hFdef] at hU
    rcases Finset.mem_union.1 hU with hAB | hC
    · rcases Finset.mem_union.1 hAB with hA | hB
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hA
        intro htop
        have hle : Module.finrank ℝ (ℝ ∙ (p.1 - p.2) : Submodule ℝ (Euc 3)) ≤ 1 := by
          simpa using finrank_span_le_card ({p.1 - p.2} : Set (Euc 3))
        rw [htop, finrank_top, finrank_euclideanSpace_fin] at hle
        omega
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hB
        rw [Finset.mem_powersetCard] at hs
        intro htop
        have hcard : Fintype.card (↥s : Type _) = 3 := by
          rw [Fintype.card_coe]; exact hs.2
        have hrange : Set.range (fun x : ↥s ↦ (x : Euc 3)) = (s : Set _) := by
          ext z
          constructor
          · rintro ⟨⟨w, hw⟩, rfl⟩
            exact Finset.mem_coe.2 hw
          · intro hz
            exact ⟨⟨z, Finset.mem_coe.1 hz⟩, rfl⟩
        have hle := finrank_vectorSpan_range_le ℝ
          (fun x : ↥s ↦ (x : Euc 3)) hcard
        rw [hrange] at hle
        rw [htop, finrank_top, finrank_euclideanSpace_fin] at hle
        omega
    · rw [Finset.mem_singleton] at hC
      subst hC
      intro htop
      have h1 : EuclideanSpace.projₗ (Fin.last 2)
          (EuclideanSpace.single (Fin.last 2) (1 : ℝ) : Euc 3) = 0 := by
        rw [← LinearMap.mem_ker, htop]
        exact Submodule.mem_top
      have h2 : EuclideanSpace.projₗ (Fin.last 2)
          (EuclideanSpace.single (Fin.last 2) (1 : ℝ) : Euc 3) = 1 := by
        simp only [PiLp.projₗ_apply, PiLp.single_eq_same]
      rw [h2] at h1
      exact one_ne_zero h1
  obtain ⟨a, ha⟩ := exists_avoid_submodules F hF
  obtain ⟨x₀, hx₀⟩ := hXne
  have ha0 : a ≠ 0 := by
    intro h0
    have hmem : ℝ ∙ (x₀ - x₀) ∈ F := by
      rw [hFdef]
      refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
      exact Finset.mem_image.2 ⟨⟨x₀, x₀⟩, Finset.mem_product.2 ⟨hx₀, hx₀⟩, rfl⟩
    have hz : a ∈ ℝ ∙ (x₀ - x₀) := by
      rw [h0]; exact Submodule.zero_mem _
    exact ha _ hmem hz
  have halast : a (Fin.last 2) ≠ 0 := by
    intro h0
    have hmem : LinearMap.ker (EuclideanSpace.projₗ (Fin.last 2) :
        Euc 3 →ₗ[ℝ] ℝ) ∈ F := by
      rw [hFdef]
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have hz : a ∈ LinearMap.ker (EuclideanSpace.projₗ (Fin.last 2) :
        Euc 3 →ₗ[ℝ] ℝ) := by
      rw [LinearMap.mem_ker]
      simpa using h0
    exact ha _ hmem hz
  refine ⟨a, ha0, halast, ?_, ?_⟩
  · intro x hx y hy
    have hmem : ℝ ∙ (x - y) ∈ F := by
      rw [hFdef]
      refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
      exact Finset.mem_image.2 ⟨⟨x, y⟩, Finset.mem_product.2 ⟨hx, hy⟩, rfl⟩
    exact ha _ hmem
  · intro s hs hcard
    have hmem : vectorSpan ℝ (s : Set (Euc 3)) ∈ F := by
      rw [hFdef]
      refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      exact Finset.mem_image.2 ⟨s, Finset.mem_powersetCard.2 ⟨hs, hcard⟩, rfl⟩
    exact ha _ hmem


/-- `projAlong a` is injective on `X` when `a` avoids all secant directions
and has nonzero last coordinate. -/
private lemma injOn_projAlong {X : Finset (Euc 3)} {a : Euc 3}
    (halast : a (Fin.last 2) ≠ 0)
    (hline : ∀ x ∈ X, ∀ y ∈ X, a ∉ ℝ ∙ (x - y)) :
    Set.InjOn (projAlong a) (X : Set (Euc 3)) := by
  intro x hx y hy hxy
  have hker : x - y ∈ LinearMap.ker (projAlong a) := by
    rw [LinearMap.mem_ker, LinearMap.map_sub, hxy, sub_self]
  rw [projAlong_ker a halast, Submodule.mem_span_singleton] at hker
  obtain ⟨t, ht⟩ := hker
  by_contra hne
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at ht
    exact hne (sub_eq_zero.1 ht.symm)
  have hamem : a ∈ ℝ ∙ (x - y) := by
    rw [Submodule.mem_span_singleton]
    refine ⟨t⁻¹, ?_⟩
    rw [← ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]
  exact hline x hx y hy hamem

/-- For a generic direction `a`, the projected set `projAlong a '' X ⊆ ℝ²`
is again in general position: any affine dependence would put `a` in the
vector span of the preimage triple. -/
private lemma inGeneralPosition_image_projAlong {X : Finset (Euc 3)}
    (hX : InGeneralPosition (X : Set (Euc 3))) (hXcard : 4 ≤ X.card)
    {a : Euc 3} (halast : a (Fin.last 2) ≠ 0)
    (hinj : Set.InjOn (projAlong a) (X : Set (Euc 3)))
    (hvec : ∀ s : Finset (Euc 3), s ⊆ X → s.card = 3 →
      a ∉ vectorSpan ℝ (s : Set (Euc 3))) :
    InGeneralPosition ((X.image (projAlong a) : Finset (Euc 2)) : Set (Euc 2)) := by
  intro s' hs' hcard'
  -- preimage finset s ⊆ X with proj '' s = s'.
  set s : Finset (Euc 3) := X.filter (fun x ↦ projAlong a x ∈ s') with hsdef
  have hsX : s ⊆ X := Finset.filter_subset _ X
  have hsimage : s.image (projAlong a) = s' := by
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hxs, rfl⟩
      exact (Finset.mem_filter.1 hxs).2
    · intro hz
      have hzX : z ∈ X.image (projAlong a) := hs' (Finset.mem_coe.2 hz)
      rw [Finset.mem_image] at hzX
      obtain ⟨x, hxX, rfl⟩ := hzX
      exact ⟨x, Finset.mem_filter.2 ⟨hxX, hz⟩, rfl⟩
  have hscard : s.card = 3 := by
    have hc := Finset.card_image_of_injOn
      (hinj.mono (Finset.coe_subset.2 hsX))
    rw [hsimage, hcard'] at hc
    exact hc.symm
  -- s is affinely independent (general position of X).
  have hsi : AffineIndependent ℝ (fun x : ↥s ↦ (x : Euc 3)) :=
    affineIndependent_of_inGeneralPosition hX hXcard hsX (by omega)
  have hsvs : Module.finrank ℝ (vectorSpan ℝ (s : Set (Euc 3))) = 2 := by
    have hcard : Fintype.card (↥s : Type _) = 2 + 1 := by
      rw [Fintype.card_coe]; exact hscard
    have hrange : Set.range (fun x : ↥s ↦ (x : Euc 3)) = (s : Set _) := by
      ext z
      constructor
      · rintro ⟨⟨w, hw⟩, rfl⟩
        exact Finset.mem_coe.2 hw
      · intro hz
        exact ⟨⟨z, Finset.mem_coe.1 hz⟩, rfl⟩
    rw [← hrange]
    exact (affineIndependent_iff_finrank_vectorSpan_eq ℝ _ hcard).1 hsi
  by_contra hdep
  -- dependent ⇒ vectorSpan s' proper ⇒ pick u ≠ 0 orthogonal to it.
  have hlt : Module.finrank ℝ (vectorSpan ℝ (s' : Set (Euc 2))) < 2 := by
    have hcard : Fintype.card (↥s' : Type _) = 2 + 1 := by
      rw [Fintype.card_coe]; exact hcard'
    have hrange : Set.range (fun x : ↥s' ↦ (x : Euc 2)) = (s' : Set _) := by
      ext z
      constructor
      · rintro ⟨⟨w, hw⟩, rfl⟩
        exact Finset.mem_coe.2 hw
      · intro hz
        exact ⟨⟨z, Finset.mem_coe.1 hz⟩, rfl⟩
    by_contra hnotlt
    have hge : 2 ≤ Module.finrank ℝ (vectorSpan ℝ (s' : Set (Euc 2))) :=
      le_of_not_gt hnotlt
    rw [← hrange] at hge
    exact hdep ((affineIndependent_iff_le_finrank_vectorSpan ℝ _ hcard).2 hge)
  have hV : vectorSpan ℝ (s' : Set (Euc 2)) ≠ ⊤ := by
    intro htop
    rw [htop, finrank_top, finrank_euclideanSpace_fin] at hlt
    omega
  have horth : (vectorSpan ℝ (s' : Set (Euc 2)))ᗮ ≠ ⊥ := by
    intro hbot
    exact hV (Submodule.orthogonal_eq_bot_iff.1 hbot)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot horth
  -- The functional L = ⟪u, ·⟫ ∘ proj vanishes on vectorSpan s and on a.
  set f : Euc 2 →ₗ[ℝ] ℝ := innerₛₗ ℝ u with hf
  have hfv : ∀ v ∈ vectorSpan ℝ (s' : Set (Euc 2)), f v = 0 := by
    intro v hv
    have h := (Submodule.mem_orthogonal' _ u).1 hu v hv
    rw [hf, innerₛₗ_apply_apply]
    exact h
  have hfu : f u ≠ 0 := by
    intro h0
    rw [hf, innerₛₗ_apply_apply] at h0
    exact hu0 (inner_self_eq_zero.1 h0)
  set L : Euc 3 →ₗ[ℝ] ℝ := f.comp (projAlong a) with hL
  have hL0 : L ≠ 0 := by
    intro h0
    obtain ⟨x, hx⟩ := projAlong_surjective a halast u
    have hLx : L x = 0 := by rw [h0]; simp
    rw [hL, LinearMap.comp_apply, hx] at hLx
    exact hfu hLx
  have hLa : L a = 0 := by
    rw [hL, LinearMap.comp_apply]
    have hpa : projAlong a a = 0 := by
      rw [← LinearMap.mem_ker, projAlong_ker a halast]
      exact Submodule.mem_span_singleton_self a
    rw [hpa]; exact f.map_zero
  have hLker : vectorSpan ℝ (s : Set (Euc 3)) ≤ LinearMap.ker L := by
    unfold vectorSpan
    rw [Submodule.span_le]
    intro w hw
    simp only [Set.mem_vsub] at hw
    obtain ⟨p, hp, q, hq, rfl⟩ := hw
    change L (p -ᵥ q) = 0
    have hp' : p ∈ s := Finset.mem_coe.1 hp
    have hq' : q ∈ s := Finset.mem_coe.1 hq
    have hproj : projAlong a p -ᵥ projAlong a q ∈
        vectorSpan ℝ (s' : Set (Euc 2)) :=
      vsub_mem_vectorSpan ℝ
        (Finset.mem_coe.2 (Finset.mem_filter.1 hp').2)
        (Finset.mem_coe.2 (Finset.mem_filter.1 hq').2)
    rw [vsub_eq_sub] at hproj
    simp only [hL, LinearMap.comp_apply]
    rw [vsub_eq_sub, map_sub]
    exact hfv _ hproj
  -- dimensions force ker L = vectorSpan s, which contains a — contradiction.
  have hkerfin : Module.finrank ℝ (LinearMap.ker L) = 2 := by
    obtain ⟨xL, hxL⟩ := DFunLike.ne_iff.1 hL0
    simp only [LinearMap.zero_apply] at hxL
    have hran : LinearMap.range L = ⊤ := by
      rw [eq_top_iff]
      intro y _
      rw [LinearMap.mem_range]
      refine ⟨(y / L xL) • xL, ?_⟩
      simp [map_smul, smul_eq_mul, div_mul_cancel₀ _ hxL]
    have hrfin : Module.finrank ℝ (LinearMap.range L) = 1 := by
      rw [hran, finrank_top, Module.finrank_self]
    have hfr := LinearMap.finrank_range_add_finrank_ker L
    rw [hrfin, finrank_euclideanSpace_fin] at hfr
    omega
  have heq : vectorSpan ℝ (s : Set (Euc 3)) = LinearMap.ker L :=
    Submodule.eq_of_le_of_finrank_eq hLker (hsvs.trans hkerfin.symm)
  have hamem : a ∈ vectorSpan ℝ (s : Set (Euc 3)) := by
    rw [heq, LinearMap.mem_ker]
    exact hLa
  exact hvec s hsX hscard hamem

/-- The full normalization: an injective linear `T : ℝ³ → ℝ³` whose
projection `proj2 ∘ T = shearX δ ∘ projAlong a` sends `X` to a
general-position set `Y ⊆ ℝ²` with pairwise distinct first coordinates,
with `proj2` injective on `T '' X`. -/
private lemma exists_normalization {X : Finset (Euc 3)}
    (hX : InGeneralPosition (X : Set (Euc 3))) (hXcard : 4 ≤ X.card) :
    ∃ T : Euc 3 →ₗ[ℝ] Euc 3, Function.Injective T ∧
      InGeneralPosition ((X.image T : Finset (Euc 3)) : Set (Euc 3)) ∧
      Set.InjOn proj2 ((X.image T : Finset (Euc 3)) : Set (Euc 3)) ∧
      ∃ Z : Finset (Euc 2), ∃ δ : ℝ,
        (X.image T).image proj2 = Z.image
          (JSPProblem.PlanarDichotomy.shearX δ) ∧
        InGeneralPosition ((Z.image
          (JSPProblem.PlanarDichotomy.shearX δ) : Finset (Euc 2)) : Set (Euc 2)) ∧
        DistinctX (Z.image (JSPProblem.PlanarDichotomy.shearX δ)) ∧
        (Z.image (JSPProblem.PlanarDichotomy.shearX δ)).card = X.card := by
  classical
  obtain ⟨x₀, hx₀⟩ : X.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨a, ha0, halast, hline, hvec⟩ := exists_direction ⟨x₀, hx₀⟩
  have hinj := injOn_projAlong halast hline
  set Z : Finset (Euc 2) := X.image (projAlong a) with hZdef
  have hZcard : Z.card = X.card := Finset.card_image_of_injOn hinj
  have hgpZ : InGeneralPosition (Z : Set (Euc 2)) :=
    inGeneralPosition_image_projAlong hX hXcard halast hinj hvec
  obtain ⟨δ, hδ⟩ := JSPProblem.PlanarDichotomy.exists_shearX_distinct Z
  set f : Euc 3 →ₗ[ℝ] Euc 2 :=
    (JSPProblem.PlanarDichotomy.shearX δ).comp (projAlong a) with hfdef
  set T : Euc 3 →ₗ[ℝ] Euc 3 := liftPlanar f with hTdef
  have hf0 : ∀ z : Euc 3, f z = 0 → z 2 = 0 → z = 0 := by
    intro z hfz hz2
    have hpa : projAlong a z = 0 := by
      have h1 : (JSPProblem.PlanarDichotomy.shearX δ) (projAlong a z) =
          (JSPProblem.PlanarDichotomy.shearX δ) 0 := by
        rw [map_zero]
        have := hfz
        rw [hfdef] at this
        simpa [LinearMap.comp_apply] using this
      exact JSPProblem.PlanarDichotomy.shearX_injective δ h1
    rw [← LinearMap.mem_ker, projAlong_ker a halast,
      Submodule.mem_span_singleton] at hpa
    obtain ⟨t, rfl⟩ := hpa
    have ht0 : t * a (Fin.last 2) = 0 := by
      have : (t • a : Euc 3) 2 = 0 := hz2
      simpa [PiLp.smul_apply, smul_eq_mul, show (2 : Fin 3) = Fin.last 2 from rfl]
        using this
    have ht : t = 0 := (mul_eq_zero.mp ht0).resolve_right halast
    rw [ht, zero_smul]
  have hT : Function.Injective T := liftPlanar_injective hf0
  have hX' : InGeneralPosition ((X.image T : Finset (Euc 3)) : Set (Euc 3)) :=
    inGeneralPosition_image_linear hX hXcard hT
  have hproj : ∀ x : Euc 3, proj2 (T x) = f x := proj2_liftPlanar f
  have hinjX' : Set.InjOn proj2 ((X.image T : Finset (Euc 3)) : Set (Euc 3)) := by
    intro z hz w hw hzw
    rw [Finset.coe_image] at hz hw
    obtain ⟨x, hx, rfl⟩ := hz
    obtain ⟨y, hy, rfl⟩ := hw
    rw [hproj, hproj] at hzw
    have hpa : projAlong a x = projAlong a y := by
      have := (JSPProblem.PlanarDichotomy.shearX_injective δ).eq_iff.mp hzw
      simpa [hfdef, LinearMap.comp_apply] using this
    have hxy : x = y := hinj (Finset.mem_coe.2 hx) (Finset.mem_coe.2 hy) hpa
    rw [hxy]
  have himg : (X.image T).image proj2 = Z.image
      (JSPProblem.PlanarDichotomy.shearX δ) := by
    rw [Finset.image_image, hZdef, Finset.image_image]
    apply Finset.image_congr
    intro x hx
    show (⇑proj2 ∘ ⇑T) x = (⇑(JSPProblem.PlanarDichotomy.shearX δ) ∘ ⇑(projAlong a)) x
    rw [Function.comp_apply, Function.comp_apply, hproj, hfdef]
    rfl
  refine ⟨T, hT, hX', hinjX', Z, δ, himg, ?_, ?_, ?_⟩
  · exact JSPProblem.PlanarDichotomy.inGeneralPosition_image_shearX hgpZ
      (by omega) δ
  · intro p hp q hq hpq
    rw [Finset.mem_image] at hp hq
    obtain ⟨x, hx, rfl⟩ := hp
    obtain ⟨y, hy, rfl⟩ := hq
    have hxy := hδ x hx y hy hpq
    rw [hxy]
  · rw [Finset.card_image_of_injective _
        (JSPProblem.PlanarDichotomy.shearX_injective δ)]
    exact hZcard


/-! ### Counting bounds -/

/-- Binomial coefficients are bounded by `(e·N/m)^m`. -/
private lemma choose_le_exp_pow {N m : ℕ} :
    ((N.choose m : ℕ) : ℝ) ≤ (Real.exp 1 * N / m) ^ m := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · have hfact : ((m : ℝ) / Real.exp 1) ^ m ≤ (Nat.factorial m : ℝ) := by
      have h := Stirling.le_factorial_stirling m
      have hs : (1:ℝ) ≤ √(2 * Real.pi * (m:ℝ)) := by
        rw [Real.one_le_sqrt]
        have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
        nlinarith [Real.pi_pos, Real.pi_gt_three]
      calc ((m:ℝ) / Real.exp 1) ^ m
          = 1 * ((m:ℝ) / Real.exp 1) ^ m := (one_mul _).symm
        _ ≤ √(2 * Real.pi * (m:ℝ)) * ((m:ℝ) / Real.exp 1) ^ m :=
            mul_le_mul_of_nonneg_right hs (by positivity)
        _ ≤ (Nat.factorial m : ℝ) := h
    calc ((N.choose m : ℕ) : ℝ)
        ≤ (N:ℝ) ^ m / (Nat.factorial m : ℝ) := Nat.choose_le_pow_div m N
      _ ≤ (N:ℝ) ^ m / ((m:ℝ) / Real.exp 1) ^ m :=
          div_le_div_of_nonneg_left (pow_nonneg (Nat.cast_nonneg N) m)
            (pow_pos (div_pos (by exact_mod_cast hm) (Real.exp_pos 1)) m) hfact
      _ = (Real.exp 1 * N / m) ^ m := by
          rw [div_pow, div_div_eq_mul_div, ← mul_pow,
            mul_comm (N:ℝ) (Real.exp 1), ← div_pow]

/-- The cap-size threshold used in the final `prop_2_1`-type applications. -/
private def capBound (n t : ℕ) : ℕ :=
  4 * ((n + 2 * (n / t) + 4).choose (2 * (n / t) + 4)) ^ 3

/-- `capBound` is subexponential in `n` for fixed `t`: it is at most
`4·b¹²·(b^{6/t})^n` where `b = e·(t/2 + 1)`. -/
private lemma capBound_le {t : ℕ} (ht : 1 ≤ t) (n : ℕ) :
    (capBound n t : ℝ) ≤
      4 * (Real.exp 1 * ((t:ℝ)/2 + 1)) ^ (12:ℝ) *
        ((Real.exp 1 * ((t:ℝ)/2 + 1)) ^ (6/(t:ℝ))) ^ (n:ℝ) := by
  set m : ℕ := 2 * (n / t) + 4 with hm
  set b : ℝ := Real.exp 1 * ((t:ℝ)/2 + 1) with hb
  have hbpos : (0:ℝ) < b := by
    rw [hb]; positivity
  have hb1 : (1:ℝ) ≤ b := by
    rw [hb]
    have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
    have he : (1:ℝ) ≤ Real.exp 1 :=
      le_trans (by norm_num : (1:ℝ) ≤ Real.exp 0)
        (Real.exp_monotone (by norm_num))
    nlinarith
  have ht0 : (0:ℝ) < t := by exact_mod_cast ht
  have hmpos : (0:ℝ) < (m:ℝ) := by
    rw [hm]; positivity
  -- `⌊n/t⌋ ≥ n/t - 1`, hence `m ≥ 2n/t + 2 > 2n/t`.
  have hdiv : (n:ℝ) / t < (n / t : ℕ) + 1 := by
    rw [div_lt_iff₀ ht0]
    have hdm := Nat.div_add_mod n t
    have hmod := Nat.mod_lt n ht
    have hdm' : ((t * (n / t) + n % t : ℕ) : ℝ) = (n:ℝ) := by
      exact_mod_cast hdm
    rw [← hdm']
    push_cast
    have h3 : ((n % t : ℕ) : ℝ) < t := by exact_mod_cast hmod
    linarith
  have hmge : (2:ℝ) * n / t ≤ (m:ℝ) := by
    rw [hm]; push_cast
    have h2 : 2 * (n:ℝ) / t = 2 * (n / t) := by ring
    rw [h2]
    linarith
  -- `(n + m)/m = n/m + 1 ≤ t/2 + 1`.
  have hNm : ((n:ℝ) + (m:ℝ)) / m ≤ (t:ℝ)/2 + 1 := by
    have h1 : (n:ℝ) / m ≤ t / 2 := by
      rw [div_le_iff₀ hmpos]
      have hmul := mul_le_mul_of_nonneg_right hmge ht0.le
      rw [div_mul_cancel₀ _ (ne_of_gt ht0)] at hmul
      rw [mul_comm (m:ℝ) t] at hmul
      linarith
    calc ((n:ℝ) + m) / m = n / m + 1 := by
          rw [add_div, div_self (ne_of_gt hmpos)]
      _ ≤ t/2 + 1 := by linarith
  have hchoose : (((n + m : ℕ).choose m : ℕ) : ℝ) ≤ b ^ m := by
    have h1 := choose_le_exp_pow (N := n + m) (m := m)
    rw [Nat.cast_add] at h1
    refine h1.trans ?_
    apply pow_le_pow_left₀ (by positivity)
    have h2 : Real.exp 1 * ((n:ℝ) + m) / m ≤ b := by
      rw [hb, mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos 1).le
      exact hNm
    exact h2
  -- `capBound = 4·choose³ ≤ 4·b^{3m}`.
  have hcap : (capBound n t : ℝ) ≤ 4 * b ^ (3 * m) := by
    have hN : n + 2 * (n / t) + 4 = n + m := by omega
    rw [capBound, hN]
    push_cast
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 4)
    calc (↑((n + m).choose m))^3 ≤ (b^m)^3 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) hchoose 3
      _ = b^(3*m) := by rw [← pow_mul]; congr 1; ring
  -- exponent comparison `3m ≤ 6n/t + 12`.
  have hexp : ((3 * m : ℕ) : ℝ) ≤ 6 * (n:ℝ) / t + 12 := by
    have hle : ((n / t : ℕ) : ℝ) ≤ (n:ℝ) / t := Nat.cast_div_le
    have hle' : 6 * ((n / t : ℕ) : ℝ) ≤ 6 * (n:ℝ) / t := by
      have h := mul_le_mul_of_nonneg_left hle (by norm_num : (0:ℝ) ≤ 6)
      rwa [← mul_div_assoc] at h
    rw [hm]; push_cast
    linarith [hle']
  calc (capBound n t : ℝ) ≤ 4 * b ^ (3 * m) := hcap
    _ ≤ 4 * b ^ (6 * (n:ℝ) / t + 12) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 4)
        rw [← Real.rpow_natCast b (3 * m)]
        exact Real.rpow_le_rpow_of_exponent_le hb1 hexp
    _ = 4 * ((b ^ (6/(t:ℝ))) ^ (n:ℝ) * b ^ (12:ℝ)) := by
        have h1 : (6:ℝ) * (n:ℝ) / t + 12 = (6/t) * n + 12 := by ring
        rw [h1, Real.rpow_add hbpos, Real.rpow_mul hbpos.le]
    _ = _ := by ring

/-- For `ε > 0` there is a block count `t` with `e·(t/2+1) < 2^{εt/24}`. -/
private lemma exists_large_t {ε : ℝ} (hε : 0 < ε) :
    ∃ t : ℕ, 1 ≤ t ∧
      Real.exp 1 * ((t:ℝ)/2 + 1) < (2:ℝ)^(ε*(t:ℝ)/24) := by
  set r : ℝ := (2:ℝ)^(-ε/24) with hrdef
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : |r| < 1 := by
    rw [abs_of_pos hr0]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  have htend : Tendsto (fun n : ℕ ↦ (n:ℝ) * r^n) atTop (nhds 0) := by
    simpa [pow_one] using
      tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr1
  have hev : ∀ᶠ n : ℕ in atTop, (n:ℝ) * r^n < 1/(4*Real.exp 1) :=
    htend.eventually (Iio_mem_nhds (by positivity))
  obtain ⟨t, hlt, ht1⟩ := (hev.and (eventually_ge_atTop 1)).exists
  have hle : Real.exp 1 * ((t:ℝ)/2 + 1) * r^t ≤
      2 * Real.exp 1 * ((t:ℝ) * r^t) := by
    have ht1' : (1:ℝ) ≤ t := by exact_mod_cast ht1
    have hcoef : Real.exp 1 * ((t:ℝ)/2 + 1) ≤ 2 * Real.exp 1 * t := by
      nlinarith [Real.exp_pos 1]
    calc Real.exp 1 * ((t:ℝ)/2 + 1) * r^t
        ≤ 2 * Real.exp 1 * t * r^t :=
          mul_le_mul_of_nonneg_right hcoef (pow_nonneg hr0.le _)
      _ = 2 * Real.exp 1 * ((t:ℝ) * r^t) := by ring
  have hlt2 : Real.exp 1 * ((t:ℝ)/2 + 1) * r^t < 1 := by
    refine hle.trans_lt ?_
    calc 2 * Real.exp 1 * ((t:ℝ) * r^t)
        < 2 * Real.exp 1 * (1/(4*Real.exp 1)) :=
          mul_lt_mul_of_pos_left hlt (by positivity)
      _ = 1/2 := by
          rw [mul_one_div,
            div_eq_iff (ne_of_gt (by positivity : (0:ℝ) < 4*Real.exp 1))]
          ring
      _ < 1 := by norm_num
  refine ⟨t, ht1, ?_⟩
  have hrt : r ^ t = (2:ℝ) ^ (-ε * (t:ℝ) / 24) := by
    rw [hrdef, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  have hpos : 0 < r ^ t := pow_pos hr0 t
  have h2 : Real.exp 1 * ((t:ℝ)/2 + 1) < 1 / r ^ t := by
    rw [lt_div_iff₀ hpos]
    exact hlt2
  have hfin : (1:ℝ) / r ^ t = (2:ℝ)^(ε * (t:ℝ)/24) := by
    rw [hrt, one_div, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rwa [hfin] at h2

/-- Eventually `capBound n t · 2^{C₀} < 2^{εn}`. -/
private lemma capBound_eventually {ε : ℝ} (hε : 0 < ε) {t : ℕ}
    (ht : 1 ≤ t)
    (htcond : Real.exp 1 * ((t:ℝ)/2 + 1) < (2:ℝ)^(ε*(t:ℝ)/24)) (C₀ : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (capBound n t : ℝ) * 2 ^ C₀ < (2:ℝ)^(ε * (n:ℝ)) := by
  set b : ℝ := Real.exp 1 * ((t:ℝ)/2 + 1) with hb
  have hbpos : 0 < b := by rw [hb]; positivity
  have ht0 : (0:ℝ) < t := by exact_mod_cast ht
  have hb1 : 1 ≤ b := by
    rw [hb]
    have he : (1:ℝ) ≤ Real.exp 1 :=
      le_trans (by norm_num : (1:ℝ) ≤ Real.exp 0)
        (Real.exp_monotone (by norm_num))
    nlinarith [Real.exp_pos 1]
  set D : ℝ := b ^ (6/(t:ℝ)) with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  have hDlt : D < (2:ℝ)^(ε/4) := by
    have hexp : (0:ℝ) < 6 / (t:ℝ) := by positivity
    have h1 : b ^ (6/(t:ℝ)) < ((2:ℝ)^(ε*(t:ℝ)/24)) ^ (6/(t:ℝ)) :=
      Real.rpow_lt_rpow hbpos.le htcond hexp
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)] at h1
    have he2 : ε * (t:ℝ) / 24 * (6 / t) = ε / 4 := by field_simp; ring
    rwa [he2] at h1
  have hconst : ∀ᶠ n : ℕ in atTop,
      4 * b ^ (12:ℝ) * 2 ^ C₀ ≤ (2:ℝ)^(3*ε*(n:ℝ)/4) := by
    have hb2 : (1:ℝ) < (2:ℝ)^(3*ε/4) :=
      Real.one_lt_rpow (by norm_num) (by linarith)
    have htend : Tendsto (fun n : ℕ ↦ ((2:ℝ)^(3*ε/4))^n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hb2
    have hconv : ∀ n : ℕ, (2:ℝ)^(3*ε*(n:ℝ)/4) = ((2:ℝ)^(3*ε/4))^n := by
      intro n
      rw [← Real.rpow_natCast ((2:ℝ)^(3*ε/4)) n,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 1; ring
    exact (htend.eventually_ge_atTop _).mono fun n hn ↦ by rwa [hconv n]
  filter_upwards [hconst, eventually_gt_atTop 0] with n hn hn0
  have hcap := capBound_le ht n
  have hDn : D ^ (n:ℝ) < (2:ℝ)^(ε*(n:ℝ)/4) := by
    have hn0' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn0
    have h1 : D ^ (n:ℝ) < ((2:ℝ)^(ε/4)) ^ (n:ℝ) :=
      Real.rpow_lt_rpow hDpos.le hDlt hn0'
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)] at h1
    have he : ε / 4 * (n:ℝ) = ε * (n:ℝ) / 4 := by ring
    rwa [he] at h1
  calc (capBound n t : ℝ) * 2 ^ C₀
      ≤ 4 * b ^ (12:ℝ) * D ^ (n:ℝ) * 2 ^ C₀ :=
        mul_le_mul_of_nonneg_right hcap (by positivity)
    _ = 4 * b ^ (12:ℝ) * 2 ^ C₀ * D ^ (n:ℝ) := by ring
    _ < 4 * b ^ (12:ℝ) * 2 ^ C₀ * (2:ℝ)^(ε*(n:ℝ)/4) :=
        mul_lt_mul_of_pos_left hDn (by positivity)
    _ ≤ (2:ℝ)^(3*ε*(n:ℝ)/4) * (2:ℝ)^(ε*(n:ℝ)/4) :=
        mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg (by norm_num) _)
    _ = (2:ℝ)^(ε*(n:ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1; ring


end GeometricInfrastructure

/-- **Geometric core of the §3 assembly** (Pohoata–Zakharov §3).  Fix the block
count `t` chosen by `exists_large_t`.  For all sufficiently large `n`, any
general-position `X ⊆ ℝ³` containing no `n`-element subset in convex position
satisfies `|X| ≤ capBound n t · 2^{εn/2}`: the `capBound` factor is the
`prop_2_1`-type binomial threshold (with the `≤ 3`-edge polytopes of
Proposition 3.1), and `2^{εn/2}` absorbs the subexponential thinning losses
`2^{O(k₀³)}`, `k₀ = n^{1/4}`, from `porValtr_positiveFraction` and `prop_2_5`
together with the `aboveBelow_ramsey`/`cor_2_4` and 3-uniform Ramsey
(`exists_ramsey`) reductions.

The intended proof: normalize the projection via `exists_normalization`, apply
`porValtr_positiveFraction` with `k₀ = ⌈n^{1/4}⌉`, thin the support fibers with
`prop_2_5`, extract the interval-split structure via `cor_2_4`, build the two
3-edge polytopes (Proposition 3.1), extract a `P¹`- or `P²`-free block with
`exists_isChain_or_isAntichain_sq'`, pass to a monochromatic clique via
`exists_ramsey`, and close with `prop_2_1` — whose current finite-polytope
statement must first be generalized to regions cut by at most three
halfspaces (the exponent is the number of boundary planes). -/
private theorem card_le_capBound_mul_exp (ε : ℝ) (hε : 0 < ε)
    {t : ℕ} (ht : 1 ≤ t) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ X : Finset (Euc 3),
      InGeneralPosition (X : Set (Euc 3)) →
      (∀ S ⊆ X, S.card = n → ¬ InConvexPosition S) →
      (X.card : ℝ) ≤ (capBound n t : ℝ) * (2:ℝ) ^ (ε * (n:ℝ) / 2) := by
  sorry

/-- **Theorem 1.1** of Pohoata–Zakharov, *Convex polytopes from fewer points*:
`ES₃(n) = 2^{o(n)}`.  For any `ε > 0` there exists `n₀(ε)` such that for every
`n ≥ n₀`, every set `X ⊆ ℝ³` in general position with `|X| ≥ 2^{εn}` contains
`n` points in convex position. -/
theorem es_three_subexponential (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ X : Finset (Euc 3),
      InGeneralPosition (X : Set (Euc 3)) →
      (2:ℝ) ^ (ε * (n:ℝ)) ≤ (X.card : ℝ) →
      ∃ S ⊆ X, S.card = n ∧ InConvexPosition S := by
  -- Parameter choices: the block count `t` is fixed once and for all via
  -- `exists_large_t`, large enough that `e·(t/2+1) < 2^{(ε/2)·t/24}`.
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨t, ht1, htcond⟩ := exists_large_t hε2
  -- `n₀₁`: the threshold from which the quantitative geometric core applies.
  obtain ⟨N₁, hN₁⟩ := card_le_capBound_mul_exp ε hε ht1
  -- `n₀₂`: the threshold where `capBound n t < 2^{(ε/2)·n}`.
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (capBound_eventually hε2 ht1 htcond 0)
  refine ⟨max n₀ N₁, fun n hn X hX hcard ↦ ?_⟩
  by_contra hno
  push_neg at hno
  -- `X` has no convex `n`-subset, so the geometric core bounds its size.
  have hcap := hN₁ n (le_trans (le_max_right _ _) hn) X hX hno
  have hbound : (capBound n t : ℝ) < (2:ℝ) ^ (ε * (n:ℝ) / 2) := by
    have h := hn₀ n (le_trans (le_max_left _ _) hn)
    rw [pow_zero, mul_one] at h
    have he : ε / 2 * (n:ℝ) = ε * (n:ℝ) / 2 := by ring
    rwa [he] at h
  have hpos : (0:ℝ) < (2:ℝ) ^ (ε * (n:ℝ) / 2) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hlt : (2:ℝ) ^ (ε * (n:ℝ)) < (2:ℝ) ^ (ε * (n:ℝ)) :=
    calc (2:ℝ) ^ (ε * (n:ℝ)) ≤ (X.card : ℝ) := hcard
      _ ≤ (capBound n t : ℝ) * (2:ℝ) ^ (ε * (n:ℝ) / 2) := hcap
      _ < (2:ℝ) ^ (ε * (n:ℝ) / 2) * (2:ℝ) ^ (ε * (n:ℝ) / 2) :=
          mul_lt_mul_of_pos_right hbound hpos
      _ = (2:ℝ) ^ (ε * (n:ℝ)) := by
          rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
          congr 1
          ring
  exact lt_irrefl _ hlt

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
