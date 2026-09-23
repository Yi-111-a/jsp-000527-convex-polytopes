import JSPProblem.Projection
import JSPProblem.Separation
import JSPProblem.SeparationHalving
import JSPProblem.Caps3D
import JSPProblem.PorValtr
import JSPProblem.PlanarDichotomy
import JSPProblem.SeparationRamsey
import JSPProblem.TriplePlanes

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
  have muu' : (u : Euc 2) 0 < (u' : Euc 2) 0 := hmono (Fin.lt_iff_val_lt_val.mpr (by omega))
  have muw : (u : Euc 2) 0 < (w : Euc 2) 0 := hmono (Fin.lt_iff_val_lt_val.mpr (by omega))
  have mzw : (z : Euc 2) 0 < (w : Euc 2) 0 := hmono (Fin.lt_iff_val_lt_val.mpr (by omega))
  have h1 : pvSgn σ * pvCross u u' w < 0 :=
    hshape ⟨a, by omega⟩ ⟨a + 1, by omega⟩ ⟨b + 1, by omega⟩
      (Fin.lt_iff_val_lt_val.mpr (by omega)) (Fin.lt_iff_val_lt_val.mpr (by omega))
  have key1 : pvSgn σ * (pvSl u w - pvSl u u') < 0 := by
    rw [pvCross_eq_mid muu' muw] at h1
    exact pv_mul_neg_of_pos_factor (mul_pos (sub_pos.mpr muu') (sub_pos.mpr muw)) h1
  have h2 : pvSgn σ * pvCross u z w < 0 :=
    hshape ⟨a, by omega⟩ ⟨b, by omega⟩ ⟨b + 1, by omega⟩
      (Fin.lt_iff_val_lt_val.mpr hab) (Fin.lt_iff_val_lt_val.mpr (by omega))
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
      have hzw : (z : Euc 2) 0 < (w : Euc 2) 0 := hmono (Fin.lt_iff_val_lt_val.mpr (by omega))
      have hww' : (w : Euc 2) 0 < (w' : Euc 2) 0 := hmono (Fin.lt_iff_val_lt_val.mpr (by omega))
      have huu' : (u : Euc 2) 0 < (u' : Euc 2) 0 := hmono (Fin.lt_iff_val_lt_val.mpr (by omega))
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
              (Fin.lt_iff_val_lt_val.mpr (by omega)) (Fin.lt_iff_val_lt_val.mpr (by omega))
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
      have huu' : (u : Euc 2) 0 < (u' : Euc 2) 0 := hmono (Fin.lt_iff_val_lt_val.mpr (by omega))
      have hww' : (w : Euc 2) 0 < (w' : Euc 2) 0 := hmono (Fin.lt_iff_val_lt_val.mpr (by omega))
      have hw'w'' : (w' : Euc 2) 0 < (w'' : Euc 2) 0 := hmono (Fin.lt_iff_val_lt_val.mpr (by omega))
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
              ⟨i.val + 1, by omega⟩ (Fin.lt_iff_val_lt_val.mpr (by omega))
              (Fin.lt_iff_val_lt_val.mpr (by omega))
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

/-! ### The `dirLeC` cylinder order over an arbitrary convex region

`prop_2_1` in `Caps3D.lean` is stated for a finite vertex set `P`, and the
exponent in its threshold is `edgeCount P`.  The regions used in the §3
assembly are unbounded intersections of (at most) three halfspaces, so a
variant is needed in which the set of edge directions `D` is supplied
abstractly together with the separation property `hsep` (proved for
three-halfspace regions in `separates_poly3` below).  The order `dirLeC` is
`dirLe` with `conv P` replaced by an arbitrary set `C`; the `aug` machinery
and the iterated Mirsky lemma are re-proved here because the `Caps3D`
versions are private to that file. -/

section PolyhedralCaps

variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

/-- `y ≺_{C,d} x`: `y` lies in the `d`-cylinder over `conv (C ∪ {x})`. -/
private def dirLeC (C : Set (Euc 3)) (d : Euc 3) (y x : Euc 3) : Prop :=
  ∃ w ∈ convexHull ℝ (C ∪ {x}), ∃ t : ℝ, y = w + t • d

private theorem dirLeC_refl (C : Set (Euc 3)) (d x : Euc 3) : dirLeC C d x x :=
  ⟨x, subset_convexHull _ _
    (Set.mem_union_right _ (Set.mem_singleton_iff.2 rfl)), 0, by simp⟩

private theorem dirLeC_mono {C₁ C₂ : Set (Euc 3)} (h : C₁ ⊆ C₂) (d : Euc 3)
    {y x : Euc 3} (hxy : dirLeC C₁ d y x) : dirLeC C₂ d y x := by
  obtain ⟨w, hw, t, rfl⟩ := hxy
  exact ⟨w, convexHull_mono
    (Set.union_subset_union h (Set.Subset.refl _)) hw, t, rfl⟩

private theorem dirLeC_trans {C : Set (Euc 3)} {d x y z : Euc 3}
    (hzy : dirLeC C d z y) (hyx : dirLeC C d y x) : dirLeC C d z x := by
  obtain ⟨w₁, hw₁, t₁, rfl⟩ := hzy
  obtain ⟨w₂, hw₂, t₂, rfl⟩ := hyx
  obtain ⟨w₁', hw₁', s₁, hs₁⟩ : ∃ w' ∈ convexHull ℝ (C ∪ {x}),
      ∃ s : ℝ, w₁ = w' + s • d := by
    rcases Set.eq_empty_or_nonempty C with hCe | hCne
    · rw [hCe, Set.empty_union] at hw₁
      rw [convexHull_singleton, Set.mem_singleton_iff] at hw₁
      exact ⟨w₂, hw₂, t₂, hw₁⟩
    · have hw₁' : w₁ ∈ convexJoin ℝ (convexHull ℝ C)
          ({w₂ + t₂ • d} : Set (Euc 3)) := by
        have hsub : convexHull ℝ (C ∪ {w₂ + t₂ • d}) ⊆
            convexJoin ℝ (convexHull ℝ C) {w₂ + t₂ • d} := by
          rw [← (convex_convexHull ℝ C).convexHull_union (convex_singleton _)
            hCne.convexHull (Set.singleton_nonempty _)]
          apply convexHull_mono
          exact Set.union_subset
            (subset_convexHull ℝ _ Set.subset_union_left)
            (Set.singleton_subset_iff.2 (Set.mem_union_right _ rfl))
        exact hsub hw₁
      rw [mem_convexJoin] at hw₁'
      obtain ⟨c, hc, b', hb', hseg⟩ := hw₁'
      rw [Set.mem_singleton_iff] at hb'; subst hb'
      rw [segment_eq_image₂] at hseg
      obtain ⟨⟨α₁, β₁⟩, ⟨hα, hβ, hαβ⟩, hcomb⟩ := hseg
      have hc' : c ∈ convexHull ℝ (C ∪ {x}) :=
        convexHull_mono Set.subset_union_left hc
      have hw₁'mem : α₁ • c + β₁ • w₂ ∈ convexHull ℝ (C ∪ {x}) :=
        (convex_convexHull _ _).segment_subset hc' hw₂
          (by rw [segment_eq_image₂]; exact ⟨(α₁, β₁), ⟨hα, hβ, hαβ⟩, rfl⟩)
      exact ⟨α₁ • c + β₁ • w₂, hw₁'mem, β₁ * t₂, by
        have hcomb' : α₁ • c + β₁ • (w₂ + t₂ • d) = w₁ := hcomb
        rw [← hcomb', smul_add, smul_smul, add_assoc]⟩
  exact ⟨w₁', hw₁', s₁ + t₁, by rw [hs₁, add_smul]; abel⟩

/-- If `H` vanishes on `d`, is equal at `x` and `y`, and is strictly smaller
on `C` than at `x`, then `x` and `y` are `dirLeC C d`-incomparable (provided
`d` is not parallel to `x - y`). -/
private theorem dirLeC_incomp {C : Set (Euc 3)} (hC : Convex ℝ C) {d : Euc 3}
    (H : Euc 3 →ₗ[ℝ] ℝ) (hd : H d = 0) {x y : Euc 3}
    (hxy : H x = H y) (hP : ∀ w ∈ C, H w < H x)
    (hpar : ∀ t : ℝ, x - y ≠ t • d) :
    ¬ dirLeC C d x y ∧ ¬ dirLeC C d y x := by
  -- for `z` with `H z = H x`, `w ∈ conv (C ∪ {z})` has `H w ≤ H z`,
  -- with equality only at `w = z`.
  have hmax : ∀ z : Euc 3, H z = H x → ∀ w : Euc 3,
      w ∈ convexHull ℝ (C ∪ {z}) →
      H w ≤ H z ∧ (H w = H z → w = z) := by
    intro z hz w hw
    rcases Set.eq_empty_or_nonempty C with hCe | hCne
    · rw [hCe, Set.empty_union, convexHull_singleton,
        Set.mem_singleton_iff] at hw
      subst hw
      exact ⟨le_rfl, fun _ ↦ rfl⟩
    · rw [hC.convexHull_union (convex_singleton _) hCne
        (Set.singleton_nonempty _), mem_convexJoin] at hw
      obtain ⟨a, ha, b', hb', hseg⟩ := hw
      rw [Set.mem_singleton_iff] at hb'; subst hb'
      rw [segment_eq_image₂] at hseg
      obtain ⟨⟨α₁, β₁⟩, ⟨hα, hβ, hαβ⟩, hcomb⟩ := hseg
      have hHa : H a < H z := hz ▸ hP a ha
      have hHw : H w = α₁ * H a + β₁ * H z := by
        rw [← hcomb, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
      refine ⟨?_, ?_⟩
      · rw [hHw]
        have h1 : α₁ * H a ≤ α₁ * H z :=
          mul_le_mul_of_nonneg_left hHa.le hα
        have h2 : α₁ * H z + β₁ * H z = H z := by
          rw [← add_mul, hαβ, one_mul]
        linarith [h1]
      · intro hEq
        have hα0 : α₁ = 0 := by
          have h1 : α₁ * H a + β₁ * H z = H z := by
            rw [← hHw]; exact hEq
          have h2 : α₁ * (H a - H z) = 0 := by
            have h3 : α₁ * H a + β₁ * H z = (α₁ + β₁) * H z := by
              rw [← h1]; ring
            have h4 : α₁ * H a + β₁ * H z - (α₁ + β₁) * H z =
                α₁ * (H a - H z) := by ring
            rw [hαβ, one_mul] at h4
            linarith [h4]
          exact (mul_eq_zero.1 h2).resolve_right
            (sub_ne_zero.2 (ne_of_lt hHa))
        have hβ1 : β₁ = 1 := by linarith [hαβ]
        rw [← hcomb, hα0, hβ1, zero_smul, one_smul, zero_add]
  constructor
  · rintro ⟨w, hw, t, rfl⟩
    obtain ⟨hle, heq⟩ := hmax y hxy.symm w hw
    have hHw : H (w + t • d) = H w := by
      rw [map_add, map_smul, hd, smul_zero, add_zero]
    have hwy : w = y := heq (by rw [← hHw]; exact hxy)
    exact hpar t (by rw [hwy]; abel)
  · rintro ⟨w, hw, t, rfl⟩
    obtain ⟨hle, heq⟩ := hmax x rfl w hw
    have hHw : H (w + t • d) = H w := by
      rw [map_add, map_smul, hd, smul_zero, add_zero]
    have hwx : w = x := heq (by rw [hxy, hHw])
    exact hpar (-t) (by rw [hwx, neg_smul]; abel)

/-! #### The augmented strict order (local copy)

`aug le ltt x y` is the strict part of `le`, with `le`-equivalent elements
ordered by `ltt`.  Identical to the private machinery in `Caps3D.lean`. -/

/-- The augmented strict order: `x < y` iff `x ≤ y` strictly, or `x, y` are
`le`-equivalent and `ltt x y`. -/
private def aug (le ltt : α → α → Prop) (x y : α) : Prop :=
  (le x y ∧ ¬ le y x) ∨ (le x y ∧ le y x ∧ ltt x y)

private theorem aug_irrefl {le ltt : α → α → Prop}
    (hrefl : ∀ x : α, le x x) (hirr : ∀ x : α, ¬ ltt x x) (x : α) :
    ¬ aug le ltt x x := by
  rintro (⟨-, h⟩ | ⟨-, -, h⟩)
  · exact h (hrefl x)
  · exact hirr x h

private theorem aug_trans {le ltt : α → α → Prop}
    (htr : ∀ {x y z : α}, le x y → le y z → le x z)
    (htr₂ : ∀ ⦃x y z : α⦄, ltt x y → ltt y z → ltt x z)
    {x y z : α} (hxy : aug le ltt x y) (hyz : aug le ltt y z) :
    aug le ltt x z := by
  rcases hxy with ⟨hxy1, hxy2⟩ | ⟨hxy1, hxy2, hxyl⟩
  · rcases hyz with ⟨hyz1, hyz2⟩ | ⟨hyz1, hyz2, -⟩
    · exact Or.inl ⟨htr hxy1 hyz1, fun hzx ↦ hyz2 (htr hzx hxy1)⟩
    · exact Or.inl ⟨htr hxy1 hyz1, fun hzx ↦ hxy2 (htr hyz1 hzx)⟩
  · rcases hyz with ⟨hyz1, hyz2⟩ | ⟨hyz1, hyz2, hyzl⟩
    · exact Or.inl ⟨htr hxy1 hyz1, fun hzx ↦ hyz2 (htr hzx hxy1)⟩
    · exact Or.inr ⟨htr hxy1 hyz1, htr hyz2 hxy2, htr₂ hxyl hyzl⟩

private theorem aug_le {le ltt : α → α → Prop} {x y : α}
    (h : aug le ltt x y) : le x y :=
  h.elim (fun h ↦ h.1) (fun h ↦ h.1)

/-- If `x, y` are `le`-comparable (in either direction), they are
`aug`-comparable. -/
private theorem aug_of_le_or_le {le ltt : α → α → Prop}
    (htri : ∀ ⦃a b : α⦄, a ≠ b → ltt a b ∨ ltt b a) {x y : α} (hxy : x ≠ y)
    (h : le x y ∨ le y x) : aug le ltt x y ∨ aug le ltt y x := by
  rcases h with h1 | h1
  · by_cases h2 : le y x
    · rcases htri hxy with hl | hl
      · exact Or.inl (Or.inr ⟨h1, h2, hl⟩)
      · exact Or.inr (Or.inr ⟨h2, h1, hl⟩)
    · exact Or.inl (Or.inl ⟨h1, h2⟩)
  · by_cases h2 : le x y
    · rcases htri hxy with hl | hl
      · exact Or.inl (Or.inr ⟨h2, h1, hl⟩)
      · exact Or.inr (Or.inr ⟨h1, h2, hl⟩)
    · exact Or.inr (Or.inl ⟨h1, h2⟩)

/-! #### Iterated Mirsky extraction (local copy) -/

/-- Mirsky-type dichotomy with an explicit bound: either an `r`-antichain of
size `> M`, or an `r`-chain `c` with `s.card ≤ c.card * M`. -/
private theorem exists_antichain_or_chain_mul (s : Finset α) (r : α → α → Prop)
    [DecidableRel r] (hirr : ∀ x, ¬ r x x)
    (htr : ∀ ⦃x y z⦄, r x y → r y z → r x z) (M : ℕ) :
    (∃ t : Finset α, t ⊆ s ∧ M < t.card ∧
      ∀ x ∈ t, ∀ y ∈ t, x ≠ y → ¬ r x y ∧ ¬ r y x) ∨
    (∃ c : Finset α, c ⊆ s ∧ (∀ x ∈ c, ∀ y ∈ c, x ≠ y → r x y ∨ r y x) ∧
      s.card ≤ c.card * M) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact Or.inr ⟨∅, Finset.empty_subset _, by simp, by simp⟩
  set R := s.image (chainRank s r) with hR
  have hRne : R.Nonempty := Finset.image_nonempty.mpr hs
  set h := R.max' hRne
  obtain ⟨x₀, hx₀, hx₀r⟩ : ∃ x₀ ∈ s, chainRank s r x₀ = h := by
    have hh : h ∈ R := Finset.max'_mem R hRne
    rw [hR, Finset.mem_image] at hh
    obtain ⟨x₀, hx₀, hx₀e⟩ := hh
    exact ⟨x₀, hx₀, hx₀e⟩
  have hrank_le : ∀ x ∈ s, chainRank s r x ≤ h :=
    fun x hx ↦ Finset.le_max' R _ (Finset.mem_image_of_mem _ hx)
  have hrank_pos : ∀ x ∈ s, 1 ≤ chainRank s r x :=
    fun _ hx ↦ chainRank_pos s r hx
  set fib := fun i ↦ s.filter (fun x ↦ chainRank s r x = i) with hfib
  by_cases hbig : ∃ i, M < (fib i).card
  · obtain ⟨i, hi⟩ := hbig
    refine Or.inl ⟨fib i, Finset.filter_subset _ _, hi, ?_⟩
    intro x hx y hy hxy
    rw [hfib, Finset.mem_filter] at hx hy
    constructor
    · intro hr
      have hh := chainRank_lt_of_rel s r hirr htr hx.1 hy.1 hr
      rw [hx.2, hy.2] at hh
      exact lt_irrefl _ hh
    · intro hr
      have hh := chainRank_lt_of_rel s r hirr htr hy.1 hx.1 hr
      rw [hy.2, hx.2] at hh
      exact lt_irrefl _ hh
  · push_neg at hbig
    have hcover : s ⊆ (Finset.Icc 1 h).biUnion fib := by
      intro x hx
      simp only [Finset.mem_biUnion, Finset.mem_Icc]
      exact ⟨chainRank s r x, ⟨hrank_pos x hx, hrank_le x hx⟩,
        by simp [hfib, hx]⟩
    have hcard_le : s.card ≤ h * M := by
      calc s.card ≤ ((Finset.Icc 1 h).biUnion fib).card :=
            Finset.card_le_card hcover
        _ ≤ ∑ i ∈ Finset.Icc 1 h, (fib i).card := Finset.card_biUnion_le
        _ ≤ ∑ _i ∈ Finset.Icc 1 h, M := Finset.sum_le_sum fun i _ ↦ hbig i
        _ = h * M := by
            rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc,
              Nat.add_sub_cancel, Nat.cast_id]
    obtain ⟨c, hcto, hcard⟩ := exists_chainTo_card_chainRank s r hx₀
    refine Or.inr ⟨c, hcto.1, hcto.2.2.2, ?_⟩
    rw [hx₀r] at hcard
    rw [hcard]
    exact hcard_le

/-- Iterated Mirsky extraction: if every pair of distinct points of `X` is
`rᵢ`-incomparable for some `i ∈ E` and `|X| > M ^ |E|`, some `rᵢ` has an
antichain of size `> M`. -/
private theorem exists_antichain_iter
    (r : ι → α → α → Prop) [∀ i, DecidableRel (r i)]
    (hirr : ∀ i x, ¬ r i x x) (htr : ∀ i ⦃x y z⦄, r i x y → r i y z → r i x z)
    {M : ℕ} (hM : 1 ≤ M) :
    ∀ E : Finset ι, ∀ X : Finset α,
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → ∃ i ∈ E, ¬ r i x y ∧ ¬ r i y x) →
      M ^ E.card < X.card →
      ∃ i ∈ E, ∃ A : Finset α, A ⊆ X ∧ M < A.card ∧
        ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬ r i x y ∧ ¬ r i y x := by
  intro E
  induction E using Finset.induction_on with
  | empty =>
    intro X hsep hcard
    rw [Finset.card_empty, pow_zero] at hcard
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 hcard
    obtain ⟨i, hi, -⟩ := hsep x hx y hy hxy
    exact absurd hi (Finset.notMem_empty i)
  | insert a s ha IH =>
    intro X hsep hcard
    rw [Finset.card_insert_of_notMem ha, pow_succ] at hcard
    rcases exists_antichain_or_chain_mul X (r a) (hirr a) (htr a) M with hA | hC
    · obtain ⟨A, hAX, hAcard, hanti⟩ := hA
      exact ⟨a, Finset.mem_insert_self _ _, A, hAX, hAcard, hanti⟩
    · obtain ⟨c, hcX, hcchain, hcbound⟩ := hC
      have hsep' : ∀ x ∈ c, ∀ y ∈ c, x ≠ y →
          ∃ j ∈ s, ¬ r j x y ∧ ¬ r j y x := by
        intro x hx y hy hxy
        obtain ⟨j, hj, hj1, hj2⟩ := hsep x (hcX hx) y (hcX hy) hxy
        rcases Finset.mem_insert.1 hj with rfl | hjs
        · rcases hcchain x hx y hy hxy with h | h
          · exact absurd h hj1
          · exact absurd h hj2
        · exact ⟨j, hjs, hj1, hj2⟩
      have hcc : M ^ s.card < c.card := by
        have hle : M ^ s.card * M < c.card * M := lt_of_lt_of_le hcard hcbound
        exact Nat.lt_of_mul_lt_mul_right hle
      obtain ⟨j, hjs, A, hAc, hAcard, hanti⟩ := IH c hsep' hcc
      exact ⟨j, Finset.mem_insert_of_mem hjs, A, hAc.trans hcX, hAcard, hanti⟩

/-- **Proposition 2.1 for a convex region with few boundary directions.**
`C` is an arbitrary convex set (the intended application is an intersection
of at most three halfspaces); `D` is a finite set of directions and `hsep`
asserts that every pair `x y` admits a `C`-supporting plane through `x, y`
parallel to some `d ∈ D` and not containing `x - y`.  The cap conclusion is
stated relative to `conv Q` for a finite `Q ⊆ C` — this is exactly the form
needed for gluing alternating caps in the §3 assembly. -/
private theorem prop_2_1_poly
    (C : Set (Euc 3)) (hC : Convex ℝ C)
    (D : Finset (Euc 3)) (hD : ∀ d ∈ D, d ≠ 0)
    (Q : Finset (Euc 3)) (hQC : (Q : Set (Euc 3)) ⊆ C)
    {X : Finset (Euc 3)} (hX : InGeneralPosition (X : Set (Euc 3)))
    (hX4 : 4 ≤ X.card)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ∃ d ∈ D, ∃ H : Euc 3 →ₗ[ℝ] ℝ,
      H d = 0 ∧ H x = H y ∧ (∀ w ∈ C, H w < H x) ∧
        ∀ t : ℝ, x - y ≠ t • d)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hcard : (a + b - 4).choose (a - 2) ^ D.card < X.card) :
    (∃ Y ⊆ X, Y.card = a ∧ CapOf Y (convexHull ℝ (Q : Set (Euc 3)))) ∨
      (∃ S ⊆ X, S.card = b ∧ InConvexPosition S) := by
  classical
  -- `hsep` implies `X` is `conv Q`-free (a fortiori `C`-free).
  have hQC' : convexHull ℝ (Q : Set (Euc 3)) ⊆ C :=
    convexHull_min hQC hC
  have hXfree : FreeOf X (convexHull ℝ (Q : Set (Euc 3))) := by
    intro x hx y hy hxy w hwaff hwQ
    obtain ⟨d, hdD, H, hHd, hHxy, hHC, -⟩ := hsep x hx y hy hxy
    have hHw : H w = H x := by
      have hmem : w -ᵥ x ∈ vectorSpan ℝ ({x, y} : Set (Euc 3)) :=
        vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan ℝ hwaff
          (mem_affineSpan ℝ (Set.mem_insert _ _))
      rw [vectorSpan_pair] at hmem
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hmem
      have hsub : w - x = t • (x -ᵥ y) := by
        have : w -ᵥ x = t • (x -ᵥ y) := ht
        rwa [vsub_eq_sub, vsub_eq_sub] at this
      have h1 : H (w - x) = t * (H x - H y) := by
        rw [hsub, map_smul, smul_eq_mul, map_sub]
      have h2 : H (w - x) = H w - H x := map_sub _ _ _
      linarith [hHxy]
    have hlt : H w < H x := hHC w (hQC' hwQ)
    linarith [hHw]
  rcases Nat.lt_or_ge a 3 with ha3 | ha3
  · have hM : (a + b - 4).choose (a - 2) = 1 := by
      interval_cases a <;> simp
    rw [hM, one_pow] at hcard
    obtain ⟨Y, hYX, hYcard⟩ :=
      Finset.exists_subset_card_eq (show a ≤ X.card by omega)
    refine Or.inl ⟨Y, hYX, hYcard, ?_⟩
    interval_cases a
    · obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 hYcard
      rw [Finset.singleton_subset_iff] at hYX
      obtain ⟨y, hyX, hyx⟩ : ∃ y ∈ X, y ≠ x := by
        have hne : (X.erase x).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem hYX]
          omega
        obtain ⟨y, hy⟩ := hne
        exact ⟨y, (Finset.mem_erase.1 hy).2, (Finset.mem_erase.1 hy).1⟩
      exact capOf_singleton hXfree hC hYX hyX (Ne.symm hyx)
    · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hYcard
      rw [Finset.insert_subset_iff] at hYX
      exact capOf_pair hXfree hC hYX.1
        (Finset.singleton_subset_iff.1 hYX.2) hxy
  · rcases Nat.lt_or_ge b 3 with hb3 | hb3
    · obtain ⟨S, hSX, hScard⟩ : ∃ S ⊆ X, S.card = b := by
        apply Finset.exists_subset_card_eq
        rcases Nat.lt_or_ge b 2 with hb2 | hb2
        · omega
        · have hM : (a + b - 4).choose (a - 2) = 1 := by
            have hb2' : b = 2 := by omega
            subst hb2'
            have : a + 2 - 4 = a - 2 := by omega
            rw [this, Nat.choose_self]
          rw [hM, one_pow] at hcard
          omega
      refine Or.inr ⟨S, hSX, hScard, ?_⟩
      interval_cases b
      · obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 hScard
        exact inConvexPosition_singleton
      · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hScard
        exact inConvexPosition_pair hxy
    · -- `a, b ≥ 3`: the substantive case.
      have hM : 1 ≤ (a + b - 4).choose (a - 2) := Nat.choose_pos (by omega)
      -- the strict augment of `≺_{C,d}` by a well-order tiebreak
      have hltt_irr : ∀ x : Euc 3, ¬ WellOrderingRel x x := fun x ↦ irrefl x
      have hltt_tr : ∀ ⦃x y z : Euc 3⦄,
          WellOrderingRel x y → WellOrderingRel y z → WellOrderingRel x z := by
        intro x y z h1 h2
        exact _root_.trans h1 h2
      have hltt_tri : ∀ ⦃x y : Euc 3⦄, x ≠ y →
          WellOrderingRel x y ∨ WellOrderingRel y x := by
        intro x y hxy
        rcases trichotomous (r := WellOrderingRel) x y with h1 | h2 | h3
        · exact Or.inl h1
        · exact absurd h2 hxy
        · exact Or.inr h3
      set rel : Euc 3 → Euc 3 → Euc 3 → Prop :=
        fun d ↦ aug (dirLeC C d) WellOrderingRel with hrel
      haveI : ∀ d : Euc 3, DecidableRel (rel d) :=
        fun d a b ↦ Classical.propDecidable _
      have hirr : ∀ d x, ¬ rel d x x := fun d x ↦
        aug_irrefl (fun z ↦ dirLeC_refl C d z) hltt_irr x
      have htr : ∀ d ⦃x y z⦄, rel d x y → rel d y z → rel d x z := by
        intro d x y z h1 h2
        exact aug_trans (le := dirLeC C d) (ltt := WellOrderingRel)
          (dirLeC_trans (C := C) (d := d)) hltt_tr h1 h2
      -- every pair is separated by some direction `d ∈ D`.
      have hsep' : ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
          ∃ d ∈ D, ¬ rel d x y ∧ ¬ rel d y x := by
        intro x hx y hy hxy
        obtain ⟨d, hdD, H, hHd, hHxy, hHC, hpar⟩ := hsep x hx y hy hxy
        refine ⟨d, hdD, ?_⟩
        obtain ⟨h1, h2⟩ := dirLeC_incomp hC H hHd hHxy hHC hpar
        exact ⟨fun h ↦ h1 (aug_le h), fun h ↦ h2 (aug_le h)⟩
      obtain ⟨d₀, hd₀D, A, hAX, hAcard, hAanti⟩ := exists_antichain_iter rel
        hirr htr hM D X hsep' hcard
      have hd₀ : d₀ ≠ 0 := hD d₀ hd₀D
      have hAanti' : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
          ¬ dirLeC C d₀ y x ∧ ¬ dirLeC C d₀ x y := by
        intro x hx y hy hxy
        obtain ⟨h1, h2⟩ := hAanti x hx y hy hxy
        constructor
        · intro h
          rcases aug_of_le_or_le hltt_tri hxy (Or.inr h) with h' | h'
          · exact h1 h'
          · exact h2 h'
        · intro h
          rcases aug_of_le_or_le hltt_tri hxy (Or.inl h) with h' | h'
          · exact h1 h'
          · exact h2 h'
      -- downgrade the `dirLeC`-antichain to a `dirLe Q`-antichain
      have hdirQ : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
          ¬ dirLe Q d₀ y x ∧ ¬ dirLe Q d₀ x y := by
        intro x hx y hy hxy
        obtain ⟨h1, h2⟩ := hAanti' x hx y hy hxy
        refine ⟨fun h ↦ h1 ?_, fun h ↦ h2 ?_⟩
        · obtain ⟨w, hw, t, rfl⟩ := h
          exact ⟨w, convexHull_mono
            (Set.union_subset_union_left _ hQC) hw, t, rfl⟩
        · obtain ⟨w, hw, t, rfl⟩ := h
          exact ⟨w, convexHull_mono
            (Set.union_subset_union_left _ hQC) hw, t, rfl⟩
      obtain ⟨π, hinj, hgpZ, hantiπ⟩ := exists_generic_projection hX hX4 hAX
        hd₀ hdirQ
      set Z := A.image π with hZdef
      have hcardZ : (a + b - 4).choose (a - 2) < Z.card := by
        rw [hZdef, Finset.card_image_of_injOn hinj]
        exact hAcard
      have hpair : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q →
          q ∉ convexHull ℝ
            (convexHull ℝ (π '' (Q : Set (Euc 3))) ∪ ({p} : Set (Euc 2))) := by
        intro p hp q hq hpq
        obtain ⟨x, hxA, rfl⟩ := Finset.mem_image.1 hp
        obtain ⟨y, hyA, rfl⟩ := Finset.mem_image.1 hq
        have hxy : x ≠ y := fun e ↦ hpq (congrArg π e)
        rw [convexHull_convHull_union_singleton]
        exact (hantiπ x hxA y hyA hxy).1
      obtain hplanar | hplanar := planar_dichotomy (convex_convexHull _ _)
        ((Q.finite_toSet.image π).isCompact_convexHull ℝ) hgpZ hpair ha3 hb3
        hcardZ
      · obtain ⟨A', hA'Z, hA'card, hcap'⟩ := hplanar
        obtain ⟨Y, hYA, himg, hYcard⟩ := exists_preimage_finset hinj hA'Z
        refine Or.inl ⟨Y, hYA.trans hAX, hYcard.trans hA'card, ?_⟩
        rw [← himg] at hcap'
        exact lift_cap hinj hYA
          (LinearMap.image_convexHull π (Q : Set (Euc 3))).le hcap'
      · obtain ⟨B', hB'Z, hB'card, hconv'⟩ := hplanar
        obtain ⟨S, hSA, himg, hScard⟩ := exists_preimage_finset hinj hB'Z
        refine Or.inr ⟨S, hSA.trans hAX, hScard.trans hB'card, ?_⟩
        rw [← himg] at hconv'
        exact lift_convexPosition hinj hSA hconv'

end PolyhedralCaps

section SeparationPolytope

/-- A nonzero vector in the intersection of the kernels of two linear
functionals on `Euc 3` (two planes through the origin always share a line). -/
private lemma exists_mem_ker_ker (g h : Euc 3 →ₗ[ℝ] ℝ) :
    ∃ d : Euc 3, d ≠ 0 ∧ g d = 0 ∧ h d = 0 := by
  have hker : LinearMap.ker (g.prod h) ≠ ⊥ := by
    intro hbot
    have h1 := LinearMap.finrank_range_add_finrank_ker (g.prod h)
    have h2 : Module.finrank ℝ (LinearMap.range (g.prod h)) ≤ 2 :=
      le_trans (Submodule.finrank_le _)
        (by simp [Module.finrank_prod, finrank_self])
    have h3 : Module.finrank ℝ (Euc 3) = 3 := finrank_euclideanSpace_fin
    rw [hbot, finrank_bot, h3] at h1
    omega
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.ker_prod] at hd
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hd
  exact ⟨d, hd0, LinearMap.mem_ker.mp h1, LinearMap.mem_ker.mp h2⟩

/-- If every lower bound is strictly below every upper bound, the joint open
interval is nonempty. -/
private lemma exists_between_of_forall {lo hi : Finset ℝ}
    (h : ∀ l ∈ lo, ∀ u ∈ hi, l < u) :
    ∃ t : ℝ, (∀ l ∈ lo, l < t) ∧ (∀ u ∈ hi, t < u) := by
  rcases lo.eq_empty_or_nonempty with hl | hl
  · rcases hi.eq_empty_or_nonempty with hh | hh
    · exact ⟨0, by simp [hl], by simp [hh]⟩
    · refine ⟨hi.min' hh - 1, by simp [hl], fun u hu ↦ ?_⟩
      have := Finset.min'_le hi u hu
      linarith
  · rcases hi.eq_empty_or_nonempty with hh | hh
    · refine ⟨lo.max' hl + 1, fun l hlm ↦ ?_, by simp [hh]⟩
      have := Finset.le_max' lo l hlm
      linarith
    · have hlt : lo.max' hl < hi.min' hh :=
        h _ (Finset.max'_mem _ _) _ (Finset.min'_mem _ _)
      refine ⟨(lo.max' hl + hi.min' hh) / 2, fun l hlm ↦ ?_, fun u hu ↦ ?_⟩
      · have := Finset.le_max' lo l hlm
        linarith
      · have := Finset.min'_le hi u hu
        linarith

/-- The hard case of `separates_poly3`: the secant direction `v = y - x` is
not parallel to the boundary planes of facets `0` and `1`.  Comparing the
bound values `Bᵢ = (cᵢ - gᵢx)/gᵢv` along the line `x + t·v` with the fact
that the line misses `C` produces a violated bound pair `Bₛ ≤ Bᵣ`, and the
bisecting functional `(gₛv)⁻¹gₛ - (gᵣv)⁻¹gᵣ` is a supporting plane whose
kernel contains the corresponding edge direction. -/
private lemma sep_hard_case
    (C : Set (Euc 3)) {g₀ g₁ g₂ : Euc 3 →ₗ[ℝ] ℝ} {c₀ c₁ c₂ : ℝ}
    (hC : C = {z | g₀ z < c₀ ∧ c₁ < g₁ z ∧ c₂ < g₂ z})
    {x y : Euc 3} (hx2 : c₂ < g₂ x)
    {v : Euc 3} (hvdef : v = y - x) (hv : v ≠ 0)
    (hline : ∀ t : ℝ, ¬ (g₀ (x + t • v) < c₀ ∧ c₁ < g₁ (x + t • v) ∧
      c₂ < g₂ (x + t • v)))
    (hg0v : g₀ v ≠ 0) (hg1v : g₁ v ≠ 0)
    {D : Finset (Euc 3)} {e01 e02 e12 : Euc 3}
    (he01 : e01 ≠ 0 ∧ g₀ e01 = 0 ∧ g₁ e01 = 0)
    (he02 : e02 ≠ 0 ∧ g₀ e02 = 0 ∧ g₂ e02 = 0)
    (he12 : e12 ≠ 0 ∧ g₁ e12 = 0 ∧ g₂ e12 = 0)
    (hm01 : e01 ∈ D) (hm02 : e02 ∈ D) (hm12 : e12 ∈ D) :
    ∃ d ∈ D, ∃ H : Euc 3 →ₗ[ℝ] ℝ,
      H d = 0 ∧ H x = H y ∧
        (∀ w ∈ C, H w < H x) ∧
        ∀ t : ℝ, x - y ≠ t • d := by
  classical
  have memC : ∀ w : Euc 3, w ∈ C →
      g₀ w < c₀ ∧ c₁ < g₁ w ∧ c₂ < g₂ w :=
    fun w hw ↦ by
      rw [hC] at hw
      exact hw
  -- a violated bound pair `(r, s)` gives a supporting plane in direction `d`
  have finalize : ∀ {gr gs : Euc 3 →ₗ[ℝ] ℝ} {cr cs : ℝ} {d : Euc 3},
      gr v ≠ 0 → gs v ≠ 0 →
      (∀ w : Euc 3, g₀ w < c₀ → c₁ < g₁ w → c₂ < g₂ w →
        (cr - gr w) / gr v < 0) →
      (∀ w : Euc 3, g₀ w < c₀ → c₁ < g₁ w → c₂ < g₂ w →
        0 < (cs - gs w) / gs v) →
      (cs - gs x) / gs v ≤ (cr - gr x) / gr v →
      gr d = 0 → gs d = 0 → d ∈ D → d ≠ 0 →
      ∃ d ∈ D, ∃ H : Euc 3 →ₗ[ℝ] ℝ, H d = 0 ∧ H x = H y ∧
        (∀ w ∈ C, H w < H x) ∧
        ∀ t : ℝ, x - y ≠ t • d := by
    intro gr gs cr cs d hrv hsv hLB hUB hviol hdr hds hdD hd0
    have hpar : ∀ t : ℝ, x - y ≠ t • d := by
      intro t ht
      have e1 : gr (x - y) = 0 := by
        rw [ht, map_smul, smul_eq_mul, hdr, mul_zero]
      have e2 : gr (x - y) = -gr v := by
        rw [hvdef, map_sub, map_sub]
        ring
      rw [e2] at e1
      exact hrv (neg_eq_zero.mp e1)
    refine ⟨d, hdD, (gs v)⁻¹ • gs - (gr v)⁻¹ • gr, ?_, ?_, ?_, hpar⟩
    · simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        hdr, hds, mul_zero, sub_self]
    · have hHv : ((gs v)⁻¹ • gs - (gr v)⁻¹ • gr) v = 0 := by
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
        rw [inv_mul_cancel₀ hsv, inv_mul_cancel₀ hrv, sub_self]
      have h2 : ((gs v)⁻¹ • gs - (gr v)⁻¹ • gr) (y - x) = 0 := by
        rw [← hvdef]
        exact hHv
      rw [map_sub] at h2
      linarith
    · intro w hw
      obtain ⟨hw0, hw1, hw2⟩ := memC w hw
      have hLBw := hLB w hw0 hw1 hw2
      have hUBw := hUB w hw0 hw1 hw2
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [← sub_neg]
      have e1 : (gs v)⁻¹ * gs w - (gr v)⁻¹ * gr w -
          ((gs v)⁻¹ * gs x - (gr v)⁻¹ * gr x) =
          (cs - gs x) / gs v - (cr - gr x) / gr v -
            ((cs - gs w) / gs v - (cr - gr w) / gr v) := by
        field_simp
        ring
      rw [e1]
      linarith
  -- the side signs of the bounds at `w ∈ C` for each facet role
  have LB0 : g₀ v < 0 → ∀ w : Euc 3, g₀ w < c₀ → c₁ < g₁ w → c₂ < g₂ w →
      (c₀ - g₀ w) / g₀ v < 0 :=
    fun h w hw0 _ _ ↦ div_neg_of_pos_of_neg (by linarith) h
  have UB0 : 0 < g₀ v → ∀ w : Euc 3, g₀ w < c₀ → c₁ < g₁ w → c₂ < g₂ w →
      0 < (c₀ - g₀ w) / g₀ v :=
    fun h w hw0 _ _ ↦ div_pos (by linarith) h
  have LB1 : 0 < g₁ v → ∀ w : Euc 3, g₀ w < c₀ → c₁ < g₁ w → c₂ < g₂ w →
      (c₁ - g₁ w) / g₁ v < 0 :=
    fun h w _ hw1 _ ↦ div_neg_of_neg_of_pos (by linarith) h
  have UB1 : g₁ v < 0 → ∀ w : Euc 3, g₀ w < c₀ → c₁ < g₁ w → c₂ < g₂ w →
      0 < (c₁ - g₁ w) / g₁ v :=
    fun h w _ hw1 _ ↦ div_pos_of_neg_of_neg (by linarith) h
  have LB2 : 0 < g₂ v → ∀ w : Euc 3, g₀ w < c₀ → c₁ < g₁ w → c₂ < g₂ w →
      (c₂ - g₂ w) / g₂ v < 0 :=
    fun h w _ _ hw2 ↦ div_neg_of_neg_of_pos (by linarith) h
  have UB2 : g₂ v < 0 → ∀ w : Euc 3, g₀ w < c₀ → c₁ < g₁ w → c₂ < g₂ w →
      0 < (c₂ - g₂ w) / g₂ v :=
    fun h w _ _ hw2 ↦ div_pos_of_neg_of_neg (by linarith) h
  -- the lower/upper bound sets on the line parameter
  set lo : Finset ℝ :=
    (if g₀ v < 0 then {(c₀ - g₀ x) / g₀ v} else ∅) ∪
      ((if 0 < g₁ v then {(c₁ - g₁ x) / g₁ v} else ∅) ∪
        if 0 < g₂ v then {(c₂ - g₂ x) / g₂ v} else ∅) with hlodef
  set hi : Finset ℝ :=
    (if 0 < g₀ v then {(c₀ - g₀ x) / g₀ v} else ∅) ∪
      ((if g₁ v < 0 then {(c₁ - g₁ x) / g₁ v} else ∅) ∪
        if g₂ v < 0 then {(c₂ - g₂ x) / g₂ v} else ∅) with hhidef
  have hmem_lo : ∀ {b : ℝ}, b ∈ lo →
      (g₀ v < 0 ∧ b = (c₀ - g₀ x) / g₀ v) ∨
        (0 < g₁ v ∧ b = (c₁ - g₁ x) / g₁ v) ∨
          (0 < g₂ v ∧ b = (c₂ - g₂ x) / g₂ v) := by
    intro b hb
    rw [hlodef] at hb
    rcases Finset.mem_union.mp hb with hb | hb
    · by_cases h : g₀ v < 0
      · rw [if_pos h, Finset.mem_singleton] at hb
        exact Or.inl ⟨h, hb⟩
      · rw [if_neg h] at hb
        exact absurd hb (Finset.notMem_empty _)
    · rcases Finset.mem_union.mp hb with hb | hb
      · by_cases h : 0 < g₁ v
        · rw [if_pos h, Finset.mem_singleton] at hb
          exact Or.inr (Or.inl ⟨h, hb⟩)
        · rw [if_neg h] at hb
          exact absurd hb (Finset.notMem_empty _)
      · by_cases h : 0 < g₂ v
        · rw [if_pos h, Finset.mem_singleton] at hb
          exact Or.inr (Or.inr ⟨h, hb⟩)
        · rw [if_neg h] at hb
          exact absurd hb (Finset.notMem_empty _)
  have hmem_hi : ∀ {b : ℝ}, b ∈ hi →
      (0 < g₀ v ∧ b = (c₀ - g₀ x) / g₀ v) ∨
        (g₁ v < 0 ∧ b = (c₁ - g₁ x) / g₁ v) ∨
          (g₂ v < 0 ∧ b = (c₂ - g₂ x) / g₂ v) := by
    intro b hb
    rw [hhidef] at hb
    rcases Finset.mem_union.mp hb with hb | hb
    · by_cases h : 0 < g₀ v
      · rw [if_pos h, Finset.mem_singleton] at hb
        exact Or.inl ⟨h, hb⟩
      · rw [if_neg h] at hb
        exact absurd hb (Finset.notMem_empty _)
    · rcases Finset.mem_union.mp hb with hb | hb
      · by_cases h : g₁ v < 0
        · rw [if_pos h, Finset.mem_singleton] at hb
          exact Or.inr (Or.inl ⟨h, hb⟩)
        · rw [if_neg h] at hb
          exact absurd hb (Finset.notMem_empty _)
      · by_cases h : g₂ v < 0
        · rw [if_pos h, Finset.mem_singleton] at hb
          exact Or.inr (Or.inr ⟨h, hb⟩)
        · rw [if_neg h] at hb
          exact absurd hb (Finset.notMem_empty _)
  have hmem_lo_of : ∀ {b : ℝ},
      (g₀ v < 0 ∧ b = (c₀ - g₀ x) / g₀ v) ∨
        (0 < g₁ v ∧ b = (c₁ - g₁ x) / g₁ v) ∨
          (0 < g₂ v ∧ b = (c₂ - g₂ x) / g₂ v) → b ∈ lo := by
    intro b hb
    rw [hlodef]
    rcases hb with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exact Finset.mem_union_left _ (by
        rw [if_pos h]; exact Finset.mem_singleton_self _)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (by
        rw [if_pos h]; exact Finset.mem_singleton_self _))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (by
        rw [if_pos h]; exact Finset.mem_singleton_self _))
  have hmem_hi_of : ∀ {b : ℝ},
      (0 < g₀ v ∧ b = (c₀ - g₀ x) / g₀ v) ∨
        (g₁ v < 0 ∧ b = (c₁ - g₁ x) / g₁ v) ∨
          (g₂ v < 0 ∧ b = (c₂ - g₂ x) / g₂ v) → b ∈ hi := by
    intro b hb
    rw [hhidef]
    rcases hb with ⟨h, rfl⟩ | ⟨h, rfl⟩ | ⟨h, rfl⟩
    · exact Finset.mem_union_left _ (by
        rw [if_pos h]; exact Finset.mem_singleton_self _)
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (by
        rw [if_pos h]; exact Finset.mem_singleton_self _))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (by
        rw [if_pos h]; exact Finset.mem_singleton_self _))
  -- the joint interval of admissible parameters is empty
  have hempty : ¬ ∃ t : ℝ, (∀ l ∈ lo, l < t) ∧ (∀ u ∈ hi, t < u) := by
    rintro ⟨t, hlt, htu⟩
    refine hline t ⟨?_, ?_, ?_⟩
    · have he : g₀ (x + t • v) = g₀ x + t * g₀ v := by
        rw [map_add, map_smul, smul_eq_mul]
      rw [he]
      rcases lt_or_gt_of_ne hg0v with h | h
      · have hb := hmem_lo_of (Or.inl ⟨h, rfl⟩)
        have ht := hlt _ hb
        have e1 : (c₀ - g₀ x) / g₀ v * g₀ v = c₀ - g₀ x :=
          div_mul_cancel₀ _ hg0v
        have e2 : t * g₀ v < (c₀ - g₀ x) / g₀ v * g₀ v :=
          mul_lt_mul_of_neg_right ht h
        linarith
      · have hb := hmem_hi_of (Or.inl ⟨h, rfl⟩)
        have ht := htu _ hb
        have e1 : (c₀ - g₀ x) / g₀ v * g₀ v = c₀ - g₀ x :=
          div_mul_cancel₀ _ hg0v
        have e2 : t * g₀ v < (c₀ - g₀ x) / g₀ v * g₀ v :=
          mul_lt_mul_of_pos_right ht h
        linarith
    · have he : g₁ (x + t • v) = g₁ x + t * g₁ v := by
        rw [map_add, map_smul, smul_eq_mul]
      rw [he]
      rcases lt_or_gt_of_ne hg1v with h | h
      · have hb := hmem_hi_of (Or.inr (Or.inl ⟨h, rfl⟩))
        have ht := htu _ hb
        have e1 : (c₁ - g₁ x) / g₁ v * g₁ v = c₁ - g₁ x :=
          div_mul_cancel₀ _ hg1v
        have e2 : (c₁ - g₁ x) / g₁ v * g₁ v < t * g₁ v :=
          mul_lt_mul_of_neg_right ht h
        linarith
      · have hb := hmem_lo_of (Or.inr (Or.inl ⟨h, rfl⟩))
        have ht := hlt _ hb
        have e1 : (c₁ - g₁ x) / g₁ v * g₁ v = c₁ - g₁ x :=
          div_mul_cancel₀ _ hg1v
        have e2 : (c₁ - g₁ x) / g₁ v * g₁ v < t * g₁ v :=
          mul_lt_mul_of_pos_right ht h
        linarith
    · by_cases h2 : g₂ v = 0
      · have he : g₂ (x + t • v) = g₂ x + t * g₂ v := by
          rw [map_add, map_smul, smul_eq_mul]
        rw [he, h2, mul_zero, add_zero]
        exact hx2
      · have he : g₂ (x + t • v) = g₂ x + t * g₂ v := by
          rw [map_add, map_smul, smul_eq_mul]
        rw [he]
        rcases lt_or_gt_of_ne h2 with h | h
        · have hb := hmem_hi_of (Or.inr (Or.inr ⟨h, rfl⟩))
          have ht := htu _ hb
          have e1 : (c₂ - g₂ x) / g₂ v * g₂ v = c₂ - g₂ x :=
            div_mul_cancel₀ _ h2
          have e2 : (c₂ - g₂ x) / g₂ v * g₂ v < t * g₂ v :=
            mul_lt_mul_of_neg_right ht h
          linarith
        · have hb := hmem_lo_of (Or.inr (Or.inr ⟨h, rfl⟩))
          have ht := hlt _ hb
          have e1 : (c₂ - g₂ x) / g₂ v * g₂ v = c₂ - g₂ x :=
            div_mul_cancel₀ _ h2
          have e2 : (c₂ - g₂ x) / g₂ v * g₂ v < t * g₂ v :=
            mul_lt_mul_of_pos_right ht h
          linarith
  -- so some lower bound is at least some upper bound
  obtain ⟨l, hllo, u, huhi, hul⟩ : ∃ l ∈ lo, ∃ u ∈ hi, u ≤ l := by
    by_contra hcon
    push_neg at hcon
    exact hempty (exists_between_of_forall hcon)
  rcases hmem_lo hllo with ⟨h0n, rfl⟩ | ⟨h1p, rfl⟩ | ⟨h2p, rfl⟩
  · -- lower bound from facet 0
    rcases hmem_hi huhi with ⟨h0p, rfl⟩ | ⟨h1n, rfl⟩ | ⟨h2n, rfl⟩
    · linarith
    · exact finalize (ne_of_lt h0n) (ne_of_lt h1n) (LB0 h0n) (UB1 h1n) hul
        he01.2.1 he01.2.2 hm01 he01.1
    · exact finalize (ne_of_lt h0n) (ne_of_lt h2n) (LB0 h0n) (UB2 h2n) hul
        he02.2.1 he02.2.2 hm02 he02.1
  · -- lower bound from facet 1
    rcases hmem_hi huhi with ⟨h0p, rfl⟩ | ⟨h1n, rfl⟩ | ⟨h2n, rfl⟩
    · exact finalize (ne_of_gt h1p) (ne_of_gt h0p) (LB1 h1p) (UB0 h0p) hul
        he01.2.2 he01.2.1 hm01 he01.1
    · linarith
    · exact finalize (ne_of_gt h1p) (ne_of_lt h2n) (LB1 h1p) (UB2 h2n) hul
        he12.2.1 he12.2.2 hm12 he12.1
  · -- lower bound from facet 2
    rcases hmem_hi huhi with ⟨h0p, rfl⟩ | ⟨h1n, rfl⟩ | ⟨h2n, rfl⟩
    · exact finalize (ne_of_gt h2p) (ne_of_gt h0p) (LB2 h2p) (UB0 h0p) hul
        he02.2.2 he02.2.1 hm02 he02.1
    · exact finalize (ne_of_gt h2p) (ne_of_lt h1n) (LB2 h2p) (UB1 h1n) hul
        he12.2.2 he12.2.1 hm12 he12.1
    · linarith

/-- **The ≤3-halfspace separating-plane lemma.**  `C` is the open wedge cut
out by `{g₀ < c₀} ∩ {c₁ < g₁} ∩ {c₂ < g₂}`; `X` is a finite set in the
"opposite" wedge `{c₀ < g₀} ∩ {g₁ < c₁} ∩ {c₂ < g₂}` all of whose secant
lines miss `C`.  Then every pair `x ≠ y` of `X` admits a plane through them,
parallel to one of at most three fixed nonzero directions, with `C` strictly
on one side — the `hsep` hypothesis of `prop_2_1_poly` for the
Proposition 3.1 polytopes. -/
private lemma separates_poly3
    (C : Set (Euc 3)) {g₀ g₁ g₂ : Euc 3 →ₗ[ℝ] ℝ} {c₀ c₁ c₂ : ℝ}
    (hC : C = {z | g₀ z < c₀ ∧ c₁ < g₁ z ∧ c₂ < g₂ z})
    (hg₀ : g₀ ≠ 0) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    {X : Finset (Euc 3)}
    (hX : ∀ x ∈ X, c₀ < g₀ x ∧ g₁ x < c₁ ∧ c₂ < g₂ x)
    (hfree : FreeOf X C) :
    ∃ D : Finset (Euc 3), (∀ d ∈ D, d ≠ 0) ∧ D.card ≤ 3 ∧
      ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ∃ d ∈ D, ∃ H : Euc 3 →ₗ[ℝ] ℝ,
        H d = 0 ∧ H x = H y ∧ (∀ w ∈ C, H w < H x) ∧
          ∀ t : ℝ, x - y ≠ t • d := by
  classical
  have memC : ∀ w : Euc 3, w ∈ C →
      g₀ w < c₀ ∧ c₁ < g₁ w ∧ c₂ < g₂ w :=
    fun w hw ↦ by
      rw [hC] at hw
      exact hw
  by_cases hK : (LinearMap.ker g₀ ⊓ LinearMap.ker g₁ ⊓ LinearMap.ker g₂) = ⊥
  · -- ============ Case A: the three normals are independent ============
    obtain ⟨d₀₁, hd₀₁n, hd₀₁0, hd₀₁1⟩ := exists_mem_ker_ker g₀ g₁
    obtain ⟨d₀₂, hd₀₂n, hd₀₂0, hd₀₂2⟩ := exists_mem_ker_ker g₀ g₂
    obtain ⟨d₁₂, hd₁₂n, hd₁₂1, hd₁₂2⟩ := exists_mem_ker_ker g₁ g₂
    -- the edge directions are pairwise non-parallel (the common kernel is 0)
    have hnA : ∀ t : ℝ, d₀₂ ≠ t • d₀₁ := by
      intro t ht
      have hmem : d₀₂ ∈ LinearMap.ker g₁ := by
        rw [LinearMap.mem_ker, ht, map_smul, hd₀₁1, smul_zero]
      have hmemK : d₀₂ ∈
          LinearMap.ker g₀ ⊓ LinearMap.ker g₁ ⊓ LinearMap.ker g₂ :=
        Submodule.mem_inf.mpr
          ⟨Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr hd₀₂0, hmem⟩,
            LinearMap.mem_ker.mpr hd₀₂2⟩
      rw [hK, Submodule.mem_bot] at hmemK
      exact hd₀₂n hmemK
    have hnB : ∀ t : ℝ, d₁₂ ≠ t • d₀₁ := by
      intro t ht
      have hmem : d₁₂ ∈ LinearMap.ker g₀ := by
        rw [LinearMap.mem_ker, ht, map_smul, hd₀₁0, smul_zero]
      have hmemK : d₁₂ ∈
          LinearMap.ker g₀ ⊓ LinearMap.ker g₁ ⊓ LinearMap.ker g₂ :=
        Submodule.mem_inf.mpr
          ⟨Submodule.mem_inf.mpr ⟨hmem, LinearMap.mem_ker.mpr hd₁₂1⟩,
            LinearMap.mem_ker.mpr hd₁₂2⟩
      rw [hK, Submodule.mem_bot] at hmemK
      exact hd₁₂n hmemK
    refine ⟨{d₀₁, d₀₂, d₁₂}, ?_, ?_, ?_⟩
    · intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl <;> assumption
    · calc ({d₀₁, d₀₂, d₁₂} : Finset (Euc 3)).card
          ≤ ({d₀₂, d₁₂} : Finset (Euc 3)).card + 1 := Finset.card_insert_le _ _
        _ ≤ ({d₁₂} : Finset (Euc 3)).card + 1 + 1 :=
            add_le_add_right (Finset.card_insert_le _ _) 1
        _ = 3 := by simp
    · intro x hx y hy hxy
      obtain ⟨hx0, hx1, hx2⟩ := hX x hx
      set v := y - x with hvdef
      have hv : v ≠ 0 := by
        rw [hvdef, sub_ne_zero]
        exact Ne.symm hxy
      -- every point `x + t·v` lies on the secant line, hence outside `C`
      have hmem_aff : ∀ t : ℝ,
          x + t • v ∈ affineSpan ℝ ({x, y} : Set (Euc 3)) := by
        intro t
        have he : x + t • v = AffineMap.lineMap x y t := by
          rw [hvdef, AffineMap.lineMap_apply_module']
          exact add_comm _ _
        rw [he]
        exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
      have hline : ∀ t : ℝ,
          ¬ (g₀ (x + t • v) < c₀ ∧ c₁ < g₁ (x + t • v) ∧
            c₂ < g₂ (x + t • v)) := by
        intro t h
        have hwC : x + t • v ∈ C := by
          rw [hC]
          exact ⟨h.1, h.2.1, h.2.2⟩
        exact hfree x hx y hy hxy _ (hmem_aff t) hwC
      -- facet membership of the directions in `D`
      have m0 : d₀₁ ∈ ({d₀₁, d₀₂, d₁₂} : Finset (Euc 3)) :=
        Finset.mem_insert_self _ _
      have m1 : d₀₂ ∈ ({d₀₁, d₀₂, d₁₂} : Finset (Euc 3)) :=
        Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
      have m2 : d₁₂ ∈ ({d₀₁, d₀₂, d₁₂} : Finset (Euc 3)) :=
        Finset.mem_insert_of_mem
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
      by_cases h0 : g₀ v = 0
      · -- easy case: the line is parallel to facet 0's boundary plane
        have hxy0 : g₀ x = g₀ y := by
          have h' : g₀ v = g₀ y - g₀ x := by rw [hvdef, map_sub]
          linarith
        have hsep0 : ∀ w ∈ C, g₀ w < g₀ x :=
          fun w hw ↦ lt_trans (memC w hw).1 hx0
        by_cases hp : ∀ t : ℝ, x - y ≠ t • d₀₁
        · exact ⟨d₀₁, m0, g₀, hd₀₁0, hxy0, hsep0, hp⟩
        · push_neg at hp
          obtain ⟨t, ht⟩ := hp
          have hpar : ∀ s : ℝ, x - y ≠ s • d₀₂ := by
            intro s hs
            have hs0 : s ≠ 0 := by
              intro h
              rw [h, zero_smul] at hs
              exact hv (by rw [hvdef, sub_eq_zero]; exact
                (sub_eq_zero.mp hs).symm)
            have hst : s • d₀₂ = t • d₀₁ := hs.symm.trans ht
            have he : d₀₂ = (t / s) • d₀₁ := by
              calc d₀₂ = s⁻¹ • (s • d₀₂) := (inv_smul_smul₀ hs0 _).symm
                _ = s⁻¹ • (t • d₀₁) := by rw [hst]
                _ = (t / s) • d₀₁ := by
                    rw [smul_smul, div_eq_mul_inv, mul_comm]
            exact hnA (t / s) he
          exact ⟨d₀₂, m1, g₀, hd₀₂0, hxy0, hsep0, hpar⟩
      · by_cases h1 : g₁ v = 0
        · -- easy case: the line is parallel to facet 1's boundary plane
          have hxy1 : g₁ x = g₁ y := by
            have h' : g₁ v = g₁ y - g₁ x := by rw [hvdef, map_sub]
            linarith
          have hsep1 : ∀ w ∈ C, (-g₁) w < (-g₁) x := by
            intro w hw
            obtain ⟨-, hw1, -⟩ := memC w hw
            simp only [LinearMap.neg_apply]
            linarith
          by_cases hp : ∀ t : ℝ, x - y ≠ t • d₀₁
          · exact ⟨d₀₁, m0, -g₁, by simp [hd₀₁1], by simp [hxy1], hsep1, hp⟩
          · push_neg at hp
            obtain ⟨t, ht⟩ := hp
            have hpar : ∀ s : ℝ, x - y ≠ s • d₁₂ := by
              intro s hs
              have hs0 : s ≠ 0 := by
                intro h
                rw [h, zero_smul] at hs
                exact hv (by rw [hvdef, sub_eq_zero]; exact
                  (sub_eq_zero.mp hs).symm)
              have hst : s • d₁₂ = t • d₀₁ := hs.symm.trans ht
              have he : d₁₂ = (t / s) • d₀₁ := by
                calc d₁₂ = s⁻¹ • (s • d₁₂) := (inv_smul_smul₀ hs0 _).symm
                  _ = s⁻¹ • (t • d₀₁) := by rw [hst]
                  _ = (t / s) • d₀₁ := by
                      rw [smul_smul, div_eq_mul_inv, mul_comm]
              exact hnB (t / s) he
            exact ⟨d₁₂, m2, -g₁, by simp [hd₁₂1], by simp [hxy1], hsep1, hpar⟩
        · -- hard case: bound analysis on the line parameter
          exact sep_hard_case C hC hx2 hvdef hv hline h0 h1
            ⟨hd₀₁n, hd₀₁0, hd₀₁1⟩ ⟨hd₀₂n, hd₀₂0, hd₀₂2⟩
            ⟨hd₁₂n, hd₁₂1, hd₁₂2⟩ m0 m1 m2
  · -- ======== Case B: dependent normals, common kernel direction `e` ========
    obtain ⟨e, heK, he0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
    have he0k : g₀ e = 0 := by
      have h := (Submodule.mem_inf.mp heK).1
      rw [Submodule.mem_inf] at h
      exact LinearMap.mem_ker.mp h.1
    have he1k : g₁ e = 0 := by
      have h := (Submodule.mem_inf.mp heK).1
      rw [Submodule.mem_inf] at h
      exact LinearMap.mem_ker.mp h.2
    have he2k : g₂ e = 0 :=
      LinearMap.mem_ker.mp (Submodule.mem_inf.mp heK).2
    -- `ker g₀` is two-dimensional (g₀ ≠ 0); complete `{e}` to a basis
    have hker0 : Module.finrank ℝ (LinearMap.ker g₀) = 2 := by
      have h1 := LinearMap.finrank_range_add_finrank_ker g₀
      have h2 : LinearMap.range g₀ = ⊤ := by
        rw [LinearMap.range_eq_top]
        intro z
        obtain ⟨v0, hv0⟩ : ∃ v0, g₀ v0 ≠ 0 := by
          by_contra h
          push_neg at h
          exact hg₀ (LinearMap.ext h)
        exact ⟨(z / g₀ v0) • v0, by
          rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv0]⟩
      have h3 : Module.finrank ℝ (Euc 3) = 3 := finrank_euclideanSpace_fin
      rw [h2, finrank_top, finrank_self, h3] at h1
      omega
    have hlt : Submodule.span ℝ {e} < LinearMap.ker g₀ := by
      refine lt_of_le_of_ne ?_ ?_
      · rw [Submodule.span_singleton_le_iff_mem]
        exact LinearMap.mem_ker.mpr he0k
      · intro h
        have h1 : Module.finrank ℝ (Submodule.span ℝ {e}) = 2 := by
          rw [h, hker0]
        have h2 : Module.finrank ℝ (Submodule.span ℝ {e}) = 1 :=
          finrank_span_singleton he0
        omega
    obtain ⟨f₀, hf₀k, hf₀e⟩ := SetLike.exists_of_lt hlt
    have hf₀0 : f₀ ≠ 0 := fun h ↦ hf₀e (h.symm ▸ Submodule.zero_mem _)
    have hf₀k' : g₀ f₀ = 0 := LinearMap.mem_ker.mp hf₀k
    -- `f₀` is not parallel to `e`
    have hnf : ∀ t : ℝ, f₀ ≠ t • e := fun t ht ↦
      hf₀e (ht.symm ▸
        Submodule.smul_mem _ t (Submodule.mem_span_singleton_self e))
    refine ⟨{e, f₀}, ?_, ?_, ?_⟩
    · intro d hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl <;> assumption
    · calc ({e, f₀} : Finset (Euc 3)).card
          ≤ ({f₀} : Finset (Euc 3)).card + 1 := Finset.card_insert_le _ _
        _ = 2 := by simp
        _ ≤ 3 := by norm_num
    · intro x hx y hy hxy
      obtain ⟨hx0, hx1, hx2⟩ := hX x hx
      set v := y - x with hvdef
      have hv : v ≠ 0 := by
        rw [hvdef, sub_ne_zero]
        exact Ne.symm hxy
      have hmem_aff : ∀ t : ℝ,
          x + t • v ∈ affineSpan ℝ ({x, y} : Set (Euc 3)) := by
        intro t
        have he : x + t • v = AffineMap.lineMap x y t := by
          rw [hvdef, AffineMap.lineMap_apply_module']
          exact add_comm _ _
        rw [he]
        exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
      have hline : ∀ t : ℝ,
          ¬ (g₀ (x + t • v) < c₀ ∧ c₁ < g₁ (x + t • v) ∧
            c₂ < g₂ (x + t • v)) := by
        intro t h
        have hwC : x + t • v ∈ C := by
          rw [hC]
          exact ⟨h.1, h.2.1, h.2.2⟩
        exact hfree x hx y hy hxy _ (hmem_aff t) hwC
      have me : e ∈ ({e, f₀} : Finset (Euc 3)) :=
        Finset.mem_insert_self _ _
      have mf : f₀ ∈ ({e, f₀} : Finset (Euc 3)) :=
        Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      by_cases hve : v ∈ Submodule.span ℝ {e}
      · -- the secant line is parallel to `e`, hence to every facet plane
        obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hve
        have hs0 : s ≠ 0 := fun h ↦ hv (by rw [← hs, h, zero_smul])
        have hg0v : g₀ v = 0 := by rw [← hs, map_smul, he0k, smul_zero]
        have hxy0 : g₀ x = g₀ y := by
          have h' : g₀ v = g₀ y - g₀ x := by rw [hvdef, map_sub]
          linarith
        have hsep0 : ∀ w ∈ C, g₀ w < g₀ x :=
          fun w hw ↦ lt_trans (memC w hw).1 hx0
        have hpar : ∀ t : ℝ, x - y ≠ t • f₀ := by
          intro t ht
          have ht0 : t ≠ 0 := by
            intro h
            rw [h, zero_smul] at ht
            exact hxy (sub_eq_zero.mp ht)
          have hneg : x - y = (-s) • e := by
            have hs' : s • e = y - x := by rw [hs, hvdef]
            rw [← neg_sub, ← hs', neg_smul]
          have hef : t • f₀ = (-s) • e := ht.symm.trans hneg
          have hef' : f₀ = (-s / t) • e := by
            calc f₀ = t⁻¹ • (t • f₀) := (inv_smul_smul₀ ht0 _).symm
              _ = t⁻¹ • ((-s) • e) := by rw [hef]
              _ = (-s / t) • e := by
                  rw [smul_smul]
                  congr 1
                  rw [mul_comm, div_eq_mul_inv]
          exact hnf _ hef'
        exact ⟨f₀, mf, g₀, hf₀k', hxy0, hsep0, hpar⟩
      · -- `v` is not parallel to `e`
        have hp_e : ∀ t : ℝ, x - y ≠ t • e := by
          intro t ht
          apply hve
          rw [Submodule.mem_span_singleton]
          exact ⟨-t, by rw [neg_smul, ht, neg_sub, ← hvdef]⟩
        by_cases h0 : g₀ v = 0
        · have hxy0 : g₀ x = g₀ y := by
            have h' : g₀ v = g₀ y - g₀ x := by rw [hvdef, map_sub]
            linarith
          have hsep0 : ∀ w ∈ C, g₀ w < g₀ x :=
            fun w hw ↦ lt_trans (memC w hw).1 hx0
          exact ⟨e, me, g₀, he0k, hxy0, hsep0, hp_e⟩
        · by_cases h1 : g₁ v = 0
          · have hxy1 : g₁ x = g₁ y := by
              have h' : g₁ v = g₁ y - g₁ x := by rw [hvdef, map_sub]
              linarith
            have hsep1 : ∀ w ∈ C, (-g₁) w < (-g₁) x := by
              intro w hw
              obtain ⟨-, hw1, -⟩ := memC w hw
              simp only [LinearMap.neg_apply]
              linarith
            exact ⟨e, me, -g₁, by simp [he1k], by simp [hxy1], hsep1, hp_e⟩
          · exact sep_hard_case C hC hx2 hvdef hv hline h0 h1
              ⟨he0, he0k, he1k⟩ ⟨he0, he0k, he2k⟩ ⟨he0, he1k, he2k⟩
              me me me

end SeparationPolytope

section Section3Wedges

/-- `x ≺ y` relative to a region `P`: `x ≠ y` and `x` lies on a segment from
`y` into `P` — the partial order used on the middle block in §3, where
`P`-free sets are exactly the `≺`-antichains. -/
private def precRel (P : Set (Euc 3)) (x y : Euc 3) : Prop :=
  x ≠ y ∧ ∃ p ∈ P, x ∈ segment ℝ y p

private lemma precRel_irrefl (P : Set (Euc 3)) : ∀ x : Euc 3, ¬ precRel P x x :=
  fun _ h ↦ h.1 rfl

/-- A point of `affineSpan {x,y}` is an affine combination of `x,y`. -/
private lemma mem_affineSpan_pair_eq {x y w : Euc 3}
    (hw : w ∈ affineSpan ℝ ({x, y} : Set (Euc 3))) :
    ∃ s : ℝ, w = (1 - s) • x + s • y := by
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hw
  obtain ⟨t, ht⟩ := hw
  exact ⟨t, by rw [AffineMap.lineMap_apply_module] at ht; rw [← ht]; abel⟩

/-- The `precRel` relation is transitive on points strictly on the `g > c`
side, provided `P` is a convex region strictly on the `g < c` side. -/
private lemma precRel_trans {P : Set (Euc 3)} (hP : Convex ℝ P)
    {g : Euc 3 →ₗ[ℝ] ℝ} {c : ℝ} (hPside : ∀ w ∈ P, g w < c)
    {x y z : Euc 3} (hx : c < g x) (hz : c < g z)
    (hxy : precRel P x y) (hyz : precRel P y z) : precRel P x z := by
  obtain ⟨hxyne, p, hpP, hxseg⟩ := hxy
  obtain ⟨hyzne, q, hqP, hyseg⟩ := hyz
  -- `y ∈ convexHull({z} ∪ P)` since `y ∈ segment z q`.
  have hyhull : y ∈ convexHull ℝ (({z} : Set (Euc 3)) ∪ P) := by
    refine segment_subset_convexHull ?_ ?_ hyseg
    · exact Set.subset_union_left (Set.mem_singleton _)
    · exact Set.subset_union_right hqP
  -- hence `{y} ∪ P ⊆ conv({z} ∪ P)` and so `x ∈ conv({z} ∪ P)`.
  have hsub : ({y} : Set (Euc 3)) ∪ P ⊆ convexHull ℝ (({z} : Set (Euc 3)) ∪ P) := by
    rintro w (rfl | hw)
    · exact hyhull
    · exact subset_convexHull ℝ _ (Set.subset_union_right hw)
  have hxhull : x ∈ convexHull ℝ (({z} : Set (Euc 3)) ∪ P) := by
    have : ({y} : Set (Euc 3)) ∪ P ⊆ _ := hsub
    have hmem : x ∈ convexHull ℝ (({y} : Set (Euc 3)) ∪ P) :=
      segment_subset_convexHull (Set.subset_union_left (Set.mem_singleton _))
        (Set.subset_union_right hpP) hxseg
    exact convexHull_min this (convex_convexHull ℝ _) hmem
  -- `conv({z} ∪ P) = convexJoin {z} P = ⋃_{p'∈P} segment z p'`.
  have hPne : P.Nonempty := ⟨p, hpP⟩
  rw [(convex_singleton z).convexHull_union hP (Set.singleton_nonempty z) hPne,
    mem_convexJoin] at hxhull
  obtain ⟨a, ha, p', hp'P, hxseg'⟩ := hxhull
  rw [Set.mem_singleton_iff] at ha
  rw [ha] at hxseg'
  refine ⟨?_, p', hp'P, hxseg'⟩
  -- `x ≠ z`: otherwise `x = (1-u)y + u•p` and `y = (1-s)x + s•q` give
  -- `(u+s-us)·g x < (u+s-us)·c`, contradicting `c < g x`.
  intro hxz
  rw [segment_eq_image] at hxseg hyseg
  obtain ⟨u, ⟨hu0, hu1⟩, hux⟩ := hxseg
  obtain ⟨s, ⟨hs0, hs1⟩, hsy⟩ := hyseg
  rw [← hxz] at hsy hyzne
  have hu : u ≠ 0 := fun h ↦ hxyne (by
    rw [h] at hux; simpa using hux.symm)
  have hs : s ≠ 0 := fun h ↦ hyzne (by
    rw [h] at hsy; simpa using hsy.symm)
  have hu' : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
  have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
  have hgx : g x = (1 - u) * g y + u * g p := by
    have e := congrArg g hux
    simp only [map_add, map_smul, smul_eq_mul] at e
    linarith
  have hgy : g y = (1 - s) * g x + s * g q := by
    have e := congrArg g hsy
    simp only [map_add, map_smul, smul_eq_mul] at e
    linarith
  have hD : 0 < u + s - u * s := by
    have heq : u + s - u * s = u * (1 - s) + s := by ring
    rw [heq]
    exact add_pos_of_nonneg_of_pos (mul_nonneg hu'.le (sub_nonneg.mpr hs1)) hs'
  have hkey : g x * (u + s - u * s) = (1 - u) * s * g q + u * g p := by
    linear_combination hgx + (1 - u) * hgy
  have hlt : g x * (u + s - u * s) < c * (u + s - u * s) := by
    rw [hkey]
    calc (1 - u) * s * g q + u * g p
        < (1 - u) * s * c + u * c :=
          add_lt_add_of_le_of_lt
            (mul_le_mul_of_nonneg_left (hPside q hqP).le
              (mul_nonneg (sub_nonneg.mpr hu1) hs'.le))
            (mul_lt_mul_of_pos_left (hPside p hpP) hu')
      _ = c * (u + s - u * s) := by ring
  have hgc : g x < c := (mul_lt_mul_right hD).mp hlt
  linarith
/-- Cancellation of a nonzero scalar in a real vector space. -/
private lemma eq_of_smul_ne_zero {d : ℝ} (hd : d ≠ 0) {v w : Euc 3}
    (h : d • v = d • w) : v = w := by
  have h2 := congrArg (d⁻¹ • ·) h
  rwa [inv_smul_smul₀ hd, inv_smul_smul₀ hd] at h2

/-- If `w = (1 - s) • x + s • y` with `s < 0` then `x ∈ segment y w`. -/
private lemma mem_segment_of_neg {x y w : Euc 3} {s : ℝ} (hs : s < 0)
    (hsdef : w = (1 - s) • x + s • y) : x ∈ segment ℝ y w := by
  rw [segment_eq_image]
  have h1s : (0 : ℝ) < 1 - s := by linarith
  have hd : (1 - s : ℝ) ≠ 0 := h1s.ne'
  refine ⟨1 / (1 - s), ⟨div_nonneg zero_le_one h1s.le, ?_⟩, ?_⟩
  · rw [div_le_one h1s]; linarith
  · apply eq_of_smul_ne_zero hd
    simp only [smul_add, smul_smul]
    have e1 : (1 - s) * (1 - 1 / (1 - s)) = -s := by
      rw [mul_sub, mul_one, one_div, mul_inv_cancel₀ hd]; ring
    have e2 : (1 - s) * (1 / (1 - s)) = 1 := by
      rw [one_div, mul_inv_cancel₀ hd]
    rw [e1, e2, one_smul, hsdef]
    module

/-- If `w = (1 - s) • x + s • y` with `s > 1` then `y ∈ segment x w`. -/
private lemma mem_segment_of_gt {x y w : Euc 3} {s : ℝ} (hs : 1 < s)
    (hsdef : w = (1 - s) • x + s • y) : y ∈ segment ℝ x w := by
  rw [segment_eq_image]
  have hsp : (0 : ℝ) < s := by linarith
  have hd : (s : ℝ) ≠ 0 := hsp.ne'
  refine ⟨1 / s, ⟨div_nonneg zero_le_one hsp.le, ?_⟩, ?_⟩
  · rw [div_le_one hsp]; linarith
  · apply eq_of_smul_ne_zero hd
    simp only [smul_add, smul_smul]
    have e1 : s * (1 - 1 / s) = s - 1 := by
      rw [mul_sub, mul_one, one_div, mul_inv_cancel₀ hd]
    have e2 : s * (1 / s) = 1 := by
      rw [one_div, mul_inv_cancel₀ hd]
    rw [e1, e2, one_smul, hsdef]
    module

/-- Collinear-combination step: if `(1-t)•y + t•w = (1-u)•y + u•p` with `w`
on the `P²` side (`g₁w < c₁`, `g₂w < c₂`) and `p` on the `P¹` side
(`c₁ < g₁p`, `c₂ < g₂p`), then either `w = p` or `y` violates one of its
side constraints. -/
private lemma wedge_collinear {y w p : Euc 3} {t u : ℝ}
    {g₁ g₂ : Euc 3 →ₗ[ℝ] ℝ} {c₁ c₂ : ℝ}
    (ht : 0 < t) (hu : 0 < u)
    (h3 : (1 - t) • y + t • w = (1 - u) • y + u • p)
    (hw1 : g₁ w < c₁) (hw2 : g₂ w < c₂) (hp1 : c₁ < g₁ p) (hp2 : c₂ < g₂ p) :
    c₁ < g₁ y ∨ g₂ y < c₂ ∨ w = p := by
  rcases lt_trichotomy t u with htu | htu | htu
  · -- `t < u`: `(u-t)·g₁y = u·g₁p - t·g₁w > (u-t)·c₁`.
    have e := congrArg g₁ h3
    simp only [map_add, map_smul, smul_eq_mul] at e
    have key : (u - t) * g₁ y = u * g₁ p - t * g₁ w := by linear_combination e
    have hlt : (u - t) * c₁ < (u - t) * g₁ y := by
      calc (u - t) * c₁ = u * c₁ - t * c₁ := by ring
        _ < u * g₁ p - t * g₁ w :=
            sub_lt_sub (mul_lt_mul_of_pos_left hp1 hu) (mul_lt_mul_of_pos_left hw1 ht)
        _ = (u - t) * g₁ y := key.symm
    exact Or.inl ((mul_lt_mul_left (sub_pos.mpr htu)).mp hlt)
  · -- `t = u`: `t•w = t•p`, hence `w = p`.
    rw [← htu] at h3
    exact Or.inr (Or.inr (eq_of_smul_ne_zero ht.ne' (add_left_cancel_iff.mp h3)))
  · -- `t > u`: `(t-u)·g₂y = t·g₂w - u·g₂p < (t-u)·c₂`.
    have e := congrArg g₂ h3
    simp only [map_add, map_smul, smul_eq_mul] at e
    have key : (t - u) * g₂ y = t * g₂ w - u * g₂ p := by linear_combination -e
    have hlt : (t - u) * g₂ y < (t - u) * c₂ := by
      calc (t - u) * g₂ y = t * g₂ w - u * g₂ p := key
        _ < t * c₂ - u * c₂ :=
            sub_lt_sub (mul_lt_mul_of_pos_left hw2 ht) (mul_lt_mul_of_pos_left hp2 hu)
        _ = (t - u) * c₂ := by ring
    exact Or.inr (Or.inl ((mul_lt_mul_left (sub_pos.mpr htu)).mp hlt))

/-- Convex-combination step: if `b = (1-v)•a + v•p` and `a = (1-t)•b + t•w`
with `v,t ∈ (0,1]`, then `b` is a convex combination of `w,p`; applied to
`g₀` with `g₀w < c₀`, `g₀p < c₀` this gives `g₀b < c₀`. -/
private lemma wedge_conv_comb {a b w p : Euc 3} {v t : ℝ}
    {g₀ : Euc 3 →ₗ[ℝ] ℝ} {c₀ : ℝ}
    (hv : 0 < v) (hv1 : v ≤ 1) (ht : 0 < t) (ht1 : t ≤ 1)
    (hvseg : (1 - v) • a + v • p = b) (htseg : (1 - t) • b + t • w = a)
    (hw0 : g₀ w < c₀) (hp0 : g₀ p < c₀) : g₀ b < c₀ := by
  have e1 := congrArg g₀ hvseg
  have e2 := congrArg g₀ htseg
  simp only [map_add, map_smul, smul_eq_mul] at e1 e2
  have hD : (0:ℝ) < v + t - v * t := by
    have heq : v + t - v * t = v * (1 - t) + t := by ring
    rw [heq]
    exact add_pos_of_nonneg_of_pos (mul_nonneg hv.le (sub_nonneg.mpr ht1)) ht
  have key : (v + t - v * t) * g₀ b = (1 - v) * t * g₀ w + v * g₀ p := by
    linear_combination -e1 - (1 - v) * e2
  have hle : (1 - v) * t * g₀ w ≤ (1 - v) * t * c₀ :=
    mul_le_mul_of_nonneg_left hw0.le (mul_nonneg (sub_nonneg.mpr hv1) ht.le)
  have hlt : v * g₀ p < v * c₀ := mul_lt_mul_of_pos_left hp0 hv
  have hb : (v + t - v * t) * g₀ b < (v + t - v * t) * c₀ := by
    calc (v + t - v * t) * g₀ b = (1 - v) * t * g₀ w + v * g₀ p := key
      _ < (1 - v) * t * c₀ + v * c₀ := add_lt_add_of_le_of_lt hle hlt
      _ = (v + t - v * t) * c₀ := by ring
  exact (mul_lt_mul_left hD).mp hb

/-- An antichain in the `≺_P` order inside the `g > c` region is `P`-free
when `P ⊆ {g < c}`: a point of `P` on the secant line `xy` lies either on
segment `xy` (contradicting `g > c` at both ends) or beyond `x`/`y`
(producing a `≺`-comparison). -/
private lemma freeOf_of_antichain {P : Set (Euc 3)}
    {g : Euc 3 →ₗ[ℝ] ℝ} {c : ℝ} (hPside : ∀ w ∈ P, g w < c)
    {A : Finset (Euc 3)} (hA : ∀ x ∈ A, c < g x)
    (hanti : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ¬ precRel P x y ∧ ¬ precRel P y x) :
    FreeOf A P := by
  intro x hx y hy hxy w hwaff hwP
  obtain ⟨s, hsdef⟩ := mem_affineSpan_pair_eq hwaff
  rcases lt_trichotomy s 0 with hs | hs | hs
  · -- `s < 0`: `x ∈ segment y w` ⇒ `x ≺ y`.
    exact (hanti x hx y hy hxy).1 ⟨hxy, w, hwP, mem_segment_of_neg hs hsdef⟩
  · -- `s = 0`: `w = x`.
    subst hs
    simp at hsdef
    rw [hsdef] at hwP
    linarith [hPside x hwP, hA x hx]
  · rcases lt_trichotomy s 1 with hs1 | hs1 | hs1
    · -- `0 < s < 1`: `w` is a strict convex combination ⇒ `g w > c`.
      have hgw : g w = (1 - s) * g x + s * g y := by
        rw [hsdef]; simp [map_add, map_smul, smul_eq_mul]
      have hgc : c < g w := by
        rw [hgw]
        have e1 : (0:ℝ) < (1 - s) * (g x - c) :=
          mul_pos (sub_pos.mpr hs1) (sub_pos.mpr (hA x hx))
        have e2 : (0:ℝ) < s * (g y - c) := mul_pos hs (sub_pos.mpr (hA y hy))
        nlinarith
      exact absurd (hPside w hwP) (not_lt.mpr hgc.le)
    · -- `s = 1`: `w = y`.
      subst hs1
      simp at hsdef
      rw [hsdef] at hwP
      linarith [hPside y hwP, hA y hy]
    · -- `s > 1`: `y ∈ segment x w` ⇒ `y ≺ x`.
      exact (hanti x hx y hy hxy).2 ⟨Ne.symm hxy, w, hwP, mem_segment_of_gt hs1 hsdef⟩

/-- A `≺_{P¹}`-chain in the `{g₀>c₀, g₁<c₁, g₂>c₂}` region is `P²`-free,
where `P¹ = {g₀<c₀, c₁<g₁, c₂<g₂}` and `P² = {g₀<c₀, g₁<c₁, g₂<c₂}`: a point
of `P²` on a secant line `xy` either lies on `segment x y` (contradicting
`g₀ > c₀` at both ends) or yields a `≺`-comparison that contradicts one of
the `g₁`/`g₂` side constraints. -/
private lemma freeOf_of_chain
    {g₀ g₁ g₂ : Euc 3 →ₗ[ℝ] ℝ} {c₀ c₁ c₂ : ℝ} {A : Finset (Euc 3)}
    (hA : ∀ x ∈ A, c₀ < g₀ x ∧ g₁ x < c₁ ∧ c₂ < g₂ x)
    (hchain : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      precRel {z : Euc 3 | g₀ z < c₀ ∧ c₁ < g₁ z ∧ c₂ < g₂ z} x y ∨
      precRel {z : Euc 3 | g₀ z < c₀ ∧ c₁ < g₁ z ∧ c₂ < g₂ z} y x) :
    FreeOf A {z : Euc 3 | g₀ z < c₀ ∧ g₁ z < c₁ ∧ g₂ z < c₂} := by
  intro x hx y hy hxy w hwaff hwP
  obtain ⟨hx0, hx1, hx2⟩ := hA x hx
  obtain ⟨hy0, hy1, hy2⟩ := hA y hy
  obtain ⟨hw0, hw1, hw2⟩ := hwP
  obtain ⟨s, hsdef⟩ := mem_affineSpan_pair_eq hwaff
  rcases lt_trichotomy s 0 with hs | hs | hs
  · -- `s < 0`: `x` lies on segment `y w`.
    have hxw : x ∈ segment ℝ y w := mem_segment_of_neg hs hsdef
    rw [segment_eq_image] at hxw
    obtain ⟨t, ⟨ht0, ht1⟩, htw⟩ := hxw
    have ht' : 0 < t := lt_of_le_of_ne ht0 (fun h ↦ hxy (by
      rw [← h] at htw; simpa using htw.symm))
    rcases hchain x hx y hy hxy with ⟨-, p, hpP, hxseg⟩ | ⟨-, p, hpP, hyseg⟩
    · -- `x ≺ y`: `x ∈ segment y p`, `p ∈ P¹` — collinear analysis.
      obtain ⟨hp0, hp1, hp2⟩ := hpP
      rw [segment_eq_image] at hxseg
      obtain ⟨u, ⟨hu0, hu1⟩, hux⟩ := hxseg
      have hu' : 0 < u := lt_of_le_of_ne hu0 (fun h ↦ hxy (by
        rw [← h] at hux; simpa using hux.symm))
      have h3 : (1 - t) • y + t • w = (1 - u) • y + u • p := htw.trans hux.symm
      rcases wedge_collinear ht' hu' h3 hw1 hw2 hp1 hp2 with h | h | h
      · linarith
      · linarith
      · rw [h] at hw1; linarith
    · -- `y ≺ x`: `y ∈ segment x p`, `p ∈ P¹` — convex combination in `g₀`.
      obtain ⟨hp0, -, -⟩ := hpP
      rw [segment_eq_image] at hyseg
      obtain ⟨v, ⟨hv0, hv1⟩, hvy⟩ := hyseg
      have hv' : 0 < v := lt_of_le_of_ne hv0 (fun h ↦ hxy (by
        rw [← h] at hvy; simpa using hvy))
      exact absurd (wedge_conv_comb hv' hv1 ht' ht1 hvy htw hw0 hp0)
        (not_lt.mpr hy0.le)
  · -- `s = 0`: `w = x`.
    subst hs
    simp at hsdef
    rw [hsdef] at hw0
    linarith
  · -- `s > 0`
    rcases lt_trichotomy s 1 with hs1 | hs1 | hs1
    · -- `0 < s < 1`: strict convex combination ⇒ `g₀ w > c₀`.
      have hgw : g₀ w = (1 - s) * g₀ x + s * g₀ y := by
        rw [hsdef]; simp [map_add, map_smul, smul_eq_mul]
      have hgc : c₀ < g₀ w := by
        rw [hgw]
        have e1 : (0:ℝ) < (1 - s) * (g₀ x - c₀) :=
          mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hx0)
        have e2 : (0:ℝ) < s * (g₀ y - c₀) := mul_pos hs (sub_pos.mpr hy0)
        nlinarith
      linarith
    · -- `s = 1`: `w = y`.
      subst hs1
      simp at hsdef
      rw [hsdef] at hw0
      linarith
    · -- `s > 1`: `y` lies on segment `x w`.
      have hyw : y ∈ segment ℝ x w := mem_segment_of_gt hs1 hsdef
      rw [segment_eq_image] at hyw
      obtain ⟨t, ⟨ht0, ht1⟩, htw⟩ := hyw
      have ht' : 0 < t := lt_of_le_of_ne ht0 (fun h ↦ hxy (by
        rw [← h] at htw; simpa using htw))
      rcases hchain x hx y hy hxy with ⟨-, p, hpP, hxseg⟩ | ⟨-, p, hpP, hyseg⟩
      · -- `x ≺ y`: `x ∈ segment y p` — convex combination in `g₀`.
        obtain ⟨hp0, -, -⟩ := hpP
        rw [segment_eq_image] at hxseg
        obtain ⟨v, ⟨hv0, hv1⟩, hvx⟩ := hxseg
        have hv' : 0 < v := lt_of_le_of_ne hv0 (fun h ↦ hxy (by
          rw [← h] at hvx; simpa using hvx.symm))
        exact absurd (wedge_conv_comb hv' hv1 ht' ht1 hvx htw hw0 hp0)
          (not_lt.mpr hx0.le)
      · -- `y ≺ x`: `y ∈ segment x p` — collinear analysis.
        obtain ⟨hp0, hp1, hp2⟩ := hpP
        rw [segment_eq_image] at hyseg
        obtain ⟨u, ⟨hu0, hu1⟩, huy⟩ := hyseg
        have hu' : 0 < u := lt_of_le_of_ne hu0 (fun h ↦ hxy (by
          rw [← h] at huy; simpa using huy))
        have h3 : (1 - t) • x + t • w = (1 - u) • x + u • p := htw.trans huy.symm
        rcases wedge_collinear ht' hu' h3 hw1 hw2 hp1 hp2 with h | h | h
        · linarith
        · linarith
        · rw [h] at hw1; linarith

/-! ### §3 assembly -/

/-- A sorted three-element finset determines its elements. -/
private lemma sorted_triple_inj {K : ℕ} {a b c d e f : Fin K}
    (hab : a < b) (hbc : b < c) (hde : d < e) (hef : e < f)
    (h : ({a, b, c} : Finset (Fin K)) = {d, e, f}) :
    a = d ∧ b = e ∧ c = f := by
  have hmem : ∀ x : Fin K,
      x ∈ ({a, b, c} : Finset (Fin K)) ↔ x = a ∨ x = b ∨ x = c := by
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton]
  have hmem' : ∀ x : Fin K,
      x ∈ ({d, e, f} : Finset (Fin K)) ↔ x = d ∨ x = e ∨ x = f := by
    intro x
    simp only [Finset.mem_insert, Finset.mem_singleton]
  have hamin : ∀ x ∈ ({a, b, c} : Finset (Fin K)), a ≤ x := by
    intro x hx
    rcases (hmem x).mp hx with rfl | rfl | rfl
    · exact le_rfl
    · exact hab.le
    · exact (hab.trans hbc).le
  have hdmin : ∀ x ∈ ({d, e, f} : Finset (Fin K)), d ≤ x := by
    intro x hx
    rcases (hmem' x).mp hx with rfl | rfl | rfl
    · exact le_rfl
    · exact hde.le
    · exact (hde.trans hef).le
  have had : a = d :=
    le_antisymm (hdmin a (h ▸ Finset.mem_insert_self a _))
      (hamin d (h.symm ▸ Finset.mem_insert_self d _))
  have hcmax : ∀ x ∈ ({a, b, c} : Finset (Fin K)), x ≤ c := by
    intro x hx
    rcases (hmem x).mp hx with rfl | rfl | rfl
    · exact (hab.trans hbc).le
    · exact hbc.le
    · exact le_rfl
  have hfmax : ∀ x ∈ ({d, e, f} : Finset (Fin K)), x ≤ f := by
    intro x hx
    rcases (hmem' x).mp hx with rfl | rfl | rfl
    · exact (hde.trans hef).le
    · exact hef.le
    · exact le_rfl
  have hcf : c = f :=
    le_antisymm
      (hfmax c (h ▸ Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))))))
      (hcmax f (h.symm ▸ Finset.mem_insert.mpr
        (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self _))))))
  refine ⟨had, ?_, hcf⟩
  have hbm : b ∈ ({d, e, f} : Finset (Fin K)) :=
    h ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_insert_self _ _))
  rw [hmem'] at hbm
  rcases hbm with h1 | h1 | h1
  · exact absurd (h1 ▸ had ▸ hab) (lt_irrefl d)
  · exact h1
  · exact absurd (h1 ▸ hcf ▸ hbc) (lt_irrefl f)

/-- The `P¹` region `{g₀ < c₀, c₁ < g₁, c₂ < g₂}` is convex. -/
private lemma convex_halfspaces₁ {g₀ g₁ g₂ : Euc 3 →ₗ[ℝ] ℝ} {c₀ c₁ c₂ : ℝ} :
    Convex ℝ {z : Euc 3 | g₀ z < c₀ ∧ c₁ < g₁ z ∧ c₂ < g₂ z} := by
  have e : {z : Euc 3 | g₀ z < c₀ ∧ c₁ < g₁ z ∧ c₂ < g₂ z} =
      {z : Euc 3 | g₀ z < c₀} ∩ {z : Euc 3 | c₁ < g₁ z} ∩
        {z : Euc 3 | c₂ < g₂ z} := by
    ext z; simp [and_assoc]
  rw [e]
  exact ((convex_Iio c₀).linear_preimage g₀).inter
    (((convex_Ioi c₁).linear_preimage g₁).inter
      ((convex_Ioi c₂).linear_preimage g₂))

/-- The `P²` region `{g₀ < c₀, g₁ < c₁, g₂ < c₂}` is convex. -/
private lemma convex_halfspaces₂ {g₀ g₁ g₂ : Euc 3 →ₗ[ℝ] ℝ} {c₀ c₁ c₂ : ℝ} :
    Convex ℝ {z : Euc 3 | g₀ z < c₀ ∧ g₁ z < c₁ ∧ g₂ z < c₂} := by
  have e : {z : Euc 3 | g₀ z < c₀ ∧ g₁ z < c₁ ∧ g₂ z < c₂} =
      {z : Euc 3 | g₀ z < c₀} ∩ {z : Euc 3 | g₁ z < c₁} ∩
        {z : Euc 3 | g₂ z < c₂} := by
    ext z; simp [and_assoc]
  rw [e]
  exact ((convex_Iio c₀).linear_preimage g₀).inter
    (((convex_Iio c₁).linear_preimage g₁).inter
      ((convex_Iio c₂).linear_preimage g₂))

/-- The `P²` variant of `separates_poly3`: the sign pattern
`(+,-,+)` on `X` versus `(-,-,-)` on `C` is obtained from the `P¹` pattern
by substituting `(g₁, c₁, g₂, c₂) ↦ (-g₂, -c₂, -g₁, -c₁)`. -/
private lemma separates_poly3' {g₀ g₁ g₂ : Euc 3 →ₗ[ℝ] ℝ} {c₀ c₁ c₂ : ℝ}
    (hg₀ : g₀ ≠ 0) (hg₁ : g₁ ≠ 0) (hg₂ : g₂ ≠ 0)
    {X : Finset (Euc 3)}
    (hX : ∀ x ∈ X, c₀ < g₀ x ∧ g₁ x < c₁ ∧ c₂ < g₂ x)
    (hfree : FreeOf X {z : Euc 3 | g₀ z < c₀ ∧ g₁ z < c₁ ∧ g₂ z < c₂}) :
    ∃ D : Finset (Euc 3), (∀ d ∈ D, d ≠ 0) ∧ D.card ≤ 3 ∧
      ∀ x ∈ X, ∀ y ∈ X, x ≠ y → ∃ d ∈ D, ∃ H : Euc 3 →ₗ[ℝ] ℝ,
        H d = 0 ∧ H x = H y ∧
        (∀ w ∈ {z : Euc 3 | g₀ z < c₀ ∧ g₁ z < c₁ ∧ g₂ z < c₂},
          H w < H x) ∧
          ∀ t : ℝ, x - y ≠ t • d := by
  classical
  refine separates_poly3 {z : Euc 3 | g₀ z < c₀ ∧ g₁ z < c₁ ∧ g₂ z < c₂} ?_
    hg₀ (neg_ne_zero.mpr hg₂) (neg_ne_zero.mpr hg₁) ?_ hfree
  · ext z
    simp only [Set.mem_setOf_eq, LinearMap.neg_apply]
    constructor
    · rintro ⟨h0, h1, h2⟩
      exact ⟨h0, by linarith, by linarith⟩
    · rintro ⟨h0, h1, h2⟩
      exact ⟨h0, by linarith, by linarith⟩
  · intro x hx
    obtain ⟨h0, h1, h2⟩ := hX x hx
    refine ⟨h0, ?_, ?_⟩ <;> simp only [LinearMap.neg_apply] <;> linarith

/-- The Dilworth dichotomy on a middle block: a `P¹`- or `P²`-free large
subset of `X (σ b)`, packaged with the separating data of
`exists_triple_planes`. -/
private lemma triple_free_dichotomy {k k₀ : ℕ} {X : Fin k₀ → Finset (Euc 3)}
    (hne : ∀ i, (X i).Nonempty)
    (hsep : TwoSeparated X) (hconv : CollectionConvex X)
    {x : Fin k₀ → Euc 3} (hx : ∀ i, x i ∈ X i)
    {σ : Fin k ↪o Fin k₀}
    (hsplit : ∀ a b c : Fin k, a ≤ b → b ≤ c →
      Disjoint (convexHull ℝ ((Finset.image (x∘σ)
        (Finset.univ.filter (fun i ↦ i < a ∨ (b ≤ i ∧ i < c))) : Finset (Fin k))
          : Set (Euc 3)))
        (convexHull ℝ ((Finset.image (x∘σ)
        (Finset.univ.filter (fun i ↦ (a ≤ i ∧ i < b) ∨ c ≤ i)) : Finset (Fin k))
          : Set (Euc 3)))))
    {a b c : Fin k} (hab : a < b) (hbc : b < c) (hck : c.val + 1 < k) :
    ∃ g₀ g₁ g₂ : Euc 3 →ₗ[ℝ] ℝ, ∃ c₀ c₁ c₂ : ℝ, ∃ A : Finset (Euc 3),
      g₀ ≠ 0 ∧ g₁ ≠ 0 ∧ g₂ ≠ 0 ∧
      (∀ y ∈ X (σ b), c₀ < g₀ y ∧ g₁ y < c₁ ∧ c₂ < g₂ y) ∧
      (∀ i : Fin k, i < a ∨ (b < i ∧ i ≤ c) →
        ∀ y ∈ X (σ i), g₀ y < c₀ ∧ c₁ < g₁ y ∧ c₂ < g₂ y) ∧
      (∀ i : Fin k, (a ≤ i ∧ i < b) ∨ c < i →
        ∀ y ∈ X (σ i), g₀ y < c₀ ∧ g₁ y < c₁ ∧ g₂ y < c₂) ∧
      A ⊆ X (σ b) ∧ (X (σ b)).card ≤ A.card ^ 2 ∧
      (FreeOf A {z : Euc 3 | g₀ z < c₀ ∧ c₁ < g₁ z ∧ c₂ < g₂ z} ∨
       FreeOf A {z : Euc 3 | g₀ z < c₀ ∧ g₁ z < c₁ ∧ g₂ z < c₂}) := by
  classical
  obtain ⟨g₀, g₁, g₂, c₀, c₁, c₂, hg0, hg1, hg2, hmid, hP1, hP2⟩ :=
    exists_triple_planes hne hsep hconv hx hsplit hab hbc hck
  set B : Finset (Euc 3) := X (σ b) with hBdef
  set P1 : Set (Euc 3) := {z | g₀ z < c₀ ∧ c₁ < g₁ z ∧ c₂ < g₂ z} with hP1def
  have hP1c : Convex ℝ P1 := convex_halfspaces₁
  obtain ⟨t, -, htcard, hco⟩ :=
    exists_isChain_or_isAntichain_sq' B.attach
      (fun x y : ↥B ↦ precRel P1 (x : Euc 3) (y : Euc 3))
      (fun x ↦ precRel_irrefl P1 (x : Euc 3))
      (fun {x y z} hxy hyz ↦ precRel_trans hP1c (fun w hw ↦ hw.1)
        (hmid x x.2).1 (hmid z z.2).1 hxy hyz)
  refine ⟨g₀, g₁, g₂, c₀, c₁, c₂, t.image (fun y : ↥B ↦ (y : Euc 3)),
    hg0, hg1, hg2, hmid, hP1, hP2, ?_, ?_, ?_⟩
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨y', -, rfl⟩ := hy
    exact y'.2
  · have hcoe : (t.image (fun y : ↥B ↦ (y : Euc 3))).card = t.card :=
      Finset.card_image_of_injective _ Subtype.coe_injective
    rw [hcoe]
    rwa [hBdef, Finset.card_attach] at htcard
  · rcases hco with hchain | hanti
    · refine Or.inr ?_
      apply freeOf_of_chain
      · intro y hy
        rw [Finset.mem_image] at hy
        obtain ⟨y', -, rfl⟩ := hy
        exact hmid y' y'.2
      · intro x hx y hy hxy
        rw [Finset.mem_image] at hx hy
        obtain ⟨x', hx', rfl⟩ := hx
        obtain ⟨y', hy', rfl⟩ := hy
        exact hchain x' (Finset.mem_attach _ x') y' (Finset.mem_attach _ y')
          (fun h ↦ hxy (congrArg Subtype.val h))
    · refine Or.inl ?_
      apply freeOf_of_antichain (P := P1) (g := g₀) (c := c₀)
      · intro w hw; exact hw.1
      · intro y hy
        rw [Finset.mem_image] at hy
        obtain ⟨y', -, rfl⟩ := hy
        exact (hmid y' y'.2).1
      · intro x hx y hy hxy
        rw [Finset.mem_image] at hx hy
        obtain ⟨x', hx', rfl⟩ := hx
        obtain ⟨y', hy', rfl⟩ := hy
        exact hanti x' (Finset.mem_attach _ x') y' (Finset.mem_attach _ y')
          (fun h ↦ hxy (congrArg Subtype.val h))

/-- Gluing caps: if each `K l` is a `conv (Q l)`-cap and every other `K r`
lies inside `conv (Q l)`, then `⋃ K l` is in convex position. -/
private lemma cap_union_convex {u : ℕ} {B : Fin u → Finset (Euc 3)}
    (hBdisj : ∀ i j : Fin u, i ≠ j → Disjoint (B i) (B j))
    {K : Fin u → Finset (Euc 3)} (hKB : ∀ l, K l ⊆ B l)
    {Q : Fin u → Finset (Euc 3)}
    (hcap : ∀ l, CapOf (K l) (convexHull ℝ (Q l : Set (Euc 3))))
    (hKQ : ∀ l r : Fin u, l ≠ r →
      (K r : Set (Euc 3)) ⊆ convexHull ℝ (Q l : Set (Euc 3))) :
    InConvexPosition (Finset.univ.biUnion K) := by
  intro x hx hmem
  rw [Finset.mem_biUnion] at hx
  obtain ⟨l, -, hxl⟩ := hx
  refine hcap l x hxl ((convexHull_mono ?_) hmem)
  rintro y hy
  rw [Finset.coe_erase] at hy
  obtain ⟨hyr, hyx⟩ := hy
  rw [Finset.mem_biUnion] at hyr
  obtain ⟨r, -, hyK⟩ := hyr
  rw [Set.mem_singleton_iff] at hyx
  rcases eq_or_ne r l with rfl | hrl
  · exact Set.subset_union_right
      (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hyx, hyK⟩))
  · exact Set.subset_union_left
      (hKQ l r (fun h ↦ hrl h.symm) (Finset.mem_coe.mpr hyK))

/-- Closing the assembly: an `n`-element convex-position subset of the
normalized image pulls back along `T` to a convex `n`-subset of `X`,
contradicting the hypothesis. -/
private lemma close_via_convex {n : ℕ} {X : Finset (Euc 3)}
    {T : Euc 3 →ₗ[ℝ] Euc 3} (hTinj : Function.Injective T)
    (hnocvx : ∀ S ⊆ X, S.card = n → ¬ InConvexPosition S)
    {S' : Finset (Euc 3)} (hS' : S' ⊆ X.image T) (hcard : S'.card = n)
    (hconv : InConvexPosition S') : False := by
  classical
  have himg : (X.filter (fun x ↦ T x ∈ S')).image T = S' := by
    ext z
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨x, ⟨-, hxS⟩, rfl⟩
      exact hxS
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (hS' hz)
      exact ⟨x, ⟨hx, hz⟩, rfl⟩
  have hconv0 : InConvexPosition (X.filter (fun x ↦ T x ∈ S')) :=
    inConvexPosition_preimage_linear hTinj hS' hconv
  have hcard0 : (X.filter (fun x ↦ T x ∈ S')).card = n := by
    have := Finset.card_image_of_injective (X.filter (fun x ↦ T x ∈ S')) hTinj
    rw [himg] at this
    omega
  exact hnocvx _ (Finset.filter_subset _ _) hcard0 hconv0

/-- `choose (N, m) ≤ (e·N/m)^m`. -/
private lemma choose_le_e_pow {N m : ℕ} (hm : 0 < m) :
    ((N.choose m : ℕ) : ℝ) ≤ (Real.exp 1 * N / m) ^ m := by
  have hfact : (m:ℝ) ^ m ≤ (m ! : ℝ) * Real.exp m := by
    have h := Real.sum_le_exp_of_nonneg (Nat.cast_nonneg m) (m + 1)
    have hterm : (m:ℝ) ^ m / (m ! : ℝ) ≤
        ∑ i ∈ Finset.range (m + 1), (m:ℝ) ^ i / i ! :=
      Finset.single_le_sum (fun i _ ↦ by positivity)
        (Finset.mem_range.mpr (Nat.lt_succ_self m))
    have hsum := hterm.trans h
    rw [div_le_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos m))] at hsum
    exact hsum
  have he : Real.exp m = Real.exp 1 ^ m := by
    have h := Real.exp_nat_mul (1 : ℝ) m
    rw [mul_one] at h
    exact h.symm
  calc ((N.choose m : ℕ) : ℝ)
      ≤ (N : ℝ) ^ m / m ! := Nat.choose_le_pow_div m N
    _ ≤ (Real.exp 1 * N / m) ^ m := by
        rw [div_pow, div_le_div_iff (Nat.cast_pos.mpr (Nat.factorial_pos m))
          (by positivity : (0:ℝ) < (m:ℝ) ^ m)]
        calc (N:ℝ) ^ m * (m:ℝ) ^ m ≤ (N:ℝ) ^ m * ((m ! : ℝ) * Real.exp m) :=
              mul_le_mul_of_nonneg_left hfact (by positivity)
          _ = (Real.exp 1 * (N:ℝ)) ^ m * (m ! : ℝ) := by
              rw [mul_pow, ← he]; ring

/-- Choice of the cap count `u` making `6·log₂(e(u+2))/u ≤ ε/4`. -/
private lemma exists_capCount {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℕ, 1 ≤ u ∧ (6:ℝ) * Real.logb 2 (Real.exp 1 * (u + 2)) ≤ ε * u / 4 := by
  classical
  refine ⟨Nat.ceil ((250 / ε) ^ 2) + 1, by omega, ?_⟩
  have h250 : (0:ℝ) < 250 / ε := by positivity
  set u : ℕ := Nat.ceil ((250/ε)^2) + 1 with hu
  have hceil : (250 / ε) ^ 2 ≤ (u : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast Nat.le_add_right _ _)
  have hsqrt : 250 / ε ≤ Real.sqrt (u : ℝ) := by
    have h := Real.sqrt_le_sqrt hceil
    rwa [Real.sqrt_sq h250.le] at h
  have hu1 : (1:ℝ) ≤ u := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have hlog2pos : (0:ℝ) < Real.log 2 := Real.log_two_pos
  have hlog2 : (0.693 : ℝ) < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hsqrt2 : Real.sqrt ((u:ℝ) + 2) ≤ 2 * Real.sqrt (u:ℝ) := by
    have h12 : (u:ℝ) + 2 ≤ 4 * u := by nlinarith [hu1]
    calc Real.sqrt ((u:ℝ) + 2) ≤ Real.sqrt (4 * u) := Real.sqrt_le_sqrt h12
      _ = 2 * Real.sqrt u := by
          rw [show (4:ℝ) = 2^2 by norm_num,
            Real.sqrt_mul (sq_nonneg (2:ℝ)),
            Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  have hlog : Real.log ((u:ℝ) + 2) ≤ 2 * Real.sqrt ((u:ℝ) + 2) := by
    have h1 := Real.log_le_sub_one_of_pos
      (x := Real.sqrt ((u:ℝ) + 2)) (Real.sqrt_pos.mpr (by positivity))
    rw [Real.log_sqrt (by positivity : (0:ℝ) ≤ u + 2)] at h1
    linarith
  have hL : (6:ℝ) * Real.logb 2 (Real.exp 1 * (u + 2)) ≤ 52 * Real.sqrt (u:ℝ) := by
    have hloge : Real.log (Real.exp 1 * ((u:ℝ) + 2)) = 1 + Real.log (u + 2) := by
      rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt (by positivity)),
        Real.log_exp]
    have hstep : 1 + Real.log ((u:ℝ) + 2) ≤ 3 * Real.sqrt ((u:ℝ) + 2) := by
      have h1 : (1:ℝ) ≤ Real.sqrt ((u:ℝ) + 2) := by
        rw [Real.le_sqrt (by positivity) (by norm_num : (0:ℝ) < 1)]
        norm_num
        exact_mod_cast hu1.trans' (by norm_num : (0:ℝ) ≤ 1) |>.trans' (by
          norm_num : (0:ℝ) ≤ 1) |>.trans (by exact_mod_cast hu1)
      nlinarith [hlog, h1]
    have hdiv : (1 + Real.log ((u:ℝ) + 2)) / Real.log 2 ≤
        (3 * Real.sqrt ((u:ℝ) + 2)) / 0.693 :=
      div_le_div hstep hlog2.le (by norm_num)
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    calc (6:ℝ) * Real.logb 2 (Real.exp 1 * (u + 2))
        = 6 * ((1 + Real.log ((u:ℝ) + 2)) / Real.log 2) := by
          rw [Real.logb, hloge]
          push_cast
          ring_nf
      _ ≤ 6 * (3 * Real.sqrt ((u:ℝ) + 2) / 0.693) :=
          mul_le_mul_of_nonneg_left hdiv (by norm_num)
      _ = 18 / 0.693 * Real.sqrt ((u:ℝ) + 2) := by ring
      _ ≤ 26 * Real.sqrt ((u:ℝ) + 2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
          norm_num
      _ ≤ 26 * (2 * Real.sqrt (u:ℝ)) :=
          mul_le_mul_of_nonneg_left hsqrt2 (by norm_num)
      _ = 52 * Real.sqrt (u:ℝ) := by ring
  calc (6:ℝ) * Real.logb 2 (Real.exp 1 * (u + 2)) ≤ 52 * Real.sqrt (u:ℝ) := hL
    _ ≤ ε * u / 4 := by
        have h1 : (250:ℝ) ≤ ε * Real.sqrt (u:ℝ) := by
          have := hsqrt
          rw [div_le_iff₀ hε] at this
          linarith [mul_comm ε (Real.sqrt (u:ℝ)) ▸ this]
        have h2 : (52:ℝ) * Real.sqrt (u:ℝ) ≤ (ε * Real.sqrt (u:ℝ)) *
            Real.sqrt (u:ℝ) / 4 := by
          rw [div_le_iff₀ (by norm_num : (0:ℝ) < 4)]
          nlinarith [h1, Real.sqrt_nonneg (u:ℝ)]
        have h3 : (ε * Real.sqrt (u:ℝ)) * Real.sqrt (u:ℝ) / 4 = ε * u / 4 := by
          rw [mul_assoc, Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ u)]
        rwa [h3] at h2

/-- The key estimate: the `prop_2_1` threshold `C^6` times the thinning
loss `2^E` is absorbed by `2^{εn/2}` for large `n`. -/
private lemma choose_pow_le_two_pow {u : ℕ} (hu : 1 ≤ u) {ε : ℝ} (hε : 0 < ε)
    (hub : (6:ℝ) * Real.logb 2 (Real.exp 1 * (u + 2)) ≤ ε * u / 4)
    {n E : ℕ} (hn : u * (u + 1) ≤ n) (hnE : (4:ℝ) * E ≤ ε * n) :
    (((n + n / u).choose (n / u) : ℕ) : ℝ) ^ 6 * (2:ℝ) ^ E ≤
      (2:ℝ) ^ (ε * (n:ℝ) / 2) := by
  classical
  set m : ℕ := n / u with hm
  have hm1 : 1 ≤ m := by
    rw [hm, Nat.le_div_iff_mul_le (by omega : 0 < u)]
    calc u * 1 = u := mul_one u
      _ ≤ u * (u + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ n := hn
  have hmu : u ≤ m := by
    rw [hm, Nat.le_div_iff_mul_le (by omega : 0 < u)]
    calc u * u ≤ u * (u + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ n := hn
  have hnm : n ≤ (u + 1) * m := by
    have h1 : u * m + n % u = n := Nat.div_add_mod n u
    have h2 : n % u < u := Nat.mod_lt _ (by omega)
    omega
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm1
  have hupos : (0:ℝ) < u := by exact_mod_cast hu
  have hratio : ((n : ℝ) + m) / m ≤ u + 2 := by
    have h1 : ((n:ℝ) + m) / m = (n:ℝ)/m + 1 := by field_simp
    rw [h1]
    have h2 : (n:ℝ) / m ≤ u + 1 := by
      rw [div_le_iff₀ hmpos]
      calc (n:ℝ) ≤ ((u + 1) * m : ℕ) := by exact_mod_cast hnm
        _ = (u + 1) * m := by push_cast; ring
    linarith
  have hC : (((n + m).choose m : ℕ) : ℝ) ≤ (Real.exp 1 * (u + 2)) ^ m := by
    calc (((n + m).choose m : ℕ) : ℝ)
        ≤ (Real.exp 1 * (n + m) / m) ^ m := choose_le_e_pow (by omega)
      _ = (Real.exp 1 * (((n:ℝ) + m) / m)) ^ m := by
          congr 1
          push_cast
          rw [mul_div_assoc]
      _ ≤ (Real.exp 1 * (u + 2)) ^ m := by
          apply pow_le_pow_left₀ (by positivity)
          exact mul_le_mul_of_nonneg_left hratio (Real.exp_pos 1).le
  set L : ℝ := Real.logb 2 (Real.exp 1 * (u + 2)) with hL
  have hLpos : 0 ≤ L := by
    rw [hL, Real.logb]
    apply div_nonneg _ hlog2pos.le
    · -- log (e(u+2)) ≥ 0
      apply Real.log_nonneg
      calc (1:ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le.trans' (by norm_num)
        _ ≤ Real.exp 1 * (u + 2) := by
            apply le_mul_of_one_le_right (Real.exp_pos 1).le
            exact_mod_cast (by omega : 1 ≤ u + 2)
  have hkey : (Real.exp 1 * (u + 2)) ^ m ≤ (2:ℝ) ^ (L * (m:ℝ)) := by
    have e2 : Real.exp 1 * (u + 2) = (2:ℝ) ^ L := by
      rw [hL]
      exact (Real.rpow_logb (by norm_num) (by norm_num)
        (by positivity : (0:ℝ) < Real.exp 1 * (u + 2))).symm
    calc (Real.exp 1 * (u + 2)) ^ m = ((2:ℝ) ^ L) ^ (m:ℝ) := by
          rw [e2, Real.rpow_natCast]
      _ = (2:ℝ) ^ (L * m) := by rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hC6 : (((n + m).choose m : ℕ) : ℝ) ^ 6 ≤ (2:ℝ) ^ (6 * (m:ℝ) * L) := by
    calc (((n + m).choose m : ℕ) : ℝ) ^ 6
        ≤ ((Real.exp 1 * (u + 2)) ^ m) ^ 6 :=
          pow_le_pow_left₀ (by positivity) hC _
      _ = (Real.exp 1 * (u + 2)) ^ (m * 6) := by rw [pow_mul]
      _ = ((Real.exp 1 * (u + 2)) ^ m) ^ 6 := by rw [pow_mul]; ring_nf
      _ ≤ ((2:ℝ) ^ (L * m)) ^ 6 := pow_le_pow_left₀ (by positivity) hkey _
      _ = (2:ℝ) ^ (L * m * 6) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      _ = (2:ℝ) ^ (6 * (m:ℝ) * L) := by ring_nf
  have hexp : 6 * (m:ℝ) * L + E ≤ ε * n / 2 := by
    have h1 : 6 * (m:ℝ) * L ≤ ε * n / 4 := by
      have h2 : (m:ℝ) ≤ n / u := by
        rw [hm]
        exact Nat.cast_div_le
      have h3 : (m:ℝ) * (6 * L) ≤ (n / u) * (ε * u / 4) :=
        mul_le_mul h2 (by rwa [← hL]) (mul_nonneg (by norm_num) hLpos)
          (by positivity)
      have h4 : (n:ℝ) / u * (ε * u / 4) = ε * n / 4 := by
        field_simp
        ring
      calc 6 * (m:ℝ) * L = (m:ℝ) * (6 * L) := by ring
        _ ≤ (n / u) * (ε * u / 4) := h3
        _ = ε * n / 4 := h4
    linarith [h1, hnE]
  calc (((n + n / u).choose (n / u) : ℕ) : ℝ) ^ 6 * (2:ℝ) ^ E
      = (((n + m).choose m : ℕ) : ℝ) ^ 6 * (2:ℝ) ^ E := by rw [hm]
    _ ≤ (2:ℝ) ^ (6 * (m:ℝ) * L) * (2:ℝ) ^ (E:ℝ) := by
        apply mul_le_mul_of_nonneg hC6 _ (Real.rpow_nonneg (by norm_num) _)
          (Real.rpow_nonneg (by norm_num) _)
        rw [Real.rpow_natCast]
        exact Real.rpow_nonneg (by norm_num) _
    _ = (2:ℝ) ^ (6 * (m:ℝ) * L + E) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    _ ≤ (2:ℝ) ^ (ε * (n:ℝ) / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

/-- `capBound` is at least `1` (in fact `≥ 4`). -/
private lemma capBound_ge_one (n t : ℕ) : (1:ℝ) ≤ capBound n t := by
  have hc : (0:ℕ) < capBound n t := by
    unfold capBound
    have h1 : 0 < (n + 2 * (n / t) + 4).choose (2 * (n / t) + 4) :=
      Nat.choose_pos (by omega)
    positivity
  exact_mod_cast hc

/-- The geometric heart of the argument: given a 3-uniform 2-color Ramsey
clique of size `2u+3` inside `Fin K`, a family `X` of cardinality
`> C^6 · 2^E` in general position with no `n`-convex subset contains a
contradiction, where `C = (n + n/u).choose (n/u)` and
`E = 40 k₀ + k₀³`. -/
private lemma assembly_core {u K k₀ : ℕ} (hu : 1 ≤ u) (hK4 : 4 ≤ K)
    (hram : ∀ χ : Finset (Fin K) → Fin 2,
      ∃ S : Finset (Fin K), S.card = 2 * u + 3 ∧ ∃ col : Fin 2,
        ∀ T : Finset (Fin K), T ⊆ S → T.card = 3 → χ T = col)
    (hk₀ : 3 ≤ k₀)
    (hAB : Classical.choose (aboveBelow_ramsey hK4) ≤ k₀)
    {n : ℕ} (hn : u * (u + 1) ≤ n)
    {X : Finset (Euc 3)} (hX : InGeneralPosition (X : Set (Euc 3)))
    (hnocvx : ∀ S ⊆ X, S.card = n → ¬ InConvexPosition S)
    (hcard : (n + n / u).choose (n / u) ^ 6 * 2 ^ (40 * k₀ + k₀ ^ 3) <
      X.card) : False := by
  classical
  have hm1 : 1 ≤ n / u := by
    rw [Nat.le_div_iff_mul_le (show 0 < u by omega)]
    calc u * 1 = u := mul_one u
      _ ≤ u * (u + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ n := hn
  have hCpos : 0 < (n + n / u).choose (n / u) := Nat.choose_pos (by omega)
  have hC2 : 2 ≤ (n + n / u).choose (n / u) := by
    rcases Nat.lt_or_ge ((n + n / u).choose (n / u)) 2 with h | h
    · have h1 : (n + n / u).choose (n / u) = 1 := by omega
      rw [Nat.choose_eq_one_iff] at h1
      rcases h1 with h1 | h1 <;> omega
    · exact h
  set E : ℕ := 40 * k₀ + k₀ ^ 3 with hE
  have hX4 : 4 ≤ X.card := by
    have hE2 : 2 ≤ E := by rw [hE]; nlinarith [hk₀]
    have h4 : (4:ℕ) ≤ 2 ^ E := by
      calc (4:ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ E := Nat.pow_le_pow_right (by norm_num) hE2
    have h5 : (4:ℕ) ≤ (n + n / u).choose (n / u) ^ 6 * 2 ^ E :=
      le_trans h4 (Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hCpos))
    omega
  -- Step 1: normalization
  obtain ⟨T, hTinj, hX'gp, hinj2, Z, δ, hVeq, hVgp, hVdx, hVcard⟩ :=
    exists_normalization hX hX4
  set X' : Finset (Euc 3) := X.image T with hX'def
  set V : Finset (Euc 2) := Z.image (JSPProblem.PlanarDichotomy.shearX δ)
    with hVdef
  have hX'card : X'.card = X.card := Finset.card_image_of_injective _ hTinj
  -- Step 2: PorValtr
  have hpow : 2 ^ (40 * k₀) ≤ V.card := by
    rw [hVcard]
    have h1 : 2 ^ (40 * k₀) ≤ 2 ^ E :=
      Nat.pow_le_pow_right (by norm_num) (by rw [hE]; omega)
    have h2 : 2 ^ E ≤ (n + n / u).choose (n / u) ^ 6 * 2 ^ E :=
      Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hCpos)
    omega
  obtain ⟨x₂, sgn, TR, hxV, hxmono, hcap, hTeq, hTfib, htrans⟩ :=
    porValtr_positiveFraction hk₀ hVgp hVdx hpow
  have hsup : ∀ i : Fin k₀, TR i = supportOf x₂ sgn i := fun i ↦ hTeq i
  have hshape : pvShaped x₂ sgn := pvShaped_of_capOrCup hxmono hcap
  -- Step 3: support fibers in ℝ³
  set W : Fin k₀ → Finset (Euc 3) :=
    fun i ↦ X'.filter (fun z ↦ proj2 z ∈ TR i) with hWdef
  have hWsub : ∀ i, W i ⊆ X' := fun i ↦ Finset.filter_subset _ _
  have hWcard : ∀ i : Fin k₀, (W i).card = (TR i ∩ (V : Set (Euc 2))).ncard := by
    intro i
    have himg : (W i).image proj2 = V.filter (fun p ↦ p ∈ TR i) := by
      ext p
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨z, ⟨hzX', hzT⟩, rfl⟩
        refine ⟨?_, hzT⟩
        rw [← hVeq]
        exact Finset.mem_image.mpr ⟨z, hzX', rfl⟩
      · rintro ⟨hpV, hpT⟩
        rw [← hVeq, Finset.mem_image] at hpV
        obtain ⟨z, hz, rfl⟩ := hpV
        exact ⟨z, ⟨hz, hpT⟩, rfl⟩
    have hinjW : Set.InjOn proj2 ((W i : Finset (Euc 3)) : Set (Euc 3)) :=
      hinj2.mono (Finset.coe_subset.mpr (hWsub i))
    have h1 : (W i).card = ((W i).image proj2).card :=
      (Finset.card_image_of_injOn hinjW).symm
    rw [h1, himg]
    have h2 : (TR i ∩ (V : Set (Euc 2))) = ↑(V.filter (fun p ↦ p ∈ TR i)) := by
      ext p
      simp [and_comm]
    rw [h2, Set.ncard_coe_Finset]
  have hWfib : ∀ i : Fin k₀, 2 ^ (40 * k₀) * (W i).card ≥ X.card := by
    intro i
    have h := hTfib i
    rw [← hWcard i, hVcard] at h
    exact h
  have hWdisj : ∀ i j : Fin k₀, i ≠ j → Disjoint (W i) (W j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro z hzi hzj
    have hd : Disjoint (TR i) (TR j) := by
      rw [hsup i, hsup j]
      exact supportOf_disjoint hxmono hshape hij
    exact Set.disjoint_left.mp hd (Finset.mem_filter.mp hzi).2
      (Finset.mem_filter.mp hzj).2
  have hgpW : InGeneralPosition
      ((Finset.univ.biUnion W : Finset (Euc 3)) : Set (Euc 3)) := by
    apply inGeneralPosition_mono hX'gp
    intro z hz
    rw [Finset.mem_coe, Finset.mem_biUnion] at hz
    obtain ⟨i, -, hz⟩ := hz
    exact Finset.mem_coe.mpr (hWsub i hz)
  have hWsize : ∀ i : Fin k₀, 2 ^ (k₀ ^ 3) ≤ (W i).card := by
    intro i
    have h1 : 2 ^ (40 * k₀) * 2 ^ (k₀ ^ 3) ≤ 2 ^ (40 * k₀) * (W i).card := by
      calc 2 ^ (40 * k₀) * 2 ^ (k₀ ^ 3) = 2 ^ E := by rw [hE, ← Nat.pow_add]
        _ ≤ (n + n / u).choose (n / u) ^ 6 * 2 ^ E :=
            Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ hCpos)
        _ ≤ X.card := hcard.le
        _ ≤ 2 ^ (40 * k₀) * (W i).card := hWfib i
    exact Nat.le_of_mul_le_mul_left h1
      (pow_pos (by norm_num : (0:ℕ) < 2) _)
  -- Step 4: thinning
  obtain ⟨Y, hYsub, hYcard, hYsep⟩ := prop_2_5 W hWdisj hWsize hgpW
  have hYcard2 : ∀ i : Fin k₀, (n + n / u).choose (n / u) ^ 6 < (Y i).card := by
    intro i
    have h1 : X.card ≤ 2 ^ E * (Y i).card := by
      have h2 : (W i).card ≤ 2 ^ (k₀ ^ 3) * (Y i).card := hYcard i
      calc X.card ≤ 2 ^ (40 * k₀) * (W i).card := hWfib i
        _ ≤ 2 ^ (40 * k₀) * (2 ^ (k₀ ^ 3) * (Y i).card) :=
            Nat.mul_le_mul_left _ h2
        _ = 2 ^ E * (Y i).card := by rw [hE, Nat.pow_add]; ring
    have h2 : (n + n / u).choose (n / u) ^ 6 * 2 ^ E < 2 ^ E * (Y i).card :=
      lt_of_lt_of_le hcard h1
    rw [mul_comm] at h2
    exact Nat.lt_of_mul_lt_mul_left h2 (pow_pos (by norm_num : (0:ℕ) < 2) _)
  have hYne : ∀ i : Fin k₀, (Y i).Nonempty := fun i ↦
    Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) (hYcard2 i))
  have hYconv : CollectionConvex Y :=
    collectionConvex_of_regions hxmono hshape (fun i z hz ↦ by
      rw [← hsup i]
      exact (Finset.mem_filter.mp (hYsub i hz)).2)
  have hYdisj : ∀ i j : Fin k₀, i ≠ j → Disjoint (Y i) (Y j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro z hzi hzj
    have hzi' : proj2 z ∈ TR i := (Finset.mem_filter.mp (hYsub i hzi)).2
    have hzj' : proj2 z ∈ TR j := (Finset.mem_filter.mp (hYsub j hzj)).2
    have hd : Disjoint (TR i) (TR j) := by
      rw [hsup i, hsup j]
      exact supportOf_disjoint hxmono hshape hij
    exact Set.disjoint_left.mp hd hzi' hzj'
  have hYsubX' : ∀ i, Y i ⊆ X' := fun i ↦ (hYsub i).trans (hWsub i)
  -- Step 5: representatives and interval split
  have hrep : ∀ i : Fin k₀, ∃ z : Euc 3, z ∈ Y i := fun i ↦ (hYne i).exists_mem
  choose xA hxA using hrep
  have hxAinj : Function.Injective xA := by
    intro i j hij
    by_contra hne
    have hd : Disjoint (TR i) (TR j) := by
      rw [hsup i, hsup j]
      exact supportOf_disjoint hxmono hshape hne
    have hi : proj2 (xA i) ∈ TR i :=
      (Finset.mem_filter.mp (hYsub i (hxA i))).2
    have hj : proj2 (xA i) ∈ TR j :=
      hij.symm ▸ (Finset.mem_filter.mp (hYsub j (hxA j))).2
    exact Set.disjoint_left.mp hd hi hj
  have hπA : Function.Injective (proj2 ∘ xA) := by
    intro i j hij
    by_contra hne
    simp only [Function.comp_apply] at hij
    have hd : Disjoint (TR i) (TR j) := by
      rw [hsup i, hsup j]
      exact supportOf_disjoint hxmono hshape hne
    have hi : proj2 (xA i) ∈ TR i :=
      (Finset.mem_filter.mp (hYsub i (hxA i))).2
    have hj : proj2 (xA i) ∈ TR j :=
      hij.symm ▸ (Finset.mem_filter.mp (hYsub j (hxA j))).2
    exact Set.disjoint_left.mp hd hi hj
  have hgpA : InGeneralPosition
      ((Finset.image xA Finset.univ : Finset (Euc 3)) : Set (Euc 3)) := by
    apply inGeneralPosition_mono hX'gp
    intro z hz
    rw [Finset.mem_coe, Finset.mem_image] at hz
    obtain ⟨i, -, rfl⟩ := hz
    exact Finset.mem_coe.mpr (hYsubX' i (hxA i))
  have hcvpA : InConvexPosition (Finset.image (proj2 ∘ xA) Finset.univ) := by
    apply htrans
    intro i
    refine ⟨?_, ?_⟩
    · exact (Finset.mem_filter.mp (hYsub i (hxA i))).2
    · rw [← hVeq]
      exact Finset.mem_image.mpr ⟨xA i, hYsubX' i (hxA i), rfl⟩
  obtain ⟨σe, hsplit⟩ := cor_2_4 hxAinj hgpA hπA hcvpA hK4 hAB
  -- Step 6: Ramsey clique and colors
  set M : ℕ := 2 * u + 3 with hMdef
  set FreeData1 : Fin K → Fin K → Fin K → Prop := fun a b c ↦
    ∃ g₀ g₁ g₂ : Euc 3 →ₗ[ℝ] ℝ, ∃ c₀ c₁ c₂ : ℝ, ∃ A : Finset (Euc 3),
      g₀ ≠ 0 ∧ g₁ ≠ 0 ∧ g₂ ≠ 0 ∧
      (∀ y ∈ Y (σe b), c₀ < g₀ y ∧ g₁ y < c₁ ∧ c₂ < g₂ y) ∧
      (∀ i : Fin K, i < a ∨ (b < i ∧ i ≤ c) →
        ∀ y ∈ Y (σe i), g₀ y < c₀ ∧ c₁ < g₁ y ∧ c₂ < g₂ y) ∧
      (∀ i : Fin K, (a ≤ i ∧ i < b) ∨ c < i →
        ∀ y ∈ Y (σe i), g₀ y < c₀ ∧ g₁ y < c₁ ∧ g₂ y < c₂) ∧
      A ⊆ Y (σe b) ∧ (Y (σe b)).card ≤ A.card ^ 2 ∧
      FreeOf A {z : Euc 3 | g₀ z < c₀ ∧ c₁ < g₁ z ∧ c₂ < g₂ z} with hFD1
  set Φ : Finset (Fin K) → Prop := fun T ↦
    ∃ a b c : Fin K, T = {a, b, c} ∧ a < b ∧ b < c ∧ c.val + 1 < K ∧
      FreeData1 a b c with hΦdef
  set χ : Finset (Fin K) → Fin 2 := fun T ↦ if Φ T then 0 else 1 with hχdef
  obtain ⟨S, hScard, col, hmono⟩ := hram χ
  set s : Fin M ↪o Fin K := S.orderEmbOfFin hScard with hsdef
  have hsmem : ∀ i : Fin M, s i ∈ S := fun i ↦
    Finset.orderEmbOfFin_mem S hScard i
  set midPos : Fin u → Fin M := fun l ↦ ⟨2 * l.val + 2, by
    have := l.isLt; omega⟩ with hmidPos
  set bIdx : Fin u → Fin K := fun l ↦ s (midPos l) with hbIdxdef
  have hbIdxinj : Function.Injective bIdx := by
    intro i j hij
    have h1 : midPos i = midPos j := s.injective hij
    have h2 : (midPos i).val = (midPos j).val := congrArg Fin.val h1
    simp only [hmidPos] at h2
    ext
    omega
  set a' : ℕ := n / u + 2 with ha'
  set b' : ℕ := n + 2 with hb'
  -- Step 7: finishing combinatorics
  have finish (Cset : Fin u → Set (Euc 3)) (A : Fin u → Finset (Euc 3))
      (hCconv : ∀ l, Convex ℝ (Cset l))
      (hAsub : ∀ l, A l ⊆ Y (σe (bIdx l)))
      (hAcard : ∀ l, (Y (σe (bIdx l))).card ≤ (A l).card ^ 2)
      (hQmem : ∀ l r : Fin u, r ≠ l → ∀ y ∈ Y (σe (bIdx r)), y ∈ Cset l)
      (hD : ∀ l, ∃ D : Finset (Euc 3), (∀ d ∈ D, d ≠ 0) ∧ D.card ≤ 3 ∧
        ∀ x ∈ A l, ∀ y ∈ A l, x ≠ y → ∃ d ∈ D, ∃ H : Euc 3 →ₗ[ℝ] ℝ,
          H d = 0 ∧ H x = H y ∧ (∀ w ∈ Cset l, H w < H x) ∧
            ∀ t : ℝ, x - y ≠ t • d) :
      False := by
    choose D hD using hD
    set Q : Fin u → Finset (Euc 3) := fun l ↦
      (Finset.univ.erase l).biUnion (fun r ↦ Y (σe (bIdx r))) with hQdef
    have hQC : ∀ l, ((Q l : Finset (Euc 3)) : Set (Euc 3)) ⊆ Cset l := by
      intro l y hy
      rw [Finset.mem_coe, hQdef, Finset.mem_biUnion] at hy
      obtain ⟨r, hr, hy⟩ := hy
      rw [Finset.mem_erase] at hr
      exact hQmem l r hr.1 y hy
    have hAgp : ∀ l, InGeneralPosition ((A l : Finset (Euc 3)) : Set (Euc 3)) :=
      fun l ↦ inGeneralPosition_mono hX'gp
        (Finset.coe_subset.mpr ((hAsub l).trans (hYsubX' _)))
    have hA4 : ∀ l, 4 ≤ (A l).card := by
      intro l
      have h1 : (n + n / u).choose (n / u) ^ 6 < (A l).card ^ 2 :=
        lt_of_lt_of_le (hYcard2 _) (hAcard l)
      have h2 : 64 ≤ (n + n / u).choose (n / u) ^ 6 := by
        calc (64:ℕ) = 2 ^ 6 := by norm_num
          _ ≤ (n + n / u).choose (n / u) ^ 6 := Nat.pow_le_pow_left hC2 6
      by_contra hlt
      push_neg at hlt
      have hA9 : (A l).card ^ 2 ≤ 9 := by
        calc (A l).card ^ 2 ≤ 3 ^ 2 := Nat.pow_le_pow_left (by omega) 2
          _ = 9 := by norm_num
      omega
    have hcard' : ∀ l, (a' + b' - 4).choose (a' - 2) ^ (D l).card <
        (A l).card := by
      intro l
      have hCeq : (a' + b' - 4).choose (a' - 2) =
          (n + n / u).choose (n / u) := by
        have e1 : a' - 2 = n / u := by rw [ha']; omega
        have e2 : a' + b' - 4 = n + n / u := by rw [ha', hb']; omega
        rw [e1, e2]
      rw [hCeq]
      have h1 : (n + n / u).choose (n / u) ^ 6 < (A l).card ^ 2 :=
        lt_of_lt_of_le (hYcard2 _) (hAcard l)
      have h2 : (n + n / u).choose (n / u) ^ 3 < (A l).card := by
        by_contra hle
        push_neg at hle
        have h3 : (A l).card ^ 2 ≤ (n + n / u).choose (n / u) ^ 6 := by
          calc (A l).card ^ 2 ≤ ((n + n / u).choose (n / u) ^ 3) ^ 2 :=
                Nat.pow_le_pow_left hle 2
            _ = (n + n / u).choose (n / u) ^ 6 := by rw [← pow_mul]
        omega
      calc (n + n / u).choose (n / u) ^ (D l).card
          ≤ (n + n / u).choose (n / u) ^ 3 :=
            Nat.pow_le_pow_right hCpos (hD l).2.1
        _ < (A l).card := h2
    have key : ∀ l : Fin u,
        (∃ K' ⊆ A l, K'.card = a' ∧ CapOf K' (convexHull ℝ (Q l : Set (Euc 3)))) ∨
        (∃ S ⊆ A l, S.card = b' ∧ InConvexPosition S) := fun l ↦
      prop_2_1_poly (Cset l) (hCconv l) (D l) (hD l).1 (Q l) (hQC l)
        (hAgp l) (hA4 l) (hD l).2.2 (by rw [ha']; omega) (by rw [hb']; omega)
        (hcard' l)
    by_cases hbad : ∃ l : Fin u, ∃ S ⊆ A l, S.card = b' ∧ InConvexPosition S
    · obtain ⟨l, S', hS'sub, hS'card, hS'conv⟩ := hbad
      obtain ⟨S'', hS''sub, hS''card⟩ := Finset.exists_subset_card_eq
        (show n ≤ S'.card by rw [hS'card, hb']; omega)
      have hS''conv : InConvexPosition S'' := inConvexPosition_mono hS''sub hS'conv
      have hsub : S'' ⊆ X.image T :=
        hX'def ▸ hS''sub.trans ((hS'sub.trans (hAsub l)).trans (hYsubX' _))
      exact close_via_convex hTinj hnocvx hsub hS''card hS''conv
    · push_neg at hbad
      choose KC hKsub hKcard hKcap using fun l ↦ (key l).resolve_right
        (fun ⟨S, hSsub, hSc, hScv⟩ ↦ hbad l S hSsub ⟨hSc, hScv⟩)
      set KK : Finset (Euc 3) := Finset.univ.biUnion KC with hKK
      have hKdisj : ∀ i j : Fin u, i ≠ j → Disjoint (KC i) (KC j) := by
        intro i j hij
        rw [Finset.disjoint_left]
        intro z hzi hzj
        have hzi' : z ∈ Y (σe (bIdx i)) := hAsub i (hKsub i hzi)
        have hzj' : z ∈ Y (σe (bIdx j)) := hAsub j (hKsub j hzj)
        have h1 : proj2 z ∈ TR (σe (bIdx i)) :=
          (Finset.mem_filter.mp (hYsub _ hzi')).2
        have h2 : proj2 z ∈ TR (σe (bIdx j)) :=
          (Finset.mem_filter.mp (hYsub _ hzj')).2
        have hd : Disjoint (TR (σe (bIdx i))) (TR (σe (bIdx j))) := by
          simp only [hsup]
          exact supportOf_disjoint hxmono hshape
            (fun h ↦ hij (hbIdxinj (σe.injective h)))
        exact Set.disjoint_left.mp hd h1 h2
      have hKKcard : KK.card = u * a' := by
        rw [hKK, Finset.card_biUnion (fun i _ j _ hij ↦ hKdisj i j hij),
          Finset.sum_congr rfl (fun i _ ↦ hKcard i), Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have hKQ : ∀ l r : Fin u, l ≠ r →
          ((KC r : Finset (Euc 3)) : Set (Euc 3)) ⊆
            convexHull ℝ (Q l : Set (Euc 3)) := by
        intro l r hrl y hy
        apply subset_convexHull
        rw [Finset.mem_coe, hQdef, Finset.mem_biUnion]
        exact ⟨r, Finset.mem_erase.mpr ⟨fun h ↦ hrl h.symm, Finset.mem_univ r⟩,
          hAsub r (hKsub r hy)⟩
      have hKKconv : InConvexPosition KK :=
        cap_union_convex (fun i j hij ↦
            hYdisj _ _ (fun h ↦ hij (hbIdxinj (σe.injective h))))
          (fun l ↦ (hKsub l).trans (hAsub l)) hKcap hKQ
      have hnle : n ≤ KK.card := by
        rw [hKKcard]
        have h1 : u * (n / u) + n % u = n := Nat.div_add_mod n u
        have h2 : n % u < u := Nat.mod_lt _ (by omega)
        have h3 : u * a' = u * (n / u) + 2 * u := by rw [ha']; ring
        rw [h3]
        omega
      obtain ⟨S'', hS''sub, hS''card⟩ := Finset.exists_subset_card_eq hnle
      have hS''conv : InConvexPosition S'' := inConvexPosition_mono hS''sub hKKconv
      have hKKsub : KK ⊆ X' := by
        intro z hz
        rw [hKK, Finset.mem_biUnion] at hz
        obtain ⟨l, -, hz⟩ := hz
        exact hYsubX' _ (hAsub l (hKsub l hz))
      exact close_via_convex hTinj hnocvx (hX'def ▸ hS''sub.trans hKKsub)
        hS''card hS''conv
  -- Step 8: the two colors
  have hcol : col = 0 ∨ col = 1 := by
    rcases col with ⟨v, hv⟩
    interval_cases v
    · left; rfl
    · right; rfl
  -- per-branch packaging: for each `l`, a convex region `Cset` and a free
  -- `A ⊆ Y (σe (bIdx l))` with `|Y (σe (bIdx l))| ≤ |A|²`, the region
  -- containing every other middle block, and a `≤ 3`-direction separation.
  rcases hcol with hcol | hcol
  · -- color 0: every good triple in the clique admits `P¹`-free data
    have hdata : ∀ l : Fin u, ∃ Cset : Set (Euc 3), ∃ A : Finset (Euc 3),
        Convex ℝ Cset ∧ A ⊆ Y (σe (bIdx l)) ∧
        (Y (σe (bIdx l))).card ≤ A.card ^ 2 ∧
        (∀ r : Fin u, r ≠ l → ∀ y ∈ Y (σe (bIdx r)), y ∈ Cset) ∧
        (∃ D : Finset (Euc 3), (∀ d ∈ D, d ≠ 0) ∧ D.card ≤ 3 ∧
          ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ∃ d ∈ D, ∃ H : Euc 3 →ₗ[ℝ] ℝ,
            H d = 0 ∧ H x = H y ∧ (∀ w ∈ Cset, H w < H x) ∧
              ∀ t : ℝ, x - y ≠ t • d) := by
      intro l
      have hl : l.val < u := l.isLt
      set aa : Fin K := s ⟨2 * l.val + 1, by omega⟩ with haa
      set bb : Fin K := s ⟨2 * l.val + 2, by omega⟩ with hbb
      set cc : Fin K := s ⟨2 * u + 1, by omega⟩ with hcc
      have hab : aa < bb := s.lt_iff_lt.mpr (Fin.lt_iff_val_lt_val.mpr (by omega))
      have hbc : bb < cc := s.lt_iff_lt.mpr (Fin.lt_iff_val_lt_val.mpr (by omega))
      have hck : cc.val + 1 < K := by
        have h1 : cc < s ⟨2 * u + 2, by omega⟩ :=
          s.lt_iff_lt.mpr (Fin.lt_iff_val_lt_val.mpr (by omega))
        have h2 := (s ⟨2 * u + 2, by omega⟩ : Fin K).isLt
        omega
      set T' : Finset (Fin K) := {aa, bb, cc} with hT'def
      have hTcard : T'.card = 3 := by
        have h1 : aa ∉ ({bb, cc} : Finset (Fin K)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push_neg
          exact ⟨ne_of_lt hab, ne_of_lt (hab.trans hbc)⟩
        have h2 : bb ∉ ({cc} : Finset (Fin K)) := by
          simp only [Finset.mem_singleton]
          exact ne_of_lt hbc
        rw [hT'def, Finset.card_insert_of_not_mem h1,
          Finset.card_insert_of_not_mem h2, Finset.card_singleton]
      have hTsub : T' ⊆ S := by
        rw [hT'def]
        exact Finset.insert_subset (hsmem _)
          (Finset.insert_subset (hsmem _)
            (Finset.singleton_subset_iff.mpr (hsmem _)))
      have hχ : χ T' = 0 := hcol ▸ hmono T' hTsub hTcard
      have hΦ : Φ T' := by
        by_contra hnΦ
        rw [hχdef] at hχ
        rw [if_neg hnΦ] at hχ
        exact absurd hχ (by decide)
      obtain ⟨a', b', c', hTeq, ha'b', hb'c', hck', g₀, g₁, g₂, c₀, c₁, c₂, A,
        hg0, hg1, hg2, hmid, hP1side, hP2side, hAsub, hAcard, hfree⟩ := hΦ
      have hTeq' : ({aa, bb, cc} : Finset (Fin K)) = {a', b', c'} := hTeq
      obtain ⟨h1, h2, h3⟩ := sorted_triple_inj hab hbc ha'b' hb'c' hTeq'
      subst h1; subst h2; subst h3
      refine ⟨{z : Euc 3 | g₀ z < c₀ ∧ c₁ < g₁ z ∧ c₂ < g₂ z}, A,
        convex_halfspaces₁, hAsub, hAcard, ?_, ?_⟩
      · intro r hr y hy
        have hi : bIdx r < aa ∨ (bb < bIdx r ∧ bIdx r ≤ cc) := by
          rcases lt_or_gt_of_ne (show r.val ≠ l.val from fun h ↦
            hr (Fin.ext h)) with hrl | hrl
          · left
            show s (midPos r) < s ⟨2 * l.val + 1, _⟩
            apply s.lt_iff_lt.mpr
            rw [hmidPos]
            exact Fin.lt_iff_val_lt_val.mpr (by omega)
          · right
            constructor
            · show s ⟨2 * l.val + 2, _⟩ < s (midPos r)
              apply s.lt_iff_lt.mpr
              rw [hmidPos]
              exact Fin.lt_iff_val_lt_val.mpr (by omega)
            · show s (midPos r) ≤ s ⟨2 * u + 1, _⟩
              apply s.le_iff_le.mpr
              rw [hmidPos]
              exact Fin.le_iff_val_le_val.mpr (by omega)
        exact hP1side _ hi y hy
      · obtain ⟨D, hDne, hDcard, hDsep⟩ :=
          separates_poly3 {z : Euc 3 | g₀ z < c₀ ∧ c₁ < g₁ z ∧ c₂ < g₂ z} rfl
            hg0 hg1 hg2 (fun x hx ↦ hmid x (hAsub hx)) hfree
        exact ⟨D, hDne, hDcard, hDsep⟩
    choose CS A hA using hdata
    exact finish CS A (fun l ↦ (hA l).1) (fun l ↦ (hA l).2.1)
      (fun l ↦ (hA l).2.2.1) (fun l ↦ (hA l).2.2.2.1) (fun l ↦ (hA l).2.2.2.2)
  · -- color 1: no good triple has `P¹`-free data; all have `P²`-free data
    have hdata : ∀ l : Fin u, ∃ Cset : Set (Euc 3), ∃ A : Finset (Euc 3),
        Convex ℝ Cset ∧ A ⊆ Y (σe (bIdx l)) ∧
        (Y (σe (bIdx l))).card ≤ A.card ^ 2 ∧
        (∀ r : Fin u, r ≠ l → ∀ y ∈ Y (σe (bIdx r)), y ∈ Cset) ∧
        (∃ D : Finset (Euc 3), (∀ d ∈ D, d ≠ 0) ∧ D.card ≤ 3 ∧
          ∀ x ∈ A, ∀ y ∈ A, x ≠ y → ∃ d ∈ D, ∃ H : Euc 3 →ₗ[ℝ] ℝ,
            H d = 0 ∧ H x = H y ∧ (∀ w ∈ Cset, H w < H x) ∧
              ∀ t : ℝ, x - y ≠ t • d) := by
      intro l
      have hl : l.val < u := l.isLt
      set aa : Fin K := s ⟨0, by omega⟩ with haa
      set bb : Fin K := s ⟨2 * l.val + 2, by omega⟩ with hbb
      set cc : Fin K := s ⟨2 * l.val + 3, by omega⟩ with hcc
      have hab : aa < bb := s.lt_iff_lt.mpr (Fin.lt_iff_val_lt_val.mpr (by omega))
      have hbc : bb < cc := s.lt_iff_lt.mpr (Fin.lt_iff_val_lt_val.mpr (by omega))
      have hck : cc.val + 1 < K := by
        have h1 : cc ≤ s ⟨2 * u + 1, by omega⟩ :=
          s.le_iff_le.mpr (Fin.le_iff_val_le_val.mpr (by omega))
        have h2 : s ⟨2 * u + 1, by omega⟩ < s ⟨2 * u + 2, by omega⟩ :=
          s.lt_iff_lt.mpr (Fin.lt_iff_val_lt_val.mpr (by omega))
        have h3 := (s ⟨2 * u + 2, by omega⟩ : Fin K).isLt
        omega
      set T' : Finset (Fin K) := {aa, bb, cc} with hT'def
      have hTcard : T'.card = 3 := by
        have h1 : aa ∉ ({bb, cc} : Finset (Fin K)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          push_neg
          exact ⟨ne_of_lt hab, ne_of_lt (hab.trans hbc)⟩
        have h2 : bb ∉ ({cc} : Finset (Fin K)) := by
          simp only [Finset.mem_singleton]
          exact ne_of_lt hbc
        rw [hT'def, Finset.card_insert_of_not_mem h1,
          Finset.card_insert_of_not_mem h2, Finset.card_singleton]
      have hTsub : T' ⊆ S := by
        rw [hT'def]
        exact Finset.insert_subset (hsmem _)
          (Finset.insert_subset (hsmem _)
            (Finset.singleton_subset_iff.mpr (hsmem _)))
      have hχ : χ T' = 1 := hcol ▸ hmono T' hTsub hTcard
      have hnΦ : ¬ Φ T' := by
        intro hΦ
        rw [hχdef] at hχ
        rw [if_pos hΦ] at hχ
        exact absurd hχ (by decide)
      obtain ⟨g₀, g₁, g₂, c₀, c₁, c₂, A, hg0, hg1, hg2, hmid, hP1side, hP2side,
        hAsub, hAcard, hfree⟩ :=
        triple_free_dichotomy hYne hYsep hYconv hxA hsplit hab hbc hck
      have hfree2 : FreeOf A
          {z : Euc 3 | g₀ z < c₀ ∧ g₁ z < c₁ ∧ g₂ z < c₂} := by
        rcases hfree with h1 | h2
        · exfalso
          apply hnΦ
          show ∃ a b c : Fin K, T' = {a, b, c} ∧ a < b ∧ b < c ∧
            c.val + 1 < K ∧ FreeData1 a b c
          exact ⟨aa, bb, cc, rfl, hab, hbc, hck,
            g₀, g₁, g₂, c₀, c₁, c₂, A, hg0, hg1, hg2, hmid, hP1side, hP2side,
            hAsub, hAcard, h1⟩
        · exact h2
      refine ⟨{z : Euc 3 | g₀ z < c₀ ∧ g₁ z < c₁ ∧ g₂ z < c₂}, A,
        convex_halfspaces₂, hAsub, hAcard, ?_, ?_⟩
      · intro r hr y hy
        have hi : (aa ≤ bIdx r ∧ bIdx r < bb) ∨ cc < bIdx r := by
          rcases lt_or_gt_of_ne (show r.val ≠ l.val from fun h ↦
            hr (Fin.ext h)) with hrl | hrl
          · left
            constructor
            · show s ⟨0, _⟩ ≤ s (midPos r)
              apply s.le_iff_le.mpr
              rw [hmidPos]
              exact Fin.le_iff_val_le_val.mpr (Nat.zero_le _)
            · show s (midPos r) < s ⟨2 * l.val + 2, _⟩
              apply s.lt_iff_lt.mpr
              rw [hmidPos]
              exact Fin.lt_iff_val_lt_val.mpr (by omega)
          · right
            show s ⟨2 * l.val + 3, _⟩ < s (midPos r)
            apply s.lt_iff_lt.mpr
            rw [hmidPos]
            exact Fin.lt_iff_val_lt_val.mpr (by omega)
        obtain ⟨h1, h2, h3⟩ := hP2side _ hi y hy
        exact ⟨h1, h2, h3⟩
      · obtain ⟨D, hDne, hDcard, hDsep⟩ := separates_poly3' hg0 hg1 hg2
          (fun x hx ↦ hmid x (hAsub hx)) hfree2
        exact ⟨D, hDne, hDcard, hDsep⟩
    choose CS A hA using hdata
    exact finish CS A (fun l ↦ (hA l).1) (fun l ↦ (hA l).2.1)
      (fun l ↦ (hA l).2.2.1) (fun l ↦ (hA l).2.2.2.1) (fun l ↦ (hA l).2.2.2.2)

/-- The quantitative geometric core of **Theorem 1.1**, with the block
count `t` chosen by `exists_large_t`.  For all sufficiently large `n`, any
general-position `X ⊆ ℝ³` containing no `n`-element subset in convex position
satisfies `|X| ≤ capBound n t · 2^{εn/2}`: the `capBound` factor is the
`prop_2_1`-type binomial threshold (with the `≤ 3`-edge polytopes of
Proposition 3.1), and `2^{εn/2}` absorbs the subexponential thinning losses
`2^{O(k₀³)}` from `porValtr_positiveFraction` and `prop_2_5` together with
the `aboveBelow_ramsey`/`cor_2_4` and 3-uniform Ramsey (`exists_ramsey`)
reductions. -/
private theorem card_le_capBound_mul_exp (ε : ℝ) (hε : 0 < ε)
    {t : ℕ} (ht : 1 ≤ t) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ X : Finset (Euc 3),
      InGeneralPosition (X : Set (Euc 3)) →
      (∀ S ⊆ X, S.card = n → ¬ InConvexPosition S) →
      (X.card : ℝ) ≤ (capBound n t : ℝ) * (2:ℝ) ^ (ε * (n:ℝ) / 2) := by
  classical
  obtain ⟨u, hu1, hub⟩ := exists_capCount hε
  obtain ⟨K, hram⟩ := exists_ramsey 3 2 (2 * u + 3) (by norm_num)
  have hK4 : 4 ≤ K := by
    obtain ⟨S, hS, -⟩ := hram (fun _ ↦ (0 : Fin 2))
    have h : S.card ≤ K := by
      calc S.card ≤ (Finset.univ : Finset (Fin K)).card :=
            Finset.card_le_univ S
        _ = K := by rw [Finset.card_univ, Fintype.card_fin]
    omega
  set k₀ : ℕ := max 4 (Classical.choose (aboveBelow_ramsey hK4)) with hk₀def
  have hk₀3 : 3 ≤ k₀ := le_trans (by norm_num) (le_max_left _ _)
  have hk₀AB : Classical.choose (aboveBelow_ramsey hK4) ≤ k₀ := le_max_right _ _
  set E : ℕ := 40 * k₀ + k₀ ^ 3 with hEdef
  refine ⟨max (u * (u + 1)) (Nat.ceil (4 * E / ε) + 4),
    fun n hn X hX hno ↦ ?_⟩
  have hn1 : u * (u + 1) ≤ n := le_trans (le_max_left _ _) hn
  have hnE : (4:ℝ) * E ≤ ε * n := by
    have h2 : (n:ℝ) ≥ 4 * E / ε := by
      calc (n:ℝ) ≥ ((Nat.ceil (4 * E / ε) + 4 : ℕ) : ℝ) := by
            exact_mod_cast le_trans (le_max_right _ _) hn
        _ ≥ (Nat.ceil (4 * E / ε) : ℕ) := by
            exact_mod_cast Nat.le_add_right _ _
        _ ≥ 4 * E / ε := Nat.le_ceil _
    rw [div_le_iff₀ hε] at h2
    nlinarith [h2, mul_comm (n:ℝ) ε]
  have hfin : (X.card : ℝ) ≤
      (((n + n / u).choose (n / u) : ℕ) : ℝ) ^ 6 * (2:ℝ) ^ E := by
    by_contra hneg
    push_neg at hneg
    have hnat : (n + n / u).choose (n / u) ^ 6 * 2 ^ E < X.card := by
      have h := hneg
      exact_mod_cast h
    exact assembly_core hu1 hK4 hram hk₀3 hk₀AB hn1 hX hno
      (hEdef ▸ hnat)
  calc (X.card : ℝ) ≤
        (((n + n / u).choose (n / u) : ℕ) : ℝ) ^ 6 * (2:ℝ) ^ E := hfin
    _ ≤ (2:ℝ) ^ (ε * n / 2) := choose_pow_le_two_pow hu1 hε hub hn1 hnE
    _ ≤ (capBound n t : ℝ) * (2:ℝ) ^ (ε * (n:ℝ) / 2) := by
        exact le_mul_of_one_le_left (Real.rpow_nonneg (by norm_num) _)
          (capBound_ge_one n t)

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
