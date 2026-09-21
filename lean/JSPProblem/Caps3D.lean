import JSPProblem.CupsCaps
import JSPProblem.Projection

/-!
# JSP-000527 — Proposition 2.1 (`P`-caps in `ℝ³`)

For a polytope `P` (given by its vertex set) and a finite `P`-free set `X` in
general position, `|X| > (a+b-4 choose a-2)^{e(P)}` forces either a `P`-cap of
size `a` or a convex set of size `b`.  The proof superimposes the `e(P)`
partial orders `≺_e` coming from projections along the edges of `P`, applies
Dilworth to find a large common antichain, and finishes with the planar
cups–caps theorem.

`IsEdgeOf` formalizes "`[u,v]` is an edge of `conv P`": some supporting
hyperplane of `conv P` meets `conv P` exactly in `segment u v`.

## Status of `prop_2_1`

The naive statement is **false** for degenerate `P`: see
`prop_2_1_counterexample` below — for `P = ∅` (so `edgeCount P = 0`) and
`|X| = 2`, `a = b = 3`, every hypothesis holds but no `a`- or `b`-element
subset exists.  A second family of counterexamples has `P.card = 2`
(`edgeCount P = 1`), `a = b = 3` and `X` a collinear triple whose line misses
`segment u v`.  In the paper `P` is a genuine polytope (`e(P) ≥ 3`), so the
statement carries the hypothesis `3 ≤ edgeCount P` (which in particular
forces `X.card ≥ 4` in the `a, b ≥ 3` case, whence general position rules
out collinear triples in `X`).

The elementary cases `a ≤ 2` (a `P`-cap) and `b ≤ 2` (a convex set) are proved
below (`capOf_singleton`, `capOf_pair`).  The remaining case `a, b ≥ 3` is
the substantive one — it additionally needs, beyond the paper's machinery
(the `≺_e` orders, the Dilworth antichain argument, and the cup-to-`P`-cap
lifting along `π_e`), a way to apply `cupsCaps` to `π_e X'`, which need not be
in `InGeneralPosition` (collinear projected triples on lines avoiding
`conv (π_e P)` are possible even for `X` in general position).  See the
comment at the `sorry` for a fuller account of the remaining gaps.
-/

noncomputable section

/-- `[u,v]` is an edge of the polytope `conv P` (for `u v ∈ P`, `u ≠ v`):
some linear functional is minimized on `P` exactly along `segment u v`. -/
def IsEdgeOf (P : Finset (Euc 3)) (u v : Euc 3) : Prop :=
  u ∈ P ∧ v ∈ P ∧ u ≠ v ∧
    ∃ f : Euc 3 →ₗ[ℝ] ℝ, ∃ c : ℝ,
      (∀ w ∈ P, c ≤ f w) ∧ (∀ w ∈ P, f w = c → w ∈ segment ℝ u v)

/-- `e(P)`: the number of edges of `conv P`, computed as half the ordered-edge
count on the vertex set `P`. -/
def edgeCount (P : Finset (Euc 3)) : ℕ := by
  classical
  exact ((P ×ˢ P).filter fun p ↦ IsEdgeOf P p.1 p.2).card / 2

/-! ### Small-parameter cases

For `a ≤ 2` (a `P`-cap) or `b ≤ 2` (a convex set) the conclusion of
`prop_2_1` is elementary and does not need the order machinery. -/

/-- A point of a `C`-free set avoids `C` (using any distinct partner). -/
theorem FreeOf.notMem {X : Finset (Euc 3)} {C : Set (Euc 3)} (h : FreeOf X C)
    {x y : Euc 3} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) : x ∉ C :=
  h x hx y hy hxy x (left_mem_affineSpan_pair ℝ x y)

/-- A singleton `{x} ⊆ X` is a `C`-cap when `x` has a distinct partner in `X`
and `C` is convex. -/
theorem capOf_singleton {X : Finset (Euc 3)} {C : Set (Euc 3)} (h : FreeOf X C)
    (hC : Convex ℝ C) {x y : Euc 3} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    CapOf {x} C := by
  intro z hz
  rw [Finset.mem_singleton] at hz; subst hz
  rw [Finset.erase_singleton]
  simp only [Finset.coe_empty, Set.union_empty]
  rw [hC.convexHull_eq]
  exact h.notMem hx hy hxy

/-- A pair `{x, y} ⊆ X` of a `C`-free set is a `C`-cap for convex `C`:
if `x` lay in `conv (C ∪ {y})` it would lie on a segment from `C` to `y`,
putting a point of `C` on the line `xy` and contradicting `FreeOf`. -/
theorem capOf_pair {X : Finset (Euc 3)} {C : Set (Euc 3)} (h : FreeOf X C)
    (hC : Convex ℝ C) {x y : Euc 3} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    CapOf {x, y} C := by
  have hxC : x ∉ C := h.notMem hx hy hxy
  have hyC : y ∉ C := h.notMem hy hx (Ne.symm hxy)
  intro z hz
  rw [Finset.mem_insert, Finset.mem_singleton] at hz
  -- key step: `w ∉ conv (C ∪ {partner})` for `w ∈ {x, y}`.
  have key : ∀ w p' : Euc 3, w ∈ X → w ∉ C → p' ∈ X → p' ∉ C → w ≠ p' →
      w ∉ convexHull ℝ (C ∪ ({p'} : Set (Euc 3))) := by
    intro w p' hwX hwC hp'X hp'C hwp' hmem
    -- `w ∈ conv (C ∪ {p'})` lies on a segment from some `c ∈ C` to `p'`.
    obtain ⟨c, hcC, q, hq, hwseg⟩ : ∃ c ∈ C, ∃ q ∈ ({p'} : Set (Euc 3)),
        w ∈ segment ℝ c q := by
      rcases Set.eq_empty_or_nonempty C with hCe | hCne
      · subst hCe
        exfalso
        simp only [Set.empty_union] at hmem
        rw [(convex_singleton (𝕜 := ℝ) p').convexHull_eq,
          Set.mem_singleton_iff] at hmem
        exact hwp' hmem
      · have hunion := hC.convexHull_union (convex_singleton (𝕜 := ℝ) p') hCne
          ⟨p', rfl⟩
        rw [hunion, mem_convexJoin] at hmem
        exact hmem
    rw [Set.mem_singleton_iff] at hq; subst hq
    -- `w ∈ segment c q`, `w ≠ q` ⇒ `c ∈ line[w, q]` ⇒ `c ∉ C`.
    have hwseg' : w ∈ convexHull ℝ ({c, q} : Set (Euc 3)) := by
      rwa [convexHull_pair]
    have hwline : w ∈ line[ℝ, c, q] :=
      convexHull_subset_affineSpan _ hwseg'
    have hweqc : line[ℝ, w, q] = line[ℝ, c, q] :=
      affineSpan_pair_eq_of_left_mem_of_ne hwline hwp'
    have hcline : c ∈ line[ℝ, w, q] := hweqc ▸ left_mem_affineSpan_pair ℝ c q
    exact h w hwX q hp'X hwp' c hcline hcC
  have he1 : ({x, y} : Finset (Euc 3)).erase x = {y} := by
    rw [Finset.erase_insert (by simpa using hxy)]
  have he2 : ({x, y} : Finset (Euc 3)).erase y = {x} := by
    rw [Finset.erase_insert_of_ne hxy, Finset.erase_singleton,
      Finset.insert_empty]
  rcases hz with rfl | rfl
  · rw [he1, Finset.coe_singleton]
    exact key _ _ hx hxC hy hyC hxy
  · rw [he2, Finset.coe_singleton]
    exact key _ _ hy hyC hx hxC (Ne.symm hxy)

/-- **`prop_2_1` is false without a non-degeneracy hypothesis on `P`**: for
`P = ∅` (`edgeCount ∅ = 0`), `X = {0, e₀}` and `a = b = 3` all the remaining
hypotheses hold — `1 < 2` — but `X` has no three-element subset.  This
counterexample is excluded by the hypothesis `3 ≤ edgeCount P` now carried
by `prop_2_1`. -/
theorem prop_2_1_counterexample :
    let X : Finset (Euc 3) := {0, EuclideanSpace.single 0 1}
    FreeOf X (convexHull ℝ ((∅ : Finset (Euc 3)) : Set (Euc 3))) ∧
    InGeneralPosition (X : Set (Euc 3)) ∧
    (3 + 3 - 4).choose (3 - 2) ^ (edgeCount (∅ : Finset (Euc 3))) < X.card ∧
    ¬ ((∃ Y ⊆ X, Y.card = 3 ∧
        CapOf Y (convexHull ℝ ((∅ : Finset (Euc 3)) : Set (Euc 3)))) ∨
       (∃ S ⊆ X, S.card = 3 ∧ InConvexPosition S)) := by
  classical
  set X : Finset (Euc 3) := {0, EuclideanSpace.single 0 1} with hXdef
  have hXcard : X.card = 2 := by
    rw [hXdef, Finset.card_insert_of_notMem]
    · simp
    · simp only [Finset.mem_singleton]
      intro h
      have h1 := congr_arg (fun f : Euc 3 ↦ f 0) h
      simp at h1
  have hfree : FreeOf X (convexHull ℝ ((∅ : Finset (Euc 3)) : Set (Euc 3))) := by
    intro x hx y hy hxy w hw
    simp only [Finset.coe_empty, convexHull_empty, Set.mem_empty_iff_false]
    exact not_false
  have hgp : InGeneralPosition (X : Set (Euc 3)) := by
    intro s hs hcard'
    have hle : s.card ≤ X.card := Finset.card_le_card hs
    omega
  have hcard : (3 + 3 - 4).choose (3 - 2) ^ (edgeCount (∅ : Finset (Euc 3)))
      < X.card := by
    rw [show edgeCount (∅ : Finset (Euc 3)) = 0 from rfl, pow_zero, hXcard]
    decide
  refine ⟨hfree, hgp, hcard, ?_⟩
  rintro (⟨Y, hY, hYcard, -⟩ | ⟨S, hS, hScard, -⟩)
  · have hle := Finset.card_le_card hY; omega
  · have hle := Finset.card_le_card hS; omega

/-! ### Mirsky combinatorics: iterated antichain extraction

Local copies of the `chainTo`/`chainRank` machinery of `MainTheorem.lean`
(which cannot be imported here — it imports this file), culminating in
`exists_antichain_iter`: the paper's "superimposed partitions" argument.
If `|X| > M^k` and every pair of `X` is incomparable in at least one of `k`
strict orders, then some order has an antichain of size `> M`. -/

section OrderMirsky

variable {α ι : Type*} [DecidableEq α] [DecidableEq ι]

/-- `c` is an `r`-chain inside `s` whose maximum element is `x`: every element
of `c` is `x` itself or `r`-below `x`, and `c` is totally ordered by `r`. -/
private def chainTo (s : Finset α) (r : α → α → Prop) [DecidableRel r]
    (x : α) (c : Finset α) : Prop :=
  c ⊆ s ∧ x ∈ c ∧ (∀ y ∈ c, y = x ∨ r y x) ∧
    ∀ a ∈ c, ∀ b ∈ c, a ≠ b → r a b ∨ r b a

private instance (s : Finset α) (r : α → α → Prop) [DecidableRel r] (x : α) :
    DecidablePred (chainTo s r x) := fun _ ↦ Classical.propDecidable _

/-- The rank of `x` in `(s, r)`: cardinality of the largest `r`-chain in `s`
whose maximum is `x`. -/
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
    _ ≤ chainRank s r x := Finset.le_sup (f := Finset.card) hmem

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

/-- Mirsky-type dichotomy with an explicit bound: either an `r`-antichain of
size `> M`, or an `r`-chain `c` with `s.card ≤ c.card * M` (the rank fibers
are antichains partitioning `s`). -/
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
  · -- a large fiber is an antichain
    obtain ⟨i, hi⟩ := hbig
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
  · -- all fibers small: `|s| ≤ h·M` and the longest chain has size `h`.
    push_neg at hbig
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

/-- **Iterated Mirsky extraction.**  Suppose every pair of distinct points of
`X` is `rᵢ`-incomparable for some `i ∈ E`.  If `|X| > M ^ |E|`, some `rᵢ`
admits an antichain of size `> M`.  This is the paper's argument: if no order
had a large antichain, then for each `i`, `X` would split into `≤ M`
`rᵢ`-chains (here via the chain bound `|X| ≤ |chain|·M` iterated), and
superimposing the partitions would put two points of `X` in a common cell —
comparable in every order, contradiction. -/
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
      -- a pair inside an `rᵢ`-chain cannot be separated by `i`.
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

end OrderMirsky

/-! ### The cylinder preorder `≺_d` -/

/-- `y ≺_d x`: `y` lies in the cylinder over `conv (P ∪ {x})` parallel to `d`,
i.e. `y = w + t·d` for some `w ∈ conv (P ∪ {x})`.  For a linear projection
`π : ℝ³ → ℝ²` with kernel `ℝ ∙ d` this is equivalent to the paper's relation
`π y ∈ conv (π P ∪ {π x})` (by `LinearMap.image_convexHull`).  It is a
preorder: reflexive (`dirLe_refl`) and transitive (`dirLe_trans`). -/
def dirLe (P : Finset (Euc 3)) (d : Euc 3) (y x : Euc 3) : Prop :=
  ∃ w ∈ convexHull ℝ ((P : Set (Euc 3)) ∪ {x}), ∃ t : ℝ, y = w + t • d

theorem dirLe_refl (P : Finset (Euc 3)) (d x : Euc 3) : dirLe P d x x :=
  ⟨x, subset_convexHull _ _
    (Set.mem_union_right _ (Set.mem_singleton_iff.2 rfl)), 0, by simp⟩

/-- `conv (conv S ∪ {y}) = conv (S ∪ {y})`. -/
theorem convexHull_convHull_union_singleton {V : Type*} [AddCommGroup V]
    [Module ℝ V] (s : Set V) (y : V) :
    convexHull ℝ (convexHull ℝ s ∪ {y}) = convexHull ℝ (s ∪ {y}) := by
  apply le_antisymm
  · apply convexHull_min _ (convex_convexHull _ _)
    exact Set.union_subset
      (convexHull_mono (Set.subset_union_left))
      (Set.singleton_subset_iff.2
        (subset_convexHull _ _ (Set.mem_union_right _ rfl)))
  · exact convexHull_mono
      (Set.union_subset_union_left _ (subset_convexHull _ _))

theorem dirLe_trans {P : Finset (Euc 3)} {d x y z : Euc 3}
    (hzy : dirLe P d z y) (hyx : dirLe P d y x) : dirLe P d z x := by
  obtain ⟨w₁, hw₁, t₁, rfl⟩ := hzy
  obtain ⟨w₂, hw₂, t₂, rfl⟩ := hyx
  -- decompose `w₁ ∈ conv (↑P ∪ {w₂ + t₂ • d})` as a segment combination.
  obtain ⟨w₁', hw₁', s₁, hs₁⟩ : ∃ w' ∈ convexHull ℝ ((P : Set (Euc 3)) ∪ {x}),
      ∃ s : ℝ, w₁ = w' + s • d := by
    rcases Set.eq_empty_or_nonempty (P : Set (Euc 3)) with hPe | hPne
    · rw [hPe, Set.empty_union] at hw₁
      rw [convexHull_singleton, Set.mem_singleton_iff] at hw₁
      exact ⟨w₂, hw₂, t₂, hw₁⟩
    · rw [← convexHull_convHull_union_singleton,
        (convex_convexHull ℝ (P : Set (Euc 3))).convexHull_union
          (convex_singleton _) hPne.convexHull (Set.singleton_nonempty _),
        mem_convexJoin] at hw₁
      obtain ⟨c, hc, b', hb', hseg⟩ := hw₁
      rw [Set.mem_singleton_iff] at hb'; subst hb'
      rw [segment_eq_image₂] at hseg
      obtain ⟨⟨α₁, β₁⟩, ⟨hα, hβ, hαβ⟩, hcomb⟩ := hseg
      -- `w₁ = α₁ • c + β₁ • (w₂ + t₂ • d) = (α₁ • c + β₁ • w₂) + (β₁ t₂) • d`
      have hc' : c ∈ convexHull ℝ ((P : Set (Euc 3)) ∪ {x}) :=
        convexHull_mono Set.subset_union_left hc
      have hw₁'mem : α₁ • c + β₁ • w₂ ∈
          convexHull ℝ ((P : Set (Euc 3)) ∪ {x}) :=
        (convex_convexHull _ _).segment_subset hc' hw₂
          (by rw [segment_eq_image₂]; exact ⟨(α₁, β₁), ⟨hα, hβ, hαβ⟩, rfl⟩)
      exact ⟨α₁ • c + β₁ • w₂, hw₁'mem, β₁ * t₂, by
        have hcomb' : α₁ • c + β₁ • (w₂ + t₂ • d) = w₁ := hcomb
        rw [← hcomb', smul_add, smul_smul, add_assoc]⟩
  exact ⟨w₁', hw₁', s₁ + t₁, by rw [hs₁, add_smul]; abel⟩

theorem dirLe_neg {P : Finset (Euc 3)} {d : Euc 3} {x y : Euc 3} :
    dirLe P (-d) y x ↔ dirLe P d y x := by
  constructor
  · rintro ⟨w, hw, t, rfl⟩
    exact ⟨w, hw, -t, by rw [smul_neg, neg_smul]⟩
  · rintro ⟨w, hw, t, rfl⟩
    exact ⟨w, hw, -t, by rw [neg_smul_neg]⟩

/-! ### The augmented strict order

For a preorder `le` and a linear order `ltt`, `aug le ltt x y` is the strict
part of `le`, with `le`-equivalent (mutual) elements ordered by `ltt`.  It is
a strict order whose chains are exactly the `le`-chains (every pair
`le`-comparable) and whose antichains are exactly the strong antichains of
`le` (every distinct pair `le`-incomparable).  This handles the fact that the
paper's `≺_e` is only a preorder: two distinct points can satisfy
`x ≺_e y ≺_e x` (e.g. when `π_e x = π_e y`), and the planar argument needs
pairs with *no* relation in either direction. -/

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

/-! ### Unordered edges of `conv P` -/

/-- `s` is an unordered edge of `conv P`: a two-element subset `{u,v} ⊆ P`
with `segment u v` an edge. -/
def isEdge2 (P : Finset (Euc 3)) (s : Finset (Euc 3)) : Prop :=
  ∃ u ∈ s, ∃ v ∈ s, u ≠ v ∧ IsEdgeOf P u v

/-- The set of unordered edges of `conv P`, as two-element finsets. -/
def edgeSet (P : Finset (Euc 3)) : Finset (Finset (Euc 3)) := by
  classical
  exact (P.powersetCard 2).filter (isEdge2 P)

theorem mem_edgeSet {P : Finset (Euc 3)} {s : Finset (Euc 3)} :
    s ∈ edgeSet P ↔ s ⊆ P ∧ s.card = 2 ∧ isEdge2 P s := by
  classical
  simp only [edgeSet, Finset.mem_filter, Finset.mem_powersetCard]
  exact and_assoc

theorem IsEdgeOf.symm {P : Finset (Euc 3)} {u v : Euc 3} (h : IsEdgeOf P u v) :
    IsEdgeOf P v u := by
  obtain ⟨hu, hv, huv, f, c, hmin, hex⟩ := h
  refine ⟨hv, hu, Ne.symm huv, f, c, hmin, fun w hw hf ↦ ?_⟩
  rw [segment_symm]
  exact hex w hw hf

/-- There are `edgeCount P` unordered edges: the ordered-edge finset fibers
two-to-one over `edgeSet P`. -/
theorem edgeSet_card (P : Finset (Euc 3)) : (edgeSet P).card = edgeCount P := by
  classical
  set T : Finset (Euc 3 × Euc 3) :=
    (P ×ˢ P).filter (fun p ↦ IsEdgeOf P p.1 p.2) with hT
  have hTcard : T.card = 2 * (edgeSet P).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (t := edgeSet P) (f := fun p : Euc 3 × Euc 3 ↦ ({p.1, p.2} : Finset _))]
    · trans ∑ s ∈ edgeSet P, 2
      · apply Finset.sum_congr rfl
        intro s hs
        obtain ⟨hsub, hcard2, u, hu, v, hv, huv, hE⟩ := mem_edgeSet.1 hs
        have huvP : u ∈ P ∧ v ∈ P := ⟨hsub hu, hsub hv⟩
        have hsuv : s = {u, v} := by
          obtain ⟨a, b, hab, habs⟩ := Finset.card_eq_two.1 hcard2
          rw [habs] at hu hv ⊢
          rw [Finset.mem_insert, Finset.mem_singleton] at hu hv
          rcases hu with rfl | rfl <;> rcases hv with rfl | hvbe
          · exact absurd rfl huv
          · rw [hvbe]
          · rw [Finset.pair_comm]
          · exact absurd hvbe.symm huv
        have hfib : T.filter (fun p ↦ ({p.1, p.2} : Finset _) = s) =
            ({(u, v), (v, u)} : Finset (Euc 3 × Euc 3)) := by
          ext ⟨p₁, p₂⟩
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
            Prod.mk.injEq]
          constructor
          · rintro ⟨hpT, hpair⟩
            rw [hsuv] at hpair
            rw [hT] at hpT
            have hne : p₁ ≠ p₂ := (Finset.mem_filter.1 hpT).2.2.2.1
            have hp1 : p₁ ∈ ({u, v} : Finset (Euc 3)) := by
              rw [← hpair]; exact Finset.mem_insert_self _ _
            have hp2 : p₂ ∈ ({u, v} : Finset (Euc 3)) := by
              rw [← hpair]
              exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
            rw [Finset.mem_insert, Finset.mem_singleton] at hp1 hp2
            rcases hp1 with rfl | rfl <;> rcases hp2 with rfl | rfl
            · exact absurd rfl hne
            · exact Or.inl ⟨rfl, rfl⟩
            · exact Or.inr ⟨rfl, rfl⟩
            · exact absurd rfl hne
          · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
            · refine ⟨?_, ?_⟩
              · rw [hT, Finset.mem_filter, Finset.mem_product]
                exact ⟨⟨huvP.1, huvP.2⟩, hE⟩
              · exact hsuv.symm
            · refine ⟨?_, ?_⟩
              · rw [hT, Finset.mem_filter, Finset.mem_product]
                exact ⟨⟨huvP.2, huvP.1⟩, hE.symm⟩
              · rw [hsuv]; exact Finset.pair_comm _ _
        rw [hfib]
        exact Finset.card_pair (fun h ↦ huv (Prod.ext_iff.1 h).1)
      · rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_comm _ _
    · intro p hp
      rw [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hp1, hp2⟩, hE⟩ := hp
      rw [Finset.mem_coe]
      refine mem_edgeSet.2 ⟨?_, ?_, ?_⟩
      · intro z hz
        rw [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact hp1
        · exact hp2
      · rw [Finset.card_insert_of_notMem (by simpa using hE.2.2.1),
          Finset.card_singleton]
      · exact ⟨p.1, Finset.mem_insert_self _ _, p.2,
          Finset.mem_insert_of_mem (Finset.mem_singleton_self _), hE.2.2.1, hE⟩
  have hEven : T.card / 2 = (edgeSet P).card := by
    rw [hTcard]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  unfold edgeCount
  rw [← hEven]

/-- A direction vector of a two-element set `{u,v}`: `v - u` for the chosen
orientation.  Only the line `ℝ ∙ edgeDir s` matters downstream (`dirLe` is
invariant under `d ↦ -d` by `dirLe_neg`). -/
noncomputable def edgeDir (s : Finset (Euc 3)) : Euc 3 :=
  if h : s.card = 2 then
    (Finset.card_eq_two.1 h).choose_spec.choose - (Finset.card_eq_two.1 h).choose
  else 0

theorem edgeDir_spec {s : Finset (Euc 3)} (hs : s.card = 2) :
    ∃ a b : Euc 3, s = {a, b} ∧ a ≠ b ∧ edgeDir s = b - a := by
  unfold edgeDir
  rw [dif_pos hs]
  exact ⟨_, _, (Finset.card_eq_two.1 hs).choose_spec.choose_spec.2,
    (Finset.card_eq_two.1 hs).choose_spec.choose_spec.1, rfl⟩

theorem edgeDir_ne_zero {s : Finset (Euc 3)} (hs : s.card = 2) :
    edgeDir s ≠ 0 := by
  obtain ⟨a, b, -, hab, hd⟩ := edgeDir_spec hs
  rw [hd]
  exact sub_ne_zero.2 (Ne.symm hab)

/-- The direction of `{u,v}` is `±(v - u)`. -/
theorem edgeDir_orientation {s : Finset (Euc 3)} (hs : s.card = 2) {u v : Euc 3}
    (huv : u ≠ v) (h : s = {u, v}) :
    edgeDir s = v - u ∨ edgeDir s = u - v := by
  obtain ⟨a, b, hsab, hab, hd⟩ := edgeDir_spec hs
  rw [h] at hsab
  have hu : u ∈ ({a, b} : Finset (Euc 3)) := by
    rw [← hsab]; exact Finset.mem_insert_self _ _
  have hv : v ∈ ({a, b} : Finset (Euc 3)) := by
    rw [← hsab]
    exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with hua | hub <;> rcases hv with hva | hvb
  · exact absurd (hua.trans hva.symm) huv
  · left; rw [hd, hvb, hua]
  · right; rw [hd, hub, hva]
  · exact absurd (hub.trans hvb.symm) huv

/-- If `H` vanishes on `d`, is equal at `x` and `y`, and is strictly smaller
on `P` than at `x`, then `x` and `y` are `dirLe P d`-incomparable (provided
`d` is not parallel to `x - y`): the plane `H = H x` contains the line `xy`,
is parallel to `d`, and strictly separates it from `P`. -/
theorem dirLe_incomp {P : Finset (Euc 3)} {d : Euc 3}
    (H : Euc 3 →ₗ[ℝ] ℝ) (hd : H d = 0) {x y : Euc 3}
    (hxy : H x = H y) (hP : ∀ p ∈ P, H p < H x)
    (hpar : ∀ t : ℝ, x - y ≠ t • d) :
    ¬ dirLe P d x y ∧ ¬ dirLe P d y x := by
  -- for `z` with `H z = H x`, `w ∈ conv (↑P ∪ {z})` has `H w ≤ H z`,
  -- with equality only at `w = z`.
  have hmax : ∀ z : Euc 3, H z = H x → ∀ w : Euc 3,
      w ∈ convexHull ℝ ((P : Set (Euc 3)) ∪ {z}) →
      H w ≤ H z ∧ (H w = H z → w = z) := by
    intro z hz w hw
    have hzP : z ∉ P := fun hzP ↦ absurd (hz ▸ hP z hzP) (lt_irrefl _)
    rw [Set.union_singleton, ← Finset.coe_insert, Finset.convexHull_eq] at hw
    obtain ⟨wt, hwt0, hwt1, hwtw⟩ := hw
    have hHw : H w = ∑ p ∈ insert z P, wt p * H p := by
      rw [← hwtw, Finset.centerMass_eq_of_sum_1 _ _ hwt1, map_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [map_smul]
      rfl
    have hterm : ∀ p ∈ insert z P, wt p * H p ≤ wt p * H z := by
      intro p hp
      rcases Finset.mem_insert.1 hp with rfl | hpP
      · exact le_rfl
      · exact mul_le_mul_of_nonneg_left (hz.symm ▸ (hP p hpP).le) (hwt0 p hp)
    refine ⟨?_, ?_⟩
    · rw [hHw]
      calc ∑ p ∈ insert z P, wt p * H p
          ≤ ∑ p ∈ insert z P, wt p * H z := Finset.sum_le_sum hterm
        _ = (∑ p ∈ insert z P, wt p) * H z := by rw [Finset.sum_mul]
        _ = H z := by rw [hwt1, one_mul]
    · intro hEq
      -- all weight sits on `z`.
      have hsupp : ∀ p ∈ insert z P, p ≠ z → wt p = 0 := by
        intro p hp hpz
        have hpP : p ∈ P := (Finset.mem_insert.1 hp).resolve_left hpz
        have hlt : H p < H z := hz.symm ▸ hP p hpP
        have hsum : ∑ q ∈ insert z P, wt q * (H z - H q) = 0 := by
          have h1 : ∑ q ∈ insert z P, wt q * H z =
              (∑ q ∈ insert z P, wt q) * H z := by rw [Finset.sum_mul]
          have h2 : ∑ q ∈ insert z P, wt q * (H z - H q) =
              ∑ q ∈ insert z P, wt q * H z - ∑ q ∈ insert z P, wt q * H q := by
            simp_rw [mul_sub]
            exact Finset.sum_sub_distrib _ _
          rw [h2, h1, hwt1, one_mul, ← hHw]
          exact sub_eq_zero.2 (by rw [hEq, hz])
        have hnonneg : ∀ q ∈ insert z P, 0 ≤ wt q * (H z - H q) := by
          intro q hq
          apply mul_nonneg (hwt0 q hq)
          rw [Finset.mem_insert] at hq
          rcases hq with rfl | hqP
          · exact sub_nonneg.2 le_rfl
          · exact sub_nonneg.2 (hz.symm ▸ (hP q hqP).le)
        have := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum p hp
        exact (mul_eq_zero.1 this).resolve_right
          (sub_ne_zero.2 (fun h ↦ ne_of_lt hlt h.symm))
      -- `w = wt z • z = z` since `wt z = 1`.
      have hwtz : wt z = 1 := by
        have h1 := hwt1
        rw [Finset.sum_insert hzP] at h1
        have h2 : ∑ q ∈ P, wt q = 0 :=
          Finset.sum_eq_zero fun q hq ↦ hsupp q (Finset.mem_insert_of_mem hq)
            (fun h ↦ hzP (h ▸ hq))
        rw [h2, add_zero] at h1
        exact h1
      rw [← hwtw, Finset.centerMass_eq_of_sum_1 _ _ hwt1]
      rw [Finset.sum_eq_single z (fun q hq hqz ↦
          by rw [hsupp q hq hqz, zero_smul])
        (fun h ↦ absurd (Finset.mem_insert_self _ _) h)]
      rw [hwtz, one_smul]
      rfl
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
    -- `y = x + t • d`, hence `x - y = (-t) • d`.
    exact hpar (-t) (by rw [hwx, neg_smul]; abel)

/-! ### The three remaining geometric inputs

The next three lemmas are the geometric heart of the paper's proof; each is
stated as a standalone result and remains `sorry`-free in statement but
`sorry` in proof, with the gap documented. -/

/-- **Edge separation** (paper §2, "easy to see"): for `x ≠ y` in a
`conv P`-free set, there is an edge `{u,v}` of `conv P` and a plane
`H = const` through the line `xy`, parallel to the edge and strictly
separating `xy` from `P`.  In particular the direction `v - u` is not
parallel to `y - x`.

GAP.  A precise account of the intended proof and the missing lemmas:

1.  Project along `d := y - x`: a linear `π : Euc 3 →ₗ[ℝ] Euc 2` with
    `ker π = ℝ ∙ d` is needed.  `projAlong d` works only when
    `d (Fin.last 2) ≠ 0`; in general pick a coordinate permutation `σ`
    putting a nonzero coordinate of `d` last and take
    `π = projAlong (Eσ d) ∘ Eσ` (or work in the quotient
    `Euc 3 ⧸ ℝ ∙ d` and transfer through `finrank = 2`).
    Then `π x = π y =: z`, and `z ∉ convexHull ℝ (π '' ↑P)`: otherwise
    `z = π w` for `w ∈ conv P` gives `w - x ∈ ker π = ℝ ∙ (y - x)`, so
    `w ∈ affineSpan ℝ {x, y} ∩ conv P`, contradicting `FreeOf`.

2.  *Planar visible-edge lemma* (missing): for a finite `Q ⊆ Euc 2` and
    `z ∉ convexHull ℝ Q`, there is a functional `g : Euc 2 →ₗ[ℝ] ℝ` whose
    argmax face on `conv Q` is a genuine segment `segment a' b'`
    (`a' ≠ b'`, `a' b' ∈ Q`) with `g z > c' = g a'`.  Route: strict
    separation of the point `z` from the compact convex hull
    (closest point `p₀` with `⟨z - p₀, q' - p₀⟩ ≤ 0`, or Hahn–Banach)
    gives `g₀`; if its argmax face is a vertex, rotate `g₀` to the normal
    of an adjacent edge — the rotation must be justified to stay
    separating, or one instead takes the *exit edge* where the segment
    `[p₀, z]` leaves the polygon (a boundary point lies on an exposed
    edge, and transversality of the exit makes that edge visible from
    `z`).  Either way this needs boundary/edge structure of planar
    `convexHull` of a finset, which mathlib does not provide.

3.  *Lift*: with `H₀ := g ∘ π` and `c' := g a'`, the face
    `F := conv P ∩ {H₀ = c'}` satisfies `π '' F ⊆ e' = segment a' b'` and
    `F = conv (P ∩ {H₀ = c'})` (max-face of a linear functional on a
    finite convex hull is the hull of the maximizers).  Since
    `a' = π a`, `b' = π b` lift to `P`-points of `F`, `π '' F = e'` is
    non-degenerate, so `F` has a one-dimensional face `[u,v]` whose
    direction is not `ℝ`-parallel to `y - x` (if `F` is a segment it is
    that edge; if `F` is a polygon it has ≥ 3 edges, at most 2 parallel
    to `y - x`).  A one-dimensional face of a face is a face of
    `conv P`, exposed by the perturbed functional `f := -H₀ + ε • H₂`
    where `H₂` exposes `[u,v]` inside the plane `{H₀ = c'}` and `ε` is
    smaller than the finite gap `min {c' - H₀ w : w ∈ P, H₀ w < c'}`
    divided by the `H₂`-variation on `P`; this gives `IsEdgeOf P u v`.
    Finally `H := H₀` (or `-H₀` for the strict sign) satisfies
    `H (v - u) = 0`, `H x = H y`, `H p < H x`, and `v - u ≠ t • (y - x)`
    since `π (v - u) ≠ 0`.

Steps 2 and 3 require a developed theory of polytope faces
(exposed faces of `convexHull` of a finset, extreme points of a face are
extreme points of the polytope, faces of faces are faces, functional
perturbation) which is not currently in this development. -/
theorem edge_separates {P : Finset (Euc 3)} (hP : 3 ≤ edgeCount P)
    {X : Finset (Euc 3)} (hXfree : FreeOf X (convexHull ℝ (P : Set (Euc 3))))
    {x y : Euc 3} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    ∃ u v : Euc 3, IsEdgeOf P u v ∧
      ∃ H : Euc 3 →ₗ[ℝ] ℝ, H (v - u) = 0 ∧ H x = H y ∧
        (∀ p ∈ P, H p < H x) ∧ ¬ ∃ t : ℝ, v - u = t • (y - x) := by
  sorry

/-! ### Generic projection: supporting infrastructure

The proof of `exists_generic_projection` uses `projAlong` from
`Projection.lean` together with `exists_avoid_submodules` (finite algebraic
avoidance) and a topological openness lemma for `dirLe`: the set of directions
`d'` for which `y` lies on a forward ray from `conv (P ∪ {x})` along `d'`
is, after normalization, the image of a compact set, hence `dirLe` fails on a
neighbourhood of any direction where it fails. -/

/-- The last-coordinate functional on `Euc 3`. -/
private def coordLast : Euc 3 →ₗ[ℝ] ℝ where
  toFun z := z (Fin.last 2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem coordLast_apply (z : Euc 3) :
    coordLast z = z (Fin.last 2) := rfl

private theorem coordLast_ne_zero : coordLast ≠ 0 := by
  intro h
  have hz : coordLast (WithLp.toLp 2 (fun _ : Fin 3 ↦ (1 : ℝ))) = 0 := by
    rw [h]; rfl
  rw [coordLast_apply] at hz
  exact one_ne_zero hz

/-- Normalization onto the unit sphere, `v ↦ ‖v‖⁻¹ • v`. -/
private noncomputable def normDir (v : Euc 3) : Euc 3 := (‖v‖)⁻¹ • v

private theorem normDir_neg (v : Euc 3) : normDir (-v) = -normDir v := by
  simp only [normDir, norm_neg, smul_neg]

private theorem norm_normDir {v : Euc 3} (hv : v ≠ 0) : ‖normDir v‖ = 1 := by
  rw [normDir, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

private theorem norm_smul_normDir {v : Euc 3} (hv : v ≠ 0) :
    ‖v‖ • normDir v = v := by
  rw [normDir, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv), one_smul]

private theorem normDir_smul (t : ℝ) (v : Euc 3) :
    normDir (t • v) = (t / |t|) • normDir v := by
  rw [normDir, normDir, norm_smul, Real.norm_eq_abs, smul_smul, smul_smul]
  congr 1
  by_cases ht : t = 0
  · simp [ht]
  by_cases hv : v = 0
  · simp [hv]
  have h1 : |t| ≠ 0 := abs_ne_zero.mpr ht
  have h2 : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  field_simp

private theorem continuousAt_normDir {v : Euc 3} (hv : v ≠ 0) :
    ContinuousAt normDir v :=
  ((continuous_norm.continuousAt).inv₀ (norm_ne_zero_iff.mpr hv)).smul
    continuousAt_id

private theorem continuousOn_normDir : ContinuousOn normDir {0}ᶜ :=
  fun _ hv ↦ (continuousAt_normDir (by simpa using hv)).continuousWithinAt

/-- The set of bad normalized directions for the pair `(x, y)`: the unit
vectors `±(y - w)/‖y - w‖` for `w ∈ conv (P ∪ {x})`.  `dirLe P d y x` holds
iff `normDir d` lies in this set (provided `y ∉ conv (P ∪ {x})`). -/
private noncomputable def dirBadSet (P : Finset (Euc 3)) (x y : Euc 3) :
    Set (Euc 3) :=
  (fun w ↦ normDir (y - w)) '' (convexHull ℝ ((P : Set (Euc 3)) ∪ {x})) ∪
    (fun w ↦ normDir (w - y)) '' (convexHull ℝ ((P : Set (Euc 3)) ∪ {x}))

private theorem isCompact_dirBadSet (P : Finset (Euc 3)) (x y : Euc 3)
    (hy : y ∉ convexHull ℝ ((P : Set (Euc 3)) ∪ {x})) :
    IsCompact (dirBadSet P x y) := by
  have hC : IsCompact (convexHull ℝ ((P : Set (Euc 3)) ∪ {x})) :=
    Set.Finite.isCompact_convexHull ℝ
      (P.finite_toSet.union (Set.finite_singleton x))
  have hc₁ : ContinuousOn (fun w ↦ normDir (y - w))
      (convexHull ℝ ((P : Set (Euc 3)) ∪ {x})) :=
    continuousOn_normDir.comp ((continuous_const.sub continuous_id).continuousOn)
      (fun w hw ↦ by
        simpa using sub_ne_zero.mpr (fun e : y = w ↦ hy (e.symm ▸ hw)))
  have hc₂ : ContinuousOn (fun w ↦ normDir (w - y))
      (convexHull ℝ ((P : Set (Euc 3)) ∪ {x})) :=
    continuousOn_normDir.comp ((continuous_id.sub continuous_const).continuousOn)
      (fun w hw ↦ by
        simpa using sub_ne_zero.mpr (fun e : w = y ↦ hy (e ▸ hw)))
  exact (hC.image_of_continuousOn hc₁).union (hC.image_of_continuousOn hc₂)

private theorem dirLe_iff_normDir_mem_dirBadSet {P : Finset (Euc 3)}
    {x y : Euc 3} (hy : y ∉ convexHull ℝ ((P : Set (Euc 3)) ∪ {x}))
    (d : Euc 3) :
    dirLe P d y x ↔ normDir d ∈ dirBadSet P x y := by
  constructor
  · rintro ⟨w, hw, t, hteq⟩
    have hyw : y - w ≠ 0 := sub_ne_zero.mpr (fun e ↦ hy (e.symm ▸ hw))
    have hywd : y - w = t • d := by rw [hteq]; abel
    have ht : t ≠ 0 := fun e ↦ hyw (by rw [hywd, e, zero_smul])
    have hnd : normDir (y - w) = (t / |t|) • normDir d := by
      rw [hywd, normDir_smul]
    rcases lt_or_gt_of_ne ht with htn | htp
    · have hsgn : t / |t| = -1 := by rw [abs_of_neg htn]; field_simp
      rw [hsgn, neg_one_smul] at hnd
      have h2 : normDir d = normDir (w - y) := by
        rw [← neg_sub y w, normDir_neg, hnd, neg_neg]
      exact Set.mem_union_right _ ⟨w, hw, h2.symm⟩
    · have hsgn : t / |t| = 1 := by rw [abs_of_pos htp]; field_simp
      rw [hsgn, one_smul] at hnd
      exact Set.mem_union_left _ ⟨w, hw, hnd⟩
  · intro h
    unfold dirBadSet at h
    rcases h with ⟨w, hw, hwd⟩ | ⟨w, hw, hwd⟩
    · have hyw : y - w ≠ 0 := sub_ne_zero.mpr (fun e ↦ hy (e.symm ▸ hw))
      change normDir (y - w) = normDir d at hwd
      refine ⟨w, hw, ‖y - w‖ * ‖d‖⁻¹, ?_⟩
      have h1 : y - w = (‖y - w‖ * ‖d‖⁻¹) • d := by
        calc y - w = ‖y - w‖ • normDir (y - w) := (norm_smul_normDir hyw).symm
        _ = ‖y - w‖ • normDir d := by rw [hwd]
        _ = (‖y - w‖ * ‖d‖⁻¹) • d := by rw [normDir, smul_smul]
      exact (sub_eq_iff_eq_add.mp h1).trans (add_comm _ _)
    · have hwy : w - y ≠ 0 := sub_ne_zero.mpr (fun e ↦ hy (e ▸ hw))
      change normDir (w - y) = normDir d at hwd
      refine ⟨w, hw, -(‖w - y‖ * ‖d‖⁻¹), ?_⟩
      have h1 : w - y = (‖w - y‖ * ‖d‖⁻¹) • d := by
        calc w - y = ‖w - y‖ • normDir (w - y) := (norm_smul_normDir hwy).symm
        _ = ‖w - y‖ • normDir d := by rw [hwd]
        _ = (‖w - y‖ * ‖d‖⁻¹) • d := by rw [normDir, smul_smul]
      have h2 : y - w = (-(‖w - y‖ * ‖d‖⁻¹)) • d := by
        rw [neg_smul, ← h1, neg_sub]
      exact (sub_eq_iff_eq_add.mp h2).trans (add_comm _ _)

/-- The negation of `dirLe` is open in the direction parameter: the set of
directions along which `y` is *not* reached from `conv (P ∪ {x})` is a
neighbourhood of any direction where it already fails. -/
private theorem not_dirLe_nhds {P : Finset (Euc 3)} {x y : Euc 3} {d : Euc 3}
    (hnd : ¬ dirLe P d y x) (hd : d ≠ 0) :
    {d' : Euc 3 | ¬ dirLe P d' y x} ∈ nhds d := by
  have hy : y ∉ convexHull ℝ ((P : Set (Euc 3)) ∪ {x}) := fun h ↦
    hnd ⟨y, h, 0, by simp⟩
  have hB : IsClosed (dirBadSet P x y) := (isCompact_dirBadSet P x y hy).isClosed
  have hdm : normDir d ∈ (dirBadSet P x y)ᶜ :=
    Set.mem_compl fun h ↦ hnd ((dirLe_iff_normDir_mem_dirBadSet hy d).mpr h)
  have hpre : normDir ⁻¹' (dirBadSet P x y)ᶜ ∈ nhds d :=
    (continuousAt_normDir hd).preimage_mem_nhds (hB.isOpen_compl.mem_nhds hdm)
  exact Filter.mem_of_superset hpre fun d' hd' hdir ↦
    hd' ((dirLe_iff_normDir_mem_dirBadSet hy d').mp hdir)

/-- In a general-position set of size ≥ 4 in `ℝ³`, no point lies on the line
through two other points. -/
private theorem notMem_affineSpan_pair_of_gp3 {X : Finset (Euc 3)}
    (hX : InGeneralPosition (X : Set (Euc 3))) (hX4 : 4 ≤ X.card)
    {x y z : Euc 3} (hx : x ∈ X) (hy : y ∈ X) (hz : z ∈ X)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    z ∉ affineSpan ℝ ({x, y} : Set (Euc 3)) := by
  classical
  have hsc : ({x, y, z} : Finset (Euc 3)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]),
      Finset.card_insert_of_notMem (by simp [hyz]), Finset.card_singleton]
  have hsub : (({x, y, z} : Finset (Euc 3)) : Set (Euc 3)) ⊆ (X : Set _) := by
    intro p hp
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    exacts [hx, hy, hz]
  have hAI := affineIndependent_of_inGeneralPosition hX hX4 hsub (by omega)
  have hzs : z ∈ ({x, y, z} : Finset (Euc 3)) := by simp
  have h := hAI.notMem_affineSpan_sdiff ⟨z, hzs⟩ Set.univ
  have himg : (fun p : ({x, y, z} : Finset (Euc 3)) ↦ (p : Euc 3)) ''
      (Set.univ \ {⟨z, hzs⟩}) = ({x, y} : Set (Euc 3)) := by
    ext w
    constructor
    · rintro ⟨⟨p, hp⟩, ⟨-, hpn⟩, rfl⟩
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd (Set.mem_singleton_iff.mpr rfl) hpn
    · intro hw
      rcases hw with rfl | rfl
      · exact ⟨⟨w, by simp⟩,
          ⟨Set.mem_univ _, fun hmem ↦
            hxz (congrArg Subtype.val (Set.mem_singleton_iff.mp hmem))⟩, rfl⟩
      · exact ⟨⟨w, by simp⟩,
          ⟨Set.mem_univ _, fun hmem ↦
            hyz (congrArg Subtype.val (Set.mem_singleton_iff.mp hmem))⟩, rfl⟩
  rwa [himg] at h

/-- Three non-collinear points in `ℝ²` are affinely independent. -/
private theorem affineIndependent_coe_of_not_collinear {t : Finset (Euc 2)}
    (ht : t.card = 3) (h : ¬ Collinear ℝ (t : Set (Euc 2))) :
    AffineIndependent ℝ (fun w : t ↦ (w : Euc 2)) := by
  classical
  let e : ↥t ≃ Fin 3 := Finset.equivFinOfCardEq ht
  have hcomp : (fun w : ↥t ↦ (w : Euc 2))
      = (fun i : Fin 3 ↦ ((e.symm i : ↥t) : Euc 2)) ∘ e := by
    funext w; simp
  have hrange : Set.range (fun i : Fin 3 ↦ ((e.symm i : ↥t) : Euc 2))
      = (t : Set (Euc 2)) := by
    rw [show (fun i : Fin 3 ↦ ((e.symm i : ↥t) : Euc 2))
        = Subtype.val ∘ e.symm from rfl,
      Set.range_comp, Set.range_eq_univ.mpr e.symm.surjective, Set.image_univ]
    ext z
    constructor
    · rintro ⟨w, -, rfl⟩
      exact Finset.mem_coe.mpr w.2
    · intro hz
      exact ⟨⟨z, Finset.mem_coe.mp hz⟩, rfl⟩
  rw [hcomp, affineIndependent_equiv e, affineIndependent_iff_not_collinear,
    hrange]
  exact h

/-- **Generic-direction perturbation.**  If `A ⊆ X` is a *strong* antichain
for `dirLe P d` (no two points are comparable in either direction), some
linear projection `π : ℝ³ → ℝ²` — with kernel a direction `d'` arbitrarily
close to `d` — keeps `A` pairwise free over `π '' P`, is injective on `A`,
and has `π '' A` in general position.

Proof: the antichain condition `π y ∉ conv (π P ∪ {π x})` is equivalent to
`¬ dirLe P d' y x`, which is open in `d'` by `not_dirLe_nhds` (the bad
normalized directions form a compact set).  Injectivity on `A` and general
position of `π '' A` each amount to avoiding finitely many proper subspaces
(the lines `ℝ ∙ (x - y)` and the planes `span {b - a, c - a}`; the relevant
triples are non-collinear by `notMem_affineSpan_pair_of_gp3` since
`4 ≤ X.card`).  Taking `d' = d + ε • w` with `w` chosen outside those
subspaces (`exists_avoid_submodules` in `Projection.lean`) and `ε` small
enough to preserve the finitely many open conditions gives `π`, the explicit
projection `projAlong d'` with kernel `ℝ ∙ d'`. -/
theorem exists_generic_projection {P X : Finset (Euc 3)}
    (hX : InGeneralPosition (X : Set (Euc 3))) (hX4 : 4 ≤ X.card)
    {A : Finset (Euc 3)} (hA : A ⊆ X) {d : Euc 3} (hd : d ≠ 0)
    (hanti : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
      ¬ dirLe P d y x ∧ ¬ dirLe P d x y) :
    ∃ π : Euc 3 →ₗ[ℝ] Euc 2,
      Set.InjOn π (A : Set (Euc 3)) ∧
      InGeneralPosition ((A.image π : Finset (Euc 2)) : Set (Euc 2)) ∧
      ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
        π y ∉ convexHull ℝ ((π '' (P : Set (Euc 3))) ∪ ({π x} : Set (Euc 2))) ∧
        π x ∉ convexHull ℝ ((π '' (P : Set (Euc 3))) ∪ ({π y} : Set (Euc 2))) := by
  classical
  -- The ordered pairs of distinct points index the antichain conditions.
  let T : Finset (Euc 3 × Euc 3) := (A ×ˢ A).filter fun p ↦ p.1 ≠ p.2
  -- Each antichain condition `¬ dirLe P d' p.2 p.1` holds on a ball around `d`
  -- (`not_dirLe_nhds`), so a common radius `δ` works for all of them.
  have hU : ∀ p ∈ T, ∃ δ > 0,
      Metric.ball d δ ⊆ {d' : Euc 3 | ¬ dirLe P d' p.2 p.1} := by
    intro p hp
    obtain ⟨hpA, hne⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpA
    exact Metric.mem_nhds_iff.mp
      (not_dirLe_nhds ((hanti p.1 hp1 p.2 hp2 hne).1) hd)
  choose δf hδpos hδsub using hU
  let Deltas : Finset ℝ :=
    insert (‖d‖ / 2) (T.attach.image fun p ↦ δf p.1 p.2)
  have hDn : Deltas.Nonempty := ⟨‖d‖ / 2, Finset.mem_insert_self _ _⟩
  let δ : ℝ := Deltas.min' hDn
  have hδpos : 0 < δ := by
    show 0 < Deltas.min' hDn
    rw [Finset.lt_min'_iff]
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · positivity
    · obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hr
      exact hδpos p.1 p.2
  have hδle : ∀ p (hp : p ∈ T), δ ≤ δf p hp := fun p hp ↦
    Finset.min'_le _ _ (Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨⟨p, hp⟩, Finset.mem_attach _ _, rfl⟩))
  have hδnorm : δ ≤ ‖d‖ / 2 :=
    Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  -- The finitely many "bad" subspaces: `{0}` and the last-coordinate kernel
  -- for a nonzero usable direction; difference directions for injectivity;
  -- planes through projected triples for general position.
  let pairSub : Euc 3 × Euc 3 → Submodule ℝ (Euc 3) := fun p ↦ ℝ ∙ (p.1 - p.2)
  let tripSub : Euc 3 × Euc 3 × Euc 3 → Submodule ℝ (Euc 3) :=
    fun t ↦ Submodule.span ℝ ({t.2.1 - t.1, t.2.2 - t.1} : Set (Euc 3))
  let S : Finset (Submodule ℝ (Euc 3)) :=
    {(⊥ : Submodule ℝ (Euc 3)), LinearMap.ker coordLast} ∪
      (A ×ˢ A).image pairSub ∪ (A ×ˢ A ×ˢ A).image tripSub
  have hS : ∀ U ∈ S, U ≠ ⊤ := by
    intro U hU
    rcases Finset.mem_union.mp hU with hU | hU
    · rcases Finset.mem_union.mp hU with hU | hU
      · rcases Finset.mem_insert.mp hU with rfl | hU
        · intro htop
          have hfr := congrArg
            (fun V : Submodule ℝ (Euc 3) ↦ Module.finrank ℝ ↥V) htop
          rw [finrank_bot, finrank_top, finrank_euclideanSpace_fin] at hfr
          omega
        · rw [Finset.mem_singleton] at hU
          rw [hU]
          exact fun htop ↦ coordLast_ne_zero (LinearMap.ker_eq_top.mp htop)
      · obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hU
        have hle : Module.finrank ℝ ↥(pairSub p) ≤ 1 := by
          show Module.finrank ℝ ↥(ℝ ∙ (p.1 - p.2)) ≤ 1
          simpa using finrank_span_le_card ({p.1 - p.2} : Set (Euc 3))
        intro htop
        have hfr := congrArg
          (fun V : Submodule ℝ (Euc 3) ↦ Module.finrank ℝ ↥V) htop
        rw [finrank_top, finrank_euclideanSpace_fin] at hfr
        omega
    · obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hU
      have hle : Module.finrank ℝ ↥(tripSub t) ≤ 2 := by
        show Module.finrank ℝ ↥(Submodule.span ℝ
          ({t.2.1 - t.1, t.2.2 - t.1} : Set (Euc 3))) ≤ 2
        refine (finrank_span_le_card _).trans ?_
        rw [Set.toFinset_insert, Set.toFinset_singleton]
        exact (Finset.card_insert_le _ _).trans (by simp)
      intro htop
      have hfr := congrArg
        (fun V : Submodule ℝ (Euc 3) ↦ Module.finrank ℝ ↥V) htop
      rw [finrank_top, finrank_euclideanSpace_fin] at hfr
      omega
  obtain ⟨w, hw⟩ := exists_avoid_submodules S hS
  have hbotS : (⊥ : Submodule ℝ (Euc 3)) ∈ S :=
    Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
      (Or.inl (Finset.mem_insert_self _ _))))
  have hw0 : w ≠ 0 := fun e ↦ (hw ⊥ hbotS) ((Submodule.mem_bot ℝ).mpr e)
  -- For each bad subspace `U`, at most one value of `ε` puts `d + ε•w` in `U`.
  have key : ∀ U ∈ S, ({ε : ℝ | d + ε • w ∈ U} : Set ℝ).Subsingleton := by
    intro U hU ε₁ hε₁ ε₂ hε₂
    by_contra hne
    have hsub : (ε₁ - ε₂) • w ∈ U := by
      have h := U.sub_mem hε₁ hε₂
      rwa [add_sub_add_comm, sub_self, zero_add, ← sub_smul] at h
    have hte : ε₁ - ε₂ ≠ 0 := sub_ne_zero.mpr hne
    have hwU : w ∈ U := by
      have h := U.smul_mem (ε₁ - ε₂)⁻¹ hsub
      rwa [smul_smul, inv_mul_cancel₀ hte, one_smul] at h
    exact hw U hU hwU
  let Tε : Finset ℝ := S.biUnion fun U ↦
    if hU : U ∈ S then (key U hU).finite.toFinset else ∅
  let Bδ : ℝ := δ / (‖w‖ + 1)
  have hBδ : 0 < Bδ := div_pos hδpos (by positivity)
  obtain ⟨ε, hεmem, hεT⟩ :=
    (Set.Ioo_infinite hBδ).exists_notMem_finset Tε
  obtain ⟨hε0, hεB⟩ := Set.mem_Ioo.mp hεmem
  -- The perturbed direction `d' = d + ε • w` avoids all bad subspaces.
  have hd'U : ∀ U ∈ S, d + ε • w ∉ U := by
    intro U hU hmem
    apply hεT
    rw [Finset.mem_biUnion]
    exact ⟨U, hU, by
      rw [dite_eq_left hU]
      exact (Set.Finite.mem_toFinset _).mpr hmem⟩
  have hd'last : (d + ε • w) (Fin.last 2) ≠ 0 := by
    intro e
    exact hd'U (LinearMap.ker coordLast)
      (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))))
      (LinearMap.mem_ker.mpr (by rw [coordLast_apply]; exact e))
  -- `d'` stays within `δ` of `d`.
  have hnormlt : ‖d + ε • w - d‖ < δ := by
    have heq : d + ε • w - d = ε • w := by abel
    rw [heq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hε0.le]
    calc ε * ‖w‖ < Bδ * ‖w‖ :=
          mul_lt_mul_of_pos_right hεB (norm_pos_iff.mpr hw0)
      _ = δ * (‖w‖ / (‖w‖ + 1)) := by
          have hBδ' : Bδ = δ / (‖w‖ + 1) := rfl
          rw [hBδ', div_mul_eq_mul_div, mul_div_assoc]
      _ < δ * 1 :=
          mul_lt_mul_of_pos_left (by
            rw [div_lt_one (by positivity : (0:ℝ) < ‖w‖ + 1)]
            linarith [norm_nonneg w]) hδpos
      _ = δ := mul_one δ
  -- In particular `d'` preserves all the antichain conditions.
  have hgood : ∀ p ∈ T, ¬ dirLe P (d + ε • w) p.2 p.1 := fun p hp ↦
    hδsub p hp (Metric.mem_ball.mpr (by
      rw [dist_eq_norm]
      exact lt_of_lt_of_le hnormlt (hδle p hp)))
  refine ⟨projAlong (d + ε • w), ?_, ?_, ?_⟩
  · -- Injectivity on `A`: `π a = π b` puts `a - b ∈ ℝ ∙ d'`, forcing `d'`
    -- into the excluded line `ℝ ∙ (a - b)` unless `a = b`.
    intro a ha b hb hab
    by_contra hne
    have hkerab : a - b ∈ ℝ ∙ (d + ε • w) := by
      rw [← projAlong_ker _ hd'last, LinearMap.mem_ker, map_sub, hab, sub_self]
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hkerab
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ht
      exact hne (sub_eq_zero.mp ht.symm)
    have hd'mem : d + ε • w ∈ ℝ ∙ (a - b) := by
      rw [Submodule.mem_span_singleton]
      refine ⟨t⁻¹, ?_⟩
      rw [← ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    exact hd'U _ (Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
      (Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩,
        rfl⟩))))) hd'mem
  · -- General position of the image.
    intro t ht hcard3
    obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := Finset.card_eq_three.mp hcard3
    obtain ⟨a, haA, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp
      (ht (Finset.mem_coe.mpr (Finset.mem_insert_self _ _))))
    obtain ⟨b, hbA, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp
      (ht (Finset.mem_coe.mpr
        (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))))
    obtain ⟨c, hcA, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp
      (ht (Finset.mem_coe.mpr (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))))
    refine affineIndependent_coe_of_not_collinear hcard3 ?_
    intro hcol
    have hmem : projAlong (d + ε • w) c ∈
        affineSpan ℝ ({projAlong (d + ε • w) a, projAlong (d + ε • w) b} :
          Set (Euc 2)) :=
      hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hpq
    obtain ⟨s, hs⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hmem
    -- `π c` on the line through `π a, π b` means `c - a - s • (b - a)`
    -- lies in the kernel `ℝ ∙ d'`.
    have hker' : c - a - s • (b - a) ∈
        LinearMap.ker (projAlong (d + ε • w)) := by
      rw [LinearMap.mem_ker]
      have h2 : projAlong (d + ε • w) c - projAlong (d + ε • w) a
          = s • (projAlong (d + ε • w) b - projAlong (d + ε • w) a) := by
        have h3 : projAlong (d + ε • w) c
            = projAlong (d + ε • w) a
              + s • (projAlong (d + ε • w) b - projAlong (d + ε • w) a) := by
          rw [← hs, AffineMap.lineMap_apply_module]
          module
        rw [h3]; abel
      rw [map_sub, map_sub, map_smul, map_sub, h2, sub_self]
    obtain ⟨u, hu⟩ := Submodule.mem_span_singleton.mp
      ((projAlong_ker _ hd'last) ▸ hker')
    by_cases hu0 : u = 0
    · -- `c - a = s • (b - a)`: then `c` lies on the line `a b` in `ℝ³`,
      -- contradicting the 3-dimensional general position of `X`.
      rw [hu0, zero_smul] at hu
      have hca : c - a = s • (b - a) := by
        have : c - a - s • (b - a) = 0 := hu.symm
        rw [sub_eq_zero] at this
        exact this
      have hmemab : c ∈ affineSpan ℝ ({a, b} : Set (Euc 3)) := by
        rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
        refine ⟨s, ?_⟩
        rw [AffineMap.lineMap_apply_module]
        have hceq : c = a + s • (b - a) := by rw [← hca]; abel
        rw [hceq]
        module
      have hab' : a ≠ b := fun e ↦ hpq (congrArg _ e)
      have hac' : a ≠ c := fun e ↦ hpr (congrArg _ e)
      have hbc' : b ≠ c := fun e ↦ hqr (congrArg _ e)
      exact notMem_affineSpan_pair_of_gp3 hX hX4 (hA haA) (hA hbA) (hA hcA)
        hab' hac' hbc' hmemab
    · -- Otherwise `d' ∈ span {b - a, c - a}`, an excluded plane.
      have hd'mem : d + ε • w ∈ Submodule.span ℝ
          ({b - a, c - a} : Set (Euc 3)) := by
        have hcmem : c - a - s • (b - a) ∈ Submodule.span ℝ
            ({b - a, c - a} : Set (Euc 3)) := by
          have hb : b - a ∈ Submodule.span ℝ
              ({b - a, c - a} : Set (Euc 3)) :=
            Submodule.subset_span (by simp)
          have hc : c - a ∈ Submodule.span ℝ
              ({b - a, c - a} : Set (Euc 3)) :=
            Submodule.subset_span (by simp)
          exact Submodule.sub_mem _ hc (Submodule.smul_mem _ s hb)
        rw [← hu] at hcmem
        have hsmul := (Submodule.span ℝ
          ({b - a, c - a} : Set (Euc 3))).smul_mem u⁻¹ hcmem
        rwa [smul_smul, inv_mul_cancel₀ hu0, one_smul] at hsmul
      exact hd'U _ (Finset.mem_union.mpr (Or.inr
        (Finset.mem_image.mpr ⟨(a, (b, c)),
          Finset.mem_product.mpr ⟨haA, Finset.mem_product.mpr ⟨hbA, hcA⟩⟩,
          rfl⟩))) hd'mem
  · -- The pairwise noncontainment follows from `dirLe` failing along `d'`.
    have himg : ∀ z : Euc 3,
        convexHull ℝ
          ((projAlong (d + ε • w) '' (P : Set (Euc 3))) ∪
            ({projAlong (d + ε • w) z} : Set (Euc 2)))
        = projAlong (d + ε • w) ''
            convexHull ℝ ((P : Set (Euc 3)) ∪ {z}) := by
      intro z
      rw [← Set.image_singleton, ← Set.image_union,
        ← LinearMap.image_convexHull]
    intro x hx y hy hxy
    refine ⟨?_, ?_⟩
    · intro hmem
      rw [himg] at hmem
      obtain ⟨w', hw', hwe⟩ := hmem
      have hkerw : y - w' ∈ ℝ ∙ (d + ε • w) := by
        rw [← projAlong_ker _ hd'last, LinearMap.mem_ker, map_sub, hwe,
          sub_self]
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hkerw
      have hdir : dirLe P (d + ε • w) y x :=
        ⟨w', hw', t, by rw [ht]; abel⟩
      exact hgood ⟨x, y⟩ (Finset.mem_filter.mpr
        ⟨Finset.mk_mem_product hx hy, hxy⟩) hdir
    · intro hmem
      rw [himg] at hmem
      obtain ⟨w', hw', hwe⟩ := hmem
      have hkerw : x - w' ∈ ℝ ∙ (d + ε • w) := by
        rw [← projAlong_ker _ hd'last, LinearMap.mem_ker, map_sub, hwe,
          sub_self]
      obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hkerw
      have hdir : dirLe P (d + ε • w) x y :=
        ⟨w', hw', t, by rw [ht]; abel⟩
      exact hgood ⟨y, x⟩ (Finset.mem_filter.mpr
        ⟨Finset.mk_mem_product hy hx, fun e ↦ hxy e.symm⟩) hdir

/-- **Planar Erdős–Szekeres dichotomy over a compact convex set `K`.**
A finite set `Z ⊆ ℝ²` in general position which is "pairwise `K`-free"
(`q ∉ conv (K ∪ {p})` for distinct `p, q ∈ Z`) and has more than
`(a+b-4 choose a-2)` elements contains a `K`-cap of size `a` or a convex
`b`-set.

GAP: this is the correct planar replacement for applying `cupsCaps`
verbatim.  Some hypothesis like `InGeneralPosition` is necessary: for `K`
a segment, `Z = {(0,5),(5,4),(10,5)}` is pairwise `K`-free but `(5,4)` lies
in `conv (K ∪ {(0,5),(10,5)})`, so `Z` has no `K`-cap triple (and three
collinear points are never in convex position).  The natural proof runs the
cups–caps induction "relative to `K`": order the points by angle around an
interior point of `K` (after reducing to `K` with nonempty interior via
dimension), or equivalently apply `cupsCaps` in polar coordinates and show
a `K`-cap on the cup side via the pairwise condition.  Alternatively,
follow the paper literally: apply `cupsCaps` in coordinates where `K` lies
below all of `Z` (possible only after showing `Z` lies on one side — which
itself needs the pairwise condition plus more geometry). -/
theorem planar_dichotomy {K : Set (Euc 2)} (hKc : Convex ℝ K) (hKk : IsCompact K)
    {Z : Finset (Euc 2)} (hZ : InGeneralPosition (Z : Set (Euc 2)))
    (hpair : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q →
      q ∉ convexHull ℝ (K ∪ ({p} : Set (Euc 2))))
    {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hcard : (a + b - 4).choose (a - 2) < Z.card) :
    (∃ A ⊆ Z, A.card = a ∧
      ∀ y ∈ A, y ∉ convexHull ℝ (K ∪ ((A.erase y : Finset _) : Set _))) ∨
    (∃ B ⊆ Z, B.card = b ∧ InConvexPosition B) := by
  sorry

/-! ### Lifting the planar conclusion back to ℝ³ -/

/-- Preimage of a subset of the projected finset: if `π` is injective on
`X'`, every `A' ⊆ π '' X'` is the image of a unique `A ⊆ X'`. -/
theorem exists_preimage_finset {X' : Finset (Euc 3)} {π : Euc 3 →ₗ[ℝ] Euc 2}
    (hinj : Set.InjOn π (X' : Set (Euc 3))) {A' : Finset (Euc 2)}
    (hA' : A' ⊆ X'.image π) :
    ∃ A : Finset (Euc 3), A ⊆ X' ∧ A.image π = A' ∧ A.card = A'.card := by
  classical
  refine ⟨X'.filter (fun x ↦ π x ∈ A'), Finset.filter_subset _ _, ?_, ?_⟩
  · ext z
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨x, ⟨-, hxA'⟩, rfl⟩; exact hxA'
    · intro hz
      obtain ⟨x, hxX, rfl⟩ := Finset.mem_image.1 (hA' hz)
      exact ⟨x, ⟨hxX, hz⟩, rfl⟩
  · have himg : (X'.filter fun x ↦ π x ∈ A').image π = A' := by
      ext z
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨-, hxA'⟩, rfl⟩; exact hxA'
      · intro hz
        obtain ⟨x, hxX, rfl⟩ := Finset.mem_image.1 (hA' hz)
        exact ⟨x, ⟨hxX, hz⟩, rfl⟩
    have hc := Finset.card_image_of_injOn
      (hinj.mono (Finset.coe_subset.2
        (Finset.filter_subset (p := fun x ↦ π x ∈ A') X')))
    rw [himg] at hc
    exact hc.symm

/-- `π '' ↑(A.erase y) = ↑((A.image π).erase (π y))` for `π` injective on a
superset of `A`. -/
theorem image_erase_eq {X' : Finset (Euc 3)} {π : Euc 3 →ₗ[ℝ] Euc 2}
    (hinj : Set.InjOn π (X' : Set (Euc 3))) {A : Finset (Euc 3)} (hA : A ⊆ X')
    {y : Euc 3} (hy : y ∈ A) :
    π '' ((A.erase y : Finset (Euc 3)) : Set (Euc 3)) =
      (((A.image π).erase (π y) : Finset (Euc 2)) : Set (Euc 2)) := by
  ext z
  rw [Finset.coe_erase, Finset.coe_erase]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hwA, hwy⟩ := hw
    rw [Set.mem_singleton_iff] at hwy
    refine ⟨Finset.mem_coe.2
      (Finset.mem_image.2 ⟨w, Finset.mem_coe.1 hwA, rfl⟩), ?_⟩
    intro h
    exact hwy (hinj (Finset.mem_coe.2 (hA (Finset.mem_coe.1 hwA)))
      (Finset.mem_coe.2 (hA hy)) (Set.mem_singleton_iff.1 h))
  · rintro ⟨hzB, hzq⟩
    obtain ⟨w, hwA, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hzB)
    exact ⟨w, ⟨Finset.mem_coe.2 hwA, fun h ↦
      hzq (Set.mem_singleton_iff.2
        (congrArg π (Set.mem_singleton_iff.1 h)))⟩, rfl⟩

/-- A planar `conv (π '' ↑P)`-cap lifts to a `conv ↑P`-cap upstairs. -/
theorem lift_cap {P X' : Finset (Euc 3)} {π : Euc 3 →ₗ[ℝ] Euc 2}
    (hinj : Set.InjOn π (X' : Set (Euc 3))) {A : Finset (Euc 3)} (hA : A ⊆ X')
    {K : Set (Euc 2)} (hKπ : π '' convexHull ℝ (P : Set (Euc 3)) ⊆ K)
    (hcap : ∀ q ∈ A.image π, q ∉ convexHull ℝ
      (K ∪ (((A.image π).erase q : Finset (Euc 2)) : Set (Euc 2)))) :
    CapOf A (convexHull ℝ (P : Set (Euc 3))) := by
  intro y hy hmem
  have hy' : π y ∈ A.image π := Finset.mem_image.2 ⟨y, hy, rfl⟩
  apply hcap _ hy'
  have h1 : π y ∈ convexHull ℝ
      (π '' (convexHull ℝ (P : Set (Euc 3)) ∪ ((A.erase y : Finset _) : Set _))) := by
    rw [← LinearMap.image_convexHull]
    exact Set.mem_image_of_mem _ hmem
  rw [Set.image_union, image_erase_eq hinj hA hy] at h1
  exact convexHull_mono (Set.union_subset_union_left _ hKπ) h1

/-- A planar convex-position set lifts to a convex-position set upstairs. -/
theorem lift_convexPosition {X' : Finset (Euc 3)} {π : Euc 3 →ₗ[ℝ] Euc 2}
    (hinj : Set.InjOn π (X' : Set (Euc 3))) {A : Finset (Euc 3)} (hA : A ⊆ X')
    (hconv : InConvexPosition (A.image π)) : InConvexPosition A := by
  intro y hy hmem
  have hy' : π y ∈ A.image π := Finset.mem_image.2 ⟨y, hy, rfl⟩
  apply hconv _ hy'
  have h1 : π y ∈
      convexHull ℝ (π '' ((A.erase y : Finset _) : Set (Euc 3))) := by
    rw [← LinearMap.image_convexHull]
    exact Set.mem_image_of_mem _ hmem
  rwa [image_erase_eq hinj hA hy] at h1

/-- **Proposition 2.1.**  The hypothesis `3 ≤ edgeCount P` restricts to
genuine polytopes `P` (a polytope has at least three edges); without it the
statement is false — see `prop_2_1_counterexample` (`edgeCount P = 0`) and
the collinear-triple configuration (`edgeCount P = 1`) described in the
module docstring. -/
theorem prop_2_1 (P : Finset (Euc 3))
    (hP : 3 ≤ edgeCount P)
    {X : Finset (Euc 3)} (hXfree : FreeOf X (convexHull ℝ (P : Set (Euc 3))))
    (hX : InGeneralPosition (X : Set (Euc 3)))
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hcard : (a + b - 4).choose (a - 2) ^ (edgeCount P) < X.card) :
    (∃ Y ⊆ X, Y.card = a ∧ CapOf Y (convexHull ℝ (P : Set (Euc 3)))) ∨
    (∃ S ⊆ X, S.card = b ∧ InConvexPosition S) := by
  classical
  set C := convexHull ℝ (P : Set (Euc 3)) with hCdef
  have hC : Convex ℝ C := convex_convexHull _ _
  rcases Nat.lt_or_ge a 3 with ha3 | ha3
  · -- `a ∈ {1, 2}`: `(a+b-4 choose a-2) = 1`, so `|X| ≥ 2`, and any
    -- `a`-element subset of `X` is a `P`-cap.
    have hM : (a + b - 4).choose (a - 2) = 1 := by
      interval_cases a <;> simp
    rw [hM, one_pow] at hcard
    obtain ⟨Y, hYX, hYcard⟩ :=
      Finset.exists_subset_card_eq (show a ≤ X.card by omega)
    refine Or.inl ⟨Y, hYX, hYcard, ?_⟩
    interval_cases a
    · -- `a = 1`
      obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 hYcard
      rw [Finset.singleton_subset_iff] at hYX
      obtain ⟨y, hyX, hyx⟩ : ∃ y ∈ X, y ≠ x := by
        have hne : (X.erase x).Nonempty := by
          rw [← Finset.card_pos, Finset.card_erase_of_mem hYX]
          omega
        obtain ⟨y, hy⟩ := hne
        exact ⟨y, (Finset.mem_erase.1 hy).2, (Finset.mem_erase.1 hy).1⟩
      exact capOf_singleton hXfree hC hYX hyX (Ne.symm hyx)
    · -- `a = 2`
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hYcard
      rw [Finset.insert_subset_iff] at hYX
      exact capOf_pair hXfree hC hYX.1
        (Finset.singleton_subset_iff.1 hYX.2) hxy
  · rcases Nat.lt_or_ge b 3 with hb3 | hb3
    · -- `b ∈ {1, 2}`: a `b`-element subset of `X` in convex position.
      obtain ⟨S, hSX, hScard⟩ : ∃ S ⊆ X, S.card = b := by
        apply Finset.exists_subset_card_eq
        rcases Nat.lt_or_ge b 2 with hb2 | hb2
        · -- `b = 1`: `X.card ≥ 1` since `M^e ≥ 0`.
          omega
        · -- `b = 2`: `(a-2 choose a-2) = 1`, so `|X| ≥ 2`.
          have hM : (a + b - 4).choose (a - 2) = 1 := by
            have hb2' : b = 2 := by omega
            subst hb2'
            have : a + 2 - 4 = a - 2 := by omega
            rw [this, Nat.choose_self]
          rw [hM, one_pow] at hcard
          omega
      refine Or.inr ⟨S, hSX, hScard, ?_⟩
      interval_cases b
      · -- `b = 1`
        obtain ⟨x, rfl⟩ := Finset.card_eq_one.1 hScard
        exact inConvexPosition_singleton
      · -- `b = 2`
        obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.1 hScard
        exact inConvexPosition_pair hxy
    · -- `a, b ≥ 3`: the substantive case, now with `hP : 3 ≤ edgeCount P`
      -- (excluding the degenerate counterexamples — note `hcard` forces
      -- `X.card ≥ (2 choose 1)^3 + 1 = 9`, so `X` has no collinear triple).
      -- The paper's proof runs:
      --   (i) each line `xy` missing `conv P` has some edge `e` of `P` whose
      --       projection `π_e` separates `π_e (xy)` from `π_e P`
      --       (project along `xy`, take a polygon edge of `conv (π P)`
      --       separating the point `π(xy)`, lift back — "easy to see" in
      --       the paper, but it needs genuine polytope-edge machinery:
      --       the separating edge of a planar `conv` of a finite set, and
      --       the fact that its preimage face contains an edge of `conv P`
      --       exposed by a linear functional, i.e. `IsEdgeOf`);
      --   (ii) `y ≺_e x ↔ π_e y ∈ conv (π_e P ∪ {π_e x})` gives `e(P)`
      --       preorders on `X` such that every pair is incomparable for
      --       some `e` — equivalently the strict orders
      --       `y <_e x ↔ (y + ℝ·(v−u)) ∩ conv (P ∪ {x}) ≠ ∅ ∧ ¬…`;
      --   (iii) iterating Mirsky/Dilworth over the `e(P)` orders yields an
      --       `≺_e`-antichain `X'` of size `> (a+b-4 choose a-2)`
      --       (`exists_isChain_or_isAntichain_sq'` lives in
      --       `MainTheorem.lean`, which imports this file, so a local copy
      --       or an inductive rank argument is needed);
      --   (iv) finish with the planar dichotomy applied to `π_e X'`.
      -- Step (iv) is subtler than the paper suggests:
      --   * `cupsCaps` requires `InGeneralPosition` and `DistinctX` of the
      --     planar input, but `π_e X'` can have collinear triples (the edge
      --     direction can be parallel to a plane through three points of
      --     `X`).  Since the antichain property is open in the projection
      --     direction, one expects to perturb the direction
      --     (`exists_avoid_submodules` in `Projection.lean`); the perturbed
      --     projection no longer uses an edge direction, so the lifting
      --     argument must be reworked accordingly.
      --   * More importantly, the paper's claim that an `a`-cup of `π_e X'`
      --     (in "an appropriately chosen coordinate system") is a
      --     `π_e P`-cap needs more than the antichain property: e.g. for
      --     `P'` a segment, `Z = {(0,5),(5,4),(10,5)}` is a pairwise
      --     antichain and a `3`-cup, but `(5,4) ∈ conv (P' ∪ {(0,5),(10,5)})`
      --     and no `3`-subset is a `P'`-cap (cap-ness is
      --     coordinate-free).  The correct planar lemma is a different
      --     Erdős–Szekeres-type dichotomy: a pairwise antichain `Z` over
      --     `conv (π_e P)` of size `> (a+b-4 choose a-2)` contains a
      --     `π_e P`-cap of size `a` or a convex `b`-set — which then lifts
      --     to ℝ³ via `LinearMap.image_convexHull` and injectivity of the
      --     projection on `X'`.
      classical
      have hM : 1 ≤ (a + b - 4).choose (a - 2) := Nat.choose_pos (by omega)
      have hM2 : 2 ≤ (a + b - 4).choose (a - 2) := by
        calc 2 ≤ a - 1 := by omega
          _ = (a - 1).choose 1 := (Nat.choose_one_right _).symm
          _ = (a - 1).choose (a - 2) :=
              (Nat.choose_symm (show 1 ≤ a - 1 by omega)).symm
          _ ≤ (a + b - 4).choose (a - 2) :=
              Nat.choose_le_choose _ (by omega)
      have hX4 : 4 ≤ X.card := by
        have h1 : (2 : ℕ) ^ 3 ≤
            (a + b - 4).choose (a - 2) ^ edgeCount P :=
          (Nat.pow_le_pow_left hM2 3).trans (Nat.pow_le_pow_right hM hP)
        norm_num at h1
        omega
      -- the strict augment of `≺_e` by a well-order tiebreak: its chains
      -- are `≺_e`-chains and its antichains are strong `≺_e`-antichains.
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
      set rel : Finset (Euc 3) → Euc 3 → Euc 3 → Prop :=
        fun s ↦ aug (dirLe P (edgeDir s)) WellOrderingRel with hrel
      haveI : ∀ s : Finset (Euc 3), DecidableRel (rel s) :=
        fun s a b ↦ Classical.propDecidable _
      have hirr : ∀ s x, ¬ rel s x x := fun s x ↦
        aug_irrefl (fun z ↦ dirLe_refl P (edgeDir s) z) hltt_irr x
      have htr : ∀ s ⦃x y z⦄, rel s x y → rel s y z → rel s x z := by
        intro s x y z h1 h2
        exact aug_trans (le := dirLe P (edgeDir s)) (ltt := WellOrderingRel)
          (dirLe_trans (P := P) (d := edgeDir s)) hltt_tr h1 h2
      -- every pair is separated by some edge's direction.
      have hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
          ∃ s ∈ edgeSet P, ¬ rel s x y ∧ ¬ rel s y x := by
        intro x hx y hy hxy
        obtain ⟨u, v, hE, H, hHd, hHxy, hHP, hpar⟩ :=
          edge_separates hP hXfree hx hy hxy
        have huv : u ≠ v := hE.2.2.1
        have hcard2 : ({u, v} : Finset (Euc 3)).card = 2 := by
          rw [Finset.card_insert_of_notMem (by simpa using huv),
            Finset.card_singleton]
        refine ⟨{u, v}, ?_, ?_⟩
        · rw [mem_edgeSet]
          refine ⟨?_, hcard2, u, Finset.mem_insert_self _ _, v,
            Finset.mem_insert_of_mem (Finset.mem_singleton_self _), huv, hE⟩
          intro z hz
          rw [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hE.1
          · exact hE.2.1
        · have hdir := edgeDir_orientation hcard2 huv rfl
          have hHd' : H (edgeDir ({u, v} : Finset (Euc 3))) = 0 := by
            rcases hdir with h | h
            · rw [h]; exact hHd
            · rw [h, ← neg_sub v u, map_neg, hHd, neg_zero]
          have hpar' : ∀ t : ℝ, x - y ≠
              t • edgeDir ({u, v} : Finset (Euc 3)) := by
            intro t ht
            apply hpar
            rcases hdir with hd1 | hd1
            · rw [hd1] at ht
              by_cases ht0 : t = 0
              · rw [ht0, zero_smul] at ht
                exact absurd (sub_eq_zero.1 ht) hxy
              · exact ⟨-t⁻¹, by
                  rw [← neg_sub x y, smul_neg, neg_smul, neg_neg, ht, smul_smul,
                    inv_mul_cancel₀ ht0, one_smul]⟩
            · rw [hd1] at ht
              by_cases ht0 : t = 0
              · rw [ht0, zero_smul] at ht
                exact absurd (sub_eq_zero.1 ht) hxy
              · exact ⟨t⁻¹, by
                  rw [← neg_sub x y, smul_neg, ht, smul_smul,
                    inv_mul_cancel₀ ht0, one_smul, neg_sub]⟩
          obtain ⟨h1, h2⟩ := dirLe_incomp H hHd' hHxy hHP hpar'
          exact ⟨fun h ↦ h1 (aug_le h), fun h ↦ h2 (aug_le h)⟩
      -- iterated Mirsky gives a large `≺_e`-antichain for one edge `s`.
      obtain ⟨s, hsE, A, hAX, hAcard, hAanti⟩ := exists_antichain_iter rel
        (fun s x ↦ hirr s x) (fun s ↦ htr s) hM (edgeSet P) X hsep
        (by rw [edgeSet_card]; exact hcard)
      have hAanti' : ∀ x ∈ A, ∀ y ∈ A, x ≠ y →
          ¬ dirLe P (edgeDir s) y x ∧ ¬ dirLe P (edgeDir s) x y := by
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
      -- perturb to a generic projection and apply the planar dichotomy.
      obtain ⟨π, hinj, hgpZ, hantiπ⟩ := exists_generic_projection hX hX4 hAX
        (edgeDir_ne_zero (mem_edgeSet.1 hsE).2.1) hAanti'
      set Z := A.image π with hZdef
      have hcardZ : (a + b - 4).choose (a - 2) < Z.card := by
        rw [hZdef, Finset.card_image_of_injOn hinj]
        exact hAcard
      have hpair : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q →
          q ∉ convexHull ℝ
            (convexHull ℝ (π '' (P : Set (Euc 3))) ∪ ({p} : Set (Euc 2))) := by
        intro p hp q hq hpq
        obtain ⟨x, hxA, rfl⟩ := Finset.mem_image.1 hp
        obtain ⟨y, hyA, rfl⟩ := Finset.mem_image.1 hq
        have hxy : x ≠ y := fun e ↦ hpq (congrArg π e)
        rw [convexHull_convHull_union_singleton]
        exact (hantiπ x hxA y hyA hxy).1
      obtain hplanar | hplanar := planar_dichotomy (convex_convexHull _ _)
        ((P.finite_toSet.image π).isCompact_convexHull ℝ) hgpZ hpair ha3 hb3 hcardZ
      · obtain ⟨A', hA'Z, hA'card, hcap'⟩ := hplanar
        obtain ⟨Y, hYA, himg, hYcard⟩ := exists_preimage_finset hinj hA'Z
        refine Or.inl ⟨Y, hYA.trans hAX, hYcard.trans hA'card, ?_⟩
        rw [← himg] at hcap'
        exact lift_cap hinj hYA
          (LinearMap.image_convexHull π (P : Set (Euc 3))).le hcap'
      · obtain ⟨B', hB'Z, hB'card, hconv'⟩ := hplanar
        obtain ⟨S, hSA, himg, hScard⟩ := exists_preimage_finset hinj hB'Z
        refine Or.inr ⟨S, hSA.trans hAX, hScard.trans hB'card, ?_⟩
        rw [← himg] at hconv'
        exact lift_convexPosition hinj hSA hconv'

end
