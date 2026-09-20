import JSPProblem.CupsCaps

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

**The statement as formalized is false** for degenerate `P`: see
`prop_2_1_counterexample` below — for `P = ∅` (so `edgeCount P = 0`) and
`|X| = 2`, `a = b = 3`, every hypothesis holds but no `a`- or `b`-element
subset exists.  A second family of counterexamples has `P.card = 2`
(`edgeCount P = 1`), `a = b = 3` and `X` a collinear triple whose line misses
`segment u v`.  In the paper `P` is a genuine polytope (`e(P) ≥ 3`), so the
statement needs a hypothesis such as `3 ≤ edgeCount P` (which also gives
`|X| ≥ 4`, whence general position rules out collinear triples).

The elementary cases `a ≤ 2` (a `P`-cap) and `b ≤ 2` (a convex set) are proved
below (`capOf_singleton`, `capOf_pair`).  The remaining case `a, b ≥ 3` is
the substantive one — it additionally needs, beyond the paper's machinery
(the `≺_e` orders, the Dilworth antichain argument, and the cup-to-`P`-cap
lifting along `π_e`), a way to apply `cupsCaps` to `π_e X'`, which need not be
in `InGeneralPosition` (collinear projected triples on lines avoiding
`conv (π_e P)` are possible even for `X` in general position).
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

/-- **`prop_2_1` is false as stated** (missing a non-degeneracy hypothesis on
`P`): for `P = ∅` (`edgeCount ∅ = 0`), `X = {0, e₀}` and `a = b = 3` all
hypotheses hold — `1 < 2` — but `X` has no three-element subset. -/
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

/-- **Proposition 2.1.** -/
theorem prop_2_1 (P : Finset (Euc 3))
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
    · -- `a, b ≥ 3`: the substantive case.  As stated this leaf is FALSE for
      -- degenerate `P` — see `prop_2_1_counterexample`
      -- (`edgeCount P = 0`, `a, b > |X|`) and the collinear-triple
      -- configuration (`edgeCount P = 1`, `a = b = 3`, `|X| = 3` collinear).
      -- The paper additionally needs `P` to be a genuine polytope
      -- (`e(P) ≥ 3`); under such a hypothesis the proof runs:
      --   (i) each line `xy` missing `conv P` has some edge `e` of `P` whose
      --       projection `π_e` separates `π_e (xy)` from `π_e P`;
      --   (ii) `y ≺_e x ↔ π_e y ∈ conv (π_e P ∪ {π_e x})` gives `e(P)`
      --       preorders on `X` such that every pair is incomparable for
      --       some `e`;
      --   (iii) Dilworth applied to all `e(P)` orders yields an
      --       `≺_e`-antichain `X'` of size `> (a+b-4 choose a-2)`;
      --   (iv) `cupsCaps` applied to `π_e X'` gives a cup lifting to a
      --       `P`-cap, or a cap lifting to a convex `b`-set.
      -- Step (iv) has a further gap in this formalization: `cupsCaps`
      -- requires `InGeneralPosition` of the planar input, but `π_e X'` need
      -- not be in general position.
      sorry

end
