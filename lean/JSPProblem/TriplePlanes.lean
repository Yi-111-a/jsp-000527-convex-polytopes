import JSPProblem.Separation

/-!
# JSP-000527 — Proposition 3.1 region construction (`exists_triple_planes`)

The region-construction lemma of Pohoata–Zakharov §3: from a 2-separated
collection `X` in convex position, representatives `xᵢ ∈ Xᵢ`, and the
index-split disjointness hypothesis `hsplit` (the geometric input extracted
from the interval-split structure of §2), one obtains three facet functionals
`g₀, g₁, g₂` with thresholds `c₀, c₁, c₂` defining the region around the middle
block `X (σ b)`:

* `g₀` strictly separates `conv (X (σ b))` from `conv (⋃_{j ≠ b} X (σ j))`
  (strict Hahn–Banach via `CollectionConvex (X ∘ σ)`);
* `g₁` and `g₂` come from `prop_2_7` applied to the subfamily `X ∘ σ`, fed by
  the rep-level strict separations obtained by Hahn–Banach on the `hsplit`
  hull pairs with index triples `(a, b+1, c+1)` and `(a, b, c+1)`.

The collection hypotheses are pulled back along `σ`'s injectivity
(`twoSeparated_comp`, `collectionConvex_comp`).
-/

noncomputable section

open scoped Topology

/-- `TwoSeparated` pulls back along an order embedding of the index set. -/
private theorem twoSeparated_comp {k k₀ : ℕ} {X : Fin k₀ → Finset (Euc 3)}
    (hsep : TwoSeparated X) (σ : Fin k ↪o Fin k₀) :
    TwoSeparated (X ∘ σ) := by
  intro i j i' j' hii' hij' hji' hjj'
  exact hsep (σ i) (σ j) (σ i') (σ j')
    (σ.injective.ne hii') (σ.injective.ne hij')
    (σ.injective.ne hji') (σ.injective.ne hjj')

/-- `CollectionConvex` pulls back along an order embedding of the index set:
the union over `j ≠ i` of the subfamily sits inside the union over
`j' ≠ σ i` of the full family. -/
private theorem collectionConvex_comp {k k₀ : ℕ} {X : Fin k₀ → Finset (Euc 3)}
    (hconv : CollectionConvex X) (σ : Fin k ↪o Fin k₀) :
    CollectionConvex (X ∘ σ) := by
  intro i
  refine Disjoint.mono_right ?_ (hconv (σ i))
  rintro z ⟨j, hj, hzj⟩
  exact Set.mem_iUnion.mpr
    ⟨σ j, Set.mem_iUnion.mpr ⟨σ.injective.ne hj, hzj⟩⟩

/-- The `g₀` step: a single member `Y b` of a collection in convex position
can be strictly separated from the convex hull of the rest.  The functional
is nonzero because the two hulls are nonempty (there is another index `a`)
and take values separated by `u < v`. -/
private theorem exists_sep_single {k : ℕ} {Y : Fin k → Finset (Euc 3)}
    (hne : ∀ i, (Y i).Nonempty) (hconv : CollectionConvex Y)
    {a b : Fin k} (hab : a ≠ b) :
    ∃ g : Euc 3 →ₗ[ℝ] ℝ, ∃ c : ℝ, g ≠ 0 ∧
      (∀ y ∈ Y b, c < g y) ∧
      (∀ j : Fin k, j ≠ b → ∀ y ∈ Y j, g y < c) := by
  classical
  have hU : (⋃ j : Fin k, ⋃ _ : j ≠ b, (Y j : Set (Euc 3))) =
      ((Finset.univ.erase b).biUnion Y : Set (Euc 3)) := by
    ext z
    constructor
    · rintro ⟨j, hj, hzj⟩
      exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩,
          Finset.mem_coe.mp hzj⟩)
    · intro hz
      obtain ⟨j, hj, hzj⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hz)
      exact Set.mem_iUnion.mpr
        ⟨j, Set.mem_iUnion.mpr ⟨(Finset.mem_erase.mp hj).1,
          Finset.mem_coe.mpr hzj⟩⟩
  have hTcomp : IsCompact
      (convexHull ℝ (⋃ j : Fin k, ⋃ _ : j ≠ b, (Y j : Set (Euc 3)))) := by
    rw [hU]
    exact (((Finset.univ.erase b).biUnion Y).finite_toSet).isCompact_convexHull
      ℝ
  obtain ⟨f, u, v, hTlt, huv, hYb⟩ := geometric_hahn_banach_compact_closed
    (s := convexHull ℝ (⋃ j : Fin k, ⋃ _ : j ≠ b, (Y j : Set (Euc 3))))
    (t := convexHull ℝ ((Y b : Finset (Euc 3)) : Set (Euc 3)))
    (convex_convexHull ℝ _)
    hTcomp
    (convex_convexHull ℝ _)
    ((Y b).finite_toSet.isClosed_convexHull ℝ)
    (hconv b).symm
  refine ⟨f.toLinearMap, v, ?_, ?_, ?_⟩
  · intro hz
    obtain ⟨y0, hy0⟩ := hne b
    obtain ⟨y1, hy1⟩ := hne a
    have h0 : v < f y0 :=
      hYb y0 (subset_convexHull ℝ _ (Finset.mem_coe.mpr hy0))
    have h1 : f y1 < u := hTlt y1 (subset_convexHull ℝ _
      (Set.mem_iUnion.mpr ⟨a, Set.mem_iUnion.mpr ⟨hab,
        Finset.mem_coe.mpr hy1⟩⟩))
    have e0 : f y0 = 0 := by simpa using DFunLike.congr_fun hz y0
    have e1 : f y1 = 0 := by simpa using DFunLike.congr_fun hz y1
    linarith
  · intro y hy
    exact hYb y (subset_convexHull ℝ _ (Finset.mem_coe.mpr hy))
  · intro j hj y hy
    exact lt_trans (hTlt y (subset_convexHull ℝ _
      (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj,
        Finset.mem_coe.mpr hy⟩⟩))) huv

/-- The `g₁`/`g₂` step: a disjointness of the two rep-point hulls over index
sets `S`, `T` (which must cover `Fin k` and both be inhabited) produces a
nonzero plane `g` placing each whole `Y i` on the side dictated by the side of
the representative `x i` — Hahn–Banach at the rep level, then `prop_2_7`. -/
private theorem exists_plane_split {k : ℕ} {Y : Fin k → Finset (Euc 3)}
    (hne : ∀ i, (Y i).Nonempty)
    (hsep : TwoSeparated Y) (hconv : CollectionConvex Y)
    {x : Fin k → Euc 3} (hx : ∀ i, x i ∈ Y i)
    {S T : Finset (Fin k)}
    (hd : Disjoint
      (convexHull ℝ ((Finset.image x S) : Set (Euc 3)))
      (convexHull ℝ ((Finset.image x T) : Set (Euc 3))))
    (hpart : ∀ i, i ∈ S ∨ i ∈ T)
    {iP iQ : Fin k} (hiP : iP ∈ S) (hiQ : iQ ∈ T) :
    ∃ g : Euc 3 →ₗ[ℝ] ℝ, ∃ c : ℝ, g ≠ 0 ∧
      (∀ i ∈ S, ∀ y ∈ Y i, c < g y) ∧
      (∀ i ∈ T, ∀ y ∈ Y i, g y < c) := by
  classical
  obtain ⟨f, u, v, hB, huv, hA⟩ := geometric_hahn_banach_compact_closed
    (s := convexHull ℝ ((Finset.image x T) : Set (Euc 3)))
    (t := convexHull ℝ ((Finset.image x S) : Set (Euc 3)))
    (convex_convexHull ℝ _)
    ((Finset.image x T).finite_toSet.isCompact_convexHull ℝ)
    (convex_convexHull ℝ _)
    ((Finset.image x S).finite_toSet.isClosed_convexHull ℝ)
    hd.symm
  have hSmem : ∀ i, i ∈ S →
      x i ∈ convexHull ℝ ((Finset.image x S) : Set (Euc 3)) :=
    fun i hi ↦ subset_convexHull ℝ _ (Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  have hTmem : ∀ i, i ∈ T →
      x i ∈ convexHull ℝ ((Finset.image x T) : Set (Euc 3)) :=
    fun i hi ↦ subset_convexHull ℝ _ (Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  have hf : ∀ i, f.toLinearMap (x i) ≠ u := by
    intro i
    rcases hpart i with hi | hi
    · exact ne_of_gt (lt_trans huv (hA _ (hSmem i hi)))
    · exact ne_of_lt (hB _ (hTmem i hi))
  obtain ⟨g, c', hg⟩ := prop_2_7 Y hsep hconv x hx f.toLinearMap u hf
  refine ⟨g, c', ?_, ?_, ?_⟩
  · intro hz
    obtain ⟨y0, hy0⟩ := hne iP
    obtain ⟨y1, hy1⟩ := hne iQ
    have e0 : c' < g y0 :=
      (hg iP).1 (lt_trans huv (hA _ (hSmem iP hiP))) y0 hy0
    have e1 : g y1 < c' := (hg iQ).2 (hB _ (hTmem iQ hiQ)) y1 hy1
    have z0 : g y0 = 0 := by simp [hz]
    have z1 : g y1 = 0 := by simp [hz]
    linarith
  · exact fun i hi ↦ (hg i).1 (lt_trans huv (hA _ (hSmem i hi)))
  · exact fun i hi ↦ (hg i).2 (hB _ (hTmem i hi))

/-- **Proposition 3.1 region construction** (`exists_triple_planes`): three
facet functionals and thresholds such that `X (σ b)` lies in the region
`{g₀ > c₀, g₁ < c₁, g₂ > c₂}`, the "odd" blocks `{i < a} ∪ {b < i ≤ c}` lie
in `{g₀ < c₀, g₁ > c₁, g₂ > c₂}` and the remaining blocks
`{a ≤ i < b} ∪ {c < i}` lie in `{g₀ < c₀, g₁ < c₁, g₂ < c₂}`. -/
theorem exists_triple_planes
    {k k₀ : ℕ} {X : Fin k₀ → Finset (Euc 3)}
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
    ∃ g₀ g₁ g₂ : Euc 3 →ₗ[ℝ] ℝ, ∃ c₀ c₁ c₂ : ℝ,
      g₀ ≠ 0 ∧ g₁ ≠ 0 ∧ g₂ ≠ 0 ∧
      (∀ y ∈ X (σ b), c₀ < g₀ y ∧ g₁ y < c₁ ∧ c₂ < g₂ y) ∧
      (∀ i : Fin k, i < a ∨ (b < i ∧ i ≤ c) →
        ∀ y ∈ X (σ i), g₀ y < c₀ ∧ c₁ < g₁ y ∧ c₂ < g₂ y) ∧
      (∀ i : Fin k, (a ≤ i ∧ i < b) ∨ c < i →
        ∀ y ∈ X (σ i), g₀ y < c₀ ∧ g₁ y < c₁ ∧ g₂ y < c₂) := by
  classical
  have habv : a.val < b.val := hab
  have hbcv : b.val < c.val := hbc
  have hbk : b.val + 1 < k := by omega
  -- Pull the collection hypotheses back along `σ`.
  have hne' : ∀ i : Fin k, ((X ∘ σ) i).Nonempty := fun i ↦ hne (σ i)
  have hsep' : TwoSeparated (X ∘ σ) := twoSeparated_comp hsep σ
  have hconv' : CollectionConvex (X ∘ σ) := collectionConvex_comp hconv σ
  have hx' : ∀ i : Fin k, (x ∘ σ) i ∈ (X ∘ σ) i := fun i ↦ hx (σ i)
  -- `b + 1` and `c + 1` as `Fin k` elements.
  have hab' : a ≤ (⟨b.val + 1, hbk⟩ : Fin k) := by
    show a.val ≤ b.val + 1; omega
  have hbc' : (⟨b.val + 1, hbk⟩ : Fin k) ≤ ⟨c.val + 1, hck⟩ := by
    show b.val + 1 ≤ c.val + 1; omega
  have hbc'' : b ≤ (⟨c.val + 1, hck⟩ : Fin k) := by
    show b.val ≤ c.val + 1; omega
  -- The three functionals.
  obtain ⟨g₀, c₀, hg₀ne, hg₀b, hg₀o⟩ :=
    exists_sep_single hne' hconv' (ne_of_lt hab)
  obtain ⟨g₁, c₁, hg₁ne, hg₁P, hg₁Q⟩ :=
    exists_plane_split hne' hsep' hconv' hx'
      (hsplit a ⟨b.val + 1, hbk⟩ ⟨c.val + 1, hck⟩ hab' hbc')
      (fun i ↦ by
        rcases lt_or_ge i a with h | h
        · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl h⟩)
        rcases lt_or_ge i ⟨b.val + 1, hbk⟩ with h2 | h2
        · exact Or.inr
            (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl ⟨h, h2⟩⟩)
        rcases lt_or_ge i ⟨c.val + 1, hck⟩ with h3 | h3
        · exact Or.inl
            (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inr ⟨h2, h3⟩⟩)
        · exact Or.inr
            (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inr h3⟩))
      (iP := ⟨b.val + 1, hbk⟩) (iQ := b)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Or.inr ⟨le_refl _, by show b.val + 1 < c.val + 1; omega⟩⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Or.inl ⟨hab.le, by show b.val < b.val + 1; omega⟩⟩)
  obtain ⟨g₂, c₂, hg₂ne, hg₂P, hg₂Q⟩ :=
    exists_plane_split hne' hsep' hconv' hx'
      (hsplit a b ⟨c.val + 1, hck⟩ hab.le hbc'')
      (fun i ↦ by
        rcases lt_or_ge i a with h | h
        · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl h⟩)
        rcases lt_or_ge i b with h2 | h2
        · exact Or.inr
            (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl ⟨h, h2⟩⟩)
        rcases lt_or_ge i ⟨c.val + 1, hck⟩ with h3 | h3
        · exact Or.inl
            (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inr ⟨h2, h3⟩⟩)
        · exact Or.inr
            (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inr h3⟩))
      (iP := b) (iQ := a)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Or.inr ⟨le_refl _, by show b.val < c.val + 1; omega⟩⟩)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl ⟨le_refl _, hab⟩⟩)
  -- Index-set translations between the `hsplit` filters and the target ones.
  have hP₁ : ∀ i : Fin k, i < a ∨ (b < i ∧ i ≤ c) →
      i < a ∨ ((⟨b.val + 1, hbk⟩ : Fin k) ≤ i ∧ i < ⟨c.val + 1, hck⟩) := by
    intro i hi
    rcases hi with h | ⟨h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨?_, ?_⟩
      · show b.val + 1 ≤ i.val
        have : b.val < i.val := h1; omega
      · show i.val < c.val + 1
        have : i.val ≤ c.val := h2; omega
  have hQ₁ : ∀ i : Fin k, (a ≤ i ∧ i < b) ∨ c < i →
      (a ≤ i ∧ i < (⟨b.val + 1, hbk⟩ : Fin k)) ∨ ⟨c.val + 1, hck⟩ ≤ i := by
    intro i hi
    rcases hi with ⟨h1, h2⟩ | h
    · refine Or.inl ⟨h1, ?_⟩
      show i.val < b.val + 1
      have : i.val < b.val := h2; omega
    · refine Or.inr ?_
      show c.val + 1 ≤ i.val
      have : c.val < i.val := h; omega
  have hQ₁b : (a ≤ b ∧ b < (⟨b.val + 1, hbk⟩ : Fin k)) ∨
      ⟨c.val + 1, hck⟩ ≤ b :=
    Or.inl ⟨hab.le, by show b.val < b.val + 1; omega⟩
  have hP₂ : ∀ i : Fin k, i < a ∨ (b < i ∧ i ≤ c) →
      i < a ∨ (b ≤ i ∧ i < (⟨c.val + 1, hck⟩ : Fin k)) := by
    intro i hi
    rcases hi with h | ⟨h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1.le, ?_⟩
      show i.val < c.val + 1
      have : i.val ≤ c.val := h2; omega
  have hQ₂ : ∀ i : Fin k, (a ≤ i ∧ i < b) ∨ c < i →
      (a ≤ i ∧ i < b) ∨ (⟨c.val + 1, hck⟩ : Fin k) ≤ i := by
    intro i hi
    rcases hi with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      show c.val + 1 ≤ i.val
      have : c.val < i.val := h; omega
  have hP₂b : b < a ∨ (b ≤ b ∧ b < (⟨c.val + 1, hck⟩ : Fin k)) :=
    Or.inr ⟨le_refl _, by show b.val < c.val + 1; omega⟩
  refine ⟨g₀, g₁, g₂, c₀, c₁, c₂, hg₀ne, hg₁ne, hg₂ne, ?_, ?_, ?_⟩
  · intro y hy
    exact ⟨hg₀b y hy,
      hg₁Q b (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hQ₁b⟩) y hy,
      hg₂P b (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hP₂b⟩) y hy⟩
  · intro i hi y hy
    have hib : i ≠ b := by
      rcases hi with h | ⟨h1, -⟩
      · exact ne_of_lt (h.trans hab)
      · exact ne_of_gt h1
    exact ⟨hg₀o i hib y hy,
      hg₁P i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hP₁ i hi⟩) y hy,
      hg₂P i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hP₂ i hi⟩) y hy⟩
  · intro i hi y hy
    have hib : i ≠ b := by
      rcases hi with ⟨-, h2⟩ | h
      · exact ne_of_lt h2
      · exact ne_of_gt (hbc.trans h)
    exact ⟨hg₀o i hib y hy,
      hg₁Q i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hQ₁ i hi⟩) y hy,
      hg₂Q i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hQ₂ i hi⟩) y hy⟩

end
