import JSPProblem.CupsCaps

/-!
# JSP-000527 — the planar `K`-cap / convex-position dichotomy

This file develops the planar core of
Pohoata–Zakharov, *Convex polytopes from fewer points* (arXiv:2208.04878),
Proposition 2.1: for a compact convex `K ⊆ ℝ²` and a finite `Z ⊆ ℝ²` in
general position which is *pairwise `K`-free* — for every distinct `p, q ∈ Z`
the point `q` lies outside `convexHull ℝ (K ∪ {p})` — the Erdős–Szekeres bound

```
|Z| > (a + b - 4 choose a - 2)
```

forces either a `K`-cap of size `a` (a subset `A ⊆ Z` with every point outside
`conv (K ∪ (A ∖ {·}))`) or a convex-position subset of size `b`.

## Reduction to `DistinctX`

The theorem has no `DistinctX` hypothesis, but `cupsCaps` needs one.  A generic
horizontal shear `T_δ : (x, y) ↦ (x + δ·y, y)` is a linear automorphism of
`ℝ²`, hence preserves convexity, affine independence, compactness and all
membership hypotheses.  Choosing `δ` to avoid the finitely many "bad" slopes
of `Z` makes `T_δ '' Z` have pairwise distinct first coordinates.

## Status

The reduction to `DistinctX` is complete (`planar_dichotomy'` below).  The
combinatorial core `planar_dichotomy_aux` — the actual relative
cups–caps/dichotomy — is the genuinely difficult step; see the comments there
for a discussion of the mathematics and the obstruction to naively applying
`cupsCaps`.
-/

noncomputable section

open scoped Classical

namespace JSPProblem.PlanarDichotomy

/-! ### The horizontal shear and its basic properties -/

/-- The horizontal shear `(x, y) ↦ (x + δ·y, y)` as a linear map. -/
def shearX (δ : ℝ) : Euc 2 →ₗ[ℝ] Euc 2 where
  toFun v := WithLp.toLp 2 fun i : Fin 2 ↦ if i = 0 then v 0 + δ * v 1 else v 1
  map_add' v w := by
    apply PiLp.ext; intro i
    fin_cases i <;> simp [PiLp.add_apply]
    · ring
  map_smul' c v := by
    apply PiLp.ext; intro i
    fin_cases i <;> simp [PiLp.smul_apply, smul_eq_mul]
    · ring

theorem shearX_zero (δ : ℝ) (v : Euc 2) :
    (shearX δ v) 0 = v 0 + δ * v 1 := by
  simp [shearX]

theorem shearX_one (δ : ℝ) (v : Euc 2) :
    (shearX δ v) 1 = v 1 := by
  simp [shearX]

theorem shearX_injective (δ : ℝ) : Function.Injective (shearX δ) := by
  intro v w h
  have h1 : v 1 = w 1 := by
    have := congrArg (fun x : Euc 2 ↦ x 1) h
    simpa [shearX_one] using this
  have h0 : v 0 = w 0 := by
    have := congrArg (fun x : Euc 2 ↦ x 0) h
    simp [shearX_zero, h1] at this
    linarith
  apply PiLp.ext; intro i
  fin_cases i
  · exact h0
  · exact h1

/-- There is a shear parameter `δ` making all first coordinates of `Z`
distinct: for each pair `p ≠ q` the equation `(shearX δ p) 0 = (shearX δ q) 0`
has at most one solution in `δ`. -/
theorem exists_shearX_distinct (Z : Finset (Euc 2)) :
    ∃ δ : ℝ, ∀ p ∈ Z, ∀ q ∈ Z, (shearX δ p) 0 = (shearX δ q) 0 → p = q := by
  classical
  -- the finite set of "bad" parameters.
  set bad : Finset ℝ := (Z ×ˢ Z).image fun pq ↦
    if pq.1 1 = pq.2 1 then 0 else (pq.2 0 - pq.1 0) / (pq.1 1 - pq.2 1)
  have hb : (Set.univ : Set ℝ).Infinite := Set.infinite_univ
  obtain ⟨δ, -, hδ⟩ := Set.Infinite.exists_notMem_finset hb bad
  refine ⟨δ, fun p hp q hq heq ↦ ?_⟩
  by_contra hpq
  apply hδ
  rw [Finset.mem_image]
  refine ⟨(p, q), Finset.mem_product.2 ⟨hp, hq⟩, ?_⟩
  rw [shearX_zero, shearX_zero] at heq
  by_cases h1 : p 1 = q 1
  · -- then `p 0 = q 0` too, so `p = q`.
    exfalso; apply hpq
    rw [h1] at heq
    have h0 : p 0 = q 0 := by linarith
    apply PiLp.ext; intro i
    fin_cases i
    · exact h0
    · exact h1
  · have h2 : δ * (p 1 - q 1) = q 0 - p 0 := by linarith
    show (if p 1 = q 1 then (0 : ℝ) else (q 0 - p 0) / (p 1 - q 1)) = δ
    rw [ite_eq_right h1, ← h2, mul_div_cancel_right₀ _ (sub_ne_zero.2 h1)]

/-! ### Transferring the hypotheses through the shear -/

theorem inGeneralPosition_image_shearX {Z : Finset (Euc 2)}
    (hZ : InGeneralPosition (Z : Set (Euc 2))) (hZcard : 3 ≤ Z.card) (δ : ℝ) :
    InGeneralPosition ((Z.image (shearX δ)) : Set (Euc 2)) := by
  intro s' hs' hcard'
  -- preimage finset `s ⊆ Z` with `s.image (shearX δ) = s'`.
  set s : Finset (Euc 2) := Z.filter (fun x ↦ shearX δ x ∈ s') with hsdef
  have hsX : s ⊆ Z := Finset.filter_subset _ Z
  have hsimage : s.image (shearX δ) = s' := by
    ext z
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨x, hxs, rfl⟩
      exact (Finset.mem_filter.1 hxs).2
    · intro hz
      have hzX : z ∈ Z.image (shearX δ) := hs' (Finset.mem_coe.2 hz)
      rw [Finset.mem_image] at hzX
      obtain ⟨x, hxX, rfl⟩ := hzX
      exact ⟨x, Finset.mem_filter.2 ⟨hxX, hz⟩, rfl⟩
  have hscard : s.card = 3 := by
    have hinj : Set.InjOn (shearX δ) (s : Set (Euc 2)) :=
      fun _ _ _ _ h ↦ JSPProblem.PlanarDichotomy.shearX_injective δ h
    have hc := Finset.card_image_of_injOn hinj
    rw [hsimage, hcard'] at hc
    exact hc.symm
  have hsi : AffineIndependent ℝ (fun x : ↥s ↦ (x : Euc 2)) :=
    affineIndependent_of_inGeneralPosition hZ hZcard hsX (by omega)
  have hmap : AffineIndependent ℝ
      ((shearX δ).toAffineMap ∘ fun x : ↥s ↦ (x : Euc 2)) :=
    AffineIndependent.map' hsi _ (JSPProblem.PlanarDichotomy.shearX_injective δ)
  rw [LinearMap.coe_toAffineMap] at hmap
  -- the bijection `↥s ≃ ↥s'` induced by `shearX δ`.
  have hbij : Function.Bijective
      (fun x : ↥s ↦ (⟨shearX δ x, by
        rw [← hsimage]; exact Finset.mem_image.2 ⟨x, x.2, rfl⟩⟩ : ↥s')) := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact JSPProblem.PlanarDichotomy.shearX_injective δ (Subtype.ext_iff.1 hxy)
    · intro y
      have hy : (y : Euc 2) ∈ s.image (shearX δ) := hsimage.symm ▸ y.2
      obtain ⟨x, hxs, hxeq⟩ := Finset.mem_image.1 hy
      exact ⟨⟨x, hxs⟩, Subtype.ext hxeq⟩
  set e := Equiv.ofBijective _ hbij
  have hcomp : (fun x : ↥s' ↦ (x : Euc 2)) ∘ e =
      fun x : ↥s ↦ shearX δ x := rfl
  exact (affineIndependent_equiv e).1 (hcomp.symm ▸ hmap)

theorem pairwiseFree_image_shearX {K : Set (Euc 2)} {Z : Finset (Euc 2)}
    (hpair : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q →
      q ∉ convexHull ℝ (K ∪ ({p} : Set (Euc 2)))) (δ : ℝ) :
    ∀ p' ∈ Z.image (shearX δ), ∀ q' ∈ Z.image (shearX δ), p' ≠ q' →
      q' ∉ convexHull ℝ ((shearX δ '' K) ∪ ({p'} : Set (Euc 2))) := by
  intro p' hp' q' hq' hne hmem
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hp'
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hq'
  have hpq : p ≠ q := fun e ↦ hne (congrArg _ e)
  apply hpair p hp q hq hpq
  have himg : shearX δ '' (K ∪ ({p} : Set (Euc 2))) =
      (shearX δ '' K) ∪ ({shearX δ p} : Set (Euc 2)) := by
    rw [Set.image_union, Set.image_singleton]
  have hconv : shearX δ q ∈ shearX δ '' convexHull ℝ (K ∪ ({p} : Set _)) := by
    rw [LinearMap.image_convexHull, himg]
    exact hmem
  obtain ⟨w, hw, hweq⟩ := hconv
  rwa [shearX_injective δ hweq] at hw

/-! ### The combinatorial core

For the `DistinctX` case we would like to run the Erdős–Szekeres endpoint
induction relative to `K`.  The difficulty, documented at length in
`Caps3D.lean`, is that an ordinary cup or cap need not be a `K`-cap: for
`K` a segment, `Z = {(0,5),(5,4),(10,5)}` is pairwise `K`-free and a `3`-cup,
but `(5,4) ∈ conv (K ∪ {(0,5),(10,5)})`.

#### Structural reductions (proved in comments, not yet formalized)

*Carathéodory reduction.*  For `y ∈ Z` and `A ⊆ Z` finite,
`y ∈ conv (K ∪ (A ∖ {y}))` iff `y ∈ conv (A ∖ {y})` or there exist
`a, a' ∈ A ∖ {y}` with `y ∈ conv (K ∪ {a, a'})` — the other Carathéodory cases
are excluded by `Z ∩ K = ∅` and the pairwise condition.  Hence

```
A is a K-cap  ⟺  InConvexPosition A ∧ no triple {y,a,a'} ⊆ A has
                 y ∈ conv (K ∪ {a, a'}).
```

*Endpoint-chord reduction in the separated case.*  If `K` is separated from
`conv Z` (say `K` strictly below `Z`), then a cap `S` (in the `cupsCaps`
sense, i.e. a concave `x`-chain) is already a `K`-cap: the three
Carathéodory cases for `v ∈ conv (K ∪ S ∖ {v})` are excluded by
convex position of `S`, by pairwise `K`-freeness, and by `v ∉ K`.

#### The angular-order strategy (the intended proof)

The right coordinate system is *angular order around a point* `O ∈ K`.
Sort `Z` by direction from `O` (choosing `O` so the directions are distinct —
possible if `K` has nonempty interior, since `int K` is not contained in any
of the finitely many lines through pairs of `Z`).  For an angularly sorted
triple `a, m, b`, "m beyond the chord `ab` away from `O`" is a cross-sign
condition, so the cups–caps endpoint induction runs verbatim in angular
order, producing an `a`-term *angular cup* or a `b`-term *angular cap*.

*Key lemma (cap ⇒ `K`-cap in angular order).*  Let `C` be an angular cap
(every angularly-interior point beyond its bracketing chord, i.e. outside
`conv (O ∪ chord)`).  Then `C` is a `K`-cap.  Proof sketch: for `v ∈ C`,
Carathéodory reduces `v ∈ conv (K ∪ C ∖ {v})` to
`v ∈ conv (C ∖ {v})` or `v ∈ conv {k, c₁, c₂}` for `k ∈ K`, `c₁, c₂ ∈ C ∖ {v}`.
The ray from `O` through `v` exits the triangle `conv{k,c₁,c₂}` at a point
`w` on one of its three edges, and `v` lies on the segment `O–w`:
- `w` on chord `c₁c₂`: `v ∈ conv (O ∪ {c₁,c₂})`, contradicting the angular
  cap condition;
- `w` on edge `cᵢk`: `v ∈ conv (O ∪ segment cᵢk) ⊆ conv (K ∪ {cᵢ})`,
  contradicting pairwise `K`-freeness;
- `v ∈ conv (C ∖ {v})` contradicts convex position of `C`;
- `v ∈ conv {k₁,k₂,k₃} ⊆ K` contradicts `v ∉ K` (from `hpair`).

Only `O ∈ K` is needed (not `int K`): `O` and `w` are both in the beak
`conv (K ∪ {cᵢ})`, hence so is the segment `Ow` by convexity.

*Remaining difficulties.*  (i) `Z` must have pairwise distinct directions
from `O`; for `dim K ≤ 1` (`K` a point or segment) a generic `O ∈ K` may not
exist when a pair-line of `Z` contains `K` — a separate degenerate argument
is needed.  (ii) A cyclic-order version of `cupsCaps_aux` is required:
angular order is not a linear functional order, so the existing induction
must be generalized (or a cut chosen and wrap-around triples handled).
(iii) Angular caps must be shown to be in `InConvexPosition` for the
`conv (C ∖ {v})` case above.

*Obstruction to the naive endpoint induction.*  In the `x`-order, the wing
case of `v ∈ conv{k,c₁,c₂}` produces only `v ∈ conv(K ∪ {c})` for a
chord-*interior* point `c`, which pairwise freeness does not forbid.  The
angular formulation fixes exactly this: the ray from `O` meets the triangle's
far boundary at a *vertex edge* `cᵢk` or the chord `c₁c₂`, never at a
chord-interior point. -/

theorem planar_dichotomy_aux {K : Set (Euc 2)} (hKc : Convex ℝ K)
    (hKk : IsCompact K)
    {Z : Finset (Euc 2)} (hZ : InGeneralPosition (Z : Set (Euc 2)))
    (hdx : DistinctX Z)
    (hpair : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q →
      q ∉ convexHull ℝ (K ∪ ({p} : Set (Euc 2))))
    {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hcard : (a + b - 4).choose (a - 2) < Z.card) :
    (∃ A ⊆ Z, A.card = a ∧
      ∀ y ∈ A, y ∉ convexHull ℝ (K ∪ ((A.erase y : Finset _) : Set _))) ∨
    (∃ B ⊆ Z, B.card = b ∧ InConvexPosition B) := by
  sorry

end JSPProblem.PlanarDichotomy

/-! ### The main theorem -/

theorem planar_dichotomy' {K : Set (Euc 2)} (hKc : Convex ℝ K)
    (hKk : IsCompact K)
    {Z : Finset (Euc 2)} (hZ : InGeneralPosition (Z : Set (Euc 2)))
    (hpair : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q →
      q ∉ convexHull ℝ (K ∪ ({p} : Set (Euc 2))))
    {a b : ℕ} (ha : 3 ≤ a) (hb : 3 ≤ b)
    (hcard : (a + b - 4).choose (a - 2) < Z.card) :
    (∃ A ⊆ Z, A.card = a ∧
      ∀ y ∈ A, y ∉ convexHull ℝ (K ∪ ((A.erase y : Finset _) : Set _))) ∨
    (∃ B ⊆ Z, B.card = b ∧ InConvexPosition B) := by
  classical
  obtain ⟨δ, hδ⟩ := JSPProblem.PlanarDichotomy.exists_shearX_distinct Z
  set T := JSPProblem.PlanarDichotomy.shearX δ with hT
  set Z' := Z.image T with hZ'
  set K' := T '' K with hK'
  have hinjZ : Set.InjOn T (Z : Set (Euc 2)) :=
    fun _ _ _ _ h ↦ JSPProblem.PlanarDichotomy.shearX_injective δ h
  have hcardZ' : Z'.card = Z.card := Finset.card_image_of_injOn hinjZ
  have hZcard : 3 ≤ Z.card := by
    have h2 : 2 ≤ (a + b - 4).choose (a - 2) := by
      calc 2 ≤ a - 1 := by omega
        _ = (a - 1).choose 1 := (Nat.choose_one_right _).symm
        _ = (a - 1).choose (a - 2) :=
            (Nat.choose_symm (show 1 ≤ a - 1 by omega)).symm
        _ ≤ (a + b - 4).choose (a - 2) :=
            Nat.choose_le_choose _ (by omega)
    omega
  have hdx' : DistinctX Z' := by
    intro p' hp' q' hq' heq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hp'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hq'
    exact congrArg T (hδ p hp q hq heq)
  have hZ'' : InGeneralPosition (Z' : Set (Euc 2)) :=
    JSPProblem.PlanarDichotomy.inGeneralPosition_image_shearX hZ hZcard δ
  have hKc' : Convex ℝ K' := hKc.linear_image T
  have hKk' : IsCompact K' := hKk.image T.continuous_of_finiteDimensional
  have hpair' : ∀ p' ∈ Z', ∀ q' ∈ Z', p' ≠ q' →
      q' ∉ convexHull ℝ (K' ∪ ({p'} : Set (Euc 2))) :=
    JSPProblem.PlanarDichotomy.pairwiseFree_image_shearX hpair δ
  have hcard' : (a + b - 4).choose (a - 2) < Z'.card := by
    rwa [hcardZ']
  obtain hA | hB := JSPProblem.PlanarDichotomy.planar_dichotomy_aux hKc' hKk' hZ'' hdx'
    hpair' ha hb hcard'
  · obtain ⟨A', hA'Z, hA'card, hcap⟩ := hA
    -- preimage finset `A ⊆ Z` with `A.image T = A'`.
    set A : Finset (Euc 2) := Z.filter (fun x ↦ T x ∈ A') with hAdef
    have hAX : A ⊆ Z := Finset.filter_subset _ Z
    have himg : A.image T = A' := by
      ext z
      simp only [hAdef, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨-, hxA'⟩, rfl⟩; exact hxA'
      · intro hz
        obtain ⟨x, hxX, rfl⟩ := Finset.mem_image.1 (hA'Z hz)
        exact ⟨x, ⟨hxX, hz⟩, rfl⟩
    have hAcard : A.card = a := by
      have hc := Finset.card_image_of_injOn
        (hinjZ.mono (Finset.coe_subset.2 hAX))
      rw [himg, hA'card] at hc
      exact hc.symm
    refine Or.inl ⟨A, hAX, hAcard, ?_⟩
    intro y hy hmem
    have hy' : T y ∈ A' := by
      rw [← himg]; exact Finset.mem_image.2 ⟨y, hy, rfl⟩
    apply hcap _ hy'
    have h1 : T y ∈ convexHull ℝ (T '' (K ∪ ((A.erase y : Finset _) : Set _))) := by
      rw [← LinearMap.image_convexHull]
      exact Set.mem_image_of_mem _ hmem
    have h2 : T '' (K ∪ ((A.erase y : Finset _) : Set _)) =
        K' ∪ ((A'.erase (T y) : Finset _) : Set _) := by
      rw [Set.image_union]
      congr 1
      · ext z
        simp only [Set.mem_image]
        constructor
        · rintro ⟨w, hw, rfl⟩
          rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
            Finset.mem_coe] at hw
          obtain ⟨hwA, hwy⟩ := hw
          rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
            Finset.mem_coe]
          refine ⟨?_, ?_⟩
          · rw [← himg]; exact Finset.mem_image.2 ⟨w, hwA, rfl⟩
          · intro h; apply hwy; exact hinjZ (Finset.mem_coe.2 (hAX hwA))
              (Finset.mem_coe.2 (hAX hy)) h
        · intro hz
          rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
            Finset.mem_coe] at hz
          obtain ⟨hzA', hzne⟩ := hz
          have hzA : z ∈ A.image T := by rwa [himg]
          obtain ⟨w, hwA, rfl⟩ := Finset.mem_image.1 hzA
          refine ⟨w, ?_, rfl⟩
          rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
            Finset.mem_coe]
          exact ⟨hwA, fun h ↦ hzne (congrArg T h)⟩
    rw [h2] at h1
    exact h1
  · obtain ⟨B', hB'Z, hB'card, hconv⟩ := hB
    set B : Finset (Euc 2) := Z.filter (fun x ↦ T x ∈ B') with hBdef
    have hBX : B ⊆ Z := Finset.filter_subset _ Z
    have himg : B.image T = B' := by
      ext z
      simp only [hBdef, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨-, hxB'⟩, rfl⟩; exact hxB'
      · intro hz
        obtain ⟨x, hxX, rfl⟩ := Finset.mem_image.1 (hB'Z hz)
        exact ⟨x, ⟨hxX, hz⟩, rfl⟩
    have hBcard : B.card = b := by
      have hc := Finset.card_image_of_injOn
        (hinjZ.mono (Finset.coe_subset.2 hBX))
      rw [himg, hB'card] at hc
      exact hc.symm
    refine Or.inr ⟨B, hBX, hBcard, ?_⟩
    intro y hy hmem
    have hy' : T y ∈ B' := by
      rw [← himg]; exact Finset.mem_image.2 ⟨y, hy, rfl⟩
    apply hconv _ hy'
    have h1 : T y ∈ convexHull ℝ (T '' ((B.erase y : Finset _) : Set _)) := by
      rw [← LinearMap.image_convexHull]
      exact Set.mem_image_of_mem _ hmem
    have h2 : T '' ((B.erase y : Finset _) : Set _) =
        ((B'.erase (T y) : Finset _) : Set _) := by
      ext z
      simp only [Set.mem_image]
      constructor
      · rintro ⟨w, hw, rfl⟩
        rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
          Finset.mem_coe] at hw
        obtain ⟨hwB, hwy⟩ := hw
        rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
          Finset.mem_coe]
        refine ⟨?_, ?_⟩
        · rw [← himg]; exact Finset.mem_image.2 ⟨w, hwB, rfl⟩
        · intro h; apply hwy; exact hinjZ (Finset.mem_coe.2 (hBX hwB))
            (Finset.mem_coe.2 (hBX hy)) h
      · intro hz
        rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
          Finset.mem_coe] at hz
        obtain ⟨hzB', hzne⟩ := hz
        have hzB : z ∈ B.image T := by rwa [himg]
        obtain ⟨w, hwB, rfl⟩ := Finset.mem_image.1 hzB
        refine ⟨w, ?_, rfl⟩
        rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
          Finset.mem_coe]
        exact ⟨hwB, fun h ↦ hzne (congrArg T h)⟩
    rw [h2] at h1
    exact h1

end
