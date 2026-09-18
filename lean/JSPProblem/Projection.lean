import JSPProblem.Checkpoint

/-!
# JSP-000527 — Valtr's projection monotonicity

The inequality chain `ES_d(n) ≤ ES_{d-1}(n) ≤ … ≤ ES_2(n)` from eq. (1) of the
paper, formalized as

```
forcesConvex_succ : ForcesConvex d N n → ForcesConvex (d+1) N n
```

for `N ≥ d + 2`.  Proof: given `X ⊆ ℝ^{d+1}` in general position with
`|X| ≥ N`, pick a direction `a` avoiding (i) every line `ℝ·(x−y)` for
`x y ∈ X`, (ii) the `vectorSpan` of every `(d+1)`-element subset of `X`, and
(iii) the last coordinate hyperplane.  The projection `projAlong a` along `a`
onto the first `d` coordinates has kernel `ℝ ∙ a`; it is injective on `X` and
its image is in general position (an affine dependence downstairs would put
`a` in the `vectorSpan` of a `(d+1)`-subset of `X`).  A convex subset of the
image lifts to `X` since `f '' conv s ⊆ conv (f '' s)` for linear `f`.

`exists_avoid_submodules` is the standard fact that a vector space over an
infinite field is not a finite union of proper subspaces.
-/

noncomputable section

open scoped Classical

variable {d : ℕ}

/-- A finite family of proper subspaces of a real vector space does not cover
it: there is a vector avoiding all of them.  Induction on the family: if `w₀`
avoids `s` but lies in `U`, then for `u ∉ U` the vector `w₀ + t·u` avoids `U`
for all `t ≠ 0`, and each `W ∈ s` excludes at most one value of `t`, so any `t`
outside a finite set works. -/
theorem exists_avoid_submodules {V : Type*} [AddCommGroup V] [Module ℝ V]
    (s : Finset (Submodule ℝ V)) (hs : ∀ U ∈ s, U ≠ ⊤) :
    ∃ a : V, ∀ U ∈ s, a ∉ U := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun U hU ↦ absurd hU (Finset.notMem_empty U)⟩
  | insert U s hU ih =>
      obtain ⟨w₀, hw₀⟩ := ih (fun W hW ↦ hs W (Finset.mem_insert_of_mem hW))
      by_cases hw : w₀ ∈ U
      · -- w₀ ∈ U: slide along u ∉ U.
        have hUtop : U ≠ ⊤ := hs U (Finset.mem_insert_self U s)
        obtain ⟨u, hu⟩ : ∃ u : V, u ∉ U := by
          by_contra h
          apply hUtop
          rw [eq_top_iff]
          intro x _
          by_contra hx
          exact h ⟨x, hx⟩
        -- each W ∈ s excludes at most one value of t.
        have key : ∀ W ∈ s, ({t : ℝ | w₀ + t • u ∈ W} : Set ℝ).Subsingleton := by
          intro W hW t₁ ht₁ t₂ ht₂
          by_contra hne
          have hsub : (t₁ - t₂) • u ∈ W := by
            have h := W.sub_mem ht₁ ht₂
            rwa [add_sub_add_comm, sub_self, zero_add, ← sub_smul] at h
          have ht : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr hne
          have huW : u ∈ W := by
            have h := W.smul_mem (t₁ - t₂)⁻¹ hsub
            rwa [smul_smul, inv_mul_cancel₀ ht, one_smul] at h
          have hwW : w₀ ∈ W := by
            have h := W.sub_mem ht₁ (W.smul_mem t₁ huW)
            rwa [add_sub_cancel_right] at h
          exact hw₀ W hW hwW
        -- choose t outside the finite set of bad values.
        set T : Finset ℝ := insert 0
          (s.biUnion fun W ↦
            if hW : W ∈ s then (key W hW).finite.toFinset else ∅) with hT
        obtain ⟨t, htT⟩ : ∃ t : ℝ, t ∉ T := Infinite.exists_notMem_finset T
        have ht0 : t ≠ 0 := fun h ↦ htT (by rw [h]; exact Finset.mem_insert_self _ _)
        have htW : ∀ W ∈ s, w₀ + t • u ∉ W := by
          intro W hW hmem
          apply htT
          apply Finset.mem_insert_of_mem
          rw [Finset.mem_biUnion]
          exact ⟨W, hW, by
            rw [dite_eq_left hW]
            exact ((key W hW).finite.mem_toFinset).2 hmem⟩
        refine ⟨w₀ + t • u, fun W hW ↦ ?_⟩
        rcases Finset.mem_insert.1 hW with rfl | hWs
        · intro hmem
          have htu : t • u ∈ W := by
            have h2 := W.sub_mem hmem hw
            rwa [add_sub_cancel_left] at h2
          exact hu ((W.smul_mem_iff ht0).1 htu)
        · exact htW W hWs
      · exact ⟨w₀, fun W hW ↦ by
          rcases Finset.mem_insert.1 hW with rfl | hWs
          · exact hw
          · exact hw₀ W hWs⟩

/-- Projection along the vector `a` onto the last-coordinate hyperplane, read
on the first `d` coordinates: `f(x)ⱼ = xⱼ − (x_last / a_last) · aⱼ`. -/
def projAlong (a : Euc (d + 1)) : Euc (d + 1) →ₗ[ℝ] Euc d where
  toFun x := WithLp.toLp 2 fun j : Fin d ↦
    x j.castSucc - (x (Fin.last d) / a (Fin.last d)) * a j.castSucc
  map_add' x y := by
    ext j
    simp only [PiLp.add_apply]
    ring
  map_smul' c x := by
    ext j
    simp only [PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring_nf

/-- The kernel of `projAlong a` is exactly `ℝ ∙ a` when `a_last ≠ 0`. -/
theorem projAlong_ker (a : Euc (d + 1)) (ha : a (Fin.last d) ≠ 0) :
    LinearMap.ker (projAlong a) = ℝ ∙ a := by
  ext x
  simp only [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hx
    have hxj : ∀ j : Fin d,
        x j.castSucc = (x (Fin.last d) / a (Fin.last d)) * a j.castSucc := by
      intro j
      have h := congr_arg (fun f : Euc d ↦ f j) hx
      simp only [projAlong, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
        PiLp.zero_apply] at h
      linarith
    refine ⟨x (Fin.last d) / a (Fin.last d), ?_⟩
    ext j'
    simp only [PiLp.smul_apply, smul_eq_mul]
    rcases Fin.eq_castSucc_or_eq_last j' with ⟨j, rfl⟩ | rfl
    · exact (hxj j).symm
    · exact div_mul_cancel₀ _ ha
  · rintro ⟨t, rfl⟩
    ext j
    simp only [projAlong, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
      PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply]
    rw [mul_div_cancel_right₀ _ ha, sub_self]

/-- `projAlong a` is surjective when `a_last ≠ 0`: the preimage of `y` is `y`
extended by a zero last coordinate. -/
theorem projAlong_surjective (a : Euc (d + 1)) (_ha : a (Fin.last d) ≠ 0) :
    Function.Surjective (projAlong a) := by
  intro y
  refine ⟨WithLp.toLp 2 (Fin.snoc (WithLp.ofLp y) 0), ?_⟩
  ext j
  simp only [projAlong, LinearMap.coe_mk, AddHom.coe_mk, WithLp.ofLp_toLp,
    Fin.snoc_castSucc, Fin.snoc_last]
  simp

/-- **Valtr's projection inequality** `ES_{d+1}(n) ≤ ES_d(n)` in forcing form:
for `N ≥ d + 2`, if `N` points in general position force an `n`-point convex
subset in `ℝ^d`, the same holds in `ℝ^{d+1}`. -/
theorem forcesConvex_succ {N n : ℕ} (hd : 1 ≤ d) (hN : d + 2 ≤ N)
    (h : ForcesConvex d N n) :
    ForcesConvex (d + 1) N n := by
  classical
  intro X hX hXN
  have hXcard : d + 2 ≤ X.card := hN.trans hXN
  have hXne : X.Nonempty := Finset.card_pos.1 (by omega)
  -- The finite family of proper subspaces to avoid.
  set F : Finset (Submodule ℝ (Euc (d + 1))) :=
    ((X ×ˢ X).image fun p : Euc (d+1) × Euc (d+1) ↦ ℝ ∙ (p.1 - p.2)) ∪
    ((X.powersetCard (d + 1)).image fun s : Finset (Euc (d+1)) ↦
      vectorSpan ℝ (s : Set (Euc (d+1)))) ∪
    {LinearMap.ker (EuclideanSpace.projₗ (Fin.last d) : Euc (d + 1) →ₗ[ℝ] ℝ)}
    with hFdef
  have hF : ∀ U ∈ F, U ≠ ⊤ := by
    intro U hU
    rw [hFdef] at hU
    rcases Finset.mem_union.1 hU with hAB | hC
    · rcases Finset.mem_union.1 hAB with hA | hB
      · -- ℝ ∙ (p.1 − p.2) has finrank ≤ 1 < d + 1.
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hA
        intro htop
        have hle : Module.finrank ℝ (ℝ ∙ (p.1 - p.2) : Submodule ℝ (Euc (d+1))) ≤ 1 := by
          simpa using finrank_span_le_card ({p.1 - p.2} : Set (Euc (d+1)))
        rw [htop, finrank_top, finrank_euclideanSpace_fin] at hle
        omega
      · -- vectorSpan of d+1 points has finrank ≤ d < d+1.
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hB
        rw [Finset.mem_powersetCard] at hs
        intro htop
        have hcard : Fintype.card (↥s : Type _) = d + 1 := by
          rw [Fintype.card_coe]; exact hs.2
        have hrange : Set.range (fun x : ↥s ↦ (x : Euc (d+1))) = (s : Set _) := by
          ext z
          constructor
          · rintro ⟨⟨w, hw⟩, rfl⟩
            exact Finset.mem_coe.2 hw
          · intro hz
            exact ⟨⟨z, Finset.mem_coe.1 hz⟩, rfl⟩
        have hle := finrank_vectorSpan_range_le ℝ
          (fun x : ↥s ↦ (x : Euc (d+1))) hcard
        rw [hrange] at hle
        rw [htop, finrank_top, finrank_euclideanSpace_fin] at hle
        omega
    · -- ker (projₗ last) ≠ ⊤ since `single last 1` maps to `1`.
      rw [Finset.mem_singleton] at hC
      subst hC
      intro htop
      have h1 : EuclideanSpace.projₗ (Fin.last d)
          (EuclideanSpace.single (Fin.last d) (1 : ℝ) : Euc (d + 1)) = 0 := by
        rw [← LinearMap.mem_ker, htop]
        exact Submodule.mem_top
      have h2 : EuclideanSpace.projₗ (Fin.last d)
          (EuclideanSpace.single (Fin.last d) (1 : ℝ) : Euc (d + 1)) = 1 := by
        simp only [PiLp.projₗ_apply, PiLp.single_eq_same]
      rw [h2] at h1
      exact one_ne_zero h1
  obtain ⟨a, ha⟩ := exists_avoid_submodules F hF
  -- Basic properties of `a`.
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
  have halast : a (Fin.last d) ≠ 0 := by
    intro h0
    have hmem : LinearMap.ker (EuclideanSpace.projₗ (Fin.last d) :
        Euc (d + 1) →ₗ[ℝ] ℝ) ∈ F := by
      rw [hFdef]
      exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
    have hz : a ∈ LinearMap.ker (EuclideanSpace.projₗ (Fin.last d) :
        Euc (d + 1) →ₗ[ℝ] ℝ) := by
      rw [LinearMap.mem_ker]
      simpa using h0
    exact ha _ hmem hz
  have hline : ∀ x ∈ X, ∀ y ∈ X, a ∉ ℝ ∙ (x - y) := by
    intro x hx y hy
    have hmem : ℝ ∙ (x - y) ∈ F := by
      rw [hFdef]
      refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
      exact Finset.mem_image.2 ⟨⟨x, y⟩, Finset.mem_product.2 ⟨hx, hy⟩, rfl⟩
    exact ha _ hmem
  have hvec : ∀ s : Finset (Euc (d+1)), s ⊆ X → s.card = d + 1 →
      a ∉ vectorSpan ℝ (s : Set (Euc (d+1))) := by
    intro s hs hcard
    have hmem : vectorSpan ℝ (s : Set (Euc (d+1))) ∈ F := by
      rw [hFdef]
      refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      exact Finset.mem_image.2 ⟨s, Finset.mem_powersetCard.2 ⟨hs, hcard⟩, rfl⟩
    exact ha _ hmem
  -- Injectivity of the projection on `X`.
  have hinj : Set.InjOn (projAlong a) (X : Set (Euc (d+1))) := by
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
  -- The projected set.
  set pX : Finset (Euc d) := X.image (projAlong a) with hpX
  have hpXcard : pX.card = X.card := Finset.card_image_of_injOn hinj
  -- General position of the projection.
  have hgp : InGeneralPosition (pX : Set (Euc d)) := by
    intro s' hs' hcard'
    -- preimage finset s ⊆ X with proj '' s = s'.
    set s : Finset (Euc (d+1)) := X.filter (fun x ↦ projAlong a x ∈ s') with hsdef
    have hsX : s ⊆ X := Finset.filter_subset _ X
    have hsimage : s.image (projAlong a) = s' := by
      ext z
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨x, hxs, rfl⟩
        exact (Finset.mem_filter.1 hxs).2
      · intro hz
        have hzX : z ∈ pX := hs' (Finset.mem_coe.2 hz)
        rw [hpX, Finset.mem_image] at hzX
        obtain ⟨x, hxX, rfl⟩ := hzX
        exact ⟨x, Finset.mem_filter.2 ⟨hxX, hz⟩, rfl⟩
    have hscard : s.card = d + 1 := by
      have hc := Finset.card_image_of_injOn
        (hinj.mono (Finset.coe_subset.2 hsX))
      rw [hsimage, hcard'] at hc
      exact hc.symm
    -- s is affinely independent (general position of X).
    have hsi : AffineIndependent ℝ (fun x : ↥s ↦ (x : Euc (d+1))) :=
      affineIndependent_of_inGeneralPosition hX hXcard hsX (by omega)
    have hsvs : Module.finrank ℝ (vectorSpan ℝ (s : Set (Euc (d+1)))) = d := by
      have hcard : Fintype.card (↥s : Type _) = d + 1 := by
        rw [Fintype.card_coe]; exact hscard
      have hrange : Set.range (fun x : ↥s ↦ (x : Euc (d+1))) = (s : Set _) := by
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
    have hlt : Module.finrank ℝ (vectorSpan ℝ (s' : Set (Euc d))) < d := by
      have hcard : Fintype.card (↥s' : Type _) = d + 1 := by
        rw [Fintype.card_coe]; exact hcard'
      have hrange : Set.range (fun x : ↥s' ↦ (x : Euc d)) = (s' : Set _) := by
        ext z
        constructor
        · rintro ⟨⟨w, hw⟩, rfl⟩
          exact Finset.mem_coe.2 hw
        · intro hz
          exact ⟨⟨z, Finset.mem_coe.1 hz⟩, rfl⟩
      by_contra hnotlt
      have hge : d ≤ Module.finrank ℝ (vectorSpan ℝ (s' : Set (Euc d))) :=
        le_of_not_gt hnotlt
      rw [← hrange] at hge
      exact hdep ((affineIndependent_iff_le_finrank_vectorSpan ℝ _ hcard).2 hge)
    have hV : vectorSpan ℝ (s' : Set (Euc d)) ≠ ⊤ := by
      intro htop
      rw [htop, finrank_top, finrank_euclideanSpace_fin] at hlt
      omega
    have horth : (vectorSpan ℝ (s' : Set (Euc d)))ᗮ ≠ ⊥ := by
      intro hbot
      exact hV (Submodule.orthogonal_eq_bot_iff.1 hbot)
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot horth
    -- The functional L = ⟪u, ·⟫ ∘ proj vanishes on vectorSpan s and on a.
    set f : Euc d →ₗ[ℝ] ℝ := innerₛₗ ℝ u with hf
    have hfv : ∀ v ∈ vectorSpan ℝ (s' : Set (Euc d)), f v = 0 := by
      intro v hv
      have h := (Submodule.mem_orthogonal' _ u).1 hu v hv
      rw [hf, innerₛₗ_apply_apply]
      exact h
    have hfu : f u ≠ 0 := by
      intro h0
      rw [hf, innerₛₗ_apply_apply] at h0
      exact hu0 (inner_self_eq_zero.1 h0)
    set L : Euc (d+1) →ₗ[ℝ] ℝ := f.comp (projAlong a) with hL
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
    have hLker : vectorSpan ℝ (s : Set (Euc (d+1))) ≤ LinearMap.ker L := by
      unfold vectorSpan
      rw [Submodule.span_le]
      intro w hw
      simp only [Set.mem_vsub] at hw
      obtain ⟨p, hp, q, hq, rfl⟩ := hw
      change L (p -ᵥ q) = 0
      have hp' : p ∈ s := Finset.mem_coe.1 hp
      have hq' : q ∈ s := Finset.mem_coe.1 hq
      have hproj : projAlong a p -ᵥ projAlong a q ∈
          vectorSpan ℝ (s' : Set (Euc d)) :=
        vsub_mem_vectorSpan ℝ
          (Finset.mem_coe.2 (Finset.mem_filter.1 hp').2)
          (Finset.mem_coe.2 (Finset.mem_filter.1 hq').2)
      rw [vsub_eq_sub] at hproj
      simp only [hL, LinearMap.comp_apply]
      rw [vsub_eq_sub, map_sub]
      exact hfv _ hproj
    -- dimensions force ker L = vectorSpan s, which contains a — contradiction.
    have hkerfin : Module.finrank ℝ (LinearMap.ker L) = d := by
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
    have heq : vectorSpan ℝ (s : Set (Euc (d+1))) = LinearMap.ker L :=
      Submodule.eq_of_le_of_finrank_eq hLker (hsvs.trans hkerfin.symm)
    have hamem : a ∈ vectorSpan ℝ (s : Set (Euc (d+1))) := by
      rw [heq, LinearMap.mem_ker]
      exact hLa
    exact hvec s hsX hscard hamem
  -- Apply the d-dimensional hypothesis to pX.
  obtain ⟨S', hS', hcardS', hconvS'⟩ := h pX hgp (by rw [hpXcard]; exact hXN)
  -- Lift S' to S ⊆ X.
  set S : Finset (Euc (d+1)) := X.filter (fun x ↦ projAlong a x ∈ S') with hS
  refine ⟨S, Finset.filter_subset (fun x ↦ projAlong a x ∈ S') X, ?_, ?_⟩
  · -- card S = card S' = n.
    have himg : S.image (projAlong a) = S' := by
      ext z
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨x, hxs, rfl⟩
        exact (Finset.mem_filter.1 hxs).2
      · intro hz
        have hzX : z ∈ pX := hS' hz
        rw [hpX, Finset.mem_image] at hzX
        obtain ⟨x, hxX, rfl⟩ := hzX
        exact ⟨x, Finset.mem_filter.2 ⟨hxX, hz⟩, rfl⟩
    have hc := Finset.card_image_of_injOn
      (hinj.mono (Finset.coe_subset.2
        (Finset.filter_subset (fun x ↦ projAlong a x ∈ S') X)))
    rw [himg, hcardS'] at hc
    exact hc.symm
  · -- S is in convex position: a convex dependence would project to one in S'.
    intro x hxS hc
    have hxS' : projAlong a x ∈ S' := (Finset.mem_filter.1 hxS).2
    have h1 : projAlong a x ∈
        (projAlong a) '' convexHull ℝ ((S.erase x : Finset _) : Set (Euc (d+1))) :=
      ⟨x, hc, rfl⟩
    rw [LinearMap.image_convexHull] at h1
    have h2 : (projAlong a) '' ((S.erase x : Finset _) : Set (Euc (d+1))) =
        ((S'.erase (projAlong a x) : Finset _) : Set (Euc d)) := by
      ext z
      simp only [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff,
        Set.mem_image, Finset.mem_coe]
      constructor
      · rintro ⟨y, ⟨hyS, hyx⟩, rfl⟩
        refine ⟨(Finset.mem_filter.1 hyS).2, ?_⟩
        intro hzyx
        apply hyx
        exact hinj (Finset.mem_coe.2 (Finset.mem_filter.1 hyS).1)
          (Finset.mem_coe.2 (Finset.mem_filter.1 hxS).1) hzyx
      · intro hz
        rcases hz with ⟨hzS', hzne⟩
        have hzX : z ∈ pX := hS' hzS'
        rw [hpX, Finset.mem_image] at hzX
        obtain ⟨y, hyX, rfl⟩ := hzX
        have hyS : y ∈ S := Finset.mem_filter.2 ⟨hyX, hzS'⟩
        have hyx : y ≠ x := fun h ↦ hzne (congrArg _ h)
        exact ⟨y, ⟨hyS, hyx⟩, rfl⟩
    rw [h2] at h1
    exact hconvS' _ hxS' h1

end
