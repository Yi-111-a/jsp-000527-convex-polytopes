import JSPProblem.Checkpoint

/-!
# JSP-000527 — Valtr's projection monotonicity

The inequality chain `ES_d(n) ≤ ES_{d-1}(n) ≤ … ≤ ES_2(n)` from eq. (1) of the
paper, formalized as

```
forcesConvex_succ : ForcesConvex d N n → ForcesConvex (d+1) N n
```

for `N ≥ d + 2`.  Proof sketch: given `X ⊆ ℝ^{d+1}` in general position with
`|X| ≥ N`, pick a direction `a` avoiding (i) every line `ℝ·(x−y)` and (ii) the
direction subspace of every `(d+1)`-element subset of `X`.  Projection along
`a` is injective on `X` and its image is again in general position; a convex
subset in the image lifts to a convex subset of `X` because
`f '' conv S ⊆ conv (f '' S)` for any linear `f`.

The finite-subspace-avoidance lemma (`exists_not_mem_forall_submodule`) is the
standard fact that a finite union of proper subspaces of a real vector space is
not the whole space.
-/

noncomputable section

variable {d : ℕ}

/-- Over an infinite field, a finite family of proper subspaces cannot cover
the whole space.  Proved by the usual `w₀ + t·u` sliding argument. -/
theorem exists_not_mem_forall_submodule {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    [Fintype ι] (U : ι → Submodule ℝ V) (hU : ∀ i, U i ≠ ⊤) : ∃ a : V, ∀ i, a ∉ U i := by
  classical
  induction ι using Finset.induction
  case empty => sorry
  sorry

/-- Projection along the vector `a`, onto the coordinate hyperplane
`{x : x i = 0}`: `f(x) = x − (xᵢ / aᵢ) • a`, read on coordinates `≠ i`. -/
def projAlong (a : Euc (d + 1)) (i : Fin (d + 1)) : Euc (d + 1) →ₗ[ℝ] Euc d where
  toFun x := fun j ↦ x (i.succAbove j) - (x i / a i) * a (i.succAbove j)
  map_add' x y := by
    ext j
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    ext j
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem projAlong_ker (a : Euc (d + 1)) (i : Fin (d + 1)) (hai : a i ≠ 0) :
    LinearMap.ker (projAlong a i) = ℝ ∙ a := by
  sorry

theorem forcesConvex_succ {N n : ℕ} (hN : d + 2 ≤ N) (h : ForcesConvex d N n) :
    ForcesConvex (d + 1) N n := by
  sorry

end
