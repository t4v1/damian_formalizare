import Mathlib

/-!
# The `C¹` flow of a globally Lipschitz `C¹` vector field

Mathlib's ODE library stops at the Picard–Lindelöf theorem (existence,
uniqueness, continuous dependence on the initial point).  The proof of
Darboux's theorem (Theorem 5.3.2) by Moser's path method needs more: the flow
of a vector field is `C¹` in the initial point, and its differential solves the
*variational equation* `∂ₜ Dψₜ = DX(ψₜ) ∘ Dψₜ`.  This file proves that, for a
`C¹` vector field on a Banach space which is globally Lipschitz.  (The field of
the Moser argument is only defined near a point, but a cut-off makes it globally
Lipschitz without changing it near that point.)

## The route

1. **The global flow** (`exists_flow_of_lipschitz`).  Picard–Lindelöf gives
   solutions on the uniform time interval `(−1/2K, 1/2K)` from every initial
   point, uniqueness lets two solutions be glued along their overlap, and an
   induction produces solutions on arbitrarily long intervals; the global
   solution through `x` is read off these, and the group law
   `φ (s + t) = φ s ∘ φ t` is uniqueness again.
2. **Differentiability for short times.**  Fix `x`, and let `A t = Df(φ t x)`.
   The linear equation `D' = A D`, `D 0 = Id` has a solution `D` on
   `[0, 1/2K]`, again by Picard–Lindelöf.  Along the compact curve
   `{φ t x}`, `Df` is uniformly continuous on a neighbourhood (Lebesgue's number
   lemma), so `f(y) − f(z) − Df(z)(y − z) = o(‖y − z‖)` uniformly in `z` on the
   curve.  Grönwall's inequality applied to `φ t (x + w) − φ t x − D t w` then
   shows it is `o(‖w‖)`: `D t` is the differential of `φ t` at `x`.  The same
   inequality, applied to `D` at two nearby initial points, gives the
   continuity of the differential, hence `φ t` is `C¹`.
3. **All times.**  The group law `φ t = φ (t/2) ∘ φ (t/2)` and the chain rule
   double the range of `t`; negative times are the flow of `−f`; and the
   variational equation at time `t` is the one at time `0` transported by
   `φ s = φ (s − t) ∘ φ t`.
-/

open Set Filter Topology Metric
open scoped NNReal

namespace MorseFloer
namespace FlowC1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-! ### Uniqueness -/

omit [CompleteSpace E] in
/-- Two solutions of `ẋ = f(x)` on an open interval which agree at one point of
it agree on the interval, for a globally Lipschitz `f`. -/
theorem eqOn_Ioo {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b) {α β : ℝ → E} (hα : ∀ t ∈ Ioo a b, HasDerivAt α (f (α t)) t)
    (hβ : ∀ t ∈ Ioo a b, HasDerivAt β (f (β t)) t) (h : α t₀ = β t₀) : EqOn α β (Ioo a b) :=
  ODE_solution_unique_of_mem_Ioo (v := fun _ => f) (s := fun _ => univ)
    (fun _ _ => hf.lipschitzOnWith) ht₀ (fun t ht => ⟨hα t ht, mem_univ _⟩)
    (fun t ht => ⟨hβ t ht, mem_univ _⟩) h

omit [CompleteSpace E] in
/-- Two global solutions which agree at one time are equal. -/
theorem eq_of_global {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) {α β : ℝ → E}
    (hα : ∀ t, HasDerivAt α (f (α t)) t) (hβ : ∀ t, HasDerivAt β (f (β t)) t) {t₀ : ℝ}
    (h : α t₀ = β t₀) : α = β :=
  ODE_solution_unique_univ (v := fun _ => f) (s := fun _ => univ) (t₀ := t₀)
    (fun _ => hf.lipschitzOnWith) (fun t => ⟨hα t, mem_univ _⟩)
    (fun t => ⟨hβ t, mem_univ _⟩) h

/-! ### Existence -/

/-- **Picard–Lindelöf with a uniform existence time.**  A `K`-Lipschitz field,
`K ≥ 1`, has a solution on `(−1/2K, 1/2K)` through every point: on the ball of
radius `a = 2‖f x‖/2K + 1` about `x` the field is bounded by `‖f x‖ + K a`, and
`(‖f x‖ + K a)/2K ≤ a`. -/
theorem exists_local {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) (hK : 1 ≤ K) (x : E) :
    ∃ α : ℝ → E, α 0 = x ∧
      ∀ t ∈ Ioo (-(1 / (2 * (K : ℝ)))) (1 / (2 * (K : ℝ))), HasDerivAt α (f (α t)) t := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  set T : ℝ := 1 / (2 * (K : ℝ)) with hT
  have hTpos : 0 < T := by positivity
  have hKT : (K : ℝ) * T = 1 / 2 := by rw [hT]; field_simp
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hTpos.le⟩
  set a : ℝ≥0 := ⟨2 * ‖f x‖ * T + 1, by positivity⟩ with ha
  set L : ℝ≥0 := ⟨‖f x‖ + K * (2 * ‖f x‖ * T + 1), by positivity⟩ with hL
  have hpl : IsPicardLindelof (fun _ : ℝ => f) (⟨0, h0⟩ : Icc (-T) T) x a 0 L K := by
    refine IsPicardLindelof.of_time_independent ?_ hf.lipschitzOnWith ?_
    · intro y hy
      have hy' : ‖y - x‖ ≤ 2 * ‖f x‖ * T + 1 := by
        rw [mem_closedBall, dist_eq_norm] at hy; exact hy
      have h1 := hf.dist_le_mul y x
      rw [dist_eq_norm, dist_eq_norm] at h1
      show ‖f y‖ ≤ ‖f x‖ + K * (2 * ‖f x‖ * T + 1)
      calc ‖f y‖ = ‖(f y - f x) + f x‖ := by rw [sub_add_cancel]
        _ ≤ ‖f y - f x‖ + ‖f x‖ := norm_add_le _ _
        _ ≤ K * ‖y - x‖ + ‖f x‖ := by linarith
        _ ≤ K * (2 * ‖f x‖ * T + 1) + ‖f x‖ := by gcongr
        _ = _ := by ring
    · show (‖f x‖ + K * (2 * ‖f x‖ * T + 1)) * max (T - 0) (0 - -T)
        ≤ (2 * ‖f x‖ * T + 1) - 0
      rw [sub_zero, zero_sub, neg_neg, max_self, sub_zero]
      have h2 : (‖f x‖ + K * (2 * ‖f x‖ * T + 1)) * T = 2 * ‖f x‖ * T + 1 / 2 := by
        linear_combination (2 * ‖f x‖ * T + 1) * hKT
      linarith
  obtain ⟨α, hα0, hαd⟩ :=
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt (mem_closedBall_self (by simp))
  refine ⟨α, hα0, fun t ht => ?_⟩
  exact (hαd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

omit [CompleteSpace E] in
/-- **Gluing.**  A solution `α` on `(a, b)` and a solution `β` on `(c, d)`, with
`a ≤ c < b ≤ d`, which agree at a point `t₁` of the overlap `(c, b)`, glue to a
solution on `(a, d)` which is `α` on `(a, b)` and `β` on `(c, d)`. -/
theorem glue {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) {a b c d t₁ : ℝ}
    (hac : a ≤ c) (hbd : b ≤ d) (ht₁ : t₁ ∈ Ioo c b)
    {α β : ℝ → E} (hα : ∀ t ∈ Ioo a b, HasDerivAt α (f (α t)) t)
    (hβ : ∀ t ∈ Ioo c d, HasDerivAt β (f (β t)) t) (h : α t₁ = β t₁) :
    ∃ γ : ℝ → E, (∀ t ∈ Ioo a d, HasDerivAt γ (f (γ t)) t) ∧
      (∀ t ∈ Ioo a b, γ t = α t) ∧ ∀ t ∈ Ioo c d, γ t = β t := by
  have hover : EqOn α β (Ioo c b) :=
    eqOn_Ioo hf ht₁ (fun t ht => hα t ⟨lt_of_le_of_lt hac ht.1, ht.2⟩)
      (fun t ht => hβ t ⟨ht.1, lt_of_lt_of_le ht.2 hbd⟩) h
  set γ : ℝ → E := fun t => if t < t₁ then α t else β t with hγ
  have hγα : ∀ t ∈ Ioo a b, γ t = α t := fun t ht => by
    rcases lt_or_ge t t₁ with hlt | hge
    · exact ite_eq_left hlt
    · show (if t < t₁ then α t else β t) = α t
      rw [ite_eq_right (not_lt.mpr hge)]
      exact (hover ⟨lt_of_lt_of_le ht₁.1 hge, ht.2⟩).symm
  have hγβ : ∀ t ∈ Ioo c d, γ t = β t := fun t ht => by
    rcases lt_or_ge t t₁ with hlt | hge
    · show (if t < t₁ then α t else β t) = β t
      rw [ite_eq_left hlt]
      exact hover ⟨ht.1, lt_trans hlt ht₁.2⟩
    · exact ite_eq_right (not_lt.mpr hge)
  refine ⟨γ, fun t ht => ?_, hγα, hγβ⟩
  rcases lt_or_ge t t₁ with hlt | hge
  · have hmem : t ∈ Ioo a b := ⟨ht.1, lt_trans hlt ht₁.2⟩
    have hev : γ =ᶠ[𝓝 t] α := by
      filter_upwards [isOpen_Ioo.mem_nhds hmem] with s hs
      exact hγα s hs
    rw [hγα t hmem]
    exact (hα t hmem).congr_of_eventuallyEq hev
  · have hmem : t ∈ Ioo c d := ⟨lt_of_lt_of_le ht₁.1 hge, ht.2⟩
    have hev : γ =ᶠ[𝓝 t] β := by
      filter_upwards [isOpen_Ioo.mem_nhds hmem] with s hs
      exact hγβ s hs
    rw [hγβ t hmem]
    exact (hβ t hmem).congr_of_eventuallyEq hev

/-- Solutions on the intervals `(−(T + nT/2), T + nT/2)`, `T = 1/2K`, by
induction: each step glues a local solution at the two ends. -/
theorem exists_Ioo_of_nat {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) (hK : 1 ≤ K) (x : E)
    (n : ℕ) : ∃ α : ℝ → E, α 0 = x ∧
      ∀ t ∈ Ioo (-(1 / (2 * (K : ℝ)) + n * (1 / (2 * (K : ℝ)) / 2)))
        (1 / (2 * (K : ℝ)) + n * (1 / (2 * (K : ℝ)) / 2)), HasDerivAt α (f (α t)) t := by
  set T : ℝ := 1 / (2 * (K : ℝ)) with hT
  have hTpos : 0 < T := by positivity
  -- a shifted local solution through any point at any time
  have hloc : ∀ (y : E) (c : ℝ), ∃ β : ℝ → E, β c = y ∧
      ∀ t ∈ Ioo (c - T) (c + T), HasDerivAt β (f (β t)) t := by
    intro y c
    obtain ⟨β₀, hβ₀, hβ₀d⟩ := exists_local hf hK y
    refine ⟨fun t => β₀ (t - c), by simp [hβ₀], fun t ht => ?_⟩
    have h := (hβ₀d (t - c) ⟨by linarith [ht.1], by linarith [ht.2]⟩).comp_sub_const t c
    exact h
  induction n with
  | zero =>
    obtain ⟨α, hα0, hαd⟩ := exists_local hf hK x
    refine ⟨α, hα0, fun t ht => hαd t ?_⟩
    rw [hT] at ht
    simpa using ht
  | succ n ih =>
    obtain ⟨α, hα0, hαd⟩ := ih
    set R : ℝ := T + n * (T / 2) with hR
    have hRT : T ≤ R := by
      have : (0 : ℝ) ≤ n * (T / 2) := by positivity
      linarith
    -- extend to the right
    obtain ⟨β, hβc, hβd⟩ := hloc (α (R - T / 2)) (R - T / 2)
    obtain ⟨γ, hγd, hγα, -⟩ := glue hf (a := -R) (b := R) (c := R - T / 2 - T)
      (d := R - T / 2 + T) (t₁ := R - T / 2) (by linarith) (by linarith)
      ⟨by linarith, by linarith⟩ hαd hβd hβc.symm
    have hγ0 : γ 0 = x := by rw [hγα 0 ⟨by linarith, by linarith⟩, hα0]
    -- extend to the left
    obtain ⟨β', hβ'c, hβ'd⟩ := hloc (γ (-R + T / 2)) (-R + T / 2)
    obtain ⟨δ, hδd, -, hδγ⟩ := glue hf (a := -R + T / 2 - T) (b := -R + T / 2 + T) (c := -R)
      (d := R - T / 2 + T) (t₁ := -R + T / 2) (by linarith) (by linarith)
      ⟨by linarith, by linarith⟩ hβ'd hγd hβ'c
    refine ⟨δ, ?_, fun t ht => hδd t ?_⟩
    · rw [hδγ 0 ⟨by linarith, by linarith⟩, hγ0]
    · have h1 : -R + T / 2 - T = -(T + (n + 1 : ℕ) * (T / 2)) := by push_cast; ring
      have h2 : R - T / 2 + T = T + (n + 1 : ℕ) * (T / 2) := by push_cast; ring
      rw [h1, h2]
      exact ht

/-- **Global existence** for a globally Lipschitz field. -/
theorem exists_global {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) (hK : 1 ≤ K) (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t, HasDerivAt γ (f (γ t)) t := by
  choose α hα0 hα using exists_Ioo_of_nat hf hK x
  set T : ℝ := 1 / (2 * (K : ℝ)) with hT
  have hTpos : 0 < T := by positivity
  set R : ℕ → ℝ := fun n => T + n * (T / 2) with hR
  have hRpos : ∀ n, 0 < R n := fun n => by
    have : (0 : ℝ) ≤ n * (T / 2) := by positivity
    simp only [hR]; linarith
  set N : ℝ → ℕ := fun t => ⌈2 * |t| / T⌉₊ with hN
  have hmem : ∀ t, t ∈ Ioo (-(R (N t))) (R (N t)) := fun t => by
    have h1 : 2 * |t| / T ≤ (N t : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hTpos] at h1
    have h3 : |t| < R (N t) := by simp only [hR]; linarith
    exact abs_lt.mp h3
  refine ⟨fun t => α (N t) t, hα0 _, fun t => ?_⟩
  have hev : (fun s => α (N s) s) =ᶠ[𝓝 t] α (N t) := by
    filter_upwards [isOpen_Ioo.mem_nhds (hmem t)] with s hs
    set m : ℝ := min (R (N s)) (R (N t)) with hm
    have hm0 : 0 < m := lt_min (hRpos _) (hRpos _)
    have hs1 : s ∈ Ioo (-m) m :=
      ⟨neg_lt.mpr (lt_min (neg_lt.mp (hmem s).1) (neg_lt.mp hs.1)), lt_min (hmem s).2 hs.2⟩
    exact eqOn_Ioo hf (a := -m) (b := m) (t₀ := 0) ⟨by linarith, hm0⟩
      (fun u hu => hα (N s) u ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hu.1,
        lt_of_lt_of_le hu.2 (min_le_left _ _)⟩)
      (fun u hu => hα (N t) u ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) hu.1,
        lt_of_lt_of_le hu.2 (min_le_right _ _)⟩)
      (by rw [hα0, hα0]) hs1
  exact (hα (N t) t (hmem t)).congr_of_eventuallyEq hev

/-- **The global flow** of a globally Lipschitz field, with the group law
`φ (s + t) = φ s ∘ φ t`, which is uniqueness applied to the translated curve. -/
theorem exists_flow_of_lipschitz {f : E → E} {K : ℝ≥0} (hf : LipschitzWith K f) (hK : 1 ≤ K) :
    ∃ φ : ℝ → E → E, (∀ x, φ 0 x = x) ∧ (∀ t x, HasDerivAt (fun s => φ s x) (f (φ t x)) t) ∧
      ∀ s t x, φ (s + t) x = φ s (φ t x) := by
  choose γ hγ0 hγ using exists_global hf hK
  refine ⟨fun t x => γ x t, fun x => hγ0 x, fun t x => hγ x t, fun s t x => ?_⟩
  have h1 : ∀ u, HasDerivAt (fun u => γ x (u + t)) (f (γ x (u + t))) u := fun u =>
    (hγ x (u + t)).comp_add_const u t
  exact congrFun (eq_of_global hf h1 (hγ (γ x t)) (t₀ := 0) (by simp [hγ0])) s

/-! ### Differentiability for short times -/

omit [CompleteSpace E] in
/-- A bound on the Grönwall function, for `K ≥ 1`, `ε ≥ 0` and `t ≥ 0`. -/
theorem gronwallBound_zero_le {K ε t : ℝ} (hK : 1 ≤ K) (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    gronwallBound 0 K ε t ≤ ε * Real.exp (K * t) := by
  rw [gronwallBound_of_K_ne_0 (by linarith)]
  simp only [zero_mul, zero_add]
  have h1 : 1 ≤ Real.exp (K * t) := Real.one_le_exp (by positivity)
  have h2 : ε / K ≤ ε := div_le_self hε hK
  calc ε / K * (Real.exp (K * t) - 1) ≤ ε * (Real.exp (K * t) - 1) :=
        mul_le_mul_of_nonneg_right h2 (by linarith)
    _ ≤ ε * Real.exp (K * t) := by nlinarith

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- A continuous map is uniformly continuous on a neighbourhood of a compact set
(Lebesgue's number lemma). -/
theorem exists_forall_norm_sub_lt_of_isCompact {F : Type*} [NormedAddCommGroup F] {g : E → F}
    (hg : Continuous g) {C : Set E} (hC : IsCompact C) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ C, ∀ y, dist y z < δ → ‖g y - g z‖ < ε := by
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric hC
    (c := fun i : E => {y | ‖g y - g i‖ < ε / 2})
    (fun i => isOpen_lt ((hg.sub continuous_const).norm) continuous_const)
    (fun z _ => mem_iUnion.mpr ⟨z, by simp [hε]⟩)
  refine ⟨δ, hδ, fun z hz y hy => ?_⟩
  obtain ⟨i, hi⟩ := hball z hz
  have h1 : ‖g y - g i‖ < ε / 2 := hi hy
  have h2 : ‖g z - g i‖ < ε / 2 := hi (mem_ball_self hδ)
  calc ‖g y - g z‖ = ‖(g y - g i) - (g z - g i)‖ := by rw [sub_sub_sub_cancel_right]
    _ ≤ ‖g y - g i‖ + ‖g z - g i‖ := norm_sub_le _ _
    _ < ε := by linarith

omit [CompleteSpace E] in
/-- The first-order expansion of a `C¹` map is uniform along a compact set. -/
theorem exists_forall_norm_sub_le_of_isCompact {f : E → E} (hf : ContDiff ℝ 1 f) {C : Set E}
    (hC : IsCompact C) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z ∈ C, ∀ y, dist y z < δ →
      ‖f y - f z - fderiv ℝ f z (y - z)‖ ≤ ε * ‖y - z‖ := by
  obtain ⟨δ, hδ, h⟩ :=
    exists_forall_norm_sub_lt_of_isCompact (hf.continuous_fderiv one_ne_zero) hC hε
  refine ⟨δ, hδ, fun z hz y hy => ?_⟩
  exact (convex_ball z δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun ξ _ => ((hf.differentiable one_ne_zero) ξ).hasFDerivAt.hasFDerivWithinAt)
    (fun ξ hξ => (h z hz ξ hξ).le) (mem_ball_self hδ) hy

/-- **The differential of the flow for short times.**  For a `C¹`, `K`-Lipschitz
field with flow `φ`, and `T = 1/2K`: at every `x` there is `D : ℝ → (E →L E)`
with `D 0 = Id`, solving the variational equation `D' = Df(φ t x) ∘ D` on
`[0, T]`, bounded by `e^{1/2}` there, and such that `D t` is the differential of
`φ t` at `x`. -/
theorem exists_fderiv_flow {f : E → E} {K : ℝ≥0} (hf : ContDiff ℝ 1 f) (hK : LipschitzWith K f)
    (hK1 : 1 ≤ K) {φ : ℝ → E → E} (hφ0 : ∀ x, φ 0 x = x)
    (hφd : ∀ t x, HasDerivAt (fun s => φ s x) (f (φ t x)) t) (x : E) :
    ∃ D : ℝ → (E →L[ℝ] E), D 0 = 1 ∧
      (∀ t ∈ Icc 0 (1 / (2 * (K : ℝ))), HasFDerivAt (φ t) (D t) x) ∧
      (∀ t ∈ Icc 0 (1 / (2 * (K : ℝ))), HasDerivWithinAt D ((fderiv ℝ f (φ t x)).comp (D t))
        (Icc 0 (1 / (2 * (K : ℝ)))) t) ∧
      (∀ t ∈ Icc 0 (1 / (2 * (K : ℝ))), ‖D t‖ ≤ Real.exp (1 / 2)) := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  set T : ℝ := 1 / (2 * (K : ℝ)) with hT
  have hTpos : 0 < T := by positivity
  have hKT : (K : ℝ) * T = 1 / 2 := by rw [hT]; field_simp
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hDf : ∀ y, ‖fderiv ℝ f y‖ ≤ K := fun y => (hdiff y).hasFDerivAt.le_of_lipschitz hK
  have hφc : ∀ y, Continuous fun s => φ s y := fun y =>
    continuous_iff_continuousAt.2 fun s => (hφd s y).continuousAt
  have hIcc : ∀ s ∈ Ico 0 T, Icc 0 T ∈ 𝓝[Ici s] s := fun s hs =>
    mem_nhdsWithin.mpr ⟨Iio T, isOpen_Iio, hs.2, fun u hu => ⟨le_trans hs.1 hu.2, hu.1.le⟩⟩
  set C₁ : ℝ := Real.exp (1 / 2) with hC₁
  have hC₁pos : 0 < C₁ := Real.exp_pos _
  have hexp : ∀ t ∈ Icc 0 T, Real.exp (K * t) ≤ C₁ := fun t ht => by
    rw [hC₁]
    apply Real.exp_le_exp.mpr
    calc (K : ℝ) * t ≤ K * T := by gcongr; exact ht.2
      _ = 1 / 2 := hKT
  -- the flow is Lipschitz for short times
  have hlip : ∀ t ∈ Icc 0 T, ∀ y, ‖φ t y - φ t x‖ ≤ C₁ * ‖y - x‖ := fun t ht y => by
    have h := dist_le_of_trajectories_ODE (v := fun _ => f) (K := K) (a := 0) (b := T)
      (fun _ => hK) (hφc y).continuousOn (fun s _ => (hφd s y).hasDerivWithinAt)
      (hφc x).continuousOn (fun s _ => (hφd s x).hasDerivWithinAt)
      (le_refl (dist (φ 0 y) (φ 0 x))) t ht
    rw [dist_eq_norm, dist_eq_norm, hφ0, hφ0, sub_zero] at h
    calc ‖φ t y - φ t x‖ ≤ ‖y - x‖ * Real.exp (K * t) := h
      _ ≤ ‖y - x‖ * C₁ := by gcongr; exact hexp t ht
      _ = C₁ * ‖y - x‖ := mul_comm _ _
  -- the coefficient `A t = Df(φ t x)` and the linear field `M ↦ A t ∘ M`
  set A : ℝ → (E →L[ℝ] E) := fun t => fderiv ℝ f (φ t x) with hA
  have hAc : Continuous A := (hf.continuous_fderiv one_ne_zero).comp (hφc x)
  have hAle : ∀ t, ‖A t‖ ≤ K := fun t => hDf _
  set G : ℝ → (E →L[ℝ] E) → (E →L[ℝ] E) := fun t M => (A t).comp M with hG
  have hGle : ∀ t M, ‖G t M‖ ≤ K * ‖M‖ := fun t M =>
    ((A t).opNorm_comp_le M).trans (mul_le_mul_of_nonneg_right (hAle t) (norm_nonneg _))
  have hGlip : ∀ t, LipschitzWith K (G t) := fun t => by
    refine LipschitzWith.of_dist_le_mul fun M N => ?_
    rw [dist_eq_norm, dist_eq_norm]
    show ‖(A t).comp M - (A t).comp N‖ ≤ K * ‖M - N‖
    rw [← ContinuousLinearMap.comp_sub]
    exact hGle t (M - N)
  have hpl : IsPicardLindelof G (⟨0, ⟨le_rfl, hTpos.le⟩⟩ : Icc 0 T) (1 : E →L[ℝ] E) 1 0
      (2 * K) K := by
    refine ⟨fun t _ => (hGlip t).lipschitzOnWith, fun M _ => ?_, fun t _ M hM => ?_, ?_⟩
    · exact (((ContinuousLinearMap.compL ℝ E E E).continuous.comp hAc).clm_apply
        continuous_const).continuousOn
    · have hM1 : ‖M‖ ≤ 2 := by
        rw [mem_closedBall, dist_eq_norm, NNReal.coe_one] at hM
        calc ‖M‖ = ‖(M - 1) + 1‖ := by rw [sub_add_cancel]
          _ ≤ ‖M - 1‖ + ‖(1 : E →L[ℝ] E)‖ := norm_add_le _ _
          _ ≤ 1 + 1 := add_le_add hM ContinuousLinearMap.norm_id_le
          _ = 2 := by norm_num
      show ‖G t M‖ ≤ ((2 * K : ℝ≥0) : ℝ)
      push_cast
      calc ‖G t M‖ ≤ K * ‖M‖ := hGle t M
        _ ≤ K * 2 := by gcongr
        _ = 2 * K := by ring
    · show ((2 * K : ℝ≥0) : ℝ) * max (T - 0) (0 - 0) ≤ ((1 : ℝ≥0) : ℝ) - ((0 : ℝ≥0) : ℝ)
      have hmax : max (T - 0) (0 - 0) = T := by rw [sub_zero, sub_zero, max_eq_left hTpos.le]
      rw [hmax]
      push_cast
      linarith [hKT]
  obtain ⟨D, hD0, hDd⟩ :=
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt (mem_closedBall_self (by simp))
  have hDc : ContinuousOn D (Icc 0 T) := fun t ht => (hDd t ht).continuousWithinAt
  have hDd' : ∀ s ∈ Ico 0 T, HasDerivWithinAt D (G s (D s)) (Ici s) s := fun s hs =>
    (hDd s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (hIcc s hs)
  -- `‖D t‖ ≤ C₁`
  have hDle : ∀ t ∈ Icc 0 T, ‖D t‖ ≤ C₁ := by
    intro t ht
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (δ := 1) (K := K) (ε := 0) hDc hDd'
      (by rw [hD0]; exact ContinuousLinearMap.norm_id_le)
      (fun s _ => by rw [add_zero]; exact hGle s (D s)) t ht
    rw [gronwallBound_ε0, one_mul, sub_zero] at h
    exact h.trans (hexp t ht)
  have hcurve : IsCompact ((fun s => φ s x) '' Icc 0 T) := isCompact_Icc.image (hφc x)
  refine ⟨D, hD0, fun t ht => ?_, fun t ht => hDd t ht, hDle⟩
  -- differentiability of `φ t` at `x`
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hexp'⟩ := exists_forall_norm_sub_le_of_isCompact hf hcurve
    (ε := c / (C₁ * C₁)) (by positivity)
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ / C₁, by positivity, fun y hy => ?_⟩
  rw [dist_eq_norm] at hy
  set w := y - x with hw
  have hwδ : C₁ * ‖w‖ < δ := by
    calc C₁ * ‖w‖ < C₁ * (δ / C₁) := by gcongr
      _ = δ := by field_simp
  -- the deviation `z`
  set z : ℝ → E := fun s => φ s y - φ s x - D s w with hz
  have hz0 : z 0 = 0 := by
    simp only [hz, hφ0, hD0, one_apply_eq_self, hw, sub_self]
  have hzc : ContinuousOn z (Icc 0 T) :=
    ((hφc y).sub (hφc x)).continuousOn.sub (hDc.clm_apply continuousOn_const)
  have hzd : ∀ s ∈ Ico 0 T, HasDerivWithinAt z
      (f (φ s y) - f (φ s x) - G s (D s) w) (Ici s) s := fun s hs => by
    have h1 := (hDd' s hs).clm_apply (hasDerivWithinAt_const s (Ici s) w)
    rw [map_zero, add_zero] at h1
    exact (((hφd s y).sub (hφd s x)).hasDerivWithinAt).sub h1
  have hzbound : ∀ s ∈ Ico 0 T, ‖f (φ s y) - f (φ s x) - G s (D s) w‖
      ≤ K * ‖z s‖ + c / (C₁ * C₁) * (C₁ * ‖w‖) := fun s hs => by
    have hs' := Ico_subset_Icc_self hs
    have hnear : dist (φ s y) (φ s x) < δ := by
      rw [dist_eq_norm]; exact lt_of_le_of_lt (hlip s hs' y) hwδ
    have h1 := hexp' (φ s x) (mem_image_of_mem _ hs') (φ s y) hnear
    have h2 : ‖A s (z s)‖ ≤ K * ‖z s‖ :=
      ((A s).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hAle s) (norm_nonneg _))
    have hid : f (φ s y) - f (φ s x) - G s (D s) w
        = (f (φ s y) - f (φ s x) - A s (φ s y - φ s x)) + A s (z s) := by
      simp only [hG, hz, ContinuousLinearMap.comp_apply, map_sub]; abel
    rw [hid]
    calc ‖(f (φ s y) - f (φ s x) - A s (φ s y - φ s x)) + A s (z s)‖
        ≤ ‖f (φ s y) - f (φ s x) - A s (φ s y - φ s x)‖ + ‖A s (z s)‖ := norm_add_le _ _
      _ ≤ c / (C₁ * C₁) * ‖φ s y - φ s x‖ + K * ‖z s‖ := add_le_add h1 h2
      _ ≤ c / (C₁ * C₁) * (C₁ * ‖w‖) + K * ‖z s‖ := by gcongr; exact hlip s hs' y
      _ = _ := by ring
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (δ := 0) (K := K)
    (ε := c / (C₁ * C₁) * (C₁ * ‖w‖)) hzc hzd (by rw [hz0, norm_zero]) hzbound t ht
  rw [sub_zero] at hgr
  have hgr2 := hgr.trans (gronwallBound_zero_le hK' (by positivity) ht.1)
  have hC₁ne : C₁ ≠ 0 := hC₁pos.ne'
  have hgr3 : ‖z t‖ ≤ c * ‖w‖ := by
    calc ‖z t‖ ≤ c / (C₁ * C₁) * (C₁ * ‖w‖) * Real.exp (K * t) := hgr2
      _ ≤ c / (C₁ * C₁) * (C₁ * ‖w‖) * C₁ := by gcongr; exact hexp t ht
      _ = c * ‖w‖ := by field_simp
  simpa [hz, hw] using hgr3

/-- **The flow is `C¹` for short times**, and the differential at time `0` moves
with velocity `Df`: `∂ₜ Dφₜ(x)|_{t=0⁺} = Df(x)`. -/
theorem contDiff_flow_of_mem {f : E → E} {K : ℝ≥0} (hf : ContDiff ℝ 1 f) (hK : LipschitzWith K f)
    (hK1 : 1 ≤ K) {φ : ℝ → E → E} (hφ0 : ∀ x, φ 0 x = x)
    (hφd : ∀ t x, HasDerivAt (fun s => φ s x) (f (φ t x)) t) :
    (∀ t ∈ Icc 0 (1 / (2 * (K : ℝ))), ContDiff ℝ 1 (φ t)) ∧
      ∀ x, HasDerivWithinAt (fun s => fderiv ℝ (φ s) x) (fderiv ℝ f x) (Ici 0) 0 := by
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  set T : ℝ := 1 / (2 * (K : ℝ)) with hT
  have hTpos : 0 < T := by positivity
  have hKT : (K : ℝ) * T = 1 / 2 := by rw [hT]; field_simp
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hDf : ∀ y, ‖fderiv ℝ f y‖ ≤ K := fun y => (hdiff y).hasFDerivAt.le_of_lipschitz hK
  have hφc : ∀ y, Continuous fun s => φ s y := fun y =>
    continuous_iff_continuousAt.2 fun s => (hφd s y).continuousAt
  have hIcc : ∀ s ∈ Ico 0 T, Icc 0 T ∈ 𝓝[Ici s] s := fun s hs =>
    mem_nhdsWithin.mpr ⟨Iio T, isOpen_Iio, hs.2, fun u hu => ⟨le_trans hs.1 hu.2, hu.1.le⟩⟩
  set C₁ : ℝ := Real.exp (1 / 2) with hC₁
  have hC₁pos : 0 < C₁ := Real.exp_pos _
  have hexp : ∀ t ∈ Icc 0 T, Real.exp (K * t) ≤ C₁ := fun t ht => by
    rw [hC₁]
    apply Real.exp_le_exp.mpr
    calc (K : ℝ) * t ≤ K * T := by gcongr; exact ht.2
      _ = 1 / 2 := hKT
  have hlip : ∀ x, ∀ t ∈ Icc 0 T, ∀ y, ‖φ t y - φ t x‖ ≤ C₁ * ‖y - x‖ := fun x t ht y => by
    have h := dist_le_of_trajectories_ODE (v := fun _ => f) (K := K) (a := 0) (b := T)
      (fun _ => hK) (hφc y).continuousOn (fun s _ => (hφd s y).hasDerivWithinAt)
      (hφc x).continuousOn (fun s _ => (hφd s x).hasDerivWithinAt)
      (le_refl (dist (φ 0 y) (φ 0 x))) t ht
    rw [dist_eq_norm, dist_eq_norm, hφ0, hφ0, sub_zero] at h
    calc ‖φ t y - φ t x‖ ≤ ‖y - x‖ * Real.exp (K * t) := h
      _ ≤ ‖y - x‖ * C₁ := by gcongr; exact hexp t ht
      _ = C₁ * ‖y - x‖ := mul_comm _ _
  choose D hD0 hDf' hDd hDle using exists_fderiv_flow hf hK hK1 hφ0 hφd
  have hfd : ∀ t ∈ Icc 0 T, ∀ x, fderiv ℝ (φ t) x = D x t := fun t ht x => (hDf' x t ht).fderiv
  have hDc : ∀ x, ContinuousOn (D x) (Icc 0 T) := fun x t ht => (hDd x t ht).continuousWithinAt
  have hDd' : ∀ x, ∀ s ∈ Ico 0 T,
      HasDerivWithinAt (D x) ((fderiv ℝ f (φ s x)).comp (D x s)) (Ici s) s := fun x s hs =>
    (hDd x s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (hIcc s hs)
  have hGlip : ∀ x s, LipschitzWith K fun M : E →L[ℝ] E => (fderiv ℝ f (φ s x)).comp M :=
    fun x s => by
      refine LipschitzWith.of_dist_le_mul fun M N => ?_
      rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.comp_sub]
      exact ((fderiv ℝ f (φ s x)).opNorm_comp_le _).trans
        (mul_le_mul_of_nonneg_right (hDf _) (norm_nonneg _))
  refine ⟨fun t ht => ?_, fun x => ?_⟩
  · rw [contDiff_one_iff_fderiv]
    refine ⟨fun x => (hDf' x t ht).differentiableAt, ?_⟩
    rw [continuous_iff_continuousAt]
    intro x
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hunif⟩ := exists_forall_norm_sub_lt_of_isCompact (hf.continuous_fderiv one_ne_zero)
      (isCompact_Icc.image (hφc x)) (ε := ε / (2 * C₁ * C₁)) (by positivity)
    refine ⟨δ / C₁, by positivity, fun y hy => ?_⟩
    rw [dist_eq_norm] at hy
    rw [hfd t ht, hfd t ht, dist_eq_norm]
    have hnear : ∀ s ∈ Icc 0 T,
        ‖fderiv ℝ f (φ s y) - fderiv ℝ f (φ s x)‖ < ε / (2 * C₁ * C₁) := fun s hs => by
      refine hunif (φ s x) (mem_image_of_mem _ hs) (φ s y) ?_
      rw [dist_eq_norm]
      calc ‖φ s y - φ s x‖ ≤ C₁ * ‖y - x‖ := hlip x s hs y
        _ < C₁ * (δ / C₁) := by gcongr
        _ = δ := by field_simp
    have hgb : ∀ s ∈ Ico 0 T, dist ((fderiv ℝ f (φ s y)).comp (D y s))
        ((fderiv ℝ f (φ s x)).comp (D y s)) ≤ ε / (2 * C₁ * C₁) * C₁ := fun s hs => by
      rw [dist_eq_norm, ← ContinuousLinearMap.sub_comp]
      calc ‖(fderiv ℝ f (φ s y) - fderiv ℝ f (φ s x)).comp (D y s)‖
          ≤ ‖fderiv ℝ f (φ s y) - fderiv ℝ f (φ s x)‖ * ‖D y s‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ε / (2 * C₁ * C₁) * C₁ :=
            mul_le_mul (hnear s (Ico_subset_Icc_self hs)).le (hDle y s (Ico_subset_Icc_self hs))
              (norm_nonneg _) (by positivity)
    have h := dist_le_of_approx_trajectories_ODE
      (v := fun s M => (fderiv ℝ f (φ s x)).comp M) (K := K) (a := 0) (b := T)
      (εf := 0) (εg := ε / (2 * C₁ * C₁) * C₁) (δ := 0)
      (fun s => hGlip x s) (hDc x) (hDd' x) (fun s _ => (dist_self _).le)
      (hDc y) (hDd' y) hgb (by rw [hD0 x, hD0 y, dist_self]) t ht
    rw [sub_zero, zero_add] at h
    have h2 := h.trans (gronwallBound_zero_le hK' (by positivity) ht.1)
    rw [dist_eq_norm, norm_sub_rev] at h2
    calc ‖D y t - D x t‖ ≤ ε / (2 * C₁ * C₁) * C₁ * Real.exp (K * t) := h2
      _ ≤ ε / (2 * C₁ * C₁) * C₁ * C₁ := by gcongr; exact hexp t ht
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  · have h := (hDd x 0 ⟨le_rfl, hTpos.le⟩).congr_of_mem (fun s hs => hfd s hs x)
      ⟨le_rfl, hTpos.le⟩
    rw [hφ0, hD0 x, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id] at h
    exact h.mono_of_mem_nhdsWithin (hIcc 0 ⟨le_rfl, hTpos⟩)

/-! ### All times -/

omit [CompleteSpace E] in
/-- The flow of `−f` is the time-reversed flow of `f`. -/
theorem flow_neg_eq {f : E → E} {K : ℝ≥0} (hK : LipschitzWith K f) {φ φ' : ℝ → E → E}
    (hφ0 : ∀ x, φ 0 x = x) (hφd : ∀ t x, HasDerivAt (fun s => φ s x) (f (φ t x)) t)
    (hφ'0 : ∀ x, φ' 0 x = x) (hφ'd : ∀ t x, HasDerivAt (fun s => φ' s x) (-f (φ' t x)) t)
    (t : ℝ) (x : E) : φ' t x = φ (-t) x := by
  have hK' : LipschitzWith K fun y => -f y :=
    LipschitzWith.of_dist_le_mul fun a b => by rw [dist_neg_neg]; exact hK.dist_le_mul a b
  have h1 : ∀ s, HasDerivAt (fun s => φ (-s) x) (-f (φ (-s) x)) s := fun s => by
    have h := (hφd (-s) x).scomp s (hasDerivAt_neg s)
    rw [neg_one_smul] at h
    exact h
  exact congrFun (eq_of_global hK' (fun s => hφ'd s x) h1 (t₀ := 0) (by simp [hφ'0, hφ0])) t

/-- **The `C¹` flow of a globally Lipschitz `C¹` vector field.**  There is a
map `φ : ℝ → E → E` with `φ 0 = id`, `∂ₜ φ t x = f (φ t x)`, the group law
`φ (s + t) = φ s ∘ φ t`, each `φ t` of class `C¹`, and the differential
`Dφ t (x)` solving the variational equation `∂ₜ Dφ t (x) = Df(φ t x) ∘ Dφ t (x)`. -/
theorem exists_flow {f : E → E} {K : ℝ≥0} (hf : ContDiff ℝ 1 f) (hK : LipschitzWith K f) :
    ∃ φ : ℝ → E → E, (∀ x, φ 0 x = x) ∧ (∀ t x, HasDerivAt (fun s => φ s x) (f (φ t x)) t) ∧
      (∀ s t x, φ (s + t) x = φ s (φ t x)) ∧ (∀ t, ContDiff ℝ 1 (φ t)) ∧
      ∀ t x, HasDerivAt (fun s => fderiv ℝ (φ s) x)
        ((fderiv ℝ f (φ t x)).comp (fderiv ℝ (φ t) x)) t := by
  set K' : ℝ≥0 := max K 1 with hK'
  have hK1 : 1 ≤ K' := le_max_right _ _
  have hKf : LipschitzWith K' f := hK.weaken (le_max_left _ _)
  have hKf' : LipschitzWith K' fun y => -f y :=
    LipschitzWith.of_dist_le_mul fun a b => by rw [dist_neg_neg]; exact hKf.dist_le_mul a b
  obtain ⟨φ, hφ0, hφd, hφg⟩ := exists_flow_of_lipschitz hKf hK1
  obtain ⟨φ', hφ'0, hφ'd, -⟩ := exists_flow_of_lipschitz hKf' hK1
  have hrev : ∀ t x, φ' t x = φ (-t) x := flow_neg_eq hKf hφ0 hφd hφ'0 hφ'd
  set T : ℝ := 1 / (2 * (K' : ℝ)) with hT
  have hTpos : 0 < T := by positivity
  obtain ⟨hC1, hD0⟩ := contDiff_flow_of_mem hf hKf hK1 hφ0 hφd
  obtain ⟨hC1', hD0'⟩ := contDiff_flow_of_mem hf.neg hKf' hK1 hφ'0 hφ'd
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  -- `C¹` for `|t| ≤ T`
  have hsmall : ∀ t, |t| ≤ T → ContDiff ℝ 1 (φ t) := fun t ht => by
    rcases le_or_gt 0 t with h | h
    · exact hC1 t ⟨h, (le_abs_self t).trans ht⟩
    · have hφt : φ t = φ' (-t) := funext fun x => by rw [hrev, neg_neg]
      rw [hφt]
      refine hC1' (-t) ⟨by linarith, ?_⟩
      rw [abs_of_neg h] at ht
      exact ht
  -- doubling the range with the group law
  have hdouble : ∀ n : ℕ, ∀ t, |t| ≤ 2 ^ n * T → ContDiff ℝ 1 (φ t) := by
    intro n
    induction n with
    | zero => intro t ht; exact hsmall t (by simpa using ht)
    | succ n ih =>
      intro t ht
      have ht2 : |t / 2| ≤ 2 ^ n * T := by
        rw [abs_div, abs_two]
        rw [pow_succ] at ht
        linarith
      have hsplit : φ t = φ (t / 2) ∘ φ (t / 2) := funext fun x => by
        rw [Function.comp_apply, ← hφg, add_halves]
      rw [hsplit]
      exact (ih _ ht2).comp (ih _ ht2)
  have hall : ∀ t, ContDiff ℝ 1 (φ t) := fun t => by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (|t| / T) one_lt_two
    rw [div_lt_iff₀ hTpos] at hn
    exact hdouble n t hn.le
  -- the variational equation at time `0`, from both sides
  have hvar0 : ∀ y, HasDerivAt (fun s => fderiv ℝ (φ s) y) (fderiv ℝ f y) 0 := by
    intro y
    have hR := hD0 y
    have hL' : HasDerivWithinAt (fun s => fderiv ℝ (φ' s) y) (fderiv ℝ (fun y => -f y) y)
        (Ici 0) (-0) := by
      rw [neg_zero]; exact hD0' y
    have h := hL'.scomp (0 : ℝ) (hasDerivAt_neg (0 : ℝ)).hasDerivWithinAt
      (fun s (hs : s ∈ Iic (0 : ℝ)) => Set.mem_Ici.mpr (neg_nonneg.mpr (Set.mem_Iic.mp hs)))
    have hfun : ((fun s => fderiv ℝ (φ' s) y) ∘ fun s : ℝ => -s) = fun s => fderiv ℝ (φ s) y :=
      funext fun s => by
        simp only [Function.comp_apply]
        have hφs : φ' (-s) = φ s := funext fun z => by rw [hrev, neg_neg]
        rw [hφs]
    have hval : (-1 : ℝ) • fderiv ℝ (fun y => -f y) y = fderiv ℝ f y := by
      have hneg : HasFDerivAt (fun y => -f y) (-fderiv ℝ f y) y := (hdiff y).hasFDerivAt.neg
      rw [hneg.fderiv, smul_neg, neg_one_smul, neg_neg]
    rw [hfun, hval] at h
    have hu := hR.union h
    rw [Ici_union_Iic] at hu
    exact hu.hasDerivAt univ_mem
  refine ⟨φ, hφ0, hφd, hφg, hall, fun t x => ?_⟩
  -- transport to time `t` with `φ s = φ (s − t) ∘ φ t`
  have hcomp : ∀ s, φ s = φ (s - t) ∘ φ t := fun s => funext fun z => by
    rw [Function.comp_apply, ← hφg, sub_add_cancel]
  have hfun : (fun s => fderiv ℝ (φ s) x)
      = fun s => (fderiv ℝ (φ (s - t)) (φ t x)).comp (fderiv ℝ (φ t) x) := funext fun s => by
    rw [hcomp s]
    exact fderiv_comp x ((hall _).differentiable one_ne_zero _)
      ((hall _).differentiable one_ne_zero _)
  have h0 : HasDerivAt (fun σ => fderiv ℝ (φ σ) (φ t x)) (fderiv ℝ f (φ t x)) (t - t) := by
    rw [sub_self]; exact hvar0 (φ t x)
  have h := (h0.comp_sub_const t t).clm_comp (hasDerivAt_const t (fderiv ℝ (φ t) x))
  rw [ContinuousLinearMap.comp_zero, add_zero] at h
  rw [hfun]
  exact h

end FlowC1
end MorseFloer
