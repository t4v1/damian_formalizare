import MorseFloer.Part2.RhoLiftContinuity
import MorseFloer.Part2.RhoBlockSum
import MorseFloer.Part2.MaslovPaths

/-!
# The Maslov index of an admissible path (Proposition 7.2.1, construction)

For an admissible path `ψ` (§7.1.c: `ψ 0 = Id`, `ψ 1 ∈ Sp(2n)⋆`) let `θ` be the continuous
lift of `t ↦ ρ(ψ t)` through `θ ↦ e^{iθ}` with `θ 0 = 0`, and `ρ̃` the lift of `ρ` of §7.3.d,
continuous on `Sp(2n)⋆` (Lemma 7.1.6). Since `e^{iρ̃(A)} = ρ(A) · sign det(A - Id)`, the
difference `ρ̃(ψ 1) - θ 1` is an integer multiple `k π` of `π`, and

  `maslovIndex n ψ = k - n`.

The signs are those forced by the normalisation of Proposition 7.2.1 in dimension two: for
`S = ± ε Id` the path `exp(tJS)` is the rotation `realForm (e^{± i t ε})`, with `θ 1 = ± ε` and
`ρ̃ = ε`, resp. `2π - ε`, so `k = 0`, resp. `2`, and the index is `-1`, resp. `1`; for
`S = ε diag(1, -1)` the eigenvalues are `e^{± t ε}`, `ρ ≡ 1`, `ρ̃ = π`, and the index is `0`.

Using the lift `ρ̃` on the endpoint replaces the book's connecting path `γ_A` from `ψ 1` to a
base point of its component: the two definitions agree because `ρ̃` is continuous on each
component.

Proved here, for this `maslovIndex`:

* `maslovIndex_sign`: the sign of `det(ψ 1 - Id)` is `(-1)^{μ(ψ) - n}`;
* `maslovIndex_eq_of_homotopicInS`: homotopic admissible paths have the same index — the
  homotopy is lifted through `ℝ × ℝ`, which is simply connected, and the index along it is a
  continuous integer;
* `maslovIndex_blockSum`: additivity under block sums, from `ρ(A ⊕ B) = ρ(A) ρ(B)` and the
  additivity of `ρ̃`.

The lifts come from Mathlib's lifting theorem for the covering `Circle.exp : ℝ → S¹`.
-/

open Matrix Topology

namespace MorseFloer
namespace MaslovIndex

open Chapter7 Rho SymplecticEigen

/-! ### Lifts through `θ ↦ e^{iθ}` -/

section Lift

/-- A continuous map to the unit circle of a simply connected, locally path-connected space
lifts through `θ ↦ e^{iθ}`, with a prescribed value at a point. -/
theorem exists_lift {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]
    [LocallyPathConnectedSpace X] {f : X → ℂ} (hf : Continuous f) (h1 : ∀ x, ‖f x‖ = 1)
    (x₀ : X) {θ₀ : ℝ} (h0 : Complex.exp (θ₀ * Complex.I) = f x₀) :
    ∃ F : X → ℝ, Continuous F ∧ F x₀ = θ₀ ∧ ∀ x, Complex.exp (F x * Complex.I) = f x := by
  let g : C(X, Circle) :=
    ⟨fun x => ⟨f x, mem_sphere_zero_iff_norm.2 (h1 x)⟩, hf.subtype_mk _⟩
  obtain ⟨F, ⟨hF0, hFp⟩, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts g x₀ θ₀
      (Circle.ext (by rw [Circle.coe_exp, h0]; rfl))
  refine ⟨F, F.continuous, hF0, fun x => ?_⟩
  have := congrArg (fun c : Circle => (c : ℂ)) (congrFun hFp x)
  rw [Function.comp_apply, Circle.coe_exp] at this
  exact this

/-- Two continuous lifts of the same map that agree at one point of a connected space agree
everywhere. -/
theorem lift_unique {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] {F G : X → ℝ}
    (hF : Continuous F) (hG : Continuous G)
    (h : ∀ x, Complex.exp (F x * Complex.I) = Complex.exp (G x * Complex.I)) (x₀ : X)
    (h0 : F x₀ = G x₀) : F = G :=
  Circle.isCoveringMap_exp.eq_of_comp_eq hF hG
    (funext fun x => Circle.ext (by simp only [Function.comp_apply, Circle.coe_exp, h x])) x₀ h0

/-- A continuous function whose values are all integer multiples of `π` is constant. -/
theorem eq_of_exp_two_mul {X : Type*} [TopologicalSpace X] [PreconnectedSpace X] {F : X → ℝ}
    (hF : Continuous F) (h : ∀ x, ∃ k : ℤ, F x = k * Real.pi) (x₀ x : X) : F x = F x₀ := by
  have key := lift_unique (F := fun x => 2 * F x) (G := fun _ => 2 * F x₀)
    (continuous_const.mul hF) continuous_const (fun y => ?_) x₀ rfl
  · have : 2 * F x = 2 * F x₀ := congrFun key x
    linarith
  · obtain ⟨k, hk⟩ := h y
    obtain ⟨k₀, hk₀⟩ := h x₀
    have e : ∀ j : ℤ, Complex.exp (((2 * (j * Real.pi) : ℝ) : ℂ) * Complex.I) = 1 := fun j => by
      rw [Complex.exp_eq_one_iff]
      exact ⟨j, by push_cast; ring⟩
    rw [hk, hk₀, e, e]

end Lift

/-! ### The integer attached to an endpoint -/

section Endpoint

variable {n : ℕ}

theorem rho_one (n : ℕ) : rho n (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) = 1 := by
  have h1 : (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) = Matrix.fromBlocks 1 (-0) 0 1 := by
    rw [neg_zero, Matrix.fromBlocks_one]
  have hO : Chapter5.IsOrthogonalMat
      (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) ℝ) (-0) 0 1) := by
    rw [← h1, Chapter5.IsOrthogonalMat, Matrix.transpose_one, mul_one]
  rw [h1, rho_det_unitary n 1 0 hO]
  simp

/-- On `Sp(2n)⋆`, an angle of `ρ(A)` differs from `ρ̃(A)` by an integer multiple `k π` of
`π`, and the parity of `k` is the sign of `det(A - Id)`. -/
theorem exists_int_of_exp {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hA : A ∈ symplecticStar (Fin n)) {θ : ℝ} (hθ : Complex.exp (θ * Complex.I) = rho n A) :
    ∃ k : ℤ, θ - rhoLift n A = k * Real.pi ∧ 0 < (-1 : ℝ) ^ k * (A - 1).det := by
  -- two angles with the same exponential differ by `2 π m`
  have angle : ∀ φ : ℝ, Complex.exp (θ * Complex.I) = Complex.exp (φ * Complex.I) →
      ∃ m : ℤ, θ - φ = 2 * m * Real.pi := fun φ h => by
    obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
    refine ⟨m, ?_⟩
    have := congrArg Complex.im hm
    simp at this
    linarith
  rcases lt_or_gt_of_ne hA.2 with hdet | hdet
  · obtain ⟨m, hm⟩ := angle (rhoLift n A + Real.pi) (by
      rw [hθ, ← exp_rhoLift_minus n hA.1 hdet]; push_cast; rfl)
    refine ⟨2 * m + 1, by push_cast; linarith, ?_⟩
    rw [(odd_two_mul_add_one m).neg_one_zpow]
    linarith
  · obtain ⟨m, hm⟩ := angle (rhoLift n A) (by rw [hθ, exp_rhoLift_plus n hA.1 hdet])
    refine ⟨2 * m, by push_cast; linarith, ?_⟩
    rw [(even_two_mul m).neg_one_zpow, one_mul]
    exact hdet

end Endpoint

/-! ### The index -/

section Index

variable {n : ℕ}

theorem continuous_rho_comp {ψ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hψ : IsAdmissiblePath ψ) : Continuous fun t => rho n (ψ t) :=
  (continuousOn_rho n).comp_continuous hψ.continuous hψ.mem

/-- The lift of `t ↦ ρ(ψ t)` with value `0` at `0`. -/
theorem exists_angle {ψ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hψ : IsAdmissiblePath ψ) :
    ∃ F : ℝ → ℝ, Continuous F ∧ F 0 = 0 ∧ ∀ t, Complex.exp (F t * Complex.I) = rho n (ψ t) :=
  exists_lift (continuous_rho_comp hψ) (fun t => norm_rho n _) 0
    (by rw [hψ.start, rho_one]; simp)

open Classical in
/-- The angle of `ρ` along `ψ`: the continuous lift of `t ↦ ρ(ψ t)` vanishing at `0` (and
`0` if `ψ` is not admissible). -/
noncomputable def angle (n : ℕ) (ψ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) : ℝ → ℝ :=
  if h : ∃ F : ℝ → ℝ, Continuous F ∧ F 0 = 0 ∧ ∀ t, Complex.exp (F t * Complex.I) = rho n (ψ t)
  then h.choose else 0

theorem angle_spec {ψ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hψ : IsAdmissiblePath ψ) :
    Continuous (angle n ψ) ∧ angle n ψ 0 = 0 ∧
      ∀ t, Complex.exp (angle n ψ t * Complex.I) = rho n (ψ t) := by
  have h := exists_angle hψ
  rw [angle, dite_eq_left h]
  exact h.choose_spec

/-- Any continuous lift of `t ↦ ρ(ψ t)` vanishing at `0` is `angle n ψ`. -/
theorem eq_angle {ψ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hψ : IsAdmissiblePath ψ)
    {F : ℝ → ℝ} (hF : Continuous F) (hF0 : F 0 = 0)
    (hFe : ∀ t, Complex.exp (F t * Complex.I) = rho n (ψ t)) : F = angle n ψ := by
  obtain ⟨hc, h0, he⟩ := angle_spec hψ
  exact lift_unique hF hc (fun t => by rw [hFe, he]) 0 (by rw [hF0, h0])

/-- **The Maslov (Conley–Zehnder) index** of an admissible path: `(ρ̃(ψ 1) - θ 1) / π - n`,
with `θ` the angle of `ρ` along `ψ`. -/
noncomputable def maslovIndex (n : ℕ) (ψ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) : ℤ :=
  round ((rhoLift n (ψ 1) - angle n ψ 1) / Real.pi) - n

/-- The defining identity: for any continuous lift `F` of `ρ ∘ ψ` vanishing at `0`,
`(μ(ψ) + n) π = ρ̃(ψ 1) - F 1`, and `(-1)^{μ(ψ) - n}` is the sign of `det(ψ 1 - Id)`. -/
theorem maslovIndex_spec {ψ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hψ : IsAdmissiblePath ψ) {F : ℝ → ℝ} (hF : Continuous F) (hF0 : F 0 = 0)
    (hFe : ∀ t, Complex.exp (F t * Complex.I) = rho n (ψ t)) :
    rhoLift n (ψ 1) - F 1 = ((maslovIndex n ψ + n : ℤ) : ℝ) * Real.pi ∧
      0 < (-1 : ℝ) ^ (maslovIndex n ψ - n) * (ψ 1 - 1).det := by
  obtain ⟨k, hk, hsign⟩ := exists_int_of_exp hψ.endpoint (hFe 1)
  have hk' : rhoLift n (ψ 1) - F 1 = ((-k : ℤ) : ℝ) * Real.pi := by push_cast; linarith
  have hμ : maslovIndex n ψ + n = -k := by
    rw [maslovIndex, ← eq_angle hψ hF hF0 hFe, hk',
      mul_div_cancel_right₀ _ Real.pi_ne_zero, round_intCast, sub_add_cancel]
  refine ⟨by rw [hμ, hk'], ?_⟩
  -- `μ - n = k - 2 (k + n)` has the parity of `k`
  have hpar : (-1 : ℝ) ^ (maslovIndex n ψ - n) = (-1) ^ k := by
    rw [show maslovIndex n ψ - n = k + 2 * (-(k + n)) by omega, zpow_add₀ (by norm_num),
      _root_.zpow_mul, even_two.neg_one_zpow, _root_.one_zpow, mul_one]
  rw [hpar]
  exact hsign

/-- **Proposition 7.2.1, the sign clause**: `(-1)^{μ(ψ) - n} det(ψ 1 - Id) > 0`. -/
theorem maslovIndex_sign {ψ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (hψ : IsAdmissiblePath ψ) : 0 < (-1 : ℝ) ^ (maslovIndex n ψ - n) * (ψ 1 - 1).det :=
  let h := angle_spec hψ
  (maslovIndex_spec hψ h.1 h.2.1 h.2.2).2

/-- **Proposition 7.2.1, homotopy invariance**: admissible paths homotopic in `S` have the
same index. -/
theorem maslovIndex_eq_of_homotopicInS {ψ₀ ψ₁ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (h : HomotopicInS ψ₀ ψ₁) : maslovIndex n ψ₀ = maslovIndex n ψ₁ := by
  obtain ⟨H, hH, hadm, rfl, rfl⟩ := h
  -- lift `ρ ∘ H` over the plane, which is simply connected
  have hρH : Continuous fun p : ℝ × ℝ => rho n (H p.1 p.2) :=
    (continuousOn_rho n).comp_continuous hH fun p => (hadm p.1).mem p.2
  obtain ⟨G, hG, hG0, hGe⟩ := exists_lift hρH (fun p => norm_rho n _) (0, 0)
    (θ₀ := 0) (by rw [(hadm 0).start, rho_one]; simp)
  -- along `t = 0` the lift stays at `0`, since `ρ(H s 0) = ρ(Id) = 1`
  have hbase : ∀ s, G (s, 0) = 0 := fun s => by
    have := lift_unique (F := fun s => G (s, 0)) (G := fun _ => 0)
      (hG.comp (continuous_id.prodMk continuous_const)) continuous_const
      (fun s => by rw [hGe, (hadm s).start, rho_one]; simp) 0 hG0
    exact congrFun this s
  -- so each section of `G` is the angle of the corresponding path
  have hsec : ∀ s, rhoLift n (H s 1) - G (s, 1) = ((maslovIndex n (H s) + n : ℤ) : ℝ) * Real.pi :=
    fun s => (maslovIndex_spec (hadm s) (hG.comp (continuous_const.prodMk continuous_id))
      (hbase s) fun t => hGe (s, t)).1
  -- the index along the homotopy is a continuous integer, hence constant
  have hcont : Continuous fun s => rhoLift n (H s 1) - G (s, 1) :=
    ((continuousOn_rhoLift n).comp_continuous
      (hH.comp (continuous_id.prodMk continuous_const)) fun s => (hadm s).endpoint).sub
      (hG.comp (continuous_id.prodMk continuous_const))
  have hconst := eq_of_exp_two_mul hcont (fun s => ⟨_, hsec s⟩) 0 1
  rw [hsec, hsec] at hconst
  have h := Int.cast_injective (mul_right_cancel₀ Real.pi_ne_zero hconst)
  omega

end Index

/-! ### Additivity -/

section BlockSum

variable {m n : ℕ}

open Classical in
theorem liftTerm_eq_zero_of_not_mem {l : Type*} [DecidableEq l] [Fintype l]
    (M : Matrix (l ⊕ l) (l ⊕ l) ℂ) {μ : ℂ} (hμ : μ ∉ M.charpoly.roots) : liftTerm M μ = 0 := by
  have hcount : M.charpoly.roots.count μ = 0 := Multiset.count_eq_zero.2 hμ
  have hpos : mPos M μ = 0 := Nat.eq_zero_of_le_zero (hcount ▸ mPos_le_count M μ)
  have hsigma : sigma M μ = 0 := by rw [sigma, hpos, hcount]; simp
  unfold liftTerm
  rw [hcount, hpos, hsigma]
  split_ifs <;> simp

open Classical in
theorem liftTerm_blockSum (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (μ : ℂ) :
    liftTerm (cpx (blockSum A B)) μ = liftTerm (cpx A) μ + liftTerm (cpx B) μ := by
  unfold liftTerm
  rw [roots_blockSum, Multiset.count_add, mPos_blockSum, sigma_blockSum]
  split_ifs <;> push_cast <;> ring

open Classical in
theorem sum_liftTerm_eq {l : Type*} [DecidableEq l] [Fintype l] (M : Matrix (l ⊕ l) (l ⊕ l) ℂ)
    {s : Finset ℂ} (hs : M.charpoly.roots.toFinset ⊆ s) :
    ∑ μ ∈ s, liftTerm M μ = rhoLiftC M := by
  rw [rhoLiftC]
  exact (Finset.sum_subset hs fun μ _ hμ =>
    liftTerm_eq_zero_of_not_mem M (fun h => hμ (Multiset.mem_toFinset.2 h))).symm

/-- **The lift `ρ̃` is additive under block sums.** -/
theorem rhoLift_blockSum (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ)
    (B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) :
    rhoLift (m + n) (blockSum A B) = rhoLift m A + rhoLift n B := by
  classical
  unfold rhoLift
  rw [rhoLiftC]
  simp_rw [liftTerm_blockSum]
  rw [Finset.sum_add_distrib, sum_liftTerm_eq, sum_liftTerm_eq] <;>
    · rw [roots_blockSum, Multiset.toFinset_add]
      first
        | exact Finset.subset_union_left
        | exact Finset.subset_union_right

/-- **Proposition 7.2.1, additivity**: the index of a block sum of admissible paths is the sum
of their indices. -/
theorem maslovIndex_blockSum {ψ₀ : ℝ → Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℝ}
    {ψ₁ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (h₀ : IsAdmissiblePath ψ₀)
    (h₁ : IsAdmissiblePath ψ₁) :
    maslovIndex (m + n) (fun t => blockSum (ψ₀ t) (ψ₁ t)) =
      maslovIndex m ψ₀ + maslovIndex n ψ₁ := by
  obtain ⟨c₀, z₀, e₀⟩ := angle_spec h₀
  obtain ⟨c₁, z₁, e₁⟩ := angle_spec h₁
  have k₀ := (maslovIndex_spec h₀ c₀ z₀ e₀).1
  have k₁ := (maslovIndex_spec h₁ c₁ z₁ e₁).1
  -- the sum of the two angles is an angle of `ρ` along the block sum
  have k := (maslovIndex_spec (isAdmissiblePath_blockSum h₀ h₁)
    (F := fun t => angle m ψ₀ t + angle n ψ₁ t) (c₀.add c₁)
    (by simp [z₀, z₁]) fun t => by
      rw [rho_blockSum _ _ (h₀.mem t) (h₁.mem t), ← e₀, ← e₁, ← Complex.exp_add]
      push_cast; ring_nf).1
  simp only [rhoLift_blockSum] at k
  have : ((maslovIndex (m + n) (fun t => blockSum (ψ₀ t) (ψ₁ t)) + ↑(m + n) : ℤ) : ℝ) =
      ((maslovIndex m ψ₀ + m + (maslovIndex n ψ₁ + n) : ℤ) : ℝ) :=
    mul_right_cancel₀ Real.pi_ne_zero (by push_cast at k₀ k₁ k ⊢; linarith)
  have h := Int.cast_injective this
  omega

end BlockSum

end MaslovIndex
end MorseFloer
