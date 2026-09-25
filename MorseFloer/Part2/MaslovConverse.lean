import MorseFloer.Part2.SymplecticLoops
import MorseFloer.Part2.SymplecticComponents

/-!
# Admissible paths with the same Maslov index are homotopic (Proposition 7.2.1, converse)

Let `ψ₀`, `ψ₁` be admissible paths with the same index. By the sign clause their endpoints lie in
the same component `Sp(2n)±` of `Sp(2n)⋆`, which is path-connected (Proposition 7.1.4); moving the
endpoint of `ψ₀` to that of `ψ₁` along a path `γ` in that component is a homotopy in `S`. The two
paths now have the same ends, and the angle of `ρ` changes by the same amount along them: along
`ψ₀` then `γ` it changes by `θ₀(1) + ρ̃(ψ₁ 1) - ρ̃(ψ₀ 1)` (`ρ̃` is a continuous angle of `ρ` on the
component), along `ψ₁` by `θ₁(1)`, and these agree because the indices do. So they are homotopic
with their ends fixed (`Part2/SymplecticLoops.lean`), which is a homotopy in `S`.
-/

open Matrix unitInterval

namespace MorseFloer
namespace MaslovIndex

open Chapter7 Rho

variable {n : ℕ}

/-! ### Homotopy in `S` is an equivalence relation -/

section Relation

variable {l : Type*} [DecidableEq l] [Fintype l]

theorem homotopicInS_refl {ψ : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ} (hψ : IsAdmissiblePath ψ) :
    HomotopicInS ψ ψ :=
  ⟨fun _ => ψ, hψ.continuous.comp continuous_snd, fun _ => hψ, rfl, rfl⟩

theorem HomotopicInS.symm {ψ₀ ψ₁ : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ} (h : HomotopicInS ψ₀ ψ₁) :
    HomotopicInS ψ₁ ψ₀ := by
  obtain ⟨H, hH, hadm, h0, h1⟩ := h
  have hc : Continuous fun p : ℝ × ℝ => ((1 : ℝ) - p.1, p.2) := by fun_prop
  exact ⟨fun s => H (1 - s), hH.comp hc, fun s => hadm _, by simpa using h1, by simpa using h0⟩

theorem HomotopicInS.trans {ψ₀ ψ₁ ψ₂ : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ} (h₁ : HomotopicInS ψ₀ ψ₁)
    (h₂ : HomotopicInS ψ₁ ψ₂) : HomotopicInS ψ₀ ψ₂ := by
  obtain ⟨H₁, hH₁, hadm₁, h₁0, h₁1⟩ := h₁
  obtain ⟨H₂, hH₂, hadm₂, h₂0, h₂1⟩ := h₂
  refine ⟨fun s => if s ≤ 1 / 2 then H₁ (2 * s) else H₂ (2 * s - 1), ?_, fun s => ?_, ?_, ?_⟩
  · have hc1 : Continuous fun p : ℝ × ℝ => ((2 : ℝ) * p.1, p.2) := by fun_prop
    have hc2 : Continuous fun p : ℝ × ℝ => ((2 : ℝ) * p.1 - 1, p.2) := by fun_prop
    have := Continuous.if_le (f' := fun p : ℝ × ℝ => H₁ (2 * p.1) p.2)
      (g' := fun p : ℝ × ℝ => H₂ (2 * p.1 - 1) p.2) (f := fun p => p.1)
      (g := fun _ => (1 / 2 : ℝ)) (hH₁.comp hc1) (hH₂.comp hc2) continuous_fst continuous_const
      (fun p (hp : p.1 = 1 / 2) => by
        have e : (2 : ℝ) * (1 / 2) = 1 := by norm_num
        show H₁ (2 * p.1) p.2 = H₂ (2 * p.1 - 1) p.2
        rw [hp, e, sub_self, h₁1, h₂0])
    refine this.congr fun p => ?_
    show (if p.1 ≤ 1 / 2 then _ else _) = (if p.1 ≤ 1 / 2 then H₁ (2 * p.1) else H₂ (2 * p.1 - 1)) p.2
    split_ifs <;> rfl
  · show IsAdmissiblePath (if s ≤ 1 / 2 then H₁ (2 * s) else H₂ (2 * s - 1))
    split_ifs
    · exact hadm₁ _
    · exact hadm₂ _
  · simp only [show (0 : ℝ) ≤ 1 / 2 by norm_num, if_true, mul_zero, h₁0]
  · simp only [show ¬ (1 : ℝ) ≤ 1 / 2 by norm_num, if_false, mul_one,
      show (2 : ℝ) - 1 = 1 by norm_num, h₂1]

/-- The clamp of `t` to `[0, 1]`. -/
noncomputable def clamp (t : ℝ) : ℝ := (Set.projIcc (0 : ℝ) 1 zero_le_one t : ℝ)

theorem continuous_clamp : Continuous clamp :=
  continuous_subtype_val.comp continuous_projIcc

theorem clamp_zero : clamp 0 = 0 := by simp [clamp]

theorem clamp_one : clamp 1 = 1 := by simp [clamp]

/-- An admissible path is homotopic to its values on `[0, 1]`, extended as constants. -/
theorem homotopicInS_clamp {ψ : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ} (hψ : IsAdmissiblePath ψ) :
    HomotopicInS ψ fun t => ψ (clamp t) := by
  refine ⟨fun s t => ψ ((1 - s) * t + s * clamp t), hψ.continuous.comp (by
      have := continuous_clamp; fun_prop), fun s => ⟨?_, fun t => hψ.mem _, ?_, ?_⟩, ?_, ?_⟩
  · exact hψ.continuous.comp (by have := continuous_clamp; fun_prop)
  · simp only [clamp_zero, mul_zero, add_zero]; exact hψ.start
  · simp only [clamp_one, mul_one, sub_add_cancel]; exact hψ.endpoint
  · funext t; simp
  · funext t; simp

end Relation

/-! ### The converse -/

section Converse

/-- The projection of `ℝ` onto `[0, 1]`. -/
noncomputable def projI (t : ℝ) : I := Set.projIcc 0 1 zero_le_one t

theorem continuous_projI : Continuous projI :=
  (continuous_projIcc : Continuous (Set.projIcc (0 : ℝ) 1 zero_le_one))

theorem coe_projI (t : ℝ) : (projI t : ℝ) = clamp t := rfl

theorem projI_of_le {x : ℝ} (hx : x ≤ 0) : projI x = 0 := Set.projIcc_of_le_left _ hx

theorem projI_of_ge {x : ℝ} (hx : 1 ≤ x) : projI x = 1 := Set.projIcc_of_right_le _ hx

theorem projI_of_mem {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : projI x = ⟨x, hx⟩ :=
  Set.projIcc_of_mem _ hx

theorem mem_of_mem_star {A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (h : A ∈ symplecticStar (Fin n)) : A ∈ Matrix.symplecticGroup (Fin n) ℝ :=
  (mem_symplecticStar_iff.1 h).1

theorem target_mem {A B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (γ : Path A B)
    (hγ : ∀ t, γ t ∈ symplecticStar (Fin n)) : B ∈ Matrix.symplecticGroup (Fin n) ℝ := by
  have := mem_of_mem_star (hγ 1); rwa [γ.target] at this

/-- The admissible path `ψ`, read on `[0, 1]` as a path in `Sp(2n)`. -/
def spPath {ψ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hψ : IsAdmissiblePath ψ) :
    Path (1 : SpT n) ⟨ψ 1, mem_of_mem_star hψ.endpoint⟩ where
  toFun t := ⟨ψ t, hψ.mem t⟩
  continuous_toFun := (hψ.continuous.comp continuous_subtype_val).subtype_mk _
  source' := Subtype.ext (by simp [hψ.start])
  target' := rfl

/-- A path of symplectic matrices, as a path in `Sp(2n)`. -/
def liftPath {A B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (γ : Path A B)
    (hγ : ∀ t, γ t ∈ Matrix.symplecticGroup (Fin n) ℝ) (hA : A ∈ Matrix.symplecticGroup (Fin n) ℝ)
    (hB : B ∈ Matrix.symplecticGroup (Fin n) ℝ) : Path (⟨A, hA⟩ : SpT n) ⟨B, hB⟩ where
  toFun t := ⟨γ t, hγ t⟩
  continuous_toFun := γ.continuous.subtype_mk _
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

variable {ψ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (hψ : IsAdmissiblePath ψ)
  {B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ} (γ : Path (ψ 1) B)
  (hγ : ∀ t, γ t ∈ symplecticStar (Fin n))

include hψ hγ in
/-- **Moving the endpoint along `γ`** is a homotopy in `S`. -/
theorem homotopicInS_extend :
    HomotopicInS (fun t => ψ (clamp t)) fun t =>
      ((spPath hψ).trans (liftPath γ (fun t => mem_of_mem_star (hγ t)) (mem_of_mem_star hψ.endpoint)
          (target_mem γ hγ))
        (projI t)).1 := by
  have hA₀u : IsUnit (ψ 1).det := Ne.isUnit (det_ne_zero_of_mem_symplecticGroup (mem_of_mem_star hψ.endpoint))
  have hA₀inv : (ψ 1)⁻¹ ∈ Matrix.symplecticGroup (Fin n) ℝ :=
    Chapter5.inv_mem_symplecticGroup (mem_of_mem_star hψ.endpoint)
  have hcl := continuous_clamp
  have hcl0 : ∀ x, 0 ≤ clamp x := fun x => (projI x).2.1
  have hcl1 : ∀ x, clamp x ≤ 1 := fun x => (projI x).2.2
  -- run along `ψ`, then along `γ` up to time `s`
  let G : ℝ → ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ := fun s t =>
    ψ (min (clamp t * (1 + clamp s)) 1) * (ψ 1)⁻¹ * γ (projI (clamp t * (1 + clamp s) - 1))
  have hGc : Continuous fun p : ℝ × ℝ => G p.1 p.2 := by
    have hu : Continuous fun p : ℝ × ℝ => clamp p.2 * (1 + clamp p.1) :=
      (hcl.comp continuous_snd).mul (continuous_const.add (hcl.comp continuous_fst))
    exact ((hψ.continuous.comp (hu.min continuous_const)).mul continuous_const).mul
      (γ.continuous.comp (continuous_projI.comp (hu.sub continuous_const)))
  have hGs : ∀ s, Continuous (G s) := fun s => by
    have hu : Continuous fun t : ℝ => clamp t * (1 + clamp s) := hcl.mul continuous_const
    exact ((hψ.continuous.comp (hu.min continuous_const)).mul continuous_const).mul
      (γ.continuous.comp (continuous_projI.comp (hu.sub continuous_const)))
  refine ⟨G, hGc, fun s => ⟨hGs s, fun t => ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (hψ.mem _) hA₀inv) (mem_of_mem_star (hγ _))
  · show ψ (min (clamp 0 * (1 + clamp s)) 1) * (ψ 1)⁻¹ * γ (projI (clamp 0 * (1 + clamp s) - 1)) = 1
    rw [clamp_zero, zero_mul, min_eq_left zero_le_one, hψ.start, zero_sub,
      projI_of_le (by norm_num), γ.source, Matrix.one_mul, Matrix.nonsing_inv_mul _ hA₀u]
  · show ψ (min (clamp 1 * (1 + clamp s)) 1) * (ψ 1)⁻¹ * γ (projI (clamp 1 * (1 + clamp s) - 1))
      ∈ symplecticStar (Fin n)
    rw [clamp_one, one_mul, min_eq_right (by linarith [hcl0 s]), add_sub_cancel_left,
      Matrix.mul_nonsing_inv _ hA₀u, Matrix.one_mul]
    exact hγ _
  · funext t
    show ψ (min (clamp t * (1 + clamp 0)) 1) * (ψ 1)⁻¹ * γ (projI (clamp t * (1 + clamp 0) - 1)) =
      ψ (clamp t)
    rw [clamp_zero, add_zero, mul_one, min_eq_left (hcl1 t), projI_of_le (by linarith [hcl1 t]),
      γ.source, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA₀u, Matrix.mul_one]
  · funext t
    show ψ (min (clamp t * (1 + clamp 1)) 1) * (ψ 1)⁻¹ * γ (projI (clamp t * (1 + clamp 1) - 1)) = _
    rw [clamp_one, Path.trans_apply]
    split_ifs with ht
    · rw [coe_projI] at ht
      rw [min_eq_left (by linarith), projI_of_le (by linarith), γ.source, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hA₀u, Matrix.mul_one]
      show ψ (clamp t * (1 + 1)) = ψ (2 * clamp t)
      ring_nf
    · rw [coe_projI] at ht
      push Not at ht
      rw [min_eq_right (by linarith), Matrix.mul_nonsing_inv _ hA₀u, Matrix.one_mul]
      show γ (projI (clamp t * (1 + 1) - 1)) = γ ⟨2 * clamp t - 1, _⟩
      rw [projI_of_mem ⟨by linarith, by linarith [hcl1 t]⟩]
      congr 1
      exact Subtype.ext (by simp only; ring)

include hγ in
/-- The angle of `ρ` along `ψ` followed by `γ`. -/
theorem exists_trans_lift {c : ℝ}
    (hc : ∀ t, Complex.exp ((rhoLift n (γ t) + c) * Complex.I) = rho n (γ t)) :
    ∃ θ : I → ℝ, Continuous θ ∧
      (∀ t, Complex.exp (θ t * Complex.I) = rho n ((spPath hψ).trans
        (liftPath γ (fun t => mem_of_mem_star (hγ t)) (mem_of_mem_star hψ.endpoint)
          (target_mem γ hγ)) t)) ∧
      θ 1 - θ 0 = angle n ψ 1 + rhoLift n B - rhoLift n (ψ 1) := by
  obtain ⟨c₀, z₀, e₀⟩ := angle_spec hψ
  have hLγ : Continuous fun t : I => rhoLift n (γ t) + c :=
    ((continuousOn_rhoLift n).comp_continuous γ.continuous hγ).add continuous_const
  have hγ0 : Complex.exp ((rhoLift n (γ 0) + c : ℝ) * Complex.I) = rho n (ψ 1) := by
    have := hc 0; rw [γ.source] at this ⊢; push_cast at this ⊢; exact this
  refine ⟨fun t => angle n ψ (projI (2 * t)) - (rhoLift n (γ 0) + c) +
    (rhoLift n (γ (projI (2 * t - 1))) + c), ?_, fun t => ?_, ?_⟩
  · have hm : Continuous fun t : I => (2 : ℝ) * (t : ℝ) :=
      continuous_const.mul continuous_subtype_val
    exact ((c₀.comp (continuous_subtype_val.comp (continuous_projI.comp hm))).sub
      continuous_const).add (hLγ.comp (continuous_projI.comp (hm.sub continuous_const)))
  · have hsplit : ∀ a b c : ℝ, Complex.exp (((a - b + c : ℝ) : ℂ) * Complex.I) =
        Complex.exp (a * Complex.I) * Complex.exp (c * Complex.I) / Complex.exp (b * Complex.I) :=
      fun a b c => by rw [← Complex.exp_add, ← Complex.exp_sub]; congr 1; push_cast; ring
    have hA : ‖rho n (ψ 1)‖ = 1 := norm_rho n _
    have hne : rho n (ψ 1) ≠ 0 := by intro h0; rw [h0, norm_zero] at hA; exact zero_ne_one hA
    rw [hsplit, hγ0, Path.trans_apply]
    split_ifs with ht
    · have hmem : 2 * (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [t.2.1], by linarith⟩
      rw [projI_of_mem hmem, projI_of_le (by linarith), e₀]
      have h0 : Complex.exp (((rhoLift n (γ 0) : ℝ) : ℂ) * Complex.I + (c : ℂ) * Complex.I) =
          rho n (ψ 1) := by
        have := hc 0
        rw [γ.source] at this ⊢
        rw [← this]; congr 1; ring
      have h0' : Complex.exp (((rhoLift n (γ 0) + c : ℝ) : ℂ) * Complex.I) = rho n (ψ 1) := by
        rw [← h0]; congr 1; push_cast; ring
      rw [h0', mul_div_cancel_right₀ _ hne]
      rfl
    · push Not at ht
      have hmem : 2 * (t : ℝ) - 1 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [t.2.2]⟩
      rw [projI_of_ge (by linarith), projI_of_mem hmem, Set.Icc.coe_one, e₀]
      have h1 : Complex.exp (((rhoLift n (γ ⟨2 * t - 1, hmem⟩) + c : ℝ) : ℂ) * Complex.I) =
          rho n (γ ⟨2 * t - 1, hmem⟩) := by
        rw [← hc]; congr 1; push_cast; ring
      rw [h1, mul_div_cancel_left₀ _ hne]
      rfl
  · have a1 : projI (2 * ((1 : I) : ℝ)) = 1 := projI_of_ge (by norm_num)
    have a0 : projI (2 * ((0 : I) : ℝ)) = 0 := projI_of_le (by norm_num)
    have b1 : projI (2 * ((1 : I) : ℝ) - 1) = 1 := projI_of_ge (by norm_num)
    have b0 : projI (2 * ((0 : I) : ℝ) - 1) = 0 := projI_of_le (by norm_num)
    show angle n ψ (projI (2 * ((1 : I) : ℝ))) - (rhoLift n (γ 0) + c) +
        (rhoLift n (γ (projI (2 * ((1 : I) : ℝ) - 1))) + c) -
      (angle n ψ (projI (2 * ((0 : I) : ℝ))) - (rhoLift n (γ 0) + c) +
        (rhoLift n (γ (projI (2 * ((0 : I) : ℝ) - 1))) + c)) = _
    rw [a1, a0, b1, b0, γ.source, γ.target, Set.Icc.coe_one, Set.Icc.coe_zero, z₀]
    ring

omit hψ in
/-- A homotopy of paths in `Sp(2n)`, ends fixed at `1` and at a point of `Sp(2n)⋆`, is a
homotopy in `S`. -/
theorem homotopicInS_of_homotopic {C : SpT n} (hC : (C : Matrix _ _ ℝ) ∈ symplecticStar (Fin n))
    {α β : Path (1 : SpT n) C} (h : α.Homotopic β) :
    HomotopicInS (fun t => (α (projI t)).1) fun t => (β (projI t)).1 := by
  obtain ⟨F⟩ := h
  refine ⟨fun s t => (F (projI s, projI t)).1, ?_, fun s => ⟨?_, fun t => (F _).2, ?_, ?_⟩,
    ?_, ?_⟩
  · exact continuous_subtype_val.comp (F.continuous.comp ((continuous_projI.comp
      continuous_fst).prodMk (continuous_projI.comp continuous_snd)))
  · exact continuous_subtype_val.comp (F.continuous.comp (continuous_const.prodMk continuous_projI))
  · show (F (projI s, projI 0)).1 = 1
    rw [projI_of_le le_rfl, F.source]; rfl
  · show (F (projI s, projI 1)).1 ∈ symplecticStar (Fin n)
    rw [projI_of_ge le_rfl, F.target]; exact hC
  · funext t
    show (F (projI 0, projI t)).1 = (α (projI t)).1
    rw [projI_of_le le_rfl, F.apply_zero]; rfl
  · funext t
    show (F (projI 1, projI t)).1 = (β (projI t)).1
    rw [projI_of_ge le_rfl, F.apply_one]; rfl

omit hψ γ hγ in
/-- **Proposition 7.2.1, the converse of homotopy invariance**: admissible paths with the same
Maslov index are homotopic in `S`. -/
theorem homotopicInS_of_maslovIndex_eq {ψ₀ ψ₁ : ℝ → Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ}
    (h₀ : IsAdmissiblePath ψ₀) (h₁ : IsAdmissiblePath ψ₁)
    (h : maslovIndex n ψ₀ = maslovIndex n ψ₁) : HomotopicInS ψ₀ ψ₁ := by
  -- the endpoints lie in the same component of `Sp(2n)⋆`
  have hs₀ := maslovIndex_sign h₀
  have hs₁ := maslovIndex_sign h₁
  rw [h] at hs₀
  have hsame : (0 < (ψ₀ 1 - 1).det ∧ 0 < (ψ₁ 1 - 1).det) ∨
      ((ψ₀ 1 - 1).det < 0 ∧ (ψ₁ 1 - 1).det < 0) := by
    rcases lt_or_gt_of_ne (mem_symplecticStar_iff.1 h₀.endpoint).2 with hn | hp
    · right; refine ⟨hn, lt_of_le_of_ne (not_lt.1 fun hc => ?_) (mem_symplecticStar_iff.1 h₁.endpoint).2⟩
      nlinarith [mul_pos_iff.1 hs₀, mul_pos_iff.1 hs₁]
    · left; refine ⟨hp, lt_of_le_of_ne (not_lt.1 fun hc => ?_) (mem_symplecticStar_iff.1 h₁.endpoint).2.symm⟩
      nlinarith [mul_pos_iff.1 hs₀, mul_pos_iff.1 hs₁]
  -- a path `γ` from `ψ₀ 1` to `ψ₁ 1` in that component, with a continuous angle of `ρ`
  obtain ⟨γ, hγ, c, hc⟩ : ∃ γ : Path (ψ₀ 1) (ψ₁ 1), (∀ t, γ t ∈ symplecticStar (Fin n)) ∧
      ∃ c : ℝ, ∀ t, Complex.exp ((rhoLift n (γ t) + c) * Complex.I) = rho n (γ t) := by
    rcases hsame with ⟨hp₀, hp₁⟩ | ⟨hn₀, hn₁⟩
    · obtain ⟨γ, hγ⟩ := (isPathConnected_symplecticPlus' (l := Fin n)).joinedIn _
        ⟨mem_of_mem_star h₀.endpoint, hp₀⟩ _ ⟨mem_of_mem_star h₁.endpoint, hp₁⟩
      exact ⟨γ, fun t => ⟨(hγ t).1, (hγ t).2.ne'⟩, 0, fun t => by
        simp only [Complex.ofReal_zero, add_zero]; exact exp_rhoLift_plus n (hγ t).1 (hγ t).2⟩
    · have : Nonempty (Fin n) := by
        by_contra hne
        rw [not_nonempty_iff] at hne
        have : (ψ₀ 1 - 1).det = 1 := Matrix.det_isEmpty
        linarith
      obtain ⟨γ, hγ⟩ := (isPathConnected_symplecticMinus' (l := Fin n)).joinedIn _
        ⟨mem_of_mem_star h₀.endpoint, hn₀⟩ _ ⟨mem_of_mem_star h₁.endpoint, hn₁⟩
      exact ⟨γ, fun t => ⟨(hγ t).1, (hγ t).2.ne⟩, Real.pi, fun t =>
        exp_rhoLift_minus n (hγ t).1 (hγ t).2⟩
  -- the two paths from `1` to `ψ₁ 1` have the same change of angle
  obtain ⟨θ, hθc, hθe, hθ⟩ := exists_trans_lift h₀ γ hγ hc
  obtain ⟨c₀, z₀, e₀⟩ := angle_spec h₀
  obtain ⟨c₁, z₁, e₁⟩ := angle_spec h₁
  have k₀ := (maslovIndex_spec h₀ c₀ z₀ e₀).1
  have k₁ := (maslovIndex_spec h₁ c₁ z₁ e₁).1
  rw [h] at k₀
  have hhom := homotopic_of_lifts _ (spPath h₁) hθc (θβ := fun t : I => angle n ψ₁ t)
    (c₁.comp continuous_subtype_val) hθe (fun t => e₁ t) (by
      simp only [Set.Icc.coe_one, Set.Icc.coe_zero, z₁]
      linarith)
  -- chain the homotopies
  exact HomotopicInS.trans (homotopicInS_clamp h₀) (HomotopicInS.trans
    (homotopicInS_extend h₀ γ hγ) (HomotopicInS.trans (homotopicInS_of_homotopic h₁.endpoint hhom)
      (HomotopicInS.symm (homotopicInS_clamp h₁))))

end Converse

end MaslovIndex
end MorseFloer
