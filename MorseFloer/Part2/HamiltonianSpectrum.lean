import MorseFloer.Part2.SymplecticConnected

/-!
# Hamiltonian matrices without the eigenvalue `1`

A real `2n × 2n` matrix `M` is *Hamiltonian* (infinitesimally symplectic) when
`MᵀJ + JM = 0`, i.e. `ω(Mx, y) = −ω(x, My)` for the standard symplectic form.
Through the Cayley transform these are the charts of `Sp(2n)⋆` used in
`SymplecticComponents.lean`; here we prove the one analytic-free fact needed
about them:

**`exists_normal_path`.**  A Hamiltonian `M` without the eigenvalue `1` is
joined, by the straight segment `(1 − t)M + tN`, through Hamiltonian matrices
without the eigenvalue `1`, to a Hamiltonian `N` with `N³ = 4N`.

`N` is `2` on the sum of the generalised eigenspaces of the real eigenvalues
`> 1`, `−2` on that of the real eigenvalues `< −1`, and `0` on the rest.  All of
this is polynomial algebra over `ℝ`, with no complex eigenvalue and no
multiplicity count: the characteristic polynomial splits as `f₊ f₋ f₀`, with
`f₊ = ∏ (X − a)` over the roots `a > 1`, `f₋` over the roots `a < −1`, and `f₀`
having no real root of absolute value `> 1`; the Bézout identities of the three
coprime factors give the spectral projectors as polynomials in `M`.  The
subspaces `ker f₊(M)` and `ker f₋(M)` are isotropic, and both are
`ω`-orthogonal to `ker f₀(M)`, because `ω(f(M)x, y) = ω(x, f(−M)y)` and the
relevant factors are coprime to their reflections `g(−X)`; this makes `N`
Hamiltonian.  Along the segment, an eigenvector of `(1 − t)M + tN` for the
eigenvalue `1` would, in one of the three pieces, be an eigenvector of `M` for
a real eigenvalue that the corresponding factor does not vanish at.
-/

open scoped Matrix
open Polynomial

namespace MorseFloer
namespace Chapter7

section Hamiltonian

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- `M` is Hamiltonian: `MᵀJ + JM = 0`. -/
def IsHam (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) : Prop :=
  Mᵀ * Matrix.J l ℝ + Matrix.J l ℝ * M = 0

theorem IsHam.transpose_mul_J {M : Matrix (l ⊕ l) (l ⊕ l) ℝ} (h : IsHam M) :
    Mᵀ * Matrix.J l ℝ = -(Matrix.J l ℝ * M) :=
  eq_neg_of_add_eq_zero_left h

theorem IsHam.neg {M : Matrix (l ⊕ l) (l ⊕ l) ℝ} (h : IsHam M) : IsHam (-M) := by
  unfold IsHam at *
  rw [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, h, neg_zero]

theorem IsHam.add {M N : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hM : IsHam M) (hN : IsHam N) :
    IsHam (M + N) := by
  unfold IsHam at *
  rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
  calc Mᵀ * Matrix.J l ℝ + Nᵀ * Matrix.J l ℝ + (Matrix.J l ℝ * M + Matrix.J l ℝ * N)
      = (Mᵀ * Matrix.J l ℝ + Matrix.J l ℝ * M) + (Nᵀ * Matrix.J l ℝ + Matrix.J l ℝ * N) := by
        abel
    _ = 0 := by rw [hM, hN, add_zero]

theorem IsHam.smul {M : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hM : IsHam M) (c : ℝ) : IsHam (c • M) := by
  unfold IsHam at *
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hM, smul_zero]

theorem transpose_pow_mul_J {M : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hM : IsHam M) (i : ℕ) :
    (M ^ i)ᵀ * Matrix.J l ℝ = Matrix.J l ℝ * (-M) ^ i := by
  induction i with
  | zero => rw [pow_zero, pow_zero, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  | succ i ih =>
    rw [pow_succ, Matrix.transpose_mul, Matrix.mul_assoc, ih, ← Matrix.mul_assoc,
      hM.transpose_mul_J, pow_succ']
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]

theorem transpose_aeval_mul_J {M : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hM : IsHam M) (f : ℝ[X]) :
    (aeval M f)ᵀ * Matrix.J l ℝ = Matrix.J l ℝ * aeval (-M) f := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Matrix.transpose_sum, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, transpose_pow_mul_J hM]

omit [DecidableEq l] in
theorem dotProduct_mulVec_left (A : Matrix (l ⊕ l) (l ⊕ l) ℝ) (x w : (l ⊕ l) → ℝ) :
    (A *ᵥ x) ⬝ᵥ w = x ⬝ᵥ (Aᵀ *ᵥ w) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- `ω(f(M)x, y) = ω(x, f(−M)y)` for Hamiltonian `M`. -/
theorem stdForm_aeval {M : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hM : IsHam M) (f : ℝ[X])
    (x y : (l ⊕ l) → ℝ) :
    Chapter5.stdForm l (aeval M f *ᵥ x) y = Chapter5.stdForm l x (aeval (-M) f *ᵥ y) := by
  rw [Chapter5.stdForm_apply, Chapter5.stdForm_apply, dotProduct_mulVec_left,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_neg, Matrix.neg_mul,
    transpose_aeval_mul_J hM]

/-- Kernels of `f(M)` and `g(M)` are `ω`-orthogonal when `f` is coprime to `g(−X)`. -/
theorem stdForm_eq_zero_of_ker {M : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hM : IsHam M) {f g : ℝ[X]}
    (hfg : IsCoprime f (g.comp (-X))) {x y : (l ⊕ l) → ℝ} (hx : aeval M f *ᵥ x = 0)
    (hy : aeval M g *ᵥ y = 0) : Chapter5.stdForm l x y = 0 := by
  obtain ⟨a, b, hab⟩ := hfg
  rw [mul_comm b] at hab
  have hcomp : aeval M (g.comp (-X)) = aeval (-M) g := by rw [aeval_comp, map_neg, aeval_X]
  have hx' : x = aeval (-M) g *ᵥ (aeval M b *ᵥ x) := by
    have h1 := congrArg (fun p => aeval M p *ᵥ x) hab
    simp only [map_add, map_mul, map_one, Matrix.add_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, zero_add, hcomp] at h1
    exact h1.symm
  rw [hx', stdForm_aeval hM.neg, neg_neg, hy, map_zero]

/-- A matrix `N` with `ω(Nx, y) + ω(x, Ny) = 0` for all `x, y` is Hamiltonian. -/
theorem isHam_of_stdForm {N : Matrix (l ⊕ l) (l ⊕ l) ℝ}
    (h : ∀ x y, Chapter5.stdForm l (N *ᵥ x) y + Chapter5.stdForm l x (N *ᵥ y) = 0) :
    IsHam N := by
  have key : Matrix.toBilin' (Nᵀ * (-(Matrix.J l ℝ)) + (-(Matrix.J l ℝ)) * N) = 0 := by
    refine LinearMap.ext₂ fun x y => ?_
    have hxy := h x y
    rw [Chapter5.stdForm_apply, Chapter5.stdForm_apply, dotProduct_mulVec_left,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at hxy
    rw [Matrix.toBilin'_apply', Matrix.add_mulVec, dotProduct_add, LinearMap.zero_apply,
      LinearMap.zero_apply]
    exact hxy
  have h0 : Nᵀ * (-(Matrix.J l ℝ)) + (-(Matrix.J l ℝ)) * N = 0 :=
    Matrix.toBilin'.injective (key.trans (map_zero _).symm)
  unfold IsHam
  rw [Matrix.mul_neg, Matrix.neg_mul, ← neg_add] at h0
  exact neg_eq_zero.mp h0

/-- The polynomial calculus on an eigenvector. -/
theorem aeval_mulVec_of_eigen {M : Matrix (l ⊕ l) (l ⊕ l) ℝ} {v : (l ⊕ l) → ℝ} {c : ℝ}
    (hv : M *ᵥ v = c • v) (f : ℝ[X]) : aeval M f *ᵥ v = f.eval c • v := by
  induction f using Polynomial.induction_on with
  | C a => rw [aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec,
      eval_C]
  | add p q hp hq => rw [map_add, Matrix.add_mulVec, hp, hq, eval_add, add_smul]
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul,
      h, smul_smul]
    congr 1
    simp only [eval_mul, eval_X, eval_C, eval_pow]
    ring

theorem aeval_mul_comm (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) (p q : ℝ[X]) :
    aeval M p * aeval M q = aeval M q * aeval M p := by
  rw [← map_mul, mul_comm, map_mul]

end Hamiltonian

/-! ## Products of linear factors -/

section Factors

/-- `∏ (X − a)` over a multiset of reals. -/
noncomputable def prodXC (s : Multiset ℝ) : ℝ[X] := (s.map fun a => X - C a).prod

theorem prodXC_add (s t : Multiset ℝ) : prodXC (s + t) = prodXC s * prodXC t := by
  rw [prodXC, prodXC, prodXC, Multiset.map_add, Multiset.prod_add]

theorem roots_prodXC (s : Multiset ℝ) : (prodXC s).roots = s := roots_multiset_prod_X_sub_C s

theorem prodXC_ne_zero (s : Multiset ℝ) : prodXC s ≠ 0 :=
  (monic_multiset_prod_of_monic _ _ fun a _ => monic_X_sub_C a).ne_zero

theorem eval_prodXC_ne_zero {s : Multiset ℝ} {c : ℝ} (h : ∀ a ∈ s, a ≠ c) :
    (prodXC s).eval c ≠ 0 := by
  intro h0
  rw [prodXC, eval_multiset_prod, Multiset.map_map] at h0
  obtain ⟨a, ha, ha0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp h0)
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C] at ha0
  exact h a ha (sub_eq_zero.mp ha0).symm

theorem isCoprime_prodXC {s : Multiset ℝ} {g : ℝ[X]} (h : ∀ a ∈ s, g.eval a ≠ 0) :
    IsCoprime (prodXC s) g := by
  induction s using Multiset.induction_on with
  | empty => simpa [prodXC] using isCoprime_one_left
  | cons a s ih =>
    rw [prodXC, Multiset.map_cons, Multiset.prod_cons]
    refine IsCoprime.mul_left ?_ (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))
    rw [(irreducible_X_sub_C a).coprime_iff_not_dvd, dvd_iff_isRoot]
    exact h a (Multiset.mem_cons_self a s)

theorem eval_comp_neg_X (g : ℝ[X]) (a : ℝ) : (g.comp (-X)).eval a = g.eval (-a) := by
  rw [eval_comp, eval_neg, eval_X]

end Factors

/-! ## The spectral splitting of a Hamiltonian matrix -/

section Splitting

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- The characteristic polynomial splits as `f₊ f₋ f₀`, with `f₀` having no real
root of absolute value `> 1`. -/
theorem exists_splitting (M : Matrix (l ⊕ l) (l ⊕ l) ℝ) :
    ∃ f₀ : ℝ[X], M.charpoly = prodXC (M.charpoly.roots.filter (fun a => 1 < a)) *
      prodXC (M.charpoly.roots.filter (fun a => a < -1)) * f₀ ∧
      ∀ c : ℝ, (1 < c ∨ c < -1) → f₀.eval c ≠ 0 := by
  classical
  set χ := M.charpoly
  set sP := χ.roots.filter (fun a => 1 < a)
  set sM := χ.roots.filter (fun a => a < -1)
  have hχ : χ ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  have hle : sP + sM ≤ χ.roots := by
    have h1 : sM ≤ χ.roots.filter (fun a => ¬ 1 < a) :=
      Multiset.monotone_filter_right _ fun a (ha : a < -1) => by linarith
    calc sP + sM ≤ sP + χ.roots.filter (fun a => ¬ 1 < a) := add_le_add le_rfl h1
      _ = χ.roots := Multiset.filter_add_not _ _
  obtain ⟨f₀, hf₀⟩ := (Multiset.prod_X_sub_C_dvd_iff_le_roots hχ _).mpr hle
  have hf₀' : χ = prodXC (sP + sM) * f₀ := hf₀
  have hsplit : χ = prodXC sP * prodXC sM * f₀ := by
    rw [← prodXC_add]; exact hf₀
  refine ⟨f₀, hsplit, fun c hc h0 => ?_⟩
  have hne : prodXC (sP + sM) * f₀ ≠ 0 := by rw [← hf₀']; exact hχ
  have hmult := rootMultiplicity_mul (x := c) hne
  rw [← hf₀', ← count_roots, ← count_roots, roots_prodXC, Multiset.count_add] at hmult
  have hpos : 0 < rootMultiplicity c f₀ :=
    (rootMultiplicity_pos (right_ne_zero_of_mul hne)).mpr h0
  rcases hc with hc | hc
  · have e1 : Multiset.count c sP = Multiset.count c χ.roots :=
      Multiset.count_filter_of_pos (p := fun a => 1 < a) hc
    have e2 : Multiset.count c sM = 0 :=
      Multiset.count_filter_of_neg (p := fun a => a < -1) (by linarith)
    rw [e1, e2] at hmult
    omega
  · have e1 : Multiset.count c sP = 0 :=
      Multiset.count_filter_of_neg (p := fun a => 1 < a) (by linarith)
    have e2 : Multiset.count c sM = Multiset.count c χ.roots :=
      Multiset.count_filter_of_pos (p := fun a => a < -1) hc
    rw [e1, e2] at hmult
    omega

/-- **The segment to the normal form.**  A Hamiltonian `M` without the eigenvalue
`1` is joined, along the segment `(1 − t)M + tN`, to a Hamiltonian `N` with
`N³ = 4N`, without meeting the eigenvalue `1`. -/
theorem exists_normal_path {M : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hM : IsHam M)
    (h1 : (M - 1).det ≠ 0) :
    ∃ N : Matrix (l ⊕ l) (l ⊕ l) ℝ, IsHam N ∧ N * N * N = (4 : ℝ) • N ∧
      ∀ t ∈ unitInterval, (((1 - t) • M + t • N) - 1).det ≠ 0 := by
  classical
  obtain ⟨f₀, hsplit, hf₀⟩ := exists_splitting M
  set sP := M.charpoly.roots.filter (fun a => 1 < a)
  set sM := M.charpoly.roots.filter (fun a => a < -1)
  have hsP : ∀ a ∈ sP, 1 < a := fun a ha => (Multiset.mem_filter.mp ha).2
  have hsM : ∀ a ∈ sM, a < -1 := fun a ha => (Multiset.mem_filter.mp ha).2
  set fac : Fin 3 → ℝ[X] := ![prodXC sP, prodXC sM, f₀] with hfac
  set lam : Fin 3 → ℝ := ![2, -2, 0] with hlam
  have h3 : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
  have lam0 : lam 0 = 2 := rfl
  have lam1 : lam 1 = -2 := rfl
  have lam2 : lam 2 = 0 := rfl
  -- evaluation facts
  have eP : ∀ c : ℝ, c ≤ 1 → (prodXC sP).eval c ≠ 0 := fun c hc =>
    eval_prodXC_ne_zero fun a ha => by have := hsP a ha; intro h; linarith
  have eM : ∀ c : ℝ, -1 ≤ c → (prodXC sM).eval c ≠ 0 := fun c hc =>
    eval_prodXC_ne_zero fun a ha => by have := hsM a ha; intro h; linarith
  -- coprimality
  have cPM : IsCoprime (prodXC sP) (prodXC sM) :=
    isCoprime_prodXC fun a ha => eM a (by linarith [hsP a ha])
  have cP0 : IsCoprime (prodXC sP) f₀ := isCoprime_prodXC fun a ha => hf₀ a (Or.inl (hsP a ha))
  have cM0 : IsCoprime (prodXC sM) f₀ := isCoprime_prodXC fun a ha => hf₀ a (Or.inr (hsM a ha))
  -- the Bézout projectors
  set g : Fin 3 → ℝ[X] := ![prodXC sM * f₀, prodXC sP * f₀, prodXC sP * prodXC sM] with hg
  have hcop : ∀ a, IsCoprime (fac a) (g a) := by
    intro a
    fin_cases a
    · exact cPM.mul_right cP0
    · exact cPM.symm.mul_right cM0
    · exact (cP0.mul_left cM0).symm
  have hfg : ∀ a, fac a * g a = M.charpoly := by
    intro a
    fin_cases a <;> simp only [hfac, hg, hsplit] <;> simp <;> ring
  choose u w huw using hcop
  set q : Fin 3 → ℝ[X] := fun a => w a * g a with hq
  set P : Fin 3 → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun a => aeval M (q a) with hPdef
  have hχM : aeval M M.charpoly = 0 := Matrix.aeval_self_charpoly M
  have hdvd0 : ∀ r : ℝ[X], M.charpoly ∣ r → aeval M r = 0 := by
    rintro r ⟨t, rfl⟩; rw [map_mul, hχM, zero_mul]
  -- `f_a(M) P_a = 0`
  have hFP : ∀ a, aeval M (fac a) * P a = 0 := by
    intro a
    rw [hPdef, ← map_mul]
    exact hdvd0 _ ⟨w a, by rw [hq, ← hfg a]; ring⟩
  -- `P_a P_b = 0` for `a ≠ b`
  have hg2 : ∀ a b, a ≠ b → M.charpoly ∣ g a * g b := by
    intro a b hab
    rw [hsplit]
    obtain rfl | rfl | rfl := h3 a <;> obtain rfl | rfl | rfl := h3 b <;>
      simp only [ne_eq, not_true_eq_false] at hab <;> simp only [hg] <;> simp <;>
      first
      | (refine ⟨f₀, ?_⟩; ring1)
      | (refine ⟨prodXC sM, ?_⟩; ring1)
      | (refine ⟨prodXC sP, ?_⟩; ring1)
  have hPP : ∀ a b, a ≠ b → P a * P b = 0 := by
    intro a b hab
    rw [hPdef, ← map_mul]
    refine hdvd0 _ ?_
    rw [hq, show w a * g a * (w b * g b) = w a * w b * (g a * g b) by ring]
    exact dvd_mul_of_dvd_right (hg2 a b hab) _
  -- `∑ P_a = 1`
  have hsum : ∑ a, P a = 1 := by
    have hr : ∀ c, fac c ∣ (∑ a, q a) - 1 := by
      intro c
      have hc1 : q c - 1 = -(u c * fac c) := by rw [hq]; linear_combination huw c
      fin_cases c
      · refine ⟨-u 0 + w 1 * f₀ + w 2 * prodXC sM, ?_⟩
        simp only [Fin.sum_univ_three, hq, hg, hfac] at hc1 ⊢
        simp at hc1 ⊢
        linear_combination hc1
      · refine ⟨-u 1 + w 0 * f₀ + w 2 * prodXC sP, ?_⟩
        simp only [Fin.sum_univ_three, hq, hg, hfac] at hc1 ⊢
        simp at hc1 ⊢
        linear_combination hc1
      · refine ⟨-u 2 + w 0 * prodXC sM + w 1 * prodXC sP, ?_⟩
        simp only [Fin.sum_univ_three, hq, hg, hfac] at hc1 ⊢
        simp at hc1 ⊢
        linear_combination hc1
    have hall : M.charpoly ∣ (∑ a, q a) - 1 := by
      rw [hsplit]
      exact IsCoprime.mul_dvd (IsCoprime.mul_left cP0 cM0) (IsCoprime.mul_dvd cPM (hr 0) (hr 1))
        (hr 2)
    have := hdvd0 _ hall
    rw [map_sub, map_sum, map_one, sub_eq_zero] at this
    exact this
  -- `P_a² = P_a`
  have hPsq : ∀ a, P a * P a = P a := by
    intro a
    calc P a * P a = P a * ∑ b, P b - ∑ b ∈ Finset.univ.erase a, P a * P b := by
          rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ a), add_sub_cancel_right]
      _ = P a := by
          rw [hsum, Matrix.mul_one, Finset.sum_eq_zero fun b hb => hPP a b
            (Finset.ne_of_mem_erase hb).symm, sub_zero]
  -- the normal form
  set N : Matrix (l ⊕ l) (l ⊕ l) ℝ := ∑ a, lam a • P a with hN
  have hNP : ∀ a, N * P a = lam a • P a := by
    intro a
    rw [hN, Finset.sum_mul, ← Finset.add_sum_erase _ _ (Finset.mem_univ a),
      Finset.sum_eq_zero fun b hb => by
        rw [Matrix.smul_mul, hPP b a (Finset.ne_of_mem_erase hb), smul_zero],
      add_zero, Matrix.smul_mul, hPsq]
  have hMP : ∀ a, M * P a = P a * M := by
    intro a
    have := aeval_mul_comm M X (q a)
    rwa [aeval_X] at this
  have hNcomm : ∀ a, P a * N = N * P a := by
    intro a
    rw [hN, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul, hPdef, aeval_mul_comm]
  -- components of a vector
  have hdecomp : ∀ v : (l ⊕ l) → ℝ, v = ∑ a, P a *ᵥ v := by
    intro v
    rw [← Matrix.sum_mulVec, hsum, Matrix.one_mulVec]
  have hker : ∀ a (v : (l ⊕ l) → ℝ), aeval M (fac a) *ᵥ (P a *ᵥ v) = 0 := by
    intro a v; rw [Matrix.mulVec_mulVec, hFP, Matrix.zero_mulVec]
  have hNv : ∀ a (v : (l ⊕ l) → ℝ), N *ᵥ (P a *ᵥ v) = lam a • (P a *ᵥ v) := by
    intro a v; rw [Matrix.mulVec_mulVec, hNP, Matrix.smul_mulVec]
  -- the pieces are isotropic and orthogonal where needed
  have key : ∀ a b, a ≠ 2 → lam a + lam b ≠ 0 → IsCoprime (fac a) ((fac b).comp (-X)) := by
    intro a b ha hab
    obtain rfl | rfl | rfl := h3 a <;> obtain rfl | rfl | rfl := h3 b <;>
      simp only [lam0, lam1, lam2, ne_eq, not_true_eq_false] at ha hab <;> norm_num at hab
    · exact isCoprime_prodXC fun a ha => by
        rw [eval_comp_neg_X]; exact eP (-a) (by linarith [hsP a ha])
    · exact isCoprime_prodXC fun a ha => by
        rw [eval_comp_neg_X]; exact hf₀ (-a) (Or.inr (by linarith [hsP a ha]))
    · exact isCoprime_prodXC fun a ha => by
        rw [eval_comp_neg_X]; exact eM (-a) (by linarith [hsM a ha])
    · exact isCoprime_prodXC fun a ha => by
        rw [eval_comp_neg_X]; exact hf₀ (-a) (Or.inl (by linarith [hsM a ha]))
  have horth : ∀ a b, lam a + lam b ≠ 0 → ∀ x y : (l ⊕ l) → ℝ,
      Chapter5.stdForm l (P a *ᵥ x) (P b *ᵥ y) = 0 := by
    intro a b hab x y
    by_cases ha : a = 2
    · subst ha
      have hb : b ≠ 2 := by rintro rfl; rw [lam2] at hab; norm_num at hab
      rw [(Chapter5.stdForm_isSymplectic l).skew,
        stdForm_eq_zero_of_ker hM (key b 2 hb (by rwa [add_comm])) (hker b y) (hker 2 x),
        neg_zero]
    · exact stdForm_eq_zero_of_ker hM (key a b ha hab) (hker a x) (hker b y)
  have hNham : IsHam N := by
    refine isHam_of_stdForm fun x y => ?_
    have e1 : Chapter5.stdForm l (N *ᵥ x) y =
        ∑ a, ∑ b, lam a * Chapter5.stdForm l (P a *ᵥ x) (P b *ᵥ y) := by
      conv_lhs => rw [hdecomp x, hdecomp y]
      rw [Matrix.mulVec_sum, map_sum (Chapter5.stdForm l), LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hNv, map_smul, LinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
    have e2 : Chapter5.stdForm l x (N *ᵥ y) =
        ∑ a, ∑ b, lam b * Chapter5.stdForm l (P a *ᵥ x) (P b *ᵥ y) := by
      conv_lhs => rw [hdecomp x, hdecomp y]
      rw [Matrix.mulVec_sum, map_sum (Chapter5.stdForm l), LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hNv, map_smul, smul_eq_mul]
    rw [e1, e2, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hab : lam a + lam b = 0
    · linear_combination (Chapter5.stdForm l (P a *ᵥ x) (P b *ᵥ y)) * hab
    · rw [horth a b hab]; ring
  refine ⟨N, hNham, ?_, ?_⟩
  · -- `N³ = 4N`
    have hcube : ∀ a, N * N * N * P a = (4 : ℝ) • N * P a := by
      intro a
      calc N * N * N * P a = N * (N * (N * P a)) := by simp only [Matrix.mul_assoc]
        _ = (lam a * lam a * lam a) • P a := by
            simp only [hNP, Matrix.mul_smul, smul_smul]
        _ = (4 * lam a) • P a := by
            congr 1
            obtain rfl | rfl | rfl := h3 a <;> simp only [lam0, lam1, lam2] <;> norm_num
        _ = (4 : ℝ) • N * P a := by rw [Matrix.smul_mul, hNP, smul_smul]
    calc N * N * N = N * N * N * ∑ a, P a := by rw [hsum, Matrix.mul_one]
      _ = ∑ a, N * N * N * P a := Finset.mul_sum _ _ _
      _ = ∑ a, (4 : ℝ) • N * P a := Finset.sum_congr rfl fun a _ => hcube a
      _ = (4 : ℝ) • N * ∑ a, P a := (Finset.mul_sum _ _ _).symm
      _ = (4 : ℝ) • N := by rw [hsum, Matrix.mul_one]
  · -- the segment avoids the eigenvalue `1`
    intro t ht hdet
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    set Mt := (1 - t) • M + t • N with hMt
    have hMtv : Mt *ᵥ v = v := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hMv; exact hMv
    obtain ⟨a, ha⟩ : ∃ a, P a *ᵥ v ≠ 0 := by
      by_contra h
      push Not at h
      apply hv
      rw [hdecomp v]
      exact Finset.sum_eq_zero fun a _ => h a
    set va := P a *ᵥ v with hva
    have hc : Mt * P a = P a * Mt := by
      simp only [hMt, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, hMP,
        hNcomm]
    have hMtva : Mt *ᵥ va = va := by
      rw [hva, Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec, hMtv]
    have hNva : N *ᵥ va = lam a • va := hNv a v
    have heq : (1 - t) • (M *ᵥ va) = (1 - t * lam a) • va := by
      have h' := hMtva
      simp only [hMt, Matrix.add_mulVec, Matrix.smul_mulVec] at h'
      rw [hNva, smul_smul] at h'
      rw [sub_smul (1 : ℝ) (t * lam a) va, one_smul, eq_sub_iff_add_eq]
      exact h'
    have hker' : aeval M (fac a) *ᵥ va = 0 := hker a v
    rcases eq_or_lt_of_le ht.2 with rfl | ht1
    · rw [sub_self, zero_smul, one_mul] at heq
      have h0 : 1 - lam a = 0 := by
        by_contra hne
        exact ha ((smul_eq_zero.mp heq.symm).resolve_left hne)
      obtain rfl | rfl | rfl := h3 a <;> simp only [lam0, lam1, lam2] at h0 <;> norm_num at h0
    · have h1t : (0 : ℝ) < 1 - t := by linarith
      set c := (1 - t * lam a) / (1 - t) with hcdef
      have hMva : M *ᵥ va = c • va := by
        have h2 := congrArg (fun z => (1 - t)⁻¹ • z) heq
        simp only [smul_smul, inv_mul_cancel₀ h1t.ne', one_smul] at h2
        rw [h2, hcdef, div_eq_inv_mul]
      have hev := aeval_mulVec_of_eigen hMva (fac a)
      rw [hker'] at hev
      have hzero : (fac a).eval c = 0 := by
        by_contra hne
        exact ha ((smul_eq_zero.mp hev.symm).resolve_left hne)
      obtain rfl | rfl | rfl := h3 a
      · refine eP c ?_ hzero
        rw [hcdef, div_le_one h1t, lam0]
        linarith [ht.1]
      · refine eM c ?_ hzero
        rw [hcdef, le_div_iff₀ h1t, lam1]
        linarith [ht.1]
      · have hc1 : 1 ≤ c := by
          rw [hcdef, le_div_iff₀ h1t, lam2]
          linarith [ht.1]
        rcases eq_or_lt_of_le hc1 with hc | hc
        · apply h1
          rw [← Matrix.exists_mulVec_eq_zero_iff]
          exact ⟨va, ha, by rw [Matrix.sub_mulVec, hMva, ← hc, one_smul, Matrix.one_mulVec,
            sub_self]⟩
        · exact hf₀ c (Or.inl hc) hzero

end Splitting

end Chapter7
end MorseFloer
