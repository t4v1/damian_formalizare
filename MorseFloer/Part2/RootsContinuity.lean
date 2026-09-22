import MorseFloer.Part2.LatticePath

/-!
# The roots of a polynomial depend continuously on its coefficients

The first brick for the map `ρ : Sp(2n) → S¹` of Chapter 7: the multiset of roots of a monic
polynomial over `ℂ` is a continuous function of the coefficients.  Mathlib has the roots as a
multiset but nothing about their dependence on the polynomial.

Two statements are proved.

* `exists_delta_roots_close`: for every `ε` there is a `δ` such that every monic `q` of the
  same degree whose coefficients are within `δ` of those of `p` has its roots within `ε` of
  those of `p`, *counted with multiplicity*: there are enumerations `a`, `b : Fin n → ℂ` of the
  two root multisets with `‖a i - b i‖ < ε` for every `i`.
* `exists_delta_countP_roots`: consequently the number of roots of `q` in a small disc about
  any point equals the multiplicity of that point as a root of `p`.

The proof is a compactness argument, not an estimate.  If the first statement failed, there
would be a sequence `q k → p` with no `ε`-matching of the roots.  The roots of the `q k` are
bounded (`norm_root_le`, Cauchy's bound), so an enumeration of them has a convergent
subsequence; the coefficients of `∏ (X - C (a i))` are continuous in `a`
(`continuous_coeff_prod`), so the limiting enumeration `b` satisfies `∏ (X - C (b i)) = p`,
i.e. it enumerates the roots of `p`, and the matching exists along the subsequence after all.
-/

open Polynomial Filter Topology Metric Set

namespace MorseFloer
namespace RootsContinuity

/-- A multiset of cardinality `n` is the image of `Fin n`. -/
theorem exists_fin_map {α : Type*} (s : Multiset α) {n : ℕ} (hn : Multiset.card s = n) :
    ∃ f : Fin n → α, s = Finset.univ.val.map f := by
  have hl : s.toList.length = n := by rw [Multiset.length_toList, hn]
  refine ⟨fun i => s.toList.get (Fin.cast hl.symm i), ?_⟩
  rw [Fin.univ_val_map]
  have : List.ofFn (fun i : Fin n => s.toList.get (Fin.cast hl.symm i)) = s.toList := by
    subst hl
    exact List.ofFn_get _
  rw [this, Multiset.coe_toList]

/-- **Cauchy's bound.**  A root of a monic polynomial is bounded by `max 1 (∑ ‖coeff‖)`. -/
theorem norm_root_le {q : ℂ[X]} (hq : q.Monic) {z : ℂ} (hz : q.IsRoot z) :
    ‖z‖ ≤ max 1 (∑ i ∈ Finset.range q.natDegree, ‖q.coeff i‖) := by
  rcases le_or_gt ‖z‖ 1 with h | h
  · exact h.trans (le_max_left _ _)
  refine le_max_of_le_right ?_
  have hev : q.eval z = 0 := hz
  rw [eval_eq_sum_range, Finset.sum_range_succ, hq.coeff_natDegree, one_mul] at hev
  have hzn : z ^ q.natDegree = -∑ i ∈ Finset.range q.natDegree, q.coeff i * z ^ i := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hev
  have hn1 : 1 ≤ q.natDegree := by
    by_contra h0
    have h0' : q.natDegree = 0 := by omega
    rw [h0'] at hzn
    simp at hzn
  have hn : ‖z‖ ^ q.natDegree
      ≤ (∑ i ∈ Finset.range q.natDegree, ‖q.coeff i‖) * ‖z‖ ^ (q.natDegree - 1) := by
    calc ‖z‖ ^ q.natDegree = ‖z ^ q.natDegree‖ := (norm_pow z _).symm
      _ = ‖∑ i ∈ Finset.range q.natDegree, q.coeff i * z ^ i‖ := by rw [hzn, norm_neg]
      _ ≤ ∑ i ∈ Finset.range q.natDegree, ‖q.coeff i * z ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range q.natDegree, ‖q.coeff i‖ * ‖z‖ ^ (q.natDegree - 1) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [norm_mul, norm_pow]
          refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h.le ?_) (norm_nonneg _)
          exact Nat.le_sub_one_of_lt (Finset.mem_range.1 hi)
      _ = (∑ i ∈ Finset.range q.natDegree, ‖q.coeff i‖) * ‖z‖ ^ (q.natDegree - 1) := by
          rw [Finset.sum_mul]
  have hpos : 0 < ‖z‖ ^ (q.natDegree - 1) := pow_pos (by linarith) _
  have e : ‖z‖ ^ q.natDegree = ‖z‖ ^ (q.natDegree - 1) * ‖z‖ := by
    rw [← pow_succ, Nat.sub_add_cancel hn1]
  rw [e, mul_comm (∑ i ∈ Finset.range q.natDegree, ‖q.coeff i‖)] at hn
  exact le_of_mul_le_mul_left hn hpos

/-- The coefficients of `∏ (X - C (a i))` are continuous functions of `a`. -/
theorem continuous_coeff_prod (n : ℕ) (j : ℕ) :
    Continuous fun a : Fin n → ℂ => (∏ i, (X - C (a i))).coeff j := by
  induction n generalizing j with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    exact continuous_const
  | succ n ih =>
    have hsucc : Continuous fun a : Fin (n + 1) → ℂ => fun i : Fin n => a i.succ :=
      continuous_pi fun i => continuous_apply _
    have e : (fun a : Fin (n + 1) → ℂ => (∏ i, (X - C (a i))).coeff j)
        = fun a => ((∏ i : Fin n, (X - C (a i.succ))) * (X - C (a 0))).coeff j :=
      funext fun a => by rw [Fin.prod_univ_succ, mul_comm]
    rw [e]
    cases j with
    | zero =>
      have e0 : (fun a : Fin (n + 1) → ℂ =>
          ((∏ i : Fin n, (X - C (a i.succ))) * (X - C (a 0))).coeff 0)
          = fun a => (∏ i : Fin n, (X - C (a i.succ))).coeff 0 * (-(a 0)) :=
        funext fun a => by
          rw [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
      rw [e0]
      exact ((ih 0).comp hsucc).mul (continuous_apply 0).neg
    | succ j =>
      have e1 : (fun a : Fin (n + 1) → ℂ =>
          ((∏ i : Fin n, (X - C (a i.succ))) * (X - C (a 0))).coeff (j + 1))
          = fun a => (∏ i : Fin n, (X - C (a i.succ))).coeff j
            - (∏ i : Fin n, (X - C (a i.succ))).coeff (j + 1) * a 0 :=
        funext fun a => coeff_mul_X_sub_C
      rw [e1]
      exact ((ih j).comp hsucc).sub (((ih (j + 1)).comp hsucc).mul (continuous_apply 0))

/-- `∏ (X - C (a i))` as the product over the multiset of the `a i`. -/
theorem prod_X_sub_C_eq (n : ℕ) (a : Fin n → ℂ) :
    ∏ i, (X - C (a i)) = ((Finset.univ.val.map a).map fun z => X - C z).prod := by
  rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

/-- **The roots depend continuously on the coefficients**, counted with multiplicity.

No hypothesis on `p` is needed: if there is any monic `q` of degree `n` close to `p`, then `p`
is itself monic of degree `n`, and the proof shows this along the way. -/
theorem exists_delta_roots_close {n : ℕ} {p : ℂ[X]} {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℂ[X], q.Monic → q.natDegree = n →
      (∀ i, ‖q.coeff i - p.coeff i‖ < δ) →
      ∃ a b : Fin n → ℂ, q.roots = Finset.univ.val.map a ∧ p.roots = Finset.univ.val.map b ∧
        ∀ i, ‖a i - b i‖ < ε := by
  by_contra hcon
  push Not at hcon
  have hseq : ∀ k : ℕ, ∃ q : ℂ[X], q.Monic ∧ q.natDegree = n ∧
      (∀ i, ‖q.coeff i - p.coeff i‖ < 1 / ((k : ℝ) + 1)) ∧
      ∀ a b : Fin n → ℂ, q.roots = Finset.univ.val.map a → p.roots = Finset.univ.val.map b →
        ∃ i, ε ≤ ‖a i - b i‖ :=
    fun k => hcon _ (by positivity)
  choose q hqm hqn hqc hqbad using hseq
  have hcard : ∀ k, Multiset.card (q k).roots = n := fun k => by
    rw [IsAlgClosed.card_roots_eq_natDegree, hqn]
  choose a ha using fun k => exists_fin_map (q k).roots (hcard k)
  -- the roots are bounded
  have hbound : ∀ k i, ‖a k i‖ ≤ max 1 (∑ i ∈ Finset.range n, (‖p.coeff i‖ + 1)) := by
    intro k i
    have hmem : a k i ∈ (q k).roots := by
      rw [ha k]
      exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
    have hroot : (q k).IsRoot (a k i) := (mem_roots (hqm k).ne_zero).1 hmem
    refine (norm_root_le (hqm k) hroot).trans (max_le_max le_rfl ?_)
    rw [hqn k]
    refine Finset.sum_le_sum fun i _ => ?_
    have h1 : (1 : ℝ) / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    calc ‖(q k).coeff i‖ = ‖p.coeff i + ((q k).coeff i - p.coeff i)‖ := by rw [add_sub_cancel]
      _ ≤ ‖p.coeff i‖ + ‖(q k).coeff i - p.coeff i‖ := norm_add_le _ _
      _ ≤ ‖p.coeff i‖ + 1 := by linarith [hqc k i]
  have hmemball : ∀ k, a k ∈ closedBall (0 : Fin n → ℂ)
      (max 1 (∑ i ∈ Finset.range n, (‖p.coeff i‖ + 1))) := fun k => by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
    exact hbound k
  obtain ⟨b, -, φ, hφ, hlim⟩ :=
    (isCompact_closedBall (0 : Fin n → ℂ) _).tendsto_subseq hmemball
  have hlim' : ∀ i, Tendsto (fun k => a (φ k) i) atTop (𝓝 (b i)) := fun i =>
    ((continuous_apply i).tendsto b).comp hlim
  -- the limit polynomial is `p`
  have hqeq : ∀ k, q k = ∏ i, (X - C (a k i)) := by
    intro k
    have h1 := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hqm k) (by rw [hcard k, hqn k])
    rw [prod_X_sub_C_eq, ← ha k, h1]
  have hcoef : ∀ j, Tendsto (fun k => (q (φ k)).coeff j) atTop (𝓝 (p.coeff j)) := by
    intro j
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => (hqc (φ k) j).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hcoef' : ∀ j, Tendsto (fun k => (q (φ k)).coeff j) atTop
      (𝓝 ((∏ i, (X - C (b i))).coeff j)) := by
    intro j
    have h := ((continuous_coeff_prod n j).tendsto b).comp hlim
    refine h.congr fun k => ?_
    show (∏ i, (X - C (a (φ k) i))).coeff j = (q (φ k)).coeff j
    rw [hqeq (φ k)]
  have hpeq : p = ∏ i, (X - C (b i)) :=
    Polynomial.ext fun j => tendsto_nhds_unique (hcoef j) (hcoef' j)
  have hproots : p.roots = Finset.univ.val.map b := by
    rw [hpeq, prod_X_sub_C_eq, roots_multiset_prod_X_sub_C]
  -- the contradiction
  have hev : ∀ᶠ k in atTop, ∀ i, ‖a (φ k) i - b i‖ < ε := by
    rw [eventually_all]
    intro i
    exact (tendsto_order.1 (tendsto_iff_norm_sub_tendsto_zero.1 (hlim' i))).2 ε hε
  obtain ⟨k, hk⟩ := hev.exists
  obtain ⟨i, hi⟩ := hqbad (φ k) (a (φ k)) b (ha (φ k)) hproots
  exact absurd (hk i) (not_lt.2 hi)

/-- **The number of roots in a small disc is locally constant.**  For every `c` there are `ε`
and `δ` such that every monic `q` of the same degree with coefficients within `δ` of those of
`p` has exactly as many roots in the disc of radius `ε` about `c`, with multiplicity, as the
multiplicity of `c` as a root of `p`. -/
theorem exists_delta_countP_roots {n : ℕ} (p : ℂ[X]) (c : ℂ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℂ[X], q.Monic → q.natDegree = n →
      (∀ i, ‖q.coeff i - p.coeff i‖ < δ) →
      (q.roots.countP fun z => dist z c < ε) = p.roots.count c := by
  classical
  obtain ⟨ε₀, hε₀, hsep⟩ := LatticePath.exists_pos_of_finite
    (S := insert c {z : ℂ | z ∈ p.roots}) (by
      have h : {z : ℂ | z ∈ p.roots} = ↑p.roots.toFinset := by
        ext z
        simp
      rw [h]
      exact p.roots.toFinset.finite_toSet.insert c)
  obtain ⟨δ, hδ, hδq⟩ := exists_delta_roots_close (n := n) (p := p) (ε := ε₀ / 3) (by positivity)
  refine ⟨ε₀ / 3, by positivity, δ, hδ, fun q hqm hqn hqc => ?_⟩
  obtain ⟨a, b, ha, hb, hab⟩ := hδq q hqm hqn hqc
  rw [ha, hb, Multiset.countP_map, Multiset.count_map]
  congr 1
  refine Multiset.filter_congr fun i _ => ?_
  have hbmem : b i ∈ insert c {z : ℂ | z ∈ p.roots} := by
    refine Set.mem_insert_of_mem _ ?_
    show b i ∈ p.roots
    rw [hb]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)
  constructor
  · intro h
    refine (hsep (b i) hbmem c (Set.mem_insert c _) ?_).symm
    rw [dist_eq_norm]
    calc ‖b i - c‖ = ‖(b i - a i) + (a i - c)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖b i - a i‖ + ‖a i - c‖ := norm_add_le _ _
      _ < ε₀ / 3 + ε₀ / 3 := by
          rw [norm_sub_rev]
          rw [dist_eq_norm] at h
          exact add_lt_add (hab i) h
      _ < ε₀ := by linarith
  · intro h
    rw [dist_eq_norm, h]
    exact hab i

end RootsContinuity
end MorseFloer
