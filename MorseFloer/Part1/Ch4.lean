import MorseFloer.Part1.Ch3
import MorseFloer.Part1.Brouwer

/-!
# Chapter 4: Morse homology, applications

Formalization of Chapter 4 of Audin–Damian, *Théorie de Morse et homologie de
Floer* (Part I, printed pages 75–102).

Chapter 3 built the complex of critical points and its homology; this chapter
computes with it.  The sections are:

* **§4.1** names the homology `HM⋆(V)` of the complex of Chapter 3 and records
  that it only depends on the manifold;
* **§4.2** the Künneth formula: the complex of `f + g` on `M × N` is the tensor
  product of the complexes of `f` and `g` (Proposition 4.2.1), whence the mod `2`
  homology of a product (Corollaries 4.2.2 and 4.2.3);
* **§4.3** Poincaré duality: the complex of `−f` is the transposed complex of
  `f` with the grading reversed (Propositions 4.3.1 and 4.3.2);
* **§4.4** the Euler characteristic, the Poincaré polynomial and the **Morse
  inequalities** (Corollary 4.4.1, Remark 4.4.2, Proposition 4.4.3);
* **§4.5** homology and connectivity (Proposition 4.5.1 and its corollaries,
  Proposition 4.5.7);
* **§4.6** functoriality and homotopy invariance (Theorems 4.6.1 and 4.6.2);
* **§4.7** the long exact sequence of a pair;
* **§4.8** applications: `H₁` of a simply connected manifold (4.8.1), Brouwer's
  fixed point theorem, the mod `2` homology of `Pⁿ(ℝ)` (Theorem 4.8.2) and
  Borsuk–Ulam (Theorem 4.8.3) with its corollaries.

## What is formalized here, and how

The homology of Chapter 3 is attached to *abstract data* — a finite set `Crit`
of critical points, an index function `ind` and a count function `cnt` — because
Mathlib has no moduli spaces of trajectories.  Everything in this chapter that
is a statement about that data is stated and proved; everything that is a
statement about a *manifold* (functoriality, connectivity, the long exact
sequence of a pair) cannot even be phrased and is listed as a gap below.

Working over a field `K` (the book works over `Z/2` precisely so that the
rank–nullity theorem is available, Remark 4.4.2), we define

* `numCrit ind k = cₖ(f)`, the number of critical points of index `k`;
* `cyclesAt`, `boundariesIn`, `betti ind cnt k = βₖ = dim Hₖ`;
* `eulerChar` and `poincarePoly`.

**Proved in full** (no geometric input beyond `BrokenPairs`):

* `betti_add_bdim`, `bdim_add_finrank_cyclesAt` — rank–nullity for the complex;
* `betti_le_numCrit` — **the Morse inequalities `βₖ ≤ cₖ`** (Proposition 4.4.3);
* `sum_betti_le_card` — the total form of Proposition 4.4.3: a Morse function
  has at least `Σ βₖ` critical points;
* `sum_alt_numCrit` — the telescoping identity
  `Σ (−1)ᵏ cₖ = Σ (−1)ᵏ βₖ + (−1)ᴺ dim Bₙ`, from which follow
  `eulerChar_eq_alt_sum_numCrit` (Remark 4.4.2: the Euler characteristic is the
  alternating sum of the numbers of critical points), `card_crit_modEq`
  (**Corollary 4.4.1**: the number of critical points modulo `2` depends only on
  the homology) and `strong_morse_inequality`, the sharper alternating form
  `Σ_{k≤m} (−1)^{m−k} βₖ ≤ Σ_{k≤m} (−1)^{m−k} cₖ`;
* `poincarePoly_eval_neg_one` — `P_V(−1) = χ(V)`;
* `eulerChar_eq_zero_of_odd` — Remark 4.4.7, the Euler characteristic of an
  odd-dimensional closed manifold vanishes (from Poincaré duality);
* `betti_dual` — **Proposition 4.3.1**, `βₖ = β_{n−k}`, for the complex of `−f`,
  which is the transposed complex with the grading reversed.  The linear algebra
  behind it, `Matrix.rank_transpose`, is Mathlib's;
* `betti_of_count_zero` and the examples: the torus (Poincaré polynomial
  `1 + 2t + t²`, Euler characteristic `0`) and `Pⁿ(ℝ)` (**Theorem 4.8.2**);
* `brokenPairs_prod` and `betti_prod` — **Proposition 4.2.1 and Corollaries
  4.2.2, 4.2.3 (Künneth)**: in characteristic `2` the product complex is a
  complex and `βₖ(M × N) = Σ_{i+j=k} βᵢ(M) βⱼ(N)`;
* `betti_sumComplex` — the additivity of §4.1 and Corollary 4.5.5: the Betti
  numbers of a disjoint union add up;
* `finrank_homology_dual_int` — **Proposition 4.3.2**, duality over `ℤ` for an
  oriented manifold, in the form of the free ranks.  The book's statement
  `HM_{n−k}(V; Z) ≅ HMₖ(V; Z)` cannot be taken literally: the complex of `−f` is
  the transposed complex, whose homology is *cohomology*, and over `ℤ` the two
  differ by torsion — for `P³(ℝ)`, `HM₁ = Z/2` while `HM₂ = 0`.  Over a field,
  which is Proposition 4.3.1, there is no discrepancy;
* `brouwer_fixedPoint` and `no_retraction_closedBall` (§4.8.b), in every
  dimension: the first restates `MorseFloer.brouwer_fixed_point` from
  `MorseFloer/Part1/Brouwer.lean`, proved analytically since this Mathlib has no
  homology of spheres, and the second is deduced from it;
* `borsuk_ulam_of_odd`, `exists_eq_antipode` and
  `exists_antipodal_pair_of_closed_cover` — **Corollaries 4.8.4, 4.8.5 and
  4.8.6** of Borsuk–Ulam, deduced from Theorem 4.8.3.

The two statements about Betti numbers of a *changed* complex (Künneth and the
disjoint union) rest on one piece of linear algebra, proved below under
"Deformation retractions of based complexes": every based complex over a field
retracts, by explicit matrices, onto a graded vector space with zero
differential (`exists_retract`), whose numbers of generators are then the Betti
numbers (`betti_eq_numCrit_of_retract`); retractions tensor
(`betti_prod_of_retract`) and add up along block sums.

**Stated with `sorry`**, because the proof needs topology Mathlib does not have:

* `borsuk_ulam` — Theorem 4.8.3.  **This Mathlib version does not contain
  Borsuk–Ulam** (a search for `borsuk` finds only the Borsuk–Mazurkiewicz
  example on local contractibility), so it is stated here and its corollaries
  are proved from it.  Nor can it be derived along the book's lines: Mathlib has
  no excision or Mayer–Vietoris for its singular homology (so the mod `2`
  homology of `Pⁿ(ℝ)` is nowhere computed), and no degree theory.  Unlike
  Brouwer, it has no known short analytic proof; the realistic routes are
  Tucker's combinatorial lemma or a mod `2` degree built on Sard's theorem.

## Gaps: results carrying no Lean declaration

* **Remark 4.1.2** and all of **§4.6** (Theorems 4.6.1 and 4.6.2, Proposition
  4.6.3, Lemma 4.6.6) and **§4.7** (the long exact sequence of a pair).  These
  speak of smooth maps between manifolds and of the induced maps on Morse
  homology; with abstract count data there is no manifold and no induced map.
  The purely homological half of §4.7 — that a short exact sequence of complexes
  induces a long exact sequence — is Mathlib's
  `CategoryTheory.ShortComplex.ShortExact` together with
  `HomologySequence.snakeInput`, and applies verbatim to `morseComplex`.
* **Proposition 4.5.1** (`HM₀ ≅ Z/2` for a connected manifold), **Corollary
  4.5.3**, **Remark 4.5.6** and **Proposition 4.5.7** (a Morse function without
  critical points of index `1` forces simple connectivity): all of these need
  the connectivity of `V` and the unstable manifolds of the index-`1` critical
  points, none of which is expressible.
* **Proposition 4.8.1** (`HM₁ = 0` for a simply connected manifold): needs
  `π₁(V)` of the manifold carrying the complex.
* **§4.8.e** (the complex of critical points computes the cellular homology of
  `V`): needs ordered Morse functions and cellular homology of the manifold.
* **Examples 4.1.1, 4.4.4, 4.4.6, 4.4.8, 4.7.1** are commentary on manifolds; the
  torus and `Pⁿ(ℝ)` computations they use are recorded below as complexes.
-/

namespace MorseFloer
namespace Chapter4

open MorseFloer.Chapter3

/-! ## §4.1 Homology

The homology of the complex of critical points is `HM⋆(V)`; Chapter 3 provides
it as `morseHomology`.  For the computations of this chapter we need its
*dimension*, so we work over a field `K` (the book works over `Z/2` for exactly
this reason, Remark 4.4.2) and describe `Hₖ` concretely as `Ker ∂ₖ / Im ∂ₖ₊₁`.

Recall the indexing convention of Chapter 3: `dLin ind cnt k` is the
differential `Cₖ₊₁ → Cₖ`, so `cycles ind cnt k` is the space of cycles in degree
`k + 1` and `boundaries ind cnt k` the space of boundaries in degree `k`. -/

section Complex

variable {R : Type*} [CommRing R] {Crit : Type*} [Fintype Crit]
  {ind : Crit → ℕ} {cnt : Crit → Crit → R}

/-- `Zₖ`, the cycles in degree `k`.  Every chain of degree `0` is a cycle, since
the differential leaving degree `0` is zero. -/
noncomputable def cyclesAt (ind : Crit → ℕ) (cnt : Crit → Crit → R) :
    ∀ k : ℕ, Submodule R (Chains R ind k)
  | 0 => ⊤
  | (k + 1) => cycles ind cnt k

@[simp] theorem cyclesAt_zero (ind : Crit → ℕ) (cnt : Crit → Crit → R) :
    cyclesAt ind cnt 0 = ⊤ := rfl

@[simp] theorem cyclesAt_succ (ind : Crit → ℕ) (cnt : Crit → Crit → R) (k : ℕ) :
    cyclesAt ind cnt (k + 1) = cycles ind cnt k := rfl

/-- `Im ∂ₖ₊₁ ⊆ Ker ∂ₖ` in every degree, so the quotient below is the book's
`Hₖ = Ker ∂ₖ / Im ∂ₖ₊₁`. -/
theorem boundaries_le_cyclesAt (h : BrokenPairs ind cnt) (k : ℕ) :
    boundaries ind cnt k ≤ cyclesAt ind cnt k := by
  cases k with
  | zero => exact le_top
  | succ k => exact boundaries_le_cycles h k

/-- `Bₖ` seen inside `Zₖ`, so that `HMₖ` is the quotient
`cyclesAt ind cnt k ⧸ boundariesIn ind cnt k`. -/
noncomputable def boundariesIn (ind : Crit → ℕ) (cnt : Crit → Crit → R) (k : ℕ) :
    Submodule R (cyclesAt ind cnt k) :=
  Submodule.comap (cyclesAt ind cnt k).subtype (boundaries ind cnt k)

end Complex

section Basic

variable {K : Type*} [Field K] {Crit : Type*} [Fintype Crit]
  {ind : Crit → ℕ} {cnt : Crit → Crit → K}

/-- `cₖ(f)`: the number of critical points of index `k` (§4.4). -/
def numCrit (ind : Crit → ℕ) (k : ℕ) : ℕ := Fintype.card (CritSet ind k)

theorem finrank_chains (ind : Crit → ℕ) (k : ℕ) :
    Module.finrank K (Chains K ind k) = numCrit ind k :=
  Module.finrank_fintype_fun_eq_card K

/-- `βₖ = dim HMₖ`, the `k`-th Betti number (§4.4): the dimension of
`Ker ∂ₖ / Im ∂ₖ₊₁`. -/
noncomputable def betti (ind : Crit → ℕ) (cnt : Crit → Crit → K) (k : ℕ) : ℕ :=
  Module.finrank K ((cyclesAt ind cnt k) ⧸ boundariesIn ind cnt k)

/-- `dim Bₖ`, the dimension of the space of boundaries in degree `k`. -/
noncomputable def bdim (ind : Crit → ℕ) (cnt : Crit → Crit → K) (k : ℕ) : ℕ :=
  Module.finrank K (boundaries ind cnt k)

/-- `dim Hₖ + dim Bₖ = dim Zₖ`: the defining property of the quotient. -/
theorem betti_add_bdim (h : BrokenPairs ind cnt) (k : ℕ) :
    betti ind cnt k + bdim ind cnt k = Module.finrank K (cyclesAt ind cnt k) := by
  have h2 : Module.finrank K (boundariesIn ind cnt k) = bdim ind cnt k :=
    (Submodule.comapSubtypeEquivOfLe (boundaries_le_cyclesAt h k)).finrank_eq
  have h1 := Submodule.finrank_quotient_add_finrank (boundariesIn ind cnt k)
  simp only [betti]
  rw [← h2]
  exact h1

/-- **Rank–nullity for `∂ₖ : Cₖ₊₁ → Cₖ`**: `dim Bₖ + dim Zₖ₊₁ = cₖ₊₁`.  This is
the "kernel–image theorem" the book invokes in Remark 4.4.2, and the reason for
working over a field. -/
theorem bdim_add_finrank_cyclesAt (ind : Crit → ℕ) (cnt : Crit → Crit → K) (k : ℕ) :
    bdim ind cnt k + Module.finrank K (cyclesAt ind cnt (k + 1)) = numCrit ind (k + 1) := by
  have h : Module.finrank K (LinearMap.range (dLin ind cnt k))
      + Module.finrank K (LinearMap.ker (dLin ind cnt k))
      = Module.finrank K (Chains K ind (k + 1)) :=
    LinearMap.finrank_range_add_finrank_ker (dLin ind cnt k)
  rw [finrank_chains] at h
  exact h

/-- `c₀ = β₀ + dim B₀`. -/
theorem numCrit_zero_eq (h : BrokenPairs ind cnt) :
    numCrit ind 0 = betti ind cnt 0 + bdim ind cnt 0 := by
  have h1 := betti_add_bdim h 0
  rw [cyclesAt_zero, finrank_top, finrank_chains] at h1
  omega

/-- `cₖ₊₁ = dim Bₖ + (βₖ₊₁ + dim Bₖ₊₁)`. -/
theorem numCrit_succ_eq (h : BrokenPairs ind cnt) (k : ℕ) :
    numCrit ind (k + 1) = bdim ind cnt k + (betti ind cnt (k + 1) + bdim ind cnt (k + 1)) := by
  have h1 := betti_add_bdim h (k + 1)
  have h2 := bdim_add_finrank_cyclesAt ind cnt k
  omega

omit [Fintype Crit] in
/-- Above the top index there are no critical points. -/
theorem isEmpty_critSet {f : Crit → ℕ} {n m : ℕ} (hf : ∀ c, f c ≤ n) (hm : n < m) :
    IsEmpty (CritSet f m) :=
  ⟨fun c => by have h1 := hf c.1; have h2 := c.2; omega⟩

/-- If there is no critical point of index `k + 1` then `∂ₖ = 0`. -/
theorem bdim_eq_zero_of_isEmpty {k : ℕ} (hE : IsEmpty (CritSet ind (k + 1))) :
    bdim ind cnt k = 0 := by
  have h0 : dLin ind cnt k = 0 := by
    ext x b
    have := hE
    simp
  show Module.finrank K (LinearMap.range (dLin ind cnt k)) = 0
  rw [h0, LinearMap.range_zero, finrank_bot]

/-- The total number of critical points is the sum of the `cₖ`. -/
theorem card_eq_sum_numCrit {N : ℕ} (hN : ∀ c, ind c ≤ N) :
    Fintype.card Crit = ∑ k ∈ Finset.range (N + 1), numCrit ind k := by
  rw [← Finset.card_univ,
    Finset.card_eq_sum_card_fiberwise (f := ind) (t := Finset.range (N + 1))
      (fun c _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (hN c)))]
  exact Finset.sum_congr rfl fun k _ => (Fintype.card_subtype _).symm

/-- A complex with vanishing differential has `βₖ = cₖ`. -/
theorem betti_of_count_zero (ind : Crit → ℕ) (k : ℕ) :
    betti ind (fun _ _ => (0 : K)) k = numCrit ind k := by
  have hb : bdim ind (fun _ _ => (0 : K)) k = 0 := by
    show Module.finrank K (boundaries ind (fun _ _ => (0 : K)) k) = 0
    rw [boundaries_zero ind k, finrank_bot]
  have hz : Module.finrank K (cyclesAt ind (fun _ _ => (0 : K)) k) = numCrit ind k := by
    cases k with
    | zero => rw [cyclesAt_zero, finrank_top]; exact finrank_chains ind 0
    | succ k =>
        rw [cyclesAt_succ, cycles_zero, finrank_top]
        exact finrank_chains ind (k + 1)
  have h := betti_add_bdim (brokenPairs_zero (R := K) ind) k
  omega

end Basic

/-! ## §4.2 The Künneth formula

If `f` and `g` are Morse functions on `M` and `N` with adapted Smale
pseudo-gradients `X` and `Y`, then `f + g` is a Morse function on `M × N` whose
critical points are the pairs `(a, a')`, with `Ind(a, a') = Ind a + Ind a'`, and
whose pseudo-gradient is `(X, Y)`.  Since the flow of `(X, Y)` is the product of
the flows, a connecting trajectory between critical points of consecutive
indices must be constant in one factor, so

`n((a,a'),(b,b')) = n_Y(a',b')` if `a = b`, `n_X(a,b)` if `a' = b'`, and `0`
otherwise.

That is exactly the differential `∂_X ⊗ 1 + 1 ⊗ ∂_Y` of the tensor product of
the two complexes, which is Proposition 4.2.1. -/

/-! ### Sum bookkeeping for the product complex -/

section Sums

/-- A sum over the critical points of index `m` is the sum over all critical
points of the function extended by zero. -/
theorem sum_critSet_eq {Crit : Type*} [Fintype Crit] {M : Type*} [AddCommMonoid M]
    (ind : Crit → ℕ) (m : ℕ) (f : Crit → M) :
    ∑ c : CritSet ind m, f c.1 = ∑ c : Crit, if ind c = m then f c else 0 := by
  have h1 : ∑ c ∈ Finset.univ.filter (fun c : Crit => ind c = m), f c
      = ∑ c : CritSet ind m, f c.1 :=
    Finset.sum_subtype _ (fun x => by simp) f
  rw [← h1, Finset.sum_filter]

/-- `cₖ(f)`, the number of critical points of index `k`, as a sum of indicators. -/
theorem numCrit_eq_sum {Crit : Type*} [Fintype Crit] (ind : Crit → ℕ) (m : ℕ) :
    numCrit ind m = ∑ c : Crit, if ind c = m then 1 else 0 := by
  have h := sum_critSet_eq ind m (fun _ => (1 : ℕ))
  have h2 : (∑ _c : CritSet ind m, (1 : ℕ)) = numCrit ind m := by
    simp [numCrit, Finset.card_univ]
  rw [← h2]
  exact h

private theorem sum_range_ite_mul (k p q : ℕ) :
    (∑ i ∈ Finset.range (k + 1), (if p = i then (1 : ℕ) else 0) * (if q = k - i then 1 else 0))
      = if p + q = k then 1 else 0 := by
  by_cases hp : p ≤ k
  · have h1 : (∑ i ∈ Finset.range (k + 1),
        (if p = i then (1 : ℕ) else 0) * (if q = k - i then 1 else 0))
        = (if p = p then (1 : ℕ) else 0) * (if q = k - p then 1 else 0) :=
      Finset.sum_eq_single p (fun b _ hb => by rw [if_neg (Ne.symm hb), zero_mul])
        (fun h => absurd (Finset.mem_range.mpr (by omega)) h)
    rw [h1, if_pos rfl, one_mul]
    by_cases hq : p + q = k
    · rw [if_pos (show q = k - p by omega), if_pos hq]
    · rw [if_neg (show ¬(q = k - p) by omega), if_neg hq]
  · rw [if_neg (show ¬(p + q = k) by omega)]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    rw [if_neg (show ¬(p = i) by omega), zero_mul]

end Sums

/-! ### Deformation retractions of based complexes

Two results of this chapter compute the Betti numbers of a complex built from
others — the product complex of §4.2 and the disjoint union of §4.1 — and the
based model of Chapter 3 gives no direct handle on either, since the natural
argument changes basis.  The tool used instead is a *deformation retraction onto
the homology*, written with matrices on the whole set of critical points:

* `totalD ind cnt` is the whole differential as one square matrix;
* a retraction is a based graded set `CH` with matrices `I` (degree preserving,
  into the cycles), `P` (killing the boundaries) and `Hm`, with `P I = 1` and
  `I P = 1 + ∂ Hm + Hm ∂`.

`betti_eq_numCrit_of_retract` shows that `βₖ` is then the number of elements of
`CH` of degree `k`, and `exists_retract` that every based complex over a field
has such a retraction.  Retractions are stable under Kronecker products and
block sums, which is how `betti_prod` and `betti_sumComplex` are proved. -/

section Retraction

open scoped Matrix

variable {K : Type*} [Field K] {Crit : Type*} [Fintype Crit]

/-- The whole differential of the complex as one square matrix on the set of all
critical points: the entry in row `b`, column `a` is the count from `a` to `b`
when the index drops by one, and `0` otherwise. -/
def totalD (ind : Crit → ℕ) (cnt : Crit → Crit → K) : Matrix Crit Crit K :=
  Matrix.of fun b a => if ind a = ind b + 1 then cnt a b else 0

omit [Fintype Crit] in
theorem totalD_apply (ind : Crit → ℕ) (cnt : Crit → Crit → K) (b a : Crit) :
    totalD ind cnt b a = if ind a = ind b + 1 then cnt a b else 0 := rfl

/-- A chain of degree `k`, extended by zero to a function on all critical points. -/
def extChains (ind : Crit → ℕ) (k : ℕ) : Chains K ind k →ₗ[K] (Crit → K) where
  toFun x c := if h : ind c = k then x ⟨c, h⟩ else 0
  map_add' x y := by
    funext c
    by_cases h : ind c = k
    · simp only [dif_pos h, Pi.add_apply]
    · simp only [dif_neg h, Pi.add_apply, add_zero]
  map_smul' r x := by
    funext c
    by_cases h : ind c = k
    · simp only [dif_pos h, Pi.smul_apply, RingHom.id_apply]
    · simp only [dif_neg h, Pi.smul_apply, RingHom.id_apply, smul_zero]

/-- The degree `k` part of a function on all critical points. -/
def resChains (ind : Crit → ℕ) (k : ℕ) : (Crit → K) →ₗ[K] Chains K ind k :=
  LinearMap.funLeft K K Subtype.val

omit [Fintype Crit] in
theorem extChains_apply_of_eq {ind : Crit → ℕ} {k : ℕ} (x : Chains K ind k) {c : Crit}
    (h : ind c = k) : extChains ind k x c = x ⟨c, h⟩ := dif_pos h

omit [Fintype Crit] in
theorem extChains_apply_of_ne {ind : Crit → ℕ} {k : ℕ} (x : Chains K ind k) {c : Crit}
    (h : ind c ≠ k) : extChains ind k x c = 0 := dif_neg h

omit [Fintype Crit] in
theorem resChains_extChains (ind : Crit → ℕ) (k : ℕ) (x : Chains K ind k) :
    resChains ind k (extChains ind k x) = x := by
  funext c
  exact extChains_apply_of_eq x c.2

omit [Fintype Crit] in
theorem extChains_injective (ind : Crit → ℕ) (k : ℕ) :
    Function.Injective (extChains (K := K) ind k) :=
  Function.LeftInverse.injective (resChains_extChains ind k)

omit [Fintype Crit] in
theorem extChains_resChains_apply (ind : Crit → ℕ) (k : ℕ) (x : Crit → K) (c : Crit) :
    extChains ind k (resChains ind k x) c = if ind c = k then x c else 0 := by
  by_cases h : ind c = k
  · rw [extChains_apply_of_eq _ h, if_pos h]
    rfl
  · rw [extChains_apply_of_ne _ h, if_neg h]

/-- Reading the total differential in degree `k` gives back `∂ₖ`. -/
theorem resChains_totalD_mulVec (ind : Crit → ℕ) (cnt : Crit → Crit → K) (k : ℕ)
    (w : Crit → K) :
    resChains ind k (totalD ind cnt *ᵥ w) = dLin ind cnt k (resChains ind (k + 1) w) := by
  funext b
  show ∑ a : Crit, totalD ind cnt b.1 a * w a = ∑ a : CritSet ind (k + 1), w a.1 * cnt a.1 b.1
  rw [sum_critSet_eq ind (k + 1) (fun a => w a * cnt a b.1)]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hb : ind b.1 = k := b.2
  rw [totalD_apply]
  by_cases ha : ind a = k + 1
  · rw [if_pos (by omega), if_pos ha, mul_comm]
  · rw [if_neg (by omega), if_neg ha, zero_mul]

/-- The total differential kills everything of degree `0`. -/
theorem totalD_mulVec_extChains_zero (ind : Crit → ℕ) (cnt : Crit → Crit → K)
    (x : Chains K ind 0) : totalD ind cnt *ᵥ extChains ind 0 x = 0 := by
  funext b
  show ∑ a : Crit, totalD ind cnt b a * extChains ind 0 x a = 0
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [totalD_apply]
  by_cases ha : ind a = ind b + 1
  · rw [extChains_apply_of_ne x (show ind a ≠ 0 by omega), mul_zero]
  · rw [if_neg ha, zero_mul]

/-- On chains of degree `k + 1` the total differential is `∂ₖ`. -/
theorem totalD_mulVec_extChains (ind : Crit → ℕ) (cnt : Crit → Crit → K) (k : ℕ)
    (x : Chains K ind (k + 1)) :
    totalD ind cnt *ᵥ extChains ind (k + 1) x = extChains ind k (dLin ind cnt k x) := by
  funext b
  by_cases hb : ind b = k
  · rw [extChains_apply_of_eq _ hb]
    have h1 := congrFun (resChains_totalD_mulVec ind cnt k (extChains ind (k + 1) x)) ⟨b, hb⟩
    rw [resChains_extChains] at h1
    exact h1
  · rw [extChains_apply_of_ne _ hb]
    show ∑ a : Crit, totalD ind cnt b a * extChains ind (k + 1) x a = 0
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [totalD_apply]
    by_cases ha : ind a = ind b + 1
    · rw [extChains_apply_of_ne x (show ind a ≠ k + 1 by omega), mul_zero]
    · rw [if_neg ha, zero_mul]

/-- `BrokenPairs` says exactly that the total differential squares to zero. -/
theorem totalD_mul_self {ind : Crit → ℕ} {cnt : Crit → Crit → K} (h : BrokenPairs ind cnt) :
    totalD ind cnt * totalD ind cnt = 0 := by
  ext b a
  rw [Matrix.mul_apply, Matrix.zero_apply]
  by_cases hab : ind a = ind b + 2
  · have hB : ∑ c : CritSet ind (ind b + 1), cnt a c.1 * cnt c.1 b = 0 :=
      h (ind b) ⟨a, hab⟩ ⟨b, rfl⟩
    rw [sum_critSet_eq ind (ind b + 1) (fun c => cnt a c * cnt c b)] at hB
    refine Eq.trans (Finset.sum_congr rfl fun c _ => ?_) hB
    rw [totalD_apply, totalD_apply]
    by_cases hc : ind c = ind b + 1
    · rw [if_pos hc, if_pos (by omega), if_pos hc, mul_comm]
    · rw [if_neg hc, if_neg hc, zero_mul]
  · refine Finset.sum_eq_zero fun c _ => ?_
    rw [totalD_apply, totalD_apply]
    by_cases hc : ind c = ind b + 1
    · rw [if_neg (show ¬ind a = ind c + 1 by omega), mul_zero]
    · rw [if_neg hc, zero_mul]

/-- A chain is a cycle exactly when the total differential kills its extension
by zero; in degree `0` both conditions always hold. -/
theorem mem_cyclesAt_iff (ind : Crit → ℕ) (cnt : Crit → Crit → K) (k : ℕ)
    (x : Chains K ind k) :
    x ∈ cyclesAt ind cnt k ↔ totalD ind cnt *ᵥ extChains ind k x = 0 := by
  cases k with
  | zero =>
      simp only [cyclesAt_zero, Submodule.mem_top, true_iff]
      exact totalD_mulVec_extChains_zero ind cnt x
  | succ k =>
      rw [cyclesAt_succ, totalD_mulVec_extChains]
      change dLin ind cnt k x = 0 ↔ _
      constructor
      · intro hx
        rw [hx, map_zero]
      · intro hx
        exact extChains_injective ind k (by rw [hx, map_zero])

omit [Fintype Crit] in
/-- A graded matrix commutes with taking the degree `k` part. -/
theorem extChains_resChains_mulVec {CH : Type*} [Fintype CH] (ind : Crit → ℕ)
    (indH : CH → ℕ) (I : Matrix Crit CH K) (hI : ∀ c e, I c e ≠ 0 → ind c = indH e)
    (k : ℕ) (y : CH → K) :
    extChains ind k (resChains ind k (I *ᵥ y)) = I *ᵥ extChains indH k (resChains indH k y) := by
  funext c
  rw [extChains_resChains_apply]
  show _ = ∑ e, I c e * extChains indH k (resChains indH k y) e
  by_cases hc : ind c = k
  · rw [if_pos hc]
    show ∑ e, I c e * y e = _
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [extChains_resChains_apply]
    by_cases he : indH e = k
    · rw [if_pos he]
    · rw [if_neg he]
      have h0 : I c e = 0 := by
        by_contra hne
        exact he ((hI c e hne).symm.trans hc)
      rw [h0, zero_mul, mul_zero]
  · rw [if_neg hc]
    symm
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [extChains_resChains_apply]
    by_cases he : indH e = k
    · have h0 : I c e = 0 := by
        by_contra hne
        exact hc ((hI c e hne).trans he)
      rw [h0, zero_mul]
    · rw [if_neg he, mul_zero]

/-- **Betti numbers from a deformation retraction.**  Suppose the complex retracts
onto a based graded vector space with zero differential: a degree-preserving `I`
into the cycles, a `P` killing the boundaries with `P ∘ I = 1`, and a homotopy
`Hm` with `I ∘ P = 1 + (∂ Hm + Hm ∂)`.  Then `βₖ` is the number of generators of
degree `k`.  Proof: every cycle `z` equals `I P z − ∂(Hm z)`, so in each degree
the cycles are the direct sum of the image of `I` and the boundaries. -/
theorem betti_eq_numCrit_of_retract [DecidableEq Crit] {ind : Crit → ℕ} {cnt : Crit → Crit → K}
    (h : BrokenPairs ind cnt) {CH : Type*} [Fintype CH] [DecidableEq CH] (indH : CH → ℕ)
    (I : Matrix Crit CH K) (P : Matrix CH Crit K) (Hm : Matrix Crit Crit K)
    (hI : ∀ c e, I c e ≠ 0 → ind c = indH e) (hDI : totalD ind cnt * I = 0)
    (hPD : P * totalD ind cnt = 0) (hPI : P * I = 1)
    (hH : I * P = 1 + (totalD ind cnt * Hm + Hm * totalD ind cnt)) (k : ℕ) :
    betti ind cnt k = numCrit indH k := by
  let Ik : Chains K indH k →ₗ[K] Chains K ind k :=
    resChains ind k ∘ₗ I.mulVecLin ∘ₗ extChains indH k
  have hIk : ∀ y, extChains ind k (Ik y) = I *ᵥ extChains indH k y := by
    intro y
    have h1 := extChains_resChains_mulVec ind indH I hI k (extChains indH k y)
    rw [resChains_extChains] at h1
    exact h1
  have hPIv : ∀ v, P *ᵥ (I *ᵥ v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, hPI, Matrix.one_mulVec]
  -- the image of `I` meets the boundaries only in `0`
  have hdisj : ∀ y w, Ik y = dLin ind cnt k w → y = 0 := by
    intro y w hyw
    have h1 : I *ᵥ extChains indH k y = totalD ind cnt *ᵥ extChains ind (k + 1) w := by
      rw [← hIk, hyw, totalD_mulVec_extChains]
    have h2 : extChains indH k y = 0 := by
      rw [← hPIv (extChains indH k y), h1, Matrix.mulVec_mulVec, hPD, Matrix.zero_mulVec]
    exact extChains_injective indH k (by rw [h2, map_zero])
  have hinj : Function.Injective Ik := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact hdisj y 0 (by rw [hy, map_zero])
  -- the image of `I` consists of cycles
  have hIcyc : LinearMap.range Ik ≤ cyclesAt ind cnt k := by
    rintro _ ⟨y, rfl⟩
    rw [mem_cyclesAt_iff, hIk, Matrix.mulVec_mulVec, hDI, Matrix.zero_mulVec]
  -- every cycle is an image of `I` plus a boundary
  have hcyc : cyclesAt ind cnt k ≤ LinearMap.range Ik ⊔ boundaries ind cnt k := by
    intro z hz
    rw [mem_cyclesAt_iff] at hz
    have h1 : extChains ind k z
        = I *ᵥ (P *ᵥ extChains ind k z) - totalD ind cnt *ᵥ (Hm *ᵥ extChains ind k z) := by
      have h2 := congrArg (fun M => M *ᵥ extChains ind k z) hH
      simp only [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hz,
        Matrix.mulVec_zero, add_zero] at h2
      rw [h2]
      abel
    have h3 : z = Ik (resChains indH k (P *ᵥ extChains ind k z))
        - dLin ind cnt k (resChains ind (k + 1) (Hm *ᵥ extChains ind k z)) := by
      have h4 := congrArg (resChains ind k) h1
      rw [resChains_extChains, map_sub, resChains_totalD_mulVec] at h4
      have h5 := congrArg (resChains ind k)
        (extChains_resChains_mulVec ind indH I hI k (P *ᵥ extChains ind k z))
      rw [resChains_extChains] at h5
      refine h4.trans ?_
      congr 1
    rw [h3]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (LinearMap.mem_range_self _ _))
      (Submodule.mem_sup_right (LinearMap.mem_range_self _ _))
  have hsup : cyclesAt ind cnt k = LinearMap.range Ik ⊔ boundaries ind cnt k :=
    le_antisymm hcyc (sup_le hIcyc (boundaries_le_cyclesAt h k))
  have hinf : LinearMap.range Ik ⊓ boundaries ind cnt k = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨y, rfl⟩, ⟨w, hw⟩⟩
    rw [hdisj y w hw.symm, map_zero]
    exact Submodule.zero_mem _
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range Ik)
    (boundaries ind cnt k)
  rw [← hsup, hinf, finrank_bot, add_zero, LinearMap.finrank_range_of_inj hinj,
    finrank_chains] at hdim
  have hb := betti_add_bdim h k
  have hbd : Module.finrank K (boundaries ind cnt k) = bdim ind cnt k := rfl
  omega


/-- Over a field every matrix has a generalised inverse: some `G` with
`A G A = A`.  Take a right inverse of `A` onto its range, composed with a
projection of the target onto that range. -/
theorem exists_mul_mul_eq_self {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    [DecidableEq n] (A : Matrix m n K) : ∃ G : Matrix n m K, A * G * A = A := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective (Matrix.toLin' A).rangeRestrict
    (LinearMap.range_rangeRestrict _)
  obtain ⟨t, ht⟩ := LinearMap.exists_leftInverse_of_injective
    (LinearMap.range (Matrix.toLin' A)).subtype (Submodule.ker_subtype _)
  refine ⟨LinearMap.toMatrix' (s ∘ₗ t), ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
  refine LinearMap.ext fun x => ?_
  have h1 : t (Matrix.toLin' A x) = (Matrix.toLin' A).rangeRestrict x :=
    LinearMap.congr_fun ht ((Matrix.toLin' A).rangeRestrict x)
  have h2 : (Matrix.toLin' A).rangeRestrict (s ((Matrix.toLin' A).rangeRestrict x))
      = (Matrix.toLin' A).rangeRestrict x :=
    LinearMap.congr_fun hs ((Matrix.toLin' A).rangeRestrict x)
  show Matrix.toLin' A (s (t (Matrix.toLin' A x))) = Matrix.toLin' A x
  rw [h1]
  exact congrArg Subtype.val h2

/-- **Every complex of finite-dimensional vector spaces retracts onto its
homology.**  For a based complex over a field there is a based graded vector
space `CH` (with zero differential) and matrices `I`, `P`, `Hm` forming a
deformation retraction in the sense of `betti_eq_numCrit_of_retract`.

Construction: `G` is a generalised inverse of the total differential `∂`, so
`πZ = 1 − G∂` projects onto the cycles.  In each degree `k` let `Zₖ` and `Bₖ` be
the cycles and boundaries of degree `k`, choose a complement `Cₖ` of `Bₖ` in the
whole space and put `Uₖ = Cₖ ∩ Zₖ`, a complement of `Bₖ` inside `Zₖ`.  `CH`
indexes a basis of the `Uₖ`, `I` is the inclusion of that basis, `P` takes the
coordinates of the projection onto `Cₖ` (along `Bₖ`) of the degree `k` part of
`πZ x`, and `Hm = −G (πZ − I P)` is the homotopy.  The identity
`I P = 1 + ∂ Hm + Hm ∂` holds because `πZ − I P` takes values in the
boundaries, on which `∂ G` is the identity. -/
theorem exists_retract [DecidableEq Crit] {ind : Crit → ℕ} {cnt : Crit → Crit → K}
    (h : BrokenPairs ind cnt) :
    ∃ (CH : Type) (_ : Fintype CH) (_ : DecidableEq CH) (indH : CH → ℕ)
      (I : Matrix Crit CH K) (P : Matrix CH Crit K) (Hm : Matrix Crit Crit K),
      (∀ c e, I c e ≠ 0 → ind c = indH e) ∧ totalD ind cnt * I = 0 ∧
      P * totalD ind cnt = 0 ∧ P * I = 1 ∧
      I * P = 1 + (totalD ind cnt * Hm + Hm * totalD ind cnt) := by
  obtain ⟨G, hG⟩ := exists_mul_mul_eq_self (totalD ind cnt)
  have hDD := totalD_mul_self h
  obtain ⟨N, hN⟩ : ∃ N, ∀ c, ind c ≤ N :=
    ⟨Finset.univ.sup ind, fun c => Finset.le_sup (Finset.mem_univ c)⟩
  have hDDv : ∀ x, totalD ind cnt *ᵥ (totalD ind cnt *ᵥ x) = 0 := fun x => by
    rw [Matrix.mulVec_mulVec, hDD, Matrix.zero_mulVec]
  have hGv : ∀ x, totalD ind cnt *ᵥ (G *ᵥ (totalD ind cnt *ᵥ x)) = totalD ind cnt *ᵥ x :=
    fun x => by
      rw [Matrix.mulVec_mulVec (totalD ind cnt *ᵥ x) (totalD ind cnt) G,
        Matrix.mulVec_mulVec x (totalD ind cnt * G) (totalD ind cnt), hG]
  -- the degree projections add up to the identity
  have sum_pr : ∀ x : Crit → K, ∑ k : Fin (N + 1), extChains ind k (resChains ind k x) = x := by
    intro x
    funext c
    rw [Finset.sum_apply, Finset.sum_eq_single ⟨ind c, Nat.lt_succ_of_le (hN c)⟩]
    · rw [extChains_resChains_apply, if_pos rfl]
    · intro k _ hk
      rw [extChains_resChains_apply, if_neg]
      intro hc
      exact hk (Fin.ext hc.symm)
    · intro hc
      exact absurd (Finset.mem_univ _) hc
  have D_pr : ∀ (k : ℕ) (y : Crit → K), totalD ind cnt *ᵥ y = 0 →
      totalD ind cnt *ᵥ extChains ind k (resChains ind k y) = 0 := by
    intro k y hy
    cases k with
    | zero => exact totalD_mulVec_extChains_zero ind cnt _
    | succ k =>
        rw [totalD_mulVec_extChains, ← resChains_totalD_mulVec, hy, map_zero, map_zero]
  have pr_D : ∀ (k : ℕ) (y : Crit → K),
      extChains ind k (resChains ind k (totalD ind cnt *ᵥ y))
        = totalD ind cnt *ᵥ extChains ind (k + 1) (resChains ind (k + 1) y) := by
    intro k y
    rw [totalD_mulVec_extChains, resChains_totalD_mulVec]
  -- the projection onto the cycles
  let πZ : (Crit → K) →ₗ[K] (Crit → K) :=
    LinearMap.id - G.mulVecLin ∘ₗ (totalD ind cnt).mulVecLin
  have πZ_apply : ∀ x, πZ x = x - G *ᵥ (totalD ind cnt *ᵥ x) := fun x => rfl
  have D_πZ : ∀ x, totalD ind cnt *ᵥ πZ x = 0 := by
    intro x
    rw [πZ_apply, Matrix.mulVec_sub, hGv, sub_self]
  have πZ_fix : ∀ y, totalD ind cnt *ᵥ y = 0 → πZ y = y := by
    intro y hy
    rw [πZ_apply, hy, Matrix.mulVec_zero, sub_zero]
  -- cycles and boundaries of degree `k`, and a complement of the boundaries
  let V : ℕ → Submodule K (Crit → K) := fun k =>
    LinearMap.ker (totalD ind cnt).mulVecLin ⊓ LinearMap.range (extChains (K := K) ind k)
  let W : ℕ → Submodule K (Crit → K) := fun k =>
    LinearMap.range (totalD ind cnt).mulVecLin ⊓ LinearMap.range (extChains (K := K) ind k)
  have hWV : ∀ k, W k ≤ V k := by
    intro k x hx
    obtain ⟨⟨y, rfl⟩, hx2⟩ := Submodule.mem_inf.mp hx
    exact Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr (hDDv y), hx2⟩
  choose C hC using fun k => Submodule.exists_isCompl (W k)
  let U : ℕ → Submodule K (Crit → K) := fun k => C k ⊓ V k
  let prC : (k : ℕ) → (Crit → K) →ₗ[K] (Crit → K) := fun k =>
    Submodule.projection (C k) (W k) (hC k).symm
  have hU : ∀ (k : ℕ) (v : Crit → K), v ∈ V k → prC k v ∈ U k := by
    intro k v hv
    refine Submodule.mem_inf.mpr ⟨Submodule.projection_apply_mem _ _, ?_⟩
    have h1 : v - prC k v ∈ W k := Submodule.sub_projection_mem (hC k).symm v
    have h3 := Submodule.sub_mem (V k) hv (hWV k h1)
    rwa [sub_sub_cancel] at h3
  have hv : ∀ (k : ℕ) (x : Crit → K), extChains ind k (resChains ind k (πZ x)) ∈ V k :=
    fun k x => Submodule.mem_inf.mpr
      ⟨LinearMap.mem_ker.mpr (D_pr k _ (D_πZ x)), LinearMap.mem_range_self _ _⟩
  have hvU : ∀ (k : ℕ) (x : Crit → K),
      prC k (extChains ind k (resChains ind k (πZ x))) ∈ U k :=
    fun k x => hU k _ (hv k x)
  let b : (k : ℕ) → Module.Basis (Fin (Module.finrank K (U k))) K (U k) :=
    fun k => Module.finBasis K (U k)
  let CH : Type := Σ k : Fin (N + 1), Fin (Module.finrank K (U k))
  let u : CH → (Crit → K) := fun e => ((b e.1 e.2 : U e.1) : Crit → K)
  have hu_U : ∀ e : CH, u e ∈ U e.1 := fun e => (b e.1 e.2).2
  have hu_mem : ∀ e : CH, u e ∈ V e.1 := fun e => (Submodule.mem_inf.mp (hu_U e)).2
  have hu_C : ∀ e : CH, u e ∈ C e.1 := fun e => (Submodule.mem_inf.mp (hu_U e)).1
  have hu_ker : ∀ e : CH, totalD ind cnt *ᵥ u e = 0 := fun e =>
    LinearMap.mem_ker.mp (Submodule.mem_inf.mp (hu_mem e)).1
  have hu_deg : ∀ (e : CH) (c : Crit), ind c ≠ e.1 → u e c = 0 := by
    intro e c hc
    obtain ⟨w, hw⟩ := (Submodule.mem_inf.mp (hu_mem e)).2
    rw [← hw]
    exact extChains_apply_of_ne w hc
  have pr_u : ∀ (k : ℕ) (e : CH),
      extChains ind k (resChains ind k (u e)) = if (e.1 : ℕ) = k then u e else 0 := by
    intro k e
    funext c
    rw [extChains_resChains_apply]
    by_cases hk : (e.1 : ℕ) = k
    · rw [if_pos hk]
      by_cases hc : ind c = k
      · rw [if_pos hc]
      · rw [if_neg hc, hu_deg e c (by omega)]
    · rw [if_neg hk, Pi.zero_apply]
      by_cases hc : ind c = k
      · rw [if_pos hc, hu_deg e c (by omega)]
      · rw [if_neg hc]
  -- the matrices
  let Pl : (Crit → K) →ₗ[K] (CH → K) := LinearMap.pi fun e : CH =>
    (Finsupp.lapply e.2) ∘ₗ (b e.1).repr.toLinearMap ∘ₗ
      LinearMap.codRestrict (U e.1) (prC e.1 ∘ₗ extChains ind e.1 ∘ₗ resChains ind e.1 ∘ₗ πZ)
        (fun x => hvU e.1 x)
  let I : Matrix Crit CH K := Matrix.of fun c e => u e c
  let P : Matrix CH Crit K := LinearMap.toMatrix' Pl
  have hPx : ∀ x, P *ᵥ x = Pl x := fun x => LinearMap.toMatrix'_mulVec Pl x
  have hIy : ∀ y : CH → K, I *ᵥ y = ∑ e, y e • u e := by
    intro y
    funext c
    rw [Finset.sum_apply]
    show ∑ e, u e c * y e = _
    exact Finset.sum_congr rfl fun e _ => by rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  have hPl_D : ∀ x, Pl (totalD ind cnt *ᵥ x) = 0 := by
    intro x
    funext e
    have hmem : extChains ind e.1 (resChains ind e.1 (πZ (totalD ind cnt *ᵥ x))) ∈ W e.1 := by
      rw [πZ_fix _ (hDDv x)]
      refine Submodule.mem_inf.mpr ⟨?_, LinearMap.mem_range_self _ _⟩
      rw [pr_D]
      exact LinearMap.mem_range_self _ _
    have h1 : LinearMap.codRestrict (U e.1)
        (prC e.1 ∘ₗ extChains ind e.1 ∘ₗ resChains ind e.1 ∘ₗ πZ)
        (fun x => hvU e.1 x) (totalD ind cnt *ᵥ x) = 0 :=
      Subtype.ext (Submodule.projection_apply_of_mem_right (hC e.1).symm hmem)
    show (b e.1).repr (LinearMap.codRestrict (U e.1)
      (prC e.1 ∘ₗ extChains ind e.1 ∘ₗ resChains ind e.1 ∘ₗ πZ)
        (fun x => hvU e.1 x) (totalD ind cnt *ᵥ x)) e.2 = 0
    rw [h1, map_zero, Finsupp.zero_apply]
  have hPu : ∀ e e' : CH, Pl (u e) e' = if e' = e then 1 else 0 := by
    rintro ⟨k, j⟩ ⟨k', j'⟩
    by_cases hk : k = k'
    · subst hk
      have hvL : LinearMap.codRestrict (U k)
          (prC k ∘ₗ extChains ind k ∘ₗ resChains ind k ∘ₗ πZ)
          (fun x => hvU k x) (u ⟨k, j⟩) = b k j := by
        apply Subtype.ext
        show prC k (extChains ind k (resChains ind k (πZ (u ⟨k, j⟩)))) = u ⟨k, j⟩
        rw [πZ_fix _ (hu_ker _), pr_u, if_pos rfl]
        exact Submodule.projection_apply_of_mem_left (hC k).symm (hu_C ⟨k, j⟩)
      show (b k).repr (LinearMap.codRestrict (U k)
        (prC k ∘ₗ extChains ind k ∘ₗ resChains ind k ∘ₗ πZ)
          (fun x => hvU k x) (u ⟨k, j⟩)) j' = _
      rw [hvL, Module.Basis.repr_self, Finsupp.single_apply]
      by_cases hj : j = j'
      · subst hj
        rw [if_pos rfl, if_pos rfl]
      · rw [if_neg hj, if_neg]
        intro heq
        exact hj (eq_of_heq (Sigma.mk.inj_iff.mp heq).2).symm
    · have hvL : LinearMap.codRestrict (U k')
          (prC k' ∘ₗ extChains ind k' ∘ₗ resChains ind k' ∘ₗ πZ)
          (fun x => hvU k' x) (u ⟨k, j⟩) = 0 := by
        apply Subtype.ext
        show prC k' (extChains ind k' (resChains ind k' (πZ (u ⟨k, j⟩)))) = 0
        rw [πZ_fix _ (hu_ker _), pr_u, if_neg (fun h => hk (Fin.ext h)), map_zero]
      show (b k').repr (LinearMap.codRestrict (U k')
        (prC k' ∘ₗ extChains ind k' ∘ₗ resChains ind k' ∘ₗ πZ)
          (fun x => hvU k' x) (u ⟨k, j⟩)) j' = _
      rw [hvL, map_zero, Finsupp.zero_apply, if_neg]
      intro heq
      exact hk (Sigma.mk.inj_iff.mp heq).1.symm
  have hIPl : ∀ x, I *ᵥ Pl x = ∑ k : Fin (N + 1),
      prC k (extChains ind k (resChains ind k (πZ x))) := by
    intro x
    rw [hIy, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : prC k (extChains ind k (resChains ind k (πZ x)))
        = ((LinearMap.codRestrict (U k) (prC k ∘ₗ extChains ind k ∘ₗ resChains ind k ∘ₗ πZ)
          (fun x => hvU k x) x : U k) : Crit → K) := rfl
    rw [h1, ← (b k).sum_repr (LinearMap.codRestrict (U k)
        (prC k ∘ₗ extChains ind k ∘ₗ resChains ind k ∘ₗ πZ) (fun x => hvU k x) x),
      Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul]
    rfl
  have hY : ∀ x, (1 - G * totalD ind cnt - I * P) *ᵥ x
      ∈ LinearMap.range (totalD ind cnt).mulVecLin := by
    intro x
    have e1 : (1 - G * totalD ind cnt - I * P) *ᵥ x = πZ x - I *ᵥ Pl x := by
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
        ← Matrix.mulVec_mulVec, hPx]
      rfl
    have e2 : πZ x - I *ᵥ Pl x = ∑ k : Fin (N + 1),
        (extChains ind k (resChains ind k (πZ x))
          - prC k (extChains ind k (resChains ind k (πZ x)))) := by
      rw [Finset.sum_sub_distrib, sum_pr, hIPl]
    rw [e1, e2]
    refine Submodule.sum_mem _ fun k _ => ?_
    exact (Submodule.mem_inf.mp (Submodule.sub_projection_mem (hC k).symm
      (extChains ind k (resChains ind k (πZ x))))).1
  have hDI : totalD ind cnt * I = 0 := by
    ext c e
    rw [Matrix.mul_apply, Matrix.zero_apply]
    exact congrFun (hu_ker e) c
  have hPD : P * totalD ind cnt = 0 := by
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [← Matrix.mulVec_mulVec, hPx, hPl_D, Matrix.zero_mulVec]
  have hPI : P * I = 1 := by
    ext e' e
    rw [Matrix.one_apply]
    show (P *ᵥ u e) e' = _
    rw [hPx, hPu]
  have hYD : (1 - G * totalD ind cnt - I * P) * totalD ind cnt = totalD ind cnt := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_assoc G (totalD ind cnt) (totalD ind cnt), hDD, Matrix.mul_zero,
      Matrix.mul_assoc I P (totalD ind cnt), hPD, Matrix.mul_zero, sub_zero, sub_zero]
  have hDGY : totalD ind cnt * G * (1 - G * totalD ind cnt - I * P)
      = 1 - G * totalD ind cnt - I * P := by
    apply Matrix.ext_of_mulVec_single
    intro i
    obtain ⟨z, hz⟩ := hY (Pi.single i 1)
    rw [← Matrix.mulVec_mulVec, ← hz]
    show (totalD ind cnt * G) *ᵥ (totalD ind cnt *ᵥ z) = totalD ind cnt *ᵥ z
    rw [Matrix.mulVec_mulVec, hG]
  refine ⟨CH, inferInstance, inferInstance, fun e => (e.1 : ℕ), I, P,
    -(G * (1 - G * totalD ind cnt - I * P)), ?_, hDI, hPD, hPI, ?_⟩
  · intro c e hce
    by_contra hne
    exact hce (hu_deg e c hne)
  · rw [Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, hDGY, Matrix.mul_assoc, hYD]
    abel


end Retraction

section Kunneth

variable {K : Type*} [Field K] {Crit₁ Crit₂ : Type*} [Fintype Crit₁] [Fintype Crit₂]
  [DecidableEq Crit₁] [DecidableEq Crit₂]

open scoped Kronecker

/-- The index on `Crit(f + g) = Crit f × Crit g`: `Ind(a, a') = Ind a + Ind a'`. -/
def prodIndex (ind₁ : Crit₁ → ℕ) (ind₂ : Crit₂ → ℕ) : Crit₁ × Crit₂ → ℕ :=
  fun p => ind₁ p.1 + ind₂ p.2

/-- The count function of the product, as computed in §4.2.  (For critical
points of consecutive indices at most one of the two tests can succeed, so the
sum written here agrees with the book's case distinction.) -/
def prodCount (cnt₁ : Crit₁ → Crit₁ → K) (cnt₂ : Crit₂ → Crit₂ → K) :
    Crit₁ × Crit₂ → Crit₁ × Crit₂ → K :=
  fun a b => (if a.1 = b.1 then cnt₂ a.2 b.2 else 0) + (if a.2 = b.2 then cnt₁ a.1 b.1 else 0)

omit [Fintype Crit₁] [Fintype Crit₂] in
/-- The coefficient of `∂_{C⊗D}` between two basis elements: `∂ ⊗ 1 + 1 ⊗ ∂`
counts a connection in the second factor when the first is unchanged, and one in
the first factor when the second is unchanged. -/
theorem prodCount_apply (cnt₁ : Crit₁ → Crit₁ → K) (cnt₂ : Crit₂ → Crit₂ → K)
    (a₁ b₁ : Crit₁) (a₂ b₂ : Crit₂) :
    prodCount cnt₁ cnt₂ (a₁, a₂) (b₁, b₂)
      = (if a₁ = b₁ then cnt₂ a₂ b₂ else 0) + (if a₂ = b₂ then cnt₁ a₁ b₁ else 0) := rfl

/-- The same for the product complex: a sum over the critical points of `C ⊗ D`
of total degree `m` is a double sum over the two factors, restricted to the
pairs of degrees adding up to `m`.  This is the statement that
`(C ⊗ D)ₘ = ⨁_{i+j=m} Cᵢ ⊗ Dⱼ` (§15.1.a), read on the canonical bases. -/
theorem sum_critSet_prod {Crit₁ Crit₂ : Type*} [Fintype Crit₁] [Fintype Crit₂]
    {M : Type*} [AddCommMonoid M] (ind₁ : Crit₁ → ℕ) (ind₂ : Crit₂ → ℕ) (m : ℕ)
    (f : Crit₁ × Crit₂ → M) :
    ∑ c : CritSet (prodIndex ind₁ ind₂) m, f c.1
      = ∑ c₁ : Crit₁, ∑ c₂ : Crit₂, if ind₁ c₁ + ind₂ c₂ = m then f (c₁, c₂) else 0 := by
  have h := sum_critSet_eq (prodIndex ind₁ ind₂) m f
  rw [Fintype.sum_prod_type] at h
  exact h

/-- **Proposition 4.2.1** (algebraic half).  `Φ(a ⊗ a') = (a, a')` identifies
`(C⋆(f) ⊗ C⋆(g), ∂_X ⊗ 1 + 1 ⊗ ∂_Y)` with `(C⋆(f + g), ∂_(X,Y))`; in particular
the product differential squares to zero.  As the book points out, without signs
this holds only in characteristic `2` — the cross terms `∂_X ⊗ ∂_Y` cancel in
pairs there, which is why the passage to homology in Corollary 4.2.2 is stated
over `Z/2`.

Proved: expanding `∂∂` gives four terms.  The two "square" terms vanish because
`∂` does in each factor; the two cross terms are *equal*, so they cancel exactly
when `2 = 0`, which is the book's footnote about `Z/2`. -/
theorem brokenPairs_prod {ind₁ : Crit₁ → ℕ} {ind₂ : Crit₂ → ℕ}
    {cnt₁ : Crit₁ → Crit₁ → K} {cnt₂ : Crit₂ → Crit₂ → K}
    (h₁ : BrokenPairs ind₁ cnt₁) (h₂ : BrokenPairs ind₂ cnt₂) (h2 : (2 : K) = 0) :
    BrokenPairs (prodIndex ind₁ ind₂) (prodCount cnt₁ cnt₂) := by
  intro k a b
  obtain ⟨⟨a₁, a₂⟩, ha⟩ := a
  obtain ⟨⟨b₁, b₂⟩, hb⟩ := b
  simp only [prodIndex] at ha hb
  show (∑ c : CritSet (prodIndex ind₁ ind₂) (k + 1),
      prodCount cnt₁ cnt₂ (a₁, a₂) c.1 * prodCount cnt₁ cnt₂ c.1 (b₁, b₂)) = 0
  have key : (∑ c : CritSet (prodIndex ind₁ ind₂) (k + 1),
        prodCount cnt₁ cnt₂ (a₁, a₂) c.1 * prodCount cnt₁ cnt₂ c.1 (b₁, b₂))
      = ∑ c₁ : Crit₁, ∑ c₂ : Crit₂,
          if ind₁ c₁ + ind₂ c₂ = k + 1 then
            prodCount cnt₁ cnt₂ (a₁, a₂) (c₁, c₂) * prodCount cnt₁ cnt₂ (c₁, c₂) (b₁, b₂)
          else 0 :=
    sum_critSet_prod ind₁ ind₂ (k + 1)
      (fun c => prodCount cnt₁ cnt₂ (a₁, a₂) c * prodCount cnt₁ cnt₂ c (b₁, b₂))
  have expand : ∀ (c₁ : Crit₁) (c₂ : Crit₂),
      (if ind₁ c₁ + ind₂ c₂ = k + 1 then
          prodCount cnt₁ cnt₂ (a₁, a₂) (c₁, c₂) * prodCount cnt₁ cnt₂ (c₁, c₂) (b₁, b₂) else 0)
      = (if ind₁ c₁ + ind₂ c₂ = k + 1 then
            (if a₁ = c₁ then cnt₂ a₂ c₂ else 0) * (if c₁ = b₁ then cnt₂ c₂ b₂ else 0) else 0)
        + (if ind₁ c₁ + ind₂ c₂ = k + 1 then
            (if a₁ = c₁ then cnt₂ a₂ c₂ else 0) * (if c₂ = b₂ then cnt₁ c₁ b₁ else 0) else 0)
        + (if ind₁ c₁ + ind₂ c₂ = k + 1 then
            (if a₂ = c₂ then cnt₁ a₁ c₁ else 0) * (if c₁ = b₁ then cnt₂ c₂ b₂ else 0) else 0)
        + (if ind₁ c₁ + ind₂ c₂ = k + 1 then
            (if a₂ = c₂ then cnt₁ a₁ c₁ else 0) * (if c₂ = b₂ then cnt₁ c₁ b₁ else 0) else 0) := by
    intro c₁ c₂
    simp only [prodCount_apply]
    split_ifs <;> ring
  have hS1 : (∑ c₁ : Crit₁, ∑ c₂ : Crit₂,
      if ind₁ c₁ + ind₂ c₂ = k + 1 then
        (if a₁ = c₁ then cnt₂ a₂ c₂ else 0) * (if c₁ = b₁ then cnt₂ c₂ b₂ else 0) else 0) = 0 := by
    rw [Finset.sum_eq_single a₁]
    · show (∑ c₂ : Crit₂, if ind₁ a₁ + ind₂ c₂ = k + 1 then
          (if a₁ = a₁ then cnt₂ a₂ c₂ else 0) * (if a₁ = b₁ then cnt₂ c₂ b₂ else 0) else 0) = 0
      by_cases hab : a₁ = b₁
      · have hbb : ind₁ b₁ = ind₁ a₁ := by rw [hab]
        have hsimp : ∀ c₂ : Crit₂,
            (if ind₁ a₁ + ind₂ c₂ = k + 1 then
              (if a₁ = a₁ then cnt₂ a₂ c₂ else 0) * (if a₁ = b₁ then cnt₂ c₂ b₂ else 0) else 0)
              = (if ind₂ c₂ = ind₂ b₂ + 1 then cnt₂ a₂ c₂ * cnt₂ c₂ b₂ else 0) := by
          intro c₂
          rw [if_pos hab, if_pos (rfl : a₁ = a₁)]
          by_cases hc : ind₂ c₂ = ind₂ b₂ + 1
          · rw [if_pos (show ind₁ a₁ + ind₂ c₂ = k + 1 by omega), if_pos hc]
          · rw [if_neg (show ¬(ind₁ a₁ + ind₂ c₂ = k + 1) by omega), if_neg hc]
        rw [Finset.sum_congr rfl fun c₂ _ => hsimp c₂]
        have hconv : (∑ c₂ : Crit₂, if ind₂ c₂ = ind₂ b₂ + 1 then cnt₂ a₂ c₂ * cnt₂ c₂ b₂ else 0)
            = ∑ c : CritSet ind₂ (ind₂ b₂ + 1), cnt₂ a₂ c.1 * cnt₂ c.1 b₂ :=
          (sum_critSet_eq ind₂ (ind₂ b₂ + 1) (fun c => cnt₂ a₂ c * cnt₂ c b₂)).symm
        rw [hconv]
        exact h₂ (ind₂ b₂) ⟨a₂, by omega⟩ ⟨b₂, rfl⟩
      · simp [hab]
    · intro c₁ _ hc₁
      simp [Ne.symm hc₁]
    · intro h
      exact absurd (Finset.mem_univ a₁) h
  have hS4 : (∑ c₁ : Crit₁, ∑ c₂ : Crit₂,
      if ind₁ c₁ + ind₂ c₂ = k + 1 then
        (if a₂ = c₂ then cnt₁ a₁ c₁ else 0) * (if c₂ = b₂ then cnt₁ c₁ b₁ else 0) else 0) = 0 := by
    have hin : ∀ c₁ : Crit₁,
        (∑ c₂ : Crit₂, if ind₁ c₁ + ind₂ c₂ = k + 1 then
          (if a₂ = c₂ then cnt₁ a₁ c₁ else 0) * (if c₂ = b₂ then cnt₁ c₁ b₁ else 0) else 0)
        = (if ind₁ c₁ + ind₂ a₂ = k + 1 then
            cnt₁ a₁ c₁ * (if a₂ = b₂ then cnt₁ c₁ b₁ else 0) else 0) := by
      intro c₁
      rw [Finset.sum_eq_single a₂]
      · simp
      · intro c₂ _ hc₂
        simp [Ne.symm hc₂]
      · intro h
        exact absurd (Finset.mem_univ a₂) h
    rw [Finset.sum_congr rfl fun c₁ _ => hin c₁]
    by_cases hab : a₂ = b₂
    · have hbb : ind₂ b₂ = ind₂ a₂ := by rw [hab]
      have hsimp : ∀ c₁ : Crit₁,
          (if ind₁ c₁ + ind₂ a₂ = k + 1 then
            cnt₁ a₁ c₁ * (if a₂ = b₂ then cnt₁ c₁ b₁ else 0) else 0)
          = (if ind₁ c₁ = ind₁ b₁ + 1 then cnt₁ a₁ c₁ * cnt₁ c₁ b₁ else 0) := by
        intro c₁
        rw [if_pos hab]
        by_cases hc : ind₁ c₁ = ind₁ b₁ + 1
        · rw [if_pos (show ind₁ c₁ + ind₂ a₂ = k + 1 by omega), if_pos hc]
        · rw [if_neg (show ¬(ind₁ c₁ + ind₂ a₂ = k + 1) by omega), if_neg hc]
      rw [Finset.sum_congr rfl fun c₁ _ => hsimp c₁]
      have hconv : (∑ c₁ : Crit₁, if ind₁ c₁ = ind₁ b₁ + 1 then cnt₁ a₁ c₁ * cnt₁ c₁ b₁ else 0)
          = ∑ c : CritSet ind₁ (ind₁ b₁ + 1), cnt₁ a₁ c.1 * cnt₁ c.1 b₁ :=
        (sum_critSet_eq ind₁ (ind₁ b₁ + 1) (fun c => cnt₁ a₁ c * cnt₁ c b₁)).symm
      rw [hconv]
      exact h₁ (ind₁ b₁) ⟨a₁, by omega⟩ ⟨b₁, rfl⟩
    · simp [hab]
  have hS2 : (∑ c₁ : Crit₁, ∑ c₂ : Crit₂,
      if ind₁ c₁ + ind₂ c₂ = k + 1 then
        (if a₁ = c₁ then cnt₂ a₂ c₂ else 0) * (if c₂ = b₂ then cnt₁ c₁ b₁ else 0) else 0)
      = (if ind₁ a₁ + ind₂ b₂ = k + 1 then cnt₂ a₂ b₂ * cnt₁ a₁ b₁ else 0) := by
    rw [Finset.sum_eq_single a₁]
    · rw [Finset.sum_eq_single b₂]
      · simp
      · intro c₂ _ hc₂
        simp [hc₂]
      · intro h
        exact absurd (Finset.mem_univ b₂) h
    · intro c₁ _ hc₁
      simp [Ne.symm hc₁]
    · intro h
      exact absurd (Finset.mem_univ a₁) h
  have hS3 : (∑ c₁ : Crit₁, ∑ c₂ : Crit₂,
      if ind₁ c₁ + ind₂ c₂ = k + 1 then
        (if a₂ = c₂ then cnt₁ a₁ c₁ else 0) * (if c₁ = b₁ then cnt₂ c₂ b₂ else 0) else 0)
      = (if ind₁ b₁ + ind₂ a₂ = k + 1 then cnt₁ a₁ b₁ * cnt₂ a₂ b₂ else 0) := by
    rw [Finset.sum_eq_single b₁]
    · rw [Finset.sum_eq_single a₂]
      · simp
      · intro c₂ _ hc₂
        simp [Ne.symm hc₂]
      · intro h
        exact absurd (Finset.mem_univ a₂) h
    · intro c₁ _ hc₁
      simp [hc₁]
    · intro h
      exact absurd (Finset.mem_univ b₁) h
  rw [key, Finset.sum_congr rfl (fun c₁ _ => Finset.sum_congr rfl (fun c₂ _ => expand c₁ c₂))]
  simp only [Finset.sum_add_distrib]
  rw [hS1, hS4, hS2, hS3]
  by_cases hC : ind₁ a₁ + ind₂ b₂ = k + 1
  · rw [if_pos hC, if_pos (show ind₁ b₁ + ind₂ a₂ = k + 1 by omega), zero_add, add_zero,
      show cnt₂ a₂ b₂ * cnt₁ a₁ b₁ + cnt₁ a₁ b₁ * cnt₂ a₂ b₂
        = 2 * (cnt₂ a₂ b₂ * cnt₁ a₁ b₁) by ring, h2, zero_mul]
  · rw [if_neg hC, if_neg (show ¬(ind₁ b₁ + ind₂ a₂ = k + 1) by omega)]
    simp

/-- **The graded vector space underlying the product complex**: the degree `k`
part of `C ⊗ D` has dimension `Σ_{i+j=k} dim Cᵢ · dim Dⱼ`, which is
`(C ⊗ D)ₖ = ⨁_{i+j=k} Cᵢ ⊗ Dⱼ` counted on the canonical bases. -/
theorem numCrit_prodIndex {Crit₁ Crit₂ : Type*} [Fintype Crit₁] [Fintype Crit₂]
    (ind₁ : Crit₁ → ℕ) (ind₂ : Crit₂ → ℕ) (k : ℕ) :
    numCrit (prodIndex ind₁ ind₂) k
      = ∑ i ∈ Finset.range (k + 1), numCrit ind₁ i * numCrit ind₂ (k - i) := by
  symm
  calc ∑ i ∈ Finset.range (k + 1), numCrit ind₁ i * numCrit ind₂ (k - i)
      = ∑ i ∈ Finset.range (k + 1), (∑ c₁ : Crit₁, if ind₁ c₁ = i then (1 : ℕ) else 0)
          * (∑ c₂ : Crit₂, if ind₂ c₂ = k - i then (1 : ℕ) else 0) :=
        Finset.sum_congr rfl fun i _ => by rw [numCrit_eq_sum, numCrit_eq_sum]
    _ = ∑ i ∈ Finset.range (k + 1), ∑ c₁ : Crit₁, ∑ c₂ : Crit₂,
          (if ind₁ c₁ = i then (1 : ℕ) else 0) * (if ind₂ c₂ = k - i then (1 : ℕ) else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun c₁ _ => Finset.mul_sum _ _ _
    _ = ∑ c₁ : Crit₁, ∑ c₂ : Crit₂, ∑ i ∈ Finset.range (k + 1),
          (if ind₁ c₁ = i then (1 : ℕ) else 0) * (if ind₂ c₂ = k - i then (1 : ℕ) else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c₁ _ => Finset.sum_comm
    _ = ∑ c₁ : Crit₁, ∑ c₂ : Crit₂, if ind₁ c₁ + ind₂ c₂ = k then (1 : ℕ) else 0 :=
        Finset.sum_congr rfl fun c₁ _ => Finset.sum_congr rfl fun c₂ _ =>
          sum_range_ite_mul k (ind₁ c₁) (ind₂ c₂)
    _ = numCrit (prodIndex ind₁ ind₂) k := by
        have h := numCrit_eq_sum (prodIndex ind₁ ind₂) k
        rw [Fintype.sum_prod_type] at h
        exact h.symm

omit [Fintype Crit₁] [Fintype Crit₂] in
/-- The total differential of the product complex is `∂ ⊗ 1 + 1 ⊗ ∂`, as a
Kronecker product of matrices. -/
theorem totalD_prod (ind₁ : Crit₁ → ℕ) (ind₂ : Crit₂ → ℕ) (cnt₁ : Crit₁ → Crit₁ → K)
    (cnt₂ : Crit₂ → Crit₂ → K) :
    totalD (prodIndex ind₁ ind₂) (prodCount cnt₁ cnt₂)
      = totalD ind₁ cnt₁ ⊗ₖ (1 : Matrix Crit₂ Crit₂ K)
        + (1 : Matrix Crit₁ Crit₁ K) ⊗ₖ totalD ind₂ cnt₂ := by
  ext ⟨b₁, b₂⟩ ⟨a₁, a₂⟩
  have hp : ∀ x₁ x₂, prodIndex ind₁ ind₂ (x₁, x₂) = ind₁ x₁ + ind₂ x₂ := fun _ _ => rfl
  rw [Matrix.add_apply, Matrix.kronecker_apply, Matrix.kronecker_apply, Matrix.one_apply,
    Matrix.one_apply, totalD_apply, totalD_apply, totalD_apply, prodCount_apply]
  by_cases h1 : a₁ = b₁ <;> by_cases h2 : a₂ = b₂
  · subst h1; subst h2
    simp
  · subst h1
    rw [if_pos rfl, if_neg h2, if_neg (Ne.symm h2), if_pos rfl, add_zero, mul_zero, zero_add,
      one_mul]
    by_cases h : ind₂ a₂ = ind₂ b₂ + 1
    · rw [if_pos (show prodIndex ind₁ ind₂ (a₁, a₂) = prodIndex ind₁ ind₂ (a₁, b₂) + 1 by
        rw [hp, hp]; omega), if_pos h]
    · rw [if_neg (show ¬prodIndex ind₁ ind₂ (a₁, a₂) = prodIndex ind₁ ind₂ (a₁, b₂) + 1 by
        rw [hp, hp]; omega), if_neg h]
  · subst h2
    rw [if_neg h1, if_pos rfl, if_pos rfl, if_neg (Ne.symm h1), zero_add, mul_one, zero_mul,
      add_zero]
    by_cases h : ind₁ a₁ = ind₁ b₁ + 1
    · rw [if_pos (show prodIndex ind₁ ind₂ (a₁, a₂) = prodIndex ind₁ ind₂ (b₁, a₂) + 1 by
        rw [hp, hp]; omega), if_pos h]
    · rw [if_neg (show ¬prodIndex ind₁ ind₂ (a₁, a₂) = prodIndex ind₁ ind₂ (b₁, a₂) + 1 by
        rw [hp, hp]; omega), if_neg h]
  · rw [if_neg h1, if_neg h2, if_neg (Ne.symm h1), if_neg (Ne.symm h2), add_zero, mul_zero,
      zero_mul, add_zero, ite_self]

/-- **Künneth for retractions.**  Retractions of two complexes onto `H₁` and `H₂`
tensor to a retraction of the product complex onto `H₁ ⊗ H₂`, with homotopy
`Hm₁ ⊗ 1 + (I₁ P₁) ⊗ Hm₂`.  The two cross terms `Hm₁ ⊗ ∂₂` cancel because
`2 = 0`, exactly as in `brokenPairs_prod`. -/
theorem betti_prod_of_retract {ind₁ : Crit₁ → ℕ} {ind₂ : Crit₂ → ℕ}
    {cnt₁ : Crit₁ → Crit₁ → K} {cnt₂ : Crit₂ → Crit₂ → K}
    (hB : BrokenPairs (prodIndex ind₁ ind₂) (prodCount cnt₁ cnt₂)) (h2 : (2 : K) = 0)
    {CH₁ CH₂ : Type*} [Fintype CH₁] [DecidableEq CH₁] [Fintype CH₂] [DecidableEq CH₂]
    (indH₁ : CH₁ → ℕ) (I₁ : Matrix Crit₁ CH₁ K) (P₁ : Matrix CH₁ Crit₁ K)
    (Hm₁ : Matrix Crit₁ Crit₁ K)
    (hI₁ : ∀ c e, I₁ c e ≠ 0 → ind₁ c = indH₁ e) (hDI₁ : totalD ind₁ cnt₁ * I₁ = 0)
    (hPD₁ : P₁ * totalD ind₁ cnt₁ = 0) (hPI₁ : P₁ * I₁ = 1)
    (hH₁ : I₁ * P₁ = 1 + (totalD ind₁ cnt₁ * Hm₁ + Hm₁ * totalD ind₁ cnt₁))
    (indH₂ : CH₂ → ℕ) (I₂ : Matrix Crit₂ CH₂ K) (P₂ : Matrix CH₂ Crit₂ K)
    (Hm₂ : Matrix Crit₂ Crit₂ K)
    (hI₂ : ∀ c e, I₂ c e ≠ 0 → ind₂ c = indH₂ e) (hDI₂ : totalD ind₂ cnt₂ * I₂ = 0)
    (hPD₂ : P₂ * totalD ind₂ cnt₂ = 0) (hPI₂ : P₂ * I₂ = 1)
    (hH₂ : I₂ * P₂ = 1 + (totalD ind₂ cnt₂ * Hm₂ + Hm₂ * totalD ind₂ cnt₂)) (k : ℕ) :
    betti (prodIndex ind₁ ind₂) (prodCount cnt₁ cnt₂) k
      = numCrit (prodIndex indH₁ indH₂) k := by
  set D₁ := totalD ind₁ cnt₁ with hD₁
  set D₂ := totalD ind₂ cnt₂ with hD₂
  refine betti_eq_numCrit_of_retract hB (prodIndex indH₁ indH₂) (I₁ ⊗ₖ I₂) (P₁ ⊗ₖ P₂)
    (Hm₁ ⊗ₖ 1 + (I₁ * P₁) ⊗ₖ Hm₂) ?_ ?_ ?_ ?_ ?_ k
  · rintro ⟨c₁, c₂⟩ ⟨e₁, e₂⟩ hne
    rw [Matrix.kronecker_apply] at hne
    have h₁ := hI₁ c₁ e₁ (left_ne_zero_of_mul hne)
    have h₂ := hI₂ c₂ e₂ (right_ne_zero_of_mul hne)
    simp only [prodIndex]
    omega
  · rw [totalD_prod, ← hD₁, ← hD₂, Matrix.add_mul, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, hDI₁, hDI₂, Matrix.zero_kronecker, Matrix.kronecker_zero,
      add_zero]
  · rw [totalD_prod, ← hD₁, ← hD₂, Matrix.mul_add, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, hPD₁, hPD₂, Matrix.zero_kronecker, Matrix.kronecker_zero,
      add_zero]
  · rw [← Matrix.mul_kronecker_mul, hPI₁, hPI₂, Matrix.one_kronecker_one]
  · rw [totalD_prod, ← hD₁, ← hD₂]
    have hD1E : D₁ * (I₁ * P₁) = 0 := by rw [← Matrix.mul_assoc, hDI₁, Matrix.zero_mul]
    have hED1 : I₁ * P₁ * D₁ = 0 := by rw [Matrix.mul_assoc, hPD₁, Matrix.mul_zero]
    have hc : Hm₁ ⊗ₖ D₂ + Hm₁ ⊗ₖ D₂ = 0 := by
      rw [← two_smul K (Hm₁ ⊗ₖ D₂), h2, zero_smul]
    have hL : I₁ ⊗ₖ I₂ * P₁ ⊗ₖ P₂ = 1 + (D₁ * Hm₁) ⊗ₖ (1 : Matrix Crit₂ Crit₂ K)
        + (Hm₁ * D₁) ⊗ₖ (1 : Matrix Crit₂ Crit₂ K) + (I₁ * P₁) ⊗ₖ (D₂ * Hm₂)
        + (I₁ * P₁) ⊗ₖ (Hm₂ * D₂) := by
      rw [← Matrix.mul_kronecker_mul, hH₂, Matrix.kronecker_add, Matrix.kronecker_add]
      have hE : (I₁ * P₁) ⊗ₖ (1 : Matrix Crit₂ Crit₂ K)
          = 1 + (D₁ * Hm₁) ⊗ₖ (1 : Matrix Crit₂ Crit₂ K) + (Hm₁ * D₁) ⊗ₖ (1 : Matrix Crit₂ Crit₂ K) := by
        rw [hH₁, Matrix.add_kronecker, Matrix.add_kronecker, Matrix.one_kronecker_one]
        abel
      rw [hE]
      abel
    have hR : (D₁ ⊗ₖ (1 : Matrix Crit₂ Crit₂ K) + (1 : Matrix Crit₁ Crit₁ K) ⊗ₖ D₂)
          * (Hm₁ ⊗ₖ (1 : Matrix Crit₂ Crit₂ K) + (I₁ * P₁) ⊗ₖ Hm₂)
        + (Hm₁ ⊗ₖ (1 : Matrix Crit₂ Crit₂ K) + (I₁ * P₁) ⊗ₖ Hm₂)
          * (D₁ ⊗ₖ (1 : Matrix Crit₂ Crit₂ K) + (1 : Matrix Crit₁ Crit₁ K) ⊗ₖ D₂)
        = (D₁ * Hm₁) ⊗ₖ (1 : Matrix Crit₂ Crit₂ K) + (Hm₁ * D₁) ⊗ₖ (1 : Matrix Crit₂ Crit₂ K)
          + (I₁ * P₁) ⊗ₖ (D₂ * Hm₂) + (I₁ * P₁) ⊗ₖ (Hm₂ * D₂)
          + (Hm₁ ⊗ₖ D₂ + Hm₁ ⊗ₖ D₂) := by
      simp only [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
        hD1E, hED1, Matrix.zero_kronecker]
      abel
    rw [hL, hR, hc, add_zero]
    abel


/-- **Corollaries 4.2.2 and 4.2.3 (the Künneth formula).**  Over a field of
characteristic `2` — in particular over `Z/2` — the homology of the product
complex is the tensor product of the homologies, so the Betti numbers satisfy
`βₖ(M × N) = Σ_{i+j=k} βᵢ(M) βⱼ(N)`.

Proved.  Each factor retracts onto a graded vector space with zero differential
whose dimensions are its Betti numbers (`exists_retract`,
`betti_eq_numCrit_of_retract`); the Kronecker product of the two retractions is
a retraction of the product complex (`betti_prod_of_retract`, where `2 = 0`
cancels the cross terms exactly as in `brokenPairs_prod`), and the dimension
count `numCrit_prodIndex` finishes.  This replaces the book's inductive
splitting argument, which changes basis and so does not fit the based model. -/
theorem betti_prod {ind₁ : Crit₁ → ℕ} {ind₂ : Crit₂ → ℕ}
    {cnt₁ : Crit₁ → Crit₁ → K} {cnt₂ : Crit₂ → Crit₂ → K}
    (h₁ : BrokenPairs ind₁ cnt₁) (h₂ : BrokenPairs ind₂ cnt₂) (h2 : (2 : K) = 0) (k : ℕ) :
    betti (prodIndex ind₁ ind₂) (prodCount cnt₁ cnt₂) k
      = ∑ i ∈ Finset.range (k + 1), betti ind₁ cnt₁ i * betti ind₂ cnt₂ (k - i) := by
  obtain ⟨CH₁, _, _, indH₁, I₁, P₁, Hm₁, hI₁, hDI₁, hPD₁, hPI₁, hH₁⟩ := exists_retract h₁
  obtain ⟨CH₂, _, _, indH₂, I₂, P₂, Hm₂, hI₂, hDI₂, hPD₂, hPI₂, hH₂⟩ := exists_retract h₂
  rw [betti_prod_of_retract (brokenPairs_prod h₁ h₂ h2) h2 indH₁ I₁ P₁ Hm₁ hI₁ hDI₁ hPD₁ hPI₁
    hH₁ indH₂ I₂ P₂ Hm₂ hI₂ hDI₂ hPD₂ hPI₂ hH₂ k, numCrit_prodIndex]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [betti_eq_numCrit_of_retract h₁ indH₁ I₁ P₁ Hm₁ hI₁ hDI₁ hPD₁ hPI₁ hH₁,
    betti_eq_numCrit_of_retract h₂ indH₂ I₂ P₂ Hm₂ hI₂ hDI₂ hPD₂ hPI₂ hH₂]

end Kunneth

/-! ## §4.3 Poincaré duality

The critical points of index `k` of `f` are the critical points of index `n − k`
of `−f`, and `−X` is a pseudo-gradient adapted to `−f`; a trajectory of `X` from
`a` to `b` is a trajectory of `−X` from `b` to `a`.  So the complex of `−f` is
the complex of `f` with the grading reversed and the differential transposed:
`C_{n−k}(−f) = Cₖ(f)⋆` and `∂_{−X} = ᵗ∂_X`.

Both halves are visible in the data: `dualCount cnt a b = cnt b a`, and the
index function of `−f` is any `ind'` with `ind c + ind' c = n`. -/

section Duality

open scoped Matrix

variable {K : Type*} [Field K] {Crit : Type*} [Fintype Crit]

/-- The matrix of `∂ₖ : Cₖ₊₁ → Cₖ` in the bases of critical points. -/
def diffMatrix (ind : Crit → ℕ) (cnt : Crit → Crit → K) (k : ℕ) :
    Matrix (CritSet ind k) (CritSet ind (k + 1)) K :=
  Matrix.of fun b a => cnt a.1 b.1

theorem dLin_eq_mulVecLin (ind : Crit → ℕ) (cnt : Crit → Crit → K) (k : ℕ) :
    dLin ind cnt k = (diffMatrix ind cnt k).mulVecLin := by
  refine LinearMap.ext fun x => funext fun b => ?_
  show (∑ a : CritSet ind (k + 1), x a * cnt a.1 b.1) = _
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, diffMatrix, Matrix.of_apply]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem bdim_eq_rank (ind : Crit → ℕ) (cnt : Crit → Crit → K) (k : ℕ) :
    bdim ind cnt k = (diffMatrix ind cnt k).rank := by
  show Module.finrank K (LinearMap.range (dLin ind cnt k)) = _
  rw [dLin_eq_mulVecLin]
  rfl

/-- The count function of `−f`: the transpose of that of `f` (§4.3). -/
def dualCount (cnt : Crit → Crit → K) : Crit → Crit → K := fun a b => cnt b a

variable {ind ind' : Crit → ℕ} {cnt : Crit → Crit → K} {n : ℕ}

/-- A critical point of index `k` for `f` is a critical point of index `n − k`
for `−f` (Remark 1.3.3, `MorseFloer.Chapter1.index_neg_add_index`, is what makes
the indices add up to `n`). -/
def dualCritEquiv (hn : ∀ c, ind c + ind' c = n) {k j : ℕ} (hkj : k + j = n) :
    CritSet ind' j ≃ CritSet ind k :=
  Equiv.subtypeEquivRight fun c => by have := hn c; omega

/-- `−f` has as many critical points of index `n − k` as `f` has of index `k`. -/
theorem numCrit_dual (hn : ∀ c, ind c + ind' c = n) {k j : ℕ} (hkj : k + j = n) :
    numCrit ind' j = numCrit ind k :=
  Fintype.card_congr (dualCritEquiv hn hkj)

/-- The differential of the dual complex is the transpose of the differential of
the original one, so it has the same rank.  This is where Poincaré duality
actually happens; the linear algebra is `Matrix.rank_transpose`. -/
theorem bdim_dual (hn : ∀ c, ind c + ind' c = n) {k j : ℕ} (hkj : k + j + 1 = n) :
    bdim ind' (dualCount cnt) j = bdim ind cnt k := by
  rw [bdim_eq_rank, bdim_eq_rank,
    show diffMatrix ind' (dualCount cnt) j
        = (diffMatrix ind cnt k).transpose.submatrix
            (dualCritEquiv hn (show (k + 1) + j = n by omega))
            (dualCritEquiv hn (show k + (j + 1) = n by omega)) from rfl,
    Matrix.rank_submatrix, Matrix.rank_transpose]

/-- **Proposition 4.3.1 (Poincaré duality).**  For a closed manifold of
dimension `n`, `HMₖ(V; Z/2)` and `HM_{n−k}(V; Z/2)` have the same dimension.

Here `ind'` is the index function of `−f` (so `ind c + ind' c = n`, which is
Remark 1.3.3) and `dualCount cnt` is the transposed count function, i.e. the
complex of `−f`; the conclusion is `β_{n−k}(−f) = βₖ(f)`.  The proof is the one
the book indicates: the two complexes have the same numbers of generators in
dual degrees and their differentials are transposes of each other, hence have
equal ranks, and the Betti numbers are determined by those data. -/
theorem betti_dual (h : BrokenPairs ind cnt) (h' : BrokenPairs ind' (dualCount cnt))
    (hn : ∀ c, ind c + ind' c = n) {k j : ℕ} (hkj : k + j = n) :
    betti ind' (dualCount cnt) j = betti ind cnt k := by
  have hind : ∀ c, ind c ≤ n := fun c => by have := hn c; omega
  have hind' : ∀ c, ind' c ≤ n := fun c => by have := hn c; omega
  have hc : numCrit ind' j = numCrit ind k := numCrit_dual hn hkj
  cases k with
  | zero =>
      cases j with
      | zero =>
          have hn0 : n = 0 := by omega
          have hb : bdim ind cnt 0 = 0 :=
            bdim_eq_zero_of_isEmpty (isEmpty_critSet hind (by omega))
          have hb' : bdim ind' (dualCount cnt) 0 = 0 :=
            bdim_eq_zero_of_isEmpty (isEmpty_critSet hind' (by omega))
          have hA := numCrit_zero_eq h (ind := ind) (cnt := cnt)
          have hA' := numCrit_zero_eq h' (ind := ind') (cnt := dualCount cnt)
          omega
      | succ j₀ =>
          have hb' : bdim ind' (dualCount cnt) (j₀ + 1) = 0 :=
            bdim_eq_zero_of_isEmpty (isEmpty_critSet hind' (by omega))
          have hbd : bdim ind' (dualCount cnt) j₀ = bdim ind cnt 0 :=
            bdim_dual hn (by omega)
          have hA := numCrit_zero_eq h (ind := ind) (cnt := cnt)
          have hB' := numCrit_succ_eq h' (ind := ind') (cnt := dualCount cnt) j₀
          omega
  | succ k₀ =>
      cases j with
      | zero =>
          have hb : bdim ind cnt (k₀ + 1) = 0 :=
            bdim_eq_zero_of_isEmpty (isEmpty_critSet hind (by omega))
          have hbd : bdim ind' (dualCount cnt) 0 = bdim ind cnt k₀ :=
            bdim_dual hn (by omega)
          have hB := numCrit_succ_eq h (ind := ind) (cnt := cnt) k₀
          have hA' := numCrit_zero_eq h' (ind := ind') (cnt := dualCount cnt)
          omega
      | succ j₀ =>
          have hbd₁ : bdim ind' (dualCount cnt) j₀ = bdim ind cnt (k₀ + 1) :=
            bdim_dual hn (by omega)
          have hbd₂ : bdim ind' (dualCount cnt) (j₀ + 1) = bdim ind cnt k₀ :=
            bdim_dual hn (by omega)
          have hB := numCrit_succ_eq h (ind := ind) (cnt := cnt) k₀
          have hB' := numCrit_succ_eq h' (ind := ind') (cnt := dualCount cnt) j₀
          omega

/-- Over `ℤ` the free rank of `Zₖ / Bₖ` is `rank Zₖ − rank Bₖ` (rank–nullity holds over a
domain). -/
theorem finrank_int_quot_add {ind : Crit → ℕ} {cntZ : Crit → Crit → ℤ}
    (h : BrokenPairs ind cntZ) (k : ℕ) :
    Module.finrank ℤ (cyclesAt ind cntZ k ⧸ boundariesIn ind cntZ k)
      + Module.finrank ℤ (LinearMap.range (dLin ind cntZ k))
      = Module.finrank ℤ (cyclesAt ind cntZ k) := by
  have h2 : Module.finrank ℤ (boundariesIn ind cntZ k)
      = Module.finrank ℤ (LinearMap.range (dLin ind cntZ k)) :=
    (Submodule.comapSubtypeEquivOfLe (boundaries_le_cyclesAt h k)).finrank_eq
  rw [← h2]
  exact Submodule.finrank_quotient_add_finrank _

/-- Rank–nullity over `ℤ` for `∂ₖ : Cₖ₊₁ → Cₖ`. -/
theorem finrank_int_range_add (ind : Crit → ℕ) (cntZ : Crit → Crit → ℤ) (k : ℕ) :
    Module.finrank ℤ (LinearMap.range (dLin ind cntZ k))
      + Module.finrank ℤ (cyclesAt ind cntZ (k + 1)) = numCrit ind (k + 1) := by
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker (dLin ind cntZ k))
  rw [(LinearMap.quotKerEquivRange (dLin ind cntZ k)).finrank_eq,
    Module.finrank_fintype_fun_eq_card] at h1
  exact h1

/-- Every chain of degree `0` is a cycle, so `rank Z₀ = c₀`. -/
theorem finrank_int_cyclesAt_zero (ind : Crit → ℕ) (cntZ : Crit → Crit → ℤ) :
    Module.finrank ℤ (cyclesAt ind cntZ 0) = numCrit ind 0 := by
  rw [cyclesAt_zero, finrank_top]
  exact Module.finrank_fintype_fun_eq_card ℤ

/-- Rank–nullity over `ℤ` for an integer matrix. -/
theorem int_rank_add_finrank_ker {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℤ) :
    A.rank + Module.finrank ℤ (LinearMap.ker A.mulVecLin) = Fintype.card n := by
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker A.mulVecLin)
  rw [(LinearMap.quotKerEquivRange A.mulVecLin).finrank_eq,
    Module.finrank_fintype_fun_eq_card] at h1
  exact h1

/-- Over `ℤ`, `Aᵀ A x = 0` forces `A x = 0`: pair with `x` to get `‖A x‖² = 0`. -/
theorem int_ker_transpose_mul_self {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℤ) :
    LinearMap.ker (Aᵀ * A).mulVecLin = LinearMap.ker A.mulVecLin := by
  ext x
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    replace h := congr_arg (dotProduct x) h
    rwa [Matrix.dotProduct_mulVec, dotProduct_zero, Matrix.vecMul_transpose,
      dotProduct_self_eq_zero] at h
  · intro h
    rw [h, Matrix.mulVec_zero]

/-- `Aᵀ A` and `A` have the same kernel, hence the same rank. -/
theorem int_rank_transpose_mul_self {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℤ) :
    (Aᵀ * A).rank = A.rank := by
  have h1 := int_rank_add_finrank_ker (Aᵀ * A)
  have h2 := int_rank_add_finrank_ker A
  rw [int_ker_transpose_mul_self] at h1
  omega

/-- **An integer matrix and its transpose have the same rank.**  Mathlib proves
`Matrix.rank_transpose` over a field; over `ℤ` the argument through `Aᵀ A`
(whose kernel is that of `A`, `ℤ` being ordered) still applies. -/
theorem int_rank_transpose {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℤ) :
    Aᵀ.rank = A.rank := by
  apply le_antisymm
  · have h := Matrix.rank_mul_le_left Aᵀᵀ Aᵀ
    rw [int_rank_transpose_mul_self Aᵀ, Matrix.transpose_transpose] at h
    exact h
  · have h := Matrix.rank_mul_le_left Aᵀ A
    rw [int_rank_transpose_mul_self A] at h
    exact h

/-- The integral differential is multiplication by the count matrix. -/
theorem dLin_eq_mulVecLin_int (ind : Crit → ℕ) (cntZ : Crit → Crit → ℤ) (k : ℕ) :
    dLin ind cntZ k
      = (Matrix.of fun (b : CritSet ind k) (a : CritSet ind (k + 1)) => cntZ a.1 b.1).mulVecLin := by
  refine LinearMap.ext fun x => funext fun b => ?_
  show (∑ a : CritSet ind (k + 1), x a * cntZ a.1 b.1) = _
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

/-- The integral analogue of `bdim_dual`: the differential of the dual complex
is a transpose, hence has the same rank, by `int_rank_transpose`. -/
theorem finrank_range_dLin_dual_int {ind ind' : Crit → ℕ} {cntZ : Crit → Crit → ℤ} {n : ℕ}
    (hn : ∀ c, ind c + ind' c = n) {k j : ℕ} (hkj : k + j + 1 = n) :
    Module.finrank ℤ (LinearMap.range (dLin ind' (fun a b => cntZ b a) j))
      = Module.finrank ℤ (LinearMap.range (dLin ind cntZ k)) := by
  have e1 : dLin ind' (fun a b => cntZ b a) j
      = ((Matrix.of fun (b : CritSet ind k) (a : CritSet ind (k + 1)) => cntZ a.1 b.1).transpose.submatrix
          (dualCritEquiv hn (show (k + 1) + j = n by omega))
          (dualCritEquiv hn (show k + (j + 1) = n by omega))).mulVecLin := by
    rw [dLin_eq_mulVecLin_int]
    rfl
  rw [e1, dLin_eq_mulVecLin_int]
  exact (Matrix.rank_submatrix _ _ _).trans (int_rank_transpose _)


/-- **Proposition 4.3.2 (Poincaré duality for oriented manifolds).**  For a
closed oriented manifold of dimension `n`, the homology of the complex of `−f`
in degree `n − k` is dual to the homology of the complex of `f` in degree `k`.

A word of care is needed over `ℤ`, and it is the reason this statement is about
*ranks*.  The proof of §4.3 identifies `C_{n−k}(−f)` with the dual `Cₖ(f)⋆` and
`∂_{−X}` with the transpose `ᵗ∂_X`; the homology of the transposed complex is
therefore the *cohomology* of the original one, and over `ℤ` cohomology differs
from homology by a shift of the torsion (universal coefficients).  It really
does differ: for `P³(ℝ)`, whose integral Morse complex is
`ℤ →⁰ ℤ →² ℤ →⁰ ℤ`, one has `H₁ = Z/2` and `H₂ = 0`, so no isomorphism
`HM₂ ≅ HM₁` can hold, although `n − 1 = 2`.  Over a field — the setting of
Proposition 4.3.1, and of `betti_dual` above — the difficulty disappears, and
over `ℤ` what survives is the duality of the free ranks, stated here.

Proved by the bookkeeping of `betti_dual`, run over `ℤ`.  Ranks over a domain
are additive (`finrank_int_quot_add`, `finrank_int_range_add`), so the free rank
of `Zₖ / Bₖ` is `cₖ − rank ∂ₖ₋₁ − rank ∂ₖ`; the dual complex has the same `cₖ`
in dual degrees and transposed differentials, and an integer matrix has the rank
of its transpose (`int_rank_transpose`). -/
theorem finrank_homology_dual_int {cntZ : Crit → Crit → ℤ}
    (h : BrokenPairs ind cntZ) (h' : BrokenPairs ind' (fun a b => cntZ b a))
    (hn : ∀ c, ind c + ind' c = n) {k j : ℕ} (hkj : k + j = n) :
    Module.finrank ℤ
        (cyclesAt ind' (fun a b => cntZ b a) j ⧸ boundariesIn ind' (fun a b => cntZ b a) j)
      = Module.finrank ℤ (cyclesAt ind cntZ k ⧸ boundariesIn ind cntZ k) := by
  have hind : ∀ c, ind c ≤ n := fun c => by have := hn c; omega
  have hind' : ∀ c, ind' c ≤ n := fun c => by have := hn c; omega
  have hc : numCrit ind' j = numCrit ind k := numCrit_dual hn hkj
  have V : ∀ m, n < m → numCrit ind m = 0 := fun m hm => by
    have := isEmpty_critSet hind hm
    exact Fintype.card_eq_zero
  have V' : ∀ m, n < m → numCrit ind' m = 0 := fun m hm => by
    have := isEmpty_critSet hind' hm
    exact Fintype.card_eq_zero
  have Q := finrank_int_quot_add h
  have Q' := finrank_int_quot_add h'
  have R := finrank_int_range_add ind cntZ
  have R' := finrank_int_range_add ind' (fun a b => cntZ b a)
  have Z0 := finrank_int_cyclesAt_zero ind cntZ
  have Z0' := finrank_int_cyclesAt_zero ind' (fun a b => cntZ b a)
  cases k with
  | zero =>
      cases j with
      | zero =>
          have := Q 0; have := Q' 0; have := R 0; have := R' 0
          have := V (0 + 1) (by omega); have := V' (0 + 1) (by omega)
          omega
      | succ j₀ =>
          have := Q 0; have := Q' (j₀ + 1); have := R' j₀; have := R' (j₀ + 1)
          have := V' (j₀ + 1 + 1) (by omega)
          have := finrank_range_dLin_dual_int (cntZ := cntZ) (k := 0) (j := j₀) hn (by omega)
          omega
  | succ k₀ =>
      cases j with
      | zero =>
          have := Q (k₀ + 1); have := R k₀; have := R (k₀ + 1); have := Q' 0
          have := V (k₀ + 1 + 1) (by omega)
          have := finrank_range_dLin_dual_int (cntZ := cntZ) (k := k₀) (j := 0) hn (by omega)
          omega
      | succ j₀ =>
          have := Q (k₀ + 1); have := R k₀; have := R (k₀ + 1)
          have := Q' (j₀ + 1); have := R' j₀; have := R' (j₀ + 1)
          have := finrank_range_dLin_dual_int (cntZ := cntZ) (k := k₀ + 1) (j := j₀) hn
            (by omega)
          have := finrank_range_dLin_dual_int (cntZ := cntZ) (k := k₀) (j := j₀ + 1) hn
            (by omega)
          omega

end Duality

/-! ## §4.4 Euler characteristic, Poincaré polynomial, Morse inequalities

Everything here is linear algebra over a field, exactly as in the book: writing
`cₖ = dim Cₖ`, `zₖ = dim Ker ∂ₖ` and `bₖ = dim Im ∂ₖ₊₁`, rank–nullity gives
`cₖ₊₁ = bₖ + zₖ₊₁` and the definition of homology gives `βₖ = zₖ − bₖ`.  Hence
`cₖ ≥ βₖ` (the Morse inequalities) and, the `bₖ` telescoping in the alternating
sum, `Σ (−1)ᵏ cₖ = Σ (−1)ᵏ βₖ` (the Euler characteristic). -/

section Euler

variable {K : Type*} [Field K] {Crit : Type*} [Fintype Crit]
  {ind : Crit → ℕ} {cnt : Crit → Crit → K}

/-- **Proposition 4.4.3 (the Morse inequalities).**  A Morse function has at
least `βₖ` critical points of index `k`. -/
theorem betti_le_numCrit (h : BrokenPairs ind cnt) (k : ℕ) :
    betti ind cnt k ≤ numCrit ind k := by
  cases k with
  | zero => have := numCrit_zero_eq h (ind := ind) (cnt := cnt); omega
  | succ k => have := numCrit_succ_eq h (ind := ind) (cnt := cnt) k; omega

/-- The telescoping identity behind Corollary 4.4.1 and Remark 4.4.2:
`Σ_{k ≤ N} (−1)ᵏ cₖ = Σ_{k ≤ N} (−1)ᵏ βₖ + (−1)ᴺ dim B_N`. -/
theorem sum_alt_numCrit (h : BrokenPairs ind cnt) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k * (numCrit ind k : ℤ)
      = (∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k * (betti ind cnt k : ℤ))
        + (-1 : ℤ) ^ N * (bdim ind cnt N : ℤ) := by
  induction N with
  | zero =>
      have hA : numCrit ind 0 = betti ind cnt 0 + bdim ind cnt 0 := numCrit_zero_eq h
      simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul]
      exact_mod_cast hA
  | succ N ih =>
      have hB : numCrit ind (N + 1)
          = bdim ind cnt N + (betti ind cnt (N + 1) + bdim ind cnt (N + 1)) :=
        numCrit_succ_eq h N
      have hB' : (numCrit ind (N + 1) : ℤ)
          = (bdim ind cnt N : ℤ) + ((betti ind cnt (N + 1) : ℤ) + (bdim ind cnt (N + 1) : ℤ)) := by
        exact_mod_cast hB
      rw [Finset.sum_range_succ (f := fun k => (-1 : ℤ) ^ k * (numCrit ind k : ℤ)),
        Finset.sum_range_succ (f := fun k => (-1 : ℤ) ^ k * (betti ind cnt k : ℤ)), ih, hB']
      ring

/-- The same telescoping without signs: `Σ cₖ = Σ βₖ + 2 Σ_{k<N} dim Bₖ + dim B_N`. -/
theorem sum_numCrit_eq (h : BrokenPairs ind cnt) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), numCrit ind k
      = (∑ k ∈ Finset.range (N + 1), betti ind cnt k)
        + 2 * (∑ k ∈ Finset.range N, bdim ind cnt k) + bdim ind cnt N := by
  induction N with
  | zero =>
      have hA : numCrit ind 0 = betti ind cnt 0 + bdim ind cnt 0 := numCrit_zero_eq h
      simp only [zero_add, Finset.sum_range_one, Finset.range_zero, Finset.sum_empty,
        Nat.mul_zero, Nat.add_zero]
      omega
  | succ N ih =>
      have hB : numCrit ind (N + 1)
          = bdim ind cnt N + (betti ind cnt (N + 1) + bdim ind cnt (N + 1)) :=
        numCrit_succ_eq h N
      rw [Finset.sum_range_succ (f := fun k => numCrit ind k),
        Finset.sum_range_succ (f := fun k => betti ind cnt k),
        Finset.sum_range_succ (f := fun k => bdim ind cnt k), ih, hB]
      ring

/-- **The Euler characteristic** `χ(V) = Σ (−1)ᵏ βₖ` (§4.4).  `N` is any bound
for the Morse index, e.g. the dimension of the manifold. -/
noncomputable def eulerChar (ind : Crit → ℕ) (cnt : Crit → Crit → K) (N : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k * (betti ind cnt k : ℤ)

/-- **Remark 4.4.2.**  The Euler characteristic is the alternating sum of the
numbers of critical points of a Morse function; in particular that alternating
sum does not depend on the function. -/
theorem eulerChar_eq_alt_sum_numCrit (h : BrokenPairs ind cnt) {N : ℕ} (hN : ∀ c, ind c ≤ N) :
    ∑ k ∈ Finset.range (N + 1), (-1 : ℤ) ^ k * (numCrit ind k : ℤ) = eulerChar ind cnt N := by
  rw [eulerChar, sum_alt_numCrit h N,
    bdim_eq_zero_of_isEmpty (cnt := cnt) (isEmpty_critSet hN (Nat.lt_succ_self N))]
  simp

/-- **Corollary 4.4.1.**  The number of critical points of a Morse function,
taken modulo `2`, depends only on the homology — hence only on the manifold and
not on the function. -/
theorem card_crit_modEq (h : BrokenPairs ind cnt) {N : ℕ} (hN : ∀ c, ind c ≤ N) :
    Nat.ModEq 2 (Fintype.card Crit) (∑ k ∈ Finset.range (N + 1), betti ind cnt k) := by
  have hcard := card_eq_sum_numCrit (ind := ind) hN
  have hsum := sum_numCrit_eq h N
  have hb : bdim ind cnt N = 0 :=
    bdim_eq_zero_of_isEmpty (cnt := cnt) (isEmpty_critSet hN (Nat.lt_succ_self N))
  show Fintype.card Crit % 2 = _ % 2
  omega

/-- **Proposition 4.4.3, total form.**  A Morse function on `V` has at least
`Σ βₖ` critical points. -/
theorem sum_betti_le_card (h : BrokenPairs ind cnt) {N : ℕ} (hN : ∀ c, ind c ≤ N) :
    (∑ k ∈ Finset.range (N + 1), betti ind cnt k) ≤ Fintype.card Crit := by
  have hcard := card_eq_sum_numCrit (ind := ind) hN
  have hsum := sum_numCrit_eq h N
  omega

/-- An alternating sum with the exponents counted downwards. -/
theorem sum_neg_one_pow_sub (x : ℕ → ℕ) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - k) * (x k : ℤ)
      = (-1 : ℤ) ^ m * ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * (x k : ℤ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hpow : (-1 : ℤ) ^ (m - k) = (-1 : ℤ) ^ m * (-1 : ℤ) ^ k := by
    have h1 : m + k = (m - k) + 2 * k := by omega
    calc (-1 : ℤ) ^ (m - k) = (-1 : ℤ) ^ (m - k) * ((-1 : ℤ) ^ 2) ^ k := by norm_num
      _ = (-1 : ℤ) ^ ((m - k) + 2 * k) := by rw [pow_add, pow_mul]
      _ = (-1 : ℤ) ^ (m + k) := by rw [← h1]
      _ = (-1 : ℤ) ^ m * (-1 : ℤ) ^ k := by rw [pow_add]
  rw [hpow, mul_assoc]

/-- **The strong Morse inequalities.**  For every `m`,
`βₘ − βₘ₋₁ + ⋯ ≤ cₘ − cₘ₋₁ + ⋯`; the difference of the two sides is
`dim Bₘ ≥ 0`.  Taking `m` above the top index turns the inequality into the
equality of Euler characteristics. -/
theorem strong_morse_inequality (h : BrokenPairs ind cnt) (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - k) * (betti ind cnt k : ℤ)
      ≤ ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ (m - k) * (numCrit ind k : ℤ) := by
  have hsq : (-1 : ℤ) ^ m * (-1 : ℤ) ^ m = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨m, rfl⟩
  have hb : (0 : ℤ) ≤ (bdim ind cnt m : ℤ) := Nat.cast_nonneg _
  rw [sum_neg_one_pow_sub (fun k => betti ind cnt k) m,
    sum_neg_one_pow_sub (fun k => numCrit ind k) m, sum_alt_numCrit h m]
  set A : ℤ := ∑ k ∈ Finset.range (m + 1), (-1 : ℤ) ^ k * (betti ind cnt k : ℤ) with hA
  have key : (-1 : ℤ) ^ m * (A + (-1 : ℤ) ^ m * (bdim ind cnt m : ℤ))
      = (-1 : ℤ) ^ m * A + (bdim ind cnt m : ℤ) := by
    have hstep : (-1 : ℤ) ^ m * ((-1 : ℤ) ^ m * (bdim ind cnt m : ℤ))
        = ((-1 : ℤ) ^ m * (-1 : ℤ) ^ m) * (bdim ind cnt m : ℤ) := by ring
    rw [mul_add, hstep, hsq, one_mul]
  rw [key]
  linarith

/-- **The Poincaré polynomial** `P_V(t) = Σ βₖ tᵏ` (§4.4). -/
noncomputable def poincarePoly (ind : Crit → ℕ) (cnt : Crit → Crit → K) (N : ℕ) :
    Polynomial ℤ :=
  ∑ k ∈ Finset.range (N + 1), Polynomial.C (betti ind cnt k : ℤ) * Polynomial.X ^ k

/-- `P_V(−1) = χ(V)`: the relation between the Poincaré polynomial and the Euler
characteristic (§4.4). -/
theorem poincarePoly_eval_neg_one (ind : Crit → ℕ) (cnt : Crit → Crit → K) (N : ℕ) :
    (poincarePoly ind cnt N).eval (-1) = eulerChar ind cnt N := by
  simp only [poincarePoly, eulerChar, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- **Remark 4.4.7.**  The Euler characteristic of a closed manifold of odd
dimension vanishes: by Poincaré duality the terms of the alternating sum cancel
in pairs.  Stated with the duality of the Betti numbers as a hypothesis, which
is what `betti_dual` provides. -/
theorem eulerChar_eq_zero_of_odd {n : ℕ} (hodd : Odd n)
    (hdual : ∀ k ≤ n, betti ind cnt k = betti ind cnt (n - k)) :
    eulerChar ind cnt n = 0 := by
  have h1 : ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - j) * (betti ind cnt (n - j) : ℤ)
      = ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * (betti ind cnt j : ℤ) :=
    Finset.sum_range_reflect (fun j => (-1 : ℤ) ^ j * (betti ind cnt j : ℤ)) (n + 1)
  have h2 : ∀ j ∈ Finset.range (n + 1),
      (-1 : ℤ) ^ (n - j) * (betti ind cnt (n - j) : ℤ)
        = (-1 : ℤ) * ((-1 : ℤ) ^ j * (betti ind cnt j : ℤ)) := by
    intro j hj
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hb : betti ind cnt (n - j) = betti ind cnt j := by
      have hstep := hdual (n - j) (Nat.sub_le _ _)
      rw [hstep]
      congr 1
      omega
    have h5 : (-1 : ℤ) ^ j * (-1 : ℤ) ^ j = 1 := by
      rw [← pow_add]; exact Even.neg_one_pow ⟨j, rfl⟩
    have h3 : (-1 : ℤ) ^ (n - j) * (-1 : ℤ) ^ j = (-1 : ℤ) ^ n := by
      rw [← pow_add]
      congr 1
      omega
    have h4 : (-1 : ℤ) ^ n = -1 := hodd.neg_one_pow
    have hpow : (-1 : ℤ) ^ (n - j) = -((-1 : ℤ) ^ j) := by
      calc (-1 : ℤ) ^ (n - j) = (-1 : ℤ) ^ (n - j) * ((-1 : ℤ) ^ j * (-1 : ℤ) ^ j) := by
            rw [h5, mul_one]
        _ = ((-1 : ℤ) ^ (n - j) * (-1 : ℤ) ^ j) * (-1 : ℤ) ^ j := by ring
        _ = (-1 : ℤ) ^ n * (-1 : ℤ) ^ j := by rw [h3]
        _ = -((-1 : ℤ) ^ j) := by rw [h4]; ring
    rw [hb, hpow]
    ring
  have h6 : eulerChar ind cnt n = -eulerChar ind cnt n := by
    conv_lhs => rw [eulerChar, ← h1]
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, eulerChar]
    ring
  linarith

end Euler

/-! ## §4.5 Homology and connectivity

Proposition 4.5.1 (`HM₀(V; Z/2) ≅ Z/2` for `V` connected), Corollary 4.5.3, its
integral variants and Proposition 4.5.7 (a Morse function without critical
points of index `1` forces `V` simply connected) are all statements about a
connected manifold and its unstable manifolds; none of them can be phrased for
abstract count data, so none carries a Lean declaration.

What *is* algebraic is the observation opening §4.1 and used again in Corollary
4.5.5: the complex of a disjoint union is the direct sum of the complexes. -/

section DisjointUnion

variable {K : Type*} [Field K] {Crit₁ Crit₂ : Type*} [Fintype Crit₁] [Fintype Crit₂]

/-- The count function of a disjoint union: no trajectory joins the two pieces. -/
def sumCount (cnt₁ : Crit₁ → Crit₁ → K) (cnt₂ : Crit₂ → Crit₂ → K) :
    Crit₁ ⊕ Crit₂ → Crit₁ ⊕ Crit₂ → K
  | Sum.inl a, Sum.inl b => cnt₁ a b
  | Sum.inr a, Sum.inr b => cnt₂ a b
  | _, _ => 0

omit [Fintype Crit₁] [Fintype Crit₂] in
/-- The total differential of a disjoint union is block diagonal. -/
theorem totalD_sum (ind₁ : Crit₁ → ℕ) (ind₂ : Crit₂ → ℕ) (cnt₁ : Crit₁ → Crit₁ → K)
    (cnt₂ : Crit₂ → Crit₂ → K) :
    totalD (Sum.elim ind₁ ind₂) (sumCount cnt₁ cnt₂)
      = Matrix.fromBlocks (totalD ind₁ cnt₁) 0 0 (totalD ind₂ cnt₂) := by
  ext (b | b) (a | a)
  · rfl
  · show (if Sum.elim ind₁ ind₂ (Sum.inr a) = Sum.elim ind₁ ind₂ (Sum.inl b) + 1 then (0 : K)
      else 0) = 0
    exact ite_self _
  · show (if Sum.elim ind₁ ind₂ (Sum.inl a) = Sum.elim ind₁ ind₂ (Sum.inr b) + 1 then (0 : K)
      else 0) = 0
    exact ite_self _
  · rfl

/-- The critical points of a disjoint union of index `k` are those of either piece. -/
theorem numCrit_sum {α β : Type*} [Fintype α] [Fintype β] (f : α → ℕ) (g : β → ℕ) (k : ℕ) :
    numCrit (Sum.elim f g) k = numCrit f k + numCrit g k := by
  rw [numCrit_eq_sum, numCrit_eq_sum, numCrit_eq_sum, Fintype.sum_sum_type]
  rfl


/-- **§4.1 and Corollary 4.5.5.**  `C⋆(f ⊔ g) = C⋆(f) ⊕ C⋆(g)` and
`∂_{X ⊔ Y} = ∂_X ⊕ ∂_Y`, so the Betti numbers of a disjoint union add up.  (With
Proposition 4.5.1 this gives Corollary 4.5.5: `HM₀` and `HMₙ` have dimension the
number of connected components.)

Proved: the total differential of the union is block diagonal (`totalD_sum`),
so the block sum of retractions of the two pieces (`exists_retract`) is a
retraction of the union, and `betti_eq_numCrit_of_retract` together with
`numCrit_sum` gives the formula. -/
theorem betti_sumComplex {ind₁ : Crit₁ → ℕ} {ind₂ : Crit₂ → ℕ}
    {cnt₁ : Crit₁ → Crit₁ → K} {cnt₂ : Crit₂ → Crit₂ → K}
    (h₁ : BrokenPairs ind₁ cnt₁) (h₂ : BrokenPairs ind₂ cnt₂)
    (hS : BrokenPairs (Sum.elim ind₁ ind₂) (sumCount cnt₁ cnt₂)) (k : ℕ) :
    betti (Sum.elim ind₁ ind₂) (sumCount cnt₁ cnt₂) k = betti ind₁ cnt₁ k + betti ind₂ cnt₂ k := by
  have := Classical.decEq Crit₁
  have := Classical.decEq Crit₂
  obtain ⟨CH₁, _, _, indH₁, I₁, P₁, Hm₁, hI₁, hDI₁, hPD₁, hPI₁, hH₁⟩ := exists_retract h₁
  obtain ⟨CH₂, _, _, indH₂, I₂, P₂, Hm₂, hI₂, hDI₂, hPD₂, hPI₂, hH₂⟩ := exists_retract h₂
  rw [betti_eq_numCrit_of_retract h₁ indH₁ I₁ P₁ Hm₁ hI₁ hDI₁ hPD₁ hPI₁ hH₁ k,
    betti_eq_numCrit_of_retract h₂ indH₂ I₂ P₂ Hm₂ hI₂ hDI₂ hPD₂ hPI₂ hH₂ k, ← numCrit_sum]
  refine betti_eq_numCrit_of_retract hS (Sum.elim indH₁ indH₂) (Matrix.fromBlocks I₁ 0 0 I₂)
    (Matrix.fromBlocks P₁ 0 0 P₂) (Matrix.fromBlocks Hm₁ 0 0 Hm₂) ?_ ?_ ?_ ?_ ?_ k
  · rintro (c | c) (e | e) hne
    · exact hI₁ c e hne
    · exact absurd rfl hne
    · exact absurd rfl hne
    · exact hI₂ c e hne
  · rw [totalD_sum, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, hDI₁, hDI₂, Matrix.fromBlocks_zero]
  · rw [totalD_sum, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, hPD₁, hPD₂, Matrix.fromBlocks_zero]
  · rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, hPI₁, hPI₂,
      Matrix.fromBlocks_one]
  · rw [totalD_sum, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [Matrix.fromBlocks_add, ← Matrix.fromBlocks_one, Matrix.fromBlocks_add, hH₁, hH₂]
    simp only [add_zero]

end DisjointUnion

/-! ## §4.6 Functoriality, §4.7 the long exact sequence

Theorem 4.6.1 (a `C^∞` map `u : V → W` induces `u⋆ : HM⋆(V) → HM⋆(W)`,
functorially), Theorem 4.6.2 (homotopic maps induce the same morphism),
Proposition 4.6.3 (a Morse–Smale pair on a submanifold extends to the ambient
manifold with the same critical points and the same differential), Lemma 4.6.6
and the whole of §4.7 speak about smooth maps between manifolds and the Morse
homology *of a manifold*.  In this development the homology is attached to
abstract count data, so there is no manifold to map and no declaration is made.

Two remarks on what would be reusable.  The proof of Theorem 4.6.1 reduces the
general case to embeddings by factoring `u` through `V → Dᴺ × W`, and its only
homological ingredient is that `(i₀)⋆` is an isomorphism, which is Künneth
together with `HM⋆(Dᴺ) = Z` in degree `0`.  The long exact sequence of §4.7 is
obtained from the short exact sequence of complexes
`C⋆(f) → C⋆(f̃) → C⋆(f̃|_{W − 𝒱})`, and the passage from a short exact sequence of
complexes to a long exact sequence in homology is already in Mathlib
(`CategoryTheory.ShortComplex.ShortExact` and `HomologySequence`), applicable to
`MorseFloer.Chapter3.morseComplex`. -/

/-! ## §4.8 Applications -/

section Applications

/-! ### §4.8.b Brouwer's fixed point theorem

The book re-proves Brouwer's theorem from `HM_{n−1}(Dⁿ) = 0`: a fixed point free
self-map of the disc produces a retraction `r : Dⁿ → Sⁿ⁻¹` with `r ∘ j = id`,
which is impossible since the identity of `HM_{n−1}(Sⁿ⁻¹) = Z/2` would factor
through `0`.

**Why the proof here is not the book's.**  The homological route is closed in
this Mathlib: `Mathlib.AlgebraicTopology.SingularHomology` builds singular
homology with homotopy invariance and `H₀`, but has **no excision and no
Mayer–Vietoris**, so `H_{n−1}(Sⁿ⁻¹)` is computed nowhere.  (Nor are `π₁(S¹) ≅ ℤ`,
the combinatorial Sperner lemma — `Combinatorics/SetFamily/LYM.lean` is
Sperner's unrelated theorem on antichains — or degree theory available.)

The theorem is instead proved analytically, after Milnor and Rogers, in
`MorseFloer/Part1/Brouwer.lean`.  A `C¹` retraction `r` of the ball onto the
sphere would give `∫_D det Dr = vol D`, by following the homotopy
`id + t (r − id)` with the change of variables formula (the integral is a
polynomial in `t`), and also `∫_D det Dr = 0`, since `‖r‖ = 1` forces `Dr` to
be singular.  Smooth partitions of unity reduce continuous maps to `C¹` ones.
`brouwer_fixedPoint` restates the result, `no_retraction_closedBall` is deduced
from it, and the elementary cases `brouwer_fixedPoint_dim_zero` and
`brouwer_fixedPoint_dim_one` (the intermediate value theorem on `[−1, 1]`) are
kept alongside. -/

/-- The norm on the line `EuclideanSpace ℝ (Fin 1)` is the absolute value of the
single coordinate.  This is what identifies the one-dimensional closed unit ball
with the interval `[−1, 1]`, and it is the only computation the base case
`brouwer_fixedPoint_dim_one` needs beyond the intermediate value theorem. -/
theorem norm_eq_abs_coord (x : EuclideanSpace ℝ (Fin 1)) : ‖x‖ = |x 0| := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs,
    Real.sqrt_sq_eq_abs]

/-- **Brouwer's fixed point theorem, base case `n = 0`.**  Proved in full.
`EuclideanSpace ℝ (Fin 0)` has exactly one point, so the closed unit ball is
`{0}` and every self-map fixes the origin. -/
theorem brouwer_fixedPoint_dim_zero
    (f : EuclideanSpace ℝ (Fin 0) → EuclideanSpace ℝ (Fin 0))
    (_hf : ContinuousOn f (Metric.closedBall 0 1))
    (_hmaps : Set.MapsTo f (Metric.closedBall 0 1) (Metric.closedBall 0 1)) :
    ∃ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 0)) 1, f x = x := by
  refine ⟨0, Metric.mem_closedBall_self zero_le_one, ?_⟩
  ext i
  exact i.elim0

/-- **Brouwer's fixed point theorem, base case `n = 1`.**  Proved in full.

The closed unit ball of `EuclideanSpace ℝ (Fin 1)` is the image of `[−1, 1]`
under the isometric parametrisation `t ↦ (t)`, by `norm_eq_abs_coord`.  Transport
`f` to `g t = f(t) − t` on `[−1, 1]`: it is continuous, `g(1) ≤ 0` and
`g(−1) ≥ 0` because `f` maps the ball into itself, so `intermediate_value_Icc'`
produces a zero of `g`, which is a fixed point of `f`.

Kept as the elementary case; `brouwer_fixedPoint` below covers every
dimension. -/
theorem brouwer_fixedPoint_dim_one
    (f : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1))
    (hf : ContinuousOn f (Metric.closedBall 0 1))
    (hmaps : Set.MapsTo f (Metric.closedBall 0 1) (Metric.closedBall 0 1)) :
    ∃ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1, f x = x := by
  obtain ⟨j, hj0, hjc, hjn⟩ :
      ∃ j : ℝ → EuclideanSpace ℝ (Fin 1),
        (∀ t, j t 0 = t) ∧ Continuous j ∧ ∀ t, ‖j t‖ = |t| := by
    refine ⟨fun t => WithLp.toLp 2 fun _ => t, fun _ => rfl, ?_, ?_⟩
    · exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => continuous_id)
    · intro t
      rw [norm_eq_abs_coord]
  have hjmem : ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 →
      j t ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
    intro t ht
    rw [mem_closedBall_zero_iff, hjn]
    exact abs_le.mpr ⟨ht.1, ht.2⟩
  have hgc : ContinuousOn (fun t : ℝ => f (j t) 0 - t) (Set.Icc (-1 : ℝ) 1) :=
    ((PiLp.continuous_apply 2 _ 0).comp_continuousOn
      (hf.comp hjc.continuousOn hjmem)).sub continuousOn_id
  have hbound : ∀ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 → |f (j t) 0| ≤ 1 := by
    intro t ht
    have h := hmaps (hjmem t ht)
    rw [mem_closedBall_zero_iff, norm_eq_abs_coord] at h
    exact h
  have h1 : f (j 1) 0 - 1 ≤ 0 := by
    have h := (abs_le.mp (hbound 1 ⟨by norm_num, le_refl 1⟩)).2
    linarith
  have h2 : (0 : ℝ) ≤ f (j (-1)) 0 - (-1) := by
    have h := (abs_le.mp (hbound (-1) ⟨le_refl (-1 : ℝ), by norm_num⟩)).1
    linarith
  obtain ⟨t, ht, hgt⟩ :=
    intermediate_value_Icc' (by norm_num : (-1 : ℝ) ≤ 1) hgc ⟨h1, h2⟩
  refine ⟨j t, hjmem t ht, ?_⟩
  have hcoord : f (j t) 0 = t := by
    have h : f (j t) 0 - t = 0 := hgt
    linarith
  ext i
  have hi : i = 0 := Fin.fin_one_eq_zero i
  subst hi
  rw [hj0]
  exact hcoord

/-- **Theorem 2.3.3, reproved in §4.8.b (Brouwer).**  A continuous self-map of
the closed unit ball has a fixed point.

Proved in every dimension: this restates `MorseFloer.brouwer_fixed_point` from
`MorseFloer/Part1/Brouwer.lean`, whose analytic proof (Milnor–Rogers: the change
of variables formula along the homotopy `id + t (r − id)`, and smoothing by
partitions of unity) is described in that file and in the note above.  It is
also `Chapter2.brouwer`; Chapter 4 imports the Brouwer file directly because
`Part1/Ch3.lean`, and hence this file, does not import Chapter 2. -/
theorem brouwer_fixedPoint {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hf : ContinuousOn f (Metric.closedBall 0 1))
    (hmaps : Set.MapsTo f (Metric.closedBall 0 1) (Metric.closedBall 0 1)) :
    ∃ x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, f x = x :=
  brouwer_fixed_point f hf hmaps

/-- **§4.8.b.**  There is no retraction of the closed ball onto its boundary
sphere: a map of the ball into the sphere must move some point of the sphere.

Deduced from `brouwer_fixedPoint` (the book argues the other way, homologically: `r ∘ j = id` on `Sⁿ⁻¹` would factor
the identity of `HM_{n−1}(Sⁿ⁻¹) = Z/2` through `HM_{n−1}(Dⁿ) = 0`).  Suppose `r`
fixed the sphere pointwise.  Then `x ↦ −r x` maps the ball into the sphere,
hence into the ball, and has a fixed point `x = −r x`; this `x` has norm `1`, so
`r x = x`, whence `x = −x` and `x = 0`, which does not lie on the sphere. -/
theorem no_retraction_closedBall {n : ℕ}
    (r : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hr : ContinuousOn r (Metric.closedBall 0 1))
    (hmaps : Set.MapsTo r (Metric.closedBall 0 1) (Metric.sphere 0 1)) :
    ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, r x ≠ x := by
  by_contra hcon
  push Not at hcon
  have hmaps' : Set.MapsTo (fun x => -r x) (Metric.closedBall 0 1) (Metric.closedBall 0 1) := by
    intro x hx
    have h1 := hmaps hx
    rw [mem_sphere_zero_iff_norm] at h1
    show -r x ∈ Metric.closedBall 0 1
    rw [mem_closedBall_zero_iff, norm_neg, h1]
  obtain ⟨x, _, hx⟩ := brouwer_fixedPoint (fun x => -r x) hr.neg hmaps'
  have hxs : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
    have hxb : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
      rw [← hx]; exact hmaps' ‹_›
    have h1 := hmaps hxb
    rw [mem_sphere_zero_iff_norm] at h1 ⊢
    rw [← hx, norm_neg, h1]
  have hrx : r x = x := hcon x hxs
  have hx0 : x = 0 := by
    have h2 : x = -x := by
      calc x = -r x := hx.symm
        _ = -x := by rw [hrx]
    have h3 : (2 : ℝ) • x = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h2]
      exact add_neg_cancel x
    exact (smul_eq_zero.mp h3).resolve_left two_ne_zero
  rw [mem_sphere_zero_iff_norm, hx0, norm_zero] at hxs
  exact zero_ne_one hxs

/-! ### §4.8.c The mod 2 homology of the real projective space

The double cover `Sⁿ → Pⁿ(ℝ)` gives a short exact sequence of complexes
`0 → C⋆(f) → C⋆(f ∘ p) → C⋆(f) → 0` whose long exact sequence, `HM⋆(Sⁿ)` being
trivial in the intermediate degrees, forces the connecting map
`HMₖ(Pⁿ(ℝ)) → HMₖ₋₁(Pⁿ(ℝ))` to be an isomorphism for `0 ≤ k ≤ n`; hence
Theorem 4.8.2.

Here we record the complex itself: `Pⁿ(ℝ)` carries a Morse function with
exactly one critical point in each index `0, …, n`, and, there being a single
generator in each degree while the homology is `Z/2` in each degree, its mod `2`
differential vanishes.  With that complex the theorem becomes a computation. -/

/-- The Morse index function of the standard Morse function on `Pⁿ(ℝ)`: one
critical point of each index `0, …, n`. -/
def projIndex (n : ℕ) : Fin (n + 1) → ℕ := fun i => (i : ℕ)

/-- The mod `2` count function of that Morse function: it vanishes (§4.8.c). -/
def projCount (n : ℕ) : Fin (n + 1) → Fin (n + 1) → ZMod 2 := fun _ _ => 0

theorem projCount_brokenPairs (n : ℕ) : BrokenPairs (projIndex n) (projCount n) :=
  brokenPairs_zero (projIndex n)

theorem numCrit_projIndex (n k : ℕ) (hk : k ≤ n) : numCrit (projIndex n) k = 1 := by
  have : Unique (CritSet (projIndex n) k) := by
    refine ⟨⟨⟨⟨k, by omega⟩, rfl⟩⟩, ?_⟩
    rintro ⟨⟨a, ha⟩, rfl⟩
    rfl
  exact Fintype.card_unique

/-- **Theorem 4.8.2.**  `HMₖ(Pⁿ(ℝ); Z/2) ≅ Z/2` for `0 ≤ k ≤ n`. -/
theorem betti_proj (n k : ℕ) (hk : k ≤ n) : betti (projIndex n) (projCount n) k = 1 := by
  have hz : projCount n = fun _ _ => (0 : ZMod 2) := rfl
  rw [hz, betti_of_count_zero (projIndex n) k, numCrit_projIndex n k hk]

/-! ### §4.4 examples: the torus

The function `cos 2πx + cos 2πy` on `T²` has one minimum, two saddles and one
maximum and, all its counts being even, a vanishing mod `2` differential
(§3.1.c).  Its Poincaré polynomial is `1 + 2t + t²`, its Euler characteristic is
`0`, and Example 4.4.4 follows: a Morse function on `T²` has at least four
critical points. -/

theorem betti_torus_zero : betti Chapter3.torusIndex Chapter3.torusCount 0 = 1 := by
  have hz : Chapter3.torusCount = fun _ _ => (0 : ZMod 2) := rfl
  rw [hz, betti_of_count_zero Chapter3.torusIndex 0]
  decide

theorem betti_torus_one : betti Chapter3.torusIndex Chapter3.torusCount 1 = 2 := by
  have hz : Chapter3.torusCount = fun _ _ => (0 : ZMod 2) := rfl
  rw [hz, betti_of_count_zero Chapter3.torusIndex 1]
  decide

theorem betti_torus_two : betti Chapter3.torusIndex Chapter3.torusCount 2 = 1 := by
  have hz : Chapter3.torusCount = fun _ _ => (0 : ZMod 2) := rfl
  rw [hz, betti_of_count_zero Chapter3.torusIndex 2]
  decide

/-- **Example 4.4.4.**  The Betti numbers of `T²` sum to `4`, so by Proposition
4.4.3 a Morse function on the torus has at least four critical points. -/
theorem sum_betti_torus :
    (∑ k ∈ Finset.range 3, betti Chapter3.torusIndex Chapter3.torusCount k) = 4 := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    betti_torus_zero, betti_torus_one, betti_torus_two]

/-- The Euler characteristic of the torus is `0`. -/
theorem eulerChar_torus : eulerChar Chapter3.torusIndex Chapter3.torusCount 2 = 0 := by
  rw [eulerChar, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    betti_torus_zero, betti_torus_one, betti_torus_two]
  norm_num

/-! ### §4.8.d The Borsuk–Ulam theorem

Theorem 4.8.3 itself needs the mod `2` homology of the projective spaces and the
commutation of the connecting map with `ψ⋆`, so it is stated without proof (and
is not in this Mathlib version).  Its corollaries 4.8.4, 4.8.5 and 4.8.6 are
deduced from it here. -/

/-- **Theorem 4.8.3 (Borsuk–Ulam).**  There is no continuous odd map
`Sⁿ → Sⁿ⁻¹`.  Not in this Mathlib version. -/
theorem borsuk_ulam (n : ℕ) :
    ¬ ∃ φ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n),
        ContinuousOn φ (Metric.sphere 0 1) ∧
        Set.MapsTo φ (Metric.sphere 0 1) (Metric.sphere 0 1) ∧
        ∀ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, φ (-x) = -φ x := by
  sorry

/-- **Corollary 4.8.4.**  A continuous odd map `Sⁿ → ℝⁿ` vanishes somewhere: if
it did not, dividing by its norm would produce a map forbidden by Theorem
4.8.3. -/
theorem borsuk_ulam_of_odd (n : ℕ)
    (ψ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (hcont : ContinuousOn ψ (Metric.sphere 0 1))
    (hodd : ∀ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, ψ (-x) = -ψ x) :
    ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, ψ x = 0 := by
  by_contra hcon
  push Not at hcon
  have hne : ∀ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, ‖ψ x‖ ≠ 0 := by
    intro x hx
    exact norm_ne_zero_iff.mpr (hcon x hx)
  have hneg : ∀ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      -x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
    intro x hx
    rw [mem_sphere_zero_iff_norm, norm_neg]
    exact mem_sphere_zero_iff_norm.mp hx
  refine borsuk_ulam n ⟨fun x => ‖ψ x‖⁻¹ • ψ x, ?_, ?_, ?_⟩
  · exact (hcont.norm.inv₀ hne).smul hcont
  · intro x hx
    show ‖ψ x‖⁻¹ • ψ x ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hne x hx)
  · intro x hx
    have hxn := hodd x hx
    show ‖ψ (-x)‖⁻¹ • ψ (-x) = -(‖ψ x‖⁻¹ • ψ x)
    rw [hxn, norm_neg, smul_neg]

/-- **Corollary 4.8.5 (the temperature–pressure theorem).**  Every continuous
map `Sⁿ → ℝⁿ` takes the same value at some pair of antipodal points; apply
Corollary 4.8.4 to `x ↦ ψ x − ψ(−x)`. -/
theorem exists_eq_antipode (n : ℕ)
    (ψ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (hcont : ContinuousOn ψ (Metric.sphere 0 1)) :
    ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, ψ x = ψ (-x) := by
  have hneg : Set.MapsTo (fun x : EuclideanSpace ℝ (Fin (n + 1)) => -x)
      (Metric.sphere 0 1) (Metric.sphere 0 1) := by
    intro x hx
    show -x ∈ Metric.sphere 0 1
    rw [mem_sphere_zero_iff_norm, norm_neg]
    exact mem_sphere_zero_iff_norm.mp hx
  have hcont' : ContinuousOn (fun x => ψ x - ψ (-x)) (Metric.sphere 0 1) :=
    hcont.sub (hcont.comp (continuous_neg.continuousOn) hneg)
  have hodd : ∀ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      (fun x => ψ x - ψ (-x)) (-x) = -((fun x => ψ x - ψ (-x)) x) := by
    intro x _
    simp only [neg_neg]
    abel
  obtain ⟨x, hx, hx0⟩ := borsuk_ulam_of_odd n (fun x => ψ x - ψ (-x)) hcont' hodd
  exact ⟨x, hx, sub_eq_zero.mp hx0⟩

/-- **Corollary 4.8.6.**  If `n + 1` closed sets cover `Sⁿ`, one of them
contains a pair of antipodal points.

Proved from Corollary 4.8.5.  Empty members of the family are first replaced by
a nonempty one (there is one, since the sphere is nonempty), which changes
neither closedness nor the cover, and matters because the distance to the empty
set is `0`.  The map `x ↦ (d(x, F₀), …, d(x, Fₙ₋₁))` then takes equal values at
some antipodal pair `x, −x`.  For a closed nonempty set, `d(x, F) = 0` means
`x ∈ F`, so for `i < n` the point `x` lies in `Fᵢ` exactly when `−x` does.
Either `x` lies in some such `Fᵢ`, and so does `−x`; or neither `x` nor `−x`
lies in any of them, and both lie in the last set `Fₙ`. -/
theorem exists_antipodal_pair_of_closed_cover (n : ℕ)
    (F : Fin (n + 1) → Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hclosed : ∀ i, IsClosed (F i))
    (hcover : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ⊆ ⋃ i, F i) :
    ∃ (i : Fin (n + 1)) (x : EuclideanSpace ℝ (Fin (n + 1))),
      x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ∧ x ∈ F i ∧ -x ∈ F i := by
  -- a point of the sphere, hence a nonempty member of the family
  have hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.mp (hcover hx₀)
  classical
  let G : Fin (n + 1) → Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    fun i => if (F i).Nonempty then F i else F i₀
  have hGne : ∀ i, (G i).Nonempty := by
    intro i
    by_cases h : (F i).Nonempty
    · show (if (F i).Nonempty then F i else F i₀).Nonempty
      rw [if_pos h]; exact h
    · show (if (F i).Nonempty then F i else F i₀).Nonempty
      rw [if_neg h]; exact ⟨x₀, hi₀⟩
  have hGcl : ∀ i, IsClosed (G i) := by
    intro i
    show IsClosed (if (F i).Nonempty then F i else F i₀)
    split_ifs
    · exact hclosed i
    · exact hclosed i₀
  have hGF : ∀ i, ∃ j, G i = F j := by
    intro i
    by_cases h : (F i).Nonempty
    · exact ⟨i, if_pos h⟩
    · exact ⟨i₀, if_neg h⟩
  have hGcover : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ⊆ ⋃ i, G i := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hx)
    refine Set.mem_iUnion.mpr ⟨i, ?_⟩
    show x ∈ (if (F i).Nonempty then F i else F i₀)
    rw [if_pos ⟨x, hi⟩]
    exact hi
  -- the distances to the first `n` sets
  let ψ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n) :=
    fun x => WithLp.toLp 2 fun j => Metric.infDist x (G (Fin.castSucc j))
  have hψ : Continuous ψ :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => Metric.continuous_infDist_pt _)
  obtain ⟨x, hx, hxx⟩ := exists_eq_antipode n ψ hψ.continuousOn
  have hsame : ∀ j : Fin n, x ∈ G (Fin.castSucc j) ↔ -x ∈ G (Fin.castSucc j) := by
    intro j
    have hj : Metric.infDist x (G (Fin.castSucc j)) = Metric.infDist (-x) (G (Fin.castSucc j)) :=
      congrArg (fun v : EuclideanSpace ℝ (Fin n) => v j) hxx
    rw [(hGcl _).mem_iff_infDist_zero (hGne _), (hGcl _).mem_iff_infDist_zero (hGne _), hj]
  have hxneg : -x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_neg]
    exact mem_sphere_zero_iff_norm.mp hx
  -- a pair inside some `G i`
  obtain ⟨i, hxi, hxi'⟩ : ∃ i, x ∈ G i ∧ -x ∈ G i := by
    by_cases hj : ∃ j : Fin n, x ∈ G (Fin.castSucc j)
    · obtain ⟨j, hj⟩ := hj
      exact ⟨Fin.castSucc j, hj, (hsame j).mp hj⟩
    · push Not at hj
      have hlast : ∀ y ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
          (∀ j : Fin n, y ∉ G (Fin.castSucc j)) → y ∈ G (Fin.last n) := by
        intro y hy hyj
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hGcover hy)
        cases i using Fin.lastCases with
        | last => exact hi
        | cast j => exact absurd hi (hyj j)
      refine ⟨Fin.last n, hlast x hx hj, hlast (-x) hxneg fun j hj' => hj j ((hsame j).mpr hj')⟩
  obtain ⟨j, hj⟩ := hGF i
  rw [hj] at hxi hxi'
  exact ⟨j, x, hx, hxi, hxi'⟩

end Applications

end Chapter4
end MorseFloer
