import Mathlib

/-!
# Theorem 2: the covering rank of the unique-disjointness matrix

Self-contained formalisation of **Theorem 2** of the paper,
`rk∨ Uₙ ≤ n^{O(1)} (3/2)^n` (`theorem2`).

The *unique-disjointness matrix* `Uₙ` is the partially defined `2ⁿ × 2ⁿ` boolean matrix — rows
and columns indexed by the boolean vectors `BVec (Fin n)`, i.e. by the subsets of `[n]` — with
`Uₙ[a,b] = 1` iff the supports of `a` and `b` are disjoint, `0` iff they meet in exactly one
coordinate, and `*` otherwise.  A *rectangle* is a submatrix with no `0`-entry and the *covering
rank* `rk∨ Uₙ` (`coverRank`) is the least number of rectangles covering all `1`-entries
(`HasCoverFin`; intersections of rectangles are allowed).

**Theorem 2.** There are constants `c, d` with `(rk∨ Uₙ : ℝ) ≤ c (n+1)^d (3/2)^n` for all `n`
(`theorem2`, with the explicit values `c = 6`, `d = 7`).

The proof fixes the row weight `p` and column weight `q` (with `p + q ≤ n`, else the block has no
`1`-entry), bounds the covering number of each `(p,q)`-block by the paper's four-case
construction (`blockCover_caseI`–`blockCover_caseIV`, assembled in `blockCover_poly`), and sums
the `(n+1)²` block bounds with `hasCoverFin_of_blocks`.

This file is self-contained (`import Mathlib` only).  The supporting vocabulary it needs — the
code-theoretic Lemma 1 and Lemma 2 (the cube `Bⁿ` partitions into `2n` 3-codes, built from the
Hamming-code balls), the binomial-entropy bound of inequality `(2)`, and the greedy covering
bounds in indexed form — is developed here rather than imported.
-/

open Finset
open scoped BigOperators
namespace Udisj

noncomputable def H (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, (1:ℝ)/(k+1)

@[simp] lemma H_zero : H 0 = 0 := by simp [H]
lemma H_succ (n : ℕ) : H (n+1) = H n + 1/(n+1) := by unfold H; rw [Finset.sum_range_succ]
lemma H_one : H 1 = 1 := by show H (0+1) = 1; rw [H_succ, H_zero]; norm_num

lemma H_eq_harmonic (n : ℕ) : H n = (harmonic n : ℝ) := by
  unfold H harmonic
  rw [Rat.cast_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  push_cast; rw [one_div]

lemma H_le_one_add_log (n : ℕ) : H n ≤ 1 + Real.log n := by
  rw [H_eq_harmonic]; exact harmonic_le_one_add_log n

lemma H_mono : Monotone H := monotone_nat_of_le_succ (fun n => by
  rw [H_succ]; exact le_add_of_nonneg_right (by positivity))

lemma H_sub_ge {m n : ℕ} (hmn : m ≤ n) : ((n - m : ℕ) : ℝ)/n ≤ H n - H m := by
  have hsplit : H n - H m = ∑ k ∈ Finset.Ico m n, (1:ℝ)/(k+1) := by
    have h1 : H n = H m + ∑ k ∈ Finset.Ico m n, (1:ℝ)/(k+1) := by
      unfold H
      rw [Finset.range_eq_Ico m, Finset.range_eq_Ico n,
          ← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le m) hmn,
          Finset.sum_union (Finset.disjoint_left.mpr fun x hx1 hx2 => by
            rw [Finset.mem_Ico] at hx1 hx2; omega)]
    rw [h1]; ring
  rw [hsplit]
  calc ((n - m : ℕ) : ℝ)/n
      = ∑ _k ∈ Finset.Ico m n, (1:ℝ)/n := by
        rw [Finset.sum_const, nsmul_eq_mul]
        rw [show #(Finset.Ico m n) = n - m by simp]; ring
    _ ≤ ∑ k ∈ Finset.Ico m n, (1:ℝ)/(k+1) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [Finset.mem_Ico] at hk
        have h2 : (k:ℝ)+1 ≤ n := by exact_mod_cast (by omega : k + 1 ≤ n)
        have h3 : (0:ℝ) < (k:ℝ)+1 := by positivity
        have := one_div_le_one_div_of_le h3 h2
        calc (1:ℝ)/n = 1/n := by ring
          _ ≤ 1/((k:ℝ)+1) := this
          _ = (1:ℝ)/(k+1) := by ring

end Udisj

namespace Udisj.Covering

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

/-! Boolean (GF(2)-) vectors indexed by `κ`. -/
abbrev BVec (κ : Type*) := κ → ZMod 2

/-- Weight of a codeword `(a, b)`: the Hamming weight of the concatenated vector
`E`-segment `a` and `G`-segment `b`. -/
def cwWeight (x : BVec ι × BVec κ) : ℕ := hammingNorm x.1 + hammingNorm x.2

/-- The systematic encoding `a ↦ (a, a·G)` whose range is the Hamming code `Hₙ`;
its generator matrix is `[E | G]` (the `E`-segment is the identity). -/
def enc (g : ι → BVec κ) : BVec ι →ₗ[ZMod 2] (BVec ι × BVec κ) where
  toFun a := (a, ∑ i, a i • g i)
  map_add' a b := by
    ext <;> simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    ext <;> simp [mul_smul, Finset.smul_sum]

-- Rows of the generator matrix `[E | G]`: the `i`-th row is `(eᵢ, gᵢ)`, the concatenation
-- of the `i`-th standard basis vector and the `i`-th `G`-row.

omit [DecidableEq ι] in
lemma weight_enc (g : ι → BVec κ) (a : BVec ι) :
    cwWeight (enc g a) = hammingNorm a + hammingNorm (∑ i, a i • g i) := rfl

/-- In `GF(2)` every element is `0` or `1`. -/
lemma zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

lemma zmod_two_eq_one {x : ZMod 2} (h : x ≠ 0) : x = 1 :=
  (zmod_two_eq_zero_or_one x).resolve_left h

/-- Core of Lemma 1 (a property of Hamming code): if the `G`-rows `g` are pairwise distinct
and each has weight `≥ 2`, then every non-zero codeword of the systematic code
`range (enc g)` has weight `≥ 3`.

The three cases are recovered here, where `s = support a` and `k = |s|` is the
number of summed rows: `k ≥ 3` (E-segment already contributes `k ≥ 3`), `k = 1`
(one E-entry plus `‖g i‖ ≥ 2`), `k = 2` (`i ≠ j` gives `g i + g j ≠ 0`, hence a G-entry). -/
theorem codeword_weight_ge_three
    (g : ι → BVec κ) (hinj : Function.Injective g)
    (hwt : ∀ i, 2 ≤ hammingNorm (g i))
    (x : BVec ι × BVec κ) (hx : x ∈ LinearMap.range (enc g)) (hx0 : x ≠ 0) :
    3 ≤ cwWeight x := by
  obtain ⟨a, rfl⟩ := hx
  have ha : a ≠ 0 := by
    intro h
    exact hx0 (by simp [enc, h])
  set s : Finset ι := Finset.univ.filter (fun i => a i ≠ 0) with hs
  have hcard : hammingNorm a = s.card := by rw [hs]; rfl
  have hsum : (∑ i, a i • g i) = ∑ i ∈ s, g i := by
    have hterm : ∀ i, a i • g i = if i ∈ s then g i else (0 : BVec κ) := by
      intro i
      by_cases hi : i ∈ s
      · have hai : a i ≠ 0 := by rw [hs] at hi; simpa using hi
        simp [hi, zmod_two_eq_one hai]
      · have hai : a i = 0 := by
          by_contra hc
          exact hi (by rw [hs]; simp [hc])
        simp [hi, hai]
    calc ∑ i, a i • g i
        = ∑ i, (if i ∈ s then g i else 0) := Finset.sum_congr rfl (fun i _ => hterm i)
      _ = ∑ i ∈ s, g i := by
          rw [← Finset.sum_filter]
          simp
  rw [weight_enc, hsum]
  have hpos : 1 ≤ s.card := by
    have : hammingNorm a ≠ 0 := hammingNorm_ne_zero_iff.mpr ha
    omega
  rcases lt_or_ge s.card 3 with hlt | hge
  · have hcases : s.card = 1 ∨ s.card = 2 := by omega
    rcases hcases with h1 | h2
    · -- Case 1: a single summed row.
      obtain ⟨i, hsi⟩ := Finset.card_eq_one.mp h1
      rw [hsi] at hcard h1 ⊢
      have hi : hammingNorm a = 1 := by rw [hcard, h1]
      simp only [Finset.sum_singleton]
      rw [hi]
      have := hwt i
      omega
    · -- Case 2: the sum of two distinct rows.
      obtain ⟨i, j, hij, hsi⟩ := Finset.card_eq_two.mp h2
      rw [hsi] at hcard h2 ⊢
      have hij2 : hammingNorm a = 2 := by rw [hcard, h2]
      rw [hij2, Finset.sum_pair hij]
      have hne : g i + g j ≠ 0 := by
        intro h
        apply hij
        apply hinj
        funext t
        have hgt : (g i) t + (g j) t = 0 := by simpa using congrFun h t
        have h1 : (g i) t = - (g j) t := by rw [eq_neg_iff_add_eq_zero]; exact hgt
        rwa [CharTwo.neg_eq] at h1
      have : 1 ≤ hammingNorm (g i + g j) :=
        Nat.one_le_iff_ne_zero.mpr (hammingNorm_ne_zero_iff.mpr hne)
      omega
  · -- Case 3: at least three distinct rows.
    omega

/-- The `G`-rows of length `n`: all boolean length-`n` vectors of weight `≥ 2`
(the paper's row set of `Gₙ`). -/
abbrev Grows (n : ℕ) := {v : BVec (Fin n) // 2 ≤ hammingNorm v}

/-- **Lemma 1** (Hamming code).  For `n ∈ ℕ`, the Hamming code
`Hₙ = range (enc ·)` built from `Gₙ` is a 3-code: any two distinct codewords differ in
at least `3` coordinates, i.e. `cwWeight (x − y) ≥ 3`. -/
theorem lemma1 (n : ℕ) :
    ∀ x ∈ LinearMap.range (enc (fun v : Grows n => v.1)),
      ∀ y ∈ LinearMap.range (enc (fun v : Grows n => v.1)),
        x ≠ y → 3 ≤ cwWeight (x - y) := by
  intro x hx y hy hxy
  exact codeword_weight_ge_three (fun v : Grows n => v.1) Subtype.val_injective
    (fun v => v.2) (x - y) (sub_mem hx hy) (sub_ne_zero.mpr hxy)

/-! ## The Hamming code `Hₙ` and its radius-`1` balls (used by Lemma 2) -/

/-- Generator of the `G`-rows of `Hₙ`: the `i`-th row of `Gₙ` is `i.1`. -/
def Gfun (n : ℕ) : Grows n → BVec (Fin n) := fun v => v.1

section HammingHelpers
variable {δ : Type*} [Fintype δ]

lemma hammingNorm_neg (x : δ → ZMod 2) : hammingNorm (-x) = hammingNorm x := by
  simp only [hammingNorm, Pi.neg_apply]
  congr 1
  ext i
  simp

end HammingHelpers

section Abstract
variable {α β : Type*} [Fintype α] [Fintype β]

/-- Radius-`1` ball around a point `c` of the cube: `{x | ‖x − c‖ ≤ 1}`. -/
def ball (c : BVec α × BVec β) : Set (BVec α × BVec β) := {x | cwWeight (x - c) ≤ 1}

end Abstract

section UnitVec
variable {α : Type*} [DecidableEq α]

/-- The unit vector `eᵢ` (`1` at `i`, `0` elsewhere). -/
abbrev unitVec (i : α) : BVec α := Pi.single i (1 : ZMod 2)

end UnitVec

section UnitVecNorm
variable {α : Type*} [Fintype α] [DecidableEq α]

lemma hammingNorm_unitVec (i : α) : hammingNorm (unitVec i) = 1 := by
  classical
  have hset : (Finset.univ.filter (fun j => unitVec i j ≠ 0)) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; by_contra hj; exact h (by rw [unitVec, Pi.single_eq_of_ne hj])
    · intro h; subst h; simp [unitVec]
  rw [hammingNorm, hset, Finset.card_singleton]

end UnitVecNorm

section EncSub
variable {α β : Type*} [Fintype α]

lemma sub_enc (g : α → BVec β) (a : BVec α) (x : BVec α × BVec β) :
    x - enc g a = (x.1 - a, x.2 - ∑ j, a j • g j) := by
  ext <;> simp [enc]

end EncSub

section CoverHelpers
variable {α β : Type*} [Fintype α] [DecidableEq α]

lemma single_smul_sum (g : α → BVec β) (i : α) :
    (∑ j, (unitVec i) j • g j) = g i := by
  rw [Finset.sum_eq_single i]
  · simp [unitVec]
  · intro j _ hj; rw [show (unitVec i) j = 0 by rw [unitVec, Pi.single_eq_of_ne hj], zero_smul]
  · intro hi; exact absurd (Finset.mem_univ i) hi

lemma sum_add_single (g : α → BVec β) (a : BVec α) (i : α) :
    (∑ j, (a + unitVec i) j • g j) = (∑ j, a j • g j) + g i := by
  rw [Finset.sum_congr rfl (fun j _ => by rw [Pi.add_apply, add_smul]),
      Finset.sum_add_distrib, single_smul_sum]

end CoverHelpers

/-- **Covering / perfect-code fact.**  Every point of the cube `B^{2ⁿ−1}` lies in the
radius-`1` ball around some codeword of `Hₙ`.  Given `x = (u, v)`, the syndrome
`s = v − u·Gₙ` is either of weight `≤ 1` (so `(u, v)` is already within distance `1` of the
codeword `(u, u·Gₙ)`), or has weight `≥ 2`, hence is a `Gₙ`-row `gᵢ = s`, and then
`(u + eᵢ, (u + eᵢ)·Gₙ)` is within distance `1` of `(u, v)`. -/
lemma hamming_ball_cover (n : ℕ) :
    ∀ x : BVec (Grows n) × BVec (Fin n),
      ∃ c ∈ LinearMap.range (enc (Gfun n)), x ∈ ball c := by
  intro x
  obtain ⟨u, v⟩ := x
  by_cases hle : hammingNorm (v - ∑ j, u j • Gfun n j) ≤ 1
  · refine ⟨enc (Gfun n) u, ⟨u, rfl⟩, ?_⟩
    have hx : (u, v) - enc (Gfun n) u = (0, v - ∑ j, u j • Gfun n j) := by
      rw [sub_enc]; simp
    show cwWeight ((u, v) - enc (Gfun n) u) ≤ 1
    rw [hx]; simp only [cwWeight, hammingNorm_zero, zero_add]; exact hle
  · have hge : 2 ≤ hammingNorm (v - ∑ j, u j • Gfun n j) := by omega
    let i : Grows n := ⟨v - ∑ j, u j • Gfun n j, hge⟩
    refine ⟨enc (Gfun n) (u + unitVec i), ⟨u + unitVec i, rfl⟩, ?_⟩
    have hgi : Gfun n i = v - ∑ j, u j • Gfun n j := rfl
    have hx : (u, v) - enc (Gfun n) (u + unitVec i) = (-(unitVec i), 0) := by
      rw [sub_enc, sum_add_single (Gfun n) u i, hgi]
      have h1 : u - (u + unitVec i) = -(unitVec i) := by abel
      have h2 : v - ((∑ j, u j • Gfun n j) + (v - ∑ j, u j • Gfun n j)) = 0 := by abel
      rw [h1, h2]
    show cwWeight ((u, v) - enc (Gfun n) (u + unitVec i)) ≤ 1
    rw [hx]
    simp [cwWeight, hammingNorm_zero, hammingNorm_neg, hammingNorm_unitVec]

/-- The Hamming code `Hₙ`, the `GF(2)`-range of the systematic encoder `[E | Gₙ]`. -/
def hammingCode (n : ℕ) : Submodule (ZMod 2) (BVec (Grows n) × BVec (Fin n)) :=
  LinearMap.range (enc (Gfun n))

/-! ## Counting helpers for boolean cubes

Cardinalities of the boolean cube `B^δ`, of its low-weight vectors, and of the `G`-row set
`Grows n`, used in the counting arguments below. -/

section UnitVecBasic
variable {δ : Type*} [DecidableEq δ]

lemma unitVec_ne_zero (i : δ) : (unitVec i : BVec δ) ≠ 0 := by
  intro h
  have := congrFun h i
  simp only [unitVec, Pi.single_eq_same, Pi.zero_apply] at this
  exact one_ne_zero this

lemma unitVec_injective : Function.Injective (unitVec : δ → BVec δ) := by
  intro i j h
  have hh := congrFun h i
  simp only [unitVec, Pi.single_eq_same] at hh
  by_contra hij
  rw [Pi.single_eq_of_ne hij] at hh
  exact one_ne_zero hh

end UnitVecBasic

section EncInjective
variable {α β : Type*} [Fintype α]

end EncInjective

section BoolCount
variable {δ : Type*} [Fintype δ] [DecidableEq δ]

/-- The boolean cube `B^δ` has `2^{|δ|}` points. -/
lemma card_BVec : Fintype.card (δ → ZMod 2) = 2 ^ Fintype.card δ := by
  rw [Fintype.card_fun, ZMod.card]

lemma exists_unitVec_of_hammingNorm_eq_one {v : BVec δ} (h : hammingNorm v = 1) :
    ∃ i, v = unitVec i := by
  classical
  have hcard : (Finset.univ.filter (fun k => v k ≠ 0)).card = 1 := by
    rw [← h]; rfl
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hcard
  refine ⟨i, ?_⟩
  ext j
  by_cases hj : j = i
  · rw [hj, unitVec, Pi.single_eq_same]
    exact zmod_two_eq_one (by
      have : i ∈ Finset.univ.filter (fun k => v k ≠ 0) := by rw [hi]; simp
      simpa using this)
  · rw [unitVec, Pi.single_eq_of_ne hj]
    have : j ∉ Finset.univ.filter (fun k => v k ≠ 0) := by rw [hi]; simp [hj]
    simpa using this

/-- A boolean vector of weight `≤ 1` is either `0` or a unit vector. -/
lemma eq_zero_or_unitVec_of_hammingNorm_le_one {v : BVec δ} (h : hammingNorm v ≤ 1) :
    v = 0 ∨ ∃ i, v = unitVec i := by
  rcases Nat.eq_zero_or_pos (hammingNorm v) with h0 | hpos
  · exact Or.inl (hammingNorm_eq_zero.mp h0)
  · exact Or.inr (exists_unitVec_of_hammingNorm_eq_one (by omega))

/-- `δ`-dimensional boolean cube has `|δ| + 1` vectors of weight `≤ 1`. -/
lemma card_leOne : Fintype.card {v : BVec δ // hammingNorm v ≤ 1} = Fintype.card δ + 1 := by
  rw [Fintype.card_subtype]
  have hset : (Finset.univ.filter (fun v : BVec δ => hammingNorm v ≤ 1))
      = insert 0 (Finset.univ.image (unitVec : δ → BVec δ)) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_image]
    constructor
    · intro h
      rcases eq_zero_or_unitVec_of_hammingNorm_le_one h with h0 | ⟨i, hi⟩
      · exact Or.inl h0
      · exact Or.inr ⟨i, hi.symm⟩
    · rintro (rfl | ⟨i, rfl⟩)
      · simp
      · simp [hammingNorm_unitVec]
  rw [hset, Finset.card_insert_of_notMem (by
        rw [Finset.mem_image]; rintro ⟨i, -, hi⟩; exact unitVec_ne_zero i hi),
      Finset.card_image_of_injective (Finset.univ) unitVec_injective, Finset.card_univ]

end BoolCount

/-- `|Gₙ| = 2ⁿ − n − 1`: the number of length-`n` boolean rows of weight `≥ 2`. -/
theorem card_Grows (n : ℕ) : Fintype.card (Grows n) = 2 ^ n - n - 1 := by
  have hcongr : Fintype.card (Grows n)
      = Fintype.card {v : BVec (Fin n) // ¬ (hammingNorm v ≤ 1)} :=
    Fintype.card_congr (Equiv.subtypeEquivRight (fun v => by simp only [Nat.not_le]; omega))
  rw [hcongr, Fintype.card_subtype_compl, card_BVec, card_leOne, Fintype.card_fin, Nat.sub_sub]

section BallCount
variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- A codeword of weight `≤ 1` is `0`, or a unit vector in the `E`- or the `G`-segment. -/
lemma eq_zero_or_of_cwWeight_le_one {y : BVec α × BVec β} (h : cwWeight y ≤ 1) :
    y = 0 ∨ (∃ i, y = ((unitVec i : BVec α), (0 : BVec β)))
      ∨ (∃ j, y = ((0 : BVec α), (unitVec j : BVec β))) := by
  by_cases h1 : y.1 = 0
  · by_cases h2 : y.2 = 0
    · left; ext <;> simp [h1, h2]
    · right; right
      obtain ⟨j, hj⟩ := exists_unitVec_of_hammingNorm_eq_one (v := y.2) (by
        have : hammingNorm y.2 ≠ 0 := hammingNorm_ne_zero_iff.mpr h2
        have := h; simp only [cwWeight] at this; omega)
      exact ⟨j, by ext <;> simp [hj, h1]⟩
  · right; left
    have hy2' : y.2 = 0 := by
      have hz : hammingNorm y.2 = 0 := by
        have : hammingNorm y.1 ≠ 0 := hammingNorm_ne_zero_iff.mpr h1
        have := h; simp only [cwWeight] at this; omega
      exact hammingNorm_eq_zero.mp hz
    obtain ⟨i, hi⟩ := exists_unitVec_of_hammingNorm_eq_one (v := y.1) (by
      have : hammingNorm y.1 ≠ 0 := hammingNorm_ne_zero_iff.mpr h1
      have := h; simp only [cwWeight] at this; omega)
    exact ⟨i, by ext <;> simp [hi, hy2']⟩

end BallCount

/-! ## Lemma 2: the cube `Bⁿ` partitions into `2n` 3-codes -/

section Lemma2

/-- The coordinate set of the cube `B^{2^m−1}` split into its `E`-segment (rows `Gₘ`, indexed
by `Grows m`) and its `G`-segment (`Fin m`). -/
abbrev Coord (m : ℕ) := Grows m ⊕ Fin m

theorem card_Coord (m : ℕ) : Fintype.card (Coord m) = 2 ^ m - 1 := by
  rw [Fintype.card_sum, card_Grows, Fintype.card_fin]
  have h : m + 1 ≤ 2 ^ m := Nat.succ_le_of_lt m.lt_two_pow_self
  omega

theorem hammingNorm_unitVec_add {δ : Type*} [Fintype δ] [DecidableEq δ] {i j : δ} (h : i ≠ j) :
    hammingNorm (unitVec i + unitVec j : BVec δ) = 2 := by
  have hset : Finset.univ.filter (fun k : δ => (unitVec i + unitVec j) k ≠ 0) = {i, j} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    rw [Pi.add_apply]
    constructor
    · intro hk
      by_contra hc
      push Not at hc
      obtain ⟨hki, hkj⟩ := hc
      rw [unitVec, unitVec, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj, zero_add] at hk
      exact hk rfl
    · rintro (rfl | rfl)
      · rw [unitVec, unitVec, Pi.single_eq_same, Pi.single_eq_of_ne h, add_zero]
        exact one_ne_zero
      · rw [unitVec, unitVec, Pi.single_eq_of_ne (Ne.symm h), Pi.single_eq_same, zero_add]
        exact one_ne_zero
  rw [hammingNorm, hset, Finset.card_pair_eq_two_iff.mpr h]

/-- The `δ`-th coordinate unit vector of the cube `B^{2^m−1}`, in product form. -/
def coordUnit {m : ℕ} (δ : Coord m) : BVec (Grows m) × BVec (Fin m) :=
  Sum.elim (fun i => ((unitVec i : BVec (Grows m)), (0 : BVec (Fin m))))
    (fun j => ((0 : BVec (Grows m)), (unitVec j : BVec (Fin m)))) δ

theorem neg_self {m : ℕ} (x : BVec (Grows m) × BVec (Fin m)) : -x = x := by
  apply Prod.ext <;> funext k <;> exact CharTwo.neg_eq _

theorem cwWeight_coordUnit {m : ℕ} (δ : Coord m) : cwWeight (coordUnit δ) = 1 := by
  rcases δ with i | j <;> simp [coordUnit, cwWeight, hammingNorm_unitVec]

theorem cwWeight_coordUnit_add {m : ℕ} {δ δ' : Coord m} (h : δ ≠ δ') :
    cwWeight (coordUnit δ + coordUnit δ') = 2 := by
  rcases δ with i | j <;> rcases δ' with i' | j'
  · have hii : i ≠ i' := fun he => h (by rw [he])
    simp only [coordUnit, Sum.elim_inl, Prod.mk_add_mk, cwWeight, hammingNorm_zero, add_zero,
      hammingNorm_unitVec_add hii]
  · simp [coordUnit, cwWeight, hammingNorm_unitVec]
  · simp [coordUnit, cwWeight, hammingNorm_unitVec]
  · have hjj : j ≠ j' := fun he => h (by rw [he])
    simp only [coordUnit, Sum.elim_inr, Prod.mk_add_mk, cwWeight, hammingNorm_zero, zero_add,
      hammingNorm_unitVec_add hjj]

/-- The paper's sets `C₀, C₁, …` of the ball decomposition of `B^{2^m−1}`: `C₀ = H_m`, and
`C_δ` is `C₀` with coordinate `δ` flipped. -/
def paperSets (m : ℕ) : Option (Coord m) → Set (BVec (Grows m) × BVec (Fin m))
  | none => (hammingCode m : Set (BVec (Grows m) × BVec (Fin m)))
  | some δ =>
    (fun c => c + coordUnit δ) '' (hammingCode m : Set (BVec (Grows m) × BVec (Fin m)))

/-- Each `C_i` is a 3-code. -/
theorem paperSets_isThreeCode (m : ℕ) (k : Option (Coord m)) :
    ∀ x ∈ paperSets m k, ∀ y ∈ paperSets m k, x ≠ y → 3 ≤ cwWeight (x - y) := by
  intro x hx y hy hxy
  cases k with
  | none => exact lemma1 m x hx y hy hxy
  | some δ =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨c', hc', rfl⟩ := hy
    have hsub : (c + coordUnit δ) - (c' + coordUnit δ) = c - c' := by abel
    rw [hsub]
    exact lemma1 m c hc c' hc' (fun hcc => hxy (by rw [hcc]))

/-- The `C_i` are pairwise disjoint. -/
theorem paperSets_disjoint (m : ℕ) {k l : Option (Coord m)} (h : k ≠ l) :
    Disjoint (paperSets m k) (paperSets m l) := by
  rw [Set.disjoint_left]
  intro x hxk hxl
  cases k with
  | none =>
    cases l with
    | none => exact absurd rfl h
    | some δ =>
      obtain ⟨c', hc', hxeq⟩ := hxl
      have hxeq' : x = c' + coordUnit δ := hxeq.symm
      have hxc : x - c' = coordUnit δ := by rw [hxeq']; abel_nf
      have hcw : cwWeight (x - c') = 1 := by rw [hxc, cwWeight_coordUnit]
      have hne : x ≠ c' := by
        intro hx0
        have hz : cwWeight (0 : BVec (Grows m) × BVec (Fin m)) = 1 := by
          have h0 : (0 : BVec (Grows m) × BVec (Fin m)) = x - c' := by rw [hx0, sub_self]
          rw [h0]; exact hcw
        simp [cwWeight, hammingNorm_zero] at hz
      exact absurd (lemma1 m x hxk c' hc' hne) (by omega)
  | some δ =>
    cases l with
    | none =>
      obtain ⟨c, hc, hxeq⟩ := hxk
      have hxeq' : x = c + coordUnit δ := hxeq.symm
      have hxc : x - c = coordUnit δ := by rw [hxeq']; abel_nf
      have hcw : cwWeight (x - c) = 1 := by rw [hxc, cwWeight_coordUnit]
      have hne : x ≠ c := by
        intro hx0
        have hz : cwWeight (0 : BVec (Grows m) × BVec (Fin m)) = 1 := by
          have h0 : (0 : BVec (Grows m) × BVec (Fin m)) = x - c := by rw [hx0, sub_self]
          rw [h0]; exact hcw
        simp [cwWeight, hammingNorm_zero] at hz
      exact absurd (lemma1 m x hxl c hc hne) (by omega)
    | some δ' =>
      have hδ : δ ≠ δ' := fun he => h (by rw [he])
      obtain ⟨c, hc, hxeq⟩ := hxk
      obtain ⟨c', hc', hxeq'⟩ := hxl
      have h2 : c + coordUnit δ = c' + coordUnit δ' := hxeq.trans hxeq'.symm
      have heq : c - c' = coordUnit δ' - coordUnit δ := by linear_combination h2
      have hcw : cwWeight (c - c') = 2 := by
        rw [heq, sub_eq_add_neg, neg_self, cwWeight_coordUnit_add (Ne.symm hδ)]
      have hcc : c = c' := by
        by_contra hne
        exact absurd (lemma1 m c hc c' hc' hne) (by omega)
      have hz : cwWeight (0 : BVec (Grows m) × BVec (Fin m)) = 2 := by
        have h0 : (0 : BVec (Grows m) × BVec (Fin m)) = c - c' := by rw [hcc, sub_self]
        rw [h0]; exact hcw
      simp [cwWeight, hammingNorm_zero] at hz

/-- The `C_i` cover the whole cube `B^{2^m−1}`. -/
theorem paperSets_cover (m : ℕ) : Set.univ = ⋃ k, paperSets m k := by
  rw [eq_comm]
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨c, hc, hxball⟩ := hamming_ball_cover m x
  rcases eq_zero_or_of_cwWeight_le_one hxball with h0 | ⟨i, hi⟩ | ⟨j, hj⟩
  · refine Set.mem_iUnion.mpr ⟨none, ?_⟩
    rw [sub_eq_zero] at h0
    rw [h0]; exact hc
  · refine Set.mem_iUnion.mpr ⟨some (Sum.inl i), ?_⟩
    refine ⟨c, hc, ?_⟩
    have hδ : coordUnit (Sum.inl i) = (unitVec i, (0 : BVec (Fin m))) := by simp [coordUnit]
    rw [hδ, ← hi]; abel_nf
  · refine Set.mem_iUnion.mpr ⟨some (Sum.inr j), ?_⟩
    refine ⟨c, hc, ?_⟩
    have hδ : coordUnit (Sum.inr j) = ((0 : BVec (Grows m)), unitVec j) := by simp [coordUnit]
    rw [hδ, ← hj]; abel_nf

/-- Currying equivalence `BVec (Coord m) ≃ₗ (BVec (Grows m) × BVec (Fin m))`. -/
def toProd (m : ℕ) : BVec (Coord m) ≃ₗ[ZMod 2] (BVec (Grows m) × BVec (Fin m)) where
  toFun z := (fun i => z (Sum.inl i), fun j => z (Sum.inr j))
  map_add' z w := by apply Prod.ext <;> funext i <;> rfl
  map_smul' c z := by apply Prod.ext <;> funext i <;> rfl
  invFun p := fun δ => Sum.elim p.1 p.2 δ
  left_inv z := by funext δ; rcases δ with i | j <;> rfl
  right_inv p := by apply Prod.ext <;> funext i <;> rfl

theorem cwWeight_toProd (m : ℕ) (z : BVec (Coord m)) : cwWeight (toProd m z) = hammingNorm z := by
  have hset : Finset.univ.filter (fun δ : Coord m => z δ ≠ 0)
      = (Finset.univ.filter (fun i : Grows m => z (Sum.inl i) ≠ 0)).image Sum.inl
        ∪ (Finset.univ.filter (fun j : Fin m => z (Sum.inr j) ≠ 0)).image Sum.inr := by
    apply Finset.ext
    intro δ
    cases δ with
    | inl i => simp
    | inr j => simp
  have hdisj : Disjoint ((Finset.univ.filter (fun i : Grows m => z (Sum.inl i) ≠ 0)).image Sum.inl)
      ((Finset.univ.filter (fun j : Fin m => z (Sum.inr j) ≠ 0)).image Sum.inr) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    rw [Finset.mem_image] at hxA hxB
    obtain ⟨i, -, hi⟩ := hxA
    obtain ⟨j, -, hj⟩ := hxB
    cases hi.trans hj.symm
  have hcard : (Finset.univ.filter (fun i : Grows m => z (Sum.inl i) ≠ 0)).card
      + (Finset.univ.filter (fun j : Fin m => z (Sum.inr j) ≠ 0)).card
      = (Finset.univ.filter (fun δ : Coord m => z δ ≠ 0)).card := by
    simp only [hset, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective]
  have hgoal : cwWeight (toProd m z)
      = (Finset.univ.filter (fun i : Grows m => z (Sum.inl i) ≠ 0)).card
        + (Finset.univ.filter (fun j : Fin m => z (Sum.inr j) ≠ 0)).card := rfl
  have hrhs : hammingNorm z = (Finset.univ.filter (fun δ : Coord m => z δ ≠ 0)).card := rfl
  simp only [hgoal, hcard, hrhs]

theorem toProd_injective (m : ℕ) : Function.Injective (toProd m) := by
  intro x y h
  have := congrArg (toProd m).symm h
  simpa using this

theorem paperSetsC_isThreeCode (m : ℕ) (k : Option (Coord m)) :
    ∀ x ∈ (toProd m ⁻¹' paperSets m k), ∀ y ∈ (toProd m ⁻¹' paperSets m k),
      x ≠ y → 3 ≤ hammingNorm (x - y) := by
  intro x hx y hy hxy
  rw [Set.mem_preimage] at hx hy
  have hxy' : toProd m x ≠ toProd m y := fun he => hxy (toProd_injective m he)
  have h := paperSets_isThreeCode m k (toProd m x) hx (toProd m y) hy hxy'
  rwa [← map_sub, cwWeight_toProd] at h

theorem paperSetsC_disjoint (m : ℕ) {k l : Option (Coord m)} (h : k ≠ l) :
    Disjoint (toProd m ⁻¹' paperSets m k) (toProd m ⁻¹' paperSets m l) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  rw [Set.mem_preimage] at hz hz'
  exact Set.disjoint_left.mp (paperSets_disjoint m h) hz hz'

theorem paperSetsC_cover (m : ℕ) : Set.univ = ⋃ k, (toProd m ⁻¹' paperSets m k) := by
  rw [eq_comm]
  apply Set.eq_univ_of_forall
  intro z
  have hz : toProd m z ∈ (Set.univ : Set (BVec (Grows m) × BVec (Fin m))) := trivial
  rw [paperSets_cover m] at hz
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
  exact Set.mem_iUnion.mpr ⟨k, hk⟩

/-- Embed `Bⁿ` into `BVec (Coord m)` by placing the word `c` on the coordinates in the range of
`ψ` and `0` elsewhere. -/
noncomputable def embC {n m : ℕ} (ψ : Fin n ↪ Coord m) (c : BVec (Fin n)) : BVec (Coord m) :=
  fun δ => if h : ∃ k, ψ k = δ then c h.choose else 0

theorem embC_sub {n m : ℕ} (ψ : Fin n ↪ Coord m) (c d : BVec (Fin n)) :
    embC ψ (c - d) = embC ψ c - embC ψ d := by
  funext δ
  by_cases h : ∃ k, ψ k = δ <;> simp [embC, h, Pi.sub_apply]

theorem hammingNorm_embC {n m : ℕ} (ψ : Fin n ↪ Coord m)
    (c : BVec (Fin n)) : hammingNorm (embC ψ c) = hammingNorm c := by
  have hset : (Finset.univ.filter (fun δ : Coord m => embC ψ c δ ≠ 0))
      = (Finset.univ.filter (fun k : Fin n => c k ≠ 0)).image ψ := by
    ext δ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      have hex : ∃ k, ψ k = δ := by
        by_contra hc
        exact h (by simp [embC, hc])
      refine ⟨hex.choose, ?_, hex.choose_spec⟩
      have hval : embC ψ c δ = c hex.choose := by simp [embC, hex]
      rwa [hval] at h
    · rintro ⟨k, hk, rfl⟩
      have hex : ∃ k', ψ k' = ψ k := ⟨k, rfl⟩
      have hval : embC ψ c (ψ k) = c k := by
        have h1 : embC ψ c (ψ k) = c hex.choose := by simp only [embC, dite_eq_left hex]
        rw [h1, ψ.injective hex.choose_spec]
      rw [hval]; exact hk
  have key : (Finset.univ.filter (fun δ : Coord m => embC ψ c δ ≠ 0)).card
      = (Finset.univ.filter (fun k : Fin n => c k ≠ 0)).card := by
    rw [hset]
    exact Finset.card_image_of_injective _ ψ.injective
  simpa only [hammingNorm] using key

theorem embC_injective {n m : ℕ} (ψ : Fin n ↪ Coord m) : Function.Injective (embC ψ) := by
  intro c d h
  have hz : hammingNorm (c - d) = 0 := by
    rw [← hammingNorm_embC ψ (c - d), embC_sub, h, sub_self, hammingNorm_zero]
  exact sub_eq_zero.mp (hammingNorm_eq_zero.mp hz)

/-- The induced partition `Γᵢ = {c ∈ Bⁿ | (c, 0⃗) ∈ Cᵢ}` of the paper. -/
noncomputable def Gamma {n m : ℕ} (ψ : Fin n ↪ Coord m) (k : Option (Coord m)) :
    Set (BVec (Fin n)) := embC ψ ⁻¹' (toProd m ⁻¹' paperSets m k)

theorem Gamma_isThreeCode {n m : ℕ} (ψ : Fin n ↪ Coord m) (k : Option (Coord m)) :
    ∀ x ∈ Gamma ψ k, ∀ y ∈ Gamma ψ k, x ≠ y → 3 ≤ hammingNorm (x - y) := by
  intro x hx y hy hxy
  rw [Gamma, Set.mem_preimage] at hx hy
  have heq : embC ψ x - embC ψ y = embC ψ (x - y) := (embC_sub ψ x y).symm
  have hne : embC ψ x ≠ embC ψ y := fun h => hxy (embC_injective ψ h)
  have h := paperSetsC_isThreeCode m k (embC ψ x) hx (embC ψ y) hy hne
  rwa [heq, hammingNorm_embC ψ] at h

theorem Gamma_disjoint {n m : ℕ} (ψ : Fin n ↪ Coord m) {k l : Option (Coord m)} (h : k ≠ l) :
    Disjoint (Gamma ψ k) (Gamma ψ l) := by
  rw [Set.disjoint_left]
  intro z hz hz'
  rw [Gamma, Set.mem_preimage] at hz hz'
  exact Set.disjoint_left.mp (paperSetsC_disjoint m h) hz hz'

theorem Gamma_cover {n m : ℕ} (ψ : Fin n ↪ Coord m) : Set.univ = ⋃ k, Gamma ψ k := by
  rw [eq_comm]
  apply Set.eq_univ_of_forall
  intro z
  have hz : embC ψ z ∈ (Set.univ : Set (BVec (Coord m))) := trivial
  rw [paperSetsC_cover m] at hz
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
  exact Set.mem_iUnion.mpr ⟨k, by rwa [Gamma, Set.mem_preimage]⟩

/-- An injection `Fin n ↪ Coord m` whenever `n ≤ 2^m − 1`. -/
noncomputable def finEmbedding {n m : ℕ} (h : n ≤ 2 ^ m - 1) : Fin n ↪ Coord m :=
  (Function.Embedding.mk (Fin.castLE (by rw [card_Coord]; exact h))
      (fun a b hab => Fin.ext (by simpa using congrArg Fin.val hab))).trans
    (Fintype.equivFin (Coord m)).symm.toEmbedding

end Lemma2

/-- The least power of two `≥ n + 1` is at most `2n`: `2^{⌈log₂(n+1)⌉} ≤ 2n` for `n ≥ 1`.
This is the paper's bound `N + 1 = 2^m ≤ 2n` (since `2^{m−1} ≤ n`). -/
theorem two_pow_clog_le (n : ℕ) (hn : 1 ≤ n) : 2 ^ Nat.clog 2 (n + 1) ≤ 2 * n := by
  have hb : 1 < (2 : ℕ) := by norm_num
  have hpos : 0 < Nat.clog 2 (n + 1) := Nat.clog_pos hb (by omega)
  have hpred : 2 ^ (Nat.clog 2 (n + 1) - 1) ≤ n := by
    have h := Nat.pow_lt_of_lt_clog (b := 2) (x := n + 1)
      (show Nat.clog 2 (n + 1) - 1 < Nat.clog 2 (n + 1) by omega)
    omega
  calc 2 ^ Nat.clog 2 (n + 1)
      = 2 ^ ((Nat.clog 2 (n + 1) - 1) + 1) := by congr 1; omega
    _ = 2 ^ (Nat.clog 2 (n + 1) - 1) * 2 := by rw [pow_succ]
    _ = 2 * 2 ^ (Nat.clog 2 (n + 1) - 1) := by ring
    _ ≤ 2 * n := Nat.mul_le_mul_left 2 hpred

/-- **Lemma 2** (Lemma 1 in the paper).  For `n ∈ ℕ` with `n ≥ 1`, the cube `Bⁿ` can be partitioned into
`2 * n` parts, each of which is a 3-code.  The parts are the `Γᵢ` obtained by restricting the
Hamming-code ball decomposition of `B^{2^m−1}` (Corollary 1) to `Bⁿ`, where `2^m` is the least
power of two `≥ n + 1`.  Since `2^m ≤ 2 * n` (`two_pow_clog_le`), the `2^m` code parts are padded
to `2 * n` parts with `∅` (a vacuous 3-code) — the paper's "partitioned into `2n` parts that are
3-codes". -/
theorem lemma2 (n : ℕ) (hn : 1 ≤ n) :
    ∃ (Γ : Fin (2 * n) → Set (BVec (Fin n))),
      (∀ i, ∀ x ∈ Γ i, ∀ y ∈ Γ i, x ≠ y → 3 ≤ hammingNorm (x - y)) ∧
      (∀ i j, i ≠ j → Disjoint (Γ i) (Γ j)) ∧
      Set.univ = ⋃ i, Γ i := by
  have hb : 1 < (2 : ℕ) := by norm_num
  set m : ℕ := Nat.clog 2 (n + 1) with hm
  have hNm : n ≤ 2 ^ m - 1 := by
    have h := Nat.le_pow_clog hb (n + 1)
    rw [hm]; omega
  have hbound : 2 ^ m ≤ 2 * n := by rw [hm]; exact two_pow_clog_le n hn
  have hcardOpt : Fintype.card (Option (Coord m)) = 2 ^ m := by
    rw [Fintype.card_option, card_Coord]
    have h : m + 1 ≤ 2 ^ m := Nat.succ_le_of_lt m.lt_two_pow_self
    omega
  let e : Option (Coord m) ≃ Fin (2 ^ m) := (Fintype.equivFin _).trans (finCongr hcardOpt)
  let G : Fin (2 ^ m) → Set (BVec (Fin n)) := fun i => Gamma (finEmbedding hNm) (e.symm i)
  have hG_three : ∀ i, ∀ x ∈ G i, ∀ y ∈ G i, x ≠ y → 3 ≤ hammingNorm (x - y) :=
    fun i => Gamma_isThreeCode (finEmbedding hNm) (e.symm i)
  have hG_disj : ∀ i j, i ≠ j → Disjoint (G i) (G j) :=
    fun i j hij => Gamma_disjoint (finEmbedding hNm) (fun h => hij (e.symm.injective h))
  have hG_cover : Set.univ = ⋃ i, G i := by
    show Set.univ = ⋃ i, Gamma (finEmbedding hNm) (e.symm i)
    rw [Gamma_cover (finEmbedding hNm)]
    apply le_antisymm
    · intro z hz
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion.mpr ⟨e k, by rw [Equiv.symm_apply_apply]; exact hk⟩
    · intro z hz
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion.mpr ⟨e.symm i, hi⟩
  let P : Fin (2 * n) → Set (BVec (Fin n)) :=
    fun i => if h : (i : ℕ) < 2 ^ m then G ⟨i, h⟩ else ∅
  have hPunfold : ∀ i, P i = (if h : (i : ℕ) < 2 ^ m then G ⟨i, h⟩ else ∅) := fun i => rfl
  refine ⟨P, ?_, ?_, ?_⟩
  · intro i x hx y hy hxy
    rw [hPunfold i] at hx hy
    by_cases h : (i : ℕ) < 2 ^ m
    · rw [dite_eq_left h] at hx hy
      exact hG_three ⟨i, h⟩ x hx y hy hxy
    · rw [dite_eq_right h] at hx
      exact absurd hx (by simp)
  · intro i j hij
    rw [hPunfold i, hPunfold j]
    by_cases hi : (i : ℕ) < 2 ^ m
    · by_cases hj : (j : ℕ) < 2 ^ m
      · rw [dite_eq_left hi, dite_eq_left hj]
        exact hG_disj ⟨i, hi⟩ ⟨j, hj⟩ (fun h => hij (Fin.ext (by simpa using congrArg Fin.val h)))
      · rw [dite_eq_left hi, dite_eq_right hj]; simp
    · rw [dite_eq_right hi]; simp
  · rw [eq_comm]
    apply Set.eq_univ_of_forall
    intro z
    have hz : z ∈ ⋃ j, G j := by rw [← hG_cover]; trivial
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hz
    refine Set.mem_iUnion.mpr ⟨Fin.castLEEmb hbound j, ?_⟩
    rw [hPunfold (Fin.castLEEmb hbound j)]
    have hlt : ((Fin.castLEEmb hbound j : Fin (2 * n)) : ℕ) < 2 ^ m := j.isLt
    rw [dite_eq_left hlt]
    exact hj

/-! ## The binomial-entropy bound (inequality (2) of the paper)

The paper records the standard two-sided estimate of the binomial coefficients

`1/n . 2^{nH(k/n)} <= C^n_k <= 2^{nH(k/n)}`   `(2)`

valid as `min {k, n - k} -> infinity`, where `H x = -x log2 x - (1 - x) log2 (1 - x)` is the
binary entropy.  We prove the sharp (non-asymptotic) form of it, valid for all `0 < k < n`:

* `choose_le_two_pow_H2` : `C^n_k <= 2^{nH(k/n)}`;
* `two_pow_H2_div_le_choose` : `2^{nH(k/n)} / (n+1) <= C^n_k`.

The upper bound is the binomial-theorem estimate
`1 = (k/n + (n-k)/n)^n >= C^n_k (k/n)^k ((n-k)/n)^{n-k}`.  The lower bound uses the modal
term of the binomial pmf: `t_j = C^n_j (k/n)^j ((n-k)/n)^{n-j}` is increasing for `j <= k`
and decreasing for `j >= k` (`hup`, `hdown`), so `t_k` is the maximum and
`1 = sum_j t_j <= (n+1) . t_k`.  Both are converted to the paper's base-2 expression via
`two_pow_mul_H2_eq`.  (The paper's coefficient `1/n` is the sharp `1/(n+1)` up to the factor
`1 + 1/n`, which is irrelevant for its asymptotic notation.) -/
section BinomialEntropy

/-- Binary entropy function with the base-`2` logarithm (the paper's `H`):
`H x = -x log2 x - (1-x) log2 (1-x)`, with the convention `logb 2 0 = 0` (so `H 0 = H 1 = 0`). -/
noncomputable def H2 (x : ℝ) : ℝ := -x * Real.logb 2 x - (1 - x) * Real.logb 2 (1 - x)
lemma log2_mul_logb (x : ℝ) : Real.log 2 * Real.logb 2 x = Real.log x := by
  rw [Real.logb]; field_simp

lemma log2_mul_H2 (x : ℝ) : Real.log 2 * H2 x = Real.binEntropy x := by
  rw [H2, Real.binEntropy, Real.log_inv, Real.log_inv]
  rw [show Real.log 2 * (-x * Real.logb 2 x - (1 - x) * Real.logb 2 (1 - x))
        = -(x * (Real.log 2 * Real.logb 2 x)) - ((1 - x) * (Real.log 2 * Real.logb 2 (1 - x)))
        by ring]
  rw [log2_mul_logb, log2_mul_logb]
  ring

lemma two_pow_H2_eq_exp (x : ℝ) : (2:ℝ) ^ H2 x = Real.exp (Real.binEntropy x) := by
  rw [Real.rpow_def_of_pos (by norm_num), log2_mul_H2]

lemma two_pow_mul_H2_eq (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    (2:ℝ) ^ ((n:ℝ) * H2 ((k:ℝ)/n))
      = ((n:ℝ)/k)^k * ((n:ℝ)/((n-k:ℕ):ℝ))^(n-k) := by
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le hk (le_of_lt hkn))
  have hnk0 : (0:ℝ) < ((n-k:ℕ):ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt hkn : 0 < n - k)
  rw [show (n:ℝ) * H2 ((k:ℝ)/n) = H2 ((k:ℝ)/n) * (n:ℝ) by ring,
      Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast, two_pow_H2_eq_exp]
  rw [← Real.exp_nat_mul]
  rw [show ((n:ℝ)/k)^k = Real.exp ((k:ℝ) * Real.log ((n:ℝ)/k)) by
        rw [Real.exp_nat_mul, Real.exp_log (div_pos hn0 hk0)],
      show ((n:ℝ)/((n-k:ℕ):ℝ))^(n-k)
            = Real.exp (((n-k:ℕ):ℝ) * Real.log ((n:ℝ)/((n-k:ℕ):ℝ))) by
        rw [Real.exp_nat_mul, Real.exp_log (div_pos hn0 hnk0)]]
  rw [← Real.exp_add, Real.exp_eq_exp]
  rw [Real.binEntropy, Real.log_inv, Real.log_inv]
  have h1 : (1:ℝ) - (k:ℝ)/n = ((n-k:ℕ):ℝ)/n := by
    rw [Nat.cast_sub (le_of_lt hkn)]; field_simp
  rw [h1]
  rw [Real.log_div hk0.ne' hn0.ne', Real.log_div hnk0.ne' hn0.ne',
      Real.log_div hn0.ne' hk0.ne', Real.log_div hn0.ne' hnk0.ne']
  field_simp
  ring

lemma choose_le_prod (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    (n.choose k : ℝ) ≤ ((n:ℝ)/k)^k * ((n:ℝ)/((n-k:ℕ):ℝ))^(n-k) := by
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le hk (le_of_lt hkn))
  have hnk0 : (0:ℝ) < ((n-k:ℕ):ℝ) := by
    exact_mod_cast (Nat.sub_pos_of_lt hkn : 0 < n - k)
  set x : ℝ := (k:ℝ)/n with hx
  set y : ℝ := ((n-k:ℕ):ℝ)/n with hy
  have hx0 : 0 < x := by rw [hx]; exact div_pos hk0 hn0
  have hy0 : 0 < y := by rw [hy]; exact div_pos hnk0 hn0
  have hxy : x + y = 1 := by
    rw [hx, hy, ← add_div, Nat.cast_sub (le_of_lt hkn)]; field_simp; ring
  have hsum : (1:ℝ) = ∑ m ∈ range (n+1), x^m * y^(n-m) * (n.choose m : ℝ) := by
    rw [← add_pow x y n, hxy, one_pow]
  have hmem : k ∈ range (n+1) :=
    mem_range.mpr (Nat.lt_succ_of_le (le_of_lt hkn))
  have hnonneg : ∀ m ∈ range (n+1), (0:ℝ) ≤ x^m * y^(n-m) * (n.choose m : ℝ) := by
    intro m _
    exact mul_nonneg (mul_nonneg (pow_nonneg hx0.le m) (pow_nonneg hy0.le (n-m)))
      (Nat.cast_nonneg _)
  have hle : x^k * y^(n-k) * (n.choose k : ℝ) ≤ 1 := by
    have := single_le_sum (s := range (n+1))
      (f := fun m => x^m * y^(n-m) * (n.choose m : ℝ)) hnonneg hmem
    rw [← hsum] at this
    exact this
  have ha0 : 0 < x^k * y^(n-k) := mul_pos (pow_pos hx0 k) (pow_pos hy0 (n-k))
  have ha_inv : (x^k * y^(n-k))⁻¹ = ((n:ℝ)/k)^k * ((n:ℝ)/((n-k:ℕ):ℝ))^(n-k) := by
    rw [hx, hy, mul_inv, ← inv_pow, ← inv_pow, inv_div, inv_div]
  calc (n.choose k : ℝ)
      = (x^k * y^(n-k))⁻¹ * (x^k * y^(n-k) * (n.choose k : ℝ)) := by
        rw [← mul_assoc, inv_mul_cancel₀ ha0.ne', one_mul]
    _ ≤ (x^k * y^(n-k))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr ha0.le)
    _ = ((n:ℝ)/k)^k * ((n:ℝ)/((n-k:ℕ):ℝ))^(n-k) := by rw [mul_one, ha_inv]

theorem choose_le_two_pow_H2_of_pos (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    (n.choose k : ℝ) ≤ (2:ℝ) ^ ((n:ℝ) * H2 ((k:ℝ)/n)) := by
  rw [two_pow_mul_H2_eq n k hk hkn]
  exact choose_le_prod n k hk hkn

/-- Inequality `(2)`, upper bound `C^n_k <= 2^{nH(k/n)}`, for all `k <= n`. -/
theorem choose_le_two_pow_H2 (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℝ) ≤ (2:ℝ) ^ ((n:ℝ) * H2 ((k:ℝ)/n)) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    rw [Nat.choose_zero_right, Nat.cast_one]
    simp [H2]
  · rcases eq_or_lt_of_le hk with hkn | hkn
    · rw [hkn]
      rw [Nat.choose_self, Nat.cast_one]
      have hnR : (n:ℝ) ≠ 0 := by
        have : 0 < n := by rw [← hkn]; exact hkpos
        exact_mod_cast this.ne'
      rw [div_self hnR]
      simp [H2]
    · exact choose_le_two_pow_H2_of_pos n k hkpos hkn

end BinomialEntropy

/-! ## The disjointness matrix `Uₙ`: rectangles and the covering vocabulary

Rows and columns of `Uₙ` are indexed by the boolean vectors `BVec (Fin n)` (the subsets of `[n]`,
via `support`); `Uₙ[a,b] = 1` iff `interCard a b = 0`.  A *rectangle* `R × C` is a submatrix
without a `0`-entry (`IsRectangle`); `HasPartFin`/`HasCoverFin` record that the `1`-entries are
partitioned/covered by rectangles.  The section also provides the restriction, extension and
reindexing bookkeeping (`reindexBVec`, `restrict`, `extend`) used to transport the covering
constructions between cubes. -/

def support (v : BVec ι) : Finset ι := Finset.univ.filter (fun i => v i ≠ 0)

omit [DecidableEq ι] in
lemma hammingNorm_eq_support (v : BVec ι) : hammingNorm v = (support v).card := rfl

def interCard (a b : BVec ι) : ℕ := (Finset.univ.filter (fun i => a i ≠ 0 ∧ b i ≠ 0)).card

def IsRectangle (R C : Finset (BVec ι)) : Prop := ∀ a ∈ R, ∀ b ∈ C, interCard a b ≠ 1

/-- The `1`-entries of the disjointness matrix are *partitioned* by `k` pairwise disjoint
rectangles `R i × C i`: each is a rectangle (`IsRectangle`, no `0`-entry), they cover every
`1`-entry, and no `1`-entry lies in two of them.  (Rectangles may share `*`-entries; disjointness
is required only on the `1`-entries, which is the condition that makes the family a partition of
the support of the matrix — this is exactly `rk⁺ Uₙ`.) -/
def HasPartFin (n k : ℕ) : Prop :=
  ∃ R C : Fin k → Finset (BVec (Fin n)), (∀ i, IsRectangle (R i) (C i)) ∧
    (∀ a b : BVec (Fin n), interCard a b = 0 → ∃ i, a ∈ R i ∧ b ∈ C i) ∧
    (∀ i j, i ≠ j → ∀ a b : BVec (Fin n), a ∈ R i → b ∈ C i → a ∈ R j → b ∈ C j →
      interCard a b ≠ 0)

lemma hasPartFin_of_card_eq {n k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = k) (R C : ι → Finset (BVec (Fin n)))
    (hR : ∀ i, IsRectangle (R i) (C i))
    (hCov : ∀ a b : BVec (Fin n), interCard a b = 0 → ∃ i, a ∈ R i ∧ b ∈ C i)
    (hDisj : ∀ i j : ι, i ≠ j → ∀ a b : BVec (Fin n), a ∈ R i → b ∈ C i → a ∈ R j → b ∈ C j →
      interCard a b ≠ 0) :
    HasPartFin n k := by
  classical
  let e : ι ≃ Fin k := (Fintype.equivFin ι).trans (finCongr hι)
  refine ⟨fun i => R (e.symm i), fun i => C (e.symm i), ?_, ?_, ?_⟩
  · intro i; exact hR _
  · intro a b hab
    obtain ⟨i, hi⟩ := hCov a b hab
    exact ⟨e i, by show a ∈ R (e.symm (e i)); rw [Equiv.symm_apply_apply]; exact hi.1,
      by show b ∈ C (e.symm (e i)); rw [Equiv.symm_apply_apply]; exact hi.2⟩
  · intro i j hij a b hai hbi haj hbj
    exact hDisj (e.symm i) (e.symm j) (fun h => hij (e.symm.injective h)) a b hai hbi haj hbj

lemma card_sq_BVec (n : ℕ) : Fintype.card (BVec (Fin n) × BVec (Fin n)) = 4 ^ n := by
  rw [Fintype.card_prod, card_BVec, Fintype.card_fin, ← pow_add,
    show n + n = 2 * n by ring, pow_mul]
  norm_num

lemma hasPartFin_four (n : ℕ) : HasPartFin n (4 ^ n) := by
  refine hasPartFin_of_card_eq (card_sq_BVec n)
    (fun p => if interCard p.1 p.2 = 0 then {p.1} else ∅)
    (fun p => if interCard p.1 p.2 = 0 then {p.2} else ∅) ?_ ?_ ?_
  · rintro ⟨a, b⟩
    by_cases h : interCard a b = 0
    · intro x hx y hy
      simp only [h, ↓reduceIte, Finset.mem_singleton] at hx
      simp only [h, ↓reduceIte, Finset.mem_singleton] at hy
      rw [hx, hy, h]; omega
    · simp only [h, ↓reduceIte]; simp [IsRectangle]
  · intro a b hab
    exact ⟨(a, b), by simp only [hab, ↓reduceIte, Finset.mem_singleton],
      by simp only [hab, ↓reduceIte, Finset.mem_singleton]⟩
  · intro i j hij a b hai hbi haj hbj
    by_cases hi : interCard i.1 i.2 = 0
    · by_cases hj : interCard j.1 j.2 = 0
      · simp only [hi, hj, ↓reduceIte, Finset.mem_singleton] at hai hbi haj hbj
        exact absurd (Prod.ext (hai.symm.trans haj) (hbi.symm.trans hbj)) hij
      · simp only [hj, ↓reduceIte] at haj
        exact absurd haj (by simp)
    · simp only [hi, ↓reduceIte] at hai
      exact absurd hai (by simp)

section Transport

def reindexBVec {ι κ : Type*} (e : ι ≃ κ) (x : BVec ι) : BVec κ := fun k => x (e.symm k)

lemma reindexBVec_sub {ι κ : Type*} (e : ι ≃ κ) (x y : BVec ι) :
    reindexBVec e (x - y) = reindexBVec e x - reindexBVec e y := by
  funext k; simp [reindexBVec, Pi.sub_apply]

lemma reindexBVec_injective {ι κ : Type*} (e : ι ≃ κ) : Function.Injective (reindexBVec e) := by
  intro x y h
  funext i
  have := congrFun h (e i)
  simpa [reindexBVec] using this

lemma hammingNorm_reindexBVec {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (x : BVec ι) : hammingNorm (reindexBVec e x) = hammingNorm x := by
  have hset : (Finset.univ.filter (fun k : κ => reindexBVec e x k ≠ 0))
      = (Finset.univ.filter (fun i : ι => x i ≠ 0)).image (e : ι → κ) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h; exact ⟨e.symm k, by simpa [reindexBVec] using h, e.apply_symm_apply k⟩
    · rintro ⟨i, hi, rfl⟩; simpa [reindexBVec] using hi
  rw [hammingNorm, hset, Finset.card_image_of_injective _ e.injective]
  rfl

lemma hammingNorm_one_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (x : BVec ι) :
    hammingNorm ((1 : BVec ι) - x) = Fintype.card ι - hammingNorm x := by
  have hset : (Finset.univ.filter (fun i : ι => ((1 : BVec ι) - x) i ≠ 0))
      = Finset.univ.filter (fun i : ι => x i = 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, Pi.one_apply]
    constructor
    · intro h; by_contra hx
      rw [zmod_two_eq_one hx, sub_self] at h; exact h rfl
    · intro h; rw [h, sub_zero]; norm_num
  have hset2 : (Finset.univ.filter (fun i : ι => x i = 0))
      = Finset.univ \ Finset.univ.filter (fun i : ι => x i ≠ 0) := by
    ext i; simp [Finset.mem_filter]
  have hc : (Finset.univ.filter (fun i : ι => x i = 0)).card
      = Fintype.card ι - (Finset.univ.filter (fun i : ι => x i ≠ 0)).card := by
    rw [hset2, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
  calc hammingNorm ((1 : BVec ι) - x)
      = (Finset.univ.filter (fun i : ι => ((1 : BVec ι) - x) i ≠ 0)).card := rfl
    _ = (Finset.univ.filter (fun i : ι => x i = 0)).card := by rw [hset]
    _ = Fintype.card ι - (Finset.univ.filter (fun i : ι => x i ≠ 0)).card := hc
    _ = Fintype.card ι - hammingNorm x := rfl

end Transport

section Counts

lemma card_weight_eq_choose (n p : ℕ) :
    Fintype.card {a : BVec (Fin n) // hammingNorm a = p} = n.choose p := by
  classical
  have key : Fintype.card {a : BVec (Fin n) // hammingNorm a = p}
      = Fintype.card {s : Finset (Fin n) // s.card = p} := by
    apply Fintype.card_congr
    refine
      { toFun := fun a => ⟨support a.1, by rw [← hammingNorm_eq_support]; exact a.2⟩
        invFun := fun s => ⟨fun i => if i ∈ s.1 then (1 : ZMod 2) else 0, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · rw [hammingNorm_eq_support]
      have : support (fun i : Fin n => if i ∈ s.1 then (1 : ZMod 2) else 0) = s.1 := by
        ext i
        simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases h : i ∈ s.1 <;> simp [h]
      rw [this]; exact s.2
    · intro a
      apply Subtype.ext
      funext i
      by_cases h : a.1 i = 0
      · have hi : i ∉ support a.1 := by simp [support, h]
        simp only [hi, ↓reduceIte, h]
      · have hi : i ∈ support a.1 := by simp [support, h]
        simp only [hi, ↓reduceIte]
        exact (zmod_two_eq_one h).symm
    · intro s
      apply Subtype.ext
      have : support (fun i : Fin n => if i ∈ s.1 then (1 : ZMod 2) else 0) = s.1 := by
        ext i
        simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases h : i ∈ s.1 <;> simp [h]
      simp [this]
  rw [key, Fintype.card_finset_len, Fintype.card_fin]

end Counts

section Ext

variable {n : ℕ}

/-- Restriction of a `B^n`-vector to the coordinate set `S`. -/
def restrict (S : Finset (Fin n)) (a : BVec (Fin n)) : BVec ↥S := fun j => a j

/-- Extension of an `↥S`-vector to `B^n` (zero outside `S`). -/
def extend (S : Finset (Fin n)) (y : BVec ↥S) : BVec (Fin n) :=
  fun j => if h : j ∈ S then y ⟨j, h⟩ else 0

@[simp] lemma restrict_apply (S : Finset (Fin n)) (a : BVec (Fin n)) (j : ↥S) :
    restrict S a j = a j := rfl

lemma support_extend_subset (S : Finset (Fin n)) (y : BVec ↥S) : support (extend S y) ⊆ S := by
  intro i hi
  by_contra hc
  rw [support, Finset.mem_filter] at hi
  exact hi.2 (by rw [extend, dite_eq_right (by exact hc)])

lemma restrict_extend (S : Finset (Fin n)) (y : BVec ↥S) : restrict S (extend S y) = y := by
  funext j; rw [restrict_apply, extend, dite_eq_left j.2]

lemma extend_restrict {S : Finset (Fin n)} {a : BVec (Fin n)} (h : support a ⊆ S) :
    extend S (restrict S a) = a := by
  funext j
  by_cases hj : j ∈ S
  · rw [extend, dite_eq_left hj, restrict_apply]
  · have : a j = 0 := by
      by_contra hc
      exact hj (h (by rw [support, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hc⟩))
    rw [extend, dite_eq_right (by exact hj), this]

lemma card_support_restrict (S : Finset (Fin n)) (a : BVec (Fin n)) :
    (support (restrict S a)).card = (S.filter (fun i => a i ≠ 0)).card := by
  apply Finset.card_bij (fun (j : ↥S) (_ : j ∈ support (restrict S a)) => (j : Fin n))
  · intro j hj
    rw [support, Finset.mem_filter] at hj
    exact Finset.mem_filter.mpr ⟨j.2, hj.2⟩
  · intro j₁ _ j₂ _ h; exact Subtype.ext h
  · intro i hi
    rw [Finset.mem_filter] at hi
    exact ⟨⟨i, hi.1⟩, by rw [support, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi.2⟩, rfl⟩

lemma hammingNorm_restrict_of_subset {S : Finset (Fin n)} {a : BVec (Fin n)}
    (h : support a ⊆ S) : hammingNorm (restrict S a) = hammingNorm a := by
  have hEq : S.filter (fun i => a i ≠ 0) = support a := by
    ext i
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hh => hh.2, fun hh => ⟨h (by simp [support, hh]), hh⟩⟩
  calc hammingNorm (restrict S a) = (support (restrict S a)).card := hammingNorm_eq_support _
    _ = (S.filter (fun i => a i ≠ 0)).card := card_support_restrict S a
    _ = (support a).card := by rw [hEq]
    _ = hammingNorm a := (hammingNorm_eq_support _).symm

lemma interCard_eq_support_inter (a b : BVec ι) :
    interCard a b = (support a ∩ support b).card := by
  rw [interCard]
  congr 1
  ext i; simp [support]

end Ext

section Support2

lemma zmod_two_sub_ne_zero {a b : ZMod 2} :
    a - b ≠ 0 ↔ (a ≠ 0 ∨ b ≠ 0) ∧ ¬(a ≠ 0 ∧ b ≠ 0) := by
  by_cases ha : a = 0
  · subst ha; by_cases hb : b = 0
    · subst hb; simp
    · rw [zmod_two_eq_one hb]; simp
  · by_cases hb : b = 0
    · subst hb; rw [zmod_two_eq_one ha]; simp
    · rw [zmod_two_eq_one ha, zmod_two_eq_one hb]; simp

lemma one_sub_ne_zero {a : ZMod 2} : (1 : ZMod 2) - a ≠ 0 ↔ a = 0 := by
  by_cases ha : a = 0
  · rw [ha]; simp
  · rw [zmod_two_eq_one ha]; simp

lemma support_sub (x y : BVec ι) :
    support (x - y) = (support x ∪ support y) \ (support x ∩ support y) := by
  ext k
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    Finset.mem_union, Finset.mem_inter, Pi.sub_apply]
  exact zmod_two_sub_ne_zero

lemma support_one_sub (y : BVec ι) : support ((1 : BVec ι) - y) = Finset.univ \ support y := by
  ext k
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
    Pi.sub_apply, Pi.one_apply]
  simpa using one_sub_ne_zero (a := y k)

lemma hammingNorm_sub_add (x y : BVec ι) :
    hammingNorm (x - y) + 2 * interCard x y = hammingNorm x + hammingNorm y := by
  rw [hammingNorm_eq_support (x - y), hammingNorm_eq_support x, hammingNorm_eq_support y,
      interCard_eq_support_inter, support_sub x y]
  have hsub : support x ∩ support y ⊆ support x ∪ support y := by
    intro k hk; exact Finset.mem_union_left _ (Finset.mem_inter.mp hk).1
  have hle : (support x ∩ support y).card ≤ (support x ∪ support y).card :=
    Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hsub]
  have hunion := Finset.card_union_add_card_inter (support x) (support y)
  omega

lemma interCard_one_sub (x y : BVec ι) :
    interCard x (1 - y) = hammingNorm x - interCard x y := by
  have hset : support x ∩ support (1 - y) = support x \ support y := by
    rw [support_one_sub]; ext k
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and]
  have h2 : (support x \ support y).card = (support x).card - (support x ∩ support y).card := by
    rw [Finset.card_sdiff, Finset.inter_comm]
  calc interCard x (1 - y)
      = (support x ∩ support (1 - y)).card := interCard_eq_support_inter x (1 - y)
    _ = (support x \ support y).card := by rw [hset]
    _ = (support x).card - (support x ∩ support y).card := h2
    _ = hammingNorm x - interCard x y := by
        rw [hammingNorm_eq_support, interCard_eq_support_inter]

lemma interCard_self_one_sub (x : BVec ι) : interCard x (1 - x) = 0 := by
  rw [interCard_eq_support_inter, support_one_sub]
  apply Finset.card_eq_zero.mpr
  rw [Finset.eq_empty_iff_forall_notMem]
  intro k hk
  rw [Finset.mem_inter, Finset.mem_sdiff] at hk
  exact hk.2.2 hk.1

end Support2

section Family3

/-- The equivalence `↥S ≃ Fin m` induced by `S.card = m`. -/
noncomputable def phiS {n m : ℕ} (S : Finset (Fin n)) (hm : S.card = m) : ↥S ≃ Fin m :=
  (Fintype.equivFin ↥S).trans (finCongr (by rw [Fintype.card_coe, hm]))

end Family3

/-! ## The covering rank `rk∨ Uₙ` and Theorem 2

The paper's *covering rank* `rk∨ Uₙ` is the least number of rectangles (submatrices without a
`0`-entry; intersections of rectangles are allowed) covering all `1`-entries of the disjointness
matrix `Uₙ` (`HasCoverFin`, `coverRank`).  **Theorem 2** states `rk∨ Uₙ ≤ n^{O(1)} (3/2)^n`.

We follow the paper's four-case construction, applied blockwise to the submatrices `Uₙ^{p,q}` of
fixed row weight `p` and column weight `q` (with `p + q ≤ n`, else the block has no `1`-entry):

  * **Case I** (`β ≤ 0.1` or `α ≥ 0.9`): single-row / single-column rectangles,
    `≤ 2^{nH(0.1)}` of them (`blockCover_caseI`);
  * **Case II** (`α ≤ 1/2 ≤ α+β`): the code-based construction of Lemma 2 on the middle layer
    (with `x = α+β−1/2`), then Corollary 2;
  * **Case III** (`α+β ≤ 1/2`): separation of variables, then Corollary 2;
  * **Case IV** (`α ≥ 1/2`): rectangles indexed by *every* outer set `X ⊆ [n]` with `q ≤ |X|`
    together with a 3-code part of `B^X`.  The family covers the block uniformly with degree
    `2^p`, giving `≤ n^{O(1)}·2^{n-p} ≤ n^{O(1)}(3/2)^n` of them (`blockCover_caseIV`).

Summing the block bounds over the `(n+1)²` blocks `(p,q)` with `p + q ≤ n` — via the per-block
bound `blockCover_poly` (which reduces to `p ≥ q` by the transposition symmetry `blockCover_swap`
and dispatches Cases I–IV), the summation lemma `hasCoverFin_of_blocks`, and `coverRank_le` —
yields **`theorem2`**: there are explicit constants with `(rk∨ Uₙ : ℝ) ≤ c (n+1)^d (3/2)^n`
(namely `c = 6`, `d = 7`), the formalised form of the paper's `rk∨ Uₙ ≤ n^{O(1)} (3/2)^n`. -/

/-- `HasBlockCover n p q k`: the `1`-entries of the `(p,q)`-block of `Uₙ` — the disjoint pairs
`(a,b)` with `‖a‖ = p`, `‖b‖ = q` — are covered by `k` rectangles. -/
def HasBlockCover (n p q k : ℕ) : Prop :=
  ∃ R C : Fin k → Finset (BVec (Fin n)),
    (∀ i, IsRectangle (R i) (C i)) ∧
    (∀ a b : BVec (Fin n), hammingNorm a = p → hammingNorm b = q → interCard a b = 0 →
      ∃ i, a ∈ R i ∧ b ∈ C i)

/-- `HasCoverFin n k`: `rk∨ Uₙ ≤ k` — the `1`-entries of `Uₙ` are covered by `k` rectangles
(intersections of rectangles are allowed). -/
def HasCoverFin (n k : ℕ) : Prop :=
  ∃ R C : Fin k → Finset (BVec (Fin n)),
    (∀ i, IsRectangle (R i) (C i)) ∧
    (∀ a b : BVec (Fin n), interCard a b = 0 → ∃ i, a ∈ R i ∧ b ∈ C i)

/-- A partition of the `1`-entries is in particular a covering. -/
lemma hasCoverFin_of_hasPartFin {n k : ℕ} (h : HasPartFin n k) : HasCoverFin n k := by
  obtain ⟨R, C, hrect, hcov, _⟩ := h
  exact ⟨R, C, hrect, fun a b hab => hcov a b hab⟩

/-- Build a covering with `k` rectangles from one indexed by an arbitrary finite type `ι`. -/
lemma hasCoverFin_of_card_eq {n k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = k) (R C : ι → Finset (BVec (Fin n)))
    (hR : ∀ i, IsRectangle (R i) (C i))
    (hCov : ∀ a b : BVec (Fin n), interCard a b = 0 → ∃ i, a ∈ R i ∧ b ∈ C i) :
    HasCoverFin n k := by
  classical
  let e : ι ≃ Fin k := (Fintype.equivFin ι).trans (finCongr hι)
  refine ⟨fun i => R (e.symm i), fun i => C (e.symm i), fun i => hR _, ?_⟩
  intro a b hab
  obtain ⟨i, hi⟩ := hCov a b hab
  exact ⟨e i, by show a ∈ R (e.symm (e i)); rw [Equiv.symm_apply_apply]; exact hi.1,
    by show b ∈ C (e.symm (e i)); rw [Equiv.symm_apply_apply]; exact hi.2⟩

theorem hasCoverFin_exists (n : ℕ) : ∃ k, HasCoverFin n k :=
  ⟨4 ^ n, hasCoverFin_of_hasPartFin (hasPartFin_four n)⟩

/-- The covering rank `rk∨ Uₙ`. -/
noncomputable def coverRank (n : ℕ) : ℕ := by
  classical
  exact Nat.find (p := HasCoverFin n) (hasCoverFin_exists n)

lemma coverRank_le {n k : ℕ} (h : HasCoverFin n k) : coverRank n ≤ k := by
  classical
  exact Nat.find_min' (p := HasCoverFin n) (hasCoverFin_exists n) h

/-- Block indices: pairs `(p,q)` of row/column weights with `p + q ≤ n`. -/
abbrev BlockIdx (n : ℕ) : Type :=
  {pq : Fin (n + 1) × Fin (n + 1) // (pq.1 : ℕ) + (pq.2 : ℕ) ≤ n}

/-- Covering every block of `Uₙ` (block `(p,q)` by `k pq` rectangles) covers `Uₙ` by
`∑ pq, k pq` rectangles. -/
lemma hasCoverFin_of_blocks (n : ℕ) (k : BlockIdx n → ℕ)
    (h : ∀ pq : BlockIdx n, HasBlockCover n (pq.1.1 : ℕ) (pq.1.2 : ℕ) (k pq)) :
    HasCoverFin n (Fintype.card (Σ pq : BlockIdx n, Fin (k pq))) := by
  classical
  choose R C hbody using h
  refine hasCoverFin_of_card_eq rfl (fun i : Σ pq : BlockIdx n, Fin (k pq) => R i.1 i.2)
    (fun i => C i.1 i.2) (fun i => (hbody i.1).1 i.2) ?_
  rintro a b hab
  have hdisj : Disjoint (support a) (support b) := by
    rw [Finset.disjoint_left]
    intro c hca hcb
    rw [support, Finset.mem_filter] at hca hcb
    have hmem : c ∈ Finset.univ.filter (fun i => a i ≠ 0 ∧ b i ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hca.2, hcb.2⟩
    have hpos : 0 < (Finset.univ.filter (fun i => a i ≠ 0 ∧ b i ≠ 0)).card :=
      Finset.card_pos.mpr ⟨c, hmem⟩
    have h0 : (Finset.univ.filter (fun i => a i ≠ 0 ∧ b i ≠ 0)).card = 0 := hab
    omega
  have hle : hammingNorm a + hammingNorm b ≤ n := by
    have h1 : (support a ∪ support b).card = hammingNorm a + hammingNorm b := by
      rw [Finset.card_union_of_disjoint hdisj, hammingNorm_eq_support a, hammingNorm_eq_support b]
    have h2 : (support a ∪ support b).card ≤ n := by
      have h3 := Finset.card_le_card (Finset.subset_univ (support a ∪ support b))
      rwa [Finset.card_univ, Fintype.card_fin] at h3
    omega
  let pq : BlockIdx n :=
    ⟨(⟨hammingNorm a, Nat.lt_succ_of_le (le_trans (Nat.le_add_right _ _) hle)⟩,
      ⟨hammingNorm b, Nat.lt_succ_of_le (le_trans (Nat.le_add_left _ _) hle)⟩),
      by simpa using hle⟩
  obtain ⟨i, hi⟩ := (hbody pq).2 a b rfl rfl hab
  exact ⟨⟨pq, i⟩, hi.1, hi.2⟩

/-! ### Monotonicity of the binary entropy on `[0, 1/2]` -/

lemma H2_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ (2:ℝ)⁻¹) : H2 a ≤ H2 b := by
  have hmono := Real.binEntropy_strictMonoOn.monotoneOn
    (Set.mem_Icc.mpr ⟨ha, le_trans hab hb⟩) (Set.mem_Icc.mpr ⟨le_trans ha hab, hb⟩) hab
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h : Real.log 2 * H2 a ≤ Real.log 2 * H2 b := by rw [log2_mul_H2, log2_mul_H2]; exact hmono
  exact le_of_mul_le_mul_left h hlog

lemma H2_div_le_tenth {n m : ℕ} (hn : 0 < n) (hm : 10 * m ≤ n) :
    H2 ((m:ℝ)/n) ≤ H2 ((1:ℝ)/10) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hle : (m:ℝ)/n ≤ (1:ℝ)/10 := by
    rw [div_le_iff₀ hnR]
    have h10 : (10:ℝ) * (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hm
    linarith
  exact H2_mono (by positivity) hle (by norm_num)

/-! ### An indexed (multiset) form of the greedy covering bound

Cases II–IV below produce families of rectangles indexed by a finite type, in which the same
rectangle may occur several times (a multiset family).  We therefore prove an *indexed* form of
Lemma 3: if `rect : τ → Finset α` has members of size `≤ s` and every `x ∈ α` lies in at least
`r` of the members (counting multiplicity), then some subfamily (a `Finset τ`) of size at most
`(1 + log s) |τ| / r` covers `α`.  Its proof is the potential/greedy argument of Lemma 3,
restated for an indexed family (`maxCovI`, `potI`, …). -/

section IndexedCover

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {τ : Type*} [Fintype τ] [DecidableEq τ] [Nonempty τ]

noncomputable def maxCovI (rect : τ → Finset α) (R : Finset α) : ℕ :=
  Finset.univ.sup (fun i => (rect i ∩ R).card)

lemma maxCovI_le (rect : τ → Finset α) (R : Finset α) (i : τ) :
    (rect i ∩ R).card ≤ maxCovI rect R :=
  Finset.le_sup (f := fun i => (rect i ∩ R).card) (Finset.mem_univ i)

lemma maxCovI_mono (rect : τ → Finset α) {R R' : Finset α} (h : R' ⊆ R) :
    maxCovI rect R' ≤ maxCovI rect R := by
  rw [maxCovI, maxCovI]; apply Finset.sup_le; intro i _
  exact (Finset.card_le_card (Finset.inter_subset_inter Subset.rfl h)).trans
    (Finset.le_sup (f := fun i => (rect i ∩ R).card) (Finset.mem_univ i))

noncomputable def argmaxI (rect : τ → Finset α) (R : Finset α) : τ :=
  Classical.choose (Finset.exists_max_image Finset.univ (fun i => (rect i ∩ R).card)
    Finset.univ_nonempty)

lemma argmaxI_spec (rect : τ → Finset α) (R : Finset α) (i : τ) :
    (rect i ∩ R).card ≤ (rect (argmaxI rect R) ∩ R).card :=
  (Classical.choose_spec (Finset.exists_max_image Finset.univ (fun i => (rect i ∩ R).card)
    Finset.univ_nonempty)).2 i (Finset.mem_univ i)

lemma argmaxI_card (rect : τ → Finset α) (R : Finset α) :
    (rect (argmaxI rect R) ∩ R).card = maxCovI rect R := by
  apply le_antisymm
  · exact maxCovI_le rect R _
  · rw [maxCovI]; exact Finset.sup_le (fun i _ => argmaxI_spec rect R i)

lemma exists_mem_of_degI (rect : τ → Finset α) (r : ℕ) (hr : 1 ≤ r)
    (hdeg : ∀ x : α, r ≤ (Finset.univ.filter (fun i => x ∈ rect i)).card) (x : α) :
    ∃ i, x ∈ rect i := by
  have hpos : 0 < (Finset.univ.filter (fun i => x ∈ rect i)).card := lt_of_lt_of_le hr (hdeg x)
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter] at hi
  exact ⟨i, hi.2⟩

lemma card_le_mul_maxCovI (rect : τ → Finset α) (r : ℕ)
    (hdeg : ∀ x : α, r ≤ (Finset.univ.filter (fun i => x ∈ rect i)).card) (R : Finset α) :
    r * R.card ≤ Fintype.card τ * maxCovI rect R := by
  have h1 : ∑ x ∈ R, r ≤ ∑ x ∈ R, (Finset.univ.filter (fun i => x ∈ rect i)).card :=
    Finset.sum_le_sum (fun x _ => hdeg x)
  have h2 : ∑ x ∈ R, (Finset.univ.filter (fun i => x ∈ rect i)).card = ∑ i, (rect i ∩ R).card := by
    simp only [Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.card_filter (fun x => x ∈ rect i) R, Finset.filter_mem_eq_inter, Finset.inter_comm]
  have h3 : ∑ i, (rect i ∩ R).card ≤ ∑ _i : τ, maxCovI rect R :=
    Finset.sum_le_sum (fun i _ => maxCovI_le rect R i)
  calc r * R.card = R.card * r := Nat.mul_comm r R.card
    _ = ∑ _x ∈ R, r := by rw [Finset.sum_const, nsmul_eq_mul]; simp
    _ ≤ ∑ x ∈ R, (Finset.univ.filter (fun i => x ∈ rect i)).card := h1
    _ = ∑ i, (rect i ∩ R).card := h2
    _ ≤ ∑ _i : τ, maxCovI rect R := h3
    _ = Fintype.card τ * maxCovI rect R := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; simp

lemma one_le_maxCovI (rect : τ → Finset α) (r : ℕ) (hr : 1 ≤ r)
    (hdeg : ∀ x : α, r ≤ (Finset.univ.filter (fun i => x ∈ rect i)).card) {R : Finset α}
    (hR : R ≠ ∅) : 1 ≤ maxCovI rect R := by
  obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hR
  obtain ⟨i, hxi⟩ := exists_mem_of_degI rect r hr hdeg x₀
  have : 1 ≤ (rect i ∩ R).card := Finset.card_pos.mpr ⟨x₀, Finset.mem_inter.mpr ⟨hxi, hx₀⟩⟩
  exact this.trans (maxCovI_le rect R i)

lemma div_bound {N r c m : ℕ} (hr : 0 < r) (h : r * N ≤ c * m) :
    (N : ℝ) ≤ ((c : ℝ)/r) * (m : ℝ) := by
  have hr' : (0:ℝ) < r := by exact_mod_cast hr
  have hh : (r:ℝ) * (N:ℝ) ≤ (c:ℝ) * (m:ℝ) := by exact_mod_cast h
  rw [div_mul_eq_mul_div, le_div_iff₀ hr']; linarith

noncomputable def potI (rect : τ → Finset α) (a : ℝ) (R : Finset α) : ℝ :=
  if R = ∅ then 0 else a * Udisj.H (maxCovI rect R) + (R.card : ℝ)/(maxCovI rect R) - a

lemma potI_empty (rect : τ → Finset α) (a : ℝ) : potI rect a ∅ = 0 := by simp [potI]

lemma potI_of_ne (rect : τ → Finset α) {a : ℝ} {R : Finset α} (hR : R ≠ ∅) :
    potI rect a R = a * Udisj.H (maxCovI rect R) + (R.card : ℝ)/(maxCovI rect R) - a := by
  rw [potI, ite_eq_right hR]

lemma potI_step (rect : τ → Finset α) (r : ℕ) (hr : 1 ≤ r)
    (hdeg : ∀ x : α, r ≤ (Finset.univ.filter (fun i => x ∈ rect i)).card)
    {R : Finset α} (hR : R ≠ ∅) :
    potI rect ((Fintype.card τ : ℝ)/r) R
      - potI rect ((Fintype.card τ : ℝ)/r) (R \ rect (argmaxI rect R)) ≥ 1 := by
  classical
  set a : ℝ := (Fintype.card τ : ℝ)/r with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hcov0 : (0:ℝ) < (maxCovI rect R : ℝ) := by
    have := one_le_maxCovI rect r hr hdeg hR; positivity
  have hH1 : 1 ≤ Udisj.H (maxCovI rect R) := by
    have := Udisj.H_mono (one_le_maxCovI rect r hr hdeg hR); rwa [Udisj.H_one] at this
  have hkeyR : (R.card : ℝ) ≤ a * (maxCovI rect R : ℝ) := by
    rw [ha]; exact div_bound (lt_of_lt_of_le Nat.zero_lt_one hr) (card_le_mul_maxCovI rect r hdeg R)
  by_cases hR'e : R \ rect (argmaxI rect R) = ∅
  · have hsubF : R ⊆ rect (argmaxI rect R) := by
      intro x hx; by_contra hxF
      have hmem : x ∈ R \ rect (argmaxI rect R) := Finset.mem_sdiff.mpr ⟨hx, hxF⟩
      rw [hR'e] at hmem; exact absurd hmem (by simp)
    have hcovR : maxCovI rect R = R.card := by
      rw [← argmaxI_card rect R]
      apply le_antisymm
      · exact Finset.card_le_card (Finset.inter_subset_right)
      · exact Finset.card_le_card (fun x hx => Finset.mem_inter.mpr ⟨hsubF hx, hx⟩)
    have hc : (R.card : ℝ) ≠ 0 := by
      rw [Nat.cast_ne_zero]; exact Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hR)
    rw [hR'e, potI_empty, potI_of_ne rect hR]
    rw [hcovR] at hH1 ⊢
    rw [div_self hc]
    nlinarith [ha0, hH1]
  · have hmono : maxCovI rect (R \ rect (argmaxI rect R)) ≤ maxCovI rect R :=
      maxCovI_mono rect Finset.sdiff_subset
    have hcov'1 : 1 ≤ maxCovI rect (R \ rect (argmaxI rect R)) :=
      one_le_maxCovI rect r hr hdeg hR'e
    have hcov'0 : (0:ℝ) < (maxCovI rect (R \ rect (argmaxI rect R)) : ℝ) := by positivity
    have hkeyR' : ((R \ rect (argmaxI rect R)).card : ℝ)
        ≤ a * (maxCovI rect (R \ rect (argmaxI rect R)) : ℝ) := by
      rw [ha]; exact div_bound (lt_of_lt_of_le Nat.zero_lt_one hr)
        (card_le_mul_maxCovI rect r hdeg (R \ rect (argmaxI rect R)))
    have hrc : (R.card : ℝ) = ((R \ rect (argmaxI rect R)).card : ℝ) + (maxCovI rect R : ℝ) := by
      have h := Finset.card_sdiff_add_card_inter R (rect (argmaxI rect R))
      rw [Finset.inter_comm, argmaxI_card rect R] at h
      rw [← h]; push_cast; ring
    have hcore : a*(Udisj.H (maxCovI rect R) - Udisj.H (maxCovI rect (R \ rect (argmaxI rect R))))
        + ((R \ rect (argmaxI rect R)).card : ℝ)*(1/(maxCovI rect R : ℝ) - 1/(maxCovI rect (R \ rect (argmaxI rect R)) : ℝ)) ≥ 0 := by
      have hcast : ((maxCovI rect R - maxCovI rect (R \ rect (argmaxI rect R)) : ℕ) : ℝ)
          = (maxCovI rect R : ℝ) - (maxCovI rect (R \ rect (argmaxI rect R)) : ℝ) := Nat.cast_sub hmono
      have hsubH : ((maxCovI rect R - maxCovI rect (R \ rect (argmaxI rect R)) : ℕ) : ℝ)/(maxCovI rect R : ℝ)
          ≤ Udisj.H (maxCovI rect R) - Udisj.H (maxCovI rect (R \ rect (argmaxI rect R))) := Udisj.H_sub_ge hmono
      have hA : a * (Udisj.H (maxCovI rect R) - Udisj.H (maxCovI rect (R \ rect (argmaxI rect R))))
          ≥ a * (((maxCovI rect R : ℝ) - (maxCovI rect (R \ rect (argmaxI rect R)) : ℝ))/(maxCovI rect R : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ ha0
        rw [← hcast]; exact hsubH
      have hneg : 1/(maxCovI rect R : ℝ) - 1/(maxCovI rect (R \ rect (argmaxI rect R)) : ℝ) ≤ 0 := by
        rw [sub_nonpos]
        exact one_div_le_one_div_of_le hcov'0 (by exact_mod_cast hmono)
      have hmul : ((R \ rect (argmaxI rect R)).card : ℝ)*(1/(maxCovI rect R : ℝ) - 1/(maxCovI rect (R \ rect (argmaxI rect R)) : ℝ))
          ≥ (a*(maxCovI rect (R \ rect (argmaxI rect R)) : ℝ))*(1/(maxCovI rect R : ℝ) - 1/(maxCovI rect (R \ rect (argmaxI rect R)) : ℝ)) :=
        mul_le_mul_of_nonpos_right hkeyR' hneg
      have hval : (a*(maxCovI rect (R \ rect (argmaxI rect R)) : ℝ))*(1/(maxCovI rect R : ℝ) - 1/(maxCovI rect (R \ rect (argmaxI rect R)) : ℝ))
          = -(a*(((maxCovI rect R : ℝ) - (maxCovI rect (R \ rect (argmaxI rect R)) : ℝ))/(maxCovI rect R : ℝ))) := by
        field_simp; ring
      linarith [hA, hmul, hval]
    rw [potI_of_ne rect hR, potI_of_ne rect hR'e, hrc]
    have key : a * Udisj.H (maxCovI rect R) + ((((R \ rect (argmaxI rect R)).card:ℝ) + (maxCovI rect R : ℝ))/(maxCovI rect R : ℝ)) - a
          - (a * Udisj.H (maxCovI rect (R \ rect (argmaxI rect R))) + ((R \ rect (argmaxI rect R)).card:ℝ)/(maxCovI rect (R \ rect (argmaxI rect R)) : ℝ) - a)
        = a*(Udisj.H (maxCovI rect R) - Udisj.H (maxCovI rect (R \ rect (argmaxI rect R))))
          + ((R \ rect (argmaxI rect R)).card:ℝ)*(1/(maxCovI rect R : ℝ) - 1/(maxCovI rect (R \ rect (argmaxI rect R)) : ℝ)) + 1 := by
      field_simp; ring
    rw [key]; linarith [hcore]

lemma potI_univ_le (rect : τ → Finset α) (r s : ℕ) (hr : 1 ≤ r)
    (hdeg : ∀ x : α, r ≤ (Finset.univ.filter (fun i => x ∈ rect i)).card)
    (hsize : ∀ i, (rect i).card ≤ s) :
    potI rect ((Fintype.card τ : ℝ)/r) (Finset.univ : Finset α)
      ≤ (1 + Real.log s) * (Fintype.card τ : ℝ)/r := by
  classical
  have hs0 : (0:ℝ) ≤ 1 + Real.log (s:ℝ) := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp
    · have h1 : (1:ℝ) ≤ s := by exact_mod_cast h
      have := Real.log_nonneg h1; linarith
  by_cases hX : (Finset.univ : Finset α) = ∅
  · rw [hX, potI_empty]
    exact mul_nonneg (mul_nonneg hs0 (by positivity)) (by positivity)
  · obtain ⟨x₀, -⟩ := Finset.nonempty_iff_ne_empty.mpr hX
    obtain ⟨i₀, -⟩ := exists_mem_of_degI rect r hr hdeg x₀
    have hcov1 : 1 ≤ maxCovI rect (Finset.univ : Finset α) := one_le_maxCovI rect r hr hdeg hX
    have hcovs : maxCovI rect (Finset.univ : Finset α) ≤ s := by
      rw [maxCovI]; apply Finset.sup_le; intro i _
      rw [Finset.inter_univ]; exact hsize i
    have hkey : ((Finset.univ : Finset α).card : ℝ)
        ≤ ((Fintype.card τ : ℝ)/r) * (maxCovI rect (Finset.univ : Finset α) : ℝ) :=
      div_bound (lt_of_lt_of_le Nat.zero_lt_one hr) (card_le_mul_maxCovI rect r hdeg Finset.univ)
    have hlogmono : Real.log (maxCovI rect (Finset.univ : Finset α) : ℝ) ≤ Real.log (s:ℝ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast hcovs)
    have hHle : Udisj.H (maxCovI rect (Finset.univ : Finset α)) ≤ 1 + Real.log (s:ℝ) :=
      (Udisj.H_le_one_add_log _).trans (by linarith)
    have hcov0 : (0:ℝ) < (maxCovI rect (Finset.univ : Finset α) : ℝ) := by positivity
    have hdiv : ((Finset.univ : Finset α).card : ℝ)/(maxCovI rect (Finset.univ : Finset α) : ℝ)
        ≤ (Fintype.card τ : ℝ)/r := by
      rw [div_le_iff₀ hcov0]; exact hkey
    rw [potI_of_ne rect hX]
    have ha0 : 0 ≤ (Fintype.card τ : ℝ)/r := by positivity
    have h1b := mul_le_mul_of_nonneg_left hHle ha0
    have htgt : (Fintype.card τ : ℝ)/r * (1 + Real.log (s:ℝ))
        = (1 + Real.log s) * (Fintype.card τ : ℝ)/r := by ring
    linarith [h1b, hdiv, htgt]

lemma cover_existsI (rect : τ → Finset α) (r : ℕ) (hr : 1 ≤ r)
    (hdeg : ∀ x : α, r ≤ (Finset.univ.filter (fun i => x ∈ rect i)).card) :
    ∀ R : Finset α, ∃ I : Finset τ, (∀ x ∈ R, ∃ i ∈ I, x ∈ rect i) ∧
      (I.card : ℝ) ≤ potI rect ((Fintype.card τ : ℝ)/r) R := by
  intro R
  refine Finset.strongInductionOn R ?_
  intro R ih
  by_cases hR : R = ∅
  · exact ⟨∅, by intro x hx; rw [hR] at hx; exact absurd hx (by simp), by simp [hR, potI]⟩
  · have hcov1 : 1 ≤ (rect (argmaxI rect R) ∩ R).card := by
      rw [argmaxI_card]; exact one_le_maxCovI rect r hr hdeg hR
    have hssub : R \ rect (argmaxI rect R) ⊂ R := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.sdiff_subset, ?_⟩
      intro heq
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hcov1
      rw [Finset.mem_inter] at hx
      have hmem : x ∈ R \ rect (argmaxI rect R) := by rw [heq]; exact hx.2
      rw [Finset.mem_sdiff] at hmem; exact hmem.2 hx.1
    obtain ⟨I', hI'cov, hI'card⟩ := ih (R \ rect (argmaxI rect R)) hssub
    refine ⟨insert (argmaxI rect R) I', ?_, ?_⟩
    · intro x hx
      by_cases hxF : x ∈ rect (argmaxI rect R)
      · exact ⟨argmaxI rect R, Finset.mem_insert_self _ _, hxF⟩
      · obtain ⟨i, hi, hxi⟩ := hI'cov x (Finset.mem_sdiff.mpr ⟨hx, hxF⟩)
        exact ⟨i, Finset.mem_insert_of_mem hi, hxi⟩
    · have hstep := potI_step rect r hr hdeg hR
      have h2 : ((I'.card : ℝ) + 1) ≤ potI rect ((Fintype.card τ : ℝ)/r) R := by
        linarith [hI'card, hstep]
      calc ((insert (argmaxI rect R) I').card : ℝ) ≤ ((I'.card + 1 : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_insert_le (argmaxI rect R) I'
        _ = (I'.card : ℝ) + 1 := by push_cast; ring
        _ ≤ potI rect ((Fintype.card τ : ℝ)/r) R := h2

/-- **Indexed Lemma 3.** (Sapozhenko-Lovasz-Stein)  If the indexed family `rect : τ → Finset α` has members of size `≤ s`
and every `x ∈ α` lies in at least `r ≥ 1` members (counting multiplicity), then some subfamily
(a `Finset τ`) of size at most `(1 + log s) |τ| / r` covers `α`. -/
theorem lemma3_indexed (rect : τ → Finset α) (r s : ℕ) (hr : 1 ≤ r)
    (hsize : ∀ i, (rect i).card ≤ s)
    (hdeg : ∀ x : α, r ≤ (Finset.univ.filter (fun i => x ∈ rect i)).card) :
    ∃ I : Finset τ, (∀ x : α, ∃ i ∈ I, x ∈ rect i) ∧
      (I.card : ℝ) ≤ (1 + Real.log s) * (Fintype.card τ : ℝ)/r := by
  obtain ⟨I, hIcov, hIcard⟩ := cover_existsI rect r hr hdeg (Finset.univ : Finset α)
  exact ⟨I, fun x => hIcov x (Finset.mem_univ x),
    hIcard.trans (potI_univ_le rect r s hr hdeg hsize)⟩

end IndexedCover

/-! ### Case I: single-row / single-column rectangles -/

/-- Build a block covering with `k` rectangles from one indexed by an arbitrary finite type. -/
lemma hasBlockCover_of_card_eq {n p q k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : Fintype.card ι = k) (R C : ι → Finset (BVec (Fin n)))
    (hR : ∀ i, IsRectangle (R i) (C i))
    (hCov : ∀ a b : BVec (Fin n), hammingNorm a = p → hammingNorm b = q → interCard a b = 0 →
      ∃ i, a ∈ R i ∧ b ∈ C i) :
    HasBlockCover n p q k := by
  classical
  let e : ι ≃ Fin k := (Fintype.equivFin ι).trans (finCongr hι)
  refine ⟨fun i => R (e.symm i), fun i => C (e.symm i), fun i => hR _, ?_⟩
  intro a b ha hb hab
  obtain ⟨i, hi⟩ := hCov a b ha hb hab
  exact ⟨e i, by show a ∈ R (e.symm (e i)); rw [Equiv.symm_apply_apply]; exact hi.1,
    by show b ∈ C (e.symm (e i)); rw [Equiv.symm_apply_apply]; exact hi.2⟩

/-- The `(p,q)` block is covered by the `C(n,p)` single-row rectangles. -/
lemma blockCover_of_rows (n p q : ℕ) : HasBlockCover n p q (n.choose p) := by
  classical
  refine hasBlockCover_of_card_eq (card_weight_eq_choose n p)
    (fun a : {a : BVec (Fin n) // hammingNorm a = p} => {a.1})
    (fun a => Finset.univ.filter (fun b => hammingNorm b = q ∧ interCard a.1 b ≠ 1)) ?_ ?_
  · intro i x hx y hy
    simp only [Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [hx]; exact hy.2
  · intro a b ha hb hab
    refine ⟨⟨a, ha⟩, ?_, ?_⟩
    · rw [Finset.mem_singleton]
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hb, by rw [hab]; norm_num⟩

/-- The `(p,q)` block is covered by the `C(n,q)` single-column rectangles. -/
lemma blockCover_of_cols (n p q : ℕ) : HasBlockCover n p q (n.choose q) := by
  classical
  refine hasBlockCover_of_card_eq (card_weight_eq_choose n q)
    (fun b : {b : BVec (Fin n) // hammingNorm b = q} =>
      Finset.univ.filter (fun a => hammingNorm a = p ∧ interCard a b.1 ≠ 1))
    (fun b => {b.1}) ?_ ?_
  · intro i x hx y hy
    simp only [Finset.mem_singleton] at hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [hy]; exact hx.2
  · intro a b ha hb hab
    refine ⟨⟨b, hb⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ha, by rw [hab]; norm_num⟩
    · rw [Finset.mem_singleton]

/-- **Case I.**  If `10 q ≤ n` or `10 (n - p) ≤ n` (the paper's `β ≤ 0.1` or `α ≥ 0.9`), the
`(p,q)` block is covered by at most `2^{n H(1/10)}` rectangles. -/
lemma blockCover_caseI (n p q : ℕ) (hn : 0 < n) (hpq : p + q ≤ n)
    (hcond : 10 * q ≤ n ∨ 10 * (n - p) ≤ n) :
    ∃ k, HasBlockCover n p q k ∧ (k : ℝ) ≤ (2:ℝ)^((n:ℝ) * H2 ((1:ℝ)/10)) := by
  rcases hcond with hq | hp
  · refine ⟨n.choose q, blockCover_of_cols n p q, ?_⟩
    calc (n.choose q : ℝ) ≤ (2:ℝ)^((n:ℝ) * H2 ((q:ℝ)/n)) :=
          choose_le_two_pow_H2 n q (by omega)
      _ ≤ (2:ℝ)^((n:ℝ) * H2 ((1:ℝ)/10)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
          exact mul_le_mul_of_nonneg_left (H2_div_le_tenth hn hq) (Nat.cast_nonneg n)
  · refine ⟨n.choose p, blockCover_of_rows n p q, ?_⟩
    have hp' : p ≤ n := by omega
    calc (n.choose p : ℝ) = (n.choose (n - p) : ℝ) := by rw [Nat.choose_symm hp']
      _ ≤ (2:ℝ)^((n:ℝ) * H2 (((n - p : ℕ):ℝ)/n)) :=
          choose_le_two_pow_H2 n (n - p) (by omega)
      _ ≤ (2:ℝ)^((n:ℝ) * H2 ((1:ℝ)/10)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
          exact mul_le_mul_of_nonneg_left (H2_div_le_tenth hn hp) (Nat.cast_nonneg n)

/-! ### Case III: separation of variables

Here `2(p+q) ≤ n`.  The family of *all* subsets `S ⊆ [n]` gives rectangle
`rectRow n p S × rectCol n q S` (`p`-vectors supported in `S`, `q`-vectors supported in its
complement).  It is legal (`IsRectangle`) for every `S`, covers every `1`-entry, and — crucially —
indexing by *all* `2^n` subsets makes the coverage exactly uniform with degree `r = 2^{n-p-q}`:
so `|τ|/r = 2^n/2^{n-p-q} = 2^{p+q}` exactly, and the indexed Lemma 3 gives a cover of size
`≤ (1 + n log 2) · 2^{p+q}` — no entropy optimisation or rounding needed. -/

section CaseIII

/-- The `1`-entries of the `(p,q)`-block, as a finite type. -/
abbrev BlockEntries (n p q : ℕ) : Type :=
  {ab : BVec (Fin n) × BVec (Fin n) //
    hammingNorm ab.1 = p ∧ hammingNorm ab.2 = q ∧ interCard ab.1 ab.2 = 0}

lemma card_finset_fin (n : ℕ) : Fintype.card (Finset (Fin n)) = 2 ^ n := by
  rw [Fintype.card_finset, Fintype.card_fin]

/-- Boolean vectors supported in `S` number `2^{|S|}`. -/
lemma card_support_subset (n : ℕ) (S : Finset (Fin n)) :
    Fintype.card {a : BVec (Fin n) // support a ⊆ S} = 2 ^ S.card := by
  have e : {a : BVec (Fin n) // support a ⊆ S} ≃ BVec ↥S :=
    { toFun := fun a => restrict S a.1
      invFun := fun y => ⟨extend S y, support_extend_subset S y⟩
      left_inv := fun a => Subtype.ext (extend_restrict a.2)
      right_inv := fun y => restrict_extend S y }
  rw [Fintype.card_congr e, card_BVec, Fintype.card_coe]

lemma disjoint_support_iff (n : ℕ) (S : Finset (Fin n)) (b : BVec (Fin n)) :
    Disjoint (support b) S ↔ support b ⊆ Finset.univ \ S := by
  constructor
  · intro h i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, Finset.disjoint_left.mp h hi⟩
  · intro h
    rw [Finset.disjoint_left]
    intro i hi hiS
    exact (Finset.mem_sdiff.mp (h hi)).2 hiS

/-- Boolean vectors whose support is disjoint from `S` number `2^{n-|S|}`. -/
lemma eq_of_support_eq {n : ℕ} {v w : BVec (Fin n)} (h : support v = support w) : v = w := by
  funext i
  have hiff : v i ≠ 0 ↔ w i ≠ 0 := by
    have hh := h
    rw [support, support] at hh
    have : i ∈ Finset.univ.filter (fun j => v j ≠ 0) ↔ i ∈ Finset.univ.filter (fun j => w j ≠ 0) := by
      rw [hh]
    simpa using this
  by_cases hv : v i = 0
  · rw [hv]
    by_contra hw
    exact (hiff.mpr (fun h => hw h.symm)) hv
  · rw [zmod_two_eq_one hv, zmod_two_eq_one (hiff.mp hv)]

lemma card_disjoint_support (n : ℕ) (S : Finset (Fin n)) :
    Fintype.card {b : BVec (Fin n) // Disjoint (support b) S} = 2 ^ (n - S.card) := by
  have h : Fintype.card {b : BVec (Fin n) // Disjoint (support b) S}
      = Fintype.card {b : BVec (Fin n) // support b ⊆ Finset.univ \ S} :=
    Fintype.card_congr
      { toFun := fun b => ⟨b.1, (disjoint_support_iff n S b.1).mp b.2⟩
        invFun := fun b => ⟨b.1, (disjoint_support_iff n S b.1).mpr b.2⟩
        left_inv := fun b => Subtype.ext rfl
        right_inv := fun b => Subtype.ext rfl }
  rw [h, card_support_subset n (Finset.univ \ S),
    Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, Fintype.card_fin]

/-- Rows of the rectangle indexed by `S`: weight-`p` vectors supported in `S`. -/
noncomputable def rectRow (n p : ℕ) (S : Finset (Fin n)) : Finset (BVec (Fin n)) :=
  Finset.univ.filter (fun a => hammingNorm a = p ∧ support a ⊆ S)

/-- Columns: weight-`q` vectors supported in the complement of `S`. -/
noncomputable def rectCol (n q : ℕ) (S : Finset (Fin n)) : Finset (BVec (Fin n)) :=
  Finset.univ.filter (fun b => hammingNorm b = q ∧ Disjoint (support b) S)

lemma rectRow_isRect (n p q : ℕ) (S : Finset (Fin n)) :
    IsRectangle (rectRow n p S) (rectCol n q S) := by
  intro a ha b hb
  rw [rectRow, Finset.mem_filter] at ha
  rw [rectCol, Finset.mem_filter] at hb
  rw [interCard_eq_support_inter]
  have hempty : support a ∩ support b = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    rw [Finset.mem_inter] at hi
    exact (Finset.disjoint_left.mp hb.2.2) hi.2 (ha.2.2 hi.1)
  rw [hempty]; norm_num

/-- **Case III.**  For every `p,q` the `(p,q)` block is covered by at most
`(1 + n log 2) · 2^{p+q}` rectangles.  (When `2(p+q) ≤ n` this is `≤ (1 + n log 2) 2^{n/2}`.) -/
lemma blockCover_caseIII (n p q : ℕ) (hpq : p + q ≤ n) :
    ∃ k, HasBlockCover n p q k ∧
      (k : ℝ) ≤ (1 + (n:ℝ) * Real.log 2) * (2:ℝ)^(p + q) := by
  classical
  have hr : 1 ≤ 2 ^ (n - p - q) := Nat.one_le_two_pow
  have hsize : ∀ S : Finset (Fin n), (Finset.univ.filter (fun ab : BlockEntries n p q =>
      support ab.1.1 ⊆ S ∧ Disjoint (support ab.1.2) S)).card ≤ 2 ^ n := by
    intro S
    have h1 : (Finset.univ.filter (fun ab : BlockEntries n p q =>
        support ab.1.1 ⊆ S ∧ Disjoint (support ab.1.2) S)).card
        ≤ Fintype.card {a : BVec (Fin n) // support a ⊆ S} *
          Fintype.card {b : BVec (Fin n) // Disjoint (support b) S} := by
      rw [← Fintype.card_subtype (fun ab : BlockEntries n p q =>
        support ab.1.1 ⊆ S ∧ Disjoint (support ab.1.2) S)]
      rw [← Fintype.card_prod]
      apply Fintype.card_le_of_injective
        (fun ab : {ab : BlockEntries n p q //
            support ab.1.1 ⊆ S ∧ Disjoint (support ab.1.2) S} =>
          (⟨ab.1.1.1, ab.2.1⟩, ⟨ab.1.1.2, ab.2.2⟩))
      intro a b h
      have hf : a.1.1.1 = b.1.1.1 := congrArg (fun x => x.1.1) h
      have hs : a.1.1.2 = b.1.1.2 := congrArg (fun x => x.2.1) h
      exact Subtype.ext (Subtype.ext (Prod.ext hf hs))
    rw [card_support_subset n S, card_disjoint_support n S] at h1
    calc _ ≤ 2 ^ S.card * 2 ^ (n - S.card) := h1
      _ = 2 ^ n := by
          rw [← pow_add]; congr 1
          have h := Finset.card_le_univ S
          simp only [Fintype.card_fin] at h
          omega
  have hdeg : ∀ ab : BlockEntries n p q, 2 ^ (n - p - q) ≤
      (Finset.univ.filter (fun S : Finset (Fin n) => ab ∈ Finset.univ.filter
        (fun ab' : BlockEntries n p q =>
          support ab'.1.1 ⊆ S ∧ Disjoint (support ab'.1.2) S))).card := by
    intro ab
    have ha : hammingNorm ab.1.1 = p := ab.2.1
    have hb : hammingNorm ab.1.2 = q := ab.2.2.1
    have hab : interCard ab.1.1 ab.1.2 = 0 := ab.2.2.2
    have hdisj : Disjoint (support ab.1.1) (support ab.1.2) := by
      rw [Finset.disjoint_left]
      intro i hia hib
      rw [support, Finset.mem_filter] at hia hib
      have hmem : i ∈ Finset.univ.filter (fun k => ab.1.1 k ≠ 0 ∧ ab.1.2 k ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hia.2, hib.2⟩
      have hpos : 0 < (Finset.univ.filter (fun k => ab.1.1 k ≠ 0 ∧ ab.1.2 k ≠ 0)).card :=
        Finset.card_pos.mpr ⟨i, hmem⟩
      have h0 : (Finset.univ.filter (fun k => ab.1.1 k ≠ 0 ∧ ab.1.2 k ≠ 0)).card = 0 := hab
      omega
    set T := Finset.univ \ (support ab.1.1 ∪ support ab.1.2) with hT
    have hcardT : T.card = n - p - q := by
      have hU : (support ab.1.1 ∪ support ab.1.2).card = p + q := by
        rw [Finset.card_union_of_disjoint hdisj, ← hammingNorm_eq_support ab.1.1,
          ← hammingNorm_eq_support ab.1.2, ha, hb]
      rw [hT, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        Fintype.card_fin, hU]
      exact (Nat.sub_sub n p q).symm
    have hle : 2 ^ (n - p - q) ≤ (Finset.univ.filter (fun S : Finset (Fin n) =>
        ab ∈ Finset.univ.filter (fun ab' : BlockEntries n p q =>
          support ab'.1.1 ⊆ S ∧ Disjoint (support ab'.1.2) S))).card := by
      have hPs : Fintype.card {S : Finset (Fin n) // ab ∈ Finset.univ.filter
          (fun ab' : BlockEntries n p q =>
            support ab'.1.1 ⊆ S ∧ Disjoint (support ab'.1.2) S)}
          = (Finset.univ.filter (fun S : Finset (Fin n) => ab ∈ Finset.univ.filter
            (fun ab' : BlockEntries n p q =>
              support ab'.1.1 ⊆ S ∧ Disjoint (support ab'.1.2) S))).card :=
        Fintype.card_subtype _
      rw [← hPs]
      have hinj := Fintype.card_le_of_injective
        (fun W : {W : BVec (Fin n) // support W ⊆ T} =>
          (⟨support ab.1.1 ∪ support W.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            Finset.subset_union_left, by
              rw [Finset.disjoint_left]
              intro i hib hi
              rw [Finset.mem_union] at hi
              rcases hi with hi | hi
              · exact (Finset.disjoint_left.mp hdisj) hi hib
              · exact (Finset.mem_sdiff.mp (W.2 hi)).2 (Finset.mem_union.mpr (Or.inr hib))⟩⟩ :
            {S : Finset (Fin n) // ab ∈ Finset.univ.filter
              (fun ab' : BlockEntries n p q =>
                support ab'.1.1 ⊆ S ∧ Disjoint (support ab'.1.2) S)}))
        (fun W W' h => by
          have hh : support ab.1.1 ∪ support W.1 = support ab.1.1 ∪ support W'.1 :=
            congrArg Subtype.val h
          have hsub : support W.1 = support W'.1 := by
            ext i
            constructor
            · intro hi
              have hm : i ∈ support ab.1.1 ∪ support W.1 := Finset.mem_union.mpr (Or.inr hi)
              rw [hh, Finset.mem_union] at hm
              rcases hm with hA | hW
              · exfalso; exact (Finset.mem_sdiff.mp (W.2 hi)).2 (Finset.mem_union.mpr (Or.inl hA))
              · exact hW
            · intro hi
              have hm : i ∈ support ab.1.1 ∪ support W'.1 := Finset.mem_union.mpr (Or.inr hi)
              rw [← hh, Finset.mem_union] at hm
              rcases hm with hA | hW
              · exfalso; exact (Finset.mem_sdiff.mp (W'.2 hi)).2 (Finset.mem_union.mpr (Or.inl hA))
              · exact hW
          exact Subtype.ext (eq_of_support_eq hsub))
      rw [card_support_subset n T, hcardT] at hinj
      exact hinj
    exact hle
  obtain ⟨I, hIcov, hIcard⟩ := lemma3_indexed (fun S : Finset (Fin n) =>
      Finset.univ.filter (fun ab : BlockEntries n p q =>
        support ab.1.1 ⊆ S ∧ Disjoint (support ab.1.2) S)) (2 ^ (n - p - q)) (2 ^ n) hr hsize hdeg
  have hcover : HasBlockCover n p q I.card := by
    refine hasBlockCover_of_card_eq (k := I.card) (ι := {S : Finset (Fin n) // S ∈ I})
      (by rw [Fintype.card_subtype, Finset.filter_mem_eq_inter, Finset.univ_inter])
      (fun Si => rectRow n p Si.1) (fun Si => rectCol n q Si.1)
      (fun Si => rectRow_isRect n p q Si.1) ?_
    intro a b ha hb hab
    obtain ⟨S, hSI, hS⟩ := hIcov ⟨(a, b), ha, hb, hab⟩
    rw [Finset.mem_filter] at hS
    exact ⟨⟨S, hSI⟩, by
      rw [rectRow, Finset.mem_filter]; exact ⟨Finset.mem_univ _, ha, hS.2.1⟩, by
      rw [rectCol, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hb, hS.2.2⟩⟩
  refine ⟨I.card, hcover, ?_⟩
  have hlog : Real.log ((2:ℝ)^n) = (n:ℝ) * Real.log 2 := Real.log_pow 2 n
  have hn : n = (n - p - q) + (p + q) := by omega
  have hA : (2:ℝ)^n = (2:ℝ)^(n-p-q) * (2:ℝ)^(p+q) := by
    conv_lhs => rw [hn]
    rw [pow_add]
  have hpow : (2:ℝ)^n / (2:ℝ)^(n-p-q) = (2:ℝ)^(p+q) := by
    rw [div_eq_iff (pow_ne_zero _ (by norm_num : (2:ℝ) ≠ 0)), hA]
    ring
  rw [card_finset_fin] at hIcard
  push_cast at hIcard
  rw [hlog, mul_div_assoc, hpow] at hIcard
  exact hIcard

end CaseIII

/-! ### Case II: middle-layer code covering

Assume `2p ≤ n`, `2q ≤ n` and `n + 1 ≤ 2(p+q)`; set `M = 2p+2q-n ≥ 1` (the middle-layer size) and
`h = ⌈M/2⌉ = (M+1)/2`.  For each partition `[n] = X₀ ⊔ X₁ ⊔ X₂` with `|X₀| = M`, `|X₁| = n-2q`
(hence `|X₂| = n-2p`) and each code part `i` of the cube `B^{X₀}` (Lemma 2), the rectangle
`R_{X₀,X₁,i} × C_{X₀,X₁,i}` has as rows the `p`-vectors whose `X₀`-part is an `h`-subset lying in
code part `i`, and as columns the `q`-vectors whose `X₀`-part is the complement of an `h`-subset
lying in code part `i`.

The certificate map `IICert → {x // x covers}` (`iiCertInv`) is injective (`iiCertInv_injective`),
so the family covers *uniformly* with degree `r = IIDeg n p q = C(p,h) C(q,M-h) C(n-p-q, n-2q-p+h)`
(`iiDeg_lower`).  Writing `U = C(n,p) C(n-p,q) ≤ 3^n` (`U_le_three_pow`) and
`Q = C(M,h) C(n-2q,p-h) C(n-2p,q-M+h) ≥ 2^n/(n+1)^3` (all three factors central, `two_pow_le_central`),
the multinomial identity `C(n,M) C(n-M,n-2q) · Q = r · U` (`ii_Q_identity`) gives
`|IIIdx|/r = 2M·U/Q ≤ 2M (n+1)^3 (3/2)^n` (`ii_ratio_bound`).  Applying the indexed Lemma 3
(`lemma3_indexed`, with `s = 4^n`) finally covers the `(p,q)`-block by at most
`(1 + n log 4) · 2M (n+1)^3 · (3/2)^n` rectangles (`blockCover_caseII`). -/

section CaseII

/-- The cube-code partition of `B^M` (Lemma 2) used by case II. -/
noncomputable def iiGamma (M : ℕ) (hM : 1 ≤ M) : Fin (2*M) → Set (BVec (Fin M)) :=
  Classical.choose (lemma2 M hM)

lemma iiGamma_threeCode (M : ℕ) (hM : 1 ≤ M) (i : Fin (2*M)) :
    ∀ x ∈ iiGamma M hM i, ∀ y ∈ iiGamma M hM i, x ≠ y → 3 ≤ hammingNorm (x - y) :=
  (Classical.choose_spec (lemma2 M hM)).1 i

lemma iiGamma_cover (M : ℕ) (hM : 1 ≤ M) : Set.univ = ⋃ i, iiGamma M hM i :=
  (Classical.choose_spec (lemma2 M hM)).2.2

/-- The support of `a` restricted to the index set `S`, as a subset of `S`. -/
def suppL {n : ℕ} (S : Finset (Fin n)) (a : BVec (Fin n)) : Finset (Fin n) :=
  S.filter (fun i => a i ≠ 0)

lemma support_restrict_card {n : ℕ} (S : Finset (Fin n)) (a : BVec (Fin n)) :
    (support (restrict S a)).card = (suppL S a).card :=
  card_support_restrict S a

lemma card_support_restrict_inter {n : ℕ} (S : Finset (Fin n)) (a b : BVec (Fin n)) :
    (support (restrict S a) ∩ support (restrict S b)).card
      = (suppL S a ∩ suppL S b).card := by
  rw [suppL, suppL]
  apply Finset.card_bij
    (fun (j : ↥S) (_ : j ∈ support (restrict S a) ∩ support (restrict S b)) => (j : Fin n))
  · intro j hj
    rw [Finset.mem_inter, support, support, Finset.mem_filter, Finset.mem_filter] at hj
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_filter.mpr ⟨j.2, hj.1.2⟩, Finset.mem_filter.mpr ⟨j.2, hj.2.2⟩⟩
  · intro j₁ _ j₂ _ h; exact Subtype.ext h
  · intro i hi
    rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hi
    exact ⟨⟨i, hi.1.1⟩, by
        rw [Finset.mem_inter, support, support, Finset.mem_filter, Finset.mem_filter]
        exact ⟨⟨Finset.mem_univ _, hi.1.2⟩, ⟨Finset.mem_univ _, hi.2.2⟩⟩, rfl⟩

/-- For a `1`-entry whose supports lie in `X0∪X1` and `X0∪X2` with `X2 = (X0∪X1)ᶜ`, the number of
common `1`s equals that of the `X0`-restrictions. -/
lemma interCard_restrict_eq {n : ℕ} (X0 X1 : Finset (Fin n)) (a b : BVec (Fin n))
    (ha : support a ⊆ X0 ∪ X1) (hb : support b ⊆ X0 ∪ (Finset.univ \ (X0 ∪ X1))) :
    interCard a b = interCard (restrict X0 a) (restrict X0 b) := by
  rw [interCard_eq_support_inter, interCard_eq_support_inter, card_support_restrict_inter]
  have hsub : support a ∩ support b ⊆ X0 := by
    intro i hi
    rw [Finset.mem_inter] at hi
    have h1 := ha hi.1
    have h2 := hb hi.2
    rw [Finset.mem_union] at h1 h2
    rcases h1 with h1 | h1
    · exact h1
    · rcases h2 with h2 | h2
      · exact h2
      · rw [Finset.mem_sdiff] at h2
        exact absurd (Finset.mem_union.mpr (Or.inr h1) : i ∈ X0 ∪ X1) h2.2
  have hL : suppL X0 a ∩ suppL X0 b = support a ∩ support b := by
    ext i
    rw [suppL, suppL, support, support]
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨_, ha'⟩, _, hb'⟩; exact ⟨ha', hb'⟩
    · rintro ⟨ha', hb'⟩
      have hmem : i ∈ X0 := hsub (Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha'⟩,
         Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb'⟩⟩)
      exact ⟨⟨hmem, ha'⟩, ⟨hmem, hb'⟩⟩
  rw [hL]

/-- The code part `i` of the cube `B^{X0}` (Lemma 2), restricted to the `h`-subsets of `X0`. -/
def iiY {n : ℕ} (M h : ℕ) (hM : 1 ≤ M) (X0 : Finset (Fin n)) (hX0 : X0.card = M)
    (i : Fin (2*M)) : Set (BVec ↥X0) :=
  {v | hammingNorm v = h ∧ reindexBVec (phiS X0 hX0) v ∈ iiGamma M hM i}

/-- The middle-layer size `M = 2p+2q-n` of case II. -/
abbrev IIM (n p q : ℕ) : ℕ := 2*p + 2*q - n

/-- The half-layer `h = ⌈M/2⌉ = (M+1)/2` of case II. -/
abbrev IIh (n p q : ℕ) : ℕ := (2*p + 2*q - n + 1)/2

/-- Case-II rectangle indices: a middle set `X0` of size `M`, an outer set `X1 ⊆ X0ᶜ` of size
`n-2q`, and a code index `i`. -/
abbrev IIIdx (n p q : ℕ) : Type :=
  Σ (X0 : {s : Finset (Fin n) // s.card = IIM n p q}),
    {X1 : Finset (Fin n) // X1 ⊆ (Finset.univ \ X0.1) ∧ X1.card = n - 2*q}
      × Fin (2 * IIM n p q)

namespace IIIdx

variable {n p q : ℕ}

/-- The middle set `X0`. -/
def X0 (x : IIIdx n p q) : Finset (Fin n) := x.1.1
/-- `|X0| = M`. -/
lemma X0card (x : IIIdx n p q) : x.X0.card = IIM n p q := x.1.2
/-- The outer row set `X1`. -/
def X1 (x : IIIdx n p q) : Finset (Fin n) := x.2.1.1
/-- The code index. -/
def cd (x : IIIdx n p q) : Fin (2 * IIM n p q) := x.2.2
/-- The outer column set `X2 = (X0 ∪ X1)ᶜ`. -/
def X2 (x : IIIdx n p q) : Finset (Fin n) := Finset.univ \ (x.X0 ∪ x.X1)

end IIIdx

/-- The rows of the rectangle indexed by `x`: `p`-vectors with `X0`-part an `h`-subset in code
part `i` and support in `X0 ∪ X1`. -/
noncomputable def iiRow (n p q : ℕ) (hM : 1 ≤ IIM n p q) (x : IIIdx n p q) :
    Finset (BVec (Fin n)) := by
  classical
  exact Finset.univ.filter (fun a : BVec (Fin n) =>
    hammingNorm a = p ∧ support a ⊆ x.X0 ∪ x.X1 ∧
      restrict x.X0 a ∈ iiY (IIM n p q) (IIh n p q) hM x.X0 x.X0card x.cd)

/-- The columns of the rectangle indexed by `x`: `q`-vectors with `X0`-part the complement of an
`h`-subset in code part `i` and support in `X0 ∪ X2`. -/
noncomputable def iiCol (n p q : ℕ) (hM : 1 ≤ IIM n p q) (x : IIIdx n p q) :
    Finset (BVec (Fin n)) := by
  classical
  exact Finset.univ.filter (fun b : BVec (Fin n) =>
    hammingNorm b = q ∧ support b ⊆ x.X0 ∪ x.X2 ∧
      (1 - restrict x.X0 b) ∈ iiY (IIM n p q) (IIh n p q) hM x.X0 x.X0card x.cd)

/-- The `1`-entries covered by the rectangle indexed by `x`. -/
noncomputable def iiMem (n p q : ℕ) (hM : 1 ≤ IIM n p q) (x : IIIdx n p q) :
    Finset (BlockEntries n p q) := by
  classical
  exact Finset.univ.filter (fun ab : BlockEntries n p q =>
    ab.1.1 ∈ iiRow n p q hM x ∧ ab.1.2 ∈ iiCol n p q hM x)

lemma mem_iiRow {n p q : ℕ} {hM : 1 ≤ IIM n p q} {x : IIIdx n p q} {a : BVec (Fin n)} :
    a ∈ iiRow n p q hM x ↔ hammingNorm a = p ∧ support a ⊆ x.X0 ∪ x.X1 ∧
      restrict x.X0 a ∈ iiY (IIM n p q) (IIh n p q) hM x.X0 x.X0card x.cd := by
  classical
  unfold iiRow
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma mem_iiCol {n p q : ℕ} {hM : 1 ≤ IIM n p q} {x : IIIdx n p q} {b : BVec (Fin n)} :
    b ∈ iiCol n p q hM x ↔ hammingNorm b = q ∧ support b ⊆ x.X0 ∪ x.X2 ∧
      (1 - restrict x.X0 b) ∈ iiY (IIM n p q) (IIh n p q) hM x.X0 x.X0card x.cd := by
  classical
  unfold iiCol
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Case II, legality.**  The rectangle belongs to the disjointness matrix (has no `0`-entry),
because the `X0`-parts of a row and a column lie in the same 3-code part. -/
theorem iiRect_isRect (n p q : ℕ) (hM : 1 ≤ IIM n p q) (x : IIIdx n p q) :
    IsRectangle (iiRow n p q hM x) (iiCol n p q hM x) := by
  intro a ha b hb
  rw [mem_iiRow] at ha
  rw [mem_iiCol] at hb
  obtain ⟨han, hasupp, hacode⟩ := ha
  obtain ⟨hbn, hbsupp, hbcode⟩ := hb
  rw [iiY, Set.mem_ofPred_eq] at hacode hbcode
  obtain ⟨hacn, hacg⟩ := hacode
  obtain ⟨hbcn, hbcg⟩ := hbcode
  rw [interCard_restrict_eq x.X0 x.X1 a b hasupp hbsupp]
  by_cases heq : restrict x.X0 a = 1 - restrict x.X0 b
  · have h1 : restrict x.X0 b = 1 - restrict x.X0 a := by rw [heq]; abel
    have h0 : interCard (restrict x.X0 a) (restrict x.X0 b) = 0 := by
      rw [h1, interCard_self_one_sub]
    rw [h0]; norm_num
  · have hne : reindexBVec (phiS x.X0 x.X0card) (restrict x.X0 a) ≠
        reindexBVec (phiS x.X0 x.X0card) (1 - restrict x.X0 b) :=
      fun h => heq (reindexBVec_injective _ h)
    have hthree := iiGamma_threeCode (IIM n p q) hM x.cd _ hacg _ hbcg hne
    rw [← reindexBVec_sub, hammingNorm_reindexBVec] at hthree
    have hsa := hammingNorm_sub_add (restrict x.X0 a) (1 - restrict x.X0 b)
    rw [hacn, hbcn] at hsa
    have hic2 : interCard (restrict x.X0 a) (1 - restrict x.X0 b) ≤ IIh n p q - 2 := by
      omega
    have hbase := interCard_one_sub (restrict x.X0 a) (1 - restrict x.X0 b)
    have hb2 : (1 : BVec ↥x.X0) - (1 - restrict x.X0 b) = restrict x.X0 b := by abel
    rw [hb2, hacn] at hbase
    rw [hbase]; omega

/-- Number of subsets of `x` of size `k`. -/
lemma card_subset_card {n : ℕ} (x : Finset (Fin n)) (k : ℕ) :
    Fintype.card {A : Finset (Fin n) // A ⊆ x ∧ A.card = k} = x.card.choose k := by
  have h : {A : Finset (Fin n) // A ⊆ x ∧ A.card = k} ≃ ↥(x.powersetCard k) :=
    { toFun := fun A => ⟨A.1, Finset.mem_powersetCard.mpr A.2⟩
      invFun := fun A => ⟨A.1, Finset.mem_powersetCard.mp A.2⟩
      left_inv := fun A => Subtype.ext rfl
      right_inv := fun A => Subtype.ext rfl }
  rw [Fintype.card_congr h, Fintype.card_coe, Finset.card_powersetCard]

/-- Certificates counted by the case-II degree: a `h`-subset `A` of the row support, an
`(M-h)`-subset `B` of the column support, and a `(n-2q-p+h)`-subset `T` of the remaining
coordinates. -/
abbrev IICert (n p q : ℕ) (a b : BVec (Fin n)) : Type :=
  {A : Finset (Fin n) // A ⊆ support a ∧ A.card = IIh n p q} ×
  {B : Finset (Fin n) // B ⊆ support b ∧ B.card = IIM n p q - IIh n p q} ×
  {T : Finset (Fin n) // T ⊆ Finset.univ \ (support a ∪ support b) ∧
      T.card = n - 2*q - (p - IIh n p q)}

lemma card_IICert {n p q : ℕ} {a b : BVec (Fin n)} (ha : hammingNorm a = p) (hb : hammingNorm b = q)
    (hab : interCard a b = 0) :
    Fintype.card (IICert n p q a b) =
      p.choose (IIh n p q) * (q.choose (IIM n p q - IIh n p q))
        * ((n - p - q).choose (n - 2*q - (p - IIh n p q))) := by
  classical
  have hdisj : Disjoint (support a) (support b) := by
    rw [Finset.disjoint_left]; intro i hia hib
    have hmem : i ∈ support a ∩ support b := Finset.mem_inter.mpr ⟨hia, hib⟩
    have hcard : (support a ∩ support b).card = 0 := by
      rw [← interCard_eq_support_inter, hab]
    rw [Finset.card_eq_zero] at hcard
    rw [hcard] at hmem
    exact absurd hmem (by simp)
  have hSa : (support a).card = p := by rw [← hammingNorm_eq_support, ha]
  have hSb : (support b).card = q := by rw [← hammingNorm_eq_support, hb]
  have hcomp : (Finset.univ \ (support a ∪ support b)).card = n - p - q := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin,
      Finset.card_union_of_disjoint hdisj, hSa, hSb]
    omega
  rw [Fintype.card_prod, Fintype.card_prod, card_subset_card, card_subset_card, card_subset_card,
    hSa, hSb, hcomp]
  ring

lemma iiExists {M : ℕ} (hM : 1 ≤ M) (v : BVec (Fin M)) : ∃ i, v ∈ iiGamma M hM i := by
  have : v ∈ ⋃ i, iiGamma M hM i := by rw [← iiGamma_cover M hM]; trivial
  exact Set.mem_iUnion.mp this

/-- The code index of a cube vector (Lemma 2 partition). -/
noncomputable def iiPart {M : ℕ} (hM : 1 ≤ M) (v : BVec (Fin M)) : Fin (2*M) :=
  Classical.choose (iiExists hM v)

lemma iiPart_spec {M : ℕ} (hM : 1 ≤ M) (v : BVec (Fin M)) :
    v ∈ iiGamma M hM (iiPart hM v) := Classical.choose_spec (iiExists hM v)

lemma support_restrict_inter_card {n : ℕ} (S : Finset (Fin n)) (a : BVec (Fin n)) :
    (support (restrict S a)).card = (S ∩ support a).card := by
  rw [support_restrict_card]
  congr 1
  ext i; simp [suppL, support]

lemma iiSaSb_notMem {n : ℕ} {a b : BVec (Fin n)} (hab : interCard a b = 0)
    {x : Fin n} (ha : x ∈ support a) (hb : x ∈ support b) : False := by
  have hmem : x ∈ support a ∩ support b := Finset.mem_inter.mpr ⟨ha, hb⟩
  have hc : (support a ∩ support b).card = 0 := by rw [← interCard_eq_support_inter, hab]
  rw [Finset.card_eq_zero] at hc
  rw [hc] at hmem
  simpa using hmem

lemma iiCert_hX0card {n p q : ℕ} {a b : BVec (Fin n)} (hM : 1 ≤ IIM n p q)
    (hab : interCard a b = 0)
    (c : IICert n p q a b) : (c.1.1 ∪ c.2.1.1).card = IIM n p q := by
  have hAB : Disjoint c.1.1 c.2.1.1 := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    rw [Finset.mem_inter] at hi
    exact iiSaSb_notMem hab (c.1.2.1 hi.1) (c.2.1.2.1 hi.2)
  rw [Finset.card_union_of_disjoint hAB, c.1.2.2, c.2.1.2.2]
  have hle : IIh n p q ≤ IIM n p q := by
    have h1 : IIh n p q = (IIM n p q + 1)/2 := rfl
    omega
  omega

lemma iiCert_hX1sub {n p q : ℕ} {a b : BVec (Fin n)} (hab : interCard a b = 0)
    (c : IICert n p q a b) :
    ((support a \ c.1.1) ∪ c.2.2.1) ⊆ Finset.univ \ (c.1.1 ∪ c.2.1.1) := by
  intro j hj
  rw [Finset.mem_sdiff]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [Finset.mem_union, not_or]
  rw [Finset.mem_union] at hj
  constructor
  · rcases hj with hj | hj
    · exact (Finset.mem_sdiff.mp hj).2
    · exact fun h => (Finset.mem_sdiff.mp (c.2.2.2.1 hj)).2 (Finset.mem_union_left _ (c.1.2.1 h))
  · rcases hj with hj | hj
    · exact fun h => iiSaSb_notMem hab (Finset.mem_sdiff.mp hj).1 (c.2.1.2.1 h)
    · exact fun h => (Finset.mem_sdiff.mp (c.2.2.2.1 hj)).2 (Finset.mem_union_right _ (c.2.1.2.1 h))

lemma iiCert_hX1card {n p q : ℕ} {a b : BVec (Fin n)} (h2q : 2*q ≤ n) (ha : hammingNorm a = p)
    (c : IICert n p q a b) :
    ((support a \ c.1.1) ∪ c.2.2.1).card = n - 2*q := by
  have hdisj : Disjoint (support a \ c.1.1) c.2.2.1 := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    rw [Finset.mem_inter, Finset.mem_sdiff] at hi
    exact (Finset.mem_sdiff.mp (c.2.2.2.1 hi.2)).2 (Finset.mem_union_left _ hi.1.1)
  rw [Finset.card_union_of_disjoint hdisj, c.2.2.2.2]
  have hsa : (support a).card = p := by rw [← hammingNorm_eq_support, ha]
  have hsd : (support a \ c.1.1).card = p - IIh n p q := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr c.1.2.1, c.1.2.2, hsa]
  have hle : p - IIh n p q ≤ n - 2*q := by
    have : IIh n p q = (2*p + 2*q - n + 1)/2 := rfl
    omega
  rw [hsd]
  omega

noncomputable def iiCertInv {n p q : ℕ} (hM : 1 ≤ IIM n p q) (h2q : 2*q ≤ n) {a b : BVec (Fin n)}
    (ha : hammingNorm a = p) (hb : hammingNorm b = q) (hab : interCard a b = 0)
    (c : IICert n p q a b) :
    {x : IIIdx n p q // a ∈ iiRow n p q hM x ∧ b ∈ iiCol n p q hM x} := by
  classical
  have hX0c : (c.1.1 ∪ c.2.1.1).card = IIM n p q := iiCert_hX0card hM hab c
  have hX1s : ((support a \ c.1.1) ∪ c.2.2.1) ⊆ Finset.univ \ (c.1.1 ∪ c.2.1.1) :=
    iiCert_hX1sub hab c
  have hX1c : ((support a \ c.1.1) ∪ c.2.2.1).card = n - 2*q := iiCert_hX1card h2q ha c
  have hX0Sa : (c.1.1 ∪ c.2.1.1) ∩ support a = c.1.1 := by
    rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr c.1.2.1]
    rw [show c.2.1.1 ∩ support a = ∅ from by
        rw [Finset.eq_empty_iff_forall_notMem]; intro i hi
        rw [Finset.mem_inter] at hi
        exact iiSaSb_notMem hab hi.2 (c.2.1.2.1 hi.1)]
    rw [Finset.union_empty]
  let x : IIIdx n p q :=
    ⟨⟨c.1.1 ∪ c.2.1.1, hX0c⟩,
      ⟨⟨(support a \ c.1.1) ∪ c.2.2.1, hX1s, hX1c⟩,
       iiPart hM (reindexBVec (phiS (c.1.1 ∪ c.2.1.1) hX0c) (restrict (c.1.1 ∪ c.2.1.1) a))⟩⟩
  have hx0 : x.X0 = c.1.1 ∪ c.2.1.1 := rfl
  have hx1 : x.X1 = (support a \ c.1.1) ∪ c.2.2.1 := rfl
  have hxc : x.X0card = hX0c := rfl
  have hxd : x.cd = iiPart hM (reindexBVec (phiS (c.1.1 ∪ c.2.1.1) hX0c)
      (restrict (c.1.1 ∪ c.2.1.1) a)) := rfl
  refine ⟨x, ?_, ?_⟩
  · rw [mem_iiRow]
    simp only [hx0, hx1, hxc, hxd]
    refine ⟨ha, ?_, ?_⟩
    · intro j hj
      by_cases hjA : j ∈ c.1.1
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hjA)))
      · exact Finset.mem_union.mpr
          (Or.inr (Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mpr ⟨hj, hjA⟩))))
    · simp only [iiY, Set.mem_ofPred_eq]
      refine ⟨?_, iiPart_spec hM _⟩
      rw [hammingNorm_eq_support, support_restrict_inter_card, hx0, hX0Sa]
      exact c.1.2.2
  · rw [mem_iiCol]
    simp only [hx0, hx1, hxc, hxd, IIIdx.X2]
    refine ⟨hb, ?_, ?_⟩
    · intro j hj
      by_cases hjB : j ∈ c.2.1.1
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hjB)))
      · apply Finset.mem_union.mpr; right
        rw [Finset.mem_sdiff]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hX
        rw [Finset.mem_union] at hX
        rcases hX with hX | hX
        · rw [Finset.mem_union] at hX
          rcases hX with hA | hB
          · exact iiSaSb_notMem hab (c.1.2.1 hA) hj
          · exact hjB hB
        · rw [Finset.mem_union] at hX
          rcases hX with h1 | h1
          · exact iiSaSb_notMem hab (Finset.mem_sdiff.mp h1).1 hj
          · exact (Finset.mem_sdiff.mp (c.2.2.2.1 h1)).2 (Finset.mem_union_right _ hj)
    · have heq : (1 : BVec ↥x.X0) - restrict x.X0 b = restrict x.X0 a := by
        funext j
        simp only [Pi.sub_apply, Pi.one_apply, restrict_apply]
        have hj : (j : Fin n) ∈ c.1.1 ∪ c.2.1.1 := by simpa only [hx0] using j.2
        rw [Finset.mem_union] at hj
        rcases hj with hA | hB
        · have hAj : a (j : Fin n) ≠ 0 := (Finset.mem_filter.mp (c.1.2.1 hA)).2
          have hbj : b (j : Fin n) = 0 := by
            by_contra h
            exact iiSaSb_notMem hab (c.1.2.1 hA) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          rw [hbj, zmod_two_eq_one hAj]; ring
        · have hBj : b (j : Fin n) ≠ 0 := (Finset.mem_filter.mp (c.2.1.2.1 hB)).2
          have haj : a (j : Fin n) = 0 := by
            by_contra h
            exact iiSaSb_notMem hab (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩) (c.2.1.2.1 hB)
          rw [haj, zmod_two_eq_one hBj]; ring
      simp only [iiY, Set.mem_ofPred_eq]
      refine ⟨?_, ?_⟩
      · rw [heq, hammingNorm_eq_support, support_restrict_inter_card, hx0, hX0Sa]
        exact c.1.2.2
      · rw [heq]; exact iiPart_spec hM _

/-- The certificate-to-index map `iiCertInv` is injective; the value
`(iiCertInv c).1.1.1` is `c.1.1 ∪ c.2.1.1` and `(iiCertInv c).1.2.1.1` is
`(support a \ c.1.1) ∪ c.2.2.1`. -/
lemma iiCertInv_injective {n p q : ℕ} (hM : 1 ≤ IIM n p q) (h2q : 2*q ≤ n)
    {a b : BVec (Fin n)} (ha : hammingNorm a = p) (hb : hammingNorm b = q)
    (hab : interCard a b = 0) :
    Function.Injective (iiCertInv hM h2q ha hb hab) := by
  classical
  have key_a : ∀ c : IICert n p q a b, (c.1.1 ∪ c.2.1.1) ∩ support a = c.1.1 := by
    intro c
    rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr c.1.2.1]
    rw [show c.2.1.1 ∩ support a = ∅ from by
      rw [Finset.eq_empty_iff_forall_notMem]; intro i hi
      rw [Finset.mem_inter] at hi
      exact iiSaSb_notMem hab hi.2 (c.2.1.2.1 hi.1)]
    rw [Finset.union_empty]
  have key_b : ∀ c : IICert n p q a b, (c.1.1 ∪ c.2.1.1) ∩ support b = c.2.1.1 := by
    intro c
    rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr c.2.1.2.1]
    rw [show c.1.1 ∩ support b = ∅ from by
      rw [Finset.eq_empty_iff_forall_notMem]; intro i hi
      rw [Finset.mem_inter] at hi
      exact iiSaSb_notMem hab (c.1.2.1 hi.1) hi.2]
    rw [Finset.empty_union]
  intro c c' h
  have hX0 : (iiCertInv hM h2q ha hb hab c).1.1.1 = (iiCertInv hM h2q ha hb hab c').1.1.1 :=
    congrArg (fun y => y.1.1.1) h
  have hX1 : (iiCertInv hM h2q ha hb hab c).1.2.1.1
      = (iiCertInv hM h2q ha hb hab c').1.2.1.1 :=
    congrArg (fun y => y.1.2.1.1) h
  rw [show (iiCertInv hM h2q ha hb hab c).1.1.1 = c.1.1 ∪ c.2.1.1 from rfl,
      show (iiCertInv hM h2q ha hb hab c').1.1.1 = c'.1.1 ∪ c'.2.1.1 from rfl] at hX0
  rw [show (iiCertInv hM h2q ha hb hab c).1.2.1.1 = (support a \ c.1.1) ∪ c.2.2.1 from rfl,
      show (iiCertInv hM h2q ha hb hab c').1.2.1.1 = (support a \ c'.1.1) ∪ c'.2.2.1 from rfl]
      at hX1
  have hA : c.1.1 = c'.1.1 := by rw [← key_a c, hX0, key_a c']
  have hB : c.2.1.1 = c'.2.1.1 := by rw [← key_b c, hX0, key_b c']
  have hT : c.2.2.1 = c'.2.2.1 := by
    have hX1' : (support a \ c'.1.1) ∪ c.2.2.1 = (support a \ c'.1.1) ∪ c'.2.2.1 := by
      rw [← hX1, hA]
    apply Finset.Subset.antisymm
    · intro i hi
      have hmem : i ∈ (support a \ c'.1.1) ∪ c'.2.2.1 := by
        rw [← hX1']; exact Finset.mem_union_right _ hi
      rw [Finset.mem_union] at hmem
      rcases hmem with h1 | h1
      · exact absurd (Finset.mem_sdiff.mp h1).1
          (fun hmem => (Finset.mem_sdiff.mp (c.2.2.2.1 hi)).2 (Finset.mem_union_left _ hmem))
      · exact h1
    · intro i hi
      have hmem : i ∈ (support a \ c'.1.1) ∪ c.2.2.1 := by
        rw [hX1']; exact Finset.mem_union_right _ hi
      rw [Finset.mem_union] at hmem
      rcases hmem with h1 | h1
      · exact absurd (Finset.mem_sdiff.mp h1).1
          (fun hmem => (Finset.mem_sdiff.mp (c'.2.2.2.1 hi)).2 (Finset.mem_union_left _ hmem))
      · exact h1
  exact Prod.ext (Subtype.ext hA) (Prod.ext (Subtype.ext hB) (Subtype.ext hT))

/-- The `(p,q)`-block entries number at most `4^n`. -/
lemma card_BlockEntries_le (n p q : ℕ) : Fintype.card (BlockEntries n p q) ≤ 4 ^ n := by
  have h1 : Fintype.card (BlockEntries n p q)
      ≤ Fintype.card (BVec (Fin n) × BVec (Fin n)) := Fintype.card_subtype_le _
  rw [Fintype.card_prod, card_BVec, Fintype.card_fin] at h1
  refine h1.trans (le_of_eq ?_)
  rw [← pow_add, show n + n = 2 * n by ring, pow_mul]; norm_num

/-- Every covering set of the case-II family has size `≤ 4^n`. -/
lemma iiMem_card_le (n p q : ℕ) (hM : 1 ≤ IIM n p q) (x : IIIdx n p q) :
    (iiMem n p q hM x).card ≤ 4 ^ n :=
  (Finset.card_le_univ _).trans (card_BlockEntries_le n p q)

/-- **Case II, uniform degree.**  Every `1`-entry of the `(p,q)`-block is covered by exactly
`|IICert| = C(p,h) C(q,M-h) C(n-p-q,T)` members of the case-II family. -/
lemma iiDeg_lower (n p q : ℕ) (hM : 1 ≤ IIM n p q) (h2q : 2*q ≤ n)
    (x : BlockEntries n p q) :
    Fintype.card (IICert n p q x.1.1 x.1.2) ≤
      (Finset.univ.filter (fun i : IIIdx n p q => x ∈ iiMem n p q hM i)).card := by
  classical
  have h1 : Fintype.card (IICert n p q x.1.1 x.1.2) ≤
      (Finset.univ.filter (fun i : IIIdx n p q =>
          x.1.1 ∈ iiRow n p q hM i ∧ x.1.2 ∈ iiCol n p q hM i)).card := by
    have hinj := iiCertInv_injective hM h2q x.2.1 x.2.2.1 x.2.2.2
    have h := Fintype.card_le_of_injective _ hinj
    rwa [Fintype.card_subtype] at h
  refine h1.trans (le_of_eq ?_)
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [iiMem, Finset.mem_filter]
  simp

abbrev IIDeg (n p q : ℕ) : ℕ := p.choose (IIh n p q) * (q.choose (IIM n p q - IIh n p q)) * ((n - p - q).choose (n - 2*q - (p - IIh n p q)))

theorem ii_multinomial_identity (n M L1 L2 h c1 T c2 U p q : ℕ)
    (hM : M + L1 + L2 = n) (hp : h + c1 = p) (hq : (M - h) + c2 = q)
    (hr : T + U = n - p - q) (hL1 : c1 + T = L1) (hL2 : c2 + U = L2)
    (hM2 : h + (M - h) = M) :
    (n.choose M) * ((n - M).choose L1) * ((M.choose h) * (L1.choose c1) * (L2.choose c2))
      = ((p.choose h) * (q.choose (M - h)) * ((n - p - q).choose T)) *
        ((n.choose p) * ((n - p).choose q)) := by
  have hMn : M ≤ n := by omega
  have hL1n : L1 ≤ n - M := by omega
  have hhM : h ≤ M := by omega
  have hc1L1 : c1 ≤ L1 := by omega
  have hc2L2 : c2 ≤ L2 := by omega
  have hp' : p ≤ n := by omega
  have hq' : q ≤ n - p := by omega
  have hp'h : h ≤ p := by omega
  have hMhq : M - h ≤ q := by omega
  have hUn : T ≤ n - p - q := by omega
  have e_nM : n - M - L1 = L2 := by omega
  have e_L1 : L1 - c1 = T := by omega
  have e_5 : L2 - c2 = n - p - q - T := by omega
  have e_p : p - h = c1 := by omega
  have e_q : q - (M - h) = c2 := by omega
  set W1 := M.factorial * (n-M).factorial * L1.factorial * (n-M-L1).factorial * h.factorial
      * (M-h).factorial * c1.factorial * (L1-c1).factorial * c2.factorial * (L2-c2).factorial with hW1
  set W2 := h.factorial * (M-h).factorial * (p-h).factorial * (q-(M-h)).factorial * T.factorial
      * (n-p-q-T).factorial * p.factorial * (n-p).factorial * q.factorial * (n-p-q).factorial with hW2
  have hWpos : 0 < W1 * W2 := by rw [hW1, hW2]; positivity
  have hA : (n.choose M * (n - M).choose L1 * (M.choose h * L1.choose c1 * L2.choose c2)) * (W1 * W2)
      = n.factorial * (n-M).factorial * M.factorial * L1.factorial * L2.factorial * W2 := by
    rw [hW1, hW2]
    rw [show (n.choose M * (n - M).choose L1 * (M.choose h * L1.choose c1 * L2.choose c2))
          * ((M.factorial * (n-M).factorial * L1.factorial * (n-M-L1).factorial * h.factorial
              * (M-h).factorial * c1.factorial * (L1-c1).factorial * c2.factorial * (L2-c2).factorial)
            * (h.factorial * (M-h).factorial * (p-h).factorial * (q-(M-h)).factorial * T.factorial
              * (n-p-q-T).factorial * p.factorial * (n-p).factorial * q.factorial * (n-p-q).factorial))
        = (n.choose M * M.factorial * (n-M).factorial)
          * ((n-M).choose L1 * L1.factorial * (n-M-L1).factorial)
          * (M.choose h * h.factorial * (M-h).factorial)
          * (L1.choose c1 * c1.factorial * (L1-c1).factorial)
          * (L2.choose c2 * c2.factorial * (L2-c2).factorial)
          * (h.factorial * (M-h).factorial * (p-h).factorial * (q-(M-h)).factorial * T.factorial
              * (n-p-q-T).factorial * p.factorial * (n-p).factorial * q.factorial * (n-p-q).factorial) from by ring]
    rw [Nat.choose_mul_factorial_mul_factorial hMn,
        Nat.choose_mul_factorial_mul_factorial hL1n,
        Nat.choose_mul_factorial_mul_factorial hhM,
        Nat.choose_mul_factorial_mul_factorial hc1L1,
        Nat.choose_mul_factorial_mul_factorial hc2L2]
  have hB : ((p.choose h * q.choose (M - h) * (n - p - q).choose T) * (n.choose p * (n - p).choose q))
        * (W1 * W2)
      = n.factorial * (n-M).factorial * M.factorial * L1.factorial * L2.factorial * W2 := by
    rw [hW1, hW2]
    rw [show ((p.choose h * q.choose (M - h) * (n - p - q).choose T) * (n.choose p * (n - p).choose q))
          * ((M.factorial * (n-M).factorial * L1.factorial * (n-M-L1).factorial * h.factorial
              * (M-h).factorial * c1.factorial * (L1-c1).factorial * c2.factorial * (L2-c2).factorial)
            * (h.factorial * (M-h).factorial * (p-h).factorial * (q-(M-h)).factorial * T.factorial
              * (n-p-q-T).factorial * p.factorial * (n-p).factorial * q.factorial * (n-p-q).factorial))
        = (p.choose h * h.factorial * (p-h).factorial)
          * (q.choose (M-h) * (M-h).factorial * (q-(M-h)).factorial)
          * ((n-p-q).choose T * T.factorial * (n-p-q-T).factorial)
          * (n.choose p * p.factorial * (n-p).factorial)
          * ((n-p).choose q * q.factorial * (n-p-q).factorial)
          * (M.factorial * (n-M).factorial * L1.factorial * (n-M-L1).factorial * h.factorial
              * (M-h).factorial * c1.factorial * (L1-c1).factorial * c2.factorial * (L2-c2).factorial) from by ring]
    rw [Nat.choose_mul_factorial_mul_factorial hp'h,
        Nat.choose_mul_factorial_mul_factorial hMhq,
        Nat.choose_mul_factorial_mul_factorial hUn,
        Nat.choose_mul_factorial_mul_factorial hp',
        Nat.choose_mul_factorial_mul_factorial hq']
    rw [show p.factorial * q.factorial * (n-p-q).factorial * n.factorial * (n-p).factorial
          * (M.factorial * (n-M).factorial * L1.factorial * (n-M-L1).factorial * h.factorial
              * (M-h).factorial * c1.factorial * (L1-c1).factorial * c2.factorial * (L2-c2).factorial)
        = n.factorial * (n-M).factorial * M.factorial * L1.factorial * L2.factorial
          * (h.factorial * (M-h).factorial * (p-h).factorial * (q-(M-h)).factorial * T.factorial
              * (n-p-q-T).factorial * p.factorial * (n-p).factorial * q.factorial * (n-p-q).factorial)
        from by rw [e_nM, e_L1, e_5, ← e_p, ← e_q]; ring]
  have hsame : (n.choose M * (n - M).choose L1 * (M.choose h * L1.choose c1 * L2.choose c2)) * (W1 * W2)
      = ((p.choose h * q.choose (M - h) * (n - p - q).choose T) * (n.choose p * (n - p).choose q))
        * (W1 * W2) := hA.trans hB.symm
  exact Nat.mul_right_cancel hWpos hsame

theorem ii_Q_identity (n p q : ℕ) (h2p : 2*p ≤ n) (h2q : 2*q ≤ n) (hpq : p+q ≤ n) (hlo : n ≤ 2*p + 2*q) :
    (n.choose (IIM n p q)) * ((n - IIM n p q).choose (n - 2*q))
      * ((IIM n p q).choose (IIh n p q) * ((n - 2*q).choose (p - IIh n p q))
          * ((n - 2*p).choose (q - (IIM n p q - IIh n p q))))
    = ((p.choose (IIh n p q)) * (q.choose (IIM n p q - IIh n p q))
        * ((n - p - q).choose (n - 2*q - (p - IIh n p q))))
      * ((n.choose p) * ((n - p).choose q)) := by
  exact ii_multinomial_identity n (IIM n p q) (n - 2*q) (n - 2*p) (IIh n p q) (p - IIh n p q)
    (n - 2*q - (p - IIh n p q)) (q - (IIM n p q - IIh n p q))
    (n - p - q - (n - 2*q - (p - IIh n p q))) p q
    (by simp only [IIM, IIh]; omega) (by simp only [IIM, IIh]; omega)
    (by simp only [IIM, IIh]; omega) (by simp only [IIM, IIh]; omega)
    (by simp only [IIM, IIh]; omega) (by simp only [IIM, IIh]; omega)
    (by simp only [IIM, IIh]; omega)

lemma two_pow_le_central (N : ℕ) : 2^N ≤ (N+1) * N.choose (N/2) := by
  have h := Nat.sum_range_choose N
  rw [← h]
  calc ∑ k ∈ Finset.range (N+1), N.choose k ≤ ∑ _k ∈ Finset.range (N+1), N.choose (N/2) :=
        Finset.sum_le_sum (fun k _ => Nat.choose_le_middle k N)
    _ = (N+1) * N.choose (N/2) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

lemma U_le_three_pow (n p q : ℕ) (hpq : p + q ≤ n) :
    n.choose p * (n - p).choose q ≤ 3 ^ n := by
  have hp : p ≤ n := by omega
  have hterm : 2^(n-p) * n.choose p ≤ 3^n := by
    have h := add_pow (1:ℕ) 2 n
    rw [show (1:ℕ) + 2 = 3 by norm_num] at h
    rw [h]
    have := Finset.single_le_sum (f := fun m => 1^m * 2^(n-m) * n.choose m)
      (fun i _ => by positivity) (show p ∈ Finset.range (n+1) by simp only [Finset.mem_range]; omega)
    simpa using this
  calc n.choose p * (n - p).choose q ≤ n.choose p * 2^(n-p) :=
        Nat.mul_le_mul_left _ (Nat.choose_le_two_pow (n-p) q)
    _ = 2^(n-p) * n.choose p := by ring
    _ ≤ 3^n := hterm

lemma choose_half_eq (M : ℕ) : M.choose ((M+1)/2) = M.choose (M/2) :=
  Nat.choose_symm_of_eq_add (show M = (M+1)/2 + M/2 by omega)

lemma Q_ge (n p q : ℕ) (h2p : 2*p ≤ n) (h2q : 2*q ≤ n) (hpq : p + q ≤ n) (hlo : n ≤ 2*p + 2*q) :
    2^n ≤ ((IIM n p q).choose (IIh n p q) * ((n - 2*q).choose (p - IIh n p q))
        * ((n - 2*p).choose (q - (IIM n p q - IIh n p q)))) * (n+1)^3 := by
  have h1 : 2^(IIM n p q) ≤ (IIM n p q + 1) * (IIM n p q).choose (IIM n p q / 2) :=
    two_pow_le_central (IIM n p q)
  have h2 : 2^(n - 2*q) ≤ (n - 2*q + 1) * ((n - 2*q).choose ((n - 2*q)/2)) :=
    two_pow_le_central (n - 2*q)
  have h3 : 2^(n - 2*p) ≤ (n - 2*p + 1) * ((n - 2*p).choose ((n - 2*p)/2)) :=
    two_pow_le_central (n - 2*p)
  have e1 : (IIM n p q).choose (IIh n p q) = (IIM n p q).choose (IIM n p q / 2) :=
    choose_half_eq (IIM n p q)
  have e2 : (n - 2*q).choose (p - IIh n p q) = (n - 2*q).choose ((n - 2*q)/2) := by
    rw [show p - IIh n p q = (n - 2*q)/2 by simp only [IIh, IIM]; omega]
  have e3 : (n - 2*p).choose (q - (IIM n p q - IIh n p q)) = (n - 2*p).choose ((n - 2*p)/2) := by
    rw [show q - (IIM n p q - IIh n p q) = (n-2*p) - (n-2*p)/2 by simp only [IIh, IIM]; omega,
      Nat.choose_symm (by omega : (n-2*p)/2 ≤ n-2*p)]
  rw [e1, e2, e3]
  have hmul : 2^(IIM n p q) * 2^(n - 2*q) * 2^(n - 2*p)
      ≤ ((IIM n p q + 1) * (n - 2*q + 1) * (n - 2*p + 1))
        * ((IIM n p q).choose (IIM n p q / 2) * ((n-2*q).choose ((n-2*q)/2))
            * ((n-2*p).choose ((n-2*p)/2))) := by
    calc 2^(IIM n p q) * 2^(n - 2*q) * 2^(n - 2*p)
        ≤ ((IIM n p q + 1) * (IIM n p q).choose (IIM n p q / 2))
          * ((n - 2*q + 1) * ((n-2*q).choose ((n-2*q)/2)))
          * ((n - 2*p + 1) * ((n-2*p).choose ((n-2*p)/2))) := by
          exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
      _ = ((IIM n p q + 1) * (n - 2*q + 1) * (n - 2*p + 1))
          * ((IIM n p q).choose (IIM n p q / 2) * ((n-2*q).choose ((n-2*q)/2))
              * ((n-2*p).choose ((n-2*p)/2))) := by ring
  have hexp : 2^(IIM n p q) * 2^(n - 2*q) * 2^(n - 2*p) = 2^n := by
    rw [← pow_add, ← pow_add]
    congr 1
    simp only [IIM]; omega
  rw [hexp] at hmul
  have ha : (IIM n p q + 1) * (n - 2*q + 1) * (n - 2*p + 1) ≤ (n+1)^3 := by
    have hM1 : IIM n p q + 1 ≤ n + 1 := by simp only [IIM]; omega
    have hq1 : n - 2*q + 1 ≤ n + 1 := by omega
    have hp1 : n - 2*p + 1 ≤ n + 1 := by omega
    calc (IIM n p q + 1) * (n - 2*q + 1) * (n - 2*p + 1)
        ≤ (n+1) * (n+1) * (n+1) :=
          Nat.mul_le_mul (Nat.mul_le_mul hM1 hq1) hp1
      _ = (n+1)^3 := by ring
  calc 2^n ≤ ((IIM n p q + 1) * (n - 2*q + 1) * (n - 2*p + 1))
              * ((IIM n p q).choose (IIM n p q / 2) * (n - 2*q).choose ((n - 2*q) / 2)
                  * (n - 2*p).choose ((n - 2*p) / 2)) := hmul
    _ ≤ (n+1)^3 * ((IIM n p q).choose (IIM n p q / 2) * (n - 2*q).choose ((n - 2*q) / 2)
                  * (n - 2*p).choose ((n - 2*p) / 2)) := Nat.mul_le_mul_right _ ha
    _ = ((IIM n p q).choose (IIM n p q / 2) * (n - 2*q).choose ((n - 2*q) / 2)
                  * (n - 2*p).choose ((n - 2*p) / 2)) * (n+1)^3 := by ring

lemma card_IIIdx (n p q : ℕ) :
    Fintype.card (IIIdx n p q)
      = n.choose (IIM n p q) * ((n - IIM n p q).choose (n - 2*q)) * (2 * IIM n p q) := by
  classical
  have hX0 : Fintype.card {s : Finset (Fin n) // s.card = IIM n p q} = n.choose (IIM n p q) := by
    rw [show Fintype.card {s : Finset (Fin n) // s.card = IIM n p q}
        = Fintype.card {s : Finset (Fin n) // s ⊆ (Finset.univ : Finset (Fin n)) ∧ s.card = IIM n p q}
        from Fintype.card_congr (Equiv.subtypeEquivRight (fun s => by simp))]
    rw [card_subset_card, Finset.card_univ, Fintype.card_fin]
  change Fintype.card (Σ (X0 : {s : Finset (Fin n) // s.card = IIM n p q}),
      {X1 : Finset (Fin n) // X1 ⊆ Finset.univ \ X0.1 ∧ X1.card = n - 2*q} × Fin (2 * IIM n p q))
    = n.choose (IIM n p q) * ((n - IIM n p q).choose (n - 2*q)) * (2 * IIM n p q)
  rw [Fintype.card_sigma]
  have hconst : ∀ X0 : {s : Finset (Fin n) // s.card = IIM n p q},
      Fintype.card ({X1 : Finset (Fin n) // X1 ⊆ Finset.univ \ X0.1 ∧ X1.card = n - 2*q}
        × Fin (2 * IIM n p q)) = ((n - IIM n p q).choose (n - 2*q)) * (2 * IIM n p q) := by
    intro X0
    rw [Fintype.card_prod, Fintype.card_fin, card_subset_card]
    congr 1
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, X0.2]
  rw [Finset.sum_congr rfl (fun X0 _ => hconst X0), Finset.sum_const, Finset.card_univ, smul_eq_mul, hX0]
  ring

lemma ii_ratio_bound (n p q : ℕ) (hM : 1 ≤ IIM n p q) (h2p : 2*p ≤ n) (h2q : 2*q ≤ n)
    (hpq : p + q ≤ n) (hlo : n ≤ 2*p + 2*q) :
    (Fintype.card (IIIdx n p q) : ℝ) / (IIDeg n p q : ℝ)
      ≤ 2 * (IIM n p q) * ((n:ℝ)+1)^3 * ((3:ℝ)/2)^n := by
  classical
  have hid := ii_Q_identity n p q h2p h2q hpq hlo
  have hU := U_le_three_pow n p q hpq
  have hQ := Q_ge n p q h2p h2q hpq hlo
  have hQpos : 0 < (IIM n p q).choose (IIh n p q) * (n - 2*q).choose (p - IIh n p q)
      * (n - 2*p).choose (q - (IIM n p q - IIh n p q)) := by
    apply Nat.mul_pos (Nat.mul_pos ?_ ?_) ?_
    · exact Nat.choose_pos (by simp only [IIh, IIM]; omega)
    · exact Nat.choose_pos (by simp only [IIh, IIM]; omega)
    · exact Nat.choose_pos (by simp only [IIh, IIM]; omega)
  have hrpos : 0 < IIDeg n p q := by
    show 0 < p.choose (IIh n p q) * (q.choose (IIM n p q - IIh n p q))
      * ((n - p - q).choose (n - 2*q - (p - IIh n p q)))
    apply Nat.mul_pos (Nat.mul_pos ?_ ?_) ?_
    · exact Nat.choose_pos (by simp only [IIh, IIM]; omega)
    · exact Nat.choose_pos (by simp only [IIh, IIM]; omega)
    · exact Nat.choose_pos (by simp only [IIh, IIM]; omega)
  set X : ℕ := n.choose (IIM n p q) * (n - IIM n p q).choose (n-2*q) with hXdef
  set U : ℕ := n.choose p * (n-p).choose q with hUdef
  set Q : ℕ := (IIM n p q).choose (IIh n p q) * (n - 2*q).choose (p - IIh n p q)
      * (n - 2*p).choose (q - (IIM n p q - IIh n p q)) with hQdef
  set r : ℕ := p.choose (IIh n p q) * q.choose (IIM n p q - IIh n p q)
      * (n-p-q).choose (n-2*q-(p-IIh n p q)) with hrdef
  have hQposR : (0:ℝ) < (Q:ℝ) := by rw [hQdef]; push_cast; exact_mod_cast hQpos
  have hrposR : (0:ℝ) < (IIDeg n p q : ℝ) := by exact_mod_cast hrpos
  have hidR : (X:ℝ) * (Q:ℝ) = (r:ℝ) * (U:ℝ) := by
    rw [hXdef, hQdef, hrdef, hUdef]; push_cast; exact_mod_cast hid
  have hkey : (U:ℝ) ≤ ((n:ℝ)+1)^3 * ((3:ℝ)/2)^n * (Q:ℝ) := by
    have h1 : (U:ℝ) ≤ (3:ℝ)^n := by rw [hUdef]; exact_mod_cast hU
    have h2 : (2:ℝ)^n ≤ (Q:ℝ) * ((n:ℝ)+1)^3 := by rw [hQdef]; push_cast; exact_mod_cast hQ
    calc (U:ℝ) ≤ (3:ℝ)^n := h1
      _ = ((3:ℝ)/2)^n * (2:ℝ)^n := by rw [← mul_pow]; norm_num
      _ ≤ ((3:ℝ)/2)^n * ((Q:ℝ) * ((n:ℝ)+1)^3) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ((n:ℝ)+1)^3 * ((3:ℝ)/2)^n * (Q:ℝ) := by ring
  have hXle : (X:ℝ) ≤ ((n:ℝ)+1)^3 * ((3:ℝ)/2)^n * (r:ℝ) := by
    have hstep : (X:ℝ) * (Q:ℝ) ≤ (((n:ℝ)+1)^3 * ((3:ℝ)/2)^n * (r:ℝ)) * (Q:ℝ) := by
      rw [hidR]
      calc (r:ℝ) * (U:ℝ) ≤ (r:ℝ) * (((n:ℝ)+1)^3 * ((3:ℝ)/2)^n * (Q:ℝ)) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
        _ = (((n:ℝ)+1)^3 * ((3:ℝ)/2)^n * (r:ℝ)) * (Q:ℝ) := by ring
    exact le_of_mul_le_mul_right hstep hQposR
  have hcardX : (Fintype.card (IIIdx n p q) : ℝ) = (X:ℝ) * (2 * (IIM n p q)) := by
    rw [card_IIIdx]
    have : n.choose (IIM n p q) * (n - IIM n p q).choose (n-2*q) * (2 * IIM n p q)
        = X * (2 * IIM n p q) := by rw [hXdef]
    rw [this]; push_cast; ring
  rw [hcardX, div_le_iff₀ hrposR]
  nlinarith [hXle]

/-- **Case II.**  If `2p ≤ n`, `2q ≤ n`, `p + q ≤ n` and `n ≤ 2(p+q)` (so the middle layer
`M = 2p+2q-n ≥ 1`), the `(p,q)`-block is covered by at most
`(1 + n log 4) · 2M(n+1)^3 · (3/2)^n` rectangles. -/
lemma blockCover_caseII (n p q : ℕ) (hM : 1 ≤ IIM n p q) (h2p : 2*p ≤ n) (h2q : 2*q ≤ n)
    (hpq : p + q ≤ n) (hlo : n ≤ 2*p + 2*q) :
    ∃ k, HasBlockCover n p q k ∧
      (k : ℝ) ≤ (1 + (n:ℝ) * Real.log 4) * (2 * (IIM n p q) * ((n:ℝ)+1)^3) * ((3:ℝ)/2)^n := by
  classical
  haveI : Nonempty (IIIdx n p q) := by
    have hMn : IIM n p q ≤ n := by simp only [IIM]; omega
    have hL : n - 2*q ≤ n - IIM n p q := by simp only [IIM]; omega
    obtain ⟨X0, -, hX0c⟩ := Finset.exists_subset_card_eq (n := IIM n p q)
      (s := (Finset.univ : Finset (Fin n)))
      (by rw [Finset.card_univ, Fintype.card_fin]; exact hMn)
    obtain ⟨X1, hX1sub, hX1c⟩ := Finset.exists_subset_card_eq (n := n - 2*q) (s := Finset.univ \ X0)
      (by rw [Finset.card_sdiff_of_subset (Finset.subset_univ X0), Finset.card_univ,
            Fintype.card_fin, hX0c]; exact hL)
    exact ⟨⟨X0, hX0c⟩, ⟨⟨X1, hX1sub, hX1c⟩, ⟨0, by have := hM; omega⟩⟩⟩
  have hrpos : 0 < IIDeg n p q := by
    show 0 < p.choose (IIh n p q) * (q.choose (IIM n p q - IIh n p q))
      * ((n - p - q).choose (n - 2*q - (p - IIh n p q)))
    apply Nat.mul_pos (Nat.mul_pos ?_ ?_) ?_
    · exact Nat.choose_pos (by simp only [IIh, IIM]; omega)
    · exact Nat.choose_pos (by simp only [IIh, IIM]; omega)
    · exact Nat.choose_pos (by simp only [IIh, IIM]; omega)
  have hdeg : ∀ x : BlockEntries n p q, IIDeg n p q ≤
      (Finset.univ.filter (fun i : IIIdx n p q => x ∈ iiMem n p q hM i)).card := by
    intro x
    have h1 := iiDeg_lower n p q hM h2q x
    have h2 : Fintype.card (IICert n p q x.1.1 x.1.2) = IIDeg n p q :=
      card_IICert x.2.1 x.2.2.1 x.2.2.2
    rw [h2] at h1
    exact h1
  obtain ⟨I, hIcov, hIcard⟩ := lemma3_indexed (fun i : IIIdx n p q => iiMem n p q hM i)
    (IIDeg n p q) (4^n) hrpos (fun i => iiMem_card_le n p q hM i) hdeg
  have hcover : HasBlockCover n p q I.card := by
    refine hasBlockCover_of_card_eq (k := I.card) (ι := {i : IIIdx n p q // i ∈ I})
      (by rw [Fintype.card_subtype]; congr 1; ext i; simp)
      (fun i => iiRow n p q hM i.1) (fun i => iiCol n p q hM i.1)
      (fun i => iiRect_isRect n p q hM i.1) ?_
    intro a b ha hb hab
    obtain ⟨i, hiI, hi⟩ := hIcov ⟨(a, b), ha, hb, hab⟩
    rw [iiMem, Finset.mem_filter] at hi
    exact ⟨⟨i, hiI⟩, hi.2.1, hi.2.2⟩
  refine ⟨I.card, hcover, ?_⟩
  have hlog : Real.log (((4:ℕ)^n : ℕ) : ℝ) = (n:ℝ) * Real.log 4 := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
  have hratio := ii_ratio_bound n p q hM h2p h2q hpq hlo
  have hfac : (0:ℝ) ≤ 1 + (n:ℝ) * Real.log 4 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  refine hIcard.trans ?_
  rw [hlog]
  calc (1 + (n:ℝ) * Real.log 4) * (Fintype.card (IIIdx n p q) : ℝ) / (IIDeg n p q : ℝ)
      = (1 + (n:ℝ) * Real.log 4) * ((Fintype.card (IIIdx n p q) : ℝ) / (IIDeg n p q : ℝ)) := by
        ring
    _ ≤ (1 + (n:ℝ) * Real.log 4) * (2 * (IIM n p q) * ((n:ℝ)+1)^3 * ((3:ℝ)/2)^n) :=
          mul_le_mul_of_nonneg_left hratio hfac
    _ = (1 + (n:ℝ) * Real.log 4) * (2 * (IIM n p q) * ((n:ℝ)+1)^3) * ((3:ℝ)/2)^n := by ring

end CaseII

/-! ### Case IV: the `α ≥ 1/2` regime via "all outer sets"

Here `n ≤ 2p`.  Rectangles are indexed by *every* subset `X ⊆ [n]` with `q ≤ |X|`, together
with a codeword index `i ∈ Fin (2|X|)`.  The columns of the rectangle `R_{X,i}` are the
weight-`q` subsets of `X` lying in the `i`-th 3-code part (`iiY`) of the cube `B^X`, and its rows
are the `p`-vectors `a` whose `X`-part is the complement (in `X`) of such a codeword.  Every
`1`-entry `(a,b)` is covered by exactly the `2^p` sets `X = supp b ∪ Y` (`Y ⊆ supp a`), so the
family covers uniformly with degree `2^p`.  Because there are at most `2n·2^n` rectangles, the
indexed Lemma 3 produces a covering of size `≤ (1 + n log 4)·2n·2^{n-p} ≤ n^{O(1)}(3/2)^n`. -/

section CaseIV

/-- Case-IV rectangle indices: an outer set `X ⊆ [n]` with `q ≤ |X|`, and a code index
`i ∈ Fin (2|X|)`. -/
abbrev IVIdx (n p q : ℕ) : Type :=
  Σ (X : {s : Finset (Fin n) // q ≤ s.card}), Fin (2 * X.1.card)

namespace IVIdx

variable {n p q : ℕ}

/-- The outer set `X`. -/
def X (x : IVIdx n p q) : Finset (Fin n) := x.1.1

/-- `q ≤ |X|`. -/
lemma X_card_ge (x : IVIdx n p q) : q ≤ x.X.card := x.1.2

/-- The code index. -/
def cd (x : IVIdx n p q) : Fin (2 * x.X.card) := x.2

end IVIdx

/-- Rows of the rectangle indexed by `x`: `p`-vectors whose `X`-part is the complement of a
weight-`q` codeword in code part `i`. -/
noncomputable def ivRow (n p q : ℕ) (hq : 1 ≤ q) (x : IVIdx n p q) :
    Finset (BVec (Fin n)) := by
  classical
  exact Finset.univ.filter (fun a : BVec (Fin n) =>
    hammingNorm a = p ∧
      (1 - restrict x.X a) ∈ iiY x.X.card q (le_trans hq x.X_card_ge) x.X rfl x.cd)

/-- Columns of the rectangle indexed by `x`: `q`-vectors in code part `i` (hence supported in
`X`). -/
noncomputable def ivCol (n p q : ℕ) (hq : 1 ≤ q) (x : IVIdx n p q) :
    Finset (BVec (Fin n)) := by
  classical
  exact Finset.univ.filter (fun b : BVec (Fin n) =>
    hammingNorm b = q ∧ restrict x.X b ∈ iiY x.X.card q (le_trans hq x.X_card_ge) x.X rfl x.cd)

/-- The `1`-entries covered by the rectangle indexed by `x`. -/
noncomputable def ivMem (n p q : ℕ) (hq : 1 ≤ q) (x : IVIdx n p q) :
    Finset (BlockEntries n p q) := by
  classical
  exact Finset.univ.filter (fun ab : BlockEntries n p q =>
    ab.1.1 ∈ ivRow n p q hq x ∧ ab.1.2 ∈ ivCol n p q hq x)

lemma mem_ivRow {n p q : ℕ} {hq : 1 ≤ q} {x : IVIdx n p q} {a : BVec (Fin n)} :
    a ∈ ivRow n p q hq x ↔ hammingNorm a = p ∧
      (1 - restrict x.X a) ∈ iiY x.X.card q (le_trans hq x.X_card_ge) x.X rfl x.cd := by
  classical
  unfold ivRow
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma mem_ivCol {n p q : ℕ} {hq : 1 ≤ q} {x : IVIdx n p q} {b : BVec (Fin n)} :
    b ∈ ivCol n p q hq x ↔ hammingNorm b = q ∧
      restrict x.X b ∈ iiY x.X.card q (le_trans hq x.X_card_ge) x.X rfl x.cd := by
  classical
  unfold ivCol
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The columns of a case-IV rectangle are supported in `X`. -/
lemma ivCol_support_subset {n p q : ℕ} {hq : 1 ≤ q} {x : IVIdx n p q} {b : BVec (Fin n)}
    (hb : b ∈ ivCol n p q hq x) : support b ⊆ x.X := by
  obtain ⟨hbn, hbc⟩ := mem_ivCol.mp hb
  rw [iiY, Set.mem_ofPred_eq] at hbc
  obtain ⟨hbcn, _⟩ := hbc
  have hcard : (x.X ∩ support b).card = q := by
    rw [← support_restrict_inter_card x.X b, ← hammingNorm_eq_support]
    exact hbcn
  have hsub : x.X ∩ support b ⊆ support b := Finset.inter_subset_right
  have hle : (support b).card ≤ (x.X ∩ support b).card := by
    rw [hcard, ← hammingNorm_eq_support, hbn]
  have heq : x.X ∩ support b = support b := Finset.eq_of_subset_of_card_le hsub hle
  rw [← heq]; exact Finset.inter_subset_left

/-- `suppL X a ∩ suppL X b = supp a ∩ supp b` when `supp b ⊆ X`. -/
lemma suppL_inter_eq {n : ℕ} (X : Finset (Fin n)) (a b : BVec (Fin n)) (hb : support b ⊆ X) :
    suppL X a ∩ suppL X b = support a ∩ support b := by
  ext i
  simp only [suppL, support, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨_, ha⟩, _, hb'⟩; exact ⟨ha, hb'⟩
  · rintro ⟨ha, hb'⟩
    have hi : i ∈ X := hb (by rw [support]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb'⟩)
    exact ⟨⟨hi, ha⟩, ⟨hi, hb'⟩⟩

/-- `interCard` may be computed after restricting both vectors to `X`, when `supp b ⊆ X`. -/
lemma interCard_restrict_eq_of_subset {n : ℕ} {X : Finset (Fin n)} {a b : BVec (Fin n)}
    (hb : support b ⊆ X) : interCard a b = interCard (restrict X a) (restrict X b) := by
  rw [interCard_eq_support_inter (restrict X a) (restrict X b), card_support_restrict_inter,
    suppL_inter_eq X a b hb, ← interCard_eq_support_inter a b]

lemma interCard_comm {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : BVec ι) :
    interCard x y = interCard y x := by
  rw [interCard_eq_support_inter, interCard_eq_support_inter, Finset.inter_comm]

lemma disjoint_support_of_interCard_zero {n : ℕ} {a b : BVec (Fin n)} (hab : interCard a b = 0) :
    Disjoint (support a) (support b) := by
  rw [Finset.disjoint_left]; intro i hia hib
  have hmem : i ∈ support a ∩ support b := Finset.mem_inter.mpr ⟨hia, hib⟩
  have hc : (support a ∩ support b).card = 0 := by rw [← interCard_eq_support_inter, hab]
  rw [Finset.card_eq_zero] at hc
  rw [hc] at hmem
  exact absurd hmem (by simp)

/-- **Case IV, legality.**  The rectangle has no `0`-entry: the `X`-parts of a row and a column
lie in complementary parts of the same 3-code, so their common `1`-count is `0` or `≥ 2`. -/
theorem ivRect_isRect (n p q : ℕ) (hq : 1 ≤ q) (x : IVIdx n p q) :
    IsRectangle (ivRow n p q hq x) (ivCol n p q hq x) := by
  intro a ha b hb
  obtain ⟨han, hacode⟩ := mem_ivRow.mp ha
  obtain ⟨hbn, hbcode⟩ := mem_ivCol.mp hb
  rw [iiY, Set.mem_ofPred_eq] at hacode hbcode
  obtain ⟨hacn, hacg⟩ := hacode
  obtain ⟨hbcn, hbcg⟩ := hbcode
  have hbsub : support b ⊆ x.X := ivCol_support_subset hb
  rw [interCard_restrict_eq_of_subset hbsub]
  by_cases heq : (1 : BVec ↥x.X) - restrict x.X a = restrict x.X b
  · have h0 : interCard (restrict x.X a) (restrict x.X b) = 0 := by
      rw [← heq, interCard_self_one_sub]
    rw [h0]; norm_num
  · have hne : reindexBVec (phiS x.X rfl) ((1 : BVec ↥x.X) - restrict x.X a) ≠
        reindexBVec (phiS x.X rfl) (restrict x.X b) :=
      fun h => heq (reindexBVec_injective _ h)
    have hthree := iiGamma_threeCode x.X.card (le_trans hq x.X_card_ge) x.cd
      _ hacg _ hbcg hne
    rw [← reindexBVec_sub, hammingNorm_reindexBVec] at hthree
    have hsa := hammingNorm_sub_add ((1 : BVec ↥x.X) - restrict x.X a) (restrict x.X b)
    rw [hacn, hbcn] at hsa
    have hic : interCard ((1 : BVec ↥x.X) - restrict x.X a) (restrict x.X b) ≤ q - 2 := by omega
    have hb2 : (1 : BVec ↥x.X) - (1 - restrict x.X a) = restrict x.X a := by abel
    have hbase := interCard_one_sub (restrict x.X b) ((1 : BVec ↥x.X) - restrict x.X a)
    rw [interCard_comm (restrict x.X b) ((1 : BVec ↥x.X) - restrict x.X a), hbcn, hb2,
        interCard_comm (restrict x.X b) (restrict x.X a)] at hbase
    rw [hbase]; omega

/-- Every covering set of the case-IV family has size `≤ 4^n`. -/
lemma ivMem_card_le (n p q : ℕ) (hq : 1 ≤ q) (x : IVIdx n p q) :
    (ivMem n p q hq x).card ≤ 4 ^ n :=
  (Finset.card_le_univ _).trans (card_BlockEntries_le n p q)

/-- Case-IV certificates for the `1`-entry `(a,b)`: a subset `Y ⊆ supp a`. -/
abbrev IVCert (n : ℕ) (a : BVec (Fin n)) : Type := {Y : Finset (Fin n) // Y ⊆ support a}

lemma card_IVCert (n : ℕ) (a : BVec (Fin n)) :
    Fintype.card (IVCert n a) = 2 ^ (support a).card := by
  have e : IVCert n a ≃ ↥(support a).powerset :=
    { toFun := fun Y => ⟨Y.1, Finset.mem_powerset.mpr Y.2⟩
      invFun := fun Y => ⟨Y.1, Finset.mem_powerset.mp Y.2⟩
      left_inv := fun Y => Subtype.ext rfl
      right_inv := fun Y => Subtype.ext rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_powerset]

/-- The rectangle covering the `1`-entry `(a,b)` from the certificate `Y`: the outer set is
`X = supp b ∪ Y`, coded by the code part of `b` in `B^X`. -/
noncomputable def ivCertFwd {n p q : ℕ} {a b : BVec (Fin n)} (hq : 1 ≤ q)
    (hb : hammingNorm b = q) (hdisj : Disjoint (support a) (support b)) (Y : IVCert n a) :
    IVIdx n p q := by
  classical
  let X : Finset (Fin n) := support b ∪ Y.1
  have hXge : q ≤ X.card := by
    show q ≤ (support b ∪ Y.1).card
    rw [Finset.card_union_of_disjoint (hdisj.symm.mono_right Y.2), ← hammingNorm_eq_support, hb]
    omega
  have hX1 : 1 ≤ X.card := le_trans hq hXge
  exact ⟨⟨X, hXge⟩, iiPart hX1 (reindexBVec (phiS X rfl) (restrict X b))⟩

@[simp] lemma ivCertFwd_X {n p q : ℕ} {a b : BVec (Fin n)} {hq : 1 ≤ q}
    (hb : hammingNorm b = q) (hdisj : Disjoint (support a) (support b)) (Y : IVCert n a) :
    (ivCertFwd (p := p) hq hb hdisj Y).X = support b ∪ Y.1 := rfl

lemma ivCertFwd_col {n p q : ℕ} {a b : BVec (Fin n)} {hq : 1 ≤ q}
    (hb : hammingNorm b = q) (hdisj : Disjoint (support a) (support b)) (Y : IVCert n a) :
    b ∈ ivCol n p q hq (ivCertFwd hq hb hdisj Y) := by
  classical
  have hnorm : hammingNorm (restrict (support b ∪ Y.1) b) = q := by
    rw [hammingNorm_restrict_of_subset Finset.subset_union_left, hb]
  rw [mem_ivCol]
  refine ⟨hb, ?_⟩
  rw [iiY, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · exact hnorm
  · exact iiPart_spec _ _

lemma ivCertFwd_row {n p q : ℕ} {a b : BVec (Fin n)} {hq : 1 ≤ q} (ha : hammingNorm a = p)
    (hb : hammingNorm b = q) (hdisj : Disjoint (support a) (support b)) (Y : IVCert n a) :
    a ∈ ivRow n p q hq (ivCertFwd hq hb hdisj Y) := by
  classical
  have hd : Disjoint (support b) Y.1 := hdisj.symm.mono_right Y.2
  have hXcard : (support b ∪ Y.1).card = q + Y.1.card := by
    rw [Finset.card_union_of_disjoint hd, ← hammingNorm_eq_support, hb]
  have hint : (support b ∪ Y.1) ∩ support a = Y.1 := by
    rw [Finset.union_inter_distrib_right, Finset.disjoint_iff_inter_eq_empty.mp hdisj.symm,
      Finset.empty_union]
    ext i
    rw [Finset.mem_inter]
    exact ⟨fun h => h.1, fun h => ⟨h, Y.2 h⟩⟩
  have hnorm : hammingNorm ((1 : BVec ↥(support b ∪ Y.1)) - restrict (support b ∪ Y.1) a) = q := by
    rw [hammingNorm_one_sub, Fintype.card_coe, hXcard]
    have hr : hammingNorm (restrict (support b ∪ Y.1) a) = Y.1.card := by
      rw [hammingNorm_eq_support, support_restrict_inter_card, hint]
    rw [hr]; omega
  have hveq : (1 : BVec ↥(support b ∪ Y.1)) - restrict (support b ∪ Y.1) a
      = restrict (support b ∪ Y.1) b := by
    funext j
    rw [Pi.sub_apply, Pi.one_apply, restrict_apply, restrict_apply]
    have hjmem : (j : Fin n) ∈ support b ∪ Y.1 := j.2
    rw [Finset.mem_union] at hjmem
    rcases hjmem with hbj | hY
    · have hbj' : b (j : Fin n) ≠ 0 := by simpa [support] using hbj
      have haj : a (j : Fin n) = 0 := by
        by_contra hc
        exact (Finset.disjoint_left.mp hdisj) (by simpa [support] using hc)
          (by simpa [support] using hbj')
      rw [haj, zmod_two_eq_one hbj']; norm_num
    · have haj' : a (j : Fin n) ≠ 0 := by simpa [support] using Y.2 hY
      have hbj0 : b (j : Fin n) = 0 := by
        by_contra hc
        have hmem : (j : Fin n) ∈ support b ∩ Y.1 :=
          Finset.mem_inter.mpr ⟨by simpa [support] using hc, hY⟩
        rw [Finset.disjoint_iff_inter_eq_empty.mp hd] at hmem
        simpa using hmem
      rw [zmod_two_eq_one haj', hbj0]; norm_num
  rw [mem_ivRow]
  refine ⟨ha, ?_⟩
  rw [iiY, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · exact hnorm
  · rw [show ((1 : BVec ↥(ivCertFwd (p := p) hq hb hdisj Y).X) -
          restrict (ivCertFwd (p := p) hq hb hdisj Y).X a)
        = restrict (support b ∪ Y.1) b from hveq]
    exact iiPart_spec _ _

lemma ivCertFwd_mem {n p q : ℕ} {a b : BVec (Fin n)} {hq : 1 ≤ q} (ha : hammingNorm a = p)
    (hb : hammingNorm b = q) (hab : interCard a b = 0) (Y : IVCert n a) :
    (⟨(a, b), ha, hb, hab⟩ : BlockEntries n p q) ∈
      ivMem n p q hq (ivCertFwd hq hb (disjoint_support_of_interCard_zero hab) Y) := by
  classical
  rw [ivMem, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, ivCertFwd_row ha hb _ Y, ivCertFwd_col hb _ Y⟩

lemma ivCertFwd_injective {n p q : ℕ} {a b : BVec (Fin n)} {hq : 1 ≤ q}
    (hb : hammingNorm b = q) (hdisj : Disjoint (support a) (support b)) :
    Function.Injective (ivCertFwd (p := p) hq hb hdisj) := by
  intro Y₁ Y₂ h
  apply Subtype.ext
  have hX : support b ∪ Y₁.1 = support b ∪ Y₂.1 := by
    have hh := congrArg (fun x : IVIdx n p q => x.X) h
    rwa [ivCertFwd_X hb hdisj Y₁, ivCertFwd_X hb hdisj Y₂] at hh
  have hd : support b ∩ support a = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hdisj.symm
  have e1 : (support b ∪ Y₁.1) ∩ support a = Y₁.1 := by
    rw [Finset.union_inter_distrib_right, hd, Finset.empty_union]
    ext i
    rw [Finset.mem_inter]
    exact ⟨fun h => h.1, fun h => ⟨h, Y₁.2 h⟩⟩
  have e2 : (support b ∪ Y₂.1) ∩ support a = Y₂.1 := by
    rw [Finset.union_inter_distrib_right, hd, Finset.empty_union]
    ext i
    rw [Finset.mem_inter]
    exact ⟨fun h => h.1, fun h => ⟨h, Y₂.2 h⟩⟩
  rw [← e1, hX, e2]

/-- **Case IV, uniform degree.**  Every `1`-entry of the `(p,q)`-block is covered by at least
`2^p` members of the case-IV family. -/
lemma ivDeg_lower (n p q : ℕ) (hq : 1 ≤ q) (x : BlockEntries n p q) :
    2 ^ p ≤ (Finset.univ.filter (fun i : IVIdx n p q => x ∈ ivMem n p q hq i)).card := by
  classical
  have hcert : Fintype.card (IVCert n x.1.1) = 2 ^ p := by
    rw [card_IVCert, ← hammingNorm_eq_support, x.2.1]
  rw [← hcert]
  have hinj : Function.Injective (fun Y : IVCert n x.1.1 =>
      (⟨ivCertFwd hq x.2.2.1 (disjoint_support_of_interCard_zero x.2.2.2) Y,
        ivCertFwd_mem x.2.1 x.2.2.1 x.2.2.2 Y⟩ :
        {i : IVIdx n p q // x ∈ ivMem n p q hq i})) := by
    intro Y₁ Y₂ h
    exact ivCertFwd_injective (hq := hq) x.2.2.1 (disjoint_support_of_interCard_zero x.2.2.2)
      (congrArg Subtype.val h)
  have h := Fintype.card_le_of_injective _ hinj
  rw [show Fintype.card {i : IVIdx n p q // x ∈ ivMem n p q hq i}
        = (Finset.univ.filter (fun i : IVIdx n p q => x ∈ ivMem n p q hq i)).card
      from Fintype.card_subtype _] at h
  exact h

lemma card_IVIdx_le (n p q : ℕ) : Fintype.card (IVIdx n p q) ≤ 2 * n * 2 ^ n := by
  classical
  have hsigma : Fintype.card (IVIdx n p q)
      = ∑ X : {s : Finset (Fin n) // q ≤ s.card}, 2 * X.1.card := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
  rw [hsigma]
  have h1 : ∀ X : {s : Finset (Fin n) // q ≤ s.card}, 2 * X.1.card ≤ 2 * n := by
    intro X
    have hle : X.1.card ≤ n := by
      have := Finset.card_le_card (Finset.subset_univ X.1)
      rwa [Finset.card_univ, Fintype.card_fin] at this
    omega
  calc ∑ X : {s : Finset (Fin n) // q ≤ s.card}, 2 * X.1.card
      ≤ ∑ _X : {s : Finset (Fin n) // q ≤ s.card}, 2 * n := Finset.sum_le_sum (fun X _ => h1 X)
    _ = (Fintype.card {s : Finset (Fin n) // q ≤ s.card}) * (2 * n) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ 2 ^ n * (2 * n) :=
        Nat.mul_le_mul_right _ (le_trans (Fintype.card_subtype_le _) (le_of_eq (card_finset_fin n)))
    _ = 2 * n * 2 ^ n := by ring

lemma two_pow_le_three_halves {n k : ℕ} (hk : 2 * k ≤ n) : (2:ℝ)^k ≤ ((3:ℝ)/2)^n := by
  have h2 : (2:ℝ)^k * (2:ℝ)^k = (2:ℝ)^(2*k) := by rw [← pow_add]; ring_nf
  have hsq : ((2:ℝ)^k)^2 ≤ (((3:ℝ)/2)^n)^2 := by
    calc ((2:ℝ)^k)^2 = (2:ℝ)^k * (2:ℝ)^k := by ring
      _ = (2:ℝ)^(2*k) := h2
      _ ≤ (2:ℝ)^n := pow_le_pow_right₀ (by norm_num) hk
      _ ≤ ((9:ℝ)/4)^n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
      _ = (((3:ℝ)/2)^n)^2 := by rw [sq, ← mul_pow]; norm_num
  have h := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h

lemma iv_ratio_bound (n p q : ℕ) (hp : p ≤ n) (h2p : n ≤ 2 * p) :
    (Fintype.card (IVIdx n p q) : ℝ) / ((2:ℝ) ^ p) ≤ (2:ℝ) * (n:ℝ) * ((3:ℝ)/2) ^ n := by
  have hc := card_IVIdx_le n p q
  have hcR : (Fintype.card (IVIdx n p q) : ℝ) ≤ (2:ℝ) * (n:ℝ) * (2:ℝ)^n := by
    have h := (Nat.cast_le (α := ℝ)).mpr hc
    push_cast at h ⊢
    exact h
  have hkp : 2 * (n - p) ≤ n := by omega
  have hrat : (2:ℝ)^(n-p) ≤ ((3:ℝ)/2)^n := two_pow_le_three_halves hkp
  calc (Fintype.card (IVIdx n p q) : ℝ) / (2:ℝ)^p
      ≤ ((2:ℝ) * (n:ℝ) * (2:ℝ)^n) / (2:ℝ)^p :=
        div_le_div_of_nonneg_right hcR (by positivity)
    _ = (2:ℝ) * (n:ℝ) * (2:ℝ)^(n-p) := by
        rw [div_eq_iff (by positivity : ((2:ℝ)^p) ≠ 0)]
        rw [show (2:ℝ)^n = (2:ℝ)^(n-p) * (2:ℝ)^p from by rw [← pow_add]; congr 1; omega]
        ring
    _ ≤ (2:ℝ) * (n:ℝ) * ((3:ℝ)/2)^n := by
        apply mul_le_mul_of_nonneg_left hrat; positivity

/-- **Case IV.**  If `p + q ≤ n`, `n ≤ 2p` and `q ≥ 1` (so `α ≥ 1/2`), the `(p,q)`-block is
covered by at most `(1 + n log 4)·2n·(3/2)^n` rectangles. -/
lemma blockCover_caseIV (n p q : ℕ) (hpq : p + q ≤ n) (h2p : n ≤ 2 * p) (hq : 1 ≤ q) :
    ∃ k, HasBlockCover n p q k ∧
      (k : ℝ) ≤ (1 + (n:ℝ) * Real.log 4) * (2 * (n:ℝ)) * ((3:ℝ)/2)^n := by
  classical
  have hn : q ≤ n := by omega
  haveI : Nonempty (IVIdx n p q) := by
    refine ⟨⟨⟨Finset.univ, by rw [Finset.card_univ, Fintype.card_fin]; exact hn⟩, ⟨0, ?_⟩⟩⟩
    rw [Finset.card_univ, Fintype.card_fin]; omega
  obtain ⟨I, hIcov, hIcard⟩ := lemma3_indexed (fun i : IVIdx n p q => ivMem n p q hq i)
    (2 ^ p) (4 ^ n) (Nat.one_le_pow p 2 (by norm_num)) (fun i => ivMem_card_le n p q hq i)
    (fun x => ivDeg_lower n p q hq x)
  have hcover : HasBlockCover n p q I.card := by
    refine hasBlockCover_of_card_eq (k := I.card) (ι := {i : IVIdx n p q // i ∈ I})
      (by rw [Fintype.card_subtype]; congr 1; ext i; simp)
      (fun i => ivRow n p q hq i.1) (fun i => ivCol n p q hq i.1)
      (fun i => ivRect_isRect n p q hq i.1) ?_
    intro a b ha hb hab
    obtain ⟨i, hiI, hi⟩ := hIcov ⟨(a, b), ha, hb, hab⟩
    rw [ivMem, Finset.mem_filter] at hi
    exact ⟨⟨i, hiI⟩, hi.2.1, hi.2.2⟩
  refine ⟨I.card, hcover, ?_⟩
  have hlog : Real.log (((4:ℕ)^n : ℕ) : ℝ) = (n:ℝ) * Real.log 4 := by
    rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
  have hratio := iv_ratio_bound n p q (by omega) h2p
  have hfac : (0:ℝ) ≤ 1 + (n:ℝ) * Real.log 4 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4); nlinarith [Nat.cast_nonneg (α := ℝ) n]
  refine hIcard.trans ?_
  rw [hlog]
  calc (1 + (n:ℝ) * Real.log 4) * (Fintype.card (IVIdx n p q) : ℝ) / ((2 ^ p : ℕ) : ℝ)
      = (1 + (n:ℝ) * Real.log 4) * ((Fintype.card (IVIdx n p q) : ℝ) / (2:ℝ)^p) := by
        push_cast; ring
    _ ≤ (1 + (n:ℝ) * Real.log 4) * ((2:ℝ) * (n:ℝ) * ((3:ℝ)/2)^n) :=
        mul_le_mul_of_nonneg_left hratio hfac
    _ = (1 + (n:ℝ) * Real.log 4) * (2 * (n:ℝ)) * ((3:ℝ)/2)^n := by ring

end CaseIV

/-! ### Transposition symmetry of the blocks -/

lemma blockCover_swap {n p q k : ℕ} (h : HasBlockCover n p q k) : HasBlockCover n q p k := by
  obtain ⟨R, C, hrect, hcov⟩ := h
  refine ⟨C, R, ?_, ?_⟩
  · intro i a ha b hb
    rw [interCard_comm]
    exact hrect i b hb a ha
  · intro a b ha hb hab
    obtain ⟨i, hi1, hi2⟩ := hcov b a hb ha (by rw [interCard_comm b a]; exact hab)
    exact ⟨i, hi2, hi1⟩

/-! ### Numeric helpers -/

lemma log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
  linarith

lemma log_four_le_two : Real.log 4 ≤ 2 := by
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  rw [h]; linarith [log_two_le_one]

lemma binEntropy_tenth_le_log_three_halves :
    Real.binEntropy ((1:ℝ)/10) ≤ Real.log ((3:ℝ)/2) := by
  have hp : ((1:ℝ)/10)⁻¹ = 10 := by norm_num
  have hq : (1 - (1:ℝ)/10) = (9:ℝ)/10 := by norm_num
  have hqi : ((9:ℝ)/10)⁻¹ = (10:ℝ)/9 := by norm_num
  have hlog9 : Real.log 9 = 2 * Real.log 3 := by
    rw [show (9:ℝ) = 3^2 by norm_num, Real.log_pow]; norm_num
  have hlog32 : Real.log ((3:ℝ)/2) = Real.log 3 - Real.log 2 :=
    Real.log_div (by norm_num) (by norm_num)
  have hkey : Real.log 10 + Real.log 2 ≤ (14/5) * Real.log 3 := by
    have h20 : Real.log 20 ≤ (14/5) * Real.log 3 := by
      have hpow : (20:ℝ)^5 ≤ (3:ℝ)^14 := by norm_num
      have h := Real.log_le_log (by positivity : (0:ℝ) < 20^5) hpow
      rw [Real.log_pow, Real.log_pow] at h
      push_cast at h
      linarith
    have hlog20 : Real.log 20 = Real.log 10 + Real.log 2 := by
      rw [show (20:ℝ) = 10 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith
  rw [Real.binEntropy, hp, hq, hqi,
      Real.log_div (by norm_num : (10:ℝ) ≠ 0) (by norm_num : (9:ℝ) ≠ 0), hlog9, hlog32]
  linarith

lemma two_pow_H2_tenth_le_three_halves : (2:ℝ)^(H2 ((1:ℝ)/10)) ≤ (3:ℝ)/2 := by
  rw [two_pow_H2_eq_exp]
  calc Real.exp (Real.binEntropy ((1:ℝ)/10)) ≤ Real.exp (Real.log ((3:ℝ)/2)) :=
        Real.exp_le_exp.mpr binEntropy_tenth_le_log_three_halves
    _ = (3:ℝ)/2 := Real.exp_log (by norm_num)

lemma two_pow_H2_tenth_le (n : ℕ) :
    (2:ℝ)^((n:ℝ) * H2 ((1:ℝ)/10)) ≤ ((3:ℝ)/2)^n := by
  have hbase : (2:ℝ)^(H2 ((1:ℝ)/10)) ≤ (3:ℝ)/2 := two_pow_H2_tenth_le_three_halves
  have heq : (2:ℝ)^((n:ℝ) * H2 ((1:ℝ)/10)) = ((2:ℝ)^(H2 ((1:ℝ)/10)))^n := by
    rw [mul_comm, ← Real.rpow_natCast, Real.rpow_mul (by norm_num)]
  rw [heq]
  exact pow_le_pow_left₀ (by positivity) hbase n

lemma one_le_nat_add_one (n : ℕ) : (1:ℝ) ≤ (n:ℝ)+1 := by
  have := Nat.cast_nonneg (α := ℝ) n; linarith

abbrev blockFac (n : ℕ) : ℝ := 6 * ((n:ℝ)+1)^5
noncomputable def blockPoly (n : ℕ) : ℝ := blockFac n * ((3:ℝ)/2)^n

lemma one_le_blockFac (n : ℕ) : (1:ℝ) ≤ blockFac n := by
  have h : (1:ℝ) ≤ ((n:ℝ)+1)^5 := one_le_pow₀ (one_le_nat_add_one n)
  have h0 : (0:ℝ) ≤ ((n:ℝ)+1)^5 := by positivity
  unfold blockFac; nlinarith

lemma one_add_nat_le_blockFac (n : ℕ) : (1:ℝ) + (n:ℝ) ≤ blockFac n := by
  have h1 : (1:ℝ) ≤ (n:ℝ)+1 := one_le_nat_add_one n
  have h5 : (n:ℝ)+1 ≤ ((n:ℝ)+1)^5 := by
    have := pow_le_pow_right₀ h1 (show (1:ℕ) ≤ 5 by norm_num)
    simpa using this
  unfold blockFac
  nlinarith [h5, Nat.cast_nonneg (α:=ℝ) n, h1]

lemma one_add_log2_le_blockFac (n : ℕ) : (1:ℝ) + (n:ℝ)*Real.log 2 ≤ blockFac n := by
  have hlog : Real.log 2 ≤ 1 := log_two_le_one
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  calc (1:ℝ) + (n:ℝ)*Real.log 2 ≤ 1 + (n:ℝ)*1 := by nlinarith
    _ = 1 + (n:ℝ) := by ring
    _ ≤ blockFac n := one_add_nat_le_blockFac n

lemma one_add_log4_le_three (n : ℕ) : (1:ℝ) + (n:ℝ)*Real.log 4 ≤ 3*((n:ℝ)+1) := by
  have hlog : Real.log 4 ≤ 2 := log_four_le_two
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  nlinarith

lemma caseIV_fac_le_blockFac (n : ℕ) :
    (1 + (n:ℝ)*Real.log 4) * (2*(n:ℝ)) ≤ blockFac n := by
  have h1 : (1:ℝ) + (n:ℝ)*Real.log 4 ≤ 3*((n:ℝ)+1) := one_add_log4_le_three n
  calc (1 + (n:ℝ)*Real.log 4) * (2*(n:ℝ))
      ≤ (3*((n:ℝ)+1)) * (2*((n:ℝ)+1)) := by
        apply mul_le_mul h1 ?_ (by positivity) (by positivity)
        nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    _ = 6*((n:ℝ)+1)^2 := by ring
    _ ≤ 6*((n:ℝ)+1)^5 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact pow_le_pow_right₀ (one_le_nat_add_one n) (by norm_num : 2 ≤ 5)
    _ = blockFac n := by unfold blockFac; ring

lemma caseII_fac_le_blockFac (n p q : ℕ) (hpq : p + q ≤ n) :
    (1 + (n:ℝ)*Real.log 4) * (2*(IIM n p q)*((n:ℝ)+1)^3) ≤ blockFac n := by
  have hIIM : IIM n p q ≤ n := by simp only [IIM]; omega
  have hIIMR : (IIM n p q : ℝ) ≤ (n:ℝ) := by exact_mod_cast hIIM
  have h1 : (1:ℝ) + (n:ℝ)*Real.log 4 ≤ 3*((n:ℝ)+1) := one_add_log4_le_three n
  have hX0 : (0:ℝ) ≤ ((n:ℝ)+1)^3 := by positivity
  have hstep : (1 + (n:ℝ)*Real.log 4) * (2*(IIM n p q)*((n:ℝ)+1)^3)
      ≤ (3*((n:ℝ)+1)) * (2*(n:ℝ)*((n:ℝ)+1)^3) := by
    apply mul_le_mul h1 _ (by positivity) (by positivity)
    nlinarith [hIIMR, hX0, Nat.cast_nonneg (α:=ℝ) (IIM n p q)]
  calc (1 + (n:ℝ)*Real.log 4) * (2*(IIM n p q)*((n:ℝ)+1)^3)
      ≤ (3*((n:ℝ)+1)) * (2*(n:ℝ)*((n:ℝ)+1)^3) := hstep
    _ = 6*(n:ℝ)*((n:ℝ)+1)^4 := by ring
    _ ≤ 6*((n:ℝ)+1)^5 := by
        have h0 : (0:ℝ) ≤ 6*((n:ℝ)+1)^4 := by positivity
        nlinarith [h0, Nat.cast_nonneg (α:=ℝ) n]
    _ = blockFac n := by unfold blockFac; ring

/-! ### Per-block bound and case dispatch -/

lemma blockCover_poly_ge (n : ℕ) (hn : 0 < n) (p q : ℕ) (hpq : p + q ≤ n) (hqp : q ≤ p) :
    ∃ k, HasBlockCover n p q k ∧ (k : ℝ) ≤ blockPoly n := by
  by_cases h1 : 10 * q ≤ n
  · obtain ⟨k, hk, hb⟩ := blockCover_caseI n p q hn hpq (Or.inl h1)
    exact ⟨k, hk, (hb.trans (two_pow_H2_tenth_le n)).trans
      (le_mul_of_one_le_left (by positivity) (one_le_blockFac n))⟩
  · by_cases h2 : 10 * (n - p) ≤ n
    · obtain ⟨k, hk, hb⟩ := blockCover_caseI n p q hn hpq (Or.inr h2)
      exact ⟨k, hk, (hb.trans (two_pow_H2_tenth_le n)).trans
        (le_mul_of_one_le_left (by positivity) (one_le_blockFac n))⟩
    · by_cases h3 : 2 * (p + q) ≤ n
      · obtain ⟨k, hk, hb⟩ := blockCover_caseIII n p q hpq
        refine ⟨k, hk, hb.trans ?_⟩
        have h23 : (2:ℝ)^(p+q) ≤ ((3:ℝ)/2)^n := two_pow_le_three_halves h3
        calc (1 + (n:ℝ)*Real.log 2) * (2:ℝ)^(p+q)
            ≤ blockFac n * ((3:ℝ)/2)^n :=
              mul_le_mul (one_add_log2_le_blockFac n) h23 (by positivity) (by positivity)
          _ = blockPoly n := rfl
      · by_cases h4 : 2 * p ≤ n
        · have h2q : 2 * q ≤ n := by omega
          have hlo : n ≤ 2 * p + 2 * q := by omega
          have hM : 1 ≤ IIM n p q := by simp only [IIM]; omega
          obtain ⟨k, hk, hb⟩ := blockCover_caseII n p q hM h4 h2q hpq hlo
          refine ⟨k, hk, hb.trans ?_⟩
          calc (1 + (n:ℝ)*Real.log 4) * (2*(IIM n p q)*((n:ℝ)+1)^3) * ((3:ℝ)/2)^n
              ≤ blockFac n * ((3:ℝ)/2)^n :=
                mul_le_mul_of_nonneg_right (caseII_fac_le_blockFac n p q hpq) (by positivity)
            _ = blockPoly n := rfl
        · have h2p : n ≤ 2 * p := by omega
          have hq1 : 1 ≤ q := by omega
          obtain ⟨k, hk, hb⟩ := blockCover_caseIV n p q hpq h2p hq1
          refine ⟨k, hk, hb.trans ?_⟩
          calc (1 + (n:ℝ)*Real.log 4) * (2*(n:ℝ)) * ((3:ℝ)/2)^n
              ≤ blockFac n * ((3:ℝ)/2)^n :=
                mul_le_mul_of_nonneg_right (caseIV_fac_le_blockFac n) (by positivity)
            _ = blockPoly n := rfl

lemma blockCover_poly (n : ℕ) (hn : 0 < n) (p q : ℕ) (hpq : p + q ≤ n) :
    ∃ k, HasBlockCover n p q k ∧ (k : ℝ) ≤ blockPoly n := by
  by_cases hqp : q ≤ p
  · exact blockCover_poly_ge n hn p q hpq hqp
  · obtain ⟨k, hk, hb⟩ := blockCover_poly_ge n hn q p (by omega) (by omega)
    exact ⟨k, blockCover_swap hk, hb⟩

/-! ### Theorem 2 -/

/-- **Theorem 2.**  The covering rank of the unique-disjointness matrix satisfies
`rk∨ Uₙ ≤ n^{O(1)} (3/2)^n`: there are constants `c`, `d` with `(rk∨ Uₙ : ℝ) ≤ c (n+1)^d (3/2)^n`
for all `n` (explicitly `c = 6`, `d = 7`). -/
theorem theorem2 : ∃ (c : ℝ) (d : ℕ), ∀ n : ℕ,
    (coverRank n : ℝ) ≤ c * ((n:ℝ)+1)^d * ((3:ℝ)/2)^n := by
  refine ⟨6, 7, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    have h : coverRank 0 ≤ 1 := by
      have := coverRank_le (hasCoverFin_of_hasPartFin (hasPartFin_four 0))
      simpa using this
    have h1 : (coverRank 0 : ℝ) ≤ 1 := by exact_mod_cast h
    norm_num
    linarith
  · have hb : ∀ pq : BlockIdx n,
        ∃ k, HasBlockCover n (pq.1.1 : ℕ) (pq.1.2 : ℕ) k ∧ (k : ℝ) ≤ blockPoly n :=
      fun pq => blockCover_poly n hn (pq.1.1 : ℕ) (pq.1.2 : ℕ) pq.2
    let k : BlockIdx n → ℕ := fun pq => Classical.choose (hb pq)
    have hk : ∀ pq, HasBlockCover n (pq.1.1 : ℕ) (pq.1.2 : ℕ) (k pq) :=
      fun pq => (Classical.choose_spec (hb pq)).1
    have hkb : ∀ pq, (k pq : ℝ) ≤ blockPoly n :=
      fun pq => (Classical.choose_spec (hb pq)).2
    have hcover : HasCoverFin n (Fintype.card (Σ pq : BlockIdx n, Fin (k pq))) :=
      hasCoverFin_of_blocks n k hk
    have hle : coverRank n ≤ Fintype.card (Σ pq : BlockIdx n, Fin (k pq)) := coverRank_le hcover
    have hle' : (coverRank n : ℝ) ≤ (Fintype.card (Σ pq : BlockIdx n, Fin (k pq)) : ℝ) := by
      exact_mod_cast hle
    have hcard : (Fintype.card (Σ pq : BlockIdx n, Fin (k pq)) : ℝ)
        = ∑ pq : BlockIdx n, (k pq : ℝ) := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_fin]
      push_cast
      rfl
    have hsum : ∑ pq : BlockIdx n, (k pq : ℝ) ≤ ∑ _pq : BlockIdx n, blockPoly n :=
      Finset.sum_le_sum (fun pq _ => hkb pq)
    have hconst : ∑ _pq : BlockIdx n, blockPoly n
        = (Fintype.card (BlockIdx n) : ℝ) * blockPoly n := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hIdx : (Fintype.card (BlockIdx n) : ℝ) ≤ ((n:ℝ)+1)^2 := by
      have hnat : Fintype.card (BlockIdx n) ≤ (n+1)*(n+1) := by
        have := Fintype.card_subtype_le
          (fun pq : Fin (n+1) × Fin (n+1) => (pq.1 : ℕ) + (pq.2 : ℕ) ≤ n)
        rw [Fintype.card_prod, Fintype.card_fin] at this
        simpa using this
      have := (Nat.cast_le (α := ℝ)).mpr hnat
      push_cast at this
      simpa [pow_two] using this
    calc (coverRank n : ℝ)
        ≤ (Fintype.card (Σ pq : BlockIdx n, Fin (k pq)) : ℝ) := hle'
      _ = ∑ pq : BlockIdx n, (k pq : ℝ) := hcard
      _ ≤ ∑ _pq : BlockIdx n, blockPoly n := hsum
      _ = (Fintype.card (BlockIdx n) : ℝ) * blockPoly n := hconst
      _ ≤ ((n:ℝ)+1)^2 * blockPoly n := by
          apply mul_le_mul_of_nonneg_right hIdx
          unfold blockPoly blockFac; positivity
      _ = 6 * ((n:ℝ)+1)^7 * ((3:ℝ)/2)^n := by unfold blockPoly blockFac; ring

end Udisj.Covering
