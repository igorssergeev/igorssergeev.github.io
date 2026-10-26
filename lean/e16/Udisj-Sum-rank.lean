/-
Formalisation of **Lemma 1** from the paper (here Lemma 2).

Setting (from the paper): `B = {0,1}`, a boolean vector `x = (x₁,…,xₙ) ∈ Bⁿ` has
(boolean / Hamming) weight `‖x‖ = ∑ᵢ xᵢ`, and a *3-code* in `Bⁿ` is a set `X` with
`‖x − y‖ ≥ 3` for all distinct `x, y ∈ X`.  The Hamming code `Hₙ ⊂ B^{2ⁿ−1}` is the
`GF(2)`-span of the rows of `Bₙ = [E_{2ⁿ−n−1} | Gₙ]`, where `E_m` is the identity and
`Gₙ` collects all `2ⁿ−n−1` distinct length-`n` boolean rows of weight `≥ 2`.

We model boolean vectors over `ZMod 2` (`= GF(2)`, so `x − y = x ⊕ y`).  A codeword is
a pair `(a, b)`: the `E`-segment `a` (the information word) and the `G`-segment `b`.
Its weight is the weight of the concatenation, `cwWeight (a,b) = ‖a‖ + ‖b‖`.  The code is
the range of the systematic encoding `a ↦ (a, a·G)`; its rows are exactly `[E | G]`.

Lemma 1 then says: any non-zero codeword has weight `≥ 3` (the proof of the paper simply
splits on the number `k` of summed rows, `k = |support a|`).

**Corollary 1** says the cube `B^{2ⁿ−1}` partitions into radius-`1` balls centred at the points
of `Hₙ`.  We prove it by combining the pairwise disjointness of the balls (Lemma 1 plus the
Hamming triangle inequality, `ball_disjoint`) with a covering argument (`hamming_ball_cover`):
the syndrome `s = v − u·Gₙ` of a point is `0`/a unit vector, or is itself a `Gₙ`-row, in each
case putting the point within distance `1` of a codeword.  The paper's cardinal argument is
recorded as well (`card_Grows`, `card_ball`, `card_cube`, `card_hammingCode`, `card_mul_ball`).

**Lemma 2** says the cube `Bⁿ` can be partitioned into `2n` parts that are 3-codes.  Following
the paper, we take the least `m` with `n ≤ 2^m − 1`, use the ball decomposition of `B^{2^m−1}`
(Corollary 1) — splitting each ball into its centre and the `2^m − 1` single-coordinate flips
gives the sets `C₀, …, C_{2^m−1}` (`paperSets`, each a 3-code) — and restrict them to `Bⁿ`
along an injection of coordinates (`embC`, `Gamma`).  Since `2^{m−1} ≤ n`, the number of parts
is `2^m ≤ 2n` (the paper's `N + 1 = 2^m ≤ 2n`).  See `lemma2`.

We also formalise the paper's **inequality `(2)`**, the standard two-sided binomial estimate
`1/n · 2^{nH(k/n)} ≼ Cⁿ_k ≼ 2^{nH(k/n)}` (as `min {k, n − k} → ∞`), where
`H x = −x log₂ x − (1 − x) log₂ (1 − x)` is the binary entropy.  This is a general fact about
binomial coefficients (not part of the Hamming-code development), proved in the `BinomialEntropy`
section below; see `choose_le_two_pow_H2` and `two_pow_H2_div_le_choose`.

Finally we formalise **Theorem 1**, the partition-rank bound for the paper's *unique disjointness
matrix* `Uₙ`: `rk⁺ Uₙ ≼ n³ (3/∛4)ⁿ ≺ 1.89ⁿ`.  We take `Uₙ[a,b] = 1` when the subsets `a, b ⊆ [n]`
are disjoint, `0` when they meet in exactly one point, and `*` otherwise; a *rectangle* is a
submatrix without `0`-entries and `rk⁺ Uₙ` is the least number of *pairwise disjoint* rectangles
that partition the `1`-entries (a rectangle may share a `*`-entry with another, but no `1`-entry
lies in two rectangles — see `HasPartFin`).
We prove the sharp, non-asymptotic bound `rk⁺ Uₙ ≤ 2 (n+1)³ · 2^{nH(1/3)} = 2 (n+1)³ (3/∛4)ⁿ`
(`theorem1`, `theorem1_paper`), by partitioning the `1`-entries according to the row/column weights:
rows of weight `≤ n/3` (`rowRect`), then columns of weight `≤ n/3` over the remaining rows
(`colRect`), and finally, for the middle range of weights, the paper's disjoint rectangles
`Rᵢ × R̄ᵢ` (`blockRect`) built from Lemma 2's cube-code partition (`cover_part` proves disjointness).
-/
import Mathlib

open Finset
open scoped BigOperators

namespace Udisj

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

omit [Fintype κ] [DecidableEq ι] in
lemma enc_fst (g : ι → BVec κ) (a : BVec ι) : (enc g a).1 = a := rfl

omit [Fintype κ] in
lemma enc_single (g : ι → BVec κ) (i : ι) :
    enc g (Pi.single i 1) = (Pi.single i 1, g i) := by
  have hsum : (∑ j, (Pi.single i (1 : ZMod 2) : BVec ι) j • g j) = g i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; rw [Pi.single_eq_of_ne hj, zero_smul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  simp only [enc, LinearMap.coe_mk, AddHom.coe_mk, hsum]

omit [DecidableEq ι] in
lemma weight_enc (g : ι → BVec κ) (a : BVec ι) :
    cwWeight (enc g a) = hammingNorm a + hammingNorm (∑ i, a i • g i) := rfl

/-- In `GF(2)` every element is `0` or `1`. -/
lemma zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

lemma zmod_two_eq_one {x : ZMod 2} (h : x ≠ 0) : x = 1 :=
  (zmod_two_eq_zero_or_one x).resolve_left h

/-- Core of Lemma 1 notation: if the `G`-rows `g` are pairwise distinct
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
(the row set of `Gₙ`). -/
abbrev Grows (n : ℕ) := {v : BVec (Fin n) // 2 ≤ hammingNorm v}

/-- **Lemma 1**.  For `n ∈ ℕ`, the Hamming code
`Hₙ = range (enc ·)` built from `Gₙ` is a 3-code: any two distinct codewords differ in
at least `3` coordinates, i.e. `cwWeight (x − y) ≥ 3`. -/
theorem lemma1 (n : ℕ) :
    ∀ x ∈ LinearMap.range (enc (fun v : Grows n => v.1)),
      ∀ y ∈ LinearMap.range (enc (fun v : Grows n => v.1)),
        x ≠ y → 3 ≤ cwWeight (x - y) := by
  intro x hx y hy hxy
  exact codeword_weight_ge_three (fun v : Grows n => v.1) Subtype.val_injective
    (fun v => v.2) (x - y) (sub_mem hx hy) (sub_ne_zero.mpr hxy)

/-! ## Corollary 1: the cube `B^{2ⁿ−1}` partitions into radius-`1` balls centred at `Hₙ` -/

/-- Generator of the `G`-rows of `Hₙ`: the `i`-th row of `Gₙ` is `i.1`. -/
def Gfun (n : ℕ) : Grows n → BVec (Fin n) := fun v => v.1

section HammingHelpers
variable {δ : Type*} [Fintype δ]

lemma hammingNorm_neg (x : δ → ZMod 2) : hammingNorm (-x) = hammingNorm x := by
  simp only [hammingNorm, Pi.neg_apply]
  congr 1
  ext i
  simp

/-- Subadditivity of the Hamming norm, from the Hamming distance triangle inequality. -/
lemma hammingNorm_add_le (x y : δ → ZMod 2) :
    hammingNorm (x + y) ≤ hammingNorm x + hammingNorm y := by
  have h := hammingDist_triangle (-x) 0 y
  rw [hammingDist_zero_right, hammingDist_zero_left] at h
  rw [hammingDist_eq_hammingNorm, neg_neg, hammingNorm_neg] at h
  exact h

end HammingHelpers

section Abstract
variable {α β : Type*} [Fintype α] [Fintype β]

lemma cwWeight_neg (x : BVec α × BVec β) : cwWeight (-x) = cwWeight x := by
  show hammingNorm (-x).1 + hammingNorm (-x).2 = hammingNorm x.1 + hammingNorm x.2
  rw [show (-x).1 = -(x.1) from rfl, show (-x).2 = -(x.2) from rfl]
  rw [hammingNorm_neg, hammingNorm_neg]

/-- Subadditivity of the codeword weight, componentwise from the Hamming norm. -/
lemma cwWeight_add_le (x y : BVec α × BVec β) :
    cwWeight (x + y) ≤ cwWeight x + cwWeight y := by
  simp only [cwWeight, Prod.fst_add, Prod.snd_add]
  have h1 := hammingNorm_add_le (δ := α) x.1 y.1
  have h2 := hammingNorm_add_le (δ := β) x.2 y.2
  omega

/-- Radius-`1` ball around a point `c` of the cube: `{x | ‖x − c‖ ≤ 1}`. -/
def ball (c : BVec α × BVec β) : Set (BVec α × BVec β) := {x | cwWeight (x - c) ≤ 1}

/-- Two radius-`1` balls are disjoint once their centres are at distance `≥ 3`; in
particular the balls centred at distinct points of a 3-code are disjoint 
(triangle-inequality argument: `‖c₁ − c₂‖ ≤ ‖c₁ − z‖ + ‖z − c₂‖ ≤ 2 < 3` at a common point). -/
lemma ball_disjoint {c1 c2 : BVec α × BVec β} (h : 3 ≤ cwWeight (c1 - c2)) :
    Disjoint (ball c1) (ball c2) := by
  rw [Set.disjoint_left]
  intro z hz1 hz2
  have hz1' : cwWeight (z - c1) ≤ 1 := hz1
  have hz2' : cwWeight (z - c2) ≤ 1 := hz2
  have h1 : cwWeight (c1 - z) ≤ 1 := by
    have : c1 - z = -(z - c1) := by abel
    rw [this, cwWeight_neg]; exact hz1'
  have hdecomp : c1 - c2 = (c1 - z) + (z - c2) := by abel
  have := cwWeight_add_le (c1 - z) (z - c2)
  rw [← hdecomp] at this
  omega

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

/-- **Corollary 1**.  For `n ∈ ℕ` the cube `B^{2ⁿ−1}` partitions into radius-`1`
balls centred at the points of the Hamming 3-code `Hₙ`: the balls are pairwise disjoint
(Lemma 1 plus the triangle inequality) and their union is the whole cube. -/
theorem corollary1 (n : ℕ) :
    (∀ c₁ ∈ hammingCode n, ∀ c₂ ∈ hammingCode n, c₁ ≠ c₂ →
        Disjoint (ball c₁) (ball c₂)) ∧
      Set.univ = ⋃ c ∈ hammingCode n, ball c := by
  constructor
  · intro c1 hc1 c2 hc2 hne
    exact ball_disjoint (lemma1 n c1 hc1 c2 hc2 hne)
  · rw [eq_comm]
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨c, hc, hy⟩ := hamming_ball_cover n y
    exact Set.mem_iUnion₂.mpr ⟨c, hc, hy⟩

/-! ## The counting facts behind Corollary 1

Proof of Corollary 1 counts points: `|Hₙ| = 2^{2ⁿ−n−1}`, a radius-`1` ball has `2ⁿ`
points, and `2^{2ⁿ−n−1} · 2ⁿ = 2^{2ⁿ−1} = |B^{2ⁿ−1}|`.  We record these cardinalities. -/

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

lemma enc_injective (g : α → BVec β) : Function.Injective (enc g) := by
  intro a b h
  have := congrArg Prod.fst h
  simpa [enc_fst] using this

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

lemma zero_notMem_images :
    (0 : BVec α × BVec β) ∉ Finset.univ.image (fun i : α => ((unitVec i : BVec α), (0 : BVec β)))
      ∪ Finset.univ.image (fun j : β => ((0 : BVec α), (unitVec j : BVec β))) := by
  rw [Finset.mem_union]; rintro (h | h)
  · rw [Finset.mem_image] at h; obtain ⟨i, -, hi⟩ := h
    exact unitVec_ne_zero i (congrArg Prod.fst hi)
  · rw [Finset.mem_image] at h; obtain ⟨j, -, hj⟩ := h
    exact unitVec_ne_zero j (congrArg Prod.snd hj)

lemma disjoint_images :
    Disjoint (Finset.univ.image (fun i : α => ((unitVec i : BVec α), (0 : BVec β))))
      (Finset.univ.image (fun j : β => ((0 : BVec α), (unitVec j : BVec β)))) := by
  rw [Finset.disjoint_left]
  intro y hyA hyB
  rw [Finset.mem_image] at hyA hyB
  obtain ⟨i, -, hi⟩ := hyA
  obtain ⟨j, -, hj⟩ := hyB
  exact unitVec_ne_zero i (congrArg Prod.fst (hi.trans hj.symm))

omit [Fintype α] [Fintype β] [DecidableEq β] in
lemma inl_injective : Function.Injective (fun i : α => ((unitVec i : BVec α), (0 : BVec β))) :=
  fun _ _ h => unitVec_injective (congrArg Prod.fst h)

omit [Fintype α] [Fintype β] [DecidableEq α] in
lemma inr_injective : Function.Injective (fun j : β => ((0 : BVec α), (unitVec j : BVec β))) :=
  fun _ _ h => unitVec_injective (congrArg Prod.snd h)

/-- A radius-`1` ball in `B^{α ⊕ β}` has `|α| + |β| + 1` points. -/
lemma card_weightOne :
    Fintype.card {y : BVec α × BVec β // cwWeight y ≤ 1}
      = Fintype.card α + Fintype.card β + 1 := by
  rw [Fintype.card_subtype]
  have hset : (Finset.univ.filter (fun y : BVec α × BVec β => cwWeight y ≤ 1))
      = insert 0 (Finset.univ.image (fun i : α => ((unitVec i : BVec α), (0 : BVec β)))
          ∪ Finset.univ.image (fun j : β => ((0 : BVec α), (unitVec j : BVec β)))) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_union,
      Finset.mem_image]
    constructor
    · intro h
      rcases eq_zero_or_of_cwWeight_le_one h with h0 | ⟨i, hi⟩ | ⟨j, hj⟩
      · exact Or.inl h0
      · exact Or.inr (Or.inl ⟨i, hi.symm⟩)
      · exact Or.inr (Or.inr ⟨j, hj.symm⟩)
    · rintro (rfl | ⟨i, rfl⟩ | ⟨j, rfl⟩)
      · simp [cwWeight]
      · simp [cwWeight, hammingNorm_unitVec]
      · simp [cwWeight, hammingNorm_unitVec]
  rw [hset, Finset.card_insert_of_notMem zero_notMem_images,
      Finset.card_union_of_disjoint disjoint_images,
      Finset.card_image_of_injective (Finset.univ) inl_injective,
      Finset.card_image_of_injective (Finset.univ) inr_injective,
      Finset.card_univ, Finset.card_univ]

/-- Translating a radius-`1` ball by its centre. -/
lemma ball_card_eq (c : BVec α × BVec β) :
    Fintype.card {x : BVec α × BVec β // cwWeight (x - c) ≤ 1}
      = Fintype.card {y : BVec α × BVec β // cwWeight y ≤ 1} :=
  Fintype.card_congr
    { toFun := fun x => ⟨x.1 - c, x.2⟩
      invFun := fun y => ⟨y.1 + c, by simpa using y.2⟩
      left_inv := fun x => by apply Subtype.ext; simp
      right_inv := fun y => by apply Subtype.ext; simp }

end BallCount

/-- A radius-`1` ball in `B^{2ⁿ−1}` contains `2ⁿ` points. -/
theorem card_ball (n : ℕ) (c : BVec (Grows n) × BVec (Fin n)) :
    Fintype.card {x : BVec (Grows n) × BVec (Fin n) // cwWeight (x - c) ≤ 1} = 2 ^ n := by
  rw [ball_card_eq, card_weightOne, card_Grows, Fintype.card_fin]
  have h : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt n.lt_two_pow_self
  omega

/-- The cube `B^{2ⁿ−1}` has `2^{2ⁿ−1}` points. -/
theorem card_cube (n : ℕ) :
    Fintype.card (BVec (Grows n) × BVec (Fin n)) = 2 ^ (2 ^ n - 1) := by
  rw [Fintype.card_prod, card_BVec, card_BVec, card_Grows, Fintype.card_fin, ← pow_add]
  congr 1
  have h : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt n.lt_two_pow_self
  omega

/-- `Hₙ` contains `2^{2ⁿ−n−1}` points (as a set, the range of the encoder). -/
theorem card_hammingCode (n : ℕ) :
    Fintype.card (Set.range (enc (Gfun n))) = 2 ^ (2 ^ n - n - 1) := by
  rw [Set.card_range_of_injective (f := enc (Gfun n)) (enc_injective (Gfun n)), card_BVec,
    card_Grows]

/-- Count: `|Hₙ| · 2ⁿ = 2^{2ⁿ−1}`, i.e. the balls centred at `Hₙ` cover the cube. -/
theorem card_mul_ball (n : ℕ) :
    Fintype.card (Set.range (enc (Gfun n))) * 2 ^ n = 2 ^ (2 ^ n - 1) := by
  rw [card_hammingCode, ← pow_add]
  congr 1
  have h : n + 1 ≤ 2 ^ n := Nat.succ_le_of_lt n.lt_two_pow_self
  omega

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

theorem coordUnit_injective {m : ℕ} :
    Function.Injective (coordUnit : Coord m → BVec (Grows m) × BVec (Fin m)) := by
  intro δ δ' h
  rcases δ with i | j <;> rcases δ' with i' | j'
  · have hh : (unitVec i : BVec (Grows m)) = unitVec i' := by
      simpa [coordUnit] using congrArg Prod.fst h
    rw [unitVec_injective hh]
  · exact absurd (show (unitVec i : BVec (Grows m)) = 0 by
        simpa [coordUnit] using congrArg Prod.fst h) (unitVec_ne_zero i)
  · exact absurd (show (unitVec j : BVec (Fin m)) = 0 by
        simpa [coordUnit] using congrArg Prod.snd h) (unitVec_ne_zero j)
  · have hh : (unitVec j : BVec (Fin m)) = unitVec j' := by
      simpa [coordUnit] using congrArg Prod.snd h
    rw [unitVec_injective hh]

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

/-- **Lemma 2** (paper form).  For `n ∈ ℕ` with `n ≥ 1`, the cube `Bⁿ` can be partitioned into
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

lemma choose_succ_cast (n m : ℕ) (hm : m ≤ n) :
    (n.choose (m+1) : ℝ) * ((m:ℝ)+1) = (n.choose m : ℝ) * ((n:ℝ) - m) := by
  have h := Nat.choose_succ_right_eq n m
  have hcast : ((n.choose (m+1) * (m+1) : ℕ) : ℝ) = ((n.choose m * (n-m) : ℕ) : ℝ) := by rw [h]
  push_cast at hcast
  rw [hcast, Nat.cast_sub hm]

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

lemma entropy_div_le_choose_prod (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    (1/(n+1)) * (((n:ℝ)/k)^k * ((n:ℝ)/((n-k:ℕ):ℝ))^(n-k)) ≤ (n.choose k : ℝ) := by
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
  have hsum1 : (∑ j ∈ range (n+1), x^j * y^(n-j) * (n.choose j : ℝ)) = 1 := by
    rw [← add_pow x y n, hxy, one_pow]
  have htnn : ∀ j, (0:ℝ) ≤ x^j * y^(n-j) * (n.choose j : ℝ) := by
    intro j
    exact mul_nonneg (mul_nonneg (pow_nonneg hx0.le j) (pow_nonneg hy0.le (n-j)))
      (Nat.cast_nonneg _)
  have hkey : ∀ m, m < k → y * (n.choose m : ℝ) ≤ x * (n.choose (m+1) : ℝ) := by
    intro m hm
    have hmle : m ≤ n := le_trans (le_of_lt hm) (le_of_lt hkn)
    have hnat : ((n-k:ℕ):ℝ) * ((m:ℝ)+1) ≤ (k:ℝ) * ((n:ℝ) - m) := by
      rw [Nat.cast_sub (le_of_lt hkn)]
      have hm1k : (m:ℝ) + 1 ≤ (k:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hm)
      have hkn' : (k:ℝ) ≤ (n:ℝ) := by exact_mod_cast (le_of_lt hkn)
      nlinarith [hm1k, hkn']
    have hc : 0 < (n.choose m : ℝ) := by exact_mod_cast (Nat.choose_pos hmle)
    have hm1 : 0 < (m:ℝ)+1 := by positivity
    have hch := choose_succ_cast n m hmle
    have hkey' : ((n-k:ℕ):ℝ) * (n.choose m : ℝ) ≤ (k:ℝ) * (n.choose (m+1) : ℝ) := by
      have hstep : ((n-k:ℕ):ℝ) * (n.choose m : ℝ) * ((m:ℝ)+1)
                 ≤ (k:ℝ) * (n.choose (m+1) : ℝ) * ((m:ℝ)+1) := by
        calc ((n-k:ℕ):ℝ) * (n.choose m : ℝ) * ((m:ℝ)+1)
            = (n.choose m : ℝ) * (((n-k:ℕ):ℝ) * ((m:ℝ)+1)) := by ring
          _ ≤ (n.choose m : ℝ) * ((k:ℝ) * ((n:ℝ) - m)) :=
              mul_le_mul_of_nonneg_left hnat hc.le
          _ = (k:ℝ) * ((n.choose m : ℝ) * ((n:ℝ) - m)) := by ring
          _ = (k:ℝ) * ((n.choose (m+1) : ℝ) * ((m:ℝ)+1)) := by rw [← hch]
          _ = (k:ℝ) * (n.choose (m+1) : ℝ) * ((m:ℝ)+1) := by ring
      exact le_of_mul_le_mul_right hstep hm1
    rw [hx, hy, div_mul_eq_mul_div, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hkey' hn0.le
  have hkey_down : ∀ m, k ≤ m → m + 1 ≤ n →
      x * (n.choose (m+1) : ℝ) ≤ y * (n.choose m : ℝ) := by
    intro m hkm hm1n
    have hmle : m ≤ n := le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self m) hm1n)
    have hnat : (k:ℝ) * ((n:ℝ) - m) ≤ ((n-k:ℕ):ℝ) * ((m:ℝ)+1) := by
      rw [Nat.cast_sub (le_of_lt hkn)]
      have h1 : (k:ℝ) ≤ (m:ℝ) := by exact_mod_cast hkm
      have hkn' : (k:ℝ) ≤ (n:ℝ) := by exact_mod_cast (le_of_lt hkn)
      nlinarith [h1, hkn']
    have hc : 0 < (n.choose m : ℝ) := by exact_mod_cast (Nat.choose_pos hmle)
    have hm1 : 0 < (m:ℝ)+1 := by positivity
    have hch := choose_succ_cast n m hmle
    have hkey' : (k:ℝ) * (n.choose (m+1) : ℝ) ≤ ((n-k:ℕ):ℝ) * (n.choose m : ℝ) := by
      have hstep : (k:ℝ) * (n.choose (m+1) : ℝ) * ((m:ℝ)+1)
                 ≤ ((n-k:ℕ):ℝ) * (n.choose m : ℝ) * ((m:ℝ)+1) := by
        calc (k:ℝ) * (n.choose (m+1) : ℝ) * ((m:ℝ)+1)
            = (k:ℝ) * ((n.choose (m+1) : ℝ) * ((m:ℝ)+1)) := by ring
          _ = (k:ℝ) * ((n.choose m : ℝ) * ((n:ℝ) - m)) := by rw [hch]
          _ = (n.choose m : ℝ) * ((k:ℝ) * ((n:ℝ) - m)) := by ring
          _ ≤ (n.choose m : ℝ) * (((n-k:ℕ):ℝ) * ((m:ℝ)+1)) :=
              mul_le_mul_of_nonneg_left hnat hc.le
          _ = ((n-k:ℕ):ℝ) * (n.choose m : ℝ) * ((m:ℝ)+1) := by ring
      exact le_of_mul_le_mul_right hstep hm1
    rw [hx, hy, div_mul_eq_mul_div, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hkey' hn0.le
  have hup : ∀ m, m < k → x^m * y^(n-m) * (n.choose m : ℝ)
                          ≤ x^(m+1) * y^(n-(m+1)) * (n.choose (m+1) : ℝ) := by
    intro m hm
    have hnm : n - m = (n - (m+1)) + 1 := by omega
    have hk' := hkey m hm
    have hfac : (0:ℝ) ≤ x^m * y^(n-(m+1)) :=
      mul_nonneg (pow_nonneg hx0.le m) (pow_nonneg hy0.le _)
    calc x^m * y^(n-m) * (n.choose m : ℝ)
        = x^m * y^(n-(m+1)) * (y * (n.choose m : ℝ)) := by rw [hnm, pow_succ]; ring
      _ ≤ x^m * y^(n-(m+1)) * (x * (n.choose (m+1) : ℝ)) :=
          mul_le_mul_of_nonneg_left hk' hfac
      _ = x^(m+1) * y^(n-(m+1)) * (n.choose (m+1) : ℝ) := by rw [pow_succ]; ring
  have hdown : ∀ m, k ≤ m → x^(m+1) * y^(n-(m+1)) * (n.choose (m+1) : ℝ)
                              ≤ x^m * y^(n-m) * (n.choose m : ℝ) := by
    intro m hkm
    by_cases hmn : m + 1 ≤ n
    · have hnm : n - m = (n - (m+1)) + 1 := by omega
      have hk' := hkey_down m hkm hmn
      have hfac : (0:ℝ) ≤ x^m * y^(n-(m+1)) :=
        mul_nonneg (pow_nonneg hx0.le m) (pow_nonneg hy0.le _)
      calc x^(m+1) * y^(n-(m+1)) * (n.choose (m+1) : ℝ)
          = x^m * y^(n-(m+1)) * (x * (n.choose (m+1) : ℝ)) := by rw [pow_succ]; ring
        _ ≤ x^m * y^(n-(m+1)) * (y * (n.choose m : ℝ)) :=
            mul_le_mul_of_nonneg_left hk' hfac
        _ = x^m * y^(n-m) * (n.choose m : ℝ) := by rw [hnm, pow_succ]; ring
    · push Not at hmn
      have hz : (n.choose (m+1)) = 0 := Nat.choose_eq_zero_of_lt hmn
      rw [hz, Nat.cast_zero, mul_zero]
      exact htnn m
  have hleft : ∀ d ≤ k, x^(k-d) * y^(n-(k-d)) * (n.choose (k-d) : ℝ)
                          ≤ x^k * y^(n-k) * (n.choose k : ℝ) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
        intro hd
        have hsub : (k-(d+1)) + 1 = k - d := by omega
        calc x^(k-(d+1)) * y^(n-(k-(d+1))) * (n.choose (k-(d+1)) : ℝ)
            ≤ x^((k-(d+1))+1) * y^(n-((k-(d+1))+1)) * (n.choose ((k-(d+1))+1) : ℝ) :=
              hup (k-(d+1)) (by omega)
          _ = x^(k-d) * y^(n-(k-d)) * (n.choose (k-d) : ℝ) := by rw [hsub]
          _ ≤ x^k * y^(n-k) * (n.choose k : ℝ) := ih (by omega)
  have hright : ∀ d, k + d ≤ n → x^(k+d) * y^(n-(k+d)) * (n.choose (k+d) : ℝ)
                                  ≤ x^k * y^(n-k) * (n.choose k : ℝ) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
        intro hd
        have hadd : k + (d+1) = (k+d)+1 := by omega
        calc x^(k+(d+1)) * y^(n-(k+(d+1))) * (n.choose (k+(d+1)) : ℝ)
            = x^((k+d)+1) * y^(n-((k+d)+1)) * (n.choose ((k+d)+1) : ℝ) := by rw [hadd]
          _ ≤ x^(k+d) * y^(n-(k+d)) * (n.choose (k+d) : ℝ) := hdown (k+d) (by omega)
          _ ≤ x^k * y^(n-k) * (n.choose k : ℝ) := ih (by omega)
  have hmode : ∀ j ≤ n, x^j * y^(n-j) * (n.choose j : ℝ)
                          ≤ x^k * y^(n-k) * (n.choose k : ℝ) := by
    intro j hj
    rcases le_total j k with hjk | hjk
    · have h1 := hleft (k - j) (Nat.sub_le k j)
      rwa [show k - (k - j) = j by omega] at h1
    · have h1 := hright (j - k) (by omega)
      rwa [show k + (j - k) = j by omega] at h1
  have hsum_le : (1:ℝ) ≤ (n+1) * (x^k * y^(n-k) * (n.choose k : ℝ)) := by
    calc (1:ℝ) = ∑ j ∈ range (n+1), x^j * y^(n-j) * (n.choose j : ℝ) := hsum1.symm
      _ ≤ ∑ j ∈ range (n+1), x^k * y^(n-k) * (n.choose k : ℝ) := by
          apply sum_le_sum
          intro j hj
          exact hmode j (Nat.lt_succ_iff.mp (mem_range.mp hj))
      _ = (n+1) * (x^k * y^(n-k) * (n.choose k : ℝ)) := by
          rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  have htk : (1/(n+1)) ≤ x^k * y^(n-k) * (n.choose k : ℝ) := by
    have hn1 : (0:ℝ) < n+1 := by positivity
    rw [div_le_iff₀ hn1, mul_comm]
    exact hsum_le
  have ha0 : 0 < x^k * y^(n-k) := mul_pos (pow_pos hx0 k) (pow_pos hy0 (n-k))
  have ha_inv : (x^k * y^(n-k))⁻¹ = ((n:ℝ)/k)^k * ((n:ℝ)/((n-k:ℕ):ℝ))^(n-k) := by
    rw [hx, hy, mul_inv, ← inv_pow, ← inv_pow, inv_div, inv_div]
  calc (1/(n+1)) * (((n:ℝ)/k)^k * ((n:ℝ)/((n-k:ℕ):ℝ))^(n-k))
      = (1/(n+1)) * (x^k * y^(n-k))⁻¹ := by rw [← ha_inv]
    _ ≤ (x^k * y^(n-k) * (n.choose k : ℝ)) * (x^k * y^(n-k))⁻¹ :=
        mul_le_mul_of_nonneg_right htk (inv_nonneg.mpr ha0.le)
    _ = (n.choose k : ℝ) := by
        rw [mul_assoc, mul_comm (n.choose k : ℝ) (x^k * y^(n-k))⁻¹, ← mul_assoc,
            mul_inv_cancel₀ ha0.ne', one_mul]

theorem choose_le_two_pow_H2_of_pos (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    (n.choose k : ℝ) ≤ (2:ℝ) ^ ((n:ℝ) * H2 ((k:ℝ)/n)) := by
  rw [two_pow_mul_H2_eq n k hk hkn]
  exact choose_le_prod n k hk hkn

theorem two_pow_H2_div_le_choose_of_pos (n k : ℕ) (hk : 0 < k) (hkn : k < n) :
    (1/(n+1)) * (2:ℝ) ^ ((n:ℝ) * H2 ((k:ℝ)/n)) ≤ (n.choose k : ℝ) := by
  rw [two_pow_mul_H2_eq n k hk hkn]
  exact entropy_div_le_choose_prod n k hk hkn

@[simp] lemma H2_zero : H2 0 = 0 := by simp [H2, Real.logb]
@[simp] lemma H2_one : H2 1 = 0 := by simp [H2, Real.logb]

lemma one_div_succ_le_one (n : ℕ) : (1/((n:ℝ)+1)) ≤ 1 := by
  rw [div_le_one (by positivity)]
  linarith [Nat.cast_nonneg (α := ℝ) n]

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

/-- Inequality `(2)`, lower bound `2^{nH(k/n)}/(n+1) <= C^n_k`, for all `k <= n`. -/
theorem two_pow_H2_div_le_choose (n k : ℕ) (hk : k ≤ n) :
    (1/(n+1)) * (2:ℝ) ^ ((n:ℝ) * H2 ((k:ℝ)/n)) ≤ (n.choose k : ℝ) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    rw [Nat.choose_zero_right, Nat.cast_one]
    have hz : (2:ℝ) ^ ((n:ℝ) * H2 (((0:ℕ):ℝ)/↑n)) = 1 := by simp [H2]
    rw [hz, mul_one]
    exact one_div_succ_le_one n
  · rcases eq_or_lt_of_le hk with hkn | hkn
    · rw [hkn]
      rw [Nat.choose_self, Nat.cast_one]
      have hnR : (n:ℝ) ≠ 0 := by
        have : 0 < n := by rw [← hkn]; exact hkpos
        exact_mod_cast this.ne'
      rw [div_self hnR, H2_one, mul_zero, Real.rpow_zero, mul_one]
      exact one_div_succ_le_one n
    · exact two_pow_H2_div_le_choose_of_pos n k hkpos hkn

end BinomialEntropy

/-! ## Theorem 1: the partition rank of the disjointness matrix

The paper's *unique disjointness matrix* `Uₙ` is the partially defined `2ⁿ × 2ⁿ` boolean
matrix (rows/columns indexed by the subsets of `[n]`, i.e. by the boolean vectors `BVec (Fin n)`)
with `Uₙ[a,b] = 1` iff `a ∩ b = ∅`, `0` iff `|a ∩ b| = 1`, and `*` otherwise.  A *rectangle* is a
submatrix with no `0`-entry, and the *partition rank* `rk⁺ Uₙ` is the least number of *pairwise
disjoint* rectangles whose union is the set of `1`-entries (`HasPartFin`).

Disjointness is required only on `1`-entries: a rectangle has no `0`-entry, but two rectangles may
share a `*`-entry.  For the constructions here — and for the paper's — no `1`-entry ever lies in two
rectangles, so the family is a genuine partition of the `1`-entries; this is exactly what
`HasPartFin` demands (and it is strictly stronger than mere covering).

**Theorem 1** states `rk⁺ Uₙ ≼ n³ (3/∛4)ⁿ ≺ 1.89ⁿ`.  We formalise the sharp, non-asymptotic
bound `partRank n ≤ 2 (n+1)³ · 2^{nH(1/3)}` (`theorem1`), where `2^{H(1/3)} = 3/∛4 = 1.889…`;
here `partRank n` is `rk⁺ Uₙ` (`partRank`, `partRank_le`) and `H = H2` is the base-`2` binary
entropy of inequality `(2)`.

The partition follows the paper's decomposition into blocks of fixed row/column weights `(p,q)`:

  * *strategy 1* — each weight-`p` row with `p ≤ n/3` gives the rectangle `{a} × {b | a ∩ b = ∅}`
    (`rowRect`), and each weight-`q` column with `q ≤ n/3` gives `{a | n < 3‖a‖, a ∩ b = ∅} × {b}`
    (`colRect`), restricted to rows of weight `> n/3` so that it misses the row rectangles;
  * *strategy 2* — for a block `(p,q)` with `p, q > n/3` (`validBlock`), a decomposition of the
    `(p+q)`-subsets and, for each, the paper's rectangles `Rᵢ × R̄ᵢ` (`blockRect`) built from the
    cube-code partition of `B^{p+q}` of Lemma 2 (`blockGamma`, transported to the subset `S` by
    `GammaS`, `extend`/`restrict`).

Their union is `coverIdx`/`coverR`/`coverC`; `cover_cover` shows every `1`-entry is covered and
`cover_part` shows none is covered twice.  Counting the index types (`card_weightIdx_le`,
`card_blockIdx_le`) and bounding the binomial coefficients by inequality `(2)`
(`choose_le_two_pow_H2`, `H2_div_le`, `H2_div_le_of_large`) yields the stated bound. -/

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

theorem hasPartFin_exists (n : ℕ) : ∃ k, HasPartFin n k := ⟨4 ^ n, hasPartFin_four n⟩

noncomputable def partRank (n : ℕ) : ℕ := by
  classical
  exact Nat.find (p := HasPartFin n) (hasPartFin_exists n)

lemma partRank_le {n k : ℕ} (h : HasPartFin n k) : partRank n ≤ k := by
  classical
  exact Nat.find_min' (p := HasPartFin n) (hasPartFin_exists n) h

section Transport

def reindexBVec {ι κ : Type*} (e : ι ≃ κ) (x : BVec ι) : BVec κ := fun k => x (e.symm k)

@[simp] lemma reindexBVec_apply {ι κ : Type*} (e : ι ≃ κ) (x : BVec ι) (k : κ) :
    reindexBVec e x k = x (e.symm k) := rfl

lemma reindexBVec_sub {ι κ : Type*} (e : ι ≃ κ) (x y : BVec ι) :
    reindexBVec e (x - y) = reindexBVec e x - reindexBVec e y := by
  funext k; simp [reindexBVec, Pi.sub_apply]

lemma reindexBVec_one_sub {ι κ : Type*} (e : ι ≃ κ) (x : BVec ι) :
    reindexBVec e ((1 : BVec ι) - x) = (1 : BVec κ) - reindexBVec e x := by
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

section Family12

/-- Strategy 1, rows: index by weight-`p` rows with `3p ≤ n`, one rectangle each. -/
abbrev rowIdx (n : ℕ) : Type :=
  Σ (p : {p : Fin (n+1) // 3 * (p : ℕ) ≤ n}), {a : BVec (Fin n) // hammingNorm a = (p.1 : ℕ)}

noncomputable def rowRect (n : ℕ) (i : rowIdx n) : Finset (BVec (Fin n)) × Finset (BVec (Fin n)) :=
  ({i.2.1}, Finset.univ.filter (fun b => interCard i.2.1 b = 0))

lemma rowRect_rect (n : ℕ) : ∀ i : rowIdx n, IsRectangle (rowRect n i).1 (rowRect n i).2 := by
  rintro ⟨p, a⟩ x hx y hy
  simp only [rowRect, Finset.mem_singleton] at hx
  simp only [rowRect, Finset.mem_filter, Finset.mem_univ, true_and] at hy
  rw [hx, hy]; omega

lemma rowRect_cover (n : ℕ) : ∀ a b : BVec (Fin n), interCard a b = 0 → 3 * hammingNorm a ≤ n →
    ∃ i : rowIdx n, a ∈ (rowRect n i).1 ∧ b ∈ (rowRect n i).2 := by
  intro a b hab h3
  have ha : hammingNorm a ≤ n := by
    simpa using (hammingNorm_le_card_fintype (x := a))
  refine ⟨⟨⟨⟨hammingNorm a, by omega⟩, by simpa using h3⟩, ⟨a, rfl⟩⟩, ?_, ?_⟩
  · simp [rowRect]
  · simp [rowRect, hab]

/-- Strategy 1, columns: index by weight-`q` columns with `3q ≤ n`, one rectangle each. -/
abbrev colIdx (n : ℕ) : Type :=
  Σ (q : {q : Fin (n+1) // 3 * (q : ℕ) ≤ n}), {b : BVec (Fin n) // hammingNorm b = (q.1 : ℕ)}

noncomputable def colRect (n : ℕ) (i : colIdx n) : Finset (BVec (Fin n)) × Finset (BVec (Fin n)) :=
  (Finset.univ.filter (fun a => n < 3 * hammingNorm a ∧ interCard a i.2.1 = 0), {i.2.1})

lemma colRect_rect (n : ℕ) : ∀ i : colIdx n, IsRectangle (colRect n i).1 (colRect n i).2 := by
  rintro ⟨q, b⟩ x hx y hy
  simp only [colRect, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  simp only [colRect, Finset.mem_singleton] at hy
  rw [hy, hx.2]; omega

lemma colRect_cover (n : ℕ) : ∀ a b : BVec (Fin n), interCard a b = 0 → n < 3 * hammingNorm a →
    3 * hammingNorm b ≤ n → ∃ i : colIdx n, a ∈ (colRect n i).1 ∧ b ∈ (colRect n i).2 := by
  intro a b hab ha3 h3
  have hb : hammingNorm b ≤ n := by
    simpa using (hammingNorm_le_card_fintype (x := b))
  refine ⟨⟨⟨⟨hammingNorm b, by omega⟩, by simpa using h3⟩, ⟨b, rfl⟩⟩, ?_, ?_⟩
  · simp only [colRect, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨ha3, hab⟩
  · simp [colRect]

/-! ### Membership and injectivity helpers used by `cover_part` -/

lemma rowRect_mem_fst_eq {n : ℕ} {i : rowIdx n} {a : BVec (Fin n)} (h : a ∈ (rowRect n i).1) :
    a = i.2.1 := by
  simpa only [rowRect, Finset.mem_singleton] using h

lemma rowRect_mem_fst {n : ℕ} {i : rowIdx n} {a : BVec (Fin n)} (h : a ∈ (rowRect n i).1) :
    3 * hammingNorm a ≤ n := by
  rw [rowRect_mem_fst_eq h, i.2.2]
  exact i.1.2

lemma colRect_mem_snd_eq {n : ℕ} {i : colIdx n} {b : BVec (Fin n)} (h : b ∈ (colRect n i).2) :
    b = i.2.1 := by
  simpa only [colRect, Finset.mem_singleton] using h

lemma colRect_mem_fst {n : ℕ} {i : colIdx n} {a : BVec (Fin n)} (h : a ∈ (colRect n i).1) :
    n < 3 * hammingNorm a := by
  simp only [colRect, Finset.mem_filter, Finset.mem_univ, true_and] at h
  exact h.1

lemma colRect_mem_snd {n : ℕ} {i : colIdx n} {b : BVec (Fin n)} (h : b ∈ (colRect n i).2) :
    3 * hammingNorm b ≤ n := by
  rw [colRect_mem_snd_eq h, i.2.2]
  exact i.1.2

lemma rowIdx_ext {n : ℕ} {i j : rowIdx n} (h : i.2.1 = j.2.1) : i = j := by
  obtain ⟨pi, ai⟩ := i
  obtain ⟨pj, aj⟩ := j
  have hval : (pi.1 : ℕ) = (pj.1 : ℕ) := by rw [← ai.2, ← aj.2, h]
  have hp : pi = pj := Subtype.ext (Fin.ext hval)
  subst hp
  have ha : ai = aj := Subtype.ext h
  rw [ha]

lemma colIdx_ext {n : ℕ} {i j : colIdx n} (h : i.2.1 = j.2.1) : i = j := by
  obtain ⟨qi, bi⟩ := i
  obtain ⟨qj, bj⟩ := j
  have hval : (qi.1 : ℕ) = (qj.1 : ℕ) := by rw [← bi.2, ← bj.2, h]
  have hq : qi = qj := Subtype.ext (Fin.ext hval)
  subst hq
  have hb : bi = bj := Subtype.ext h
  rw [hb]

end Family12

section Ext

variable {n : ℕ}

/-- Restriction of a `B^n`-vector to the coordinate set `S`. -/
def restrict (S : Finset (Fin n)) (a : BVec (Fin n)) : BVec ↥S := fun j => a j

/-- Extension of an `↥S`-vector to `B^n` (zero outside `S`). -/
def extend (S : Finset (Fin n)) (y : BVec ↥S) : BVec (Fin n) :=
  fun j => if h : j ∈ S then y ⟨j, h⟩ else 0

@[simp] lemma restrict_apply (S : Finset (Fin n)) (a : BVec (Fin n)) (j : ↥S) :
    restrict S a j = a j := rfl

@[simp] lemma extend_apply_of_mem {S : Finset (Fin n)} {y : BVec ↥S} {j : Fin n} (h : j ∈ S) :
    extend S y j = y ⟨j, h⟩ := by rw [extend, dite_eq_left h]

@[simp] lemma extend_apply_of_notMem {S : Finset (Fin n)} {y : BVec ↥S} {j : Fin n} (h : j ∉ S) :
    extend S y j = 0 := by rw [extend, dite_eq_right (by exact h)]

lemma support_extend_subset (S : Finset (Fin n)) (y : BVec ↥S) : support (extend S y) ⊆ S := by
  intro i hi
  by_contra hc
  rw [support, Finset.mem_filter] at hi
  exact hi.2 (by rw [extend, dite_eq_right (by exact hc)])

lemma support_extend (S : Finset (Fin n)) (y : BVec ↥S) :
    support (extend S y) = (support y).image (Subtype.val : ↥S → Fin n) := by
  ext i
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h
    have hiS : i ∈ S := by
      by_contra hc; rw [extend, dite_eq_right (by exact hc)] at h; exact h rfl
    exact ⟨⟨i, hiS⟩, by rw [extend, dite_eq_left hiS] at h; exact h, rfl⟩
  · rintro ⟨j, hj, hj'⟩
    rw [← hj', extend, dite_eq_left j.2]
    exact hj

lemma extend_injective (S : Finset (Fin n)) : Function.Injective (extend S) := by
  intro y z h
  funext j
  have hh := congrFun h (j : Fin n)
  rw [extend, extend, dite_eq_left j.2, dite_eq_left j.2] at hh
  exact hh

lemma hammingNorm_extend (S : Finset (Fin n)) (y : BVec ↥S) :
    hammingNorm (extend S y) = hammingNorm y := by
  calc hammingNorm (extend S y) = (support (extend S y)).card := hammingNorm_eq_support _
    _ = ((support y).image (Subtype.val : ↥S → Fin n)).card := by rw [support_extend]
    _ = (support y).card := Finset.card_image_of_injective _ Subtype.val_injective
    _ = hammingNorm y := (hammingNorm_eq_support _).symm

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

lemma interCard_extend (S : Finset (Fin n)) (y z : BVec ↥S) :
    interCard (extend S y) (extend S z) = interCard y z := by
  rw [interCard_eq_support_inter, interCard_eq_support_inter]
  have h : support (extend S y) ∩ support (extend S z)
      = ((support y) ∩ (support z)).image (Subtype.val : ↥S → Fin n) := by
    rw [support_extend, support_extend,
      (Finset.image_inter (support y) (support z) Subtype.val_injective).symm]
  rw [h, Finset.card_image_of_injective _ Subtype.val_injective]

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

lemma hammingNorm_sub_one_sub {x z : BVec ι}
    (hxz : hammingNorm x = Fintype.card ι - hammingNorm z) :
    hammingNorm (x - (1 - z)) = 2 * interCard x z := by
  have h1 := hammingNorm_sub_add x (1 - z)
  rw [hammingNorm_one_sub, interCard_one_sub] at h1
  have hle : interCard x z ≤ hammingNorm x := by
    rw [interCard_eq_support_inter, hammingNorm_eq_support]
    exact Finset.card_le_card Finset.inter_subset_left
  omega

end Support2

section Family3

/-- The equivalence `↥S ≃ Fin m` induced by `S.card = m`. -/
noncomputable def phiS {n m : ℕ} (S : Finset (Fin n)) (hm : S.card = m) : ↥S ≃ Fin m :=
  (Fintype.equivFin ↥S).trans (finCongr (by rw [Fintype.card_coe, hm]))

/-- Transfer a cube-code partition of `B^m` to `↥S` along `phiS`. -/
noncomputable def GammaS {n m : ℕ} (S : Finset (Fin n)) (hm : S.card = m)
    (G : Set (BVec (Fin m))) : Set (BVec ↥S) := {y | reindexBVec (phiS S hm) y ∈ G}

lemma GammaS_threeCode {n m : ℕ} (S : Finset (Fin n)) (hm : S.card = m) {G : Set (BVec (Fin m))}
    (hG : ∀ x ∈ G, ∀ y ∈ G, x ≠ y → 3 ≤ hammingNorm (x - y)) :
    ∀ x ∈ GammaS S hm G, ∀ y ∈ GammaS S hm G, x ≠ y → 3 ≤ hammingNorm (x - y) := by
  intro x hx y hy hxy
  simp only [GammaS, Set.mem_ofPred_eq] at hx hy
  have hne : reindexBVec (phiS S hm) x ≠ reindexBVec (phiS S hm) y :=
    fun h => hxy (reindexBVec_injective _ h)
  have h := hG _ hx _ hy hne
  rwa [← reindexBVec_sub, hammingNorm_reindexBVec] at h

lemma GammaS_cover {n m r : ℕ} (S : Finset (Fin n)) (hm : S.card = m)
    (G : Fin r → Set (BVec (Fin m))) (hG : Set.univ = ⋃ i, G i) :
    Set.univ = ⋃ i, GammaS S hm (G i) := by
  rw [eq_comm]
  apply Set.eq_univ_of_forall
  intro y
  have hy : reindexBVec (phiS S hm) y ∈ ⋃ i, G i := by rw [← hG]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

lemma GammaS_disjoint {n m : ℕ} (S : Finset (Fin n)) (hm : S.card = m)
    {G G' : Set (BVec (Fin m))} (h : Disjoint G G') :
    Disjoint (GammaS S hm G) (GammaS S hm G') := by
  rw [Set.disjoint_left] at h ⊢
  intro y hy hy'
  exact h hy hy'

/-- Blocks `(p,q)` of the paper: `p + q ≤ n` and both `p`, `q` strictly larger than `n/3`. -/
abbrev validBlock (n : ℕ) : Type :=
  {pq : Fin (n+1) × Fin (n+1) // n < 3 * (pq.1 : ℕ) ∧ n < 3 * (pq.2 : ℕ)
    ∧ (pq.1 : ℕ) + (pq.2 : ℕ) ≤ n}

lemma validBlock_pos (n : ℕ) (pq : validBlock n) : 1 ≤ ((pq.1.1 : ℕ) + (pq.1.2 : ℕ)) := by
  have h := pq.2.1; omega

/-- A cube-code partition of `B^{p+q}` for the block `pq` (Lemma 2). -/
noncomputable def blockGamma (n : ℕ) (pq : validBlock n) :
    Fin (2 * ((pq.1.1 : ℕ) + (pq.1.2 : ℕ))) →
      Set (BVec (Fin ((pq.1.1 : ℕ) + (pq.1.2 : ℕ)))) :=
  Classical.choose (lemma2 ((pq.1.1 : ℕ) + (pq.1.2 : ℕ)) (validBlock_pos n pq))

lemma blockGamma_threeCode (n : ℕ) (pq : validBlock n) (i) :
    ∀ x ∈ blockGamma n pq i, ∀ y ∈ blockGamma n pq i, x ≠ y → 3 ≤ hammingNorm (x - y) :=
  (Classical.choose_spec (lemma2 _ (validBlock_pos n pq))).1 i

lemma blockGamma_cover (n : ℕ) (pq : validBlock n) :
    Set.univ = ⋃ i, blockGamma n pq i :=
  (Classical.choose_spec (lemma2 _ (validBlock_pos n pq))).2.2

lemma blockGamma_disjoint (n : ℕ) (pq : validBlock n)
    {i j : Fin (2 * ((pq.1.1 : ℕ) + (pq.1.2 : ℕ)))} (h : i ≠ j) :
    Disjoint (blockGamma n pq i) (blockGamma n pq j) :=
  (Classical.choose_spec (lemma2 _ (validBlock_pos n pq))).2.1 i j h

/-- Index type of the strategy-2 rectangles: a valid block, an `(p+q)`-subset `S`, a code index. -/
abbrev blockIdx (n : ℕ) : Type :=
  Σ (pq : validBlock n), {S : Finset (Fin n) // S.card = (pq.1.1 : ℕ) + (pq.1.2 : ℕ)}
    × Fin (2 * ((pq.1.1 : ℕ) + (pq.1.2 : ℕ)))

/-- The strategy-2 rectangle `Rᵢ × R̄ᵢ` of the paper, transferred to `B^n`. -/
noncomputable def blockRect (n : ℕ) (i : blockIdx n) :
    Finset (BVec (Fin n)) × Finset (BVec (Fin n)) := by
  classical
  let S : Finset (Fin n) := i.2.1.1
  let G : Set (BVec ↥S) := GammaS S i.2.1.2 (blockGamma n i.1 i.2.2)
  exact ((Finset.univ.filter (fun y : BVec ↥S =>
      hammingNorm y = (i.1.1.1 : ℕ) ∧ y ∈ G)).image (extend S),
   (Finset.univ.filter (fun z : BVec ↥S =>
      hammingNorm z = (i.1.1.2 : ℕ) ∧ (1 - z) ∈ G)).image (extend S))

omit [DecidableEq ι] in
lemma interCard_eq_zero_iff {a b : BVec ι} :
    interCard a b = 0 ↔ ∀ j, a j ≠ 0 → b j = 0 := by
  rw [interCard, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h j hj
    by_contra hb
    exact h j (by rw [Finset.mem_filter]; exact ⟨Finset.mem_univ _, hj, hb⟩)
  · intro h j hj
    rw [Finset.mem_filter] at hj
    exact hj.2.2 (h j hj.2.1)

lemma one_sub_eq_of_disj {a b : BVec (Fin n)} (hab : interCard a b = 0) {j : Fin n}
    (hj : j ∈ support a ∪ support b) : a j = 1 - b j := by
  rw [Finset.mem_union] at hj
  rcases hj with hjA | hjB
  · have ha_ne : a j ≠ 0 := by rw [support, Finset.mem_filter] at hjA; exact hjA.2
    have ha1 : a j = 1 := zmod_two_eq_one ha_ne
    have hb0 : b j = 0 := interCard_eq_zero_iff.mp hab j ha_ne
    rw [ha1, hb0]; ring
  · have hb_ne : b j ≠ 0 := by rw [support, Finset.mem_filter] at hjB; exact hjB.2
    have hb1 : b j = 1 := zmod_two_eq_one hb_ne
    have ha0 : a j = 0 := by
      by_contra ha; exact hb_ne (interCard_eq_zero_iff.mp hab j ha)
    rw [ha0, hb1]; ring

lemma blockRect_rect (n : ℕ) : ∀ i : blockIdx n, IsRectangle (blockRect n i).1 (blockRect n i).2 := by
  rintro ⟨pq, ⟨⟨S, hm⟩, j⟩⟩ x hx y hy
  simp only [blockRect, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  obtain ⟨y1, ⟨hy1w, hy1G⟩, rfl⟩ := hx
  obtain ⟨z1, ⟨hz1w, hz1G⟩, rfl⟩ := hy
  rw [interCard_extend]
  have hcard : Fintype.card ↥S = (pq.1.1 : ℕ) + (pq.1.2 : ℕ) := by rw [Fintype.card_coe, hm]
  have hthree := GammaS_threeCode S hm (blockGamma_threeCode n pq j)
  by_cases heq : y1 = 1 - z1
  · have hz1' : z1 = 1 - y1 := by rw [heq]; ring
    have hz : interCard y1 z1 = 0 := by rw [hz1', interCard_self_one_sub]
    rw [hz]; omega
  · have hw : hammingNorm y1 = Fintype.card ↥S - hammingNorm z1 := by
      rw [hy1w, hz1w, hcard]; omega
    have hdist := hthree y1 hy1G (1 - z1) hz1G heq
    rw [hammingNorm_sub_one_sub hw] at hdist
    omega

end Family3

lemma blockRect_cover (n : ℕ) :
    ∀ a b : BVec (Fin n), interCard a b = 0 → n < 3 * hammingNorm a → n < 3 * hammingNorm b →
      ∃ i : blockIdx n, a ∈ (blockRect n i).1 ∧ b ∈ (blockRect n i).2 := by
  intro a b hab ha3 hb3
  have hdisj : Disjoint (support a) (support b) := by
    rw [Finset.disjoint_left]
    intro j hjA hjB
    rw [support, Finset.mem_filter] at hjA hjB
    exact hjB.2 (interCard_eq_zero_iff.mp hab j hjA.2)
  have hcard : (support a ∪ support b).card = hammingNorm a + hammingNorm b := by
    rw [Finset.card_union_of_disjoint hdisj, hammingNorm_eq_support, hammingNorm_eq_support]
  have hle : (support a ∪ support b).card ≤ n := by
    simpa using Finset.card_le_univ (support a ∪ support b)
  have hpq : hammingNorm a + hammingNorm b ≤ n := by rw [← hcard]; exact hle
  set S : Finset (Fin n) := support a ∪ support b with hS
  have hSa : support a ⊆ S := by rw [hS]; exact Finset.subset_union_left
  have hSb : support b ⊆ S := by rw [hS]; exact Finset.subset_union_right
  have hSm : S.card = hammingNorm a + hammingNorm b := by rw [hS]; exact hcard
  let pq : validBlock n := ⟨(⟨hammingNorm a, by omega⟩, ⟨hammingNorm b, by omega⟩),
    ⟨ha3, hb3, hpq⟩⟩
  have hyz : restrict S a = 1 - restrict S b := by
    funext j
    rw [restrict_apply, Pi.sub_apply, Pi.one_apply, restrict_apply]
    exact one_sub_eq_of_disj hab (by rw [← hS]; exact j.2)
  have hcov := GammaS_cover S hSm (blockGamma n pq) (blockGamma_cover n pq)
  have hyS : restrict S a ∈ ⋃ i, GammaS S hSm (blockGamma n pq i) := by rw [← hcov]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hyS
  refine ⟨⟨pq, ⟨⟨S, ?_⟩, i⟩⟩, ?_, ?_⟩
  · exact hSm
  · simp only [blockRect, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨restrict S a, ⟨hammingNorm_restrict_of_subset hSa, hi⟩, extend_restrict hSa⟩
  · simp only [blockRect, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨restrict S b, ⟨hammingNorm_restrict_of_subset hSb, by rw [hyz.symm]; exact hi⟩,
      extend_restrict hSb⟩

lemma blockRect_mem_fst_all {n : ℕ} {i : blockIdx n} {a : BVec (Fin n)}
    (h : a ∈ (blockRect n i).1) :
    hammingNorm a = (i.1.1.1 : ℕ) ∧ support a ⊆ i.2.1.1 ∧
      restrict i.2.1.1 a ∈ GammaS i.2.1.1 i.2.1.2 (blockGamma n i.1 i.2.2) := by
  simp only [blockRect, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨y, ⟨hyw, hyG⟩, hyeq⟩ := h
  refine ⟨by rw [← hyeq, hammingNorm_extend, hyw], ?_, ?_⟩
  · rw [← hyeq]; exact support_extend_subset _ _
  · rw [← hyeq, restrict_extend]; exact hyG

lemma blockRect_mem_snd_all {n : ℕ} {i : blockIdx n} {b : BVec (Fin n)}
    (h : b ∈ (blockRect n i).2) :
    hammingNorm b = (i.1.1.2 : ℕ) ∧ support b ⊆ i.2.1.1 ∧
      (1 - restrict i.2.1.1 b) ∈ GammaS i.2.1.1 i.2.1.2 (blockGamma n i.1 i.2.2) := by
  simp only [blockRect, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at h
  obtain ⟨z, ⟨hzw, hzG⟩, hzeq⟩ := h
  refine ⟨by rw [← hzeq, hammingNorm_extend, hzw], ?_, ?_⟩
  · rw [← hzeq]; exact support_extend_subset _ _
  · rw [← hzeq, restrict_extend]; exact hzG

lemma blockRect_large_fst {n : ℕ} {i : blockIdx n} {a : BVec (Fin n)}
    (h : a ∈ (blockRect n i).1) : n < 3 * hammingNorm a := by
  obtain ⟨hwa, _, _⟩ := blockRect_mem_fst_all h
  rw [hwa]; exact i.1.2.1

lemma blockRect_large_snd {n : ℕ} {i : blockIdx n} {b : BVec (Fin n)}
    (h : b ∈ (blockRect n i).2) : n < 3 * hammingNorm b := by
  obtain ⟨hwb, _, _⟩ := blockRect_mem_snd_all h
  rw [hwb]; exact i.1.2.2.1

lemma blockRect_union {n : ℕ} {i : blockIdx n} {a b : BVec (Fin n)} (ha : a ∈ (blockRect n i).1)
    (hb : b ∈ (blockRect n i).2) (hab : interCard a b = 0) :
    support a ∪ support b = i.2.1.1 := by
  obtain ⟨hwa, hsa, _⟩ := blockRect_mem_fst_all ha
  obtain ⟨hwb, hsb, _⟩ := blockRect_mem_snd_all hb
  have hdisj : Disjoint (support a) (support b) := by
    rw [Finset.disjoint_left]
    intro c hca hcb
    rw [support, Finset.mem_filter] at hca hcb
    exact hcb.2 (interCard_eq_zero_iff.mp hab c hca.2)
  have hcard : (support a ∪ support b).card = i.2.1.1.card := by
    rw [Finset.card_union_of_disjoint hdisj, ← hammingNorm_eq_support a, ← hammingNorm_eq_support b,
        hwa, hwb, i.2.1.2]
  exact Finset.eq_of_subset_of_card_le (Finset.union_subset hsa hsb) (by rw [hcard])

section Final

lemma H2_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ (2:ℝ)⁻¹) : H2 a ≤ H2 b := by
  have hmono := Real.binEntropy_strictMonoOn.monotoneOn
    (Set.mem_Icc.mpr ⟨ha, le_trans hab hb⟩) (Set.mem_Icc.mpr ⟨le_trans ha hab, hb⟩) hab
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have : Real.log 2 * H2 a ≤ Real.log 2 * H2 b := by rw [log2_mul_H2, log2_mul_H2]; exact hmono
  exact le_of_mul_le_mul_left this hlog

lemma H2_one_sub' (x : ℝ) : H2 (1 - x) = H2 x := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have h : Real.log 2 * H2 (1 - x) = Real.log 2 * H2 x := by
    rw [log2_mul_H2, log2_mul_H2, Real.binEntropy_one_sub]
  exact mul_left_cancel₀ hlog h

lemma H2_div_le (n p : ℕ) (hn : 0 < n) (hp : 3 * p ≤ n) : H2 ((p:ℝ)/n) ≤ H2 ((1:ℝ)/3) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have h3 : (3:ℝ) * (p:ℝ) ≤ (n:ℝ) := by exact_mod_cast hp
  have hle : (p:ℝ)/n ≤ (1:ℝ)/3 := by rw [div_le_iff₀ hnR]; linarith
  exact H2_mono (by positivity : (0:ℝ) ≤ (p:ℝ)/n) hle (by norm_num)

lemma H2_div_le_of_large (n p q : ℕ) (hn : 0 < n) (h1 : n < 3 * p) (h2 : n < 3 * q)
    (hm : p + q ≤ n) : H2 (((p+q:ℕ):ℝ)/n) ≤ H2 ((1:ℝ)/3) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 ≤ ((p+q:ℕ):ℝ)/n := by positivity
  have hx1 : (2:ℝ)/3 ≤ ((p+q:ℕ):ℝ)/n := by
    rw [le_div_iff₀ hnR]
    have h3 : (2:ℝ) * (n:ℝ) < 3 * ((p+q:ℕ):ℝ) := by
      have : 2 * n < 3 * (p + q) := by omega
      exact_mod_cast this
    linarith
  have hx2 : ((p+q:ℕ):ℝ)/n ≤ 1 := by rw [div_le_one hnR]; exact_mod_cast hm
  rw [← H2_one_sub' (((p+q:ℕ):ℝ)/n)]
  exact H2_mono (by linarith) (by linarith) (by norm_num)

lemma card_weightIdx_le (n : ℕ) (hn : 0 < n) :
    (Fintype.card (Σ (p : {p : Fin (n+1) // 3 * (p:ℕ) ≤ n}),
        {a : BVec (Fin n) // hammingNorm a = (p.1 : ℕ)}) : ℝ)
      ≤ ((n:ℝ)+1) * (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) := by
  rw [Fintype.card_sigma, Nat.cast_sum]
  have hM : (0:ℝ) ≤ (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) := Real.rpow_nonneg (by norm_num) _
  have hstep : ∀ p : {p : Fin (n+1) // 3 * (p:ℕ) ≤ n},
      (Fintype.card {a : BVec (Fin n) // hammingNorm a = (p.1 : ℕ)} : ℝ)
        ≤ (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) := by
    intro p
    rw [card_weight_eq_choose]
    calc (n.choose (p.1:ℕ) : ℝ) ≤ (2:ℝ)^((n:ℝ)*H2 ((p.1:ℕ)/n)) :=
          choose_le_two_pow_H2 n (p.1:ℕ) (by have := p.1.2; omega)
      _ ≤ (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
          exact mul_le_mul_of_nonneg_left (H2_div_le n (p.1:ℕ) hn (by exact_mod_cast p.2))
            (Nat.cast_nonneg n)
  calc (∑ p : {p : Fin (n+1) // 3 * (p:ℕ) ≤ n},
          (Fintype.card {a : BVec (Fin n) // hammingNorm a = (p.1 : ℕ)} : ℝ))
      ≤ ∑ _p : {p : Fin (n+1) // 3 * (p:ℕ) ≤ n}, (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) :=
        Finset.sum_le_sum (fun p _ => hstep p)
    _ = (Fintype.card {p : Fin (n+1) // 3 * (p:ℕ) ≤ n} : ℝ) * (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ((n:ℝ)+1) * (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) := by
        apply mul_le_mul_of_nonneg_right _ hM
        calc (Fintype.card {p : Fin (n+1) // 3 * (p:ℕ) ≤ n} : ℝ)
            ≤ (Fintype.card (Fin (n+1)) : ℝ) :=
              by exact_mod_cast Fintype.card_subtype_le (fun p : Fin (n+1) => 3 * (p:ℕ) ≤ n)
          _ = (n:ℝ) + 1 := by rw [Fintype.card_fin]; push_cast; ring

lemma choose_le_of_large (n p q : ℕ) (hn : 0 < n) (h1 : n < 3 * p) (h2 : n < 3 * q)
    (hm : p + q ≤ n) :
    (n.choose (p + q) : ℝ) ≤ (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) := by
  calc (n.choose (p+q) : ℝ) ≤ (2:ℝ)^((n:ℝ)*H2 (((p+q:ℕ):ℝ)/n)) :=
        choose_le_two_pow_H2 n (p+q) hm
    _ ≤ (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        exact mul_le_mul_of_nonneg_left (H2_div_le_of_large n p q hn h1 h2 hm) (Nat.cast_nonneg n)

lemma card_blockIdx_le (n : ℕ) (hn : 0 < n) :
    (Fintype.card (blockIdx n) : ℝ)
      ≤ ((n:ℝ)+1)^2 * (2*(n:ℝ)) * (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) := by
  unfold blockIdx
  rw [Fintype.card_sigma, Nat.cast_sum]
  have hM : (0:ℝ) ≤ (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) := Real.rpow_nonneg (by norm_num) _
  have hstep : ∀ pq : validBlock n,
      (Fintype.card ({S : Finset (Fin n) // S.card = (pq.1.1:ℕ) + (pq.1.2:ℕ)}
        × Fin (2 * ((pq.1.1:ℕ)+(pq.1.2:ℕ)))) : ℝ)
        ≤ (2*(n:ℝ)) * (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) := by
    intro pq
    have hp := pq.2.1
    have hq := pq.2.2.1
    have hm := pq.2.2.2
    have hM' : (n.choose ((pq.1.1:ℕ)+(pq.1.2:ℕ)) : ℝ) ≤ (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) :=
      choose_le_of_large n (pq.1.1:ℕ) (pq.1.2:ℕ) hn hp hq hm
    have hmn2 : ((pq.1.1:ℕ) : ℝ) + ((pq.1.2:ℕ) : ℝ) ≤ (n:ℝ) := by
      have h : (((pq.1.1:ℕ)+(pq.1.2:ℕ) : ℕ) : ℝ) ≤ (n:ℝ) := by exact_mod_cast hm
      push_cast at h ⊢
      exact h
    simp only [Fintype.card_prod, Fintype.card_finset_len, Fintype.card_fin]
    push_cast
    rw [show (2*(n:ℝ)) * (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3))
        = (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) * (2*(n:ℝ)) by ring]
    exact mul_le_mul hM' (by linarith) (by positivity) hM
  calc (∑ pq : validBlock n,
          (Fintype.card ({S : Finset (Fin n) // S.card = (pq.1.1:ℕ) + (pq.1.2:ℕ)}
            × Fin (2 * ((pq.1.1:ℕ)+(pq.1.2:ℕ)))) : ℝ))
      ≤ ∑ _pq : validBlock n, (2*(n:ℝ)) * (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) :=
        Finset.sum_le_sum (fun pq _ => hstep pq)
    _ = (Fintype.card (validBlock n) : ℝ) * ((2*(n:ℝ)) * (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ((n:ℝ)+1)^2 * (2*(n:ℝ)) * (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) := by
        have hvb : (Fintype.card (validBlock n) : ℝ) ≤ ((n:ℝ)+1)^2 := by
          have hinj : Function.Injective
              (fun pq : validBlock n => (pq.1 : Fin (n+1) × Fin (n+1))) :=
            fun a b h => Subtype.ext h
          calc (Fintype.card (validBlock n) : ℝ)
              ≤ (Fintype.card (Fin (n+1) × Fin (n+1)) : ℝ) := by
                exact_mod_cast Fintype.card_le_of_injective _ hinj
            _ = ((n:ℝ)+1)^2 := by rw [Fintype.card_prod, Fintype.card_fin]; push_cast; ring
        calc (Fintype.card (validBlock n) : ℝ) * ((2*(n:ℝ)) * (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)))
            ≤ ((n:ℝ)+1)^2 * ((2*(n:ℝ)) * (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3))) :=
              mul_le_mul_of_nonneg_right hvb (by positivity)
          _ = ((n:ℝ)+1)^2 * (2*(n:ℝ)) * (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) := by ring

abbrev coverIdx (n : ℕ) : Type := rowIdx n ⊕ colIdx n ⊕ blockIdx n

noncomputable def coverR (n : ℕ) : coverIdx n → Finset (BVec (Fin n))
  | Sum.inl i => (rowRect n i).1
  | Sum.inr (Sum.inl i) => (colRect n i).1
  | Sum.inr (Sum.inr i) => (blockRect n i).1

noncomputable def coverC (n : ℕ) : coverIdx n → Finset (BVec (Fin n))
  | Sum.inl i => (rowRect n i).2
  | Sum.inr (Sum.inl i) => (colRect n i).2
  | Sum.inr (Sum.inr i) => (blockRect n i).2

lemma cover_isRect (n : ℕ) : ∀ i : coverIdx n, IsRectangle (coverR n i) (coverC n i) := by
  rintro (i | (i | i))
  · exact rowRect_rect n i
  · exact colRect_rect n i
  · exact blockRect_rect n i

lemma cover_cover (n : ℕ) :
    ∀ a b : BVec (Fin n), interCard a b = 0 →
      ∃ i : coverIdx n, a ∈ coverR n i ∧ b ∈ coverC n i := by
  intro a b hab
  by_cases h1 : 3 * hammingNorm a ≤ n
  · obtain ⟨i, hi1, hi2⟩ := rowRect_cover n a b hab h1
    exact ⟨Sum.inl i, hi1, hi2⟩
  · push Not at h1
    by_cases h2 : 3 * hammingNorm b ≤ n
    · obtain ⟨i, hi1, hi2⟩ := colRect_cover n a b hab h1 h2
      exact ⟨Sum.inr (Sum.inl i), hi1, hi2⟩
    · push Not at h2
      obtain ⟨i, hi1, hi2⟩ := blockRect_cover n a b hab h1 h2
      exact ⟨Sum.inr (Sum.inr i), hi1, hi2⟩

/-- **Disjointness**: distinct rectangles of the family share no `1`-entry, so the `1`-entries are
*partitioned* (not merely covered).  The row/column-weight regions are disjoint by the thresholds
`3‖a‖ ≤ n` vs `n < 3‖a‖`, and inside a block the rectangles `Rᵢ × R̄ᵢ` are disjoint because the
cube-code parts `Γᵢ` are. -/
lemma cover_part (n : ℕ) :
    ∀ i j : coverIdx n, i ≠ j → ∀ a b : BVec (Fin n),
      a ∈ coverR n i → b ∈ coverC n i → a ∈ coverR n j → b ∈ coverC n j →
      interCard a b ≠ 0 := by
  intro i j hij a b hai hbi haj hbj hab
  rcases i with i | (i | i) <;> rcases j with j | (j | j)
  · exact absurd (congrArg Sum.inl
      (rowIdx_ext ((rowRect_mem_fst_eq hai).symm.trans (rowRect_mem_fst_eq haj)))) hij
  · have h1 := rowRect_mem_fst hai; have h2 := colRect_mem_fst haj; omega
  · have h1 := rowRect_mem_fst hai; have h2 := blockRect_large_fst haj; omega
  · have h1 := colRect_mem_fst hai; have h2 := rowRect_mem_fst haj; omega
  · exact absurd (congrArg (fun t => (Sum.inr (Sum.inl t) : coverIdx n))
      (colIdx_ext ((colRect_mem_snd_eq hbi).symm.trans (colRect_mem_snd_eq hbj)))) hij
  · have h1 := colRect_mem_snd hbi; have h2 := blockRect_large_snd hbj; omega
  · have h1 := blockRect_large_fst hai; have h2 := rowRect_mem_fst haj; omega
  · have h1 := blockRect_large_snd hbi; have h2 := colRect_mem_snd hbj; omega
  · obtain ⟨pq1, ⟨S1, hm1⟩, k1⟩ := i
    obtain ⟨pq2, ⟨S2, hm2⟩, k2⟩ := j
    have hU1 : support a ∪ support b = S1 := blockRect_union hai hbi hab
    have hU2 : support a ∪ support b = S2 := blockRect_union haj hbj hab
    have hS : S1 = S2 := hU1.symm.trans hU2
    obtain ⟨hwa1, _, hG1⟩ := blockRect_mem_fst_all hai
    obtain ⟨hwb1, _, _⟩ := blockRect_mem_snd_all hbi
    obtain ⟨hwa2, _, hG2⟩ := blockRect_mem_fst_all haj
    obtain ⟨hwb2, _, _⟩ := blockRect_mem_snd_all hbj
    have hp : (pq1.1.1 : ℕ) = (pq2.1.1 : ℕ) := by rw [← hwa1, hwa2]
    have hq : (pq1.1.2 : ℕ) = (pq2.1.2 : ℕ) := by rw [← hwb1, hwb2]
    have hpq : pq1 = pq2 := Subtype.ext (Prod.ext (Fin.ext hp) (Fin.ext hq))
    subst hpq
    subst hS
    have hhm : hm1 = hm2 := Subsingleton.elim _ _
    subst hhm
    have hk : k1 = k2 := by
      by_contra hne
      exact Set.disjoint_left.mp (GammaS_disjoint S1 hm1 (blockGamma_disjoint n pq1 hne)) hG1 hG2
    subst hk
    exact absurd rfl hij

theorem hasPartFin_final (n : ℕ) : HasPartFin n (Fintype.card (coverIdx n)) := by
  classical
  exact hasPartFin_of_card_eq rfl (coverR n) (coverC n) (cover_isRect n) (cover_cover n)
    (cover_part n)

lemma coverIdx_card_le (n : ℕ) (hn : 0 < n) :
    (Fintype.card (coverIdx n) : ℝ) ≤ 2 * ((n:ℝ)+1)^3 * (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) := by
  have hsum : (Fintype.card (coverIdx n) : ℝ)
      = (Fintype.card (rowIdx n) : ℝ) + (Fintype.card (colIdx n) : ℝ)
        + (Fintype.card (blockIdx n) : ℝ) := by
    unfold coverIdx
    rw [Fintype.card_sum, Fintype.card_sum]; push_cast; ring
  rw [hsum]
  have hr : (Fintype.card (rowIdx n) : ℝ) ≤ ((n:ℝ)+1) * (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) :=
    card_weightIdx_le n hn
  have hc : (Fintype.card (colIdx n) : ℝ) ≤ ((n:ℝ)+1) * (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) :=
    card_weightIdx_le n hn
  have hb := card_blockIdx_le n hn
  have hM : (0:ℝ) < (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) := Real.rpow_pos_of_pos (by norm_num) _
  nlinarith [hr, hc, hb, hM]

theorem theorem1 (n : ℕ) (hn : 1 ≤ n) :
    (partRank n : ℝ) ≤ 2 * ((n:ℝ)+1)^3 * (2:ℝ)^((n:ℝ)*H2 ((1:ℝ)/3)) := by
  have h := partRank_le (hasPartFin_final n)
  calc (partRank n : ℝ) ≤ (Fintype.card (coverIdx n) : ℝ) := by exact_mod_cast h
    _ ≤ _ := coverIdx_card_le n (by omega)

end Final

/-! ### The paper's literal constant

Since `H(1/3) = log₂3 − 2/3` one has `2^{H(1/3)} = 3/∛4 = 1.889…`, so the bound above reads
`rk⁺ Uₙ ≤ 2 (n+1)³ (3/∛4)ⁿ`, matching the paper's `n³ (3/∛4)ⁿ ≺ 1.89ⁿ` (up to the polynomial
factor). -/
lemma binEntropy_one_third :
    Real.binEntropy ((1:ℝ)/3) = Real.log 3 - (2/3) * Real.log 2 := by
  rw [Real.binEntropy]
  have e1 : ((1:ℝ)/3)⁻¹ = 3 := by norm_num
  have e2 : (1:ℝ) - 1/3 = 2/3 := by norm_num
  have e3 : ((2:ℝ)/3)⁻¹ = 3/2 := by norm_num
  rw [e1, e2, e3, Real.log_div (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
  ring

lemma two_pow_H2_one_third : (2:ℝ)^(H2 ((1:ℝ)/3)) = 3 / (4:ℝ) ^ ((1:ℝ)/3) := by
  have h2 : (0:ℝ) < 2 := by norm_num
  have h3 : (0:ℝ) < 3 := by norm_num
  have hexp : Real.exp ((2:ℝ)/3 * Real.log 2) = (2:ℝ)^((2:ℝ)/3) := by
    have h := Real.rpow_def_of_pos h2 ((2:ℝ)/3)
    rw [h]; congr 1; ring
  have h43 : (4:ℝ) ^ ((1:ℝ)/3) = (2:ℝ)^((2:ℝ)/3) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 4) ((1:ℝ)/3),
        Real.rpow_def_of_pos h2 ((2:ℝ)/3)]
    congr 1
    rw [show (4:ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
    ring
  rw [two_pow_H2_eq_exp, binEntropy_one_third, Real.exp_sub, Real.exp_log h3, hexp, h43]

lemma two_pow_H2_third_pow (n : ℕ) :
    (2:ℝ)^((n:ℝ) * H2 ((1:ℝ)/3)) = (3 / (4:ℝ) ^ ((1:ℝ)/3))^n := by
  rw [show (n:ℝ) * H2 ((1:ℝ)/3) = H2 ((1:ℝ)/3) * (n:ℝ) by ring]
  rw [Real.rpow_mul (show (0:ℝ) ≤ 2 by norm_num) _ (n:ℝ), Real.rpow_natCast,
      two_pow_H2_one_third]

theorem theorem1_paper (n : ℕ) (hn : 1 ≤ n) :
    (partRank n : ℝ) ≤ 2 * ((n:ℝ)+1)^3 * (3 / (4:ℝ) ^ ((1:ℝ)/3))^n := by
  rw [← two_pow_H2_third_pow n]
  exact theorem1 n hn

end Udisj
