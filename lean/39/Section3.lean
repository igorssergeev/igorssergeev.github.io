module

public import Preliminaries
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Section 3: estimates for the exponents in the general case

This file formalizes Theorems 1 and 2 of I. S. Sergeev, *Formula complexity of
a linear function in a k-ary basis*, Mathematical Notes 109 (2021), 445--458:

`χ_{U_k} ≤ log_{⌈k/2⌉(⌊k/2⌋+1)} k` and `χ_k ≥ 1/2 + 1/(10 ln k)`.

Theorem 1 uses the majority function `m_k`, whose `U_k`-complexity is `k` and
whose sensitivity is at least `⌈k/2⌉(⌊k/2⌋+1)`.  Theorem 2 is proved by
induction on the number of graphs in a cover, after reducing to a subgraph of
maximal density (footnote 5 of the paper); the two cases of the induction are
`step_case1` and `step_case2`.
-/

namespace UnateLin

open scoped BigOperators

/-! ### Weights, supports and the layers of the Boolean cube -/

/-- The support of a Boolean vector: the coordinates whose value is `true`. -/
def supp {k : ℕ} (x : Fin k → Bool) : Finset (Fin k) :=
  Finset.univ.filter (fun i => x i = true)

/-- The weight of a Boolean vector: the number of `true` coordinates. -/
def weight {k : ℕ} (x : Fin k → Bool) : ℕ := (supp x).card

@[simp]
theorem mem_supp {k : ℕ} {x : Fin k → Bool} {i : Fin k} : i ∈ supp x ↔ x i = true := by
  simp [supp]

/-- Boolean vectors are determined by their supports. -/
theorem eq_of_supp_eq {k : ℕ} {x y : Fin k → Bool} (h : supp x = supp y) : x = y := by
  funext i
  have h' : i ∈ supp x ↔ i ∈ supp y := by rw [h]
  simp only [mem_supp] at h'
  cases hx : x i <;> cases hy : y i <;> simp_all

/-- The layer of vectors of weight `w`. -/
def layer (k w : ℕ) : Finset (Fin k → Bool) :=
  Finset.univ.filter (fun x => weight x = w)

@[simp]
theorem mem_layer {k w : ℕ} {x : Fin k → Bool} : x ∈ layer k w ↔ weight x = w := by
  simp [layer]

/-- The vector obtained by flipping coordinate `i`. -/
def flipAt {k : ℕ} (x : Fin k → Bool) (i : Fin k) : Fin k → Bool :=
  fun j => if j = i then !x j else x j

@[simp]
theorem flipAt_self {k : ℕ} (x : Fin k → Bool) (i : Fin k) : flipAt x i i = !x i := by
  simp [flipAt]

theorem flipAt_of_ne {k : ℕ} {x : Fin k → Bool} {i j : Fin k} (h : j ≠ i) :
    flipAt x i j = x j := by
  simp [flipAt, h]

theorem supp_flipAt {k : ℕ} (x : Fin k → Bool) (i : Fin k) :
    supp (flipAt x i) = if x i then (supp x).erase i else insert i (supp x) := by
  ext j
  by_cases hji : j = i
  · rw [hji]
    by_cases hxi : x i = true
    · simp [flipAt, hxi]
    · have hxi' : x i = false := by simpa using hxi
      simp [flipAt, hxi']
  · by_cases hxi : x i = true <;> simp [flipAt, hji, hxi]

theorem weight_flipAt_true {k : ℕ} {x : Fin k → Bool} {i : Fin k} (h : x i = true) :
    weight (flipAt x i) = weight x - 1 := by
  unfold weight
  rw [supp_flipAt, ite_eq_left h, Finset.card_erase_of_mem]
  simp [h]

theorem weight_flipAt_false {k : ℕ} {x : Fin k → Bool} {i : Fin k} (h : x i = false) :
    weight (flipAt x i) = weight x + 1 := by
  unfold weight
  rw [supp_flipAt, ite_eq_right (by simp [h]), Finset.card_insert_of_notMem]
  simp [h]

/-- The number of `false` coordinates. -/
theorem card_filter_false {k : ℕ} (x : Fin k → Bool) :
    (Finset.univ.filter (fun i => x i = false)).card = k - weight x := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin k))) (p := fun i => x i = true)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have hcongr : (Finset.univ.filter (fun i => ¬ x i = true)) =
      (Finset.univ.filter (fun i => x i = false)) := by
    apply Finset.filter_congr
    intro i _
    constructor
    · intro hi
      cases hx : x i <;> simp_all
    · intro hi
      simp [hi]
  rw [hcongr] at h
  have hw : weight x = (Finset.univ.filter (fun i => x i = true)).card := rfl
  omega

theorem hammingDist_flipAt {k : ℕ} (x : Fin k → Bool) (i : Fin k) :
    hammingDist x (flipAt x i) = 1 := by
  unfold hammingDist
  have hset : (Finset.univ.filter (fun j => x j ≠ flipAt x i j)) = {i} := by
    ext j
    by_cases hji : j = i
    · rw [hji]
      by_cases hx : x i = true
      · simp [flipAt]
      · have hx' : x i = false := by simpa using hx
        simp [flipAt]
    · simp [flipAt, hji]
  rw [hset]
  simp

/-- A vector at Hamming distance one from `x` is obtained by flipping one
coordinate. -/
theorem eq_flipAt_of_hammingDist_eq_one {k : ℕ} {x y : Fin k → Bool}
    (h : hammingDist x y = 1) : ∃ i, y = flipAt x i := by
  unfold hammingDist at h
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
  refine ⟨i, ?_⟩
  funext j
  by_cases hji : j = i
  · rw [hji]
    have hmem : i ∈ Finset.univ.filter (fun j => x j ≠ y j) := by
      rw [hi]
      simp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    have hyi : y i = !x i := by
      cases hx : x i <;> cases hy : y i <;> simp_all
    simp [flipAt, hyi]
  · have hmem : j ∉ Finset.univ.filter (fun j => x j ≠ y j) := by
      rw [hi]
      simp [hji]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hmem
    rw [flipAt_of_ne hji, ← hmem]

theorem hammingDist_comm {k : ℕ} (x y : Fin k → Bool) :
    hammingDist x y = hammingDist y x := by
  unfold hammingDist
  congr 1
  apply Finset.filter_congr
  intro i _
  exact ne_comm

/-- The coordinates where two vectors related by a single flip differ. -/
theorem flipAt_injective {k : ℕ} (x : Fin k → Bool) :
    Function.Injective (fun i => flipAt x i) := by
  intro i j hij
  by_contra hne
  have h : flipAt x i i = flipAt x j i := congrFun hij i
  rw [flipAt_self, flipAt_of_ne (x := x) (i := j) (j := i) hne] at h
  cases hxi : x i with
  | true => simp [hxi] at h
  | false => simp [hxi] at h

theorem supp_indicator {k : ℕ} (t : Finset (Fin k)) :
    supp (fun i => decide (i ∈ t)) = t := by
  ext i
  simp [supp]

theorem weight_indicator {k : ℕ} (t : Finset (Fin k)) :
    weight (fun i => decide (i ∈ t)) = t.card := by
  unfold weight
  rw [supp_indicator]

/-- Every layer of the Boolean cube is nonempty. -/
theorem layer_nonempty {k w : ℕ} (hw : w ≤ k) : (layer k w).Nonempty := by
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin k))) (n := w) (by simpa using hw)
  exact ⟨fun i => decide (i ∈ t), by
    rw [mem_layer, weight_indicator, ht]⟩

/-! ### Counting the edges between consecutive layers -/

/-- A vector of weight  has exactly  neighbours of weight . -/
theorem card_filter_adj_up {k : ℕ} {x : Fin k → Bool} {w : ℕ} (hx : weight x = w) :
    ((layer k (w + 1)).filter (fun y => hammingDist x y = 1)).card = k - w := by
  classical
  have hEq : (layer k (w + 1)).filter (fun y => hammingDist x y = 1)
      = (Finset.univ.filter (fun i => x i = false)).image (fun i => flipAt x i) := by
    ext y
    constructor
    · intro hy
      simp only [mem_layer, Finset.mem_filter] at hy
      obtain ⟨hyw, hyd⟩ := hy
      obtain ⟨i, rfl⟩ := eq_flipAt_of_hammingDist_eq_one hyd
      refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
      have hxi : x i = false := by
        by_contra h
        have hx' : x i = true := by simpa using h
        rw [weight_flipAt_true hx'] at hyw
        omega
      simpa using hxi
    · intro hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy
      simp only [mem_layer, Finset.mem_filter]
      refine ⟨?_, hammingDist_flipAt x i⟩
      rw [weight_flipAt_false (by simpa using hi), hx]
  rw [hEq, Finset.card_image_of_injective _ (flipAt_injective x), card_filter_false, hx]

/-- A vector of weight  has exactly  neighbours of weight . -/
theorem card_filter_adj_down {k : ℕ} {y : Fin k → Bool} {w : ℕ} (hy : weight y = w + 1) :
    ((layer k w).filter (fun x => hammingDist x y = 1)).card = w + 1 := by
  classical
  have hEq : (layer k w).filter (fun x => hammingDist x y = 1)
      = (supp y).image (fun i => flipAt y i) := by
    ext x
    constructor
    · intro hx
      simp only [mem_layer, Finset.mem_filter] at hx
      obtain ⟨hxw, hxd⟩ := hx
      obtain ⟨i, rfl⟩ := eq_flipAt_of_hammingDist_eq_one (by rwa [hammingDist_comm] at hxd)
      refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
      have hyi : y i = true := by
        by_contra h
        have hyi' : y i = false := by simpa using h
        rw [weight_flipAt_false hyi'] at hxw
        omega
      simpa using hyi
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      simp only [mem_layer, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [weight_flipAt_true (by simpa using hi), hy]
        omega
      · rw [hammingDist_comm]
        exact hammingDist_flipAt y i
  rw [hEq, Finset.card_image_of_injective _ (flipAt_injective y), ← hy]
  rfl

/-- The total number of edges between consecutive layers, counted by the first
projection. -/
theorem card_neighborPairs_left {k w : ℕ} :
    (neighborPairs (layer k w) (layer k (w + 1))).card =
      (layer k w).card * (k - w) := by
  classical
  have hR : neighborPairs (layer k w) (layer k (w + 1)) =
      (layer k w).biUnion (fun x =>
        ((layer k (w + 1)).filter (fun y => hammingDist x y = 1)).image (fun y => (x, y))) := by
    ext q
    constructor
    · intro hq
      rw [neighborPairs] at hq
      obtain ⟨hqprod, hd⟩ := Finset.mem_filter.mp hq
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hqprod
      exact Finset.mem_biUnion.mpr
        ⟨q.1, hx, Finset.mem_image.mpr ⟨q.2, by
          rw [Finset.mem_filter]
          exact ⟨hy, hd⟩, rfl⟩⟩
    · intro hq
      obtain ⟨x, hx, hq'⟩ := Finset.mem_biUnion.mp hq
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq'
      obtain ⟨hyP, hd⟩ := Finset.mem_filter.mp hy
      rw [neighborPairs]
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx, hyP⟩, hd⟩
  rw [hR, Finset.card_biUnion]
  · have hcard : ∀ x ∈ layer k w,
        (((layer k (w + 1)).filter (fun y => hammingDist x y = 1)).image (fun y => (x, y))).card
          = k - w := by
      intro x hx
      rw [Finset.card_image_of_injective _ (fun y₁ y₂ h => by simpa using h)]
      exact card_filter_adj_up (by rwa [mem_layer] at hx)
    rw [Finset.sum_congr rfl hcard]
    simp [Finset.sum_const, mul_comm]
  · intro x hx y hy hxy
    apply Finset.disjoint_left.mpr
    intro q hq1 hq2
    obtain ⟨y₁, -, h1⟩ := Finset.mem_image.mp hq1
    obtain ⟨y₂, -, h2⟩ := Finset.mem_image.mp hq2
    exact hxy ((Prod.mk.inj h1).1.trans ((Prod.mk.inj h2).1.symm))

/-- The total number of edges between consecutive layers, counted by the second
projection. -/
theorem card_neighborPairs_right {k w : ℕ} :
    (neighborPairs (layer k w) (layer k (w + 1))).card =
      (layer k (w + 1)).card * (w + 1) := by
  classical
  have hR : neighborPairs (layer k w) (layer k (w + 1)) =
      (layer k (w + 1)).biUnion (fun y =>
        ((layer k w).filter (fun x => hammingDist x y = 1)).image (fun x => (x, y))) := by
    ext q
    constructor
    · intro hq
      rw [neighborPairs] at hq
      obtain ⟨hqprod, hd⟩ := Finset.mem_filter.mp hq
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hqprod
      exact Finset.mem_biUnion.mpr
        ⟨q.2, hy, Finset.mem_image.mpr ⟨q.1, by
          rw [Finset.mem_filter]
          exact ⟨hx, hd⟩, rfl⟩⟩
    · intro hq
      obtain ⟨y, hy, hq'⟩ := Finset.mem_biUnion.mp hq
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hq'
      obtain ⟨hxP, hd⟩ := Finset.mem_filter.mp hx
      rw [neighborPairs]
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hxP, hy⟩, hd⟩
  rw [hR, Finset.card_biUnion]
  · have hcard : ∀ y ∈ layer k (w + 1),
        (((layer k w).filter (fun x => hammingDist x y = 1)).image (fun x => (x, y))).card
          = w + 1 := by
      intro y hy
      rw [Finset.card_image_of_injective _ (fun x₁ x₂ h => by simpa using h)]
      exact card_filter_adj_down (by rwa [mem_layer] at hy)
    rw [Finset.sum_congr rfl hcard]
    simp [Finset.sum_const, mul_comm]
  · intro y hy y' hy' hne
    apply Finset.disjoint_left.mpr
    intro q hq1 hq2
    obtain ⟨x₁, -, h1⟩ := Finset.mem_image.mp hq1
    obtain ⟨x₂, -, h2⟩ := Finset.mem_image.mp hq2
    exact hne ((Prod.mk.inj h1).2.trans ((Prod.mk.inj h2).2.symm))

/-! ### The majority function -/

/-- `⌈k/2⌉`, computed as `k - k / 2`. -/
def halfCeil (k : ℕ) : ℕ := k - k / 2

/-- The base `⌈k/2⌉(⌊k/2⌋+1)` of the logarithm in Theorem 1. -/
def theoremBase (k : ℕ) : ℕ := halfCeil k * (k / 2 + 1)

/-- The majority function: true when at least `halfCeil k` coordinates are true. -/
def majority (k : ℕ) : BoolFun k := fun x => decide (halfCeil k ≤ weight x)

theorem halfCeil_pos {k : ℕ} (hk : 2 ≤ k) : 1 ≤ halfCeil k := by
  unfold halfCeil
  omega

theorem halfCeil_le (k : ℕ) : halfCeil k ≤ k := by
  unfold halfCeil
  omega

theorem two_le_theoremBase {k : ℕ} (hk : 2 ≤ k) : 2 ≤ theoremBase k := by
  unfold theoremBase
  have h1 : 1 ≤ halfCeil k := halfCeil_pos hk
  have h2 : 2 ≤ k / 2 + 1 := by omega
  calc
    2 = 1 * 2 := by norm_num
    _ ≤ halfCeil k * (k / 2 + 1) := Nat.mul_le_mul h1 h2

/-- Weight is monotone in the pointwise order. -/
theorem weight_le {k : ℕ} {x y : Fin k → Bool} (h : ∀ i, x i ≤ y i) :
    weight x ≤ weight y := by
  unfold weight
  apply Finset.card_le_card
  intro i hi
  simp only [mem_supp] at hi ⊢
  exact Bool.le_iff_imp.mp (h i) hi

theorem majority_mono {k : ℕ} {x y : Fin k → Bool} (h : ∀ i, x i ≤ y i) :
    majority k x ≤ majority k y := by
  by_cases hp : halfCeil k ≤ weight x
  · have hq : halfCeil k ≤ weight y := le_trans hp (weight_le h)
    simp [majority, hp, hq]
  · simp [majority, hp]

theorem unate_majority (k : ℕ) : Unate (majority k) := by
  intro i
  left
  intro x y hxy hle
  apply majority_mono
  intro j
  by_cases hj : j = i
  · rw [hj]
    exact hle
  · exact le_of_eq (hxy j hj)

/-- In every coordinate the majority function can be changed. -/
theorem exists_majority_change (k : ℕ) (hk : 2 ≤ k) (i : Fin k) :
    ∃ x y : Fin k → Bool, (∀ j, j ≠ i → x j = y j) ∧ majority k x ≠ majority k y := by
  classical
  have hp1 : 1 ≤ halfCeil k := halfCeil_pos hk
  have hpk : halfCeil k ≤ k := halfCeil_le k
  have hle : halfCeil k - 1 ≤ (Finset.univ.erase i : Finset (Fin k)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨t, htSub, htcard⟩ := Finset.exists_subset_card_eq hle
  have hi : i ∉ t := by
    intro hmem
    have h' := htSub hmem
    simp at h'
  have hxw : weight (fun j => decide (j ∈ t)) = halfCeil k - 1 := by
    rw [weight_indicator, htcard]
  have hyw : weight (fun j => decide (j ∈ insert i t)) = halfCeil k := by
    rw [weight_indicator, Finset.card_insert_of_notMem hi]
    omega
  have hxf : majority k (fun j => decide (j ∈ t)) = false := by
    simp only [majority, hxw]
    rw [decide_eq_false_iff_not]
    omega
  have hyf : majority k (fun j => decide (j ∈ insert i t)) = true := by
    simp only [majority, hyw]
    exact decide_eq_true le_rfl
  refine ⟨fun j => decide (j ∈ t), fun j => decide (j ∈ insert i t), ?_, ?_⟩
  · intro j hj
    have hmem : j ∈ insert i t ↔ j ∈ t := by
      rw [Finset.mem_insert]
      constructor
      · rintro (h | h)
        · exact absurd h hj
        · exact h
      · exact fun h => Or.inr h
    simp [hmem]
  · rw [hxf, hyf]
    simp

/-- The majority function is not constant. -/
theorem majority_notConstant (k : ℕ) (hk : 2 ≤ k) :
    ¬ BasisFunction.IsConstant ⟨k, majority k⟩ := by
  rintro ⟨b, hb⟩
  have hp1 : 1 ≤ halfCeil k := halfCeil_pos hk
  have hw0 : weight (fun _ : Fin k => false) = 0 := by
    unfold weight supp
    simp
  have hwk : weight (fun _ : Fin k => true) = k := by
    unfold weight supp
    simp
  have h0 : majority k (fun _ : Fin k => false) = false := by
    simp only [majority, hw0]
    rw [decide_eq_false_iff_not]
    omega
  have h1 : majority k (fun _ : Fin k => true) = true := by
    simp only [majority, hwk]
    exact decide_eq_true (halfCeil_le k)
  have e0 : majority k (fun _ : Fin k => false) = b := hb (fun _ : Fin k => false)
  have e1 : majority k (fun _ : Fin k => true) = b := hb (fun _ : Fin k => true)
  rw [h0] at e0
  rw [h1] at e1
  exact Bool.noConfusion (e1.trans e0.symm)

/-- The single-gate formula computing the majority function. -/
noncomputable def majorityFormula (k : ℕ) (hk : 2 ≤ k) : Formula (Uk k) k :=
  Formula.app ⟨k, majority k⟩ (mem_Uk.mpr ⟨le_rfl, unate_majority k⟩)
    (majority_notConstant k hk) (fun i => Formula.var i)

theorem majorityFormula_eval (k : ℕ) (hk : 2 ≤ k) :
    (majorityFormula k hk).eval = majority k := by
  funext x
  rfl

theorem majority_complexity_le (k : ℕ) (hk : 2 ≤ k) :
    complexity (Uk k) (majority k) ≤ k := by
  have h1 : complexity (Uk k) (majority k) ≤ (majorityFormula k hk).complexity :=
    complexity_le_of_eval (majorityFormula_eval k hk)
  have h2 : (majorityFormula k hk).complexity ≤ k := by
    show (∑ _i : Fin k, (1 : ℕ)) ≤ k
    simp
  exact le_trans h1 h2

/-! ### The sensitivity of the majority function -/

/-- The two middle layers of the Boolean cube prove the sensitivity bound for
the majority function. -/
theorem sensitivity_majority_ge (k : ℕ) (hk : 2 ≤ k) :
    (theoremBase k : ℝ) ≤ sensitivity (majority k) := by
  classical
  set p := halfCeil k with hp_def
  set w := p - 1 with hw_def
  have hp1 : 1 ≤ p := halfCeil_pos hk
  have hpk : p ≤ k := halfCeil_le k
  have hD : k - p = k / 2 := by
    rw [hp_def]
    unfold halfCeil
    exact Nat.sub_sub_self (Nat.div_le_self k 2)
  have hw1 : w + 1 = p := by omega
  have hkw : k - w = k / 2 + 1 := by omega
  have hbase : theoremBase k = (k - w) * (w + 1) := by
    rw [hkw, hw1]
    unfold theoremBase
    rw [← hp_def]
    exact Nat.mul_comm _ _
  have hNne : (layer k w).Nonempty := layer_nonempty (k := k) (w := w) (by omega)
  have hPne : (layer k p).Nonempty := layer_nonempty (k := k) (w := p) hpk
  have hzero : ∀ x ∈ layer k w, majority k x = false := by
    intro x hx
    rw [mem_layer] at hx
    simp only [majority, hx]
    rw [decide_eq_false_iff_not]
    omega
  have hone : ∀ y ∈ layer k p, majority k y = true := by
    intro y hy
    rw [mem_layer] at hy
    simp only [majority, hy]
    exact decide_eq_true le_rfl
  have hNpos : (0 : ℝ) < ((layer k w).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hNne
  have hPpos : (0 : ℝ) < ((layer k p).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hPne
  have hR1 : ((neighborPairs (layer k w) (layer k p)).card : ℝ) =
      ((layer k w).card : ℝ) * ((k - w : ℕ) : ℝ) := by
    rw [← hw1]
    exact_mod_cast card_neighborPairs_left (k := k) (w := w)
  have hR2 : ((neighborPairs (layer k w) (layer k p)).card : ℝ) =
      ((layer k p).card : ℝ) * ((w + 1 : ℕ) : ℝ) := by
    rw [← hw1]
    exact_mod_cast card_neighborPairs_right (k := k) (w := w)
  have hsq : ((neighborPairs (layer k w) (layer k p)).card : ℝ) ^ 2 =
      (((layer k w).card : ℝ) * ((k - w : ℕ) : ℝ)) *
        (((layer k p).card : ℝ) * ((w + 1 : ℕ) : ℝ)) := by
    calc ((neighborPairs (layer k w) (layer k p)).card : ℝ) ^ 2
        = ((neighborPairs (layer k w) (layer k p)).card : ℝ) *
            ((neighborPairs (layer k w) (layer k p)).card : ℝ) := by ring
      _ = (((layer k w).card : ℝ) * ((k - w : ℕ) : ℝ)) *
            ((neighborPairs (layer k w) (layer k p)).card : ℝ) := by rw [hR1]
      _ = (((layer k w).card : ℝ) * ((k - w : ℕ) : ℝ)) *
            (((layer k p).card : ℝ) * ((w + 1 : ℕ) : ℝ)) := by rw [hR2]
  have hratio : (theoremBase k : ℝ) =
      ((neighborPairs (layer k w) (layer k p)).card : ℝ) ^ 2 /
        (((layer k w).card : ℝ) * ((layer k p).card : ℝ)) := by
    rw [hbase, hsq]
    push_cast
    field_simp
  have hmem : (theoremBase k : ℝ) ∈ sensitivityValues (majority k) :=
    ⟨layer k w, layer k p, hNne, hPne, hzero, hone, hratio⟩
  exact le_csSup (sensitivityValues_bddAbove (majority k)) hmem

/-! ### The complexity of the majority function -/

namespace Formula

variable {B : Set BasisFunction} {n : ℕ}

/-- The set of variables occurring in a formula. -/
def varSet : Formula B n → Finset (Fin n)
  | const _ _ => ∅
  | var i => {i}
  | app _ _ _ args => Finset.univ.biUnion (fun i => (args i).varSet)

@[simp]
theorem varSet_const (b : Bool) (hb : ConstantIn B b) :
    (const b hb : Formula B n).varSet = ∅ := rfl

@[simp]
theorem varSet_var (i : Fin n) : (var (B := B) i).varSet = {i} := rfl

@[simp]
theorem varSet_app (g : BasisFunction) (hg : g ∈ B) (h : ¬ g.IsConstant)
    (args : Fin g.1 → Formula B n) :
    (app g hg h args).varSet = Finset.univ.biUnion (fun i => (args i).varSet) := rfl

theorem card_varSet_le_complexity (F : Formula B n) : F.varSet.card ≤ F.complexity := by
  induction F with
  | const b hb => simp
  | var i => simp
  | app g hg h args ih =>
      rw [varSet_app, complexity_app]
      calc (Finset.univ.biUnion fun i => (args i).varSet).card
          ≤ ∑ i : Fin g.1, (args i).varSet.card := Finset.card_biUnion_le
        _ ≤ ∑ i : Fin g.1, (args i).complexity :=
            Finset.sum_le_sum (fun i _ => ih i)

theorem eval_eq_of_forall_mem_varSet {F : Formula B n} {x y : Fin n → Bool}
    (h : ∀ i ∈ F.varSet, x i = y i) : F.eval x = F.eval y := by
  induction F with
  | const b hb => rfl
  | var i => exact h i (by simp)
  | app g hg hc args ih =>
      show g.2 (fun j => (args j).eval x) = g.2 (fun j => (args j).eval y)
      have hfun : (fun j => (args j).eval x) = (fun j => (args j).eval y) := by
        funext j
        exact ih j (fun i hi => h i (by
          rw [varSet_app]
          exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hi⟩))
      rw [hfun]

theorem exists_not_mem_varSet {F : Formula B n} (h : F.complexity < n) :
    ∃ i, i ∉ F.varSet := by
  by_contra hc
  push Not at hc
  have huniv : F.varSet = Finset.univ := Finset.eq_univ_of_forall hc
  have hcard := card_varSet_le_complexity F
  rw [huniv, Finset.card_univ, Fintype.card_fin] at hcard
  omega

theorem eval_indep_of_not_mem_varSet {F : Formula B n} {i : Fin n} (hi : i ∉ F.varSet)
    {x y : Fin n → Bool} (h : ∀ j, j ≠ i → x j = y j) : F.eval x = F.eval y :=
  eval_eq_of_forall_mem_varSet (fun j hj => h j (fun hji => hi (hji ▸ hj)))

end Formula

/-- The majority function needs at least `k` variable leaves. -/
theorem k_le_complexity_majority (k : ℕ) (hk : 2 ≤ k) :
    k ≤ complexity (Uk k) (majority k) := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨F, hF, hc⟩ := Nat.sInf_mem
    (s := {L : ℕ | ∃ F : Formula (Uk k) k, F.eval = majority k ∧ F.complexity = L})
    ⟨(majorityFormula k hk).complexity, majorityFormula k hk, majorityFormula_eval k hk, rfl⟩
  have hFlt : F.complexity < k := by
    rw [show F.complexity = complexity (Uk k) (majority k) from hc]
    exact hlt
  obtain ⟨i, hi⟩ := Formula.exists_not_mem_varSet hFlt
  obtain ⟨x, y, hxy, hne⟩ := exists_majority_change k hk i
  have hsame := Formula.eval_indep_of_not_mem_varSet hi hxy
  rw [hF] at hsame
  exact hne hsame

theorem majority_complexity (k : ℕ) (hk : 2 ≤ k) :
    complexity (Uk k) (majority k) = k :=
  le_antisymm (majority_complexity_le k hk) (k_le_complexity_majority k hk)

/-! ### Theorem 1 -/

theorem khrapchenko_bound_le_log (k : ℕ) (hk : 2 ≤ k) {χ : ℝ}
    (hχ : KhrapchenkoBound (Uk k) χ) :
    χ ≤ Real.log (k : ℝ) / Real.log (theoremBase k : ℝ) := by
  classical
  have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hq2 : (2 : ℝ) ≤ (theoremBase k : ℝ) := by
    exact_mod_cast two_le_theoremBase hk
  have hq1 : (1 : ℝ) < (theoremBase k : ℝ) := lt_of_lt_of_le (by norm_num) hq2
  have hq0 : (0 : ℝ) < (theoremBase k : ℝ) := by linarith
  have hexp : Expressible (Uk k) (majority k) :=
    ⟨majorityFormula k hk, majorityFormula_eval k hk⟩
  have hsens : (theoremBase k : ℝ) ≤ sensitivity (majority k) :=
    sensitivity_majority_ge k hk
  have hb := hχ k (majority k) hexp
  rw [majority_complexity k hk] at hb
  by_contra hcon
  push Not at hcon
  have hcpos : 0 < Real.log (k : ℝ) / Real.log (theoremBase k : ℝ) :=
    div_pos (Real.log_pos hk1) (Real.log_pos hq1)
  have hχpos : 0 < χ := lt_trans hcpos hcon
  have hle1 : (theoremBase k : ℝ) ^ χ ≤ sensitivity (majority k) ^ χ :=
    Real.rpow_le_rpow (le_of_lt hq0) hsens (le_of_lt hχpos)
  have hle2 : (theoremBase k : ℝ) ^ χ ≤ (k : ℝ) := le_trans hle1 hb
  have hlog : χ * Real.log (theoremBase k : ℝ) ≤ Real.log (k : ℝ) :=
    (Real.rpow_le_iff_le_log (x := (theoremBase k : ℝ)) (y := (k : ℝ)) hq0 (by linarith)).mp hle2
  have hbound : χ ≤ Real.log (k : ℝ) / Real.log (theoremBase k : ℝ) := by
    rw [le_div_iff₀ (Real.log_pos hq1)]
    exact hlog
  exact absurd hbound (not_le.mpr hcon)

/-- Theorem 1: `χ_{U_k} ≤ log_{⌈k/2⌉(⌊k/2⌋+1)} k`. -/
theorem theorem1 (k : ℕ) (hk : 2 ≤ k) :
    khrapchenkoExponent (Uk k) ≤ Real.log (k : ℝ) / Real.log (theoremBase k : ℝ) := by
  unfold khrapchenkoExponent
  apply Real.sSup_le
  · intro χ hχ
    exact khrapchenko_bound_le_log k hk hχ
  · have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hq2 : (2 : ℝ) ≤ (theoremBase k : ℝ) := by
      exact_mod_cast two_le_theoremBase hk
    have hq1 : (1 : ℝ) < (theoremBase k : ℝ) := lt_of_lt_of_le (by norm_num) hq2
    exact le_of_lt (div_pos (Real.log_pos hk1) (Real.log_pos hq1))

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem ratio_of_admissible (G : BipartiteGraph A B) {X : Finset A} {Y : Finset B}
    (h : G.Admissible X Y) :
    G.ratio X Y = (G.edgeCount X Y : ℝ) ^ 2 / ((X.card : ℝ) * (Y.card : ℝ)) := by
  simp [BipartiteGraph.ratio, h]

theorem ratio_le_sGraph (G : BipartiteGraph A B) {X : Finset A} {Y : Finset B}
    (h : G.Admissible X Y) : G.ratio X Y ≤ G.sGraph := by
  classical
  unfold BipartiteGraph.sGraph
  exact Finset.le_sup' (fun p : Finset A × Finset B => G.ratio p.1 p.2) (Finset.mem_univ (X, Y))

theorem sGraph_ge_full (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (h : G.Admissible X Y) :
    (G.edgeCount X Y : ℝ) ^ 2 / ((X.card : ℝ) * (Y.card : ℝ)) ≤ G.sGraph := by
  rw [← ratio_of_admissible G h]
  exact ratio_le_sGraph G h

theorem edgeCount_graphOn_self (T : A → B → Bool) (X : Finset A) (Y : Finset B) :
    (graphOn T X Y).edgeCount X Y = ((X.product Y).filter fun q => T q.1 q.2).card := by
  classical
  unfold graphOn BipartiteGraph.edgeCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro q hq
  have hq' : q.1 ∈ X ∧ q.2 ∈ Y := Finset.mem_product.mp hq
  simp [graphOn, hq'.1, hq'.2]

theorem graphOn_left (T : A → B → Bool) (X : Finset A) (Y : Finset B) :
    (graphOn T X Y).left = (↑X : Set A) := rfl

theorem graphOn_right (T : A → B → Bool) (X : Finset A) (Y : Finset B) :
    (graphOn T X Y).right = (↑Y : Set B) := rfl

theorem edgeCount_graphOn_self' (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B) :
    (graphOn G.edge X Y).edgeCount X Y = G.edgeCount X Y := by
  classical
  unfold BipartiteGraph.edgeCount graphOn
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro q hq
  have hq' : q.1 ∈ X ∧ q.2 ∈ Y := Finset.mem_product.mp hq
  simp [hq'.1, hq'.2]

theorem exists_densitySubgraph (G : BipartiteGraph A B) :
    ∃ (X : Finset A) (Y : Finset B),
      (graphOn G.edge X Y).sGraph = G.sGraph ∧
      (graphOn G.edge X Y).sGraph = G.ratio X Y ∧
      G.Admissible X Y ∧ (graphOn G.edge X Y).ratio X Y = G.ratio X Y := by
  classical
  obtain ⟨X, Y, hAdm, hsG⟩ := BipartiteGraph.exists_admissible_eq_sGraph G
  have hAdm' : (graphOn G.edge X Y).Admissible X Y :=
    ⟨fun a ha => ha, fun b hb => hb⟩
  have hHratio : (graphOn G.edge X Y).ratio X Y = G.ratio X Y := by
    rw [ratio_of_admissible _ hAdm', ratio_of_admissible G hAdm,
      edgeCount_graphOn_self']
  have hHsG : (graphOn G.edge X Y).sGraph = G.sGraph := by
    apply le_antisymm
    · apply BipartiteGraph.sGraph_mono
      · intro a ha
        exact hAdm.1 a ha
      · intro b hb
        exact hAdm.2 b hb
      · intro a b h
        simp only [graphOn, Bool.and_eq_true, decide_eq_true_eq] at h
        exact h.1.1
    · rw [hsG, ← hHratio]
      exact ratio_le_sGraph _ hAdm'
  exact ⟨X, Y, hHsG, by rw [hHsG, hsG], hAdm, hHratio⟩

/-- Restrict a graph to the vertex sets `X`, `Y`: parts are intersected with
`X`, `Y` and edges are restricted accordingly. -/
def frag (H : BipartiteGraph A B) (X : Finset A) (Y : Finset B) : BipartiteGraph A B where
  left := H.left ∩ {a | a ∈ X}
  right := H.right ∩ {b | b ∈ Y}
  edge := fun a b => H.edge a b && decide (a ∈ X) && decide (b ∈ Y)

theorem frag_left_subset (H : BipartiteGraph A B) (X : Finset A) (Y : Finset B) :
    (frag H X Y).left ⊆ H.left := fun _ ha => ha.1

theorem frag_right_subset (H : BipartiteGraph A B) (X : Finset A) (Y : Finset B) :
    (frag H X Y).right ⊆ H.right := fun _ hb => hb.1

theorem frag_edge_subset (H : BipartiteGraph A B) (X : Finset A) (Y : Finset B) :
    ∀ a b, (frag H X Y).edge a b = true → H.edge a b = true := by
  intro a b h
  simp only [frag, Bool.and_eq_true] at h
  exact h.1.1

theorem sGraph_frag_le (H : BipartiteGraph A B) (X : Finset A) (Y : Finset B) :
    (frag H X Y).sGraph ≤ H.sGraph :=
  BipartiteGraph.sGraph_mono (frag_left_subset H X Y) (frag_right_subset H X Y)
    (frag_edge_subset H X Y)

theorem frag_edgeRestriction {G H : BipartiteGraph A B} (X : Finset A) (Y : Finset B)
    (hHG : EdgeRestriction G H) :
    EdgeRestriction (graphOn G.edge X Y) (frag H X Y) := by
  intro a b
  constructor
  · intro h
    simp only [frag, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hHe, haX⟩, hbY⟩ := h
    obtain ⟨hGe, haH, hbH⟩ := (hHG a b).mp hHe
    refine ⟨?_, ⟨haH, haX⟩, ⟨hbH, hbY⟩⟩
    simpa [graphOn, haX, hbY] using hGe
  · rintro ⟨hGe, ⟨haH, haX⟩, ⟨hbH, hbY⟩⟩
    simp only [graphOn, Bool.and_eq_true, decide_eq_true_eq] at hGe
    obtain ⟨⟨hE, -⟩, -⟩ := hGe
    have hHe : H.edge a b = true := (hHG a b).mpr ⟨hE, haH, hbH⟩
    simp only [frag, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hHe, haX⟩, hbY⟩

theorem cover_frag {G : BipartiteGraph A B} {m : ℕ} {Gs : Fin m → BipartiteGraph A B}
    (hcover : IsCover G Gs) (X : Finset A) (Y : Finset B) :
    IsCover (graphOn G.edge X Y) (fun i => frag (Gs i) X Y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i a ha
    exact ha.2
  · intro i b hb
    exact hb.2
  · intro i
    exact frag_edgeRestriction X Y (hcover.2.2.1 i)
  · intro a b h
    simp only [graphOn, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hE, haX⟩, hbY⟩ := h
    obtain ⟨i, hi⟩ := hcover.2.2.2 a b hE
    exact ⟨i, by simp [frag, hi, haX, hbY]⟩

noncomputable def partRight (Y : Finset B) (S : Set B) : Finset B := by
  classical
  exact Y.filter (fun b => b ∈ S)

noncomputable def partLeft (X : Finset A) (S : Set A) : Finset A := by
  classical
  exact X.filter (fun a => a ∈ S)

@[simp] theorem mem_partRight {Y : Finset B} {S : Set B} {b : B} :
    b ∈ partRight Y S ↔ b ∈ Y ∧ b ∈ S := by
  classical
  simp [partRight]

@[simp] theorem mem_partLeft {X : Finset A} {S : Set A} {a : A} :
    a ∈ partLeft X S ↔ a ∈ X ∧ a ∈ S := by
  classical
  simp [partLeft]

theorem cover_frag_erase_right {G : BipartiteGraph A B} {n : ℕ}
    {Gs : Fin (n + 1) → BipartiteGraph A B} (hcover : IsCover G Gs)
    (X : Finset A) (Y : Finset B) (j : Fin (n + 1)) :
    IsCover (graphOn G.edge X (Y \ partRight Y (Gs j).right))
      (fun i : Fin n =>
        frag (Gs (j.succAbove i)) X (Y \ partRight Y (Gs j).right)) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i a ha
    exact ha.2
  · intro i b hb
    exact hb.2
  · intro i
    exact frag_edgeRestriction _ _ (hcover.2.2.1 (j.succAbove i))
  · intro a b h
    simp only [graphOn, Bool.and_eq_true, decide_eq_true_eq, Finset.mem_sdiff] at h
    obtain ⟨⟨hE, haX⟩, hbY, hbB⟩ := h
    obtain ⟨i, hi⟩ := hcover.2.2.2 a b hE
    have hij : i ≠ j := by
      intro hEq
      subst i
      have hbR : b ∈ (Gs j).right := ((hcover.2.2.1 j) a b).mp hi |>.2.2
      exact hbB (mem_partRight.mpr ⟨hbY, hbR⟩)
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij
    refine ⟨k, ?_⟩
    simp only [frag, Bool.and_eq_true, decide_eq_true_eq, Finset.mem_sdiff]
    exact ⟨⟨hi, haX⟩, hbY, hbB⟩

theorem cover_frag_erase_left {G : BipartiteGraph A B} {n : ℕ}
    {Gs : Fin (n + 1) → BipartiteGraph A B} (hcover : IsCover G Gs)
    (X : Finset A) (Y : Finset B) (j : Fin (n + 1)) :
    IsCover (graphOn G.edge (X \ partLeft X (Gs j).left) Y)
      (fun i : Fin n =>
        frag (Gs (j.succAbove i)) (X \ partLeft X (Gs j).left) Y) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i a ha
    exact ha.2
  · intro i b hb
    exact hb.2
  · intro i
    exact frag_edgeRestriction _ _ (hcover.2.2.1 (j.succAbove i))
  · intro a b h
    simp only [graphOn, Bool.and_eq_true, decide_eq_true_eq, Finset.mem_sdiff] at h
    obtain ⟨⟨hE, haX, haA⟩, hbY⟩ := h
    obtain ⟨i, hi⟩ := hcover.2.2.2 a b hE
    have hij : i ≠ j := by
      intro hEq
      subst i
      have haL : a ∈ (Gs j).left := ((hcover.2.2.1 j) a b).mp hi |>.2.1
      exact haA (mem_partLeft.mpr ⟨haX, haL⟩)
    obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hij
    refine ⟨k, ?_⟩
    simp only [frag, Bool.and_eq_true, decide_eq_true_eq, Finset.mem_sdiff]
    exact ⟨⟨hi, haX, haA⟩, hbY⟩

theorem rpow_sum_le_sum_rpow {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    (∑ i ∈ s, f i) ^ r ≤ ∑ i ∈ s, f i ^ r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow hr0.ne']
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have ha0 : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have hs0 : 0 ≤ ∑ i ∈ s, f i :=
        Finset.sum_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
      calc
        (f a + ∑ i ∈ s, f i) ^ r ≤ f a ^ r + (∑ i ∈ s, f i) ^ r :=
          Real.rpow_add_le_add_rpow ha0 hs0 hr0.le hr1
        _ ≤ f a ^ r + ∑ i ∈ s, f i ^ r := by
          have hih : (∑ i ∈ s, f i) ^ r ≤ ∑ i ∈ s, f i ^ r :=
            ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
          linarith

theorem isGraphExponent_of_le {k : ℕ} {χ χ' : ℝ} (hχ0 : 0 < χ) (hχχ' : χ ≤ χ')
    (h : IsGraphExponent k χ') : IsGraphExponent k χ := by
  intro m hm A B _ _ _ _ G Gs hcover
  have h' := h m hm A B G Gs hcover
  have hχ'0 : 0 < χ' := lt_of_lt_of_le hχ0 hχχ'
  have hG0 : 0 ≤ G.sGraph := BipartiteGraph.sGraph_nonneg G
  by_cases hzero : G.sGraph = 0
  · rw [hzero, Real.zero_rpow hχ0.ne']
    exact Finset.sum_nonneg fun i _ =>
      Real.rpow_nonneg (BipartiteGraph.sGraph_nonneg (Gs i)) χ
  · have hGpos : 0 < G.sGraph := lt_of_le_of_ne hG0 (Ne.symm hzero)
    set S : ℝ := ∑ i, (Gs i).sGraph ^ χ' with hS
    have hSpos : 0 < S := lt_of_lt_of_le (Real.rpow_pos_of_pos hGpos χ') h'
    have hr0 : 0 < χ / χ' := div_pos hχ0 hχ'0
    have hr1 : χ / χ' ≤ 1 := (div_le_one hχ'0).mpr hχχ'
    have hsub : S ^ (χ / χ') ≤ ∑ i, ((Gs i).sGraph ^ χ') ^ (χ / χ') := by
      rw [hS]
      exact rpow_sum_le_sum_rpow Finset.univ (fun i => (Gs i).sGraph ^ χ')
        (fun i _ => Real.rpow_nonneg (BipartiteGraph.sGraph_nonneg (Gs i)) χ') hr0 hr1
    have hT : ∑ i, ((Gs i).sGraph ^ χ') ^ (χ / χ') = ∑ i, (Gs i).sGraph ^ χ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Real.rpow_mul (BipartiteGraph.sGraph_nonneg (Gs i))]
      congr 1
      field_simp
    have hleft : G.sGraph ^ χ = (G.sGraph ^ χ') ^ (χ / χ') := by
      rw [← Real.rpow_mul hG0]
      congr 1
      field_simp
    rw [hleft]
    exact le_trans (Real.rpow_le_rpow (Real.rpow_nonneg hG0 χ') h' hr0.le)
      (by rw [← hT]; exact hsub)

theorem sGraph_eq_zero_of_no_edges {G : BipartiteGraph A B}
    (h : ∀ a b, G.edge a b = false) : G.sGraph = 0 := by
  classical
  apply le_antisymm
  · unfold BipartiteGraph.sGraph
    apply Finset.sup'_le
    intro p _
    simp [BipartiteGraph.ratio, BipartiteGraph.edgeCount, h]
  · exact BipartiteGraph.sGraph_nonneg G

theorem sGraph_le_of_ratio_le {G H : BipartiteGraph A B}
    (h : ∀ X : Finset A, ∀ Y : Finset B, G.ratio X Y ≤ H.sGraph) :
    G.sGraph ≤ H.sGraph := by
  classical
  unfold BipartiteGraph.sGraph
  apply Finset.sup'_le
  intro p _
  exact h p.1 p.2

theorem sGraph_le_of_cover_one {G : BipartiteGraph A B} {Gs : Fin 1 → BipartiteGraph A B}
    (hcover : IsCover G Gs) : G.sGraph ≤ (Gs 0).sGraph := by
  classical
  apply sGraph_le_of_ratio_le
  intro X Y
  by_cases hAdm : G.Admissible X Y
  · let X' : Finset A := partLeft X (Gs 0).left
    let Y' : Finset B := partRight Y (Gs 0).right
    have hX'sub : X' ⊆ X := by
      intro a ha
      have ha' : a ∈ partLeft X (Gs 0).left := by simpa [X'] using ha
      exact (mem_partLeft.mp ha').1
    have hY'sub : Y' ⊆ Y := by
      intro b hb
      have hb' : b ∈ partRight Y (Gs 0).right := by simpa [Y'] using hb
      exact (mem_partRight.mp hb').1
    have hAdm' : (Gs 0).Admissible X' Y' :=
      ⟨fun a ha => (mem_partLeft.mp (by simpa [X'] using ha)).2,
       fun b hb => (mem_partRight.mp (by simpa [Y'] using hb)).2⟩
    have hEdgeEq : (Gs 0).edgeCount X' Y' = G.edgeCount X Y := by
      apply le_antisymm
      · unfold BipartiteGraph.edgeCount
        apply Finset.card_le_card
        rintro ⟨a, b⟩ hq
        simp only [Finset.mem_filter] at hq ⊢
        obtain ⟨hqprod, hqE⟩ := hq
        have hp : (a, b) ∈ X' ×ˢ Y' := hqprod
        rw [Finset.mem_product] at hp
        obtain ⟨haX', hbY'⟩ := hp
        have hGe : G.edge a b = true :=
          ((hcover.2.2.1 0) a b).mp hqE |>.1
        refine ⟨?_, hGe⟩
        change (a, b) ∈ X ×ˢ Y
        rw [Finset.mem_product]
        exact ⟨hX'sub haX', hY'sub hbY'⟩
      · unfold BipartiteGraph.edgeCount
        apply Finset.card_le_card
        rintro ⟨a, b⟩ hq
        simp only [Finset.mem_filter] at hq ⊢
        obtain ⟨hqprod, hqE⟩ := hq
        have hp : (a, b) ∈ X ×ˢ Y := hqprod
        rw [Finset.mem_product] at hp
        obtain ⟨haX, hbY⟩ := hp
        obtain ⟨i, hi⟩ := hcover.2.2.2 a b hqE
        obtain ⟨-, haL, hbR⟩ := ((hcover.2.2.1 i) a b).mp hi
        have hi0 : i = 0 := Subsingleton.elim i 0
        subst hi0
        have haX' : a ∈ X' := by
          dsimp [X']
          exact mem_partLeft.mpr ⟨haX, haL⟩
        have hbY' : b ∈ Y' := by
          dsimp [Y']
          exact mem_partRight.mpr ⟨hbY, hbR⟩
        refine ⟨?_, hi⟩
        change (a, b) ∈ X' ×ˢ Y'
        rw [Finset.mem_product]
        exact ⟨haX', hbY'⟩
    have hchain : G.ratio X Y ≤ (Gs 0).ratio X' Y' := by
      rw [ratio_of_admissible G hAdm, ratio_of_admissible (Gs 0) hAdm', hEdgeEq]
      by_cases hE : G.edgeCount X Y = 0
      · simp [hE]
      · have hEpos : 0 < G.edgeCount X Y := Nat.pos_of_ne_zero hE
        obtain ⟨⟨a, b⟩, hq⟩ := Finset.card_pos.mp hEpos
        have hq' : (a, b) ∈ (X.product Y).filter (fun q => G.edge q.1 q.2) := by
          simpa [BipartiteGraph.edgeCount] using hq
        simp only [Finset.mem_filter] at hq'
        obtain ⟨hqprod, hqE⟩ := hq'
        have hp : (a, b) ∈ X ×ˢ Y := hqprod
        rw [Finset.mem_product] at hp
        obtain ⟨haX, hbY⟩ := hp
        obtain ⟨i0, hi0⟩ := hcover.2.2.2 a b hqE
        have hi0' : i0 = 0 := Subsingleton.elim i0 0
        subst hi0'
        obtain ⟨-, haL, hbR⟩ := ((hcover.2.2.1 0) a b).mp hi0
        have haX' : a ∈ X' := by
          dsimp [X']
          exact mem_partLeft.mpr ⟨haX, haL⟩
        have hbY' : b ∈ Y' := by
          dsimp [Y']
          exact mem_partRight.mpr ⟨hbY, hbR⟩
        have hX'pos : 0 < X'.card := Finset.card_pos.mpr ⟨a, haX'⟩
        have hY'pos : 0 < Y'.card := Finset.card_pos.mpr ⟨b, hbY'⟩
        have hX'le : (X'.card : ℝ) ≤ (X.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hX'sub
        have hY'le : (Y'.card : ℝ) ≤ (Y.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hY'sub
        have hX'posR : (0 : ℝ) < (X'.card : ℝ) := by exact_mod_cast hX'pos
        have hY'posR : (0 : ℝ) < (Y'.card : ℝ) := by exact_mod_cast hY'pos
        have hdenpos : (0 : ℝ) < (X'.card : ℝ) * (Y'.card : ℝ) := mul_pos hX'posR hY'posR
        have hdenle : (X'.card : ℝ) * (Y'.card : ℝ) ≤ (X.card : ℝ) * (Y.card : ℝ) :=
          mul_le_mul hX'le hY'le hY'posR.le (by positivity)
        exact div_le_div₀ (by positivity) le_rfl hdenpos hdenle
    exact le_trans hchain (ratio_le_sGraph _ hAdm')
  · have h0 : G.ratio X Y = 0 := by simp [BipartiteGraph.ratio, hAdm]
    rw [h0]
    exact BipartiteGraph.sGraph_nonneg (Gs 0)

theorem isGraphExponent_one : IsGraphExponent 1 1 := by
  intro m hm A B _ _ _ _ G Gs hcover
  have hm01 : m = 0 ∨ m = 1 := by omega
  rcases hm01 with rfl | rfl
  · have hno : ∀ a b, G.edge a b = false := by
      intro a b
      by_contra h
      have htrue : G.edge a b = true := by simpa using h
      obtain ⟨i, _⟩ := hcover.2.2.2 a b htrue
      exact Fin.elim0 i
    rw [sGraph_eq_zero_of_no_edges hno]
    simp
  · simpa using sGraph_le_of_cover_one hcover

theorem g_le_one {χ t : ℝ} (hχ1 : (1 : ℝ) / 2 < χ) (hχ2 : χ ≤ 2 / 3)
    (ht0 : (13 : ℝ) / 16 ≤ t) (ht1 : t ≤ 1) :
    t ^ (2 * χ / (2 * χ - 1)) + (4 * (1 - t)) ^ (χ / (2 * χ - 1)) ≤ 1 := by
  have hχ0 : 0 < χ := by linarith
  have hden : 0 < 2 * χ - 1 := by linarith
  have hQ4 : 4 ≤ 2 * χ / (2 * χ - 1) := by
    rw [le_div_iff₀ hden]
    nlinarith
  have hQ2 : 2 ≤ χ / (2 * χ - 1) := by
    rw [le_div_iff₀ hden]
    nlinarith
  have ht0' : 0 ≤ t := by linarith
  have hu0 : 0 ≤ 4 * (1 - t) := by nlinarith
  have hu1 : 4 * (1 - t) ≤ 1 := by nlinarith
  have h1 : t ^ (2 * χ / (2 * χ - 1)) ≤ t ^ (4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge' ht0' ht1 (by norm_num) hQ4
  have h2 : (4 * (1 - t)) ^ (χ / (2 * χ - 1)) ≤ (4 * (1 - t)) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge' hu0 hu1 (by norm_num) hQ2
  have h3 : t ^ (4 : ℝ) + (4 * (1 - t)) ^ (2 : ℝ) ≤ 1 := by
    have hpoly : t ^ 4 + (4 * (1 - t)) ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (1 - t), sq_nonneg ((1 - t) - 3 / 16),
        mul_nonneg (sub_nonneg.mpr ht1) (sq_nonneg (3 / 16 - (1 - t)))]
    simpa using hpoly
  linarith

theorem holder_two_sum_one {p q x1 x2 y1 y2 : ℝ} (hpq : p.HolderConjugate q)
    (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2)
    (hsum : x1 * y1 + x2 * y2 = 1) (hB : 0 < y1 ^ q + y2 ^ q) :
    1 / (y1 ^ q + y2 ^ q) ^ (p / q) ≤ x1 ^ p + x2 ^ p := by
  have hp : 1 < p := (Real.holderConjugate_iff.mp hpq).1
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < q := by
    have hq := hpq.conjugate_eq
    rw [hq]
    exact div_pos hp0 (by linarith)
  set A : ℝ := x1 ^ p + x2 ^ p with hA
  set B : ℝ := y1 ^ q + y2 ^ q with hBdef
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have hHolder := Real.inner_le_Lp_mul_Lq_of_nonneg (Finset.univ : Finset (Fin 2))
    (f := fun i : Fin 2 => if i = 0 then x1 else x2)
    (g := fun i : Fin 2 => if i = 0 then y1 else y2) hpq
    (by intro i _; fin_cases i <;> simp [hx1, hx2])
    (by intro i _; fin_cases i <;> simp [hy1, hy2])
  have hHolder' : x1 * y1 + x2 * y2 ≤ A ^ (1 / p) * B ^ (1 / q) := by
    simpa [A, B, Fin.sum_univ_two] using hHolder
  have h1 : (1 : ℝ) ≤ A ^ (1 / p) * B ^ (1 / q) := by simpa [hsum] using hHolder'
  have hpoweq : (A ^ p⁻¹ * B ^ q⁻¹) ^ p = A * B ^ (p / q) := by
    rw [Real.mul_rpow (Real.rpow_nonneg hA0 _) (Real.rpow_nonneg hB0 _)]
    rw [← Real.rpow_mul hA0, ← Real.rpow_mul hB0]
    have hAexp : A ^ (p⁻¹ * p) = A := by
      rw [inv_mul_cancel₀ hp0.ne', Real.rpow_one]
    have hBexp : B ^ (q⁻¹ * p) = B ^ (p / q) := by ring_nf
    rw [hAexp, hBexp]
  have hpoweq' : (A ^ (1 / p) * B ^ (1 / q)) ^ p = A * B ^ (p / q) := by
    simpa [one_div] using hpoweq
  have h2 : (1 : ℝ) ≤ A * B ^ (p / q) := by
    have hle := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) h1 hp0.le
    rw [Real.one_rpow, hpoweq'] at hle
    exact hle
  have hBpow : 0 < B ^ (p / q) := Real.rpow_pos_of_pos hB (p / q)
  have h3 : 1 / B ^ (p / q) ≤ A := (div_le_iff₀ hBpow).mpr (by simpa [mul_comm] using h2)
  simpa [A, B] using h3

theorem two_sqrt_rpow {u q : ℝ} (hu : 0 ≤ u) :
    (2 * Real.sqrt u) ^ q = (4 * u) ^ (q / 2) := by
  have h2u : 0 ≤ 2 * Real.sqrt u := by positivity
  have hsq : (2 * Real.sqrt u) ^ 2 = 4 * u := by
    nlinarith [Real.sq_sqrt hu]
  have hroot : 2 * Real.sqrt u = Real.sqrt (4 * u) := by
    rw [show Real.sqrt (4 * u) = Real.sqrt ((2 * Real.sqrt u) ^ 2) from by rw [hsq]]
    exact (Real.sqrt_sq h2u).symm
  rw [hroot, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

theorem sqrt_add_le_two_sqrt {a b : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    Real.sqrt (1 - a) + Real.sqrt (1 - b) ≤ 2 * Real.sqrt (1 - (a + b) / 2) := by
  rw [← Real.sqrt_sq (show (0:ℝ) ≤ Real.sqrt (1-a) + Real.sqrt (1-b) by positivity),
    ← Real.sqrt_sq (show (0:ℝ) ≤ 2*Real.sqrt (1-(a+b)/2) by positivity)]
  apply Real.sqrt_le_sqrt
  nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 1-a by linarith),
    Real.sq_sqrt (show (0:ℝ) ≤ 1-b by linarith),
    Real.sq_sqrt (show (0:ℝ) ≤ 1-(a+b)/2 by linarith),
    sq_nonneg (Real.sqrt (1-a) - Real.sqrt (1-b))]

theorem g_le_one_sqrt {χ t : ℝ} (hχ1 : (1 : ℝ) / 2 < χ) (hχ2 : χ ≤ 2 / 3)
    (ht0 : (13 : ℝ) / 16 ≤ t) (ht1 : t ≤ 1) :
    t ^ (2 * χ / (2 * χ - 1)) + (2 * Real.sqrt (1 - t)) ^ (2 * χ / (2 * χ - 1)) ≤ 1 := by
  have hu : 0 ≤ 1 - t := by linarith
  rw [two_sqrt_rpow hu]
  have hq : (2 * χ / (2 * χ - 1)) / 2 = χ / (2 * χ - 1) := by ring
  rw [hq]
  exact g_le_one hχ1 hχ2 ht0 ht1

theorem sqrt_bound {Xc Yc A B t : ℝ} (hXc : 0 < Xc) (hYc : 0 < Yc)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAle : A ≤ Xc) (hBle : B ≤ Yc)
    (ht : t = (A / Xc + B / Yc) / 2) (ht1 : t ≤ 1) :
    Real.sqrt (Xc * (Yc - B)) + Real.sqrt ((Xc - A) * Yc) ≤
      2 * Real.sqrt (Xc * Yc * (1 - t)) := by
  set a := A / Xc
  set b := B / Yc
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact (div_le_one hXc).mpr hAle
  have hb1 : b ≤ 1 := by
    dsimp [b]
    exact (div_le_one hYc).mpr hBle
  have ht' : t = (a + b) / 2 := by rw [ht]
  have hu' : Xc * (Yc - B) = Xc * Yc * (1 - b) := by
    dsimp [b]
    field_simp
  have hv' : (Xc - A) * Yc = Xc * Yc * (1 - a) := by
    dsimp [a]
    field_simp
  have hXY : 0 ≤ Xc * Yc := by positivity
  have h1b : 0 ≤ 1 - b := by linarith
  have h1a : 0 ≤ 1 - a := by linarith
  calc
    Real.sqrt (Xc * (Yc - B)) + Real.sqrt ((Xc - A) * Yc)
        = Real.sqrt (Xc * Yc) * Real.sqrt (1 - b) +
          Real.sqrt (Xc * Yc) * Real.sqrt (1 - a) := by
            rw [hu', hv', Real.sqrt_mul hXY, Real.sqrt_mul hXY]
    _ = Real.sqrt (Xc * Yc) * (Real.sqrt (1 - a) + Real.sqrt (1 - b)) := by ring
    _ ≤ Real.sqrt (Xc * Yc) * (2 * Real.sqrt (1 - (a + b) / 2)) := by
      exact mul_le_mul_of_nonneg_left (sqrt_add_le_two_sqrt ha0 ha1 hb0 hb1)
        (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (Xc * Yc * (1 - t)) := by
      rw [ht', Real.sqrt_mul hXY]
      ring

theorem max_div_ge {x y u v N : ℝ} (hx:0≤x) (hy:0≤y) (hu:0≤u) (hv:0≤v)
    (hu0 : u = 0 → x = 0) (hv0 : v = 0 → y = 0) (hN : 0 < N) (hsplit : N ≤ x + y) :
    N^2/(Real.sqrt u + Real.sqrt v)^2 ≤ max (x^2/u) (y^2/v) := by
  by_cases hu' : u = 0
  · subst hu'
    have hx0 : x = 0 := hu0 rfl
    subst hx0
    have hvpos : 0 < v := by
      rcases lt_or_eq_of_le hv with hvpos | hvzero
      · exact hvpos
      · exfalso
        have hy0 : y = 0 := hv0 hvzero.symm
        subst hvzero; subst hy0
        simp at hsplit
        linarith
    have hR : max ((0:ℝ)^2/0) (y^2/v) = y^2/v := by
      rw [max_eq_right (show (0:ℝ)^2/0 ≤ y^2/v by simp; positivity)]
    rw [hR, Real.sqrt_zero, zero_add, Real.sq_sqrt hvpos.le]
    have hNle : N ≤ y := by simpa using hsplit
    have hNsq : N^2 ≤ y^2 := by nlinarith
    exact div_le_div_of_nonneg_right hNsq hvpos.le
  · by_cases hv' : v = 0
    · subst hv'
      have hy0 : y = 0 := hv0 rfl
      subst hy0
      have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu')
      have hR : max (x^2/u) ((0:ℝ)^2/0) = x^2/u := by
        rw [max_eq_left (show (0:ℝ)^2/0 ≤ x^2/u by simp; positivity)]
      rw [hR, Real.sqrt_zero, add_zero, Real.sq_sqrt hupos.le]
      have hNle : N ≤ x := by simpa using hsplit
      have hNsq : N^2 ≤ x^2 := by nlinarith
      exact div_le_div_of_nonneg_right hNsq hupos.le
    · have hupos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu')
      have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv')
      set p := x / Real.sqrt u
      set q := y / Real.sqrt v
      have hp0 : 0 ≤ p := by positivity
      have hq0 : 0 ≤ q := by positivity
      have hxu : p^2 = x^2/u := by
        rw [show p = x / Real.sqrt u from rfl, div_pow, Real.sq_sqrt hupos.le]
      have hyv : q^2 = y^2/v := by
        rw [show q = y / Real.sqrt v from rfl, div_pow, Real.sq_sqrt hvpos.le]
      have hmax : max (x^2/u) (y^2/v) = max (p^2) (q^2) := by rw [← hxu, ← hyv]
      have hxy : x + y ≤ max p q * (Real.sqrt u + Real.sqrt v) := by
        have hsu : (Real.sqrt u) ≠ 0 := (Real.sqrt_pos.mpr hupos).ne'
        have hsv : (Real.sqrt v) ≠ 0 := (Real.sqrt_pos.mpr hvpos).ne'
        have hx' : x = p * Real.sqrt u := by
          rw [show p = x / Real.sqrt u from rfl, div_mul_cancel₀ _ hsu]
        have hy' : y = q * Real.sqrt v := by
          rw [show q = y / Real.sqrt v from rfl, div_mul_cancel₀ _ hsv]
        calc
          x + y = p * Real.sqrt u + q * Real.sqrt v := by rw [hx', hy']
          _ ≤ max p q * Real.sqrt u + max p q * Real.sqrt v :=
            add_le_add (mul_le_mul_of_nonneg_right (le_max_left p q) (Real.sqrt_nonneg u))
              (mul_le_mul_of_nonneg_right (le_max_right p q) (Real.sqrt_nonneg v))
          _ = max p q * (Real.sqrt u + Real.sqrt v) := by ring
      have hdenpos : 0 < Real.sqrt u + Real.sqrt v := by positivity
      have hquot : N / (Real.sqrt u + Real.sqrt v) ≤ max p q :=
        (div_le_iff₀ hdenpos).mpr (by simpa [mul_comm] using le_trans hsplit hxy)
      have hqnon : 0 ≤ max p q := le_trans hp0 (le_max_left p q)
      have hsq : (N / (Real.sqrt u + Real.sqrt v))^2 ≤ (max p q)^2 :=
        pow_le_pow_left₀ (by positivity) hquot 2
      have hmaxsq : max (p^2) (q^2) = (max p q)^2 := by
        rcases le_total p q with hpq | hqp
        · rw [max_eq_right hpq, max_eq_right (pow_le_pow_left₀ hp0 hpq 2)]
        · rw [max_eq_left hqp, max_eq_left (pow_le_pow_left₀ hq0 hqp 2)]
      rw [hmax]
      calc
        N^2/(Real.sqrt u + Real.sqrt v)^2 = (N/(Real.sqrt u + Real.sqrt v))^2 := by rw [div_pow]
        _ ≤ (max p q)^2 := hsq
        _ = max (p^2) (q^2) := hmaxsq.symm


theorem case1_holder {Xc Yc E E1 χ t : ℝ} (hXc : 0 < Xc) (hYc : 0 < Yc)
    (hE : 0 < E) (hE1 : 0 ≤ E1) (hE1E : E1 ≤ E)
    (ht0 : (13 : ℝ) / 16 ≤ t) (ht1 : t < 1)
    (hχ1 : (1 : ℝ) / 2 < χ) (hχ2 : χ ≤ 2 / 3) :
    (E ^ 2 / (Xc * Yc)) ^ χ ≤
      (E1 ^ 2 / (t ^ 2 * (Xc * Yc))) ^ χ +
        ((E - E1) ^ 2 / (4 * (1 - t) * (Xc * Yc))) ^ χ := by
  have hχ0 : 0 < χ := by linarith
  have htpos : 0 < t := by linarith
  have htle : t ≤ 1 := le_of_lt ht1
  have h1t : 0 < 1 - t := by linarith
  have hXcYc : 0 < Xc * Yc := mul_pos hXc hYc
  set s : ℝ := E ^ 2 / (Xc * Yc) with hs
  have hs0 : 0 ≤ s := by positivity
  set e1 : ℝ := E1 / E with he1
  have he10 : 0 ≤ e1 := by positivity
  have he11 : e1 ≤ 1 := by
    dsimp [e1]
    exact (div_le_one hE).mpr hE1E
  set x1 : ℝ := e1 / t with hx1
  set x2 : ℝ := (1 - e1) / (2 * Real.sqrt (1 - t)) with hx2
  have hx10 : 0 ≤ x1 := by positivity
  have hx20 : 0 ≤ x2 := by positivity
  have hAterm : E1 ^ 2 / (t ^ 2 * (Xc * Yc)) = x1 ^ 2 * s := by
    dsimp [x1, e1, s]
    field_simp
  have hBterm : (E - E1) ^ 2 / (4 * (1 - t) * (Xc * Yc)) = x2 ^ 2 * s := by
    dsimp [x2, e1, s]
    field_simp
    rw [Real.sq_sqrt h1t.le]
    ring
  have hqpos : 0 < 2 * χ / (2 * χ - 1) := by
    apply div_pos (by linarith)
    linarith
  have hpq : (2 * χ).HolderConjugate (2 * χ / (2 * χ - 1)) := by
    rw [Real.holderConjugate_iff]
    constructor
    · linarith
    · field_simp
      ring
  have hsum : x1 * t + x2 * (2 * Real.sqrt (1 - t)) = 1 := by
    dsimp [x1, x2]
    field_simp [htpos.ne']
    ring
  have hBpos : 0 < t ^ (2 * χ / (2 * χ - 1)) +
      (2 * Real.sqrt (1 - t)) ^ (2 * χ / (2 * χ - 1)) := by
    have h1 : 0 < t ^ (2 * χ / (2 * χ - 1)) := Real.rpow_pos_of_pos htpos _
    have h2 : 0 ≤ (2 * Real.sqrt (1 - t)) ^ (2 * χ / (2 * χ - 1)) := by positivity
    linarith
  have hBle : t ^ (2 * χ / (2 * χ - 1)) +
      (2 * Real.sqrt (1 - t)) ^ (2 * χ / (2 * χ - 1)) ≤ 1 :=
    g_le_one_sqrt hχ1 hχ2 ht0 htle
  have hholder := holder_two_sum_one hpq hx10 hx20 htpos.le
    (by positivity : (0:ℝ) ≤ 2 * Real.sqrt (1 - t)) hsum hBpos
  have hBpowle : (t ^ (2 * χ / (2 * χ - 1)) +
      (2 * Real.sqrt (1 - t)) ^ (2 * χ / (2 * χ - 1))) ^
        ((2 * χ) / (2 * χ / (2 * χ - 1))) ≤ 1 :=
    Real.rpow_le_one (le_of_lt hBpos) hBle (le_of_lt (div_pos (by linarith) hqpos))
  have hone : (1 : ℝ) ≤ x1 ^ (2 * χ) + x2 ^ (2 * χ) := by
    have hdiv : (1 : ℝ) / (t ^ (2 * χ / (2 * χ - 1)) +
        (2 * Real.sqrt (1 - t)) ^ (2 * χ / (2 * χ - 1))) ^
          ((2 * χ) / (2 * χ / (2 * χ - 1))) ≤ x1 ^ (2 * χ) + x2 ^ (2 * χ) := by
      simpa using hholder
    have hBpowpos : 0 < (t ^ (2 * χ / (2 * χ - 1)) +
        (2 * Real.sqrt (1 - t)) ^ (2 * χ / (2 * χ - 1))) ^
          ((2 * χ) / (2 * χ / (2 * χ - 1))) :=
      Real.rpow_pos_of_pos hBpos _
    have h1le : (1 : ℝ) ≤ 1 / (t ^ (2 * χ / (2 * χ - 1)) +
        (2 * Real.sqrt (1 - t)) ^ (2 * χ / (2 * χ - 1))) ^
          ((2 * χ) / (2 * χ / (2 * χ - 1))) :=
      (one_le_div hBpowpos).mpr hBpowle
    exact le_trans h1le hdiv
  have hpowA : (x1 ^ 2 * s) ^ χ = x1 ^ (2 * χ) * s ^ χ := by
    rw [Real.mul_rpow (by positivity) hs0, ← Real.rpow_natCast x1 2,
      ← Real.rpow_mul hx10]
    congr 2
  have hpowB : (x2 ^ 2 * s) ^ χ = x2 ^ (2 * χ) * s ^ χ := by
    rw [Real.mul_rpow (by positivity) hs0, ← Real.rpow_natCast x2 2,
      ← Real.rpow_mul hx20]
    congr 2
  rw [hAterm, hBterm, hpowA, hpowB]
  calc
    s ^ χ = 1 * s ^ χ := by ring
    _ ≤ (x1 ^ (2 * χ) + x2 ^ (2 * χ)) * s ^ χ :=
      mul_le_mul_of_nonneg_right hone (Real.rpow_nonneg hs0 _)
    _ = x1 ^ (2 * χ) * s ^ χ + x2 ^ (2 * χ) * s ^ χ := by ring

theorem sqrt_sum_pos {Xc Yc A B t : ℝ} (hXc : 0 < Xc) (hYc : 0 < Yc)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hAle : A ≤ Xc) (hBle : B ≤ Yc)
    (ht : t = (A / Xc + B / Yc) / 2) (ht1 : t < 1) :
    0 < Real.sqrt (Xc * (Yc - B)) + Real.sqrt ((Xc - A) * Yc) := by
  have hu0 : 0 ≤ Xc * (Yc - B) := by nlinarith
  have hv0 : 0 ≤ (Xc - A) * Yc := by nlinarith
  by_contra h
  push Not at h
  have hsum0 : Real.sqrt (Xc * (Yc - B)) + Real.sqrt ((Xc - A) * Yc) = 0 :=
    le_antisymm h (by positivity)
  have hu : Xc * (Yc - B) = 0 := by
    nlinarith [Real.sq_sqrt hu0, Real.sq_sqrt hv0, Real.sqrt_nonneg (Xc * (Yc - B)),
      Real.sqrt_nonneg ((Xc - A) * Yc)]
  have hv : (Xc - A) * Yc = 0 := by
    nlinarith [Real.sq_sqrt hu0, Real.sq_sqrt hv0, Real.sqrt_nonneg (Xc * (Yc - B)),
      Real.sqrt_nonneg ((Xc - A) * Yc)]
  have hB_eq : B = Yc := by
    have : Yc - B = 0 := by nlinarith [hXc]
    linarith
  have hA_eq : A = Xc := by
    have : Xc - A = 0 := by nlinarith [hYc]
    linarith
  have ht_eq : t = 1 := by
    rw [ht, hA_eq, hB_eq]
    field_simp [hXc.ne', hYc.ne']
    ring
  linarith

theorem case1_core {Xc Yc A B E E1 E2 E3 χ t : ℝ}
    (hXc : 0 < Xc) (hYc : 0 < Yc) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hAle : A ≤ Xc) (hBle : B ≤ Yc)
    (hE : 0 < E) (hE1 : 0 ≤ E1) (hE1E : E1 ≤ E)
    (hE2 : 0 ≤ E2) (hE3 : 0 ≤ E3) (hsplit : E - E1 ≤ E2 + E3)
    (hE2zero : Yc - B = 0 → E2 = 0) (hE3zero : Xc - A = 0 → E3 = 0)
    (ht : t = (A / Xc + B / Yc) / 2) (ht0 : (13 : ℝ) / 16 ≤ t) (ht1 : t < 1)
    (hχ1 : (1 : ℝ) / 2 < χ) (hχ2 : χ ≤ 2 / 3) (hN : 0 < E - E1) :
    (E ^ 2 / (Xc * Yc)) ^ χ ≤
      (E1 ^ 2 / (A * B)) ^ χ +
        max ((E2 ^ 2 / (Xc * (Yc - B))) ^ χ) ((E3 ^ 2 / ((Xc - A) * Yc)) ^ χ) := by
  have hχ0 : 0 < χ := by linarith
  have hb1 : B / Yc ≤ 1 := (div_le_one hYc).mpr hBle
  have ha1 : A / Xc ≤ 1 := (div_le_one hXc).mpr hAle
  have hApos : 0 < A := by
    rcases lt_or_eq_of_le hA with h | h
    · exact h
    · exfalso
      have hA0 : A = 0 := by linarith
      have htle : t ≤ 1 / 2 := by
        rw [hA0] at ht
        rw [ht]
        simp only [zero_div, zero_add]
        linarith
      linarith
  have hBpos : 0 < B := by
    rcases lt_or_eq_of_le hB with h | h
    · exact h
    · exfalso
      have hB0 : B = 0 := by linarith
      have htle : t ≤ 1 / 2 := by
        rw [hB0] at ht
        rw [ht]
        simp only [zero_div, add_zero]
        linarith
      linarith
  have hABle : A * B ≤ t ^ 2 * (Xc * Yc) := by
    have hAM : (A / Xc) * (B / Yc) ≤ ((A / Xc + B / Yc) / 2) ^ 2 := by
      nlinarith [sq_nonneg (A / Xc - B / Yc)]
    have hXY : 0 < Xc * Yc := mul_pos hXc hYc
    have heq : (A / Xc) * (B / Yc) * (Xc * Yc) = A * B := by field_simp
    calc
      A * B = (A / Xc) * (B / Yc) * (Xc * Yc) := heq.symm
      _ ≤ ((A / Xc + B / Yc) / 2) ^ 2 * (Xc * Yc) :=
        mul_le_mul_of_nonneg_right hAM hXY.le
      _ = t ^ 2 * (Xc * Yc) := by rw [ht]
  have hL1 : E1 ^ 2 / (t ^ 2 * (Xc * Yc)) ≤ E1 ^ 2 / (A * B) := by
    exact div_le_div₀ (by positivity) le_rfl (mul_pos hApos hBpos) hABle
  set u : ℝ := Xc * (Yc - B) with hu
  set v : ℝ := (Xc - A) * Yc with hv
  set N : ℝ := E - E1 with hNdef
  have hu0 : 0 ≤ u := by rw [hu]; nlinarith
  have hv0 : 0 ≤ v := by rw [hv]; nlinarith
  have huzero : u = 0 → E2 = 0 := by
    intro h
    apply hE2zero
    rw [hu] at h
    nlinarith [hXc]
  have hvzero : v = 0 → E3 = 0 := by
    intro h
    apply hE3zero
    rw [hv] at h
    nlinarith [hYc]
  have hsplit' : N ≤ E2 + E3 := by dsimp [N]; exact hsplit
  have hmax1 : N ^ 2 / (Real.sqrt u + Real.sqrt v) ^ 2 ≤
      max (E2 ^ 2 / u) (E3 ^ 2 / v) :=
    max_div_ge hE2 hE3 hu0 hv0 huzero hvzero (by dsimp [N]; exact hN) hsplit'
  have hsqrt := sqrt_bound hXc hYc hA hB hAle hBle ht (le_of_lt ht1)
  have hD2pos : 0 < (2 * Real.sqrt (Xc * Yc * (1 - t))) ^ 2 := by
    have h1t : 0 < 1 - t := by linarith
    have hpos : 0 < Xc * Yc * (1 - t) := by positivity
    have := Real.sqrt_pos.mpr hpos
    positivity
  have hD1pos : 0 < (Real.sqrt u + Real.sqrt v) ^ 2 := by
    have := sqrt_sum_pos hXc hYc hA hB hAle hBle ht ht1
    positivity
  have hD1le : (Real.sqrt u + Real.sqrt v) ^ 2 ≤
      (2 * Real.sqrt (Xc * Yc * (1 - t))) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hsqrt 2
  have hD2eq : (2 * Real.sqrt (Xc * Yc * (1 - t))) ^ 2 = 4 * (Xc * Yc * (1 - t)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hmax2 : N ^ 2 / (4 * (Xc * Yc * (1 - t))) ≤
      N ^ 2 / (Real.sqrt u + Real.sqrt v) ^ 2 := by
    rw [← hD2eq]
    exact div_le_div₀ (by positivity) le_rfl hD1pos hD1le
  have hmax : N ^ 2 / (4 * (Xc * Yc * (1 - t))) ≤ max (E2 ^ 2 / u) (E3 ^ 2 / v) :=
    le_trans hmax2 hmax1
  set Aterm : ℝ := E1 ^ 2 / (t ^ 2 * (Xc * Yc)) with hAterm
  set Bterm : ℝ := N ^ 2 / (4 * (Xc * Yc * (1 - t))) with hBterm
  have hAterm0 : 0 ≤ Aterm := by rw [hAterm]; positivity
  have hBterm0 : 0 ≤ Bterm := by rw [hBterm]; positivity
  have hL1pow : Aterm ^ χ ≤ (E1 ^ 2 / (A * B)) ^ χ :=
    Real.rpow_le_rpow hAterm0 hL1 hχ0.le
  have hmaxpow : Bterm ^ χ ≤ max ((E2 ^ 2 / u) ^ χ) ((E3 ^ 2 / v) ^ χ) := by
    have h1 : Bterm ^ χ ≤ (max (E2 ^ 2 / u) (E3 ^ 2 / v)) ^ χ :=
      Real.rpow_le_rpow hBterm0 hmax hχ0.le
    have hmaxrpow : (max (E2 ^ 2 / u) (E3 ^ 2 / v)) ^ χ =
        max ((E2 ^ 2 / u) ^ χ) ((E3 ^ 2 / v) ^ χ) := by
      rcases le_total (E2 ^ 2 / u) (E3 ^ 2 / v) with hle | hle
      · rw [max_eq_right hle, max_eq_right (Real.rpow_le_rpow (by positivity) hle hχ0.le)]
      · rw [max_eq_left hle, max_eq_left (Real.rpow_le_rpow (by positivity) hle hχ0.le)]
    rwa [hmaxrpow] at h1
  have hholder := case1_holder hXc hYc hE hE1 hE1E ht0 ht1 hχ1 hχ2
  have hholder' : (E ^ 2 / (Xc * Yc)) ^ χ ≤ Aterm ^ χ + Bterm ^ χ := by
    simpa [Aterm, Bterm, N, mul_assoc, mul_comm, mul_left_comm] using hholder
  calc
    (E ^ 2 / (Xc * Yc)) ^ χ ≤ Aterm ^ χ + Bterm ^ χ := hholder'
    _ ≤ (E1 ^ 2 / (A * B)) ^ χ + max ((E2 ^ 2 / u) ^ χ) ((E3 ^ 2 / v) ^ χ) :=
      add_le_add hL1pow hmaxpow
    _ = (E1 ^ 2 / (A * B)) ^ χ +
        max ((E2 ^ 2 / (Xc * (Yc - B))) ^ χ) ((E3 ^ 2 / ((Xc - A) * Yc)) ^ χ) := by
      rw [hu, hv]


theorem sum_rpow_ge_div {m:ℕ} (hm:0<m) (e:Fin m→ℝ) (he0:∀i,0≤e i) {p:ℝ} (hp:1≤p) :
    (∑ i, e i)^p / (m:ℝ)^(p-1) ≤ ∑ i, e i^p := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := Finset.univ) (f := e) hp
    (fun i _ => he0 i)
  have hcard : ((Finset.univ : Finset (Fin m)).card : ℝ) = (m:ℝ) := by simp
  rw [hcard] at h
  have hmpos : (0:ℝ) < (m:ℝ)^(p-1) := by positivity
  exact (div_le_iff₀ hmpos).mpr (by simpa [mul_comm] using h)

theorem case2_factor {m:ℕ} (hm:2≤m) {χ:ℝ} (hχ:χ=1/2+1/(10*Real.log m)) :
    (1:ℝ) ≤ (16/13:ℝ)^(2*χ) * (m:ℝ)^(1-2*χ) := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
  have hlogpos : 0 < Real.log (m:ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < m)
  have h2χ : 1 ≤ 2*χ := by
    rw [hχ]
    have hpos : 0 < 1 / (10*Real.log (m:ℝ)) := by positivity
    linarith
  have hbase : (1:ℝ) ≤ 16/13 := by norm_num
  have h16 : (16/13:ℝ) ≤ (16/13:ℝ)^(2*χ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hbase h2χ
  have hmexp : (m:ℝ)^(1-2*χ) = Real.exp (-1/5) := by
    rw [Real.rpow_def_of_pos hm0]
    congr 1
    rw [hχ]
    have hlog : Real.log (m:ℝ) ≠ 0 := by
      apply Real.log_ne_zero_of_pos_of_ne_one hm0
      intro h
      have hm1 : m = 1 := by exact_mod_cast h
      omega
    field_simp
    ring
  rw [hmexp]
  have hexp : (13:ℝ)/16 ≤ Real.exp (-1/5) := by
    have h := Real.exp_bound (x := (-1/5:ℝ)) (by norm_num) (n := 4) (by norm_num)
    rw [abs_le] at h
    have hpoly : (∑ k ∈ Finset.range 4, (-1/5:ℝ)^k / k.factorial) - (1/12000:ℝ) ≤ Real.exp (-1/5) := by
      have hh := h.1
      have herr : |(-1/5:ℝ)|^4 * ((4:ℕ).succ / ((4:ℕ).factorial * (4:ℕ))) = 1/12000 := by norm_num
      linarith
    have hp : (∑ k ∈ Finset.range 4, (-1/5:ℝ)^k / k.factorial) = 1 - 1/5 + 1/50 - 1/750 := by
      norm_num [Finset.sum_range_succ]
    rw [hp] at hpoly
    linarith
  nlinarith

theorem case2_core {m:ℕ} (hm:2≤m) {χ s : ℝ} (hχ : χ = 1/2 + 1/(10*Real.log m))
    (hs : 0 ≤ s) (e : Fin m → ℝ) (he0 : ∀ i, 0 ≤ e i) (he1 : 1 ≤ ∑ i, e i)
    (g : Fin m → ℝ) (hg : ∀ i, (16/13:ℝ)^(2*χ) * (e i)^(2*χ) * s^χ ≤ g i) :
    s^χ ≤ ∑ i, g i := by
  have hm0nat : 0 < m := lt_of_lt_of_le (by norm_num) hm
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm0nat
  have hlogpos : 0 < Real.log (m:ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < m)
  have hχpos : 0 < χ := by
    rw [hχ]
    have hpos : 0 < 1 / (10*Real.log (m:ℝ)) := by positivity
    linarith
  have h2χpos : 0 < 2*χ := by linarith
  have hp : 1 ≤ 2*χ := by
    rw [hχ]
    have hpos : 0 < 1 / (10*Real.log (m:ℝ)) := by positivity
    linarith
  have hsum := sum_rpow_ge_div hm0nat e he0 hp
  have hsum1 : (1:ℝ) ≤ (∑ i, e i)^(2*χ) :=
    Real.one_le_rpow he1 h2χpos.le
  have hmdenpos : (0:ℝ) < (m:ℝ)^(2*χ-1) := by positivity
  have hgeom : (1:ℝ) / (m:ℝ)^(2*χ-1) ≤ ∑ i, e i^(2*χ) := by
    calc
      (1:ℝ) / (m:ℝ)^(2*χ-1) = (1:ℝ)^(2*χ) / (m:ℝ)^(2*χ-1) := by rw [Real.one_rpow]
      _ ≤ (∑ i, e i)^(2*χ) / (m:ℝ)^(2*χ-1) :=
        div_le_div_of_nonneg_right (by simpa [Real.one_rpow] using hsum1) hmdenpos.le
      _ ≤ ∑ i, e i^(2*χ) := hsum
  have hinv : (1:ℝ) / (m:ℝ)^(2*χ-1) = (m:ℝ)^(1-2*χ) := by
    calc
      (1:ℝ) / (m:ℝ)^(2*χ-1) = ((m:ℝ)^(2*χ-1))⁻¹ := by rw [one_div]
      _ = (m:ℝ)^(-(2*χ-1)) := (Real.rpow_neg (le_of_lt hm0) _).symm
      _ = (m:ℝ)^(1-2*χ) := by congr 1; ring
  have hsum_e : (m:ℝ)^(1-2*χ) ≤ ∑ i, e i^(2*χ) := by simpa [hinv] using hgeom
  have hfac : (1:ℝ) ≤ (16/13:ℝ)^(2*χ) * (m:ℝ)^(1-2*χ) :=
    case2_factor hm hχ
  have hsχ0 : 0 ≤ s^χ := Real.rpow_nonneg hs _
  have hmul1 : s^χ ≤ (16/13:ℝ)^(2*χ) * (m:ℝ)^(1-2*χ) * s^χ := by
    calc
      s^χ = 1 * s^χ := by ring
      _ ≤ ((16/13:ℝ)^(2*χ) * (m:ℝ)^(1-2*χ)) * s^χ :=
        mul_le_mul_of_nonneg_right hfac hsχ0
  have hmul2 : (16/13:ℝ)^(2*χ) * (m:ℝ)^(1-2*χ) * s^χ ≤
      (16/13:ℝ)^(2*χ) * (∑ i, e i^(2*χ)) * s^χ := by
    have hc0 : 0 ≤ (16/13:ℝ)^(2*χ) * s^χ := by positivity
    calc
      (16/13:ℝ)^(2*χ) * (m:ℝ)^(1-2*χ) * s^χ =
          ((m:ℝ)^(1-2*χ)) * ((16/13:ℝ)^(2*χ) * s^χ) := by ring
      _ ≤ (∑ i, e i^(2*χ)) * ((16/13:ℝ)^(2*χ) * s^χ) :=
        mul_le_mul_of_nonneg_right hsum_e hc0
      _ = (16/13:ℝ)^(2*χ) * (∑ i, e i^(2*χ)) * s^χ := by ring
  have hsumhg : (16/13:ℝ)^(2*χ) * (∑ i, e i^(2*χ)) * s^χ ≤ ∑ i, g i := by
    have hcongr : (16/13:ℝ)^(2*χ) * (∑ i, e i^(2*χ)) * s^χ =
        ∑ i, (16/13:ℝ)^(2*χ) * (e i)^(2*χ) * s^χ := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [hcongr]
    exact Finset.sum_le_sum fun i _ => hg i
  exact le_trans hmul1 (le_trans hmul2 hsumhg)


theorem edgeCount_le_sum_of_cover {G : BipartiteGraph A B} {m : ℕ}
    {Gs : Fin m → BipartiteGraph A B} (hcover : IsCover G Gs)
    (X : Finset A) (Y : Finset B) :
    G.edgeCount X Y ≤ ∑ i, (Gs i).edgeCount X Y := by
  classical
  let t : Fin m → Finset (A × B) := fun i => (X.product Y).filter fun q => (Gs i).edge q.1 q.2
  have hsub : (X.product Y).filter (fun q => G.edge q.1 q.2) ⊆ Finset.univ.biUnion t := by
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hqX, hqE⟩ := hq
    obtain ⟨i, hi⟩ := hcover.2.2.2 q.1 q.2 hqE
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, by rw [Finset.mem_filter]; exact ⟨hqX, hi⟩⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin m))) (t := t)
  have := le_trans h1 h2
  simpa [t, BipartiteGraph.edgeCount] using this

theorem sGraph_ge_ratio_cards {H : BipartiteGraph A B} (X : Finset A) (Y : Finset B)
    (hX : ∀ a ∈ X, a ∈ H.left) (hY : ∀ b ∈ Y, b ∈ H.right) :
    (H.edgeCount X Y : ℝ) ^ 2 / ((X.card : ℝ) * (Y.card : ℝ)) ≤ H.sGraph :=
  sGraph_ge_full H X Y ⟨hX, hY⟩

theorem edgeCount_eq_parts {H : BipartiteGraph A B} (X : Finset A) (Y : Finset B)
    (h : ∀ a b, H.edge a b = true → a ∈ H.left ∧ b ∈ H.right) :
    H.edgeCount (partLeft X H.left) (partRight Y H.right) = H.edgeCount X Y := by
  classical
  apply le_antisymm
  · unfold BipartiteGraph.edgeCount
    apply Finset.card_le_card
    rintro ⟨a, b⟩ hq
    simp only [Finset.mem_filter] at hq ⊢
    obtain ⟨hqP, hqE⟩ := hq
    have hp : (a, b) ∈ X ×ˢ Y := by
      have := hqP
      rw [show (partLeft X H.left).product (partRight Y H.right) = partLeft X H.left ×ˢ partRight Y H.right from rfl] at this
      rw [Finset.mem_product] at this
      have ha : a ∈ X := (mem_partLeft.mp this.1).1
      have hb : b ∈ Y := (mem_partRight.mp this.2).1
      rw [Finset.mem_product]
      exact ⟨ha, hb⟩
    refine ⟨?_, hqE⟩
    change (a, b) ∈ X.product Y
    simpa [Finset.product] using hp
  · unfold BipartiteGraph.edgeCount
    apply Finset.card_le_card
    rintro ⟨a, b⟩ hq
    simp only [Finset.mem_filter] at hq ⊢
    obtain ⟨hqP, hqE⟩ := hq
    have hp : (a, b) ∈ X ×ˢ Y := hqP
    rw [Finset.mem_product] at hp
    obtain ⟨ha, hb⟩ := hp
    obtain ⟨haL, hbR⟩ := h a b hqE
    have ha' : a ∈ partLeft X H.left := mem_partLeft.mpr ⟨ha, haL⟩
    have hb' : b ∈ partRight Y H.right := mem_partRight.mpr ⟨hb, hbR⟩
    refine ⟨?_, hqE⟩
    change (a, b) ∈ partLeft X H.left ×ˢ partRight Y H.right
    rw [Finset.mem_product]
    exact ⟨ha', hb'⟩

theorem case2_point_lower {Xc Yc A B Ei E s χ : ℝ}
    (hXc : 0 < Xc) (hYc : 0 < Yc) (hA : 0 < A) (hB : 0 < B)
    (hE : 0 < E) (hEi : 0 ≤ Ei) (hs : s = E ^ 2 / (Xc * Yc))
    (hprod : A * B ≤ (13 / 16 : ℝ) ^ 2 * (Xc * Yc)) (hχ0 : 0 < χ) :
    (16 / 13 : ℝ) ^ (2 * χ) * (Ei / E) ^ (2 * χ) * s ^ χ ≤
      (Ei ^ 2 / (A * B)) ^ χ := by
  have hXY : 0 < Xc * Yc := mul_pos hXc hYc
  have hAB : 0 < A * B := mul_pos hA hB
  have hbase : (16 / 13 : ℝ) ^ 2 * (Ei / E) ^ 2 * s ≤ Ei ^ 2 / (A * B) := by
    have heq : (16 / 13 : ℝ) ^ 2 * (Ei / E) ^ 2 * s =
        ((16 / 13 : ℝ) ^ 2 * Ei ^ 2) / (Xc * Yc) := by
      rw [hs]
      field_simp
    rw [heq]
    rw [div_le_div_iff₀ hXY hAB]
    have hcoef : (16 / 13 : ℝ) ^ 2 * (13 / 16 : ℝ) ^ 2 = 1 := by norm_num
    nlinarith [mul_le_mul_of_nonneg_left hprod (sq_nonneg Ei), hcoef]
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  have hbase0 : 0 ≤ (16 / 13 : ℝ) ^ 2 * (Ei / E) ^ 2 * s := by positivity
  have hr := Real.rpow_le_rpow hbase0 hbase hχ0.le
  have hleft : ((16 / 13 : ℝ) ^ 2 * (Ei / E) ^ 2 * s) ^ χ =
      (16 / 13 : ℝ) ^ (2 * χ) * (Ei / E) ^ (2 * χ) * s ^ χ := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_natCast (16 / 13 : ℝ) 2, ← Real.rpow_natCast (Ei / E) 2,
      ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 16 / 13),
      ← Real.rpow_mul (by positivity : (0:ℝ) ≤ Ei / E)]
    ring_nf
  simpa [hleft] using hr

theorem case1_split_edges {G : BipartiteGraph A B} {m : ℕ}
    {Gs : Fin m → BipartiteGraph A B} (hcover : IsCover G Gs)
    (X : Finset A) (Y : Finset B) (j : Fin m) :
    G.edgeCount X Y ≤
      (Gs j).edgeCount (partLeft X (Gs j).left) (partRight Y (Gs j).right) +
        G.edgeCount X (Y \ partRight Y (Gs j).right) +
          G.edgeCount (X \ partLeft X (Gs j).left) Y := by
  classical
  set Aj := partLeft X (Gs j).left
  set Bj := partRight Y (Gs j).right
  let A1 : Finset (A × B) := (Aj.product Bj).filter fun q => (Gs j).edge q.1 q.2
  let A2 : Finset (A × B) := (X.product (Y \ Bj)).filter fun q => G.edge q.1 q.2
  let A3 : Finset (A × B) := ((X \ Aj).product Y).filter fun q => G.edge q.1 q.2
  have hsub : (X.product Y).filter (fun q => G.edge q.1 q.2) ⊆ A1 ∪ A2 ∪ A3 := by
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hqX, hqE⟩ := hq
    have hp : (q.1, q.2) ∈ X ×ˢ Y := hqX
    rw [Finset.mem_product] at hp
    obtain ⟨haX, hbY⟩ := hp
    by_cases hin : q.1 ∈ Aj ∧ q.2 ∈ Bj
    · have haL : q.1 ∈ (Gs j).left := (mem_partLeft.mp hin.1).2
      have hbR : q.2 ∈ (Gs j).right := (mem_partRight.mp hin.2).2
      have hgexp : (Gs j).edge q.1 q.2 = true :=
        ((hcover.2.2.1 j) q.1 q.2).mpr ⟨hqE, haL, hbR⟩
      have hmem : q ∈ A1 := by
        dsimp [A1]; rw [Finset.mem_filter]
        refine ⟨?_, hgexp⟩
        exact Finset.mem_product.mpr ⟨hin.1, hin.2⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hmem)
    · push Not at hin
      by_cases hb : q.2 ∈ Bj
      · have ha : q.1 ∉ Aj := by
          intro ha
          exact hin ha hb
        have hmem : q ∈ A3 := by
          have haX' : q.1 ∈ X \ Aj := Finset.mem_sdiff.mpr ⟨haX, ha⟩
          dsimp [A3]; rw [Finset.mem_filter]
          refine ⟨?_, hqE⟩
          exact Finset.mem_product.mpr ⟨haX', hbY⟩
        exact Finset.mem_union_right _ hmem
      · have hb' : q.2 ∈ Y \ Bj := Finset.mem_sdiff.mpr ⟨hbY, hb⟩
        have hmem : q ∈ A2 := by
          dsimp [A2]; rw [Finset.mem_filter]
          refine ⟨?_, hqE⟩
          exact Finset.mem_product.mpr ⟨haX, hb'⟩
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hmem)
  have h1 := Finset.card_le_card hsub
  have h2 : (A1 ∪ A2 ∪ A3).card ≤ A1.card + A2.card + A3.card := by
    calc
      (A1 ∪ A2 ∪ A3).card ≤ (A1 ∪ A2).card + A3.card := Finset.card_union_le _ _
      _ ≤ (A1.card + A2.card) + A3.card := by
        exact Nat.add_le_add_right (Finset.card_union_le A1 A2) _
  have hcount : G.edgeCount X Y ≤ A1.card + A2.card + A3.card := le_trans h1 h2
  simpa [A1, A2, A3, Aj, Bj, BipartiteGraph.edgeCount, add_assoc] using hcount

theorem edgeCount_le_of_subset_edges {G H : BipartiteGraph A B}
    {X' X : Finset A} {Y' Y : Finset B} (hX : X' ⊆ X) (hY : Y' ⊆ Y)
    (he : ∀ a b, H.edge a b = true → G.edge a b = true) :
    H.edgeCount X' Y' ≤ G.edgeCount X Y := by
  classical
  unfold BipartiteGraph.edgeCount
  apply Finset.card_le_card
  rintro ⟨a, b⟩ hq
  simp only [Finset.mem_filter] at hq ⊢
  obtain ⟨hqP, hqE⟩ := hq
  have hp : (a, b) ∈ X' ×ˢ Y' := hqP
  rw [Finset.mem_product] at hp
  exact ⟨Finset.mem_product.mpr ⟨hX hp.1, hY hp.2⟩, he a b hqE⟩

theorem card_sdiff_eq {α : Type*} [DecidableEq α] {s t : Finset α} (h : s ⊆ t) :
    (t \ s).card = t.card - s.card := by
  rw [Finset.card_sdiff]
  have : s ∩ t = s := Finset.inter_eq_left.mpr h
  rw [this]

theorem step_case1 {n : ℕ} (hn : 1 ≤ n) {χ : ℝ}
    (hχ : χ = 1 / 2 + 1 / (10 * Real.log ((n : ℝ) + 1)))
    (hχ1 : (1 : ℝ) / 2 < χ) (hχ2 : χ ≤ 2 / 3)
    (hprev : IsGraphExponent n χ)
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (G : BipartiteGraph A B) (Gs : Fin (n + 1) → BipartiteGraph A B)
    (hcover : IsCover G Gs) (X : Finset A) (Y : Finset B)
    (hleft : G.left = (↑X : Set A)) (hright : G.right = (↑Y : Set B))
    (hfull : G.sGraph = G.ratio X Y) (hEpos : 0 < G.edgeCount X Y)
    (j : Fin (n + 1))
    (hj : (13 : ℝ) / 8 ≤
      ((partLeft X (Gs j).left).card : ℝ) / (X.card : ℝ) +
        ((partRight Y (Gs j).right).card : ℝ) / (Y.card : ℝ))
    (hE1lt : (Gs j).edgeCount (partLeft X (Gs j).left) (partRight Y (Gs j).right) <
      G.edgeCount X Y) :
    G.sGraph ^ χ ≤ ∑ i, (Gs i).sGraph ^ χ := by
  classical
  set Aj : Finset A := partLeft X (Gs j).left with hAj
  set Bj : Finset B := partRight Y (Gs j).right with hBj
  set Yj : Finset B := Y \ Bj with hYj
  set Xj : Finset A := X \ Aj with hXj
  set E : ℕ := G.edgeCount X Y with hE
  set E1 : ℕ := (Gs j).edgeCount Aj Bj with hE1
  set E2 : ℕ := G.edgeCount X Yj with hE2
  set E3 : ℕ := G.edgeCount Xj Y with hE3
  set t : ℝ := ((Aj.card : ℝ) / (X.card : ℝ) + (Bj.card : ℝ) / (Y.card : ℝ)) / 2 with ht
  have hAdmXY : G.Admissible X Y := by
    refine ⟨?_, ?_⟩
    · intro a ha
      rw [hleft]
      exact ha
    · intro b hb
      rw [hright]
      exact hb
  have hXpos : 0 < X.card := by
    obtain ⟨q, hq⟩ := Finset.card_pos.mp hEpos
    have hq' : q ∈ (X.product Y).filter (fun q => G.edge q.1 q.2) := by
      simpa [BipartiteGraph.edgeCount] using hq
    rw [Finset.mem_filter] at hq'
    have hp : q ∈ X ×ˢ Y := hq'.1
    rw [Finset.mem_product] at hp
    exact Finset.card_pos.mpr ⟨q.1, hp.1⟩
  have hYpos : 0 < Y.card := by
    obtain ⟨q, hq⟩ := Finset.card_pos.mp hEpos
    have hq' : q ∈ (X.product Y).filter (fun q => G.edge q.1 q.2) := by
      simpa [BipartiteGraph.edgeCount] using hq
    rw [Finset.mem_filter] at hq'
    have hp : q ∈ X ×ˢ Y := hq'.1
    rw [Finset.mem_product] at hp
    exact Finset.card_pos.mpr ⟨q.2, hp.2⟩
  have hXposR : (0:ℝ) < (X.card : ℝ) := by exact_mod_cast hXpos
  have hYposR : (0:ℝ) < (Y.card : ℝ) := by exact_mod_cast hYpos
  have hsG : G.sGraph = (E : ℝ) ^ 2 / ((X.card : ℝ) * (Y.card : ℝ)) := by
    rw [hfull, ratio_of_admissible G hAdmXY]
  have hAj_sub : Aj ⊆ X := fun a ha => (mem_partLeft.mp ha).1
  have hBj_sub : Bj ⊆ Y := fun b hb => (mem_partRight.mp hb).1
  have hAle : (Aj.card : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast Finset.card_le_card hAj_sub
  have hBle : (Bj.card : ℝ) ≤ (Y.card : ℝ) := by exact_mod_cast Finset.card_le_card hBj_sub
  have hEposR : (0:ℝ) < (E : ℝ) := by exact_mod_cast hEpos
  have hE1ltR : (E1 : ℝ) < (E : ℝ) := by exact_mod_cast hE1lt
  have hsplitNat : E - E1 ≤ E2 + E3 := by
    have h := case1_split_edges hcover X Y j
    have h' : E ≤ E1 + E2 + E3 := by simpa [E, E1, E2, E3, Aj, Bj, Yj, Xj] using h
    have hE1lt' : E1 < E := by simpa [E, E1, Aj, Bj] using hE1lt
    rw [Nat.sub_le_iff_le_add]
    omega
  have hE1leE : E1 ≤ E := le_of_lt (by simpa [E, E1, Aj, Bj] using hE1lt)
  have hsplitR : (E : ℝ) - (E1 : ℝ) ≤ (E2 : ℝ) + (E3 : ℝ) := by
    rw [← Nat.cast_sub hE1leE]
    exact_mod_cast hsplitNat
  have hNpos : (0 : ℝ) < (E : ℝ) - (E1 : ℝ) := by
    have hpos : 0 < E - E1 := Nat.sub_pos_of_lt (by simpa [E, E1, Aj, Bj] using hE1lt)
    rw [← Nat.cast_sub hE1leE]
    exact_mod_cast hpos
  have htlt1 : t < 1 := by
    rw [ht]
    by_contra h
    push Not at h
    have ha1 : (Aj.card : ℝ) / (X.card : ℝ) ≤ 1 := (div_le_one hXposR).mpr hAle
    have hb1 : (Bj.card : ℝ) / (Y.card : ℝ) ≤ 1 := (div_le_one hYposR).mpr hBle
    have htle : ((Aj.card : ℝ) / (X.card : ℝ) + (Bj.card : ℝ) / (Y.card : ℝ)) / 2 ≤ 1 := by
      nlinarith
    have ht_eq : ((Aj.card : ℝ) / (X.card : ℝ) + (Bj.card : ℝ) / (Y.card : ℝ)) / 2 = 1 :=
      le_antisymm htle h
    have ha : (Aj.card : ℝ) / (X.card : ℝ) = 1 := by nlinarith
    have hb : (Bj.card : ℝ) / (Y.card : ℝ) = 1 := by nlinarith
    have hAjcard : (Aj.card : ℝ) = (X.card : ℝ) := (div_eq_one_iff_eq hXposR.ne').mp ha
    have hBjcard : (Bj.card : ℝ) = (Y.card : ℝ) := (div_eq_one_iff_eq hYposR.ne').mp hb
    have hAjeq : Aj = X := by
      apply Finset.eq_of_subset_of_card_le hAj_sub
      exact_mod_cast (by rw [hAjcard] : (X.card : ℝ) ≤ (Aj.card : ℝ))
    have hBjeq : Bj = Y := by
      apply Finset.eq_of_subset_of_card_le hBj_sub
      exact_mod_cast (by rw [hBjcard] : (Y.card : ℝ) ≤ (Bj.card : ℝ))
    have hYj0 : Yj = ∅ := by rw [hYj, hBjeq, Finset.sdiff_self]
    have hXj0 : Xj = ∅ := by rw [hXj, hAjeq, Finset.sdiff_self]
    have hE2zero : E2 = 0 := by simp [E2, BipartiteGraph.edgeCount, hYj0]
    have hE3zero : E3 = 0 := by simp [E3, BipartiteGraph.edgeCount, hXj0]
    have hle : E ≤ E1 := by
      rw [hE2zero, hE3zero, add_zero] at hsplitNat
      exact Nat.le_of_sub_eq_zero (Nat.eq_zero_of_le_zero hsplitNat)
    have hE1lt' : E1 < E := by simpa [E, E1, Aj, Bj] using hE1lt
    omega
  have hheart := case1_core (Xc := (X.card : ℝ)) (Yc := (Y.card : ℝ))
    (A := (Aj.card : ℝ)) (B := (Bj.card : ℝ)) (E := (E : ℝ)) (E1 := (E1 : ℝ))
    (E2 := (E2 : ℝ)) (E3 := (E3 : ℝ)) (χ := χ) (t := t)
    hXposR hYposR (by positivity) (by positivity) hAle hBle hEposR (by positivity)
    (by exact_mod_cast Nat.le_of_lt hE1lt)
    (by positivity) (by positivity) hsplitR
    (by
      intro h
      have : Yj.card = 0 := by
        have hEqR : (Y.card : ℝ) = (Bj.card : ℝ) := by linarith
        have hEq : Y.card = Bj.card := by exact_mod_cast hEqR
        rw [hYj, card_sdiff_eq hBj_sub, hEq, Nat.sub_self]
      simp [E2, BipartiteGraph.edgeCount, Finset.card_eq_zero.mp this])
    (by
      intro h
      have : Xj.card = 0 := by
        have hEqR : (X.card : ℝ) = (Aj.card : ℝ) := by linarith
        have hEq : X.card = Aj.card := by exact_mod_cast hEqR
        rw [hXj, card_sdiff_eq hAj_sub, hEq, Nat.sub_self]
      simp [E3, BipartiteGraph.edgeCount, Finset.card_eq_zero.mp this])
    ht (by rw [ht]; linarith) htlt1 hχ1 hχ2 hNpos
  have hχpos : 0 < χ := by linarith
  have hAjmem : ∀ a ∈ Aj, a ∈ (Gs j).left := fun a ha => (mem_partLeft.mp ha).2
  have hBjmem : ∀ b ∈ Bj, b ∈ (Gs j).right := fun b hb => (mem_partRight.mp hb).2
  have hGj_ge : (E1 : ℝ) ^ 2 / ((Aj.card : ℝ) * (Bj.card : ℝ)) ≤ (Gs j).sGraph := by
    have := sGraph_ge_ratio_cards (H := Gs j) Aj Bj hAjmem hBjmem
    simpa [E1, Aj, Bj, BipartiteGraph.edgeCount] using this
  have hGj_pow : ((E1 : ℝ) ^ 2 / ((Aj.card : ℝ) * (Bj.card : ℝ))) ^ χ ≤ (Gs j).sGraph ^ χ := by
    exact Real.rpow_le_rpow (by positivity) hGj_ge hχpos.le
  let G' : BipartiteGraph A B := graphOn G.edge X Yj
  let G'' : BipartiteGraph A B := graphOn G.edge Xj Y
  let GsR : Fin n → BipartiteGraph A B := fun i => frag (Gs (j.succAbove i)) X Yj
  let GsL : Fin n → BipartiteGraph A B := fun i => frag (Gs (j.succAbove i)) Xj Y
  have hcovR : IsCover G' GsR := by
    simpa [G', GsR, Yj, Bj] using cover_frag_erase_right hcover X Y j
  have hcovL : IsCover G'' GsL := by
    simpa [G'', GsL, Xj, Aj] using cover_frag_erase_left hcover X Y j
  have hR0 : G'.sGraph ^ χ ≤ ∑ i : Fin n, (GsR i).sGraph ^ χ :=
    hprev n le_rfl A B G' GsR hcovR
  have hL0 : G''.sGraph ^ χ ≤ ∑ i : Fin n, (GsL i).sGraph ^ χ :=
    hprev n le_rfl A B G'' GsL hcovL
  have hR : G'.sGraph ^ χ ≤ ∑ i : Fin n, (Gs (j.succAbove i)).sGraph ^ χ := by
    refine le_trans hR0 (Finset.sum_le_sum fun i _ => ?_)
    exact Real.rpow_le_rpow (BipartiteGraph.sGraph_nonneg _)
      (sGraph_frag_le (Gs (j.succAbove i)) X Yj) hχpos.le
  have hL : G''.sGraph ^ χ ≤ ∑ i : Fin n, (Gs (j.succAbove i)).sGraph ^ χ := by
    refine le_trans hL0 (Finset.sum_le_sum fun i _ => ?_)
    exact Real.rpow_le_rpow (BipartiteGraph.sGraph_nonneg _)
      (sGraph_frag_le (Gs (j.succAbove i)) Xj Y) hχpos.le
  set rest : ℝ := ∑ i : Fin n, (Gs (j.succAbove i)).sGraph ^ χ with hrest
  have hmax_rest : max (G'.sGraph ^ χ) (G''.sGraph ^ χ) ≤ rest := max_le hR hL
  have hL2_pow : ((E2 : ℝ) ^ 2 / ((X.card : ℝ) * (Yj.card : ℝ))) ^ χ ≤ G'.sGraph ^ χ := by
    have := sGraph_ge_ratio_cards (H := G') X Yj (by intro a ha; exact ha) (by intro b hb; exact hb)
    have hcount : G'.edgeCount X Yj = E2 := by
      dsimp [G', E2]
      exact edgeCount_graphOn_self' G X Yj
    rw [hcount] at this
    exact Real.rpow_le_rpow (by positivity) this hχpos.le
  have hL3_pow : ((E3 : ℝ) ^ 2 / ((Xj.card : ℝ) * (Y.card : ℝ))) ^ χ ≤ G''.sGraph ^ χ := by
    have := sGraph_ge_ratio_cards (H := G'') Xj Y (by intro a ha; exact ha) (by intro b hb; exact hb)
    have hcount : G''.edgeCount Xj Y = E3 := by
      dsimp [G'', E3]
      exact edgeCount_graphOn_self' G Xj Y
    rw [hcount] at this
    exact Real.rpow_le_rpow (by positivity) this hχpos.le
  have hmax_pow : max (((E2 : ℝ) ^ 2 / ((X.card : ℝ) * (Yj.card : ℝ))) ^ χ)
      (((E3 : ℝ) ^ 2 / ((Xj.card : ℝ) * (Y.card : ℝ))) ^ χ) ≤
      max (G'.sGraph ^ χ) (G''.sGraph ^ χ) := max_le_max hL2_pow hL3_pow
  have hYjcard : (Yj.card : ℝ) = (Y.card : ℝ) - (Bj.card : ℝ) := by
    rw [hYj, card_sdiff_eq hBj_sub]
    exact Nat.cast_sub (Finset.card_le_card hBj_sub)
  have hXjcard : (Xj.card : ℝ) = (X.card : ℝ) - (Aj.card : ℝ) := by
    rw [hXj, card_sdiff_eq hAj_sub]
    exact Nat.cast_sub (Finset.card_le_card hAj_sub)
  have hmax_pow' : max (((E2 : ℝ) ^ 2 / ((X.card : ℝ) * ((Y.card : ℝ) - (Bj.card : ℝ)))) ^ χ)
      (((E3 : ℝ) ^ 2 / (((X.card : ℝ) - (Aj.card : ℝ)) * (Y.card : ℝ))) ^ χ) ≤
      max (G'.sGraph ^ χ) (G''.sGraph ^ χ) := by
    simpa [hYjcard, hXjcard] using hmax_pow
  have hstep : G.sGraph ^ χ ≤ (Gs j).sGraph ^ χ + max (G'.sGraph ^ χ) (G''.sGraph ^ χ) := by
    rw [hsG]
    exact le_trans hheart (add_le_add hGj_pow hmax_pow')
  have hsum : ∑ i : Fin (n + 1), (Gs i).sGraph ^ χ =
      (Gs j).sGraph ^ χ + rest := by
    rw [Fin.sum_univ_succAbove]
  calc
    G.sGraph ^ χ ≤ (Gs j).sGraph ^ χ + max (G'.sGraph ^ χ) (G''.sGraph ^ χ) := hstep
    _ ≤ (Gs j).sGraph ^ χ + rest := by
      exact add_le_add le_rfl hmax_rest
    _ = ∑ i : Fin (n + 1), (Gs i).sGraph ^ χ := hsum.symm

theorem step_case2 {n : ℕ} (hn : 1 ≤ n) {χ : ℝ}
    (hχ : χ = 1 / 2 + 1 / (10 * Real.log ((n : ℝ) + 1)))
    (hχ1 : (1 : ℝ) / 2 < χ) (hχ2 : χ ≤ 2 / 3)
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (G : BipartiteGraph A B) (Gs : Fin (n + 1) → BipartiteGraph A B)
    (hcover : IsCover G Gs) (X : Finset A) (Y : Finset B)
    (hleft : G.left = (↑X : Set A)) (hright : G.right = (↑Y : Set B))
    (hfull : G.sGraph = G.ratio X Y) (hEpos : 0 < G.edgeCount X Y)
    (hcase2 : ∀ i : Fin (n + 1),
      ((partLeft X (Gs i).left).card : ℝ) / (X.card : ℝ) +
        ((partRight Y (Gs i).right).card : ℝ) / (Y.card : ℝ) < (13 : ℝ) / 8) :
    G.sGraph ^ χ ≤ ∑ i, (Gs i).sGraph ^ χ := by
  classical
  have hχpos : 0 < χ := by linarith
  have hAdmXY : G.Admissible X Y := by
    refine ⟨?_, ?_⟩
    · intro a ha; rw [hleft]; exact ha
    · intro b hb; rw [hright]; exact hb
  have hsG : G.sGraph = ((G.edgeCount X Y : ℝ)) ^ 2 /
      ((X.card : ℝ) * (Y.card : ℝ)) := by
    rw [hfull, ratio_of_admissible G hAdmXY]
  have hXpos : 0 < X.card := by
    obtain ⟨q, hq⟩ := Finset.card_pos.mp hEpos
    have hq' : q ∈ (X.product Y).filter (fun q => G.edge q.1 q.2) := by
      simpa [BipartiteGraph.edgeCount] using hq
    rw [Finset.mem_filter] at hq'
    have hp : q ∈ X ×ˢ Y := hq'.1
    rw [Finset.mem_product] at hp
    exact Finset.card_pos.mpr ⟨q.1, hp.1⟩
  have hYpos : 0 < Y.card := by
    obtain ⟨q, hq⟩ := Finset.card_pos.mp hEpos
    have hq' : q ∈ (X.product Y).filter (fun q => G.edge q.1 q.2) := by
      simpa [BipartiteGraph.edgeCount] using hq
    rw [Finset.mem_filter] at hq'
    have hp : q ∈ X ×ˢ Y := hq'.1
    rw [Finset.mem_product] at hp
    exact Finset.card_pos.mpr ⟨q.2, hp.2⟩
  have hXposR : (0:ℝ) < (X.card : ℝ) := by exact_mod_cast hXpos
  have hYposR : (0:ℝ) < (Y.card : ℝ) := by exact_mod_cast hYpos
  have hEposR : (0:ℝ) < (G.edgeCount X Y : ℝ) := by exact_mod_cast hEpos
  let Ai : Fin (n + 1) → Finset A := fun i => partLeft X (Gs i).left
  let Bi : Fin (n + 1) → Finset B := fun i => partRight Y (Gs i).right
  let Ei : Fin (n + 1) → ℕ := fun i => (Gs i).edgeCount (Ai i) (Bi i)
  have hAi_sub : ∀ i, Ai i ⊆ X := fun i a ha => (mem_partLeft.mp ha).1
  have hBi_sub : ∀ i, Bi i ⊆ Y := fun i b hb => (mem_partRight.mp hb).1
  have hEi_eq : ∀ i, (Gs i).edgeCount X Y = Ei i := by
    intro i
    have h := edgeCount_eq_parts (H := Gs i) X Y (fun a b h => (((hcover.2.2.1 i) a b).mp h).2)
    simpa [Ei, Ai, Bi] using h.symm
  have hsumE : G.edgeCount X Y ≤ ∑ i, Ei i := by
    have h := edgeCount_le_sum_of_cover hcover X Y
    simpa [hEi_eq] using h
  have hsumE' : (G.edgeCount X Y : ℝ) ≤ ∑ i, (Ei i : ℝ) := by exact_mod_cast hsumE
  have he1 : (1:ℝ) ≤ ∑ i : Fin (n + 1), (Ei i : ℝ) / (G.edgeCount X Y : ℝ) := by
    have hdiv := div_le_div_of_nonneg_right hsumE' hEposR.le
    rw [div_self hEposR.ne'] at hdiv
    simpa [Finset.sum_div] using hdiv
  have hprod_i : ∀ i, (Ai i).card * (Bi i).card ≤
      (13 / 16 : ℝ) ^ 2 * ((X.card : ℝ) * (Y.card : ℝ)) := by
    intro i
    have hlt : ((Ai i).card : ℝ) / (X.card : ℝ) + ((Bi i).card : ℝ) / (Y.card : ℝ) < (13 : ℝ) / 8 :=
      hcase2 i
    have ha1 : ((Ai i).card : ℝ) / (X.card : ℝ) ≤ 1 :=
      (div_le_one hXposR).mpr (by exact_mod_cast Finset.card_le_card (hAi_sub i))
    have hb1 : ((Bi i).card : ℝ) / (Y.card : ℝ) ≤ 1 :=
      (div_le_one hYposR).mpr (by exact_mod_cast Finset.card_le_card (hBi_sub i))
    have hAM : (((Ai i).card : ℝ) / (X.card : ℝ)) * (((Bi i).card : ℝ) / (Y.card : ℝ)) ≤
        ((((Ai i).card : ℝ) / (X.card : ℝ) + ((Bi i).card : ℝ) / (Y.card : ℝ)) / 2) ^ 2 := by
      nlinarith [sq_nonneg (((Ai i).card : ℝ) / (X.card : ℝ) - ((Bi i).card : ℝ) / (Y.card : ℝ))]
    have hsq : ((((Ai i).card : ℝ) / (X.card : ℝ) + ((Bi i).card : ℝ) / (Y.card : ℝ)) / 2) ^ 2 ≤
        (13 / 16 : ℝ) ^ 2 := by
      have hhalf : (((Ai i).card : ℝ) / (X.card : ℝ) + ((Bi i).card : ℝ) / (Y.card : ℝ)) / 2 < (13 : ℝ) / 16 := by
        linarith
      have hnon : 0 ≤ (((Ai i).card : ℝ) / (X.card : ℝ) + ((Bi i).card : ℝ) / (Y.card : ℝ)) / 2 := by positivity
      nlinarith
    have heq : (((Ai i).card : ℝ) / (X.card : ℝ)) * (((Bi i).card : ℝ) / (Y.card : ℝ)) *
        ((X.card : ℝ) * (Y.card : ℝ)) = ((Ai i).card : ℝ) * ((Bi i).card : ℝ) := by
      field_simp
    calc
      ((Ai i).card : ℝ) * ((Bi i).card : ℝ) =
          (((Ai i).card : ℝ) / (X.card : ℝ)) * (((Bi i).card : ℝ) / (Y.card : ℝ)) *
            ((X.card : ℝ) * (Y.card : ℝ)) := heq.symm
      _ ≤ ((13 / 16 : ℝ) ^ 2) * ((X.card : ℝ) * (Y.card : ℝ)) := by
        exact mul_le_mul_of_nonneg_right (le_trans hAM hsq) (by positivity)
  have hg : ∀ i, (16 / 13 : ℝ) ^ (2 * χ) * ((Ei i : ℝ) / (G.edgeCount X Y : ℝ)) ^ (2 * χ) *
      G.sGraph ^ χ ≤ (Gs i).sGraph ^ χ := by
    intro i
    have hAi0 : 0 ≤ ((Ai i).card : ℝ) := by positivity
    have hBi0 : 0 ≤ ((Bi i).card : ℝ) := by positivity
    have hprod0 : ((Ai i).card : ℝ) * ((Bi i).card : ℝ) = 0 ∨
        0 < ((Ai i).card : ℝ) * ((Bi i).card : ℝ) := by
      rcases lt_or_ge 0 (((Ai i).card : ℝ) * ((Bi i).card : ℝ)) with hpos | hnonpos
      · exact Or.inr hpos
      · have hzero : ((Ai i).card : ℝ) * ((Bi i).card : ℝ) = 0 :=
          le_antisymm hnonpos (by positivity)
        exact Or.inl hzero
    rcases hprod0 with hzero | hpos
    · have hEi_zero : Ei i = 0 := by
        rcases mul_eq_zero.mp hzero with hA | hB
        · have : Ai i = ∅ := Finset.card_eq_zero.mp (by exact_mod_cast hA)
          simp [Ei, BipartiteGraph.edgeCount, this]
        · have : Bi i = ∅ := Finset.card_eq_zero.mp (by exact_mod_cast hB)
          simp [Ei, BipartiteGraph.edgeCount, this]
      rw [hEi_zero]
      simp only [Nat.cast_zero, zero_div, Real.zero_rpow (by positivity : (2:ℝ) * χ ≠ 0), mul_zero, zero_mul]
      exact Real.rpow_nonneg (BipartiteGraph.sGraph_nonneg (Gs i)) χ
    · have hApos : 0 < ((Ai i).card : ℝ) :=
        pos_of_mul_pos_left hpos (by positivity : (0:ℝ) ≤ ((Bi i).card : ℝ))
      have hBpos : 0 < ((Bi i).card : ℝ) :=
        pos_of_mul_pos_right hpos (by positivity : (0:ℝ) ≤ ((Ai i).card : ℝ))
      have hbase := case2_point_lower (Xc := (X.card : ℝ)) (Yc := (Y.card : ℝ))
        (A := ((Ai i).card : ℝ)) (B := ((Bi i).card : ℝ)) (Ei := (Ei i : ℝ))
        (E := (G.edgeCount X Y : ℝ)) (s := G.sGraph) (χ := χ)
        hXposR hYposR hApos hBpos hEposR (by positivity) hsG (hprod_i i) hχpos
      have hsGi_ge : ((Ei i : ℝ) ^ 2 / (((Ai i).card : ℝ) * ((Bi i).card : ℝ))) ≤ (Gs i).sGraph := by
        have hmemA : ∀ a ∈ Ai i, a ∈ (Gs i).left := fun a ha => (mem_partLeft.mp ha).2
        have hmemB : ∀ b ∈ Bi i, b ∈ (Gs i).right := fun b hb => (mem_partRight.mp hb).2
        have := sGraph_ge_ratio_cards (H := Gs i) (Ai i) (Bi i) hmemA hmemB
        simpa [Ei, Ai, Bi, BipartiteGraph.edgeCount] using this
      exact le_trans hbase (Real.rpow_le_rpow (by positivity) hsGi_ge hχpos.le)
  have hχ' : χ = 1 / 2 + 1 / (10 * Real.log ((n + 1 : ℕ) : ℝ)) := by
    rw [hχ]
    norm_num [Nat.cast_add]
  have hcore := case2_core (m := n + 1) (by omega) (χ := χ) (s := G.sGraph) hχ'
    (BipartiteGraph.sGraph_nonneg G)
    (fun i => (Ei i : ℝ) / (G.edgeCount X Y : ℝ))
    (fun i => by positivity) (by simpa using he1)
    (fun i => (Gs i).sGraph ^ χ) (fun i => by simpa using hg i)
  simpa [hsG] using hcore

theorem step_normalized {n : ℕ} (hn : 1 ≤ n) {χ : ℝ}
    (hχ : χ = 1 / 2 + 1 / (10 * Real.log ((n : ℝ) + 1)))
    (hχ1 : (1 : ℝ) / 2 < χ) (hχ2 : χ ≤ 2 / 3)
    (hprev : IsGraphExponent n χ)
    {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (G : BipartiteGraph A B) (Gs : Fin (n + 1) → BipartiteGraph A B)
    (hcover : IsCover G Gs) (X : Finset A) (Y : Finset B)
    (hleft : G.left = (↑X : Set A)) (hright : G.right = (↑Y : Set B))
    (hfull : G.sGraph = G.ratio X Y) (hEpos : 0 < G.edgeCount X Y) :
    G.sGraph ^ χ ≤ ∑ i, (Gs i).sGraph ^ χ := by
  classical
  by_cases hcase1 : ∃ j : Fin (n + 1),
      (13 : ℝ) / 8 ≤ ((partLeft X (Gs j).left).card : ℝ) / (X.card : ℝ) +
        ((partRight Y (Gs j).right).card : ℝ) / (Y.card : ℝ)
  · obtain ⟨j, hj⟩ := hcase1
    set Aj : Finset A := partLeft X (Gs j).left with hAj
    set Bj : Finset B := partRight Y (Gs j).right with hBj
    have hE1le : (Gs j).edgeCount Aj Bj ≤ G.edgeCount X Y := by
      apply edgeCount_le_of_subset_edges (X := X) (Y := Y)
      · exact fun a ha => (mem_partLeft.mp ha).1
      · exact fun b hb => (mem_partRight.mp hb).1
      · intro a b h
        exact ((hcover.2.2.1 j) a b).mp h |>.1
    by_cases hE1lt : (Gs j).edgeCount Aj Bj < G.edgeCount X Y
    · refine step_case1 hn hχ hχ1 hχ2 hprev G Gs hcover X Y hleft hright hfull hEpos j ?_ ?_
      · simpa [Aj, Bj] using hj
      · simpa [Aj, Bj] using hE1lt
    · have hE1eq : (Gs j).edgeCount Aj Bj = G.edgeCount X Y := le_antisymm hE1le (le_of_not_gt hE1lt)
      have hAdmXY : G.Admissible X Y := by
        refine ⟨?_, ?_⟩
        · intro a ha; rw [hleft]; exact ha
        · intro b hb; rw [hright]; exact hb
      have hsG : G.sGraph = ((G.edgeCount X Y : ℝ)) ^ 2 /
          ((X.card : ℝ) * (Y.card : ℝ)) := by
        rw [hfull, ratio_of_admissible G hAdmXY]
      have hXpos : 0 < X.card := by
        obtain ⟨q, hq⟩ := Finset.card_pos.mp hEpos
        have hq' : q ∈ (X.product Y).filter (fun q => G.edge q.1 q.2) := by
          simpa [BipartiteGraph.edgeCount] using hq
        rw [Finset.mem_filter] at hq'
        have hp : q ∈ X ×ˢ Y := hq'.1
        rw [Finset.mem_product] at hp
        exact Finset.card_pos.mpr ⟨q.1, hp.1⟩
      have hYpos : 0 < Y.card := by
        obtain ⟨q, hq⟩ := Finset.card_pos.mp hEpos
        have hq' : q ∈ (X.product Y).filter (fun q => G.edge q.1 q.2) := by
          simpa [BipartiteGraph.edgeCount] using hq
        rw [Finset.mem_filter] at hq'
        have hp : q ∈ X ×ˢ Y := hq'.1
        rw [Finset.mem_product] at hp
        exact Finset.card_pos.mpr ⟨q.2, hp.2⟩
      have hAj_sub : Aj ⊆ X := fun a ha => (mem_partLeft.mp ha).1
      have hBj_sub : Bj ⊆ Y := fun b hb => (mem_partRight.mp hb).1
      have hAjBjpos : 0 < (Aj.card : ℝ) * (Bj.card : ℝ) := by
        rcases lt_or_ge 0 ((Aj.card : ℝ) * (Bj.card : ℝ)) with hpos | hnonpos
        · exact hpos
        · have hz : (Aj.card : ℝ) * (Bj.card : ℝ) = 0 :=
            le_antisymm hnonpos (by positivity)
          have hE1zero : (Gs j).edgeCount Aj Bj = 0 := by
            rcases mul_eq_zero.mp hz with hA | hB
            · have hA0 : Aj = ∅ := Finset.card_eq_zero.mp (by exact_mod_cast hA)
              simp [BipartiteGraph.edgeCount, hA0]
            · have hB0 : Bj = ∅ := Finset.card_eq_zero.mp (by exact_mod_cast hB)
              simp [BipartiteGraph.edgeCount, hB0]
          have hEzero : G.edgeCount X Y = 0 := by rw [← hE1eq, hE1zero]
          rw [hEzero] at hEpos
          exact absurd hEpos (lt_irrefl 0)
      have hAjBj_le : (Aj.card : ℝ) * (Bj.card : ℝ) ≤ (X.card : ℝ) * (Y.card : ℝ) := by
        have h1 : (Aj.card : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast Finset.card_le_card hAj_sub
        have h2 : (Bj.card : ℝ) ≤ (Y.card : ℝ) := by exact_mod_cast Finset.card_le_card hBj_sub
        exact mul_le_mul h1 h2 (by positivity) (by positivity)
      have hGj_ge : G.sGraph ≤ (Gs j).sGraph := by
        rw [hsG]
        have hmemA : ∀ a ∈ Aj, a ∈ (Gs j).left := fun a ha => (mem_partLeft.mp ha).2
        have hmemB : ∀ b ∈ Bj, b ∈ (Gs j).right := fun b hb => (mem_partRight.mp hb).2
        have hratio := sGraph_ge_ratio_cards (H := Gs j) Aj Bj hmemA hmemB
        calc
          ((G.edgeCount X Y : ℝ)) ^ 2 / ((X.card : ℝ) * (Y.card : ℝ)) ≤
              ((G.edgeCount X Y : ℝ)) ^ 2 / ((Aj.card : ℝ) * (Bj.card : ℝ)) := by
            apply div_le_div_of_nonneg_left (by positivity) hAjBjpos hAjBj_le
          _ ≤ (Gs j).sGraph := by
            rw [← hE1eq]
            exact hratio
      have hpow : G.sGraph ^ χ ≤ (Gs j).sGraph ^ χ :=
        Real.rpow_le_rpow (BipartiteGraph.sGraph_nonneg G) hGj_ge (le_of_lt (by linarith : 0 < χ))
      have hsingle : (Gs j).sGraph ^ χ ≤ ∑ i, (Gs i).sGraph ^ χ := by
        exact Finset.single_le_sum (fun i _ => Real.rpow_nonneg (BipartiteGraph.sGraph_nonneg (Gs i)) χ)
          (Finset.mem_univ j)
      exact le_trans hpow hsingle
  · have hcase2 : ∀ i : Fin (n + 1),
        ((partLeft X (Gs i).left).card : ℝ) / (X.card : ℝ) +
          ((partRight Y (Gs i).right).card : ℝ) / (Y.card : ℝ) < (13 : ℝ) / 8 := by
      intro i
      exact lt_of_not_ge (fun h => hcase1 ⟨i, h⟩)
    exact step_case2 hn hχ hχ1 hχ2 G Gs hcover X Y hleft hright hfull hEpos hcase2

theorem isGraphExponent_step (n : ℕ) (hn : 1 ≤ n) {χ : ℝ}
    (hχ : χ = 1 / 2 + 1 / (10 * Real.log ((n : ℝ) + 1)))
    (hprev : IsGraphExponent n χ) : IsGraphExponent (n + 1) χ := by
  intro m hm A B _ _ _ _ G Gs hcover
  classical
  have hlogpos : 0 < Real.log ((n : ℝ) + 1) := by
    apply Real.log_pos
    have : (1:ℝ) < (n : ℝ) + 1 := by
      have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      linarith
    exact this
  have hχpos : 0 < χ := by
    rw [hχ]
    have : 0 < 1 / (10 * Real.log ((n : ℝ) + 1)) := by positivity
    linarith
  have hχ1 : (1 : ℝ) / 2 < χ := by
    rw [hχ]
    have : 0 < 1 / (10 * Real.log ((n : ℝ) + 1)) := by positivity
    linarith
  have hχ2 : χ ≤ 2 / 3 := by
    rw [hχ]
    have hlog_ge : Real.log 2 ≤ Real.log ((n : ℝ) + 1) := by
      apply Real.log_le_log (by norm_num)
      have : (2:ℝ) ≤ (n:ℝ) + 1 := by
        have : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        linarith
      exact this
    have hlog_gt : (3:ℝ)/5 < Real.log ((n : ℝ) + 1) := by
      have : (3:ℝ)/5 < Real.log 2 := by linarith [Real.log_two_gt_d9]
      linarith
    have hsmall : 1 / (10 * Real.log ((n : ℝ) + 1)) ≤ 1 / 6 := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 10 * Real.log ((n : ℝ) + 1)) (by norm_num : (0:ℝ) < 6)]
      nlinarith
    linarith
  by_cases hmn : m ≤ n
  · exact hprev m hmn A B G Gs hcover
  · have hm_eq : m = n + 1 := by omega
    subst hm_eq
    obtain ⟨X, Y, hHsG, hHfull, hAdmG, hHratio⟩ := exists_densitySubgraph G
    set H : BipartiteGraph A B := graphOn G.edge X Y with hHdef
    have hcovH : IsCover H (fun i => frag (Gs i) X Y) := by
      simpa [H] using cover_frag hcover X Y
    by_cases hHpos : 0 < H.edgeCount X Y
    · have hmain : H.sGraph ^ χ ≤ ∑ i, (frag (Gs i) X Y).sGraph ^ χ :=
        step_normalized (n := n) hn hχ hχ1 hχ2 hprev H (fun i => frag (Gs i) X Y) hcovH X Y
          (by rfl) (by rfl) (by simpa [H] using (hHfull.trans hHratio.symm)) hHpos
      have hle : ∑ i, (frag (Gs i) X Y).sGraph ^ χ ≤ ∑ i, (Gs i).sGraph ^ χ := by
        apply Finset.sum_le_sum
        intro i _
        exact Real.rpow_le_rpow (BipartiteGraph.sGraph_nonneg _) (sGraph_frag_le (Gs i) X Y) (le_of_lt hχpos)
      calc
        G.sGraph ^ χ = H.sGraph ^ χ := by rw [hHsG]
        _ ≤ ∑ i, (frag (Gs i) X Y).sGraph ^ χ := hmain
        _ ≤ ∑ i, (Gs i).sGraph ^ χ := hle
    · have hHzero : H.sGraph = 0 := by
        rw [hHfull]
        have hzero : H.edgeCount X Y = 0 := Nat.eq_zero_of_not_pos hHpos
        have hzeroG : G.edgeCount X Y = 0 := by
          simpa [H, edgeCount_graphOn_self'] using hzero
        rw [ratio_of_admissible G hAdmG]
        simp [hzeroG]
      have hGzero : G.sGraph = 0 := by rw [← hHsG, hHzero]
      rw [hGzero, Real.zero_rpow hχpos.ne']
      exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (BipartiteGraph.sGraph_nonneg (Gs i)) χ

noncomputable def chiLower (m : ℕ) : ℝ :=
  if m = 1 then 1 else 1 / 2 + 1 / (10 * Real.log (m : ℝ))

theorem chiLower_succ_le (m : ℕ) (hm : 1 ≤ m) : chiLower (m + 1) ≤ chiLower m := by
  rcases eq_or_lt_of_le hm with rfl | hm2
  · have h1 : chiLower 1 = 1 := by simp [chiLower]
    have h2 : chiLower (1 + 1) = 1 / 2 + 1 / (10 * Real.log (2:ℝ)) := by
      norm_num [chiLower]
    rw [h2, h1]
    have hlog : (3:ℝ)/5 < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hpos : 0 < Real.log (2:ℝ) := by linarith
    have hle : 1 / (10 * Real.log (2:ℝ)) ≤ 1 / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  · have hm2' : 2 ≤ m := hm2
    rw [chiLower, chiLower]
    have h1 : ¬ (m + 1 = 1) := by omega
    have h0 : ¬ (m = 1) := by omega
    rw [if_neg h1, if_neg h0]
    have hlogm : 0 < Real.log (m : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (by omega : 1 < m)
    have hlog : Real.log (m : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.le_succ m
    have hlogm1 : 0 < Real.log ((m + 1 : ℕ) : ℝ) := by
      apply Real.log_pos
      exact_mod_cast (by omega : 1 < m + 1)
    have hden : 0 < 10 * Real.log (m : ℝ) := by positivity
    have hden' : 0 < 10 * Real.log ((m + 1 : ℕ) : ℝ) := by positivity
    have hrec : 1 / (10 * Real.log ((m + 1 : ℕ) : ℝ)) ≤ 1 / (10 * Real.log (m : ℝ)) := by
      apply one_div_le_one_div_of_le hden
      nlinarith
    linarith

theorem isGraphExponent_chiLower : ∀ n : ℕ, 1 ≤ n → IsGraphExponent n (chiLower n) := by
  intro n hn
  induction n with
  | zero => omega
  | succ k ih =>
      rcases k with _ | k
      · simpa [chiLower] using isGraphExponent_one
      · have hk1 : 1 ≤ k + 1 := by omega
        have hprev := ih hk1
        have hχle : chiLower (k + 1 + 1) ≤ chiLower (k + 1) := by
          simpa [Nat.add_assoc] using chiLower_succ_le (k + 1) hk1
        have hχpos : 0 < chiLower (k + 1 + 1) := by
          rw [chiLower]
          have : ¬ (k + 1 + 1 = 1) := by omega
          rw [if_neg this]
          have hlog : 0 < Real.log ((k + 1 + 1 : ℕ) : ℝ) := by
            apply Real.log_pos
            exact_mod_cast (by omega : 1 < k + 1 + 1)
          have : 0 < 1 / (10 * Real.log ((k + 1 + 1 : ℕ) : ℝ)) := by positivity
          linarith
        have hprev' : IsGraphExponent (k + 1) (chiLower (k + 1 + 1)) :=
          isGraphExponent_of_le hχpos hχle hprev
        have hχeq : chiLower (k + 1 + 1) =
            1 / 2 + 1 / (10 * Real.log (((k + 1 : ℕ) : ℝ) + 1)) := by
          rw [chiLower]
          have : ¬ (k + 1 + 1 = 1) := by omega
          rw [if_neg this]
          congr 1
          congr 1
          norm_num [Nat.cast_add, Nat.cast_one]
        have hstep := isGraphExponent_step (k + 1) hk1 hχeq hprev'
        simpa [hχeq] using hstep

/-- The complete bipartite graph on `2` and `1` vertices: two edges. -/
def twoEdgeGraph : BipartiteGraph (Fin 2) (Fin 1) where
  left := Set.univ
  right := Set.univ
  edge := fun _ _ => true

/-- One of the two single-edge subgraphs of `twoEdgeGraph`. -/
def singleEdgeGraph (i : Fin 2) : BipartiteGraph (Fin 2) (Fin 1) where
  left := {i}
  right := Set.univ
  edge := fun a _ => decide (a = i)

theorem twoEdgeGraph_sGraph_le : twoEdgeGraph.sGraph ≤ 2 := by
  rw [BipartiteGraph.sGraph]
  apply Finset.sup'_le
  intro p _
  by_cases h : (p.1.card : ℝ) * (p.2.card : ℝ) = 0
  · simp [BipartiteGraph.ratio, BipartiteGraph.Admissible, twoEdgeGraph, h]
  · have hAdm : twoEdgeGraph.Admissible p.1 p.2 := by
      simp [BipartiteGraph.Admissible, twoEdgeGraph]
    rw [BipartiteGraph.ratio, if_pos hAdm]
    have he : twoEdgeGraph.edgeCount p.1 p.2 = p.1.card * p.2.card := by
      simp [BipartiteGraph.edgeCount, twoEdgeGraph]
    rw [he, Nat.cast_mul]
    have hx : p.1.card ≤ 2 := by simpa using Finset.card_le_univ p.1
    have hy : p.2.card ≤ 1 := by simpa using Finset.card_le_univ p.2
    have hxR : (p.1.card : ℝ) ≤ 2 := by exact_mod_cast hx
    have hyR : (p.2.card : ℝ) ≤ 1 := by exact_mod_cast hy
    have hpos : 0 < (p.1.card : ℝ) * (p.2.card : ℝ) :=
      lt_of_le_of_ne (by positivity) (Ne.symm h)
    field_simp
    nlinarith

theorem twoEdgeGraph_sGraph_ge : 2 ≤ twoEdgeGraph.sGraph := by
  have hAdm : twoEdgeGraph.Admissible (Finset.univ) (Finset.univ) := by
    simp [BipartiteGraph.Admissible, twoEdgeGraph]
  have hE : twoEdgeGraph.edgeCount (Finset.univ : Finset (Fin 2)) (Finset.univ : Finset (Fin 1)) = 2 := by
    simp [BipartiteGraph.edgeCount, twoEdgeGraph]
  have hr : twoEdgeGraph.ratio (Finset.univ : Finset (Fin 2)) (Finset.univ : Finset (Fin 1)) = 2 := by
    rw [BipartiteGraph.ratio, if_pos hAdm, hE]
    norm_num
  rw [BipartiteGraph.sGraph]
  exact le_trans (le_of_eq hr.symm)
    (Finset.le_sup' (fun p : Finset (Fin 2) × Finset (Fin 1) => twoEdgeGraph.ratio p.1 p.2)
      (Finset.mem_univ (Finset.univ, Finset.univ)))

theorem singleEdgeGraph_sGraph_le (i : Fin 2) : (singleEdgeGraph i).sGraph ≤ 1 := by
  rw [BipartiteGraph.sGraph]
  apply Finset.sup'_le
  intro p _
  by_cases hAdm : (singleEdgeGraph i).Admissible p.1 p.2
  · rw [BipartiteGraph.ratio, if_pos hAdm]
    have hXsub : p.1 ⊆ ({i} : Finset (Fin 2)) := by
      intro a ha
      simpa [singleEdgeGraph] using hAdm.1 a ha
    have hXle : p.1.card ≤ 1 := by simpa using Finset.card_le_card hXsub
    by_cases hX0 : p.1.card = 0
    · have hE0 : (singleEdgeGraph i).edgeCount p.1 p.2 = 0 := by
        simp [BipartiteGraph.edgeCount, singleEdgeGraph, Finset.card_eq_zero.mp hX0]
      rw [hE0]; simp
    · have hX1 : p.1.card = 1 := by omega
      have hEcard : (singleEdgeGraph i).edgeCount p.1 p.2 ≤ p.2.card := by
        calc
          (singleEdgeGraph i).edgeCount p.1 p.2 ≤ p.1.card * p.2.card := by
            unfold BipartiteGraph.edgeCount
            calc
              ((p.1.product p.2).filter (fun q => (singleEdgeGraph i).edge q.1 q.2)).card ≤
                  (p.1.product p.2).card := Finset.card_filter_le _ _
              _ = p.1.card * p.2.card := Finset.card_product _ _
          _ = p.2.card := by rw [hX1, one_mul]
      have hEreal : ((singleEdgeGraph i).edgeCount p.1 p.2 : ℝ) ≤ (p.2.card : ℝ) := by exact_mod_cast hEcard
      have hy : p.2.card ≤ 1 := by simpa using Finset.card_le_univ p.2
      have hyR : (p.2.card : ℝ) ≤ 1 := by exact_mod_cast hy
      rw [hX1]
      by_cases hy0 : p.2.card = 0
      · have hE0 : (singleEdgeGraph i).edgeCount p.1 p.2 = 0 := by
          exact_mod_cast (le_antisymm (by simpa [hy0] using hEreal) (by positivity))
        simp [hE0, hy0]
      · have hypos : 0 < (p.2.card : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hy0)
        field_simp [hypos.ne']
        have hE0 : 0 ≤ ((singleEdgeGraph i).edgeCount p.1 p.2 : ℝ) := by positivity
        have h1 : ((singleEdgeGraph i).edgeCount p.1 p.2 : ℝ) * ((singleEdgeGraph i).edgeCount p.1 p.2 : ℝ) ≤
            ((singleEdgeGraph i).edgeCount p.1 p.2 : ℝ) * (p.2.card : ℝ) :=
          mul_le_mul_of_nonneg_left hEreal hE0
        have h2 : ((singleEdgeGraph i).edgeCount p.1 p.2 : ℝ) * (p.2.card : ℝ) ≤ (p.2.card : ℝ) := by
          nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ (p.2.card:ℝ))
            (sub_nonneg.mpr (le_trans hEreal hyR))]
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using le_trans h1 h2
  · rw [BipartiteGraph.ratio, if_neg hAdm]
    norm_num

theorem singleEdgeGraph_sGraph_ge (i : Fin 2) : 1 ≤ (singleEdgeGraph i).sGraph := by
  have hAdm : (singleEdgeGraph i).Admissible {i} (Finset.univ : Finset (Fin 1)) := by
    simp [BipartiteGraph.Admissible, singleEdgeGraph]
  have hEpos : 0 < (singleEdgeGraph i).edgeCount {i} (Finset.univ : Finset (Fin 1)) := by
    apply Finset.card_pos.mpr
    refine ⟨(i, (0 : Fin 1)), ?_⟩
    simp [BipartiteGraph.edgeCount, singleEdgeGraph]
  have hratio : 1 ≤ (singleEdgeGraph i).ratio {i} (Finset.univ : Finset (Fin 1)) := by
    rw [BipartiteGraph.ratio, if_pos hAdm]
    have hEc : (1:ℝ) ≤ ((singleEdgeGraph i).edgeCount {i} (Finset.univ : Finset (Fin 1)) : ℝ) := by
      exact_mod_cast hEpos
    have hcards : (({i} : Finset (Fin 2)).card : ℝ) * ((Finset.univ : Finset (Fin 1)).card : ℝ) = 1 := by
      norm_num
    rw [hcards]
    nlinarith [hEc]
  rw [BipartiteGraph.sGraph]
  exact le_trans hratio
    (Finset.le_sup' (fun p : Finset (Fin 2) × Finset (Fin 1) => (singleEdgeGraph i).ratio p.1 p.2)
      (Finset.mem_univ ({i}, Finset.univ)))

theorem singleEdgeCover_isCover :
    IsCover twoEdgeGraph (fun i : Fin 2 => singleEdgeGraph i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i a _
    simp [twoEdgeGraph]
  · intro i b _
    simp [twoEdgeGraph]
  · intro i a b
    simp [singleEdgeGraph, twoEdgeGraph, eq_comm]
  · intro a b _
    exact ⟨a, by simp [singleEdgeGraph]⟩

theorem isGraphExponent_le_one {k : ℕ} (hk : 2 ≤ k) {χ : ℝ}
    (hχ : IsGraphExponent k χ) : χ ≤ 1 := by
  have hcov : IsCover twoEdgeGraph (fun i : Fin 2 => singleEdgeGraph i) := singleEdgeCover_isCover
  have h := hχ 2 (by omega) (Fin 2) (Fin 1) twoEdgeGraph (fun i => singleEdgeGraph i) hcov
  have hG : twoEdgeGraph.sGraph = 2 :=
    le_antisymm twoEdgeGraph_sGraph_le twoEdgeGraph_sGraph_ge
  have hSi : ∀ i : Fin 2, (singleEdgeGraph i).sGraph = 1 := fun i =>
    le_antisymm (singleEdgeGraph_sGraph_le i) (singleEdgeGraph_sGraph_ge i)
  rw [hG] at h
  simp only [hSi, Real.one_rpow, Fin.sum_univ_two] at h
  norm_num at h
  have h2 : (2:ℝ) ^ χ ≤ 2 ^ (1:ℝ) := by simpa using h
  exact (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp h2

theorem bddAbove_isGraphExponent (k : ℕ) (hk : 2 ≤ k) :
    BddAbove {χ : ℝ | IsGraphExponent k χ} :=
  ⟨1, fun χ hχ => isGraphExponent_le_one hk hχ⟩

theorem theorem2 (k : ℕ) (hk : 2 ≤ k) :
    (1 : ℝ) / 2 + 1 / (10 * Real.log (k : ℝ)) ≤ chi k := by
  have hk1 : k ≠ 1 := by omega
  have hmem : (1 / 2 + 1 / (10 * Real.log (k : ℝ))) ∈ {χ : ℝ | IsGraphExponent k χ} := by
    have h := isGraphExponent_chiLower k (by omega)
    have heq : chiLower k = 1 / 2 + 1 / (10 * Real.log (k : ℝ)) := by
      rw [chiLower]
      simp [hk1]
    rwa [heq] at h
  exact le_csSup (bddAbove_isGraphExponent k hk) hmem


end UnateLin
