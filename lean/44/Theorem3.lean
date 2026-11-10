import Mathlib

/-!
# Theorem 3 of Section 5: large independence index with linear complexity `2n`

Self-contained formalization of Theorem 3 of I. S. Sergeev, *Lower bounds on the additive
complexity of linear operators and bilinear algorithms* (Section 5).
The only import is `Mathlib`; every auxiliary result used below is proved in this file.

## Statement

For every sufficiently large `n`, with `m = ⌈n^{8/9}⌉`, there is a matrix
`B ∈ GF(2)^{n × m}` — represented as a finite set of `n` row vectors of weight `3` in
`GF(2)^m` — whose independence index satisfies `ind B = Ω(n^{1/9})` and whose additive
complexity `L B` (the length of a shortest vector addition chain computing all rows)
satisfies `L B ≤ 2n`.  This is `theorem3` below.

## Proof outline

Let `W₃` be the finite set of `n × m` matrices all of whose rows have weight `3`.  For
`1 ≤ k ≤ s`, let `E_k ⊂ W₃` be the event that some `2k` rows have all their ones inside
some `3k` columns.  The union bound gives

`|E_k| / |W₃| ≤ C(n,2k) C(m,3k) C(3k,3)^{2k} / C(m,3)^{2k} ≤ ((9k)^6 n^2 / m^3)^k < 2^{-k}`,

because `m ≥ n^{8/9}` and `k ≤ n^{1/9}/18`.  Summing over `k = 1,…,s` shows that some
`A ∈ W₃` avoids all the events `E_k`.  For such an `A`:

* any odd number of rows sums to a nonzero vector (the total number of ones is odd);
* if `2k ≤ 2s` rows summed to zero then every column would contain an even number of ones,
  hence the rows would lie in at most `3k` columns, contradicting `A ∉ E_k`.

Thus every nonempty subset of at most `2s` rows has nonzero sum, i.e. `ind B ≥ 2s`, and
`2s ≥ n^{1/9}/40`.  Finally, each row of weight `3` costs two additions, so `L B ≤ 2n`.

## Organization

* vectors, vector addition chains and the additive complexity `vecComplexity`;
* the independence index `ind` and its sum characterization;
* sums of characteristic vectors and their linear independence;
* the counting argument (`W3`, the bad sets `badSet`, the union bound
  `exists_good_matrix`);
* the numeric estimates behind the union bound;
* from a spread matrix to one with `ind ≥ 2s` (`ind_image_ge`);
* the explicit chain of length `2n` computing all rows (`chainY`, `chainY_valid`);
* the numeric parameters `thmM`/`thmS`, the bundle `numeric_facts`, and the final
  theorem `theorem3` (with `N₀ = 36^9`).
-/

set_option maxHeartbeats 1000000

namespace AchainsComplexityGF2

open scoped BigOperators

/-! ### Vectors, addition chains and the additive complexity `L` -/

/-- Vectors of dimension `n` over `GF(2) = ZMod 2`. -/
abbrev Vec (n : ℕ) := Fin n → (ZMod 2)

/-- The `i`-th standard basis vector `eᵢ`. -/
def basisVec {n : ℕ} (i : Fin n) : Vec n := fun j => if j = i then 1 else 0

/-- The vectors available to an addition chain at step `k`: the basis vectors together with
the previously computed vectors `y₁,…,y_{k-1}`. -/
def chainPool {n L : ℕ} (y : Fin L → Vec n) (k : ℕ) (hk : k ≤ L) : Fin n ⊕ Fin k → Vec n
  | Sum.inl i => basisVec i
  | Sum.inr j => y ⟨j.1, lt_of_lt_of_le j.2 hk⟩

/-- A vector addition chain in `GF(2)^n`: a sequence `y₁,…,y_L` in which every `y_k` is the
sum of two vectors available strictly earlier. -/
structure VecAddChain (n : ℕ) where
  /-- the length of the chain -/
  L : ℕ
  /-- the vectors computed by the chain -/
  y : Fin L → Vec n
  /-- every step is the sum of two available vectors -/
  valid : ∀ k : Fin L, ∃ a b : Fin n ⊕ Fin k.1,
    y k = chainPool y k.1 (le_of_lt k.2) a + chainPool y k.1 (le_of_lt k.2) b

namespace VecAddChain

/-- A chain computes a finite set `B` of vectors if every element of `B` occurs among the
basis vectors, the computed vectors, or is zero. -/
def ComputesSet {m : ℕ} (c : VecAddChain m) (B : Finset (Vec m)) : Prop :=
  ∀ b ∈ B, b ∈ Set.range basisVec ∪ Set.range c.y ∪ ({0} : Set (Vec m))

end VecAddChain

/-- The additive complexity `L(B)` of a finite set `B` of vectors: the length of a shortest
addition chain computing every element of `B`. -/
noncomputable def vecComplexity {m : ℕ} (B : Finset (Vec m)) : ℕ :=
  sInf { l | ∃ c : VecAddChain m, c.L = l ∧ c.ComputesSet B }

theorem vecComplexity_le {m : ℕ} {B : Finset (Vec m)} {c : VecAddChain m}
    (h : c.ComputesSet B) : vecComplexity B ≤ c.L :=
  Nat.sInf_le ⟨c, rfl, h⟩

/-- Weight of a vector relative to a set of coordinates: the number of nonzero entries. -/
def weight {m : ℕ} (W : Finset (Fin m)) (v : Vec m) : ℕ :=
  (W.filter (fun i => v i ≠ 0)).card

/-- The characteristic vector of a finite set of coordinates. -/
def vecOf {m : ℕ} (S : Finset (Fin m)) : Vec m := fun j => if j ∈ S then 1 else 0

@[simp] theorem vecOf_apply {m : ℕ} (S : Finset (Fin m)) (j : Fin m) :
    vecOf S j = if j ∈ S then (1 : ZMod 2) else 0 := rfl

theorem weight_univ_vecOf {m : ℕ} (S : Finset (Fin m)) :
    weight (Finset.univ : Finset (Fin m)) (vecOf S) = S.card := by
  unfold weight
  congr 1
  ext j
  simp [vecOf]

/-- `vecOf` is injective. -/
theorem vecOf_injective {m : ℕ} : Function.Injective (vecOf (m := m)) := by
  intro S T h
  ext j
  have := congrFun h j
  simp only [vecOf_apply] at this
  constructor <;> intro hj
  · by_contra hT
    rw [ite_eq_left hj, ite_eq_right hT] at this
    exact one_ne_zero this
  · by_contra hS
    rw [ite_eq_right hS, ite_eq_left hj] at this
    exact one_ne_zero this.symm

@[simp] theorem vecOf_empty {m : ℕ} : vecOf (∅ : Finset (Fin m)) = 0 := by
  funext j; simp [vecOf]

theorem vecOf_nonzero {m : ℕ} {S : Finset (Fin m)} (h : S.Nonempty) : vecOf S ≠ 0 := by
  obtain ⟨j, hj⟩ := h
  intro h0
  have := congrFun h0 j
  simp [vecOf, hj] at this

/-! ### The independence index `ind` -/

/-- A finite set of vectors over `GF(2)` is linearly independent. -/
def Indep {m : ℕ} (S : Finset (Vec m)) : Prop :=
  LinearIndependent (ZMod 2) (fun x : S => (x : Vec m))

theorem indep_empty {m : ℕ} : Indep (∅ : Finset (Vec m)) :=
  linearIndependent_empty_type

theorem Indep.mono {m : ℕ} {S T : Finset (Vec m)} (h : Indep T) (hST : S ⊆ T) : Indep S := by
  have h' := h.comp (fun x : S => (⟨x.1, hST x.2⟩ : T)) (fun x y hxy => by
    have := congrArg Subtype.val hxy
    simpa using this)
  simpa [Indep, Function.comp_def] using h'

/-- `AllIndep B k`: every `k`-element subset of `B` is linearly independent. -/
def AllIndep {m : ℕ} (B : Finset (Vec m)) (k : ℕ) : Prop :=
  ∀ S : Finset (Vec m), S ⊆ B → S.card = k → Indep S

/-- The independence index: the largest `k ≤ |B|` such that every `k` elements of `B` are
linearly independent. -/
noncomputable def ind {m : ℕ} (B : Finset (Vec m)) : ℕ := by
  classical
  exact Nat.findGreatest (AllIndep B) B.card

theorem ind_le_card {m : ℕ} (B : Finset (Vec m)) : ind B ≤ B.card := by
  classical
  unfold ind
  exact Nat.findGreatest_le _

theorem allIndep_zero {m : ℕ} (B : Finset (Vec m)) : AllIndep B 0 := by
  intro S _ hc
  rw [Finset.card_eq_zero.mp hc]
  exact indep_empty

theorem ind_spec {m : ℕ} (B : Finset (Vec m)) : AllIndep B (ind B) := by
  classical
  unfold ind
  exact Nat.findGreatest_spec (m := 0) (Nat.zero_le _) (allIndep_zero B)

theorem ind_elim {m : ℕ} {B S : Finset (Vec m)} {r : ℕ} (hr : r ≤ ind B) (hSB : S ⊆ B)
    (hcard : S.card = r) : Indep S := by
  classical
  obtain ⟨T, hST, hTB, hTc⟩ := Finset.exists_subsuperset_card_eq hSB (hcard ▸ hr) (ind_le_card B)
  exact (ind_spec B T hTB hTc).mono hST

theorem le_ind {m : ℕ} {B : Finset (Vec m)} {r : ℕ} (h : AllIndep B r) (hr : r ≤ B.card) :
    r ≤ ind B := by
  classical
  unfold ind
  exact Nat.le_findGreatest hr h

/-! ### Sums of characteristic vectors and linear independence -/

/-- In `GF(2)` every element is `0` or `1`. -/
theorem zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have h := ZMod.val_lt x
  have h' : x.val = 0 ∨ x.val = 1 := by omega
  rcases h' with h0 | h1
  · left; rw [← ZMod.natCast_zmod_val x, h0]; norm_num
  · right; rw [← ZMod.natCast_zmod_val x, h1]; norm_num

theorem smul_vec_eq_zero_or_self {m : ℕ} (a : ZMod 2) (v : Vec m) :
    a • v = 0 ∨ a • v = v := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl
  · left; simp
  · right; simp

/-- A finite set of vectors over `GF(2)` is independent iff no nonempty subcollection sums
to zero. -/
theorem indep_iff_sum_ne_zero {m : ℕ} (S : Finset (Vec m)) :
    Indep S ↔ ∀ T : Finset ↥S, T.Nonempty → ∑ x ∈ T, (x : Vec m) ≠ 0 := by
  constructor
  · rintro hLI T hne hsum
    obtain ⟨x, hx⟩ := hne
    have h := (linearIndependent_iff'.mp hLI) T (fun _ => (1 : ZMod 2))
    have hsum' : ∑ i ∈ T, (1 : ZMod 2) • (i : Vec m) = 0 := by simpa using hsum
    exact one_ne_zero (h hsum' x hx)
  · intro h
    change LinearIndependent (ZMod 2) (fun x : S => (x : Vec m))
    rw [linearIndependent_iff']
    intro s g hsum i hi
    set T : Finset ↥S := s.filter (fun x => g x ≠ 0) with hT
    have hTeq : ∑ x ∈ T, (x : Vec m) = ∑ x ∈ s, g x • (x : Vec m) := by
      rw [hT, Finset.sum_filter]
      refine Finset.sum_congr rfl ?_
      intro x _
      by_cases hg : g x = 0
      · simp [hg]
      · rcases zmod2_eq_zero_or_one (g x) with h0 | h1
        · exact absurd h0 hg
        · simp [h1]
    have hzero : ∑ x ∈ T, (x : Vec m) = 0 := by rw [hTeq, hsum]
    have hTempty : T = ∅ := by
      by_contra hne
      exact h T (Finset.nonempty_iff_ne_empty.mpr hne) hzero
    by_contra hg
    have : i ∈ T := by rw [hT]; exact Finset.mem_filter.mpr ⟨hi, hg⟩
    rw [hTempty] at this
    simp at this

/-- The `j`-th coordinate of a sum of characteristic vectors counts how many of the sets
contain `j`, modulo two. -/
theorem sum_vecOf_apply {m : ℕ} {ι : Type*} (U : Finset ι)
    (A : ι → Finset (Fin m)) (j : Fin m) :
    (∑ i ∈ U, vecOf (A i)) j = ((U.filter (fun i => j ∈ A i)).card : ZMod 2) := by
  rw [Finset.sum_apply]
  simp only [vecOf_apply]
  exact Finset.sum_boole (fun i => j ∈ A i) U

/-- If a sum of characteristic vectors vanishes, then every column is covered an even number
of times. -/
theorem even_count_of_sum_eq_zero {m : ℕ} {ι : Type*} (U : Finset ι)
    (A : ι → Finset (Fin m)) (h : ∑ i ∈ U, vecOf (A i) = 0) (j : Fin m) :
    Even (U.filter (fun i => j ∈ A i)).card := by
  have h1 := congrFun h j
  simp only [Pi.zero_apply] at h1
  rw [sum_vecOf_apply] at h1
  exact ZMod.natCast_eq_zero_iff_even.mp h1

theorem sum_filter_card_eq_sum_card {m : ℕ} {ι : Type*} (U : Finset ι)
    (A : ι → Finset (Fin m)) :
    ∑ j : Fin m, (U.filter (fun i => j ∈ A i)).card = ∑ i ∈ U, (A i).card := by
  have h1 : ∀ j : Fin m, (U.filter (fun i => j ∈ A i)).card
      = ∑ i ∈ U, if j ∈ A i then 1 else 0 := by
    intro j
    rw [Finset.card_filter]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← Finset.card_filter (fun j => j ∈ A i) (Finset.univ)]
  congr 1
  ext j
  simp

/-- If the total size of a family of sets is odd, then the sum of the characteristic vectors
is nonzero. -/
theorem sum_vecOf_ne_zero_of_odd {m : ℕ} {ι : Type*} (U : Finset ι)
    (A : ι → Finset (Fin m)) (hodd : Odd (∑ i ∈ U, (A i).card)) :
    ∑ i ∈ U, vecOf (A i) ≠ 0 := by
  intro hzero
  have heven : ∀ j : Fin m, Even (U.filter (fun i => j ∈ A i)).card :=
    fun j => even_count_of_sum_eq_zero U A hzero j
  have hsum_even : Even (∑ j : Fin m, (U.filter (fun i => j ∈ A i)).card) :=
    Finset.even_sum _ (fun j _ => heven j)
  rw [sum_filter_card_eq_sum_card] at hsum_even
  rcases hodd with ⟨c, hc⟩
  rcases hsum_even with ⟨d, hd⟩
  omega

/-- If a family of `3`-element sets has a vanishing characteristic sum, then its union has at
most `3k` elements. -/
theorem card_biUnion_le_of_sum_eq_zero {m : ℕ} {ι : Type*} (U : Finset ι)
    (A : ι → Finset (Fin m)) (hcard3 : ∀ i, (A i).card = 3)
    (h : ∑ i ∈ U, vecOf (A i) = 0) {k : ℕ} (hU : U.card = 2 * k) :
    (U.biUnion A).card ≤ 3 * k := by
  have heven : ∀ j : Fin m, Even (U.filter (fun i => j ∈ A i)).card :=
    fun j => even_count_of_sum_eq_zero U A h j
  have hpos : ∀ j ∈ U.biUnion A, 2 ≤ (U.filter (fun i => j ∈ A i)).card := by
    intro j hj
    rw [Finset.mem_biUnion] at hj
    obtain ⟨i, hiU, hij⟩ := hj
    have hmem : i ∈ U.filter (fun i => j ∈ A i) := Finset.mem_filter.mpr ⟨hiU, hij⟩
    have h1 : 1 ≤ (U.filter (fun i => j ∈ A i)).card := Finset.card_pos.mpr ⟨i, hmem⟩
    rcases heven j with ⟨c, hc⟩
    omega
  have h1 : 2 * (U.biUnion A).card ≤ ∑ j ∈ U.biUnion A, (U.filter (fun i => j ∈ A i)).card := by
    calc 2 * (U.biUnion A).card = ∑ _j ∈ U.biUnion A, 2 := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ j ∈ U.biUnion A, (U.filter (fun i => j ∈ A i)).card :=
          Finset.sum_le_sum hpos
  have h2 : ∑ j ∈ U.biUnion A, (U.filter (fun i => j ∈ A i)).card
      ≤ ∑ j : Fin m, (U.filter (fun i => j ∈ A i)).card :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  have h3 : ∑ j : Fin m, (U.filter (fun i => j ∈ A i)).card = 3 * U.card := by
    rw [sum_filter_card_eq_sum_card]
    rw [Finset.sum_congr rfl (fun i _ => hcard3 i), Finset.sum_const, smul_eq_mul]
    ring
  omega

/-- Main combinatorial step: for a `3`-uniform family that is "spread out" (no `2k` rows lie
in `3k` columns for `1 ≤ k ≤ s`), every nonempty collection of at most `2s` rows has nonzero
characteristic sum. -/
theorem sum_ne_zero_of_spread {n m s : ℕ} (A : Fin n → Finset (Fin m))
    (hcard3 : ∀ i, (A i).card = 3)
    (h3s : 3 * s ≤ m)
    (hspread : ∀ k, 1 ≤ k → k ≤ s → ∀ I : Finset (Fin n), I.card = 2 * k →
      ∀ J : Finset (Fin m), J.card = 3 * k → ¬ (∀ i ∈ I, A i ⊆ J))
    {U : Finset (Fin n)} (hne : U.Nonempty) (hU : U.card ≤ 2 * s) :
    ∑ i ∈ U, vecOf (A i) ≠ 0 := by
  intro hzero
  rcases Nat.even_or_odd U.card with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk2 : U.card = 2 * k := by omega
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · subst h0
        simp at hk2
        exact absurd hk2 (by simpa using hne.ne_empty)
      · exact hpos
    have hks : k ≤ s := by omega
    have hJ : (U.biUnion A).card ≤ 3 * k :=
      card_biUnion_le_of_sum_eq_zero U A hcard3 hzero hk2
    obtain ⟨J, hsub, -, hJcard⟩ :=
      Finset.exists_subsuperset_card_eq (Finset.subset_univ (U.biUnion A)) hJ
        (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    exact hspread k hk1 hks U hk2 J hJcard
      (fun i hi j hj => hsub (Finset.mem_biUnion.mpr ⟨i, hi, hj⟩))
  · have hsum : ∑ i ∈ U, (A i).card = 3 * U.card := by
      rw [Finset.sum_congr rfl (fun i _ => hcard3 i), Finset.sum_const, smul_eq_mul]
      ring
    exact sum_vecOf_ne_zero_of_odd U A (by rw [hsum, hk]; exact ⟨3 * k + 1, by ring⟩) hzero

/-! ### The counting argument: matrices of row weight `3` -/

/-- `W3 n m` is the set of `n × m` matrices over `GF(2)` all of whose rows have weight `3`,
encoded as functions `Fin n → Finset (Fin m)`: a row is represented by the set of columns in
which it has a `1`. -/
def W3 (n m : ℕ) : Finset (Fin n → Finset (Fin m)) :=
  Fintype.piFinset (fun _ => (Finset.univ : Finset (Fin m)).powersetCard 3)

theorem mem_W3 {n m : ℕ} {A : Fin n → Finset (Fin m)} :
    A ∈ W3 n m ↔ ∀ i, (A i).card = 3 := by
  classical
  simp [W3, Fintype.mem_piFinset, Finset.mem_powersetCard]

theorem card_W3 (n m : ℕ) : (W3 n m).card = (m.choose 3) ^ n := by
  classical
  rw [W3, Fintype.card_piFinset]
  simp [Finset.card_powersetCard]

/-- Matrices of `W3 n m` whose `I`-rows avoid a set `J` of columns. -/
theorem filter_W3_subset {n m : ℕ} (I : Finset (Fin n)) (J : Finset (Fin m)) :
    (W3 n m).filter (fun A => ∀ i ∈ I, A i ⊆ J)
      = Fintype.piFinset (fun i =>
          if i ∈ I then J.powersetCard 3
          else (Finset.univ : Finset (Fin m)).powersetCard 3) := by
  classical
  ext A
  rw [Finset.mem_filter, mem_W3, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h3, hsub⟩ i
    by_cases hi : i ∈ I
    · rw [ite_eq_left hi, Finset.mem_powersetCard]
      exact ⟨hsub i hi, h3 i⟩
    · rw [ite_eq_right hi, Finset.mem_powersetCard]
      exact ⟨Finset.subset_univ _, h3 i⟩
  · intro h
    refine ⟨fun i => ?_, fun i hi => ?_⟩
    · have := h i
      by_cases hi : i ∈ I
      · rw [ite_eq_left hi, Finset.mem_powersetCard] at this
        exact this.2
      · rw [ite_eq_right hi, Finset.mem_powersetCard] at this
        exact this.2
    · have := h i
      rw [ite_eq_left hi, Finset.mem_powersetCard] at this
      exact this.1

theorem card_filter_W3_subset {n m : ℕ} (I : Finset (Fin n)) (J : Finset (Fin m)) :
    ((W3 n m).filter (fun A => ∀ i ∈ I, A i ⊆ J)).card
      = (J.card.choose 3) ^ I.card * (m.choose 3) ^ (n - I.card) := by
  classical
  rw [filter_W3_subset, Fintype.card_piFinset]
  have h1 : ∀ i : Fin n,
      (if i ∈ I then J.powersetCard 3
        else (Finset.univ : Finset (Fin m)).powersetCard 3).card
        = if i ∈ I then J.card.choose 3 else m.choose 3 := by
    intro i
    by_cases hi : i ∈ I <;> simp [hi, Finset.card_powersetCard]
  simp only [h1]
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin n)) (· ∈ I)]
  have h2 : (Finset.univ : Finset (Fin n)).filter (· ∈ I) = I := by ext x; simp
  have h3 : (Finset.univ : Finset (Fin n)).filter (fun i => ¬ i ∈ I) = Finset.univ \ I := by
    ext x; simp
  rw [h2, h3]
  have h4 : ∏ i ∈ I, (if i ∈ I then J.card.choose 3 else m.choose 3)
      = (J.card.choose 3) ^ I.card := by
    rw [Finset.prod_congr rfl (fun i hi => by rw [ite_eq_left hi]), Finset.prod_const]
  have h5 : ∏ i ∈ Finset.univ \ I, (if i ∈ I then J.card.choose 3 else m.choose 3)
      = (m.choose 3) ^ (n - I.card) := by
    rw [Finset.prod_congr rfl (fun i hi => by
      have hni : i ∉ I := (Finset.mem_sdiff.mp hi).2
      rw [ite_eq_right hni]), Finset.prod_const, Finset.card_sdiff,
      Finset.inter_eq_left.mpr (Finset.subset_univ I), Finset.card_univ, Fintype.card_fin]
  rw [h4, h5]

/-- The set of "bad" matrices of `W3 n m`: those for which some `2k` rows have all their ones
concentrated in some set of `3k` columns. -/
def badSet (n m k : ℕ) : Finset (Fin n → Finset (Fin m)) :=
  (((Finset.univ : Finset (Fin n)).powersetCard (2 * k)) ×ˢ
      ((Finset.univ : Finset (Fin m)).powersetCard (3 * k))).biUnion
    (fun p => (W3 n m).filter (fun A => ∀ i ∈ p.1, A i ⊆ p.2))

theorem card_badSet_le (n m k : ℕ) :
    (badSet n m k).card ≤ (n.choose (2 * k)) * (m.choose (3 * k)) *
      (((3 * k).choose 3) ^ (2 * k) * (m.choose 3) ^ (n - 2 * k)) := by
  classical
  set C := ((3 * k).choose 3) ^ (2 * k) * (m.choose 3) ^ (n - 2 * k) with hC
  have hterm : ∀ p ∈ ((Finset.univ : Finset (Fin n)).powersetCard (2 * k)) ×ˢ
      ((Finset.univ : Finset (Fin m)).powersetCard (3 * k)),
      ((W3 n m).filter (fun A => ∀ i ∈ p.1, A i ⊆ p.2)).card ≤ C := by
    rintro ⟨I, J⟩ hp
    rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard] at hp
    obtain ⟨⟨-, hI⟩, ⟨-, hJ⟩⟩ := hp
    rw [card_filter_W3_subset, hI, hJ]
  calc (badSet n m k).card
      ≤ ∑ p ∈ ((Finset.univ : Finset (Fin n)).powersetCard (2 * k)) ×ˢ
          ((Finset.univ : Finset (Fin m)).powersetCard (3 * k)),
          ((W3 n m).filter (fun A => ∀ i ∈ p.1, A i ⊆ p.2)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ ((Finset.univ : Finset (Fin n)).powersetCard (2 * k)) ×ˢ
          ((Finset.univ : Finset (Fin m)).powersetCard (3 * k)), C :=
        Finset.sum_le_sum hterm
    _ = (((Finset.univ : Finset (Fin n)).powersetCard (2 * k)) ×ˢ
          ((Finset.univ : Finset (Fin m)).powersetCard (3 * k))).card * C := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = _ := by
        rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
          Finset.card_univ, Finset.card_univ, Fintype.card_fin, Fintype.card_fin, hC]

/-! ### Numeric estimates -/

theorem descFactorial_three (m : ℕ) : m.descFactorial 3 = m * (m - 1) * (m - 2) := by
  rcases m with _ | _ | _ | m <;> simp [Nat.descFactorial] ; ring

/-- `m^3 ≤ 27 * C(m,3)`: a lower bound for the binomial coefficient `C(m,3)`. -/
theorem pow_three_le_choose_three (m : ℕ) (hm : 3 ≤ m) :
    (m : ℝ) ^ 3 ≤ 27 * (m.choose 3 : ℝ) := by
  have hdesc : m.descFactorial 3 = m * (m - 1) * (m - 2) := descFactorial_three m
  have hfact : m.descFactorial 3 = 6 * m.choose 3 := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]; norm_num
  have hnat : m * (m - 1) * (m - 2) = 6 * m.choose 3 := by rw [← hdesc, hfact]
  have hcast : (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) = 6 * (m.choose 3 : ℝ) := by
    have h := congrArg (fun x : ℕ => (x : ℝ)) hnat
    push_cast at h
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_sub (by omega : 2 ≤ m)] at h
    simpa using h
  have hm' : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hprod : (0 : ℝ) ≤ ((m : ℝ) - 3) * (7 * (m : ℝ) - 6) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith [hcast, hprod, hm']

/-- The counting ratio for the `k`-th bad event is at most `((9k)^6 n^2 / m^3)^k`. -/
theorem ratio_core {n m k : ℕ} (hm : 3 ≤ m) (hn : 2 * k ≤ n) :
    ((n.choose (2 * k) : ℝ) * (m.choose (3 * k) : ℝ) *
        (((3 * k).choose 3 : ℝ) ^ (2 * k) * (m.choose 3 : ℝ) ^ (n - 2 * k)))
        / ((m.choose 3 : ℝ) ^ n)
      ≤ ((9 * (k : ℝ)) ^ 6 * (n : ℝ) ^ 2 / (m : ℝ) ^ 3) ^ k := by
  classical
  have hpos : 0 < m.choose 3 := Nat.choose_pos (by omega)
  have hCm : (0 : ℝ) < (m.choose 3 : ℝ) := by exact_mod_cast hpos
  set Cm : ℝ := (m.choose 3 : ℝ)
  set Cn : ℝ := (n.choose (2 * k) : ℝ)
  set Cm3 : ℝ := (m.choose (3 * k) : ℝ)
  set C3 : ℝ := ((3 * k).choose 3 : ℝ)
  have hCmlb : (m : ℝ) ^ 3 ≤ 27 * Cm := pow_three_le_choose_three m hm
  have hCn : Cn ≤ (n : ℝ) ^ (2 * k) := by
    have h := Nat.choose_le_pow n (2 * k)
    simp only [Cn]; exact_mod_cast h
  have hCm3 : Cm3 ≤ (m : ℝ) ^ (3 * k) := by
    have h := Nat.choose_le_pow m (3 * k)
    simp only [Cm3]; exact_mod_cast h
  have hC3 : C3 ≤ (3 * (k : ℝ)) ^ 3 := by
    have h := Nat.choose_le_pow (3 * k) 3
    have hk' : ((3 * k : ℕ) : ℝ) = 3 * (k : ℝ) := by push_cast; ring
    simp only [C3]
    calc ((3 * k).choose 3 : ℝ) ≤ ((3 * k : ℕ) : ℝ) ^ 3 := by exact_mod_cast h
      _ = (3 * (k : ℝ)) ^ 3 := by rw [hk']
  have hN : (0 : ℝ) < Cm ^ n := pow_pos hCm n
  rw [div_le_iff₀ hN]
  have hexp : Cm ^ n = Cm ^ (2 * k) * Cm ^ (n - 2 * k) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hexp]
  have hkey : Cn * Cm3 * C3 ^ (2 * k)
      ≤ ((9 * (k : ℝ)) ^ 6 * (n : ℝ) ^ 2 / (m : ℝ) ^ 3) ^ k * Cm ^ (2 * k) := by
    have hCn3 : Cn * Cm3 ≤ (n : ℝ) ^ (2 * k) * (m : ℝ) ^ (3 * k) :=
      mul_le_mul hCn hCm3 (by positivity) (by positivity)
    have step1 : Cn * Cm3 * C3 ^ (2 * k)
        ≤ (n : ℝ) ^ (2 * k) * (m : ℝ) ^ (3 * k) * ((3 * (k : ℝ)) ^ 3) ^ (2 * k) :=
      mul_le_mul hCn3 (pow_le_pow_left₀ (by positivity) hC3 (2 * k)) (by positivity)
        (by positivity)
    have hpow2 : (n : ℝ) ^ (2 * k) = ((n : ℝ) ^ 2) ^ k := pow_mul (n : ℝ) 2 k
    have hpow3 : (m : ℝ) ^ (3 * k) = ((m : ℝ) ^ 3) ^ k := pow_mul (m : ℝ) 3 k
    have hpow6 : ((3 * (k : ℝ)) ^ 3) ^ (2 * k) = ((3 * (k : ℝ)) ^ 6) ^ k := by
      conv_lhs => rw [← pow_mul]
      rw [show 3 * (2 * k) = 6 * k by ring]
      rw [pow_mul]
    have step2 : (n : ℝ) ^ (2 * k) * (m : ℝ) ^ (3 * k) * ((3 * (k : ℝ)) ^ 3) ^ (2 * k)
        = ((n : ℝ) ^ 2 * (m : ℝ) ^ 3 * (3 * (k : ℝ)) ^ 6) ^ k := by
      rw [hpow2, hpow3, hpow6, ← mul_pow, ← mul_pow]
    have hm0 : (m : ℝ) ≠ 0 := by positivity
    have hbase : (n : ℝ) ^ 2 * (m : ℝ) ^ 3 * (3 * (k : ℝ)) ^ 6
        ≤ ((9 * (k : ℝ)) ^ 6 * (n : ℝ) ^ 2 / (m : ℝ) ^ 3) * Cm ^ 2 := by
      have h1' : (m : ℝ) ^ 3 / 27 ≤ Cm := by
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 27)]
        linarith
      have h1 : ((m : ℝ) ^ 3 / 27) ^ 2 ≤ Cm ^ 2 := pow_le_pow_left₀ (by positivity) h1' 2
      have h2 : (n : ℝ) ^ 2 * (m : ℝ) ^ 3 * (3 * (k : ℝ)) ^ 6
          = ((9 * (k : ℝ)) ^ 6 * (n : ℝ) ^ 2 / (m : ℝ) ^ 3) * ((m : ℝ) ^ 3 / 27) ^ 2 := by
        field_simp
        ring
      rw [h2]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have step4 : ((n : ℝ) ^ 2 * (m : ℝ) ^ 3 * (3 * (k : ℝ)) ^ 6) ^ k
        ≤ (((9 * (k : ℝ)) ^ 6 * (n : ℝ) ^ 2 / (m : ℝ) ^ 3) * Cm ^ 2) ^ k :=
      pow_le_pow_left₀ (by positivity) hbase k
    have step5 : (((9 * (k : ℝ)) ^ 6 * (n : ℝ) ^ 2 / (m : ℝ) ^ 3) * Cm ^ 2) ^ k
        = ((9 * (k : ℝ)) ^ 6 * (n : ℝ) ^ 2 / (m : ℝ) ^ 3) ^ k * Cm ^ (2 * k) := by
      rw [mul_pow, ← pow_mul]
    calc Cn * Cm3 * C3 ^ (2 * k)
        ≤ (n : ℝ) ^ (2 * k) * (m : ℝ) ^ (3 * k) * ((3 * (k : ℝ)) ^ 3) ^ (2 * k) := step1
      _ = ((n : ℝ) ^ 2 * (m : ℝ) ^ 3 * (3 * (k : ℝ)) ^ 6) ^ k := step2
      _ ≤ (((9 * (k : ℝ)) ^ 6 * (n : ℝ) ^ 2 / (m : ℝ) ^ 3) * Cm ^ 2) ^ k := step4
      _ = ((9 * (k : ℝ)) ^ 6 * (n : ℝ) ^ 2 / (m : ℝ) ^ 3) ^ k * Cm ^ (2 * k) := step5
  calc Cn * Cm3 * (C3 ^ (2 * k) * Cm ^ (n - 2 * k))
      = (Cn * Cm3 * C3 ^ (2 * k)) * Cm ^ (n - 2 * k) := by ring
    _ ≤ (((9 * (k : ℝ)) ^ 6 * (n : ℝ) ^ 2 / (m : ℝ) ^ 3) ^ k * Cm ^ (2 * k))
          * Cm ^ (n - 2 * k) := by
        exact mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = ((9 * (k : ℝ)) ^ 6 * (n : ℝ) ^ 2 / (m : ℝ) ^ 3) ^ k
          * (Cm ^ (2 * k) * Cm ^ (n - 2 * k)) := by ring

/-- The probability that a random matrix of `W3 n m` is bad for a given `k` is less than
`2^{-k}`. -/
theorem badSet_ratio_lt {n m k : ℕ} (hm : 3 ≤ m) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (hineq : 2 * (9 * k) ^ 6 * n ^ 2 < m ^ 3) :
    ((badSet n m k).card : ℝ) / ((m.choose 3 : ℝ) ^ n) < (1 / 2) ^ k := by
  classical
  have hpos : 0 < m.choose 3 := Nat.choose_pos (by omega)
  have hCm : (0 : ℝ) < (m.choose 3 : ℝ) := by exact_mod_cast hpos
  have hcard : ((badSet n m k).card : ℝ) ≤
      (n.choose (2 * k) : ℝ) * (m.choose (3 * k) : ℝ) *
        (((3 * k).choose 3 : ℝ) ^ (2 * k) * (m.choose 3 : ℝ) ^ (n - 2 * k)) := by
    have h := Nat.cast_le (α := ℝ).mpr (card_badSet_le n m k)
    simpa using h
  have hcore := ratio_core (n := n) (m := m) (k := k) hm hn
  have hlt : ((9 * (k : ℝ)) ^ 6 * (n : ℝ) ^ 2 / (m : ℝ) ^ 3) ^ k < (1 / 2) ^ k := by
    have hineq' : (2 : ℝ) * (9 * (k : ℝ)) ^ 6 * (n : ℝ) ^ 2 < (m : ℝ) ^ 3 := by
      exact_mod_cast hineq
    have hbase_lt : (9 * (k : ℝ)) ^ 6 * (n : ℝ) ^ 2 / (m : ℝ) ^ 3 < 1 / 2 := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) ^ 3)]
      linarith
    exact pow_lt_pow_left₀ hbase_lt (by positivity) (by omega : k ≠ 0)
  calc ((badSet n m k).card : ℝ) / ((m.choose 3 : ℝ) ^ n)
      ≤ ((n.choose (2 * k) : ℝ) * (m.choose (3 * k) : ℝ) *
          (((3 * k).choose 3 : ℝ) ^ (2 * k) * (m.choose 3 : ℝ) ^ (n - 2 * k)))
          / ((m.choose 3 : ℝ) ^ n) := by gcongr
    _ ≤ ((9 * (k : ℝ)) ^ 6 * (n : ℝ) ^ 2 / (m : ℝ) ^ 3) ^ k := hcore
    _ < (1 / 2) ^ k := hlt

/-- The geometric sum `2^{-1} + 2^{-2} + ⋯ + 2^{-s} = 1 - 2^{-s}`. -/
theorem sum_Icc_half (s : ℕ) :
    ∑ k ∈ Finset.Icc 1 s, ((1 / 2 : ℝ)) ^ k = 1 - (1 / 2 : ℝ) ^ s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, pow_succ]
    ring

/-- Union bound: if for every `k = 1,…,s` the bad event `E_k` has probability `< 2^{-k}`, then
some matrix of `W3 n m` avoids all of them. -/
theorem exists_good_matrix {n m s : ℕ} (hm : 3 ≤ m) (hs : 1 ≤ s) (hn : 2 * s ≤ n)
    (hineq : ∀ k, 1 ≤ k → k ≤ s → 2 * (9 * k) ^ 6 * n ^ 2 < m ^ 3) :
    ∃ A ∈ W3 n m, ∀ k, 1 ≤ k → k ≤ s →
      ∀ (I : Finset (Fin n)) (J : Finset (Fin m)),
        I.card = 2 * k → J.card = 3 * k → ¬ (∀ i ∈ I, A i ⊆ J) := by
  classical
  set N : ℝ := (m.choose 3 : ℝ) ^ n with hNdef
  have hpos : 0 < m.choose 3 := Nat.choose_pos (by omega)
  have hNpos : (0 : ℝ) < N := by rw [hNdef]; positivity
  set U := (Finset.Icc 1 s).biUnion (fun k => badSet n m k) with hUdef
  have h1 : (U.card : ℝ) ≤ ∑ k ∈ Finset.Icc 1 s, ((badSet n m k).card : ℝ) := by
    have h := Finset.card_biUnion_le (s := Finset.Icc 1 s) (t := fun k => badSet n m k)
    rw [hUdef]
    exact_mod_cast h
  have h2 : ∑ k ∈ Finset.Icc 1 s, ((badSet n m k).card : ℝ)
      < ∑ k ∈ Finset.Icc 1 s, (1 / 2 : ℝ) ^ k * N := by
    refine Finset.sum_lt_sum ?_ ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hs⟩, ?_⟩
    · intro k hk
      rw [Finset.mem_Icc] at hk
      obtain ⟨hk1, hks⟩ := hk
      have hr := badSet_ratio_lt hm hk1 (by omega : 2 * k ≤ n) (hineq k hk1 hks)
      rw [← hNdef] at hr
      exact le_of_lt ((div_lt_iff₀ hNpos).mp hr)
    · have hr := badSet_ratio_lt hm le_rfl (by omega : 2 * 1 ≤ n) (hineq 1 le_rfl hs)
      rw [← hNdef] at hr
      have := (div_lt_iff₀ hNpos).mp hr
      simpa using this
  have h3 : ∑ k ∈ Finset.Icc 1 s, (1 / 2 : ℝ) ^ k * N = N * (1 - (1 / 2 : ℝ) ^ s) := by
    rw [← Finset.sum_mul, sum_Icc_half]
    ring
  have h4 : N * (1 - (1 / 2 : ℝ) ^ s) < N := by
    have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ s := by positivity
    nlinarith
  have hlt : (U.card : ℝ) < ((W3 n m).card : ℝ) := by
    calc (U.card : ℝ) ≤ ∑ k ∈ Finset.Icc 1 s, ((badSet n m k).card : ℝ) := h1
      _ < ∑ k ∈ Finset.Icc 1 s, (1 / 2 : ℝ) ^ k * N := h2
      _ = N * (1 - (1 / 2 : ℝ) ^ s) := h3
      _ < N := h4
      _ = ((W3 n m).card : ℝ) := by rw [hNdef, card_W3]; push_cast; ring
  have hUlt : U.card < (W3 n m).card := by exact_mod_cast hlt
  obtain ⟨A, hAW, hAU⟩ := Finset.exists_mem_notMem_of_card_lt_card hUlt
  refine ⟨A, hAW, fun k hk1 hks I J hI hJ hsub => hAU ?_⟩
  rw [hUdef, Finset.mem_biUnion]
  refine ⟨k, Finset.mem_Icc.mpr ⟨hk1, hks⟩, ?_⟩
  unfold badSet
  rw [Finset.mem_biUnion]
  refine ⟨(I, J), ?_, ?_⟩
  · rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
    exact ⟨⟨Finset.subset_univ I, hI⟩, ⟨Finset.subset_univ J, hJ⟩⟩
  · rw [Finset.mem_filter]
    exact ⟨hAW, hsub⟩

/-! ### From a spread matrix to a matrix with large independence index -/

/-- The rows of a spread matrix are pairwise distinct. -/
theorem vecOf_injective_of_spread {n m s : ℕ} {A : Fin n → Finset (Fin m)}
    (hs : 1 ≤ s) (hcard3 : ∀ i, (A i).card = 3)
    (hspread : ∀ k, 1 ≤ k → k ≤ s → ∀ I : Finset (Fin n), I.card = 2 * k →
      ∀ J : Finset (Fin m), J.card = 3 * k → ¬ (∀ i ∈ I, A i ⊆ J)) :
    Function.Injective (fun i => vecOf (A i)) := by
  intro i j hij
  by_contra hne
  have hpair : ({i, j} : Finset (Fin n)).card = 2 * 1 := by
    simp [hne]
  have hsub : ∀ t ∈ ({i, j} : Finset (Fin n)), A t ⊆ A i := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Finset.Subset.refl _
    · rw [vecOf_injective hij]
  exact hspread 1 le_rfl hs ({i, j} : Finset (Fin n)) hpair (A i) (by rw [hcard3 i]) hsub

/-- A spread `3`-uniform matrix yields a matrix whose independence index is at least `2s`. -/
theorem ind_image_ge {n m s : ℕ} {A : Fin n → Finset (Fin m)}
    (hs : 1 ≤ s) (hcard3 : ∀ i, (A i).card = 3) (h3s : 3 * s ≤ m)
    (hspread : ∀ k, 1 ≤ k → k ≤ s → ∀ I : Finset (Fin n), I.card = 2 * k →
      ∀ J : Finset (Fin m), J.card = 3 * k → ¬ (∀ i ∈ I, A i ⊆ J))
    (hn : 2 * s ≤ n) :
    2 * s ≤ ind (Finset.univ.image (fun i => vecOf (A i))) := by
  classical
  have hinj : Function.Injective (fun i => vecOf (A i)) :=
    vecOf_injective_of_spread hs hcard3 hspread
  have hBcard : (Finset.univ.image (fun i => vecOf (A i))).card = n := by
    rw [Finset.card_image_of_injOn (fun x _ y _ h => hinj h), Finset.card_univ,
      Fintype.card_fin]
  refine le_ind ?_ (by rw [hBcard]; exact hn)
  intro S hS hScard
  rw [indep_iff_sum_ne_zero]
  intro T hTne hsum
  let idx : ↥S → Fin n := fun x => Classical.choose (Finset.mem_image.mp (hS x.2))
  have hidx : ∀ x : ↥S, vecOf (A (idx x)) = (x : Vec m) := fun x =>
    (Classical.choose_spec (Finset.mem_image.mp (hS x.2))).2
  let U : Finset (Fin n) := T.image idx
  have hUcard : U.card ≤ 2 * s := by
    calc U.card ≤ T.card := Finset.card_image_le
      _ ≤ Fintype.card ↥S := Finset.card_le_univ T
      _ = S.card := Fintype.card_coe S
      _ = 2 * s := hScard
  have hUne : U.Nonempty := hTne.image idx
  have hsumU : ∑ i ∈ U, vecOf (A i) = 0 := by
    have h1 : ∑ i ∈ U, vecOf (A i) = ∑ x ∈ T, vecOf (A (idx x)) := by
      refine Finset.sum_image ?_
      intro x _ y _ hxy
      exact Subtype.ext (by rw [← hidx x, ← hidx y, hxy])
    rw [h1, Finset.sum_congr rfl (fun x _ => hidx x)]
    exact hsum
  exact sum_ne_zero_of_spread A hcard3 h3s hspread hUne hUcard hsumU

/-! ### A chain of length `2n` computing the rows of a matrix of row weight `3` -/

/-- From a `3`-element finset, extract a triple of pairwise distinct elements. -/
theorem exists_triple {m : ℕ} {s : Finset (Fin m)} (h : s.card = 3) :
    ∃ t : Fin m × Fin m × Fin m, t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧
      s = {t.1, t.2.1, t.2.2} := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp h
  exact ⟨(x, y, z), hxy, hxz, hyz, rfl⟩

/-- The three columns in which the `i`-th row of `A` has a `1`, chosen arbitrarily. -/
noncomputable def rowTriple {n m : ℕ} (A : Fin n → Finset (Fin m))
    (hcard3 : ∀ i, (A i).card = 3) (i : Fin n) : Fin m × Fin m × Fin m :=
  Classical.choose (exists_triple (hcard3 i))

theorem rowTriple_spec {n m : ℕ} (A : Fin n → Finset (Fin m))
    (hcard3 : ∀ i, (A i).card = 3) (i : Fin n) :
    (rowTriple A hcard3 i).1 ≠ (rowTriple A hcard3 i).2.1 ∧
      (rowTriple A hcard3 i).1 ≠ (rowTriple A hcard3 i).2.2 ∧
      (rowTriple A hcard3 i).2.1 ≠ (rowTriple A hcard3 i).2.2 ∧
      A i = {(rowTriple A hcard3 i).1, (rowTriple A hcard3 i).2.1,
        (rowTriple A hcard3 i).2.2} :=
  Classical.choose_spec (exists_triple (hcard3 i))

/-- The characteristic vector of a triple of distinct columns is the sum of the three
corresponding basis vectors. -/
theorem vecOf_triple {m : ℕ} (t : Fin m × Fin m × Fin m)
    (h1 : t.1 ≠ t.2.1) (h2 : t.1 ≠ t.2.2) (h3 : t.2.1 ≠ t.2.2) :
    vecOf ({t.1, t.2.1, t.2.2} : Finset (Fin m)) =
      basisVec t.1 + basisVec t.2.1 + basisVec t.2.2 := by
  funext j
  simp only [vecOf_apply, Pi.add_apply, basisVec, Finset.mem_insert, Finset.mem_singleton]
  by_cases e1 : j = t.1
  · subst e1; simp [h1, h2]
  · by_cases e2 : j = t.2.1
    · subst e2; simp [e1, h3]
    · by_cases e3 : j = t.2.2
      · subst e3; simp [e1, e2]
      · simp [e1, e2, e3]

/-- The chain computing the rows of `A` in `2n` steps: the first `n` steps compute the sums
`e_a + e_b` of the first two `1`-columns of each row, the last `n` steps add the third one. -/
noncomputable def chainY {n m : ℕ} (A : Fin n → Finset (Fin m))
    (hcard3 : ∀ i, (A i).card = 3) (k : Fin (2 * n)) : Vec m :=
  if h : k.val < n then
    basisVec (rowTriple A hcard3 ⟨k.val, h⟩).1 + basisVec (rowTriple A hcard3 ⟨k.val, h⟩).2.1
  else
    basisVec (rowTriple A hcard3 ⟨k.val - n, by have := k.isLt; omega⟩).1 +
      basisVec (rowTriple A hcard3 ⟨k.val - n, by have := k.isLt; omega⟩).2.1 +
      basisVec (rowTriple A hcard3 ⟨k.val - n, by have := k.isLt; omega⟩).2.2

theorem chainY_first {n m : ℕ} (A : Fin n → Finset (Fin m))
    (hcard3 : ∀ i, (A i).card = 3) (k : Fin (2 * n)) (h : k.val < n) :
    chainY A hcard3 k =
      basisVec (rowTriple A hcard3 ⟨k.val, h⟩).1 +
        basisVec (rowTriple A hcard3 ⟨k.val, h⟩).2.1 := by
  rw [chainY, dite_eq_left h]

theorem chainY_second {n m : ℕ} (A : Fin n → Finset (Fin m))
    (hcard3 : ∀ i, (A i).card = 3) (k : Fin (2 * n)) (h : ¬ k.val < n) :
    chainY A hcard3 k =
      basisVec (rowTriple A hcard3 ⟨k.val - n, by have := k.isLt; omega⟩).1 +
        basisVec (rowTriple A hcard3 ⟨k.val - n, by have := k.isLt; omega⟩).2.1 +
        basisVec (rowTriple A hcard3 ⟨k.val - n, by have := k.isLt; omega⟩).2.2 := by
  rw [chainY, dite_eq_right h]

theorem chainY_valid {n m : ℕ} (A : Fin n → Finset (Fin m))
    (hcard3 : ∀ i, (A i).card = 3) (k : Fin (2 * n)) :
    ∃ a b : Fin m ⊕ Fin k.val,
      chainY A hcard3 k = chainPool (chainY A hcard3) k.val (le_of_lt k.isLt) a +
        chainPool (chainY A hcard3) k.val (le_of_lt k.isLt) b := by
  by_cases h : k.val < n
  · refine ⟨Sum.inl (rowTriple A hcard3 ⟨k.val, h⟩).1,
      Sum.inl (rowTriple A hcard3 ⟨k.val, h⟩).2.1, ?_⟩
    simp only [chainPool]
    rw [chainY_first A hcard3 k h]
  · have hlt : k.val - n < n := by have := k.isLt; omega
    have hsub : n + (k.val - n) = k.val := by have := k.isLt; omega
    refine ⟨Sum.inr ⟨k.val - n, by have := k.isLt; omega⟩,
      Sum.inl (rowTriple A hcard3 ⟨k.val - n, hlt⟩).2.2, ?_⟩
    simp only [chainPool]
    rw [chainY_second A hcard3 k h]
    rw [chainY_first A hcard3 ⟨k.val - n, by have := k.isLt; omega⟩ hlt]

theorem chainY_computes {n m : ℕ} (A : Fin n → Finset (Fin m))
    (hcard3 : ∀ i, (A i).card = 3) :
    (⟨2 * n, chainY A hcard3, chainY_valid A hcard3⟩ : VecAddChain m).ComputesSet
      (Finset.univ.image (fun i => vecOf (A i))) := by
  intro b hb
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨h1, h2, h3, hA⟩ := rowTriple_spec A hcard3 i
  have hidx : n + i.val < 2 * n := by have := i.isLt; omega
  have hni : ¬ n + i.val < n := by omega
  refine Or.inl (Or.inr ⟨⟨n + i.val, hidx⟩, ?_⟩)
  change chainY A hcard3 ⟨n + i.val, hidx⟩ = vecOf (A i)
  rw [chainY_second A hcard3 ⟨n + i.val, hidx⟩ hni]
  have hsub : n + i.val - n = i.val := Nat.add_sub_cancel_left n i.val
  simp only [hsub]
  rw [hA, vecOf_triple _ h1 h2 h3]

/-- Every matrix whose rows have weight `3` is computed by a chain of length `2n`. -/
theorem vecComplexity_image_le {n m : ℕ} (A : Fin n → Finset (Fin m))
    (hcard3 : ∀ i, (A i).card = 3) :
    vecComplexity (Finset.univ.image (fun i => vecOf (A i))) ≤ 2 * n :=
  vecComplexity_le (chainY_computes A hcard3)

/-! ### The numeric parameters and the final theorem -/

/-- The number `m = ⌈n^{8/9}⌉` of columns. -/
noncomputable def thmM (n : ℕ) : ℕ := Nat.ceil ((n : ℝ) ^ ((8 : ℝ) / 9))

/-- The number `s = ⌊n^{1/9}/18⌋` of levels in the union bound. -/
noncomputable def thmS (n : ℕ) : ℕ := ⌊(n : ℝ) ^ ((1 : ℝ) / 9) / 18⌋₊

/-- All the numeric hypotheses of the construction hold for `n ≥ 36^9`. -/
theorem numeric_facts :
    ∃ N₀ : ℕ, ∀ n ≥ N₀,
      3 ≤ thmM n ∧ 1 ≤ thmS n ∧ 2 * thmS n ≤ n ∧ 3 * thmS n ≤ thmM n ∧
      (∀ k, 1 ≤ k → k ≤ thmS n → 2 * (9 * k) ^ 6 * n ^ 2 < (thmM n) ^ 3) ∧
      (n : ℝ) ^ ((1 : ℝ) / 9) / 40 ≤ (2 * thmS n : ℝ) := by
  refine ⟨36 ^ 9, fun n hn => ?_⟩
  have ht9' : (((n : ℝ)) ^ ((1 : ℝ) / 9)) ^ 9 = (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have ht8' : (n : ℝ) ^ ((8 : ℝ) / 9) = (((n : ℝ)) ^ ((1 : ℝ) / 9)) ^ 8 := by
    rw [show (8 : ℝ) / 9 = (1 : ℝ) / 9 * 8 by norm_num, Real.rpow_mul (by positivity)]
    exact Real.rpow_natCast _ 8
  set t : ℝ := (n : ℝ) ^ ((1 : ℝ) / 9) with htdef
  have ht9 : t ^ 9 = (n : ℝ) := ht9'
  have ht8 : (n : ℝ) ^ ((8 : ℝ) / 9) = t ^ 8 := ht8'
  have ht0 : (0 : ℝ) < t := by rw [htdef]; positivity
  have ht36 : (36 : ℝ) ≤ t := by
    have h36 : ((36 : ℝ)) ^ 9 ≤ t ^ 9 := by
      rw [ht9]
      have hcast : ((36 ^ 9 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have : ((36 : ℝ)) ^ 9 = ((36 ^ 9 : ℕ) : ℝ) := by norm_num
      linarith
    exact (pow_le_pow_iff_left₀ (by norm_num) (le_of_lt ht0) (by norm_num)).mp h36
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hs_le : (thmS n : ℝ) ≤ t / 18 := Nat.floor_le (by positivity)
  have hs_gt : t / 18 < (thmS n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hs_gt1 : (1 : ℝ) < (thmS n : ℝ) := by linarith
  have hceil : t ^ 8 ≤ (thmM n : ℝ) := by
    rw [thmM, ← ht8]; exact Nat.le_ceil _
  have ht_le_9 : t ≤ t ^ 9 := by simpa using pow_le_pow_right₀ (m := 1) (n := 9) ht1 (by norm_num)
  have ht_le_8 : t ≤ t ^ 8 := by simpa using pow_le_pow_right₀ (m := 1) (n := 8) ht1 (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (3 : ℝ) ≤ (thmM n : ℝ) := by
      have h : ((36 : ℝ)) ^ 8 ≤ t ^ 8 := pow_le_pow_left₀ (by norm_num) ht36 8
      nlinarith
    exact_mod_cast this
  · have h : (1 : ℕ) < thmS n := by exact_mod_cast hs_gt1
    omega
  · have hc : (2 * thmS n : ℝ) ≤ (n : ℝ) := by
      have h1 : (2 : ℝ) * (thmS n : ℝ) ≤ 2 * (t / 18) := by linarith
      linarith
    exact_mod_cast hc
  · have hc : (3 * thmS n : ℝ) ≤ (thmM n : ℝ) := by
      have h1 : (3 : ℝ) * (thmS n : ℝ) ≤ 3 * (t / 18) := by linarith
      linarith
    exact_mod_cast hc
  · intro k hk1 hks
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    have hksR : (k : ℝ) ≤ (thmS n : ℝ) := by exact_mod_cast hks
    have h9k : 9 * (k : ℝ) ≤ t / 2 := by linarith
    have h6 : (9 * (k : ℝ)) ^ 6 ≤ (t / 2) ^ 6 := pow_le_pow_left₀ (by positivity) h9k 6
    have hn2 : (n : ℝ) ^ 2 = t ^ 18 := by rw [← ht9]; ring
    have hm3 : (t ^ 8) ^ 3 ≤ ((thmM n : ℕ) : ℝ) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hceil 3
    have hreal : (2 * (9 * (k : ℝ)) ^ 6 * (n : ℝ) ^ 2) < ((thmM n : ℕ) : ℝ) ^ 3 := by
      rw [hn2]
      have hstep : 2 * (9 * (k : ℝ)) ^ 6 * t ^ 18 ≤ 2 * (t / 2) ^ 6 * t ^ 18 := by
        have h2 : (0 : ℝ) ≤ 2 := by norm_num
        have hA : 2 * (9 * (k : ℝ)) ^ 6 ≤ 2 * (t / 2) ^ 6 :=
          mul_le_mul_of_nonneg_left h6 h2
        exact mul_le_mul_of_nonneg_right hA (by positivity)
      have hval : 2 * (t / 2) ^ 6 * t ^ 18 = t ^ 24 / 32 := by ring
      have hlt : t ^ 24 / 32 < t ^ 24 := by
        have : (0 : ℝ) < t ^ 24 := by positivity
        linarith
      have h24 : t ^ 24 = (t ^ 8) ^ 3 := by ring
      calc 2 * (9 * (k : ℝ)) ^ 6 * t ^ 18 ≤ 2 * (t / 2) ^ 6 * t ^ 18 := hstep
        _ = t ^ 24 / 32 := hval
        _ < t ^ 24 := hlt
        _ = (t ^ 8) ^ 3 := h24
        _ ≤ ((thmM n : ℕ) : ℝ) ^ 3 := hm3
    have hcast : ((2 * (9 * k) ^ 6 * n ^ 2 : ℕ) : ℝ) < (((thmM n) ^ 3 : ℕ) : ℝ) := by
      push_cast
      exact hreal
    exact_mod_cast hcast
  · linarith

/-- **Theorem 3.** For all sufficiently large `n`, with `m = ⌈n^{8/9}⌉` there is a matrix
`B ∈ GF(2)^{n × m}`, encoded as the finset of its `n` row vectors of weight `3`, whose
independence index satisfies `ind B ≥ n^{1/9}/40` and whose additive complexity satisfies
`L B ≤ 2n`.  (The proof gives the explicit threshold `N₀ = 36^9`.) -/
theorem theorem3 :
    ∃ N₀ : ℕ, ∀ n ≥ N₀, ∃ B : Finset (Vec (thmM n)),
      B.card = n ∧
      (∀ b ∈ B, weight (Finset.univ : Finset (Fin (thmM n))) b = 3) ∧
      (n : ℝ) ^ ((1 : ℝ) / 9) / 40 ≤ (ind B : ℝ) ∧
      vecComplexity B ≤ 2 * n := by
  obtain ⟨N₀, hN⟩ := numeric_facts
  refine ⟨N₀, fun n hn => ?_⟩
  obtain ⟨h3m, hs1, h2s, h3s, hineq, hind⟩ := hN n hn
  obtain ⟨A, hAW, hspread⟩ := exists_good_matrix h3m hs1 h2s hineq
  have hcard3 : ∀ i, (A i).card = 3 := fun i => (mem_W3.mp hAW) i
  have hspread' : ∀ k, 1 ≤ k → k ≤ thmS n → ∀ I : Finset (Fin n), I.card = 2 * k →
      ∀ J : Finset (Fin (thmM n)), J.card = 3 * k → ¬ (∀ i ∈ I, A i ⊆ J) :=
    fun k hk1 hks I hI J hJ => hspread k hk1 hks I J hI hJ
  have hinj : Function.Injective (fun i => vecOf (A i)) :=
    vecOf_injective_of_spread hs1 hcard3 hspread'
  refine ⟨Finset.univ.image (fun i => vecOf (A i)), ?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn (fun x _ y _ h => hinj h), Finset.card_univ,
      Fintype.card_fin]
  · intro b hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
    rw [weight_univ_vecOf, hcard3 i]
  · have h := ind_image_ge hs1 hcard3 h3s hspread' h2s
    have h' : (2 * thmS n : ℝ) ≤ (ind (Finset.univ.image (fun i => vecOf (A i))) : ℝ) := by
      exact_mod_cast h
    linarith
  · exact vecComplexity_image_le A hcard3
