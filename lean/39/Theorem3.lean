module

public import Mathlib
public import Preliminaries

@[expose] public section

/-!
# Theorem 3: the lower bound `chi*_3 >= 0.769`

This file formalizes Theorem 3 of I. S. Sergeev, *Formula complexity of a
linear function in a k-ary basis*, Mathematical Notes 109 (2021), 445--458:
`chi*_3 >= 0.769`, i.e. `IsMonotoneGraphExponent 3 (769 / 1000)`.

The paper proves the statement by induction over the three graphs of a
monotone cover.  The first case, in which one part of the graph is contained in
one of the cover graphs, relies on the two-graph subadditivity statement
(Proposition 3): `s(G) <= s(G_1) + s(G_2)`.  That statement, together with the
graph restriction helpers it needs, is developed below in the namespace
`UnateLin.T3`, so that this file only depends on `Preliminaries` and Mathlib.
-/

namespace UnateLin

namespace T3
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

theorem edgeCount_graphOn_self' (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B) :
    (graphOn G.edge X Y).edgeCount X Y = G.edgeCount X Y := by
  classical
  unfold BipartiteGraph.edgeCount graphOn
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro q hq
  have hq' : q.1 ∈ X ∧ q.2 ∈ Y := Finset.mem_product.mp hq
  simp [hq'.1, hq'.2]


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

theorem card_sdiff_eq {α : Type*} [DecidableEq α] {s t : Finset α} (h : s ⊆ t) :
    (t \ s).card = t.card - s.card := by
  rw [Finset.card_sdiff]
  have : s ∩ t = s := Finset.inter_eq_left.mpr h
  rw [this]

@[simp] theorem iUnion_fin_two_sets {α : Type*} (f : Fin 2 → Set α) :
    (⋃ i, f i) = f 0 ∪ f 1 := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp_all
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩

theorem edge_eq_of_edgeRestriction {G H : BipartiteGraph A B} (h : EdgeRestriction G H)
    {a : A} {b : B} (ha : a ∈ H.left) (hb : b ∈ H.right) :
    H.edge a b = G.edge a b := by
  by_cases hg : G.edge a b = true
  · have hh : H.edge a b = true := (h a b).mpr ⟨hg, ha, hb⟩
    simp [hg, hh]
  · have hh : H.edge a b = false := by
      by_contra hne
      have htrue : H.edge a b = true := by simpa using hne
      exact hg ((h a b).mp htrue).1
    simp [hg, hh]

theorem edgeCount_congr_on {H K : BipartiteGraph A B} (X : Finset A) (Y : Finset B)
    (h : ∀ a ∈ X, ∀ b ∈ Y, H.edge a b = K.edge a b) :
    H.edgeCount X Y = K.edgeCount X Y := by
  classical
  unfold BipartiteGraph.edgeCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro q hq
  obtain ⟨hqX, hqY⟩ := Finset.mem_product.mp hq
  rw [h q.1 hqX q.2 hqY]

theorem edgeCount_split_right (G : BipartiteGraph A B) (X : Finset A) (Y B1 : Finset B)
    (hB1 : B1 ⊆ Y) :
    G.edgeCount X Y = G.edgeCount X B1 + G.edgeCount X (Y \ B1) := by
  classical
  unfold BipartiteGraph.edgeCount
  let p : A × B → Prop := fun q => G.edge q.1 q.2 = true
  let s1 : Finset (A × B) := (X.product B1).filter p
  let s2 : Finset (A × B) := (X.product (Y \ B1)).filter p
  have hdisj : Disjoint s1 s2 := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    simp only [s1, s2, Finset.mem_filter] at hq1 hq2
    have hq2Y : q.2 ∈ Y \ B1 := (Finset.mem_product.mp hq2.1).2
    rw [Finset.mem_sdiff] at hq2Y
    exact hq2Y.2 ((Finset.mem_product.mp hq1.1).2)
  have hunion : (X.product Y).filter p = s1 ∪ s2 := by
    ext q
    simp only [s1, s2, p, Finset.mem_filter, Finset.mem_union, Finset.mem_product,
      Finset.mem_sdiff, Finset.product_eq_sprod]
    constructor
    · rintro ⟨⟨ha, hY⟩, he⟩
      by_cases hb : q.2 ∈ B1
      · exact Or.inl ⟨⟨ha, hb⟩, he⟩
      · exact Or.inr ⟨⟨ha, hY, hb⟩, he⟩
    · rintro (⟨⟨ha, hb⟩, he⟩ | ⟨⟨ha, hY, hb⟩, he⟩)
      · exact ⟨⟨ha, hB1 hb⟩, he⟩
      · exact ⟨⟨ha, hY⟩, he⟩
  rw [hunion, Finset.card_union_of_disjoint hdisj]

theorem sq_add_sq_div {x1 x2 y1 y2 : ℝ} (hy1 : 0 < y1) (hy2 : 0 < y2) :
    (x1 + x2) ^ 2 / (y1 + y2) ≤ x1 ^ 2 / y1 + x2 ^ 2 / y2 := by
  have h := Finset.sq_sum_div_le_sum_sq_div (s := (Finset.univ : Finset (Fin 2)))
    (f := ![x1, x2]) (g := ![y1, y2]) (by
      intro i _
      fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using h

theorem twoGraph_row
    (G H1 H2 : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (hL1 : G.left ⊆ H1.left) (hL2 : G.left ⊆ H2.left)
    (hYR : G.right ⊆ H1.right ∪ H2.right)
    (hER1 : EdgeRestriction G H1) (hER2 : EdgeRestriction G H2)
    (hGleft : G.left = (↑X : Set A)) (hGright : G.right = (↑Y : Set B)) :
    G.ratio X Y ≤ H1.sGraph + H2.sGraph := by
  classical
  have hAdm : G.Admissible X Y := by
    refine ⟨?_, ?_⟩
    · intro a ha; rw [hGleft]; exact ha
    · intro b hb; rw [hGright]; exact hb
  by_cases hEzero : G.edgeCount X Y = 0
  · rw [ratio_of_admissible G hAdm, hEzero]
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div]
    exact add_nonneg (BipartiteGraph.sGraph_nonneg H1) (BipartiteGraph.sGraph_nonneg H2)
  · have hEpos : 0 < G.edgeCount X Y := Nat.pos_of_ne_zero hEzero
    rw [ratio_of_admissible G hAdm]
    set B1 : Finset B := partRight Y H1.right with hB1def
    have hB1sub : B1 ⊆ Y := fun b hb => (mem_partRight.mp hb).1
    have hYsub : Y ⊆ B1 ∪ partRight Y H2.right := by
      intro b hb
      have hbG : b ∈ G.right := by rw [hGright]; exact hb
      rcases hYR hbG with h | h
      · exact Finset.mem_union.mpr (Or.inl (mem_partRight.mpr ⟨hb, h⟩))
      · exact Finset.mem_union.mpr (Or.inr (mem_partRight.mpr ⟨hb, h⟩))
    have hdiff : Y \ B1 ⊆ partRight Y H2.right := by
      intro b hb
      rw [Finset.mem_sdiff] at hb
      rcases Finset.mem_union.mp (hYsub hb.1) with h | h
      · exact absurd h hb.2
      · exact h
    let a : ℝ := (X.card : ℝ)
    let b : ℝ := (Y.card : ℝ)
    let b1 : ℝ := (B1.card : ℝ)
    let x1 : ℝ := (G.edgeCount X B1 : ℝ)
    let x2 : ℝ := (G.edgeCount X (Y \ B1) : ℝ)
    have hsplit : G.edgeCount X Y = G.edgeCount X B1 + G.edgeCount X (Y \ B1) :=
      edgeCount_split_right G X Y B1 hB1sub
    have hE : (G.edgeCount X Y : ℝ) = x1 + x2 := by
      rw [hsplit]
      simp only [Nat.cast_add]
      rfl
    have hx1 : x1 ^ 2 / (a * b1) ≤ H1.sGraph := by
      have hAdm1 : H1.Admissible X B1 := by
        refine ⟨?_, ?_⟩
        · intro a' ha'
          exact hL1 (by rw [hGleft]; exact ha')
        · intro b' hb'
          exact (mem_partRight.mp hb').2
      have hcount : H1.edgeCount X B1 = G.edgeCount X B1 := by
        apply edgeCount_congr_on
        intro a' ha' b' hb'
        exact edge_eq_of_edgeRestriction hER1
          (hL1 (by rw [hGleft]; exact ha')) (mem_partRight.mp hb').2
      have h := sGraph_ge_full H1 X B1 hAdm1
      rw [hcount] at h
      simpa [a, b1, x1] using h
    have hx2 : x2 ^ 2 / (a * (b - b1)) ≤ H2.sGraph := by
      have hAdm2 : H2.Admissible X (Y \ B1) := by
        refine ⟨?_, ?_⟩
        · intro a' ha'
          exact hL2 (by rw [hGleft]; exact ha')
        · intro b' hb'
          exact (mem_partRight.mp (hdiff hb')).2
      have hcount : H2.edgeCount X (Y \ B1) = G.edgeCount X (Y \ B1) := by
        apply edgeCount_congr_on
        intro a' ha' b' hb'
        exact edge_eq_of_edgeRestriction hER2
          (hL2 (by rw [hGleft]; exact ha')) (mem_partRight.mp (hdiff hb')).2
      have h := sGraph_ge_full H2 X (Y \ B1) hAdm2
      rw [hcount] at h
      have hle : B1.card ≤ Y.card := Finset.card_le_card hB1sub
      have hcard : (((Y \ B1).card : ℕ) : ℝ) = b - b1 := by
        rw [card_sdiff_eq hB1sub, Nat.cast_sub hle]
      rw [hcard] at h
      simpa [a, x2] using h
    have ha : 0 < a := by
      obtain ⟨q, hq⟩ := Finset.card_pos.mp hEpos
      change q ∈ (X.product Y).filter (fun q => G.edge q.1 q.2 = true) at hq
      rw [Finset.mem_filter] at hq
      have hqX : q.1 ∈ X := (Finset.mem_product.mp hq.1).1
      have hXpos : 0 < X.card := Finset.card_pos.mpr ⟨q.1, hqX⟩
      simp only [a]
      exact_mod_cast hXpos
    have hb : 0 < b := by
      obtain ⟨q, hq⟩ := Finset.card_pos.mp hEpos
      change q ∈ (X.product Y).filter (fun q => G.edge q.1 q.2 = true) at hq
      rw [Finset.mem_filter] at hq
      have hqY : q.2 ∈ Y := (Finset.mem_product.mp hq.1).2
      have hYpos : 0 < Y.card := Finset.card_pos.mpr ⟨q.2, hqY⟩
      simp only [b]
      exact_mod_cast hYpos
    have hb1le : b1 ≤ b := by
      simp only [b1, b]
      exact_mod_cast Finset.card_le_card hB1sub
    have hb1nonneg : 0 ≤ b1 := by positivity
    by_cases hb1zero : b1 = 0
    · have hzero : x1 = 0 := by
        have hB1card : B1.card = 0 := by
          have hz : (B1.card : ℝ) = 0 := by simpa [b1] using hb1zero
          exact_mod_cast hz
        have hB1empty : B1 = ∅ := Finset.card_eq_zero.mp hB1card
        simp [x1, hB1empty, BipartiteGraph.edgeCount]
      have hrem : b - b1 = b := by rw [hb1zero, sub_zero]
      calc
        (G.edgeCount X Y : ℝ) ^ 2 / (a * b) = x2 ^ 2 / (a * b) := by
          rw [hE, hzero, zero_add]
        _ = x2 ^ 2 / (a * (b - b1)) := by rw [hrem]
        _ ≤ H2.sGraph := hx2
        _ ≤ H1.sGraph + H2.sGraph := by linarith [BipartiteGraph.sGraph_nonneg H1]
    · by_cases hb1eq : b1 = b
      · have hzero : x2 = 0 := by
          have hdiff_empty : Y \ B1 = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro b' hb'
            rw [Finset.mem_sdiff] at hb'
            have hcard : (Y \ B1).card = 0 := by
              rw [card_sdiff_eq hB1sub]
              have hnat : B1.card = Y.card := by
                have hz : (B1.card : ℝ) = (Y.card : ℝ) := by simpa [b1, b] using hb1eq
                exact_mod_cast hz
              omega
            have hpos : 0 < (Y \ B1).card := Finset.card_pos.mpr ⟨b', Finset.mem_sdiff.mpr hb'⟩
            omega
          simp [x2, hdiff_empty, BipartiteGraph.edgeCount]
        have hrem : b - b1 = 0 := by rw [hb1eq, sub_self]
        calc
          (G.edgeCount X Y : ℝ) ^ 2 / (a * b) = x1 ^ 2 / (a * b) := by
            rw [hE, hzero, add_zero]
          _ = x1 ^ 2 / (a * b1) := by rw [← hb1eq]
          _ ≤ H1.sGraph := hx1
          _ ≤ H1.sGraph + H2.sGraph := by linarith [BipartiteGraph.sGraph_nonneg H2]
      · have hb1pos : 0 < b1 := lt_of_le_of_ne hb1nonneg (Ne.symm hb1zero)
        have hb1lt : b1 < b := lt_of_le_of_ne hb1le hb1eq
        have hy1 : 0 < a * b1 := mul_pos ha hb1pos
        have hy2 : 0 < a * (b - b1) := mul_pos ha (sub_pos.mpr hb1lt)
        have htitu := sq_add_sq_div (x1 := x1) (x2 := x2) (y1 := a * b1) (y2 := a * (b - b1)) hy1 hy2
        have hy : a * b1 + a * (b - b1) = a * b := by ring
        calc
          (G.edgeCount X Y : ℝ) ^ 2 / (a * b) = (x1 + x2) ^ 2 / (a * b) := by rw [hE]
          _ = (x1 + x2) ^ 2 / (a * b1 + a * (b - b1)) := by rw [hy]
          _ ≤ x1 ^ 2 / (a * b1) + x2 ^ 2 / (a * (b - b1)) := htitu
          _ ≤ H1.sGraph + H2.sGraph := add_le_add hx1 hx2


theorem edgeCount_split_left (G : BipartiteGraph A B) (X A1 : Finset A) (Y : Finset B)
    (hA1 : A1 ⊆ X) :
    G.edgeCount X Y = G.edgeCount A1 Y + G.edgeCount (X \ A1) Y := by
  classical
  unfold BipartiteGraph.edgeCount
  let p : A × B → Prop := fun q => G.edge q.1 q.2 = true
  let s1 : Finset (A × B) := (A1.product Y).filter p
  let s2 : Finset (A × B) := ((X \ A1).product Y).filter p
  have hdisj : Disjoint s1 s2 := by
    rw [Finset.disjoint_left]
    intro q hq1 hq2
    simp only [s1, s2, Finset.mem_filter] at hq1 hq2
    have hq2X : q.1 ∈ X \ A1 := (Finset.mem_product.mp hq2.1).1
    rw [Finset.mem_sdiff] at hq2X
    exact hq2X.2 ((Finset.mem_product.mp hq1.1).1)
  have hunion : (X.product Y).filter p = s1 ∪ s2 := by
    ext q
    simp only [s1, s2, p, Finset.mem_filter, Finset.mem_union, Finset.product_eq_sprod,
      Finset.mem_product, Finset.mem_sdiff]
    constructor
    · rintro ⟨⟨hX, hY⟩, he⟩
      by_cases ha : q.1 ∈ A1
      · exact Or.inl (And.intro (And.intro ha hY) he)
      · exact Or.inr (And.intro (And.intro (And.intro hX ha) hY) he)
    · rintro (⟨⟨ha, hY⟩, he⟩ | ⟨⟨⟨hX, ha⟩, hY⟩, he⟩)
      · exact And.intro (And.intro (hA1 ha) hY) he
      · exact And.intro (And.intro hX hY) he
  rw [hunion, Finset.card_union_of_disjoint hdisj]

theorem twoGraph_col
    (G H1 H2 : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (hR1 : G.right ⊆ H1.right) (hR2 : G.right ⊆ H2.right)
    (hXL : G.left ⊆ H1.left ∪ H2.left)
    (hER1 : EdgeRestriction G H1) (hER2 : EdgeRestriction G H2)
    (hGleft : G.left = (↑X : Set A)) (hGright : G.right = (↑Y : Set B)) :
    G.ratio X Y ≤ H1.sGraph + H2.sGraph := by
  classical
  have hAdm : G.Admissible X Y := by
    refine ⟨?_, ?_⟩
    · intro a ha; rw [hGleft]; exact ha
    · intro b hb; rw [hGright]; exact hb
  by_cases hEzero : G.edgeCount X Y = 0
  · rw [ratio_of_admissible G hAdm, hEzero]
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div]
    exact add_nonneg (BipartiteGraph.sGraph_nonneg H1) (BipartiteGraph.sGraph_nonneg H2)
  · have hEpos : 0 < G.edgeCount X Y := Nat.pos_of_ne_zero hEzero
    rw [ratio_of_admissible G hAdm]
    set A1 : Finset A := partLeft X H1.left with hA1def
    have hA1sub : A1 ⊆ X := fun a ha => (mem_partLeft.mp ha).1
    have hXsub : X ⊆ A1 ∪ partLeft X H2.left := by
      intro a ha
      have haG : a ∈ G.left := by rw [hGleft]; exact ha
      rcases hXL haG with h | h
      · exact Finset.mem_union.mpr (Or.inl (mem_partLeft.mpr ⟨ha, h⟩))
      · exact Finset.mem_union.mpr (Or.inr (mem_partLeft.mpr ⟨ha, h⟩))
    have hdiff : X \ A1 ⊆ partLeft X H2.left := by
      intro a ha
      rw [Finset.mem_sdiff] at ha
      rcases Finset.mem_union.mp (hXsub ha.1) with h | h
      · exact absurd h ha.2
      · exact h
    let a : ℝ := (X.card : ℝ)
    let b : ℝ := (Y.card : ℝ)
    let a1 : ℝ := (A1.card : ℝ)
    let x1 : ℝ := (G.edgeCount A1 Y : ℝ)
    let x2 : ℝ := (G.edgeCount (X \ A1) Y : ℝ)
    have hsplit : G.edgeCount X Y = G.edgeCount A1 Y + G.edgeCount (X \ A1) Y :=
      edgeCount_split_left G X A1 Y hA1sub
    have hE : (G.edgeCount X Y : ℝ) = x1 + x2 := by
      rw [hsplit]
      simp only [Nat.cast_add]
      rfl
    have hx1 : x1 ^ 2 / (a1 * b) ≤ H1.sGraph := by
      have hAdm1 : H1.Admissible A1 Y := by
        refine ⟨?_, ?_⟩
        · intro a' ha'
          exact (mem_partLeft.mp ha').2
        · intro b' hb'
          exact hR1 (by rw [hGright]; exact hb')
      have hcount : H1.edgeCount A1 Y = G.edgeCount A1 Y := by
        apply edgeCount_congr_on
        intro a' ha' b' hb'
        exact edge_eq_of_edgeRestriction hER1
          (mem_partLeft.mp ha').2 (hR1 (by rw [hGright]; exact hb'))
      have h := sGraph_ge_full H1 A1 Y hAdm1
      rw [hcount] at h
      simpa [a1, b, x1] using h
    have hx2 : x2 ^ 2 / ((a - a1) * b) ≤ H2.sGraph := by
      have hAdm2 : H2.Admissible (X \ A1) Y := by
        refine ⟨?_, ?_⟩
        · intro a' ha'
          exact (mem_partLeft.mp (hdiff ha')).2
        · intro b' hb'
          exact hR2 (by rw [hGright]; exact hb')
      have hcount : H2.edgeCount (X \ A1) Y = G.edgeCount (X \ A1) Y := by
        apply edgeCount_congr_on
        intro a' ha' b' hb'
        exact edge_eq_of_edgeRestriction hER2
          (mem_partLeft.mp (hdiff ha')).2 (hR2 (by rw [hGright]; exact hb'))
      have h := sGraph_ge_full H2 (X \ A1) Y hAdm2
      rw [hcount] at h
      have hle : A1.card ≤ X.card := Finset.card_le_card hA1sub
      have hcard : (((X \ A1).card : ℕ) : ℝ) = a - a1 := by
        rw [card_sdiff_eq hA1sub, Nat.cast_sub hle]
      rw [hcard] at h
      simpa [a, x2] using h
    have ha : 0 < a := by
      obtain ⟨q, hq⟩ := Finset.card_pos.mp hEpos
      change q ∈ (X.product Y).filter (fun q => G.edge q.1 q.2 = true) at hq
      rw [Finset.mem_filter] at hq
      have hqX : q.1 ∈ X := (Finset.mem_product.mp hq.1).1
      have hXpos : 0 < X.card := Finset.card_pos.mpr ⟨q.1, hqX⟩
      simp only [a]
      exact_mod_cast hXpos
    have hb : 0 < b := by
      obtain ⟨q, hq⟩ := Finset.card_pos.mp hEpos
      change q ∈ (X.product Y).filter (fun q => G.edge q.1 q.2 = true) at hq
      rw [Finset.mem_filter] at hq
      have hqY : q.2 ∈ Y := (Finset.mem_product.mp hq.1).2
      have hYpos : 0 < Y.card := Finset.card_pos.mpr ⟨q.2, hqY⟩
      simp only [b]
      exact_mod_cast hYpos
    have ha1le : a1 ≤ a := by
      simp only [a1, a]
      exact_mod_cast Finset.card_le_card hA1sub
    have ha1nonneg : 0 ≤ a1 := by positivity
    by_cases ha1zero : a1 = 0
    · have hzero : x1 = 0 := by
        have hA1card : A1.card = 0 := by
          have hz : (A1.card : ℝ) = 0 := by simpa [a1] using ha1zero
          exact_mod_cast hz
        have hA1empty : A1 = ∅ := Finset.card_eq_zero.mp hA1card
        simp [x1, hA1empty, BipartiteGraph.edgeCount]
      have hrem : a - a1 = a := by rw [ha1zero, sub_zero]
      calc
        (G.edgeCount X Y : ℝ) ^ 2 / (a * b) = x2 ^ 2 / (a * b) := by
          rw [hE, hzero, zero_add]
        _ = x2 ^ 2 / ((a - a1) * b) := by rw [hrem]
        _ ≤ H2.sGraph := hx2
        _ ≤ H1.sGraph + H2.sGraph := by linarith [BipartiteGraph.sGraph_nonneg H1]
    · by_cases ha1eq : a1 = a
      · have hzero : x2 = 0 := by
          have hdiff_empty : X \ A1 = ∅ := by
            apply Finset.eq_empty_iff_forall_notMem.mpr
            intro a' ha'
            rw [Finset.mem_sdiff] at ha'
            have hcard : (X \ A1).card = 0 := by
              rw [card_sdiff_eq hA1sub]
              have hnat : A1.card = X.card := by
                have hz : (A1.card : ℝ) = (X.card : ℝ) := by simpa [a1, a] using ha1eq
                exact_mod_cast hz
              omega
            have hpos : 0 < (X \ A1).card := Finset.card_pos.mpr ⟨a', Finset.mem_sdiff.mpr ha'⟩
            omega
          simp [x2, hdiff_empty, BipartiteGraph.edgeCount]
        have hrem : a - a1 = 0 := by rw [ha1eq, sub_self]
        calc
          (G.edgeCount X Y : ℝ) ^ 2 / (a * b) = x1 ^ 2 / (a * b) := by
            rw [hE, hzero, add_zero]
          _ = x1 ^ 2 / (a1 * b) := by rw [← ha1eq]
          _ ≤ H1.sGraph := hx1
          _ ≤ H1.sGraph + H2.sGraph := by linarith [BipartiteGraph.sGraph_nonneg H2]
      · have ha1pos : 0 < a1 := lt_of_le_of_ne ha1nonneg (Ne.symm ha1zero)
        have ha1lt : a1 < a := lt_of_le_of_ne ha1le ha1eq
        have hy1 : 0 < a1 * b := mul_pos ha1pos hb
        have hy2 : 0 < (a - a1) * b := mul_pos (sub_pos.mpr ha1lt) hb
        have htitu := sq_add_sq_div (x1 := x1) (x2 := x2) (y1 := a1 * b) (y2 := (a - a1) * b) hy1 hy2
        have hy : a1 * b + (a - a1) * b = a * b := by ring
        calc
          (G.edgeCount X Y : ℝ) ^ 2 / (a * b) = (x1 + x2) ^ 2 / (a * b) := by rw [hE]
          _ = (x1 + x2) ^ 2 / (a1 * b + (a - a1) * b) := by rw [hy]
          _ ≤ x1 ^ 2 / (a1 * b) + x2 ^ 2 / ((a - a1) * b) := htitu
          _ ≤ H1.sGraph + H2.sGraph := add_le_add hx1 hx2

theorem ratio_le_sGraph_of_parts (G H : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (hG : G.Admissible X Y) (hER : EdgeRestriction G H)
    (hXL : ∀ a ∈ X, a ∈ H.left) (hYR : ∀ b ∈ Y, b ∈ H.right) :
    G.ratio X Y ≤ H.sGraph := by
  classical
  have hH : H.Admissible X Y := ⟨hXL, hYR⟩
  have hcount : H.edgeCount X Y = G.edgeCount X Y := by
    apply edgeCount_congr_on
    intro a ha b hb
    exact edge_eq_of_edgeRestriction hER (hXL a ha) (hYR b hb)
  rw [ratio_of_admissible G hG]
  calc
    (G.edgeCount X Y : ℝ) ^ 2 / ((X.card : ℝ) * (Y.card : ℝ)) =
        (H.edgeCount X Y : ℝ) ^ 2 / ((X.card : ℝ) * (Y.card : ℝ)) := by rw [hcount]
    _ = H.ratio X Y := (ratio_of_admissible H hH).symm
    _ ≤ H.sGraph := ratio_le_sGraph H hH

theorem twoGraph_ratio_le_add
    (G H1 H2 : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (hmono : IsMonotoneCover G ![H1,H2])
    (hAdm : G.Admissible X Y)
    (hGleft : G.left = (↑X : Set A)) (hGright : G.right = (↑Y : Set B)) :
    G.ratio X Y ≤ H1.sGraph + H2.sGraph := by
  classical
  have hcover := hmono.1
  have hER1 : EdgeRestriction G H1 := hcover.2.2.1 0
  have hER2 : EdgeRestriction G H2 := hcover.2.2.1 1
  have hL1R2 : G.left ⊆ H1.left ∨ G.right ⊆ H2.right := by
    have hh := hmono.2 ({0} : Set (Fin 2))
    simpa [Set.sdiff_eq_empty] using hh
  have hL2R1 : G.left ⊆ H2.left ∨ G.right ⊆ H1.right := by
    have hh := hmono.2 ({1} : Set (Fin 2))
    simpa [Set.sdiff_eq_empty] using hh
  by_cases hEzero : G.edgeCount X Y = 0
  · rw [ratio_of_admissible G hAdm, hEzero]
    simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      zero_div]
    exact add_nonneg (BipartiteGraph.sGraph_nonneg H1) (BipartiteGraph.sGraph_nonneg H2)
  · have hEpos : 0 < G.edgeCount X Y := Nat.pos_of_ne_zero hEzero
    obtain ⟨q, hq⟩ := Finset.card_pos.mp hEpos
    change q ∈ (X.product Y).filter (fun q => G.edge q.1 q.2 = true) at hq
    rw [Finset.mem_filter] at hq
    have hge : G.edge q.1 q.2 = true := hq.2
    obtain ⟨i, hi⟩ := hcover.2.2.2 q.1 q.2 hge
    have hHiL : (![H1, H2] i).left ⊆ G.left := hcover.1 i
    have hHiR : (![H1, H2] i).right ⊆ G.right := hcover.2.1 i
    have hLne : G.left.Nonempty :=
      ⟨q.1, hHiL (((hcover.2.2.1 i) q.1 q.2).mp hi).2.1⟩
    have hRne : G.right.Nonempty :=
      ⟨q.2, hHiR (((hcover.2.2.1 i) q.1 q.2).mp hi).2.2⟩
    have hR12 : G.right ⊆ H1.right ∪ H2.right := by
      have hh := hmono.2 (∅ : Set (Fin 2))
      rcases hh with h1 | h2
      · exfalso
        have h1' : G.left = ∅ := by simpa using h1
        obtain ⟨a, ha⟩ := hLne
        rw [h1'] at ha
        exact ha
      · simpa [Set.sdiff_eq_empty] using h2
    have hL12 : G.left ⊆ H1.left ∪ H2.left := by
      have hh := hmono.2 (Set.univ : Set (Fin 2))
      rcases hh with h1 | h2
      · simpa [Set.sdiff_eq_empty] using h1
      · exfalso
        have h2' : G.right = ∅ := by simpa using h2
        obtain ⟨b, hb⟩ := hRne
        rw [h2'] at hb
        exact hb
    by_cases hL1 : G.left ⊆ H1.left
    · by_cases hR1 : G.right ⊆ H1.right
      · exact le_trans (ratio_le_sGraph_of_parts G H1 X Y hAdm hER1
          (fun a ha => hL1 (by rw [hGleft]; exact ha))
          (fun b hb => hR1 (by rw [hGright]; exact hb)))
          (le_add_of_nonneg_right (BipartiteGraph.sGraph_nonneg H2))
      · have hL2 : G.left ⊆ H2.left := by
          rcases hL2R1 with h | h
          · exact h
          · exact absurd h hR1
        exact twoGraph_row G H1 H2 X Y hL1 hL2 hR12 hER1 hER2 hGleft hGright
    · have hR2 : G.right ⊆ H2.right := by
        rcases hL1R2 with h | h
        · exact absurd h hL1
        · exact h
      by_cases hL2 : G.left ⊆ H2.left
      · exact le_trans (ratio_le_sGraph_of_parts G H2 X Y hAdm hER2
          (fun a ha => hL2 (by rw [hGleft]; exact ha))
          (fun b hb => hR2 (by rw [hGright]; exact hb)))
          (le_add_of_nonneg_left (BipartiteGraph.sGraph_nonneg H1))
      · have hR1 : G.right ⊆ H1.right := by
          rcases hL2R1 with h | h
          · exact absurd h hL2
          · exact h
        exact twoGraph_col G H1 H2 X Y hR1 hR2 hL12 hER1 hER2 hGleft hGright

theorem monotoneCover_frag {k : ℕ} {G : BipartiteGraph A B} {Gs : Fin k → BipartiteGraph A B}
    (h : IsMonotoneCover G Gs) (X : Finset A) (Y : Finset B)
    (hX : (↑X : Set A) ⊆ G.left) (hY : (↑Y : Set B) ⊆ G.right) :
    IsMonotoneCover (graphOn G.edge X Y) (fun i => frag (Gs i) X Y) := by
  classical
  refine ⟨cover_frag h.1 X Y, ?_⟩
  intro I
  rcases h.2 I with hI | hI
  · left
    rw [Set.sdiff_eq_empty] at hI ⊢
    intro a ha
    have haG : a ∈ G.left := hX ha
    have haU : a ∈ ⋃ i ∈ I, (Gs i).left := hI haG
    simp only [Set.mem_iUnion, exists_prop] at haU ⊢
    obtain ⟨i, hiI, hai⟩ := haU
    exact ⟨i, hiI, hai, ha⟩
  · right
    rw [Set.sdiff_eq_empty] at hI ⊢
    intro b hb
    have hbG : b ∈ G.right := hY hb
    have hbU : b ∈ ⋃ i ∈ Iᶜ, (Gs i).right := hI hbG
    simp only [Set.mem_iUnion, exists_prop] at hbU ⊢
    obtain ⟨i, hiI, hbi⟩ := hbU
    exact ⟨i, hiI, hbi, hb⟩

theorem sGraph_le_add_of_monotoneCover_two
    (G : BipartiteGraph A B) (Gs : Fin 2 → BipartiteGraph A B)
    (hmono : IsMonotoneCover G Gs) :
    G.sGraph ≤ (Gs 0).sGraph + (Gs 1).sGraph := by
  classical
  rw [BipartiteGraph.sGraph]
  apply Finset.sup'_le
  intro p hp
  by_cases hAdm : G.Admissible p.1 p.2
  · set X : Finset A := p.1 with hXdef
    set Y : Finset B := p.2 with hYdef
    let G' : BipartiteGraph A B := graphOn G.edge X Y
    let Gs' : Fin 2 → BipartiteGraph A B := fun i => frag (Gs i) X Y
    have hX : (↑X : Set A) ⊆ G.left := fun a ha => hAdm.1 a ha
    have hY : (↑Y : Set B) ⊆ G.right := fun b hb => hAdm.2 b hb
    have hmono' : IsMonotoneCover G' Gs' := monotoneCover_frag hmono X Y hX hY
    have hvec : (![Gs' 0, Gs' 1] : Fin 2 → BipartiteGraph A B) = Gs' := by
      funext i
      fin_cases i <;> rfl
    have hmonoVec : IsMonotoneCover G' ![Gs' 0, Gs' 1] := by
      rw [hvec]
      exact hmono'
    have hAdm' : G'.Admissible X Y := ⟨fun a ha => ha, fun b hb => hb⟩
    have hratio : G'.ratio X Y ≤ (Gs' 0).sGraph + (Gs' 1).sGraph :=
      twoGraph_ratio_le_add G' (Gs' 0) (Gs' 1) X Y hmonoVec hAdm' rfl rfl
    have hGeq : G.ratio X Y = G'.ratio X Y := by
      rw [ratio_of_admissible G hAdm, ratio_of_admissible G' hAdm',
        edgeCount_graphOn_self']
    have hle0 : (Gs' 0).sGraph ≤ (Gs 0).sGraph := sGraph_frag_le (Gs 0) X Y
    have hle1 : (Gs' 1).sGraph ≤ (Gs 1).sGraph := sGraph_frag_le (Gs 1) X Y
    calc
      G.ratio X Y = G'.ratio X Y := hGeq
      _ ≤ (Gs' 0).sGraph + (Gs' 1).sGraph := hratio
      _ ≤ (Gs 0).sGraph + (Gs 1).sGraph := add_le_add hle0 hle1
  · simp only [BipartiteGraph.ratio, hAdm, ite_false]
    exact add_nonneg (BipartiteGraph.sGraph_nonneg (Gs 0)) (BipartiteGraph.sGraph_nonneg (Gs 1))

theorem isMonotoneGraphExponent_two_one : IsMonotoneGraphExponent 2 1 := by
  intro m hm A B _ _ _ _ G Gs hmono
  have hm012 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
  rcases hm012 with rfl | rfl | rfl
  · have hno : ∀ a b, G.edge a b = false := by
      intro a b
      by_contra hne
      have htrue : G.edge a b = true := by simpa using hne
      obtain ⟨i, _⟩ := hmono.1.2.2.2 a b htrue
      exact Fin.elim0 i
    rw [sGraph_eq_zero_of_no_edges hno]
    simp
  · simpa using sGraph_le_of_cover_one hmono.1
  · simpa [Fin.sum_univ_two] using sGraph_le_add_of_monotoneCover_two G Gs hmono


theorem isMonotoneGraphExponent_of_le {k : ℕ} {χ χ' : ℝ} (hχ0 : 0 < χ) (hχχ' : χ ≤ χ')
    (h : IsMonotoneGraphExponent k χ') : IsMonotoneGraphExponent k χ := by
  intro m hm A B _ _ _ _ G Gs hmono
  have h' := h m hm A B G Gs hmono
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

theorem isMonotoneGraphExponent_two_of_le {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ ≤ 1) :
    IsMonotoneGraphExponent 2 χ :=
  isMonotoneGraphExponent_of_le hχ0 hχ1 isMonotoneGraphExponent_two_one

theorem wellFormed_graphOn (T : A → B → Bool) (X : Finset A) (Y : Finset B) :
    BipartiteGraph.WellFormed (graphOn T X Y) := by
  intro a b h
  simp only [graphOn, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2⟩

theorem edgeRestriction_frag_self {H : BipartiteGraph A B} (hwf : BipartiteGraph.WellFormed H)
    (X : Finset A) (Y : Finset B) : EdgeRestriction H (frag H X Y) := by
  intro a b
  constructor
  · intro h
    simp only [frag, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, ⟨(hwf a b h.1.1).1, h.1.2⟩, ⟨(hwf a b h.1.1).2, h.2⟩⟩
  · rintro ⟨hE, ⟨_, ha⟩, ⟨_, hb⟩⟩
    simp only [frag, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hE, ha⟩, hb⟩

theorem BipartiteGraph_ext {G H : BipartiteGraph A B} (hl : G.left = H.left)
    (hr : G.right = H.right) (he : G.edge = H.edge) : G = H := by
  rcases G with ⟨Gl, Gr, Ge⟩
  rcases H with ⟨Hl, Hr, He⟩
  simp_all

theorem sGraph_frag_mono (H : BipartiteGraph A B) {X X' : Finset A} (Y : Finset B)
    (hX : X' ⊆ X) : (frag H X' Y).sGraph ≤ (frag H X Y).sGraph := by
  apply BipartiteGraph.sGraph_mono
  · intro a ha
    exact ⟨ha.1, hX ha.2⟩
  · intro b hb
    exact hb
  · intro a b h
    simp only [frag, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact ⟨⟨h.1.1, hX h.1.2⟩, h.2⟩

theorem frag_eq_graphOn_self {G H : BipartiteGraph A B} (X : Finset A) (Y : Finset B)
    (hER : EdgeRestriction (graphOn G.edge X Y) (frag H X Y))
    (hX : (↑X : Set A) ⊆ (frag H X Y).left) (hY : (↑Y : Set B) ⊆ (frag H X Y).right) :
    frag H X Y = graphOn G.edge X Y := by
  classical
  apply BipartiteGraph_ext
  · ext a
    simp only [frag, graphOn, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => by
      have hh := hX h
      simp only [frag, Set.mem_inter_iff, Set.mem_setOf_eq] at hh
      exact ⟨hh.1, h⟩⟩
  · ext b
    simp only [frag, graphOn, Set.mem_inter_iff, Set.mem_setOf_eq]
    exact ⟨fun h => h.2, fun h => by
      have hh := hY h
      simp only [frag, Set.mem_inter_iff, Set.mem_setOf_eq] at hh
      exact ⟨hh.1, h⟩⟩
  · funext a b
    by_cases ha : a ∈ X <;> by_cases hb : b ∈ Y
    · have hh : (frag H X Y).edge a b = true ↔ G.edge a b = true := by
        constructor
        · intro h
          have := (hER a b).mp h
          simpa [graphOn, ha, hb] using this.1
        · intro h
          exact (hER a b).mpr ⟨by simp [graphOn, ha, hb, h], hX ha, hY hb⟩
      by_cases hH : H.edge a b = true
      · have hFH : (frag H X Y).edge a b = true := by simp [frag, ha, hb, hH]
        have hG : G.edge a b = true := hh.mp hFH
        simp [frag, graphOn, ha, hb, hH, hG]
      · have hHf : H.edge a b = false := by simpa using hH
        have hFH : (frag H X Y).edge a b = false := by simp [frag, ha, hb, hHf]
        have hGf : G.edge a b = false := by
          by_contra hne
          have hGt : G.edge a b = true := by simpa using hne
          have := hh.mpr hGt
          rw [hFH] at this
          exact Bool.false_ne_true this
        simp [frag, graphOn, ha, hb, hHf, hGf]
    · simp [frag, graphOn, ha, hb]
    · simp [frag, graphOn, ha, hb]
    · simp [frag, graphOn, ha, hb]



theorem frag_edgeRestriction_frag {G0 H : BipartiteGraph A B} (X X' : Finset A) (Y Y' : Finset B)
    (hER : EdgeRestriction G0 (frag H X Y)) (hX' : X' ⊆ X) (hY' : Y' ⊆ Y) :
    EdgeRestriction (frag G0 X' Y') (frag H X' Y') := by
  intro a b
  constructor
  · intro h
    simp only [frag, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hHe, ha'⟩, hb'⟩ := h
    have hHe' : (frag H X Y).edge a b = true := by
      simp only [frag, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hHe, hX' ha'⟩, hY' hb'⟩
    obtain ⟨hG, ⟨haH, _⟩, ⟨hbH, _⟩⟩ := (hER a b).mp hHe'
    refine ⟨?_, ⟨haH, ha'⟩, ⟨hbH, hb'⟩⟩
    simp only [frag, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hG, ha'⟩, hb'⟩
  · rintro ⟨hG, ⟨haH, ha'⟩, ⟨hbH, hb'⟩⟩
    simp only [frag, Bool.and_eq_true, decide_eq_true_eq] at hG ⊢
    obtain ⟨⟨hG0, _⟩, _⟩ := hG
    have hHe : (frag H X Y).edge a b = true :=
      (hER a b).mpr ⟨hG0, ⟨haH, hX' ha'⟩, ⟨hbH, hY' hb'⟩⟩
    simp only [frag, Bool.and_eq_true, decide_eq_true_eq] at hHe
    exact ⟨⟨hHe.1.1, ha'⟩, hb'⟩

theorem induced_monotone (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (Gs : Fin 3 → BipartiteGraph A B)
    (hmono : IsMonotoneCover (graphOn G.edge X Y) (fun t => frag (Gs t) X Y))
    (hnoIso : ∀ a ∈ X, ∃ b ∈ Y, G.edge a b = true)
    (i : Fin 3)
    (hB : (↑Y : Set B) ⊆ (frag (Gs i) X Y).right)
    (hsplit : (↑Y : Set B) ⊆ (frag (Gs (i.succAbove 0)) X Y).right ∪
      (frag (Gs (i.succAbove 1)) X Y).right) :
    IsMonotoneCover (frag (graphOn G.edge X Y) (X \ partLeft X (Gs i).left) Y)
      (fun t : Fin 2 => frag (Gs (i.succAbove t)) (X \ partLeft X (Gs i).left) Y) := by
  classical
  let G0 : BipartiteGraph A B := graphOn G.edge X Y
  let X' : Finset A := X \ partLeft X (Gs i).left
  let G' : BipartiteGraph A B := frag G0 X' Y
  have hX'sub : X' ⊆ X := fun a ha => (Finset.mem_sdiff.mp ha).1
  change IsMonotoneCover G' (fun t : Fin 2 => frag (Gs (i.succAbove t)) X' Y)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro t a ha
    fin_cases t
    · change a ∈ (Gs (i.succAbove 0)).left ∩ {a | a ∈ X'} at ha
      exact ⟨by simpa [G0, graphOn] using (Finset.mem_sdiff.mp ha.2).1, ha.2⟩
    · change a ∈ (Gs (i.succAbove 1)).left ∩ {a | a ∈ X'} at ha
      exact ⟨by simpa [G0, graphOn] using (Finset.mem_sdiff.mp ha.2).1, ha.2⟩
  · intro t b hb
    fin_cases t
    · change b ∈ (Gs (i.succAbove 0)).right ∩ {b | b ∈ Y} at hb
      exact ⟨by simpa [G0, graphOn] using hb.2, hb.2⟩
    · change b ∈ (Gs (i.succAbove 1)).right ∩ {b | b ∈ Y} at hb
      exact ⟨by simpa [G0, graphOn] using hb.2, hb.2⟩
  · intro t
    fin_cases t
    · exact frag_edgeRestriction_frag X X' Y Y (hmono.1.2.2.1 (i.succAbove 0)) hX'sub (by intro b hb; exact hb)
    · exact frag_edgeRestriction_frag X X' Y Y (hmono.1.2.2.1 (i.succAbove 1)) hX'sub (by intro b hb; exact hb)
  · intro a b hab
    simp only [G', frag, G0, graphOn, Bool.and_eq_true, decide_eq_true_eq,
      Finset.mem_sdiff] at hab
    obtain ⟨⟨⟨⟨hG, haX⟩, hbY⟩, haX'⟩, hbY'⟩ := hab
    have haAi : a ∉ partLeft X (Gs i).left := (Finset.mem_sdiff.mp haX').2
    obtain ⟨t, ht⟩ := hmono.1.2.2.2 a b (by simpa [G0, graphOn, haX, hbY] using hG)
    simp only [frag, Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨⟨hGst, haXt⟩, hbYt⟩ := ht
    have hti : t ≠ i := by
      intro hti
      subst t
      have hf : (frag (Gs i) X Y).edge a b = true := by simp [frag, hGst, haXt, hbYt]
      have haAi' : a ∈ (Gs i).left := (((hmono.1.2.2.1 i) a b).mp hf).2.1.1
      exact haAi (by simp [partLeft, haX, haAi'])
    obtain ⟨s, rfl⟩ := Fin.exists_succAbove_eq hti
    refine ⟨s, ?_⟩
    simp only [frag, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hGst, haX'⟩, hbYt⟩
  · intro I
    have hIcases : I = ∅ ∨ I = ({0} : Set (Fin 2)) ∨ I = ({1} : Set (Fin 2)) ∨ I = Set.univ := by
      by_cases h0 : (0 : Fin 2) ∈ I <;> by_cases h1 : (1 : Fin 2) ∈ I
      · right; right; right; ext t; fin_cases t <;> simp [h0, h1]
      · right; left; ext t; fin_cases t <;> simp [h0, h1]
      · right; right; left; ext t; fin_cases t <;> simp [h0, h1]
      · left; ext t; fin_cases t <;> simp [h0, h1]
    rcases hIcases with rfl | rfl | rfl | rfl
    · right
      rw [← Set.subset_empty_iff]
      intro b hb
      have hbY : b ∈ Y := by simpa [G', frag, G0, graphOn] using hb.1
      have hbUnion : b ∈ ⋃ t ∈ (∅ : Set (Fin 2))ᶜ,
          (frag (Gs (i.succAbove t)) X' Y).right := by
        rcases hsplit hbY with h | h
        · refine Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
          · simp
          · simpa [frag] using h
        · refine Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
          · simp
          · simpa [frag] using h
      exact hb.2 hbUnion
    · by_cases hfirst : G'.left \ (frag (Gs (i.succAbove 0)) X' Y).left = ∅
      · left; simpa using hfirst
      · right
        rw [← Set.subset_empty_iff]
        intro b hb
        have hbY : b ∈ Y := by simpa [G', frag, G0, graphOn] using hb.1
        have hbj1 : b ∉ (Gs (i.succAbove 1)).right := fun h =>
          hb.2 (by simp [frag, h, hbY])
        have hFirstFail : ¬ (G0.left \ ⋃ t ∈ ({i, i.succAbove 0} : Set (Fin 3)),
            (frag (Gs t) X Y).left = ∅) := by
          intro hEq
          apply hfirst
          rw [← Set.subset_empty_iff]
          intro a ha
          have haX' : a ∈ X' := ha.1.2
          have haX : a ∈ X := (Finset.mem_sdiff.mp haX').1
          have hnot : a ∉ ⋃ t ∈ ({i, i.succAbove 0} : Set (Fin 3)),
              (frag (Gs t) X Y).left := by
            intro hmem
            simp only [Set.mem_iUnion, exists_prop, Set.mem_insert_iff,
              Set.mem_singleton_iff] at hmem
            obtain ⟨t, ht, hmt⟩ := hmem
            rcases ht with rfl | rfl
            · exact (Finset.mem_sdiff.mp haX').2 (by simp [partLeft, haX, hmt.1])
            · exact ha.2 ⟨hmt.1, haX'⟩
          have hdiff : a ∈ G0.left \ ⋃ t ∈ ({i, i.succAbove 0} : Set (Fin 3)),
              (frag (Gs t) X Y).left := ⟨by simpa [G0, graphOn] using haX, hnot⟩
          rw [hEq] at hdiff
          exact hdiff
        have hSecondFail : ¬ (G0.right \ ⋃ t ∈ ({i, i.succAbove 0} : Set (Fin 3))ᶜ,
            (frag (Gs t) X Y).right = ∅) := by
          intro hEq
          have hmem : b ∈ G0.right \ ⋃ t ∈ ({i, i.succAbove 0} : Set (Fin 3))ᶜ,
              (frag (Gs t) X Y).right := by
            refine ⟨by simpa [G0, graphOn] using hbY, ?_⟩
            intro hbU
            simp only [Set.mem_iUnion, exists_prop, Set.mem_compl_iff] at hbU
            obtain ⟨t, ht, hmt⟩ := hbU
            have ht1 : t = i.succAbove 1 := by
              fin_cases i <;> fin_cases t <;> simp_all [Fin.succAbove]
            rw [ht1] at hmt
            exact hbj1 hmt.1
          rw [hEq] at hmem
          exact hmem
        rcases hmono.2 ({i, i.succAbove 0} : Set (Fin 3)) with h | h
        · exact hFirstFail h
        · exact hSecondFail h
    · by_cases hfirst : G'.left \ (frag (Gs (i.succAbove 1)) X' Y).left = ∅
      · left; simpa using hfirst
      · right
        rw [← Set.subset_empty_iff]
        intro b hb
        have hbY : b ∈ Y := by simpa [G', frag, G0, graphOn] using hb.1
        have hbj0 : b ∉ (Gs (i.succAbove 0)).right := fun h =>
          hb.2 (by simp [frag, h, hbY])
        have hFirstFail : ¬ (G0.left \ ⋃ t ∈ ({i, i.succAbove 1} : Set (Fin 3)),
            (frag (Gs t) X Y).left = ∅) := by
          intro hEq
          apply hfirst
          rw [← Set.subset_empty_iff]
          intro a ha
          have haX' : a ∈ X' := ha.1.2
          have haX : a ∈ X := (Finset.mem_sdiff.mp haX').1
          have hnot : a ∉ ⋃ t ∈ ({i, i.succAbove 1} : Set (Fin 3)),
              (frag (Gs t) X Y).left := by
            intro hmem
            simp only [Set.mem_iUnion, exists_prop, Set.mem_insert_iff,
              Set.mem_singleton_iff] at hmem
            obtain ⟨t, ht, hmt⟩ := hmem
            rcases ht with rfl | rfl
            · exact (Finset.mem_sdiff.mp haX').2 (by simp [partLeft, haX, hmt.1])
            · exact ha.2 ⟨hmt.1, haX'⟩
          have hdiff : a ∈ G0.left \ ⋃ t ∈ ({i, i.succAbove 1} : Set (Fin 3)),
              (frag (Gs t) X Y).left := ⟨by simpa [G0, graphOn] using haX, hnot⟩
          rw [hEq] at hdiff
          exact hdiff
        have hSecondFail : ¬ (G0.right \ ⋃ t ∈ ({i, i.succAbove 1} : Set (Fin 3))ᶜ,
            (frag (Gs t) X Y).right = ∅) := by
          intro hEq
          have hmem : b ∈ G0.right \ ⋃ t ∈ ({i, i.succAbove 1} : Set (Fin 3))ᶜ,
              (frag (Gs t) X Y).right := by
            refine ⟨by simpa [G0, graphOn] using hbY, ?_⟩
            intro hbU
            simp only [Set.mem_iUnion, exists_prop, Set.mem_compl_iff] at hbU
            obtain ⟨t, ht, hmt⟩ := hbU
            have ht0 : t = i.succAbove 0 := by
              fin_cases i <;> fin_cases t <;> simp_all [Fin.succAbove]
            rw [ht0] at hmt
            exact hbj0 hmt.1
          rw [hEq] at hmem
          exact hmem
        rcases hmono.2 ({i, i.succAbove 1} : Set (Fin 3)) with h | h
        · exact hFirstFail h
        · exact hSecondFail h
    · left
      rw [← Set.subset_empty_iff]
      intro a ha
      have haX' : a ∈ X' := ha.1.2
      obtain ⟨b, hbY, hGab⟩ := hnoIso a (Finset.mem_sdiff.mp haX').1
      have hG0 : G0.edge a b = true := by
        simp [G0, graphOn, (Finset.mem_sdiff.mp haX').1, hbY, hGab]
      obtain ⟨t, ht⟩ := hmono.1.2.2.2 a b hG0
      simp only [frag, Bool.and_eq_true, decide_eq_true_eq] at ht
      obtain ⟨⟨hGst, haXt⟩, hbYt⟩ := ht
      have hti : t ≠ i := by
        intro hti
        subst t
        have hf : (frag (Gs i) X Y).edge a b = true := by simp [frag, hGst, haXt, hbYt]
        have haAi : a ∈ (Gs i).left := (((hmono.1.2.2.1 i) a b).mp hf).2.1.1
        exact (Finset.mem_sdiff.mp haX').2
          (by simp [partLeft, (Finset.mem_sdiff.mp haX').1, haAi])
      have htcase : t = i.succAbove 0 ∨ t = i.succAbove 1 := by
        fin_cases i <;> fin_cases t <;> simp_all [Fin.succAbove]
      rcases htcase with rfl | rfl
      · refine ha.2 (Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨by simp, ?_⟩⟩)
        have hf : (frag (Gs (i.succAbove 0)) X Y).edge a b = true := by
          simp [frag, hGst, haXt, hbYt]
        have hmemLeft : a ∈ (Gs (i.succAbove 0)).left :=
          (((hmono.1.2.2.1 (i.succAbove 0)) a b).mp hf).2.1.1
        show a ∈ (frag (Gs (i.succAbove 0)) X' Y).left
        exact ⟨hmemLeft, haX'⟩
      · refine ha.2 (Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨by simp, ?_⟩⟩)
        have hf : (frag (Gs (i.succAbove 1)) X Y).edge a b = true := by
          simp [frag, hGst, haXt, hbYt]
        have hmemLeft : a ∈ (Gs (i.succAbove 1)).left :=
          (((hmono.1.2.2.1 (i.succAbove 1)) a b).mp hf).2.1.1
        show a ∈ (frag (Gs (i.succAbove 1)) X' Y).left
        exact ⟨hmemLeft, haX'⟩


theorem case_one_right
    (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (Gs : Fin 3 → BipartiteGraph A B)
    (hmono : IsMonotoneCover (graphOn G.edge X Y) (fun t => frag (Gs t) X Y))
    (hnoIso : ∀ a ∈ X, ∃ b ∈ Y, G.edge a b = true)
    (i : Fin 3)
    (hB : (↑Y : Set B) ⊆ (frag (Gs i) X Y).right)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ ≤ 1) :
    (graphOn G.edge X Y).sGraph ^ χ ≤ ∑ t, (frag (Gs t) X Y).sGraph ^ χ := by
  classical
  let G0 : BipartiteGraph A B := graphOn G.edge X Y
  let Gi : BipartiteGraph A B := frag (Gs i) X Y
  let X' : Finset A := X \ partLeft X (Gs i).left
  let G' : BipartiteGraph A B := frag G0 X' Y
  have hX'sub : X' ⊆ X := fun a ha => (Finset.mem_sdiff.mp ha).1
  have hG0wf : BipartiteGraph.WellFormed G0 := wellFormed_graphOn G.edge X Y
  have hG'ER : EdgeRestriction G0 G' := edgeRestriction_frag_self hG0wf X' Y
  have hmono2 : IsMonotoneCover G0 ![G', Gi] := by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · intro t a ha
      fin_cases t
      · change a ∈ G0.left ∩ {a | a ∈ X'} at ha
        exact (Finset.mem_sdiff.mp ha.2).1
      · change a ∈ (Gs i).left ∩ {a | a ∈ X} at ha
        exact ha.2
    · intro t b hb
      fin_cases t
      · change b ∈ G0.right ∩ {b | b ∈ Y} at hb
        exact hb.2
      · change b ∈ (Gs i).right ∩ {b | b ∈ Y} at hb
        exact hb.2
    · intro t
      fin_cases t
      · exact hG'ER
      · exact hmono.1.2.2.1 i
    · intro a b hab
      have hab' : (G.edge a b = true ∧ a ∈ X) ∧ b ∈ Y := by
        simpa [G0, graphOn, Bool.and_eq_true, decide_eq_true_eq] using hab
      obtain ⟨⟨hG, haX⟩, hbY⟩ := hab'
      by_cases hai : a ∈ (Gs i).left
      · refine ⟨1, ?_⟩
        change Gi.edge a b = true
        have hAle : a ∈ Gi.left := ⟨hai, haX⟩
        have hBle : b ∈ Gi.right := hB hbY
        exact (hmono.1.2.2.1 i a b).mpr ⟨hab, hAle, hBle⟩
      · refine ⟨0, ?_⟩
        change (frag G0 X' Y).edge a b = true
        simp only [frag, G0, graphOn, Bool.and_eq_true, decide_eq_true_eq,
          X', Finset.mem_sdiff, partLeft]
        refine ⟨⟨⟨⟨hG, haX⟩, hbY⟩, haX, ?_⟩, hbY⟩
        simp [hai]
    · intro I
      have hIcases : I = ∅ ∨ I = ({0} : Set (Fin 2)) ∨ I = ({1} : Set (Fin 2)) ∨ I = Set.univ := by
        by_cases h0 : (0 : Fin 2) ∈ I <;> by_cases h1 : (1 : Fin 2) ∈ I
        · right; right; right; ext t; fin_cases t <;> simp [h0, h1]
        · right; left; ext t; fin_cases t <;> simp [h0, h1]
        · right; right; left; ext t; fin_cases t <;> simp [h0, h1]
        · left; ext t; fin_cases t <;> simp [h0, h1]
      rcases hIcases with rfl | rfl | rfl | rfl
      · right
        rw [← Set.subset_empty_iff]
        intro b hb
        refine hb.2 (Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨by simp, ?_⟩⟩)
        show b ∈ G'.right
        simp only [G', frag]
        exact ⟨hb.1, by simpa [G0, graphOn] using hb.1⟩
      · right
        rw [← Set.subset_empty_iff]
        intro b hb
        refine hb.2 (Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨by simp, ?_⟩⟩)
        show b ∈ Gi.right
        simpa only [Gi, frag] using hB hb.1
      · right
        rw [← Set.subset_empty_iff]
        intro b hb
        refine hb.2 (Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨by simp, ?_⟩⟩)
        show b ∈ G'.right
        simp only [G', frag]
        exact ⟨hb.1, by simpa [G0, graphOn] using hb.1⟩
      · left
        rw [← Set.subset_empty_iff]
        intro a ha
        by_cases hai : a ∈ (Gs i).left
        · refine ha.2 (Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨by simp, ?_⟩⟩)
          show a ∈ Gi.left
          exact ⟨hai, ha.1⟩
        · refine ha.2 (Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨by simp, ?_⟩⟩)
          show a ∈ G'.left
          simp only [G', frag]
          refine ⟨?_, ?_⟩
          · simpa [G0, graphOn] using ha.1
          · simp only [X', Finset.mem_sdiff, partLeft, Finset.mem_filter]
            exact ⟨ha.1, fun h => hai h.2⟩
  have h2 := isMonotoneGraphExponent_two_of_le hχ0 hχ1 2 le_rfl A B G0 ![G', Gi] hmono2
  have h2' : G0.sGraph ^ χ ≤ G'.sGraph ^ χ + Gi.sGraph ^ χ := by
    simpa [Fin.sum_univ_two] using h2
  by_cases hsplit : (↑Y : Set B) ⊆ (frag (Gs (i.succAbove 0)) X Y).right ∪
      (frag (Gs (i.succAbove 1)) X Y).right
  · have hmono3 : IsMonotoneCover G' (fun t : Fin 2 => frag (Gs (i.succAbove t)) X' Y) :=
      induced_monotone G X Y Gs hmono hnoIso i hB hsplit
    have h3 := isMonotoneGraphExponent_two_of_le hχ0 hχ1 2 le_rfl A B G' _ hmono3
    have h3' : G'.sGraph ^ χ ≤ (frag (Gs (i.succAbove 0)) X' Y).sGraph ^ χ +
        (frag (Gs (i.succAbove 1)) X' Y).sGraph ^ χ := by
      simpa [Fin.sum_univ_two] using h3
    have hle0 : (frag (Gs (i.succAbove 0)) X' Y).sGraph ^ χ ≤
        (frag (Gs (i.succAbove 0)) X Y).sGraph ^ χ :=
      Real.rpow_le_rpow (BipartiteGraph.sGraph_nonneg _)
        (sGraph_frag_mono (Gs (i.succAbove 0)) Y hX'sub) hχ0.le
    have hle1 : (frag (Gs (i.succAbove 1)) X' Y).sGraph ^ χ ≤
        (frag (Gs (i.succAbove 1)) X Y).sGraph ^ χ :=
      Real.rpow_le_rpow (BipartiteGraph.sGraph_nonneg _)
        (sGraph_frag_mono (Gs (i.succAbove 1)) Y hX'sub) hχ0.le
    have hGi : Gi.sGraph ^ χ ≤ ∑ t, (frag (Gs t) X Y).sGraph ^ χ :=
      Finset.single_le_sum (f := fun t => (frag (Gs t) X Y).sGraph ^ χ)
        (fun t _ => Real.rpow_nonneg (BipartiteGraph.sGraph_nonneg _) _) (Finset.mem_univ i)
    have hsum : (frag (Gs (i.succAbove 0)) X Y).sGraph ^ χ +
        (frag (Gs (i.succAbove 1)) X Y).sGraph ^ χ + Gi.sGraph ^ χ ≤
        ∑ t, (frag (Gs t) X Y).sGraph ^ χ := by
      have hs := Fin.sum_univ_succAbove (fun t => (frag (Gs t) X Y).sGraph ^ χ) i
      rw [hs]
      simp only [Fin.sum_univ_two]
      linarith
    calc
      G0.sGraph ^ χ ≤ G'.sGraph ^ χ + Gi.sGraph ^ χ := h2'
      _ ≤ ((frag (Gs (i.succAbove 0)) X' Y).sGraph ^ χ +
            (frag (Gs (i.succAbove 1)) X' Y).sGraph ^ χ) + Gi.sGraph ^ χ :=
          add_le_add h3' le_rfl
      _ ≤ ((frag (Gs (i.succAbove 0)) X Y).sGraph ^ χ +
            (frag (Gs (i.succAbove 1)) X Y).sGraph ^ χ) + Gi.sGraph ^ χ :=
          add_le_add (add_le_add hle0 hle1) le_rfl
      _ ≤ ∑ t, (frag (Gs t) X Y).sGraph ^ χ := hsum
  · have hAi : (↑X : Set A) ⊆ (Gs i).left := by
      rw [Set.subset_def] at hsplit
      push Not at hsplit
      obtain ⟨b, hbY, hbU⟩ := hsplit
      have hb0 : b ∉ (frag (Gs (i.succAbove 0)) X Y).right := fun h => hbU (Or.inl h)
      have hb1 : b ∉ (frag (Gs (i.succAbove 1)) X Y).right := fun h => hbU (Or.inr h)
      have hsecond_ne : (G0.right \ ⋃ t ∈ ({i} : Set (Fin 3))ᶜ,
          (frag (Gs t) X Y).right) ≠ ∅ := by
        intro hEq
        have hmem : b ∈ G0.right \ ⋃ t ∈ ({i} : Set (Fin 3))ᶜ,
            (frag (Gs t) X Y).right := by
          refine ⟨hbY, ?_⟩
          intro hbU'
          simp only [Set.mem_iUnion, exists_prop] at hbU'
          obtain ⟨t, ht, hmemt⟩ := hbU'
          have hti : t ≠ i := by simpa using ht
          have htcase : t = i.succAbove 0 ∨ t = i.succAbove 1 := by
            fin_cases i <;> fin_cases t <;> simp_all [Fin.succAbove]
          rcases htcase with rfl | rfl
          · exact hb0 hmemt
          · exact hb1 hmemt
        rw [hEq] at hmem
        exact hmem
      have hfirst : G0.left \ ⋃ t ∈ ({i} : Set (Fin 3)),
          (frag (Gs t) X Y).left = ∅ := by
        rcases hmono.2 ({i} : Set (Fin 3)) with h | h
        · exact h
        · exact absurd h hsecond_ne
      intro a ha
      have hmem : a ∈ ⋃ t ∈ ({i} : Set (Fin 3)), (frag (Gs t) X Y).left := by
        by_contra hat
        have hdiff : a ∈ G0.left \ ⋃ t ∈ ({i} : Set (Fin 3)),
            (frag (Gs t) X Y).left := ⟨by simpa [G0, graphOn] using ha, hat⟩
        rw [hfirst] at hdiff
        exact hdiff
      simp only [Set.mem_iUnion, exists_prop, Set.mem_singleton_iff] at hmem
      obtain ⟨t, rfl, hmemG⟩ := hmem
      exact hmemG.1
    have hBri : (↑Y : Set B) ⊆ (Gs i).right := by
      intro b hb; exact (hB hb).1
    have hAi' : (↑X : Set A) ⊆ Gi.left := fun a ha => ⟨hAi ha, ha⟩
    have hBri' : (↑Y : Set B) ⊆ Gi.right := fun b hb => ⟨hBri hb, hb⟩
    have hGiEq : Gi = G0 := frag_eq_graphOn_self (G := G) (H := Gs i) X Y
      (hmono.1.2.2.1 i) hAi' hBri' 
    have hGiS : Gi.sGraph = G0.sGraph := by rw [hGiEq]
    have hsum : Gi.sGraph ^ χ ≤ ∑ t, (frag (Gs t) X Y).sGraph ^ χ :=
      Finset.single_le_sum (f := fun t => (frag (Gs t) X Y).sGraph ^ χ)
        (fun t _ => Real.rpow_nonneg (BipartiteGraph.sGraph_nonneg _) _) (Finset.mem_univ i)
    rwa [hGiS] at hsum





def swapGraph (G : BipartiteGraph A B) : BipartiteGraph B A where
  left := G.right
  right := G.left
  edge := fun b a => G.edge a b

@[simp] theorem swapGraph_left (G : BipartiteGraph A B) : (swapGraph G).left = G.right := rfl
@[simp] theorem swapGraph_right (G : BipartiteGraph A B) : (swapGraph G).right = G.left := rfl

theorem swapGraph_graphOn (T : A → B → Bool) (X : Finset A) (Y : Finset B) :
    swapGraph (graphOn T X Y) = graphOn (fun b a => T a b) Y X := by
  apply BipartiteGraph_ext <;> try rfl
  funext b a
  simp only [swapGraph, graphOn, Bool.and_assoc]
  rw [Bool.and_comm (decide (b ∈ Y)), Bool.and_left_comm]

theorem swapGraph_frag (H : BipartiteGraph A B) (X : Finset A) (Y : Finset B) :
    swapGraph (frag H X Y) = frag (swapGraph H) Y X := by
  apply BipartiteGraph_ext <;> try rfl
  funext b a
  simp only [swapGraph, frag, Bool.and_assoc]
  rw [Bool.and_comm (decide (b ∈ Y)), Bool.and_left_comm]

theorem isCover_swap {k : ℕ} {G : BipartiteGraph A B} {Gs : Fin k → BipartiteGraph A B}
    (h : IsCover G Gs) : IsCover (swapGraph G) (fun i => swapGraph (Gs i)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i b hb
    exact h.2.1 i hb
  · intro i a ha
    exact h.1 i ha
  · intro i b a
    constructor
    · intro hh
      have := (h.2.2.1 i a b).mp hh
      exact ⟨this.1, this.2.2, this.2.1⟩
    · rintro ⟨hG, ha, hb⟩
      exact (h.2.2.1 i a b).mpr ⟨hG, hb, ha⟩
  · intro b a hab
    obtain ⟨i, hi⟩ := h.2.2.2 a b hab
    exact ⟨i, hi⟩

theorem isMonotoneCover_swap {k : ℕ} {G : BipartiteGraph A B} {Gs : Fin k → BipartiteGraph A B}
    (h : IsMonotoneCover G Gs) : IsMonotoneCover (swapGraph G) (fun i => swapGraph (Gs i)) := by
  refine ⟨isCover_swap h.1, ?_⟩
  intro I
  rcases h.2 Iᶜ with h1 | h2
  · right; exact h1
  · left; simpa using h2



theorem edgeCount_swap (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B) :
    (swapGraph G).edgeCount Y X = G.edgeCount X Y := by
  classical
  unfold BipartiteGraph.edgeCount
  apply Finset.card_bij (fun q _ => (q.2, q.1))
  · intro q hq
    simp only [Finset.mem_filter] at hq
    have hq' : q.1 ∈ Y ∧ q.2 ∈ X := by
      have h := hq.1
      change q ∈ Y ×ˢ X at h
      exact Finset.mem_product.mp h
    rw [Finset.mem_filter]
    constructor
    · change (q.2, q.1) ∈ X ×ˢ Y
      exact Finset.mem_product.mpr ⟨hq'.2, hq'.1⟩
    · simpa [swapGraph] using hq.2
  · intro q1 _ q2 _ h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  · intro q hq
    simp only [Finset.mem_filter] at hq
    have hq' : q.1 ∈ X ∧ q.2 ∈ Y := by
      have h := hq.1
      change q ∈ X ×ˢ Y at h
      exact Finset.mem_product.mp h
    refine ⟨(q.2, q.1), ?_, rfl⟩
    rw [Finset.mem_filter]
    constructor
    · change (q.2, q.1) ∈ Y ×ˢ X
      exact Finset.mem_product.mpr ⟨hq'.2, hq'.1⟩
    · simpa [swapGraph] using hq.2

theorem admissible_swap (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B) :
    (swapGraph G).Admissible Y X ↔ G.Admissible X Y := by
  constructor <;> intro h
  · exact ⟨h.2, h.1⟩
  · exact ⟨h.2, h.1⟩

theorem ratio_swap (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B) :
    (swapGraph G).ratio Y X = G.ratio X Y := by
  classical
  by_cases h : G.Admissible X Y
  · rw [BipartiteGraph.ratio, if_pos ((admissible_swap G X Y).mpr h),
      BipartiteGraph.ratio, if_pos h, edgeCount_swap]
    rw [mul_comm]
  · have h' : ¬ (swapGraph G).Admissible Y X := fun hs => h ((admissible_swap G X Y).mp hs)
    simp [BipartiteGraph.ratio, h, h']

theorem ratio_le_sGraph' (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B) :
    G.ratio X Y ≤ G.sGraph := by
  by_cases h : G.Admissible X Y
  · exact ratio_le_sGraph G h
  · rw [BipartiteGraph.ratio, if_neg h]
    exact BipartiteGraph.sGraph_nonneg G

theorem sGraph_swap (G : BipartiteGraph A B) : (swapGraph G).sGraph = G.sGraph := by
  classical
  apply le_antisymm
  · unfold BipartiteGraph.sGraph
    apply Finset.sup'_le
    intro p _
    rw [ratio_swap]
    exact ratio_le_sGraph' G p.2 p.1
  · unfold BipartiteGraph.sGraph
    apply Finset.sup'_le
    intro p _
    rw [← ratio_swap]
    exact ratio_le_sGraph' (swapGraph G) p.2 p.1

theorem case_one_left
    (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (Gs : Fin 3 → BipartiteGraph A B)
    (hmono : IsMonotoneCover (graphOn G.edge X Y) (fun t => frag (Gs t) X Y))
    (hnoIsoY : ∀ b ∈ Y, ∃ a ∈ X, G.edge a b = true)
    (i : Fin 3)
    (hA : (↑X : Set A) ⊆ (frag (Gs i) X Y).left)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ ≤ 1) :
    (graphOn G.edge X Y).sGraph ^ χ ≤ ∑ t, (frag (Gs t) X Y).sGraph ^ χ := by
  classical
  let Gs' : Fin 3 → BipartiteGraph B A := fun t => swapGraph (Gs t)
  have hmono_s : IsMonotoneCover (graphOn (swapGraph G).edge Y X) (fun t => frag (Gs' t) Y X) := by
    have h := isMonotoneCover_swap hmono
    rw [swapGraph_graphOn] at h
    simp only [swapGraph_frag] at h
    exact h
  have hnoIso_s : ∀ b ∈ Y, ∃ a ∈ X, (swapGraph G).edge b a = true := by
    intro b hb
    obtain ⟨a, ha, hab⟩ := hnoIsoY b hb
    exact ⟨a, ha, hab⟩
  have hB_s : (↑X : Set A) ⊆ (frag (Gs' i) Y X).right := by
    intro a ha
    exact ⟨(hA ha).1, ha⟩
  have hres := case_one_right (G := swapGraph G) (X := Y) (Y := X) Gs' hmono_s hnoIso_s i hB_s hχ0 hχ1
  have hL : (graphOn (swapGraph G).edge Y X).sGraph = (graphOn G.edge X Y).sGraph := by
    change (graphOn (fun b a => G.edge a b) Y X).sGraph = (graphOn G.edge X Y).sGraph
    rw [← swapGraph_graphOn (G.edge) X Y]
    exact sGraph_swap _
  rw [hL] at hres
  simpa only [Gs', ← swapGraph_frag, sGraph_swap] using hres



/-! ### Case (1) without the isolated-vertex hypothesis

The paper's case `B_i = B` uses only maximality of the pair `(X, Y)` for the
ratio.  We derive the absence of isolated vertices from that maximality here,
so that the case applies to a density-maximising subgraph without extra data.
-/

theorem edgeCount_erase_of_isolated (H : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    {a : A} (hiso : ∀ b ∈ Y, H.edge a b = false) :
    H.edgeCount (X.erase a) Y = H.edgeCount X Y := by
  classical
  unfold BipartiteGraph.edgeCount
  apply congrArg Finset.card
  ext q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hq, he⟩
    have hq' : q.1 ∈ X.erase a ∧ q.2 ∈ Y := Finset.mem_product.mp hq
    exact ⟨Finset.mem_product.mpr ⟨(Finset.mem_erase.mp hq'.1).2, hq'.2⟩, he⟩
  · rintro ⟨hq, he⟩
    have hq' : q.1 ∈ X ∧ q.2 ∈ Y := Finset.mem_product.mp hq
    have hne : q.1 ≠ a := by
      intro h
      rw [h, hiso q.2 hq'.2] at he
      exact Bool.noConfusion he
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨hne, hq'.1⟩, hq'.2⟩, he⟩

theorem ratio_lt_ratio_erase (H : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (hadm : H.Admissible X Y) {a : A} (ha : a ∈ X)
    (hiso : ∀ b ∈ Y, H.edge a b = false)
    (hepos : 0 < H.edgeCount X Y) (hY : 0 < Y.card) (hX2 : 2 ≤ X.card) :
    H.ratio X Y < H.ratio (X.erase a) Y := by
  classical
  have hadm' : H.Admissible (X.erase a) Y :=
    ⟨fun x hx => hadm.1 x (Finset.mem_erase.mp hx).2, hadm.2⟩
  rw [ratio_of_admissible H hadm, ratio_of_admissible H hadm', edgeCount_erase_of_isolated H X Y hiso]
  have hm : ((X.erase a).card : ℝ) = (X.card : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem ha, Nat.cast_sub (Finset.card_pos.mpr ⟨a, ha⟩), Nat.cast_one]
  rw [hm]
  have hY' : (0 : ℝ) < (Y.card : ℝ) := by exact_mod_cast hY
  have hX2' : (2 : ℝ) ≤ (X.card : ℝ) := by exact_mod_cast hX2
  have hnum : (0 : ℝ) < (H.edgeCount X Y : ℝ) ^ 2 := by
    have : (0 : ℝ) < (H.edgeCount X Y : ℝ) := by exact_mod_cast hepos
    positivity
  have hden1 : (0 : ℝ) < ((X.card : ℝ) - 1) * (Y.card : ℝ) := by nlinarith
  have hlt : ((X.card : ℝ) - 1) * (Y.card : ℝ) < (X.card : ℝ) * (Y.card : ℝ) := by
    nlinarith
  exact div_lt_div_of_pos_left hnum hden1 hlt

/-- If `(X, Y)` maximises the ratio of `H` and the ratio is positive, then no
vertex of `X` is isolated towards `Y`. -/
theorem no_isolated_left_of_max_ratio (H : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (hadm : H.Admissible X Y)
    (hmax : H.ratio X Y = H.sGraph) (hpos : 0 < H.ratio X Y) :
    ∀ a ∈ X, ∃ b ∈ Y, H.edge a b = true := by
  classical
  have hr := ratio_of_admissible H hadm
  rw [hr] at hpos
  have hnum : (0 : ℝ) < (H.edgeCount X Y : ℝ) ^ 2 := by
    rcases div_pos_iff.mp hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h1
    · exact absurd h1 (not_lt.mpr (sq_nonneg _))
  have hden : (0 : ℝ) < (X.card : ℝ) * (Y.card : ℝ) := by
    rcases div_pos_iff.mp hpos with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exact absurd h1 (not_lt.mpr (sq_nonneg _))
  have heR : (0 : ℝ) < (H.edgeCount X Y : ℝ) := by
    by_contra hle
    push Not at hle
    have h0 : (H.edgeCount X Y : ℝ) = 0 := le_antisymm hle (Nat.cast_nonneg _)
    nlinarith
  have hepos : 0 < H.edgeCount X Y := by exact_mod_cast heR
  have hY : 0 < Y.card := by
    have hYR : (0 : ℝ) < (Y.card : ℝ) := by
      nlinarith [hden, Nat.cast_nonneg (α := ℝ) X.card]
    exact_mod_cast hYR
  intro a ha
  by_contra h
  push Not at h
  have hiso : ∀ b ∈ Y, H.edge a b = false := by
    intro b hb
    have h' : H.edge a b ≠ true := h b hb
    cases hb' : H.edge a b <;> simp_all
  have hX2 : 2 ≤ X.card := by
    by_contra hlt
    push Not at hlt
    have hXle1 : X.card ≤ 1 := by omega
    have hsingle : X = {a} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨ha, ?_⟩
      intro x hx
      exact Finset.card_le_one.mp hXle1 x hx a ha
    have hzero : H.edgeCount X Y = 0 := by
      unfold BipartiteGraph.edgeCount
      rw [hsingle, Finset.card_eq_zero]
      rw [Finset.filter_eq_empty_iff]
      intro q hq
      have hq' : q.1 ∈ ({a} : Finset A) ∧ q.2 ∈ Y := Finset.mem_product.mp hq
      have hq1 : q.1 = a := Finset.mem_singleton.mp hq'.1
      rw [hq1, hiso q.2 hq'.2]
      simp
    omega
  have hlt := ratio_lt_ratio_erase H X Y hadm ha hiso hepos hY hX2
  have hle : H.ratio (X.erase a) Y ≤ H.sGraph :=
    ratio_le_sGraph H ⟨fun x hx => hadm.1 x (Finset.mem_erase.mp hx).2, hadm.2⟩
  linarith [hmax]

/-- Symmetric form, obtained by swapping the two sides. -/
theorem no_isolated_right_of_max_ratio (H : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (hadm : H.Admissible X Y)
    (hmax : H.ratio X Y = H.sGraph) (hpos : 0 < H.ratio X Y) :
    ∀ b ∈ Y, ∃ a ∈ X, H.edge a b = true := by
  have h := no_isolated_left_of_max_ratio (swapGraph H) Y X
    ((admissible_swap H X Y).mpr hadm) ?_ ?_
  · intro b hb
    obtain ⟨a, ha, hab⟩ := h b hb
    exact ⟨a, ha, hab⟩
  · rw [ratio_swap, sGraph_swap]
    exact hmax
  · rw [ratio_swap]
    exact hpos

/-- Case (1) of Theorem 3, right orientation, with maximality replacing the
isolated-vertex hypothesis. -/
theorem case_one_right_of_max
    (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (Gs : Fin 3 → BipartiteGraph A B)
    (hmono : IsMonotoneCover (graphOn G.edge X Y) (fun t => frag (Gs t) X Y))
    (hmax : (graphOn G.edge X Y).ratio X Y = (graphOn G.edge X Y).sGraph)
    (hpos : 0 < (graphOn G.edge X Y).ratio X Y)
    (i : Fin 3)
    (hB : (↑Y : Set B) ⊆ (frag (Gs i) X Y).right)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ ≤ 1) :
    (graphOn G.edge X Y).sGraph ^ χ ≤ ∑ t, (frag (Gs t) X Y).sGraph ^ χ := by
  have hadm : (graphOn G.edge X Y).Admissible X Y :=
    ⟨fun a ha => ha, fun b hb => hb⟩
  have hnoIso : ∀ a ∈ X, ∃ b ∈ Y, G.edge a b = true := by
    intro a ha
    obtain ⟨b, hb, he⟩ :=
      no_isolated_left_of_max_ratio (graphOn G.edge X Y) X Y hadm hmax hpos a ha
    exact ⟨b, hb, by simpa [graphOn, ha, hb] using he⟩
  exact case_one_right G X Y Gs hmono hnoIso i hB hχ0 hχ1

/-- Case (1) of Theorem 3, left orientation, with maximality replacing the
isolated-vertex hypothesis. -/
theorem case_one_left_of_max
    (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (Gs : Fin 3 → BipartiteGraph A B)
    (hmono : IsMonotoneCover (graphOn G.edge X Y) (fun t => frag (Gs t) X Y))
    (hmax : (graphOn G.edge X Y).ratio X Y = (graphOn G.edge X Y).sGraph)
    (hpos : 0 < (graphOn G.edge X Y).ratio X Y)
    (i : Fin 3)
    (hA : (↑X : Set A) ⊆ (frag (Gs i) X Y).left)
    {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ ≤ 1) :
    (graphOn G.edge X Y).sGraph ^ χ ≤ ∑ t, (frag (Gs t) X Y).sGraph ^ χ := by
  have hadm : (graphOn G.edge X Y).Admissible X Y :=
    ⟨fun a ha => ha, fun b hb => hb⟩
  have hnoIsoY : ∀ b ∈ Y, ∃ a ∈ X, G.edge a b = true := by
    intro b hb
    obtain ⟨a, ha, he⟩ :=
      no_isolated_right_of_max_ratio (graphOn G.edge X Y) X Y hadm hmax hpos b hb
    exact ⟨a, ha, by simpa [graphOn, ha, hb] using he⟩
  exact case_one_left G X Y Gs hmono hnoIsoY i hA hχ0 hχ1


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
/-! ### Density normalisation

`ThreeCore χ` is the normalised form of the Theorem 3 inequality.  The graph is
replaced by its restriction to a density-maximising pair `(X, Y)`, the cover is
restricted accordingly, and the pair is critical: `ratio X Y = sGraph` and the
ratio is positive.  The next theorem shows that this normalised statement
implies the exponent statement for all monotone covers of size at most three.
-/

def ThreeCore (χ : ℝ) : Prop :=
  ∀ (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (Gs : Fin 3 → BipartiteGraph A B),
    IsMonotoneCover (graphOn G.edge X Y) (fun t => frag (Gs t) X Y) →
    (graphOn G.edge X Y).ratio X Y = (graphOn G.edge X Y).sGraph →
    0 < (graphOn G.edge X Y).ratio X Y →
    (graphOn G.edge X Y).sGraph ^ χ ≤ ∑ t, (frag (Gs t) X Y).sGraph ^ χ

theorem isMonotoneGraphExponent_three_of_core {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ ≤ 1)
    (hcore : ThreeCore χ) : IsMonotoneGraphExponent 3 χ := by
  intro m hm A B _ _ _ _ G Gs hmono
  rcases Nat.lt_or_ge m 3 with hlt | hge
  · exact isMonotoneGraphExponent_two_of_le hχ0 hχ1 m (by omega) A B G Gs hmono
  · have hm3 : m = 3 := by omega
    subst m
    obtain ⟨X, Y, hHsG, hG0ratio, hadm, hratio_eq⟩ := exists_densitySubgraph G
    by_cases hzero : G.sGraph = 0
    · rw [hzero, Real.zero_rpow hχ0.ne']
      exact Finset.sum_nonneg fun i _ =>
        Real.rpow_nonneg (BipartiteGraph.sGraph_nonneg (Gs i)) χ
    · have hGpos : 0 < G.sGraph :=
        lt_of_le_of_ne (BipartiteGraph.sGraph_nonneg G) (Ne.symm hzero)
      have hmax : (graphOn G.edge X Y).ratio X Y = (graphOn G.edge X Y).sGraph := by
        rw [hratio_eq, ← hG0ratio]
      have hpos : 0 < (graphOn G.edge X Y).ratio X Y := by
        rw [hratio_eq, ← hG0ratio, hHsG]
        exact hGpos
      have hmono' : IsMonotoneCover (graphOn G.edge X Y) (fun t => frag (Gs t) X Y) :=
        monotoneCover_frag hmono X Y hadm.1 hadm.2
      have hcore' := hcore A B G X Y Gs hmono' hmax hpos
      have hleft : G.sGraph ^ χ ≤ (graphOn G.edge X Y).sGraph ^ χ := by
        rw [hHsG]
      refine le_trans hleft (le_trans hcore' ?_)
      apply Finset.sum_le_sum
      intro t _
      exact Real.rpow_le_rpow (BipartiteGraph.sGraph_nonneg _)
        (sGraph_frag_le (Gs t) X Y) hχ0.le

/-! ### The main case: preparatory structure

In the main case no part of `G` is contained in a cover graph.  Monotonicity
then forces every vertex to belong to at least two graphs of the cover.  The
first two lemmas record this for the left and right sides; the remaining
analytic content of the paper's main case is isolated in `MainCase`.
-/

theorem exists_two_covers_left
    (H : BipartiteGraph A B) (Hs : Fin 3 → BipartiteGraph A B)
    (hmono : IsMonotoneCover H Hs)
    (hnoIso : ∀ a ∈ H.left, ∃ b ∈ H.right, H.edge a b = true)
    (hB : ∀ i, ¬ H.right ⊆ (Hs i).right) :
    ∀ a ∈ H.left, ∃ i j : Fin 3, i ≠ j ∧ a ∈ (Hs i).left ∧ a ∈ (Hs j).left := by
  classical
  intro a ha
  obtain ⟨b, hb, hab⟩ := hnoIso a ha
  obtain ⟨i, hi⟩ := hmono.1.2.2.2 a b hab
  have hai : a ∈ (Hs i).left := (((hmono.1.2.2.1 i) a b).mp hi).2.1
  have hex : ∃ j : Fin 3, j ≠ i ∧ a ∈ (Hs j).left := by
    by_contra hcon
    have haU : a ∉ ⋃ t ∈ ({i}ᶜ : Set (Fin 3)), (Hs t).left := by
      intro hmem
      simp only [Set.mem_iUnion, exists_prop] at hmem
      obtain ⟨t, ht, hat⟩ := hmem
      exact hcon ⟨t, by simpa using ht, hat⟩
    have h1 : (H.left \ ⋃ t ∈ ({i}ᶜ : Set (Fin 3)), (Hs t).left) ≠ ∅ := by
      intro hEq
      have : a ∈ H.left \ ⋃ t ∈ ({i}ᶜ : Set (Fin 3)), (Hs t).left := ⟨ha, haU⟩
      rw [hEq] at this
      exact this
    rcases hmono.2 ({i}ᶜ : Set (Fin 3)) with hleft | hright
    · exact h1 hleft
    · have h2 : H.right ⊆ (Hs i).right := by
        rw [Set.sdiff_eq_empty] at hright
        intro c hc
        have := hright hc
        simpa using this
      exact hB i h2
  obtain ⟨j, hji, haj⟩ := hex
  exact ⟨i, j, Ne.symm hji, hai, haj⟩

theorem exists_two_covers_right
    (H : BipartiteGraph A B) (Hs : Fin 3 → BipartiteGraph A B)
    (hmono : IsMonotoneCover H Hs)
    (hnoIso : ∀ b ∈ H.right, ∃ a ∈ H.left, H.edge a b = true)
    (hA : ∀ i, ¬ H.left ⊆ (Hs i).left) :
    ∀ b ∈ H.right, ∃ i j : Fin 3, i ≠ j ∧ b ∈ (Hs i).right ∧ b ∈ (Hs j).right := by
  classical
  intro b hb
  obtain ⟨a, ha, hab⟩ := hnoIso b hb
  obtain ⟨i, hi⟩ := hmono.1.2.2.2 a b hab
  have hbi : b ∈ (Hs i).right := (((hmono.1.2.2.1 i) a b).mp hi).2.2
  have hex : ∃ j : Fin 3, j ≠ i ∧ b ∈ (Hs j).right := by
    by_contra hcon
    have hbU : b ∉ ⋃ t ∈ ({i}ᶜ : Set (Fin 3)), (Hs t).right := by
      intro hmem
      simp only [Set.mem_iUnion, exists_prop] at hmem
      obtain ⟨t, ht, hbt⟩ := hmem
      exact hcon ⟨t, by simpa using ht, hbt⟩
    have h1 : (H.right \ ⋃ t ∈ ({i}ᶜ : Set (Fin 3)), (Hs t).right) ≠ ∅ := by
      intro hEq
      have : b ∈ H.right \ ⋃ t ∈ ({i}ᶜ : Set (Fin 3)), (Hs t).right := ⟨hb, hbU⟩
      rw [hEq] at this
      exact this
    rcases hmono.2 ({i} : Set (Fin 3)) with hleft | hright
    · have h2 : H.left ⊆ (Hs i).left := by
        rw [Set.sdiff_eq_empty] at hleft
        intro c hc
        have := hleft hc
        simpa using this
      exact hA i h2
    · exact h1 hright
  obtain ⟨j, hji, hbj⟩ := hex
  exact ⟨i, j, Ne.symm hji, hbi, hbj⟩

/-- The remaining analytic statement of Theorem 3: the main case, in which no
part of the graph is contained in a cover graph, after density normalisation.
This is where the paper's estimates (4.2)--(4.14) are used. -/
def MainCase (χ : ℝ) : Prop :=
  ∀ (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (Gs : Fin 3 → BipartiteGraph A B),
    IsMonotoneCover (graphOn G.edge X Y) (fun t => frag (Gs t) X Y) →
    (graphOn G.edge X Y).ratio X Y = (graphOn G.edge X Y).sGraph →
    0 < (graphOn G.edge X Y).ratio X Y →
    (∀ i, ¬ (↑Y : Set B) ⊆ (frag (Gs i) X Y).right) →
    (∀ i, ¬ (↑X : Set A) ⊆ (frag (Gs i) X Y).left) →
    (graphOn G.edge X Y).sGraph ^ χ ≤ ∑ t, (frag (Gs t) X Y).sGraph ^ χ

theorem threeCore_of_main {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ ≤ 1)
    (hmain : MainCase χ) : ThreeCore χ := by
  intro A B _ _ _ _ G X Y Gs hmono hmax hpos
  by_cases hB : ∃ i, (↑Y : Set B) ⊆ (frag (Gs i) X Y).right
  · obtain ⟨i, hi⟩ := hB
    exact case_one_right_of_max G X Y Gs hmono hmax hpos i hi hχ0 hχ1
  · by_cases hA : ∃ i, (↑X : Set A) ⊆ (frag (Gs i) X Y).left
    · obtain ⟨i, hi⟩ := hA
      exact case_one_left_of_max G X Y Gs hmono hmax hpos i hi hχ0 hχ1
    · push Not at hB hA
      exact hmain A B G X Y Gs hmono hmax hpos hB hA

/-- Theorem 3, conditional on the analytic main case. -/
theorem theorem3_of_main {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ ≤ 1)
    (hmain : MainCase χ) : IsMonotoneGraphExponent 3 χ :=
  isMonotoneGraphExponent_three_of_core hχ0 hχ1 (threeCore_of_main hχ0 hχ1 hmain)

theorem theorem3_of_main_0_769 (hmain : MainCase ((769 : ℝ) / 1000)) :
    IsMonotoneGraphExponent 3 ((769 : ℝ) / 1000) :=
  theorem3_of_main (by norm_num) (by norm_num) hmain
/-! ### The main case: the partition `N_1, N_2, N_3` and estimates (4.2)--(4.3)

The main case of Theorem 3 partitions the left part of the graph into three
pieces `N_1, N_2, N_3`, where `N_i` lies in the two cover graphs different from
`G_i`, and similarly for the right part.  The results below are the
combinatorial estimates (4.2) and (4.3) of the paper; the numerical part
(4.4)--(4.14) is what remains of the main case. -/

/-! ### Choosing the third index -/

/-- The element of `Fin 3` different from two distinct given indices. -/
def thirdIndex (i j : Fin 3) : Fin 3 :=
  if i = 0 then (if j = 1 then 2 else 1)
  else if i = 1 then (if j = 0 then 2 else 0)
  else (if j = 0 then 1 else 0)


omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem eq_left_or_right_of_ne_thirdIndex {i j k : Fin 3} (h : i ≠ j)
    (hk : k ≠ thirdIndex i j) : k = i ∨ k = j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all [thirdIndex]

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem exists_lonely_index {X : Finset A} {F : Fin 3 → BipartiteGraph A B}
    (h2 : ∀ a ∈ X, ∃ i j : Fin 3, i ≠ j ∧ a ∈ (F i).left ∧ a ∈ (F j).left) :
    ∀ a ∈ X, ∃ k : Fin 3, ∀ j, j ≠ k → a ∈ (F j).left := by
  intro a ha
  obtain ⟨i, j, hij, hai, haj⟩ := h2 a ha
  refine ⟨thirdIndex i j, fun k hk => ?_⟩
  rcases eq_left_or_right_of_ne_thirdIndex hij hk with rfl | rfl
  · exact hai
  · exact haj

/-! ### The partition `N_1, N_2, N_3` -/

/-- Assign to each vertex of `X` one of the two (or more) cover graphs
containing it. -/
noncomputable def pickIndex (X : Finset A) (F : Fin 3 → BipartiteGraph A B)
    (h : ∀ a : A, a ∈ X → ∃ k : Fin 3, ∀ j, j ≠ k → a ∈ (F j).left) (a : A) : Fin 3 :=
  if ha : a ∈ X then Classical.choose (h a ha) else 0

omit [Fintype A] [Fintype B] [DecidableEq B] in
theorem pickIndex_spec (X : Finset A) (F : Fin 3 → BipartiteGraph A B)
    (h : ∀ a : A, a ∈ X → ∃ k : Fin 3, ∀ j, j ≠ k → a ∈ (F j).left)
    {a : A} (ha : a ∈ X) : ∀ j, j ≠ pickIndex X F h a → a ∈ (F j).left := by
  unfold pickIndex
  rw [dite_eq_left ha]
  exact Classical.choose_spec (h a ha)

/-- A partition of the left part into three pieces, piece `i` lying in the two
cover graphs different from `i`. -/
structure ThreePartsL {A B : Type} (X : Finset A) (F : Fin 3 → BipartiteGraph A B) where
  part : Fin 3 → Finset A
  subset : ∀ i, part i ⊆ X
  disjoint : ∀ i j, i ≠ j → Disjoint (part i) (part j)
  cover : ∀ a ∈ X, ∃ i, a ∈ part i
  other : ∀ (i : Fin 3) (a : A), a ∈ part i → ∀ j, j ≠ i → a ∈ (F j).left

/-- The right-hand analogue. -/
structure ThreePartsR {A B : Type} (Y : Finset B) (F : Fin 3 → BipartiteGraph A B) where
  part : Fin 3 → Finset B
  subset : ∀ i, part i ⊆ Y
  disjoint : ∀ i j, i ≠ j → Disjoint (part i) (part j)
  cover : ∀ b ∈ Y, ∃ i, b ∈ part i
  other : ∀ (i : Fin 3) (b : B), b ∈ part i → ∀ j, j ≠ i → b ∈ (F j).right

omit [Fintype A] [Fintype B] [DecidableEq B] in
theorem exists_threePartsL (X : Finset A) (F : Fin 3 → BipartiteGraph A B)
    (h2 : ∀ a ∈ X, ∃ i j : Fin 3, i ≠ j ∧ a ∈ (F i).left ∧ a ∈ (F j).left) :
    Nonempty (ThreePartsL X F) := by
  classical
  have h3 : ∀ a : A, a ∈ X → ∃ k : Fin 3, ∀ j, j ≠ k → a ∈ (F j).left :=
    fun a ha => exists_lonely_index h2 a ha
  refine ⟨⟨fun i => X.filter (fun a => pickIndex X F h3 a = i), ?_, ?_, ?_, ?_⟩⟩
  · intro i a ha
    exact (Finset.mem_filter.mp ha).1
  · intro i j hij
    rw [Finset.disjoint_left]
    intro a hi hj
    have h1 : pickIndex X F h3 a = i := (Finset.mem_filter.mp hi).2
    have h2' : pickIndex X F h3 a = j := (Finset.mem_filter.mp hj).2
    exact hij (h1.symm.trans h2')
  · intro a ha
    exact ⟨pickIndex X F h3 a, Finset.mem_filter.mpr ⟨ha, rfl⟩⟩
  · intro i a ha j hj
    have hX : a ∈ X := (Finset.mem_filter.mp ha).1
    have hp : pickIndex X F h3 a = i := (Finset.mem_filter.mp ha).2
    exact pickIndex_spec X F h3 hX j (by rw [hp]; exact hj)

/-- Right-hand version of `pickIndex`. -/
noncomputable def pickIndexR (Y : Finset B) (F : Fin 3 → BipartiteGraph A B)
    (h : ∀ b : B, b ∈ Y → ∃ k : Fin 3, ∀ j, j ≠ k → b ∈ (F j).right) (b : B) : Fin 3 :=
  if hb : b ∈ Y then Classical.choose (h b hb) else 0

omit [Fintype A] [Fintype B] [DecidableEq A] in
theorem pickIndexR_spec (Y : Finset B) (F : Fin 3 → BipartiteGraph A B)
    (h : ∀ b : B, b ∈ Y → ∃ k : Fin 3, ∀ j, j ≠ k → b ∈ (F j).right)
    {b : B} (hb : b ∈ Y) : ∀ j, j ≠ pickIndexR Y F h b → b ∈ (F j).right := by
  unfold pickIndexR
  rw [dite_eq_left hb]
  exact Classical.choose_spec (h b hb)

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem exists_lonely_indexR {Y : Finset B} {F : Fin 3 → BipartiteGraph A B}
    (h2 : ∀ b ∈ Y, ∃ i j : Fin 3, i ≠ j ∧ b ∈ (F i).right ∧ b ∈ (F j).right) :
    ∀ b ∈ Y, ∃ k : Fin 3, ∀ j, j ≠ k → b ∈ (F j).right := by
  intro b hb
  obtain ⟨i, j, hij, hbi, hbj⟩ := h2 b hb
  refine ⟨thirdIndex i j, fun k hk => ?_⟩
  rcases eq_left_or_right_of_ne_thirdIndex hij hk with rfl | rfl
  · exact hbi
  · exact hbj

omit [Fintype A] [Fintype B] [DecidableEq A] in
theorem exists_threePartsR (Y : Finset B) (F : Fin 3 → BipartiteGraph A B)
    (h2 : ∀ b ∈ Y, ∃ i j : Fin 3, i ≠ j ∧ b ∈ (F i).right ∧ b ∈ (F j).right) :
    Nonempty (ThreePartsR Y F) := by
  classical
  have h3 : ∀ b : B, b ∈ Y → ∃ k : Fin 3, ∀ j, j ≠ k → b ∈ (F j).right :=
    fun b hb => exists_lonely_indexR h2 b hb
  refine ⟨⟨fun i => Y.filter (fun b => pickIndexR Y F h3 b = i), ?_, ?_, ?_, ?_⟩⟩
  · intro i b hb
    exact (Finset.mem_filter.mp hb).1
  · intro i j hij
    rw [Finset.disjoint_left]
    intro b hi hj
    have h1 : pickIndexR Y F h3 b = i := (Finset.mem_filter.mp hi).2
    have h2' : pickIndexR Y F h3 b = j := (Finset.mem_filter.mp hj).2
    exact hij (h1.symm.trans h2')
  · intro b hb
    exact ⟨pickIndexR Y F h3 b, Finset.mem_filter.mpr ⟨hb, rfl⟩⟩
  · intro i b hb j hj
    have hY : b ∈ Y := (Finset.mem_filter.mp hb).1
    have hp : pickIndexR Y F h3 b = i := (Finset.mem_filter.mp hb).2
    exact pickIndexR_spec Y F h3 hY j (by rw [hp]; exact hj)

/-! ### Relative densities -/

/-- The normalised edge count `|E ∩ (S × T)|² / (|S| |T|)`; for admissible
`S`, `T` it is `H.ratio S T`. -/
noncomputable def relDensity (H : BipartiteGraph A B) (S : Finset A) (T : Finset B) : ℝ :=
  (H.edgeCount S T : ℝ) ^ 2 / ((S.card : ℝ) * (T.card : ℝ))

theorem relDensity_graphOn (H : BipartiteGraph A B) (N : Finset A) (Y : Finset B) :
    relDensity (graphOn H.edge N Y) N Y = relDensity H N Y := by
  unfold relDensity
  rw [edgeCount_graphOn_self']

theorem relDensity_swap (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B) :
    relDensity (swapGraph G) Y X = relDensity G X Y := by
  unfold relDensity
  rw [edgeCount_swap]
  congr 1
  ring

/-! ### Estimate (4.2) -/

theorem frag_sGraph_ge_density (H : BipartiteGraph A B) (F : Fin 3 → BipartiteGraph A B)
    (hmono : IsMonotoneCover H F) (S : Finset A) (T : Finset B) (k : Fin 3)
    (hS : ∀ a ∈ S, a ∈ (F k).left) (hT : ∀ b ∈ T, b ∈ (F k).right) :
    relDensity H S T ≤ (F k).sGraph := by
  classical
  have hAdm : (F k).Admissible S T := ⟨hS, hT⟩
  have hcount : (F k).edgeCount S T = H.edgeCount S T := by
    apply edgeCount_congr_on
    intro a ha b hb
    exact edge_eq_of_edgeRestriction (hmono.1.2.2.1 k) (hS a ha) (hT b hb)
  have h := sGraph_ge_full (F k) S T hAdm
  rw [hcount] at h
  exact h

omit [Fintype A] [Fintype B] [DecidableEq B] in
theorem part_union_left {X : Finset A} {F : Fin 3 → BipartiteGraph A B} (PL : ThreePartsL X F)
    {i j k : Fin 3} (hik : k ≠ i) (hjk : k ≠ j) :
    ∀ a ∈ PL.part i ∪ PL.part j, a ∈ (F k).left := by
  intro a ha
  rcases Finset.mem_union.mp ha with h | h
  · exact PL.other i a h k hik
  · exact PL.other j a h k hjk

omit [Fintype A] [Fintype B] [DecidableEq A] in
theorem part_union_right {Y : Finset B} {F : Fin 3 → BipartiteGraph A B} (PR : ThreePartsR Y F)
    {i j k : Fin 3} (hik : k ≠ i) (hjk : k ≠ j) :
    ∀ b ∈ PR.part i ∪ PR.part j, b ∈ (F k).right := by
  intro b hb
  rcases Finset.mem_union.mp hb with h | h
  · exact PR.other i b h k hik
  · exact PR.other j b h k hjk

/-! ### Estimate (4.3) -/

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem two_of_three {P : Fin 3 → Prop} {i j : Fin 3} (hij : i ≠ j)
    (h : ∃ p q : Fin 3, p ≠ q ∧ P p ∧ P q) : P i ∨ P j := by
  obtain ⟨p, q, hpq, hp, hq⟩ := h
  fin_cases i <;> fin_cases j <;> fin_cases p <;> fin_cases q <;> simp_all

set_option maxHeartbeats 800000 in
theorem row_cover (H : BipartiteGraph A B) (F : Fin 3 → BipartiteGraph A B)
    (hmono : IsMonotoneCover H F) (N : Finset A) (Y : Finset B) (i j : Fin 3)
    (hNi : ∀ a ∈ N, a ∈ (F i).left) (hNj : ∀ a ∈ N, a ∈ (F j).left)
    (hYij : ∀ b ∈ Y, b ∈ (F i).right ∨ b ∈ (F j).right) :
    IsMonotoneCover (graphOn H.edge N Y) ![frag (F i) N Y, frag (F j) N Y] := by
  classical
  have hcover : IsCover (graphOn H.edge N Y) ![frag (F i) N Y, frag (F j) N Y] := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t a ha
      fin_cases t <;> exact ha.2
    · intro t b hb
      fin_cases t <;> exact hb.2
    · intro t
      fin_cases t
      · exact frag_edgeRestriction N Y (hmono.1.2.2.1 i)
      · exact frag_edgeRestriction N Y (hmono.1.2.2.1 j)
    · intro a b hab
      have hab' : (graphOn H.edge N Y).edge a b = true := hab
      simp only [graphOn, Bool.and_eq_true, decide_eq_true_eq] at hab'
      obtain ⟨⟨hE, haN⟩, hbY⟩ := hab'
      obtain ⟨t, ht⟩ := hmono.1.2.2.2 a b hE
      by_cases hti : t = i
      · rw [hti] at ht
        refine ⟨0, ?_⟩
        change ((F i).edge a b && decide (a ∈ N) && decide (b ∈ Y)) = true
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨ht, haN⟩, hbY⟩
      · by_cases htj : t = j
        · rw [htj] at ht
          refine ⟨1, ?_⟩
          change ((F j).edge a b && decide (a ∈ N) && decide (b ∈ Y)) = true
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨ht, haN⟩, hbY⟩
        · rcases hYij b hbY with hbi | hbj
          · have hFit : (F i).edge a b = true :=
              ((hmono.1.2.2.1 i) a b).mpr ⟨hE, hNi a haN, hbi⟩
            refine ⟨0, ?_⟩
            change ((F i).edge a b && decide (a ∈ N) && decide (b ∈ Y)) = true
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨⟨hFit, haN⟩, hbY⟩
          · have hFjt : (F j).edge a b = true :=
              ((hmono.1.2.2.1 j) a b).mpr ⟨hE, hNj a haN, hbj⟩
            refine ⟨1, ?_⟩
            change ((F j).edge a b && decide (a ∈ N) && decide (b ∈ Y)) = true
            simp only [Bool.and_eq_true, decide_eq_true_eq]
            exact ⟨⟨hFjt, haN⟩, hbY⟩
  refine ⟨hcover, ?_⟩
  intro I
  by_cases h0 : (0 : Fin 2) ∈ I
  · left
    rw [Set.sdiff_eq_empty]
    intro a ha
    have hai : a ∈ (![frag (F i) N Y, frag (F j) N Y] 0).left := ⟨hNi a ha, ha⟩
    exact Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨h0, hai⟩⟩
  · by_cases h1 : (1 : Fin 2) ∈ I
    · left
      rw [Set.sdiff_eq_empty]
      intro a ha
      have haj : a ∈ (![frag (F i) N Y, frag (F j) N Y] 1).left := ⟨hNj a ha, ha⟩
      exact Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨h1, haj⟩⟩
    · right
      rw [Set.sdiff_eq_empty]
      intro b hb
      have h0' : (0 : Fin 2) ∈ Iᶜ := by simpa using h0
      have h1' : (1 : Fin 2) ∈ Iᶜ := by simpa using h1
      rcases hYij b hb with hbi | hbj
      · exact Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨h0', ⟨hbi, hb⟩⟩⟩
      · exact Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨h1', ⟨hbj, hb⟩⟩⟩

set_option maxHeartbeats 800000 in
theorem row_bound (H : BipartiteGraph A B) (F : Fin 3 → BipartiteGraph A B)
    (hmono : IsMonotoneCover H F) (N : Finset A) (Y : Finset B) {i j : Fin 3}
    (hNi : ∀ a ∈ N, a ∈ (F i).left) (hNj : ∀ a ∈ N, a ∈ (F j).left)
    (hYij : ∀ b ∈ Y, b ∈ (F i).right ∨ b ∈ (F j).right) :
    relDensity H N Y ≤ (F i).sGraph + (F j).sGraph := by
  classical
  have hAdm : (graphOn H.edge N Y).Admissible N Y := ⟨fun a ha => ha, fun b hb => hb⟩
  have hratio : (graphOn H.edge N Y).ratio N Y = relDensity H N Y := by
    rw [ratio_of_admissible _ hAdm]
    exact relDensity_graphOn H N Y
  have hmonoRow := row_cover H F hmono N Y i j hNi hNj hYij
  have hbound := twoGraph_ratio_le_add (graphOn H.edge N Y) (frag (F i) N Y) (frag (F j) N Y)
    N Y hmonoRow hAdm rfl rfl
  calc relDensity H N Y = (graphOn H.edge N Y).ratio N Y := hratio.symm
    _ ≤ (frag (F i) N Y).sGraph + (frag (F j) N Y).sGraph := hbound
    _ ≤ (F i).sGraph + (F j).sGraph :=
        add_le_add (sGraph_frag_le (F i) N Y) (sGraph_frag_le (F j) N Y)

set_option maxHeartbeats 800000 in
theorem col_bound (H : BipartiteGraph A B) (F : Fin 3 → BipartiteGraph A B)
    (hmono : IsMonotoneCover H F) (X : Finset A) (P : Finset B) {i j : Fin 3}
    (hPi : ∀ b ∈ P, b ∈ (F i).right) (hPj : ∀ b ∈ P, b ∈ (F j).right)
    (hXij : ∀ a ∈ X, a ∈ (F i).left ∨ a ∈ (F j).left) :
    relDensity H X P ≤ (F i).sGraph + (F j).sGraph := by
  have hrow := row_bound (swapGraph H) (fun t => swapGraph (F t)) (isMonotoneCover_swap hmono)
    P X (i := i) (j := j)
    (fun b hb => by simpa using hPi b hb)
    (fun b hb => by simpa using hPj b hb)
    (fun a ha => by
      rcases hXij a ha with h | h
      · exact Or.inl (by simpa using h)
      · exact Or.inr (by simpa using h))
  rw [relDensity_swap] at hrow
  rwa [sGraph_swap, sGraph_swap] at hrow

set_option maxHeartbeats 800000 in
/-- The combinatorial content of the paper's main case: from the density
normalisation one obtains the partitions `N_i` and `P_i`, and every vertex
belongs to at least two cover graphs, which yields estimates (4.2) and (4.3)
for all triples of distinct indices. -/
theorem main_case_estimates
    (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (Gs : Fin 3 → BipartiteGraph A B)
    (hmono : IsMonotoneCover (graphOn G.edge X Y) (fun t => frag (Gs t) X Y))
    (hmax : (graphOn G.edge X Y).ratio X Y = (graphOn G.edge X Y).sGraph)
    (hpos : 0 < (graphOn G.edge X Y).ratio X Y)
    (hB : ∀ i, ¬ (↑Y : Set B) ⊆ (frag (Gs i) X Y).right)
    (hA : ∀ i, ¬ (↑X : Set A) ⊆ (frag (Gs i) X Y).left) :
    ∃ (PL : ThreePartsL X (fun t => frag (Gs t) X Y))
      (PR : ThreePartsR Y (fun t => frag (Gs t) X Y)),
      ∀ i j k : Fin 3, i ≠ j → k ≠ i → k ≠ j →
        relDensity (graphOn G.edge X Y) (PL.part i ∪ PL.part j) (PR.part i ∪ PR.part j)
          ≤ (frag (Gs k) X Y).sGraph ∧
        relDensity (graphOn G.edge X Y) (PL.part i) (PR.part j)
          ≤ (frag (Gs k) X Y).sGraph ∧
        relDensity (graphOn G.edge X Y) (PL.part j) (PR.part i)
          ≤ (frag (Gs k) X Y).sGraph ∧
        relDensity (graphOn G.edge X Y) (PL.part k) Y
          ≤ (frag (Gs i) X Y).sGraph + (frag (Gs j) X Y).sGraph ∧
        relDensity (graphOn G.edge X Y) X (PR.part k)
          ≤ (frag (Gs i) X Y).sGraph + (frag (Gs j) X Y).sGraph := by
  classical
  have hadm : (graphOn G.edge X Y).Admissible X Y :=
    ⟨fun a ha => ha, fun b hb => hb⟩
  have hnoIsoL : ∀ a ∈ (graphOn G.edge X Y).left,
      ∃ b ∈ (graphOn G.edge X Y).right, (graphOn G.edge X Y).edge a b = true := by
    have h := no_isolated_left_of_max_ratio (graphOn G.edge X Y) X Y hadm hmax hpos
    exact fun a ha => h a ha
  have hnoIsoR : ∀ b ∈ (graphOn G.edge X Y).right,
      ∃ a ∈ (graphOn G.edge X Y).left, (graphOn G.edge X Y).edge a b = true := by
    have h := no_isolated_right_of_max_ratio (graphOn G.edge X Y) X Y hadm hmax hpos
    exact fun b hb => h b hb
  have hX2 : ∀ a ∈ X, ∃ i j : Fin 3, i ≠ j ∧
      a ∈ (frag (Gs i) X Y).left ∧ a ∈ (frag (Gs j) X Y).left :=
    exists_two_covers_left (graphOn G.edge X Y) (fun t => frag (Gs t) X Y) hmono hnoIsoL hB
  have hY2 : ∀ b ∈ Y, ∃ i j : Fin 3, i ≠ j ∧
      b ∈ (frag (Gs i) X Y).right ∧ b ∈ (frag (Gs j) X Y).right :=
    exists_two_covers_right (graphOn G.edge X Y) (fun t => frag (Gs t) X Y) hmono hnoIsoR hA
  obtain ⟨PL⟩ := exists_threePartsL X (fun t => frag (Gs t) X Y) hX2
  obtain ⟨PR⟩ := exists_threePartsR Y (fun t => frag (Gs t) X Y) hY2
  refine ⟨PL, PR, ?_⟩
  intro i j k hij hki hkj
  have hYij : ∀ b ∈ Y, b ∈ (frag (Gs i) X Y).right ∨ b ∈ (frag (Gs j) X Y).right :=
    fun b hb => two_of_three (P := fun t => b ∈ (frag (Gs t) X Y).right) hij (hY2 b hb)
  have hXij : ∀ a ∈ X, a ∈ (frag (Gs i) X Y).left ∨ a ∈ (frag (Gs j) X Y).left :=
    fun a ha => two_of_three (P := fun t => a ∈ (frag (Gs t) X Y).left) hij (hX2 a ha)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact frag_sGraph_ge_density (graphOn G.edge X Y) (fun t => frag (Gs t) X Y) hmono
      (PL.part i ∪ PL.part j) (PR.part i ∪ PR.part j) k
      (part_union_left PL hki hkj) (part_union_right PR hki hkj)
  · exact frag_sGraph_ge_density (graphOn G.edge X Y) (fun t => frag (Gs t) X Y) hmono
      (PL.part i) (PR.part j) k
      (fun a ha => PL.other i a ha k hki) (fun b hb => PR.other j b hb k hkj)
  · exact frag_sGraph_ge_density (graphOn G.edge X Y) (fun t => frag (Gs t) X Y) hmono
      (PL.part j) (PR.part i) k
      (fun a ha => PL.other j a ha k hkj) (fun b hb => PR.other i b hb k hki)
  · exact row_bound (graphOn G.edge X Y) (fun t => frag (Gs t) X Y) hmono (PL.part k) Y
      (i := i) (j := j)
      (fun a ha => PL.other k a ha i (Ne.symm hki))
      (fun a ha => PL.other k a ha j (Ne.symm hkj)) hYij
  · exact col_bound (graphOn G.edge X Y) (fun t => frag (Gs t) X Y) hmono X (PR.part k)
      (i := i) (j := j)
      (fun b hb => PR.other k b hb i (Ne.symm hki))
      (fun b hb => PR.other k b hb j (Ne.symm hkj)) hXij

/-! ### Normalising the goal of the main case

The paper normalises `s(G)` to `1` by dividing by `|E|^2/(|A| |B|)`.  The two
lemmas below perform this reduction: the desired subadditivity becomes
`1 <= sum (s*(G_t))^chi` with `s*(G_t) = s(G_t) |A| |B| / |E|^2`. -/
theorem goal_normalised_iff (H : BipartiteGraph A B) (F : Fin 3 → BipartiteGraph A B)
    (X : Finset A) (Y : Finset B)
    (hs : H.sGraph = (H.edgeCount X Y : ℝ) ^ 2 / ((X.card : ℝ) * (Y.card : ℝ)))
    (hpos : 0 < H.sGraph) (χ : ℝ) :
    (H.sGraph ^ χ ≤ ∑ t, (F t).sGraph ^ χ) ↔
      1 ≤ ∑ t, ((F t).sGraph * ((X.card : ℝ) * (Y.card : ℝ))
        / (H.edgeCount X Y : ℝ) ^ 2) ^ χ := by
  classical
  set e : ℝ := (H.edgeCount X Y : ℝ) with he
  set ab : ℝ := (X.card : ℝ) * (Y.card : ℝ) with hab
  have hpos' : 0 < e ^ 2 / ab := hs ▸ hpos
  have he2 : 0 < e ^ 2 := by
    rcases div_pos_iff.mp hpos' with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exact absurd h1 (not_lt.mpr (sq_nonneg _))
  have hab0 : 0 < ab := by
    rcases div_pos_iff.mp hpos' with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact h2
    · exact absurd h2 (not_lt.mpr (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  have hec : e ≠ 0 := by
    intro h
    rw [h] at he2
    norm_num at he2
  have hXc : (X.card : ℝ) ≠ 0 := by
    intro h
    rw [hab, h, zero_mul] at hab0
    exact lt_irrefl 0 hab0
  have hYc : (Y.card : ℝ) ≠ 0 := by
    intro h
    rw [hab, h, mul_zero] at hab0
    exact lt_irrefl 0 hab0
  have hS : 0 < H.sGraph ^ χ := Real.rpow_pos_of_pos hpos χ
  have hkey : ∀ t, (F t).sGraph = ((F t).sGraph * ab / e ^ 2) * H.sGraph := by
    intro t
    rw [hs]
    field_simp
  have hsum : (∑ t, (F t).sGraph ^ χ)
      = (∑ t, ((F t).sGraph * ab / e ^ 2) ^ χ) * H.sGraph ^ χ := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t _
    have hu : (0:ℝ) ≤ (F t).sGraph * ab / e ^ 2 :=
      div_nonneg (mul_nonneg (BipartiteGraph.sGraph_nonneg (F t)) hab0.le) (by positivity)
    calc (F t).sGraph ^ χ = (((F t).sGraph * ab / e ^ 2) * H.sGraph) ^ χ := by
          conv_lhs => rw [hkey t]
      _ = ((F t).sGraph * ab / e ^ 2) ^ χ * H.sGraph ^ χ := Real.mul_rpow hu hpos.le
  have hgoal : H.sGraph ^ χ ≤ ∑ t, (F t).sGraph ^ χ ↔
      1 ≤ ∑ t, ((F t).sGraph * ab / e ^ 2) ^ χ := by
    rw [hsum]
    constructor
    · intro h
      have h' : H.sGraph ^ χ * 1 ≤ H.sGraph ^ χ * (∑ t, ((F t).sGraph * ab / e ^ 2) ^ χ) := by
        simpa [mul_comm] using h
      exact (mul_le_mul_iff_of_pos_left hS).mp h'
    · intro h
      have := mul_le_mul_of_nonneg_left h hS.le
      simpa [mul_comm] using this
  simpa [he, hab] using hgoal

set_option maxHeartbeats 400000 in
/-- The goal of the main case written with the paper's normalised densities:
after the normalisation `s(G) = |E|^2 / (|A| |B|)` the desired inequality is
`1 <= sum (s*(G_t))^chi`. -/
theorem main_case_goal_normalised
    (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (Gs : Fin 3 → BipartiteGraph A B)
    (hmax : (graphOn G.edge X Y).ratio X Y = (graphOn G.edge X Y).sGraph)
    (hpos : 0 < (graphOn G.edge X Y).ratio X Y) (χ : ℝ) :
    ((graphOn G.edge X Y).sGraph ^ χ ≤ ∑ t, (frag (Gs t) X Y).sGraph ^ χ) ↔
      1 ≤ ∑ t, ((frag (Gs t) X Y).sGraph * ((X.card : ℝ) * (Y.card : ℝ))
        / (G.edgeCount X Y : ℝ) ^ 2) ^ χ := by
  have hadm : (graphOn G.edge X Y).Admissible X Y := ⟨fun a ha => ha, fun b hb => hb⟩
  have hgs : (graphOn G.edge X Y).sGraph =
      ((graphOn G.edge X Y).edgeCount X Y : ℝ) ^ 2 / ((X.card : ℝ) * (Y.card : ℝ)) := by
    rw [← hmax, ratio_of_admissible _ hadm]
  have h := goal_normalised_iff (graphOn G.edge X Y) (fun t => frag (Gs t) X Y) X Y hgs
    (by rwa [← hmax]) χ
  rw [edgeCount_graphOn_self'] at h
  exact h

/-! ### Estimates (4.2)--(4.5) in the paper's normalised notation

`normSGraph` is the paper's `s*(G')`, and the estimates above become the
inequalities (4.2)--(4.5) literally: each of `H_k`, `Q_k` is bounded by
`s*(G_k)`, and `F_ij` by `s*(G_i) + s*(G_j)`. -/
/-- The normalising factor `|X| |Y| / |E(X,Y)|^2` of the paper. -/
noncomputable def normScale (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B) : ℝ :=
  ((X.card : ℝ) * (Y.card : ℝ)) / (G.edgeCount X Y : ℝ) ^ 2

/-- The normalised density `s*(G') = s(G') |X| |Y| / |E(X,Y)|^2`. -/
noncomputable def normSGraph (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (F : BipartiteGraph A B) : ℝ := F.sGraph * normScale G X Y

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem normScale_nonneg (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B) :
    0 ≤ normScale G X Y :=
  div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by positivity)

set_option maxHeartbeats 800000 in
theorem main_case_normalised_estimates
    (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (Gs : Fin 3 → BipartiteGraph A B)
    (hmono : IsMonotoneCover (graphOn G.edge X Y) (fun t => frag (Gs t) X Y))
    (hmax : (graphOn G.edge X Y).ratio X Y = (graphOn G.edge X Y).sGraph)
    (hpos : 0 < (graphOn G.edge X Y).ratio X Y)
    (hB : ∀ i, ¬ (↑Y : Set B) ⊆ (frag (Gs i) X Y).right)
    (hA : ∀ i, ¬ (↑X : Set A) ⊆ (frag (Gs i) X Y).left) :
    ∃ (PL : ThreePartsL X (fun t => frag (Gs t) X Y))
      (PR : ThreePartsR Y (fun t => frag (Gs t) X Y)),
      ∀ i j k : Fin 3, i ≠ j → k ≠ i → k ≠ j →
        relDensity (graphOn G.edge X Y) (PL.part i ∪ PL.part j) (PR.part i ∪ PR.part j)
            * normScale G X Y ≤ normSGraph G X Y (frag (Gs k) X Y) ∧
        relDensity (graphOn G.edge X Y) (PL.part i) (PR.part j)
            * normScale G X Y ≤ normSGraph G X Y (frag (Gs k) X Y) ∧
        relDensity (graphOn G.edge X Y) (PL.part j) (PR.part i)
            * normScale G X Y ≤ normSGraph G X Y (frag (Gs k) X Y) ∧
        relDensity (graphOn G.edge X Y) (PL.part k) Y * normScale G X Y
          ≤ normSGraph G X Y (frag (Gs i) X Y) + normSGraph G X Y (frag (Gs j) X Y) ∧
        relDensity (graphOn G.edge X Y) X (PR.part k) * normScale G X Y
          ≤ normSGraph G X Y (frag (Gs i) X Y) + normSGraph G X Y (frag (Gs j) X Y) := by
  obtain ⟨PL, PR, h⟩ := main_case_estimates G X Y Gs hmono hmax hpos hB hA
  refine ⟨PL, PR, ?_⟩
  intro i j k hij hki hkj
  obtain ⟨h1, h2, h3, h4, h5⟩ := h i j k hij hki hkj
  have hs := normScale_nonneg (G := G) X Y
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right h1 hs
  · exact mul_le_mul_of_nonneg_right h2 hs
  · exact mul_le_mul_of_nonneg_right h3 hs
  · have := mul_le_mul_of_nonneg_right h4 hs
    simpa [normSGraph, add_mul] using this
  · have := mul_le_mul_of_nonneg_right h5 hs
    simpa [normSGraph, add_mul] using this
/-! ### Edge counts over unions

To normalise the estimates (4.2)--(4.5) we need the edge count of a box that is
a union of two boxes, and the cardinality of such a union. -/

theorem product_union_parts (s s' : Finset A) (t : Finset B) :
    (s ∪ s').product t = s.product t ∪ s'.product t := by
  ext q
  rw [Finset.product_eq_sprod, Finset.product_eq_sprod, Finset.product_eq_sprod]
  simp [Finset.mem_product, Finset.mem_union]

theorem product_union_parts_right (s : Finset A) (t t' : Finset B) :
    s.product (t ∪ t') = s.product t ∪ s.product t' := by
  ext q
  rw [Finset.product_eq_sprod, Finset.product_eq_sprod, Finset.product_eq_sprod]
  simp [Finset.mem_product, Finset.mem_union]

theorem edgeCount_union_left (H : BipartiteGraph A B) (S1 S2 : Finset A) (T : Finset B)
    (h : Disjoint S1 S2) :
    H.edgeCount (S1 ∪ S2) T = H.edgeCount S1 T + H.edgeCount S2 T := by
  classical
  unfold BipartiteGraph.edgeCount
  rw [product_union_parts, Finset.filter_union]
  refine Finset.card_union_of_disjoint ?_
  rw [Finset.disjoint_left]
  intro q h1 h2
  rw [Finset.mem_filter] at h1 h2
  exact (Finset.disjoint_left.mp h (Finset.mem_product.mp h1.1).1)
    (Finset.mem_product.mp h2.1).1

theorem edgeCount_union_right (H : BipartiteGraph A B) (S : Finset A) (T1 T2 : Finset B)
    (h : Disjoint T1 T2) :
    H.edgeCount S (T1 ∪ T2) = H.edgeCount S T1 + H.edgeCount S T2 := by
  classical
  unfold BipartiteGraph.edgeCount
  rw [product_union_parts_right, Finset.filter_union]
  refine Finset.card_union_of_disjoint ?_
  rw [Finset.disjoint_left]
  intro q h1 h2
  rw [Finset.mem_filter] at h1 h2
  exact (Finset.disjoint_left.mp h (Finset.mem_product.mp h1.1).2)
    (Finset.mem_product.mp h2.1).2

/-- The relative density of a box, multiplied by the normalisation factor, in
terms of the normalised edge count and the normalised sizes. -/
theorem relDensity_mul_normScale (H : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (S : Finset A) (T : Finset B) (hX : 0 < X.card) (hY : 0 < Y.card)
    (hS : 0 < S.card) (hT : 0 < T.card) (hE : 0 < H.edgeCount X Y) :
    relDensity H S T * normScale H X Y =
      ((H.edgeCount S T : ℝ) / (H.edgeCount X Y : ℝ)) ^ 2 /
        (((S.card : ℝ) / (X.card : ℝ)) * ((T.card : ℝ) / (Y.card : ℝ))) := by
  have hX0 : (X.card : ℝ) ≠ 0 := by
    have : (0:ℝ) < (X.card : ℝ) := by exact_mod_cast hX
    exact this.ne'
  have hY0 : (Y.card : ℝ) ≠ 0 := by
    have : (0:ℝ) < (Y.card : ℝ) := by exact_mod_cast hY
    exact this.ne'
  have hS0 : (S.card : ℝ) ≠ 0 := by
    have : (0:ℝ) < (S.card : ℝ) := by exact_mod_cast hS
    exact this.ne'
  have hT0 : (T.card : ℝ) ≠ 0 := by
    have : (0:ℝ) < (T.card : ℝ) := by exact_mod_cast hT
    exact this.ne'
  have hE0 : (H.edgeCount X Y : ℝ) ≠ 0 := by
    have : (0:ℝ) < (H.edgeCount X Y : ℝ) := by exact_mod_cast hE
    exact this.ne'
  unfold relDensity normScale
  field_simp

/-- The relative density of a union box, multiplied by the normalisation
factor, written with the four corner edge counts and the two side lengths. -/
theorem relDensity_union_mul_normScale (H : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (S1 S2 : Finset A) (T1 T2 : Finset B) (hS : Disjoint S1 S2) (hT : Disjoint T1 T2)
    (hX : 0 < X.card) (hY : 0 < Y.card)
    (hSn : 0 < (S1 ∪ S2).card) (hTn : 0 < (T1 ∪ T2).card) (hE : 0 < H.edgeCount X Y) :
    relDensity H (S1 ∪ S2) (T1 ∪ T2) * normScale H X Y =
      (((H.edgeCount S1 T1 + H.edgeCount S1 T2 + H.edgeCount S2 T1
          + H.edgeCount S2 T2 : ℕ) : ℝ) / (H.edgeCount X Y : ℝ)) ^ 2 /
        (((((S1.card + S2.card : ℕ) : ℝ) / (X.card : ℝ))) *
          ((((T1.card + T2.card : ℕ) : ℝ) / (Y.card : ℝ)))) := by
  have hcS : ((S1 ∪ S2).card : ℝ) = ((S1.card + S2.card : ℕ) : ℝ) := by
    rw [Finset.card_union_of_disjoint hS]
  have hcT : ((T1 ∪ T2).card : ℝ) = ((T1.card + T2.card : ℕ) : ℝ) := by
    rw [Finset.card_union_of_disjoint hT]
  have hcE : ((H.edgeCount (S1 ∪ S2) (T1 ∪ T2) : ℕ) : ℝ) =
      ((H.edgeCount S1 T1 + H.edgeCount S1 T2 + H.edgeCount S2 T1
        + H.edgeCount S2 T2 : ℕ) : ℝ) := by
    rw [edgeCount_union_left H S1 S2 (T1 ∪ T2) hS,
      edgeCount_union_right H S1 T1 T2 hT, edgeCount_union_right H S2 T1 T2 hT]
    push_cast
    ring
  have := relDensity_mul_normScale H X Y (S1 ∪ S2) (T1 ∪ T2) hX hY hSn hTn hE
  rw [this, hcS, hcT, hcE]

/-! ### The partition sums

Each of the three parts of `ThreePartsL` (resp. `ThreePartsR`) is nonempty in
the main case, the parts are disjoint, and they cover the left (resp. right)
part.  Consequently the normalised sizes sum to `1`. -/

theorem sum_card_part_L {F : Fin 3 → BipartiteGraph A B} {X : Finset A}
    (PL : ThreePartsL X F) : ∑ i, (PL.part i).card = X.card := by
  have h01 : Disjoint (PL.part 0) (PL.part 1) := PL.disjoint 0 1 (by decide)
  have h02 : Disjoint (PL.part 0) (PL.part 2) := PL.disjoint 0 2 (by decide)
  have h12 : Disjoint (PL.part 1) (PL.part 2) := PL.disjoint 1 2 (by decide)
  have h012 : Disjoint (PL.part 0 ∪ PL.part 1) (PL.part 2) := by
    rw [Finset.disjoint_union_left]
    exact ⟨h02, h12⟩
  have hunion : PL.part 0 ∪ PL.part 1 ∪ PL.part 2 = X := by
    ext a
    constructor
    · intro ha
      simp only [Finset.mem_union] at ha
      rcases ha with (ha | ha) | ha
      · exact PL.subset 0 ha
      · exact PL.subset 1 ha
      · exact PL.subset 2 ha
    · intro ha
      obtain ⟨i, hi⟩ := PL.cover a ha
      fin_cases i
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hi)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)
      · exact Finset.mem_union_right _ hi
  calc ∑ i, (PL.part i).card
      = (PL.part 0).card + (PL.part 1).card + (PL.part 2).card := by
        rw [Fin.sum_univ_three]
    _ = (PL.part 0 ∪ PL.part 1).card + (PL.part 2).card := by
        rw [Finset.card_union_of_disjoint h01]
    _ = (PL.part 0 ∪ PL.part 1 ∪ PL.part 2).card := by
        rw [Finset.card_union_of_disjoint h012]
    _ = X.card := by rw [hunion]

theorem sum_card_part_R {F : Fin 3 → BipartiteGraph A B} {Y : Finset B}
    (PR : ThreePartsR Y F) : ∑ j, (PR.part j).card = Y.card := by
  have h01 : Disjoint (PR.part 0) (PR.part 1) := PR.disjoint 0 1 (by decide)
  have h02 : Disjoint (PR.part 0) (PR.part 2) := PR.disjoint 0 2 (by decide)
  have h12 : Disjoint (PR.part 1) (PR.part 2) := PR.disjoint 1 2 (by decide)
  have h012 : Disjoint (PR.part 0 ∪ PR.part 1) (PR.part 2) := by
    rw [Finset.disjoint_union_left]
    exact ⟨h02, h12⟩
  have hunion : PR.part 0 ∪ PR.part 1 ∪ PR.part 2 = Y := by
    ext b
    constructor
    · intro hb
      simp only [Finset.mem_union] at hb
      rcases hb with (hb | hb) | hb
      · exact PR.subset 0 hb
      · exact PR.subset 1 hb
      · exact PR.subset 2 hb
    · intro hb
      obtain ⟨j, hj⟩ := PR.cover b hb
      fin_cases j
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hj)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hj)
      · exact Finset.mem_union_right _ hj
  calc ∑ j, (PR.part j).card
      = (PR.part 0).card + (PR.part 1).card + (PR.part 2).card := by
        rw [Fin.sum_univ_three]
    _ = (PR.part 0 ∪ PR.part 1).card + (PR.part 2).card := by
        rw [Finset.card_union_of_disjoint h01]
    _ = (PR.part 0 ∪ PR.part 1 ∪ PR.part 2).card := by
        rw [Finset.card_union_of_disjoint h012]
    _ = Y.card := by rw [hunion]

theorem partL_nonempty {F : Fin 3 → BipartiteGraph A B} {X : Finset A}
    (PL : ThreePartsL X F) (h : ∀ i, ¬ (↑X : Set A) ⊆ (F i).left) (i : Fin 3) :
    (PL.part i).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  apply h i
  intro a ha
  have haX : a ∈ X := ha
  obtain ⟨j, hj⟩ := PL.cover a haX
  have hji : j ≠ i := by
    rintro rfl
    rw [hne] at hj
    simp at hj
  exact PL.other j a hj i (Ne.symm hji)

theorem partR_nonempty {F : Fin 3 → BipartiteGraph A B} {Y : Finset B}
    (PR : ThreePartsR Y F) (h : ∀ i, ¬ (↑Y : Set B) ⊆ (F i).right) (i : Fin 3) :
    (PR.part i).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  apply h i
  intro b hb
  have hbY : b ∈ Y := hb
  obtain ⟨j, hj⟩ := PR.cover b hbY
  have hji : j ≠ i := by
    rintro rfl
    rw [hne] at hj
    simp at hj
  exact PR.other j b hj i (Ne.symm hji)

theorem edgeCount_eq_sum_three_right (H : BipartiteGraph A B) (S : Finset A)
    {F : Fin 3 → BipartiteGraph A B} {Y : Finset B} (PR : ThreePartsR Y F) :
    H.edgeCount S Y = ∑ j, H.edgeCount S (PR.part j) := by
  have h01 : Disjoint (PR.part 0) (PR.part 1) := PR.disjoint 0 1 (by decide)
  have h02 : Disjoint (PR.part 0) (PR.part 2) := PR.disjoint 0 2 (by decide)
  have h12 : Disjoint (PR.part 1) (PR.part 2) := PR.disjoint 1 2 (by decide)
  have h012 : Disjoint (PR.part 0 ∪ PR.part 1) (PR.part 2) := by
    rw [Finset.disjoint_union_left]
    exact ⟨h02, h12⟩
  have hunion : PR.part 0 ∪ PR.part 1 ∪ PR.part 2 = Y := by
    ext b
    constructor
    · intro hb
      simp only [Finset.mem_union] at hb
      rcases hb with (hb | hb) | hb
      · exact PR.subset 0 hb
      · exact PR.subset 1 hb
      · exact PR.subset 2 hb
    · intro hb
      obtain ⟨j, hj⟩ := PR.cover b hb
      fin_cases j
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hj)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hj)
      · exact Finset.mem_union_right _ hj
  calc H.edgeCount S Y = H.edgeCount S (PR.part 0 ∪ PR.part 1 ∪ PR.part 2) := by
        rw [hunion]
    _ = H.edgeCount S (PR.part 0 ∪ PR.part 1) + H.edgeCount S (PR.part 2) := by
        rw [edgeCount_union_right H S _ _ h012]
    _ = (H.edgeCount S (PR.part 0) + H.edgeCount S (PR.part 1))
          + H.edgeCount S (PR.part 2) := by
        rw [edgeCount_union_right H S _ _ h01]
    _ = ∑ j, H.edgeCount S (PR.part j) := by
        rw [Fin.sum_univ_three]

theorem edgeCount_eq_sum_three_left (H : BipartiteGraph A B)
    {F : Fin 3 → BipartiteGraph A B} {X : Finset A} (PL : ThreePartsL X F) (T : Finset B) :
    H.edgeCount X T = ∑ i, H.edgeCount (PL.part i) T := by
  have h01 : Disjoint (PL.part 0) (PL.part 1) := PL.disjoint 0 1 (by decide)
  have h02 : Disjoint (PL.part 0) (PL.part 2) := PL.disjoint 0 2 (by decide)
  have h12 : Disjoint (PL.part 1) (PL.part 2) := PL.disjoint 1 2 (by decide)
  have h012 : Disjoint (PL.part 0 ∪ PL.part 1) (PL.part 2) := by
    rw [Finset.disjoint_union_left]
    exact ⟨h02, h12⟩
  have hunion : PL.part 0 ∪ PL.part 1 ∪ PL.part 2 = X := by
    ext a
    constructor
    · intro ha
      simp only [Finset.mem_union] at ha
      rcases ha with (ha | ha) | ha
      · exact PL.subset 0 ha
      · exact PL.subset 1 ha
      · exact PL.subset 2 ha
    · intro ha
      obtain ⟨i, hi⟩ := PL.cover a ha
      fin_cases i
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hi)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hi)
      · exact Finset.mem_union_right _ hi
  calc H.edgeCount X T = H.edgeCount (PL.part 0 ∪ PL.part 1 ∪ PL.part 2) T := by
        rw [hunion]
    _ = H.edgeCount (PL.part 0 ∪ PL.part 1) T + H.edgeCount (PL.part 2) T := by
        rw [edgeCount_union_left H _ _ T h012]
    _ = (H.edgeCount (PL.part 0) T + H.edgeCount (PL.part 1) T)
          + H.edgeCount (PL.part 2) T := by
        rw [edgeCount_union_left H _ _ T h01]
    _ = ∑ i, H.edgeCount (PL.part i) T := by
        rw [Fin.sum_univ_three]

theorem sum_edgeCount_parts (H : BipartiteGraph A B) {F : Fin 3 → BipartiteGraph A B}
    {X : Finset A} {Y : Finset B} (PL : ThreePartsL X F) (PR : ThreePartsR Y F) :
    ∑ i, ∑ j, H.edgeCount (PL.part i) (PR.part j) = H.edgeCount X Y := by
  rw [show ∑ i, ∑ j, H.edgeCount (PL.part i) (PR.part j)
      = ∑ i, H.edgeCount (PL.part i) Y from
    Finset.sum_congr rfl (fun i _ => (edgeCount_eq_sum_three_right H (PL.part i) PR).symm)]
  exact (edgeCount_eq_sum_three_left H PL Y).symm

/-! ### The normalised numeric data of the main case

`mA X PL i = |N_i| / |X|`, `mB Y PR j = |P_j| / |Y|`,
`mE H X Y PL PR i j = |E ∩ (N_i × P_j)| / |E|` and
`mS G X Y Gs k = s*(G_k)`.  These are the quantities `a_i`, `b_i`, `e_ij`
and `s_*(G_k)` of the paper. -/

noncomputable def mA {F : Fin 3 → BipartiteGraph A B} (X : Finset A) (PL : ThreePartsL X F)
    (i : Fin 3) : ℝ := ((PL.part i).card : ℝ) / (X.card : ℝ)

noncomputable def mB {F : Fin 3 → BipartiteGraph A B} (Y : Finset B) (PR : ThreePartsR Y F)
    (j : Fin 3) : ℝ := ((PR.part j).card : ℝ) / (Y.card : ℝ)

noncomputable def mE (H : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    {F : Fin 3 → BipartiteGraph A B} (PL : ThreePartsL X F) (PR : ThreePartsR Y F)
    (i j : Fin 3) : ℝ :=
  (H.edgeCount (PL.part i) (PR.part j) : ℝ) / (H.edgeCount X Y : ℝ)

noncomputable def mS (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (Gs : Fin 3 → BipartiteGraph A B) (k : Fin 3) : ℝ :=
  (frag (Gs k) X Y).sGraph * normScale G X Y

theorem mS_nonneg (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    (Gs : Fin 3 → BipartiteGraph A B) (k : Fin 3) : 0 ≤ mS G X Y Gs k := by
  unfold mS
  exact mul_nonneg (BipartiteGraph.sGraph_nonneg _) (normScale_nonneg G X Y)

theorem mE_add_four (H : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    {F : Fin 3 → BipartiteGraph A B} (PL : ThreePartsL X F) (PR : ThreePartsR Y F)
    (i j : Fin 3) :
    ((H.edgeCount (PL.part i) (PR.part i) + H.edgeCount (PL.part i) (PR.part j)
        + H.edgeCount (PL.part j) (PR.part i) + H.edgeCount (PL.part j) (PR.part j) : ℕ) : ℝ)
        / (H.edgeCount X Y : ℝ)
      = mE H X Y PL PR i i + mE H X Y PL PR i j
        + mE H X Y PL PR j i + mE H X Y PL PR j j := by
  simp only [mE]
  push_cast
  ring

theorem mA_add {F : Fin 3 → BipartiteGraph A B} {X : Finset A} (PL : ThreePartsL X F)
    {i j : Fin 3} (hij : i ≠ j) :
    (((PL.part i).card + (PL.part j).card : ℕ) : ℝ) / (X.card : ℝ)
      = mA X PL i + mA X PL j := by
  simp only [mA]
  rw [Nat.cast_add]
  ring

theorem mB_add {F : Fin 3 → BipartiteGraph A B} {Y : Finset B} (PR : ThreePartsR Y F)
    {i j : Fin 3} (hij : i ≠ j) :
    (((PR.part i).card + (PR.part j).card : ℕ) : ℝ) / (Y.card : ℝ)
      = mB Y PR i + mB Y PR j := by
  simp only [mB]
  rw [Nat.cast_add]
  ring

theorem relDensity_union_eq (H : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    {F : Fin 3 → BipartiteGraph A B} (PL : ThreePartsL X F) (PR : ThreePartsR Y F)
    {i j : Fin 3} (hij : i ≠ j) (hX : 0 < X.card) (hY : 0 < Y.card)
    (hSn : 0 < (PL.part i ∪ PL.part j).card) (hTn : 0 < (PR.part i ∪ PR.part j).card)
    (hE : 0 < H.edgeCount X Y) :
    relDensity H (PL.part i ∪ PL.part j) (PR.part i ∪ PR.part j) * normScale H X Y
      = (mE H X Y PL PR i i + mE H X Y PL PR i j + mE H X Y PL PR j i
          + mE H X Y PL PR j j) ^ 2
        / ((mA X PL i + mA X PL j) * (mB Y PR i + mB Y PR j)) := by
  rw [relDensity_union_mul_normScale H X Y _ _ _ _ (PL.disjoint i j hij)
    (PR.disjoint i j hij) hX hY hSn hTn hE, mE_add_four, mA_add PL hij, mB_add PR hij]

theorem relDensity_pair_eq (H : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    {F : Fin 3 → BipartiteGraph A B} (PL : ThreePartsL X F) (PR : ThreePartsR Y F)
    (i j : Fin 3) (hX : 0 < X.card) (hY : 0 < Y.card)
    (hSi : 0 < (PL.part i).card) (hTj : 0 < (PR.part j).card) (hE : 0 < H.edgeCount X Y) :
    relDensity H (PL.part i) (PR.part j) * normScale H X Y
      = (mE H X Y PL PR i j) ^ 2 / (mA X PL i * mB Y PR j) := by
  rw [relDensity_mul_normScale H X Y (PL.part i) (PR.part j) hX hY hSi hTj hE]
  simp only [mE, mA, mB]

theorem relDensity_row_eq (H : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    {F : Fin 3 → BipartiteGraph A B} (PL : ThreePartsL X F) (PR : ThreePartsR Y F)
    (k : Fin 3) (hX : 0 < X.card) (hY : 0 < Y.card)
    (hSk : 0 < (PL.part k).card) (hE : 0 < H.edgeCount X Y) :
    relDensity H (PL.part k) Y * normScale H X Y
      = (mE H X Y PL PR k 0 + mE H X Y PL PR k 1 + mE H X Y PL PR k 2) ^ 2 / (mA X PL k) := by
  rw [relDensity_mul_normScale H X Y (PL.part k) Y hX hY hSk hY hE,
    edgeCount_eq_sum_three_right H (PL.part k) PR]
  simp only [mE, mA, Fin.sum_univ_three]
  field_simp
  push_cast
  ring

theorem relDensity_col_eq (H : BipartiteGraph A B) (X : Finset A) (Y : Finset B)
    {F : Fin 3 → BipartiteGraph A B} (PL : ThreePartsL X F) (PR : ThreePartsR Y F)
    (k : Fin 3) (hX : 0 < X.card) (hY : 0 < Y.card)
    (hPk : 0 < (PR.part k).card) (hE : 0 < H.edgeCount X Y) :
    relDensity H X (PR.part k) * normScale H X Y
      = (mE H X Y PL PR 0 k + mE H X Y PL PR 1 k + mE H X Y PL PR 2 k) ^ 2 / (mB Y PR k) := by
  rw [relDensity_mul_normScale H X Y X (PR.part k) hX hY hX hPk hE,
    edgeCount_eq_sum_three_left H PL (PR.part k)]
  simp only [mE, mB, Fin.sum_univ_three]
  field_simp
  push_cast
  ring

/-! ### The numeric core of the main case

The paper's main case reduces, after density normalisation, to the following
statement about real numbers.  The hypotheses are exactly the normalised
estimates (4.2)--(4.5) rewritten with `a_i = b_i` after averaging the two sides
of the bipartition. -/
def MainNumeric (χ : ℝ) : Prop :=
  ∀ (s a b : Fin 3 → ℝ) (e : Fin 3 → Fin 3 → ℝ),
    (∀ i, 0 < a i) → (∑ i, a i = 1) →
    (∀ i, 0 < b i) → (∑ i, b i = 1) →
    (∀ i j, 0 ≤ e i j) → (∑ i, ∑ j, e i j = 1) →
    (∀ i, 0 ≤ s i) →
    (∀ i j k, i ≠ j → k ≠ i → k ≠ j →
      s k ≥ (e i i + e i j + e j i + e j j) ^ 2 / ((a i + a j) * (b i + b j))) →
    (∀ i j k, i ≠ j → k ≠ i → k ≠ j →
      s k ≥ (e i j) ^ 2 / (a i * b j)) →
    (∀ i j k, i ≠ j → k ≠ i → k ≠ j →
      s k ≥ (e j i) ^ 2 / (a j * b i)) →
    (∀ i j k, i ≠ j → k ≠ i → k ≠ j →
      s i + s j ≥ (e k 0 + e k 1 + e k 2) ^ 2 / a k) →
    (∀ i j k, i ≠ j → k ≠ i → k ≠ j →
      s i + s j ≥ (e 0 k + e 1 k + e 2 k) ^ 2 / b k) →
    1 ≤ ∑ i, (s i) ^ χ

theorem mainCase_of_numeric {χ : ℝ} (hnum : MainNumeric χ) : MainCase χ := by
  intro A₁ B₁ iA iB dA dB G X Y Gs hmono hmax hpos hB hA
  classical
  obtain ⟨PL, PR, hb⟩ := main_case_normalised_estimates G X Y Gs hmono hmax hpos hB hA
  have hEpos : 0 < (graphOn G.edge X Y).edgeCount X Y := by
    by_contra h
    have hzero : (graphOn G.edge X Y).edgeCount X Y = 0 := Nat.eq_zero_of_not_pos h
    have hadm : (graphOn G.edge X Y).Admissible X Y := ⟨fun a ha => ha, fun b hb => hb⟩
    rw [ratio_of_admissible _ hadm, hzero] at hpos
    simp at hpos
  have hXpos : 0 < X.card := by
    obtain ⟨q, hq⟩ := Finset.card_pos.mp hEpos
    rw [Finset.mem_filter] at hq
    exact Finset.card_pos.mpr ⟨q.1, (Finset.mem_product.mp hq.1).1⟩
  have hYpos : 0 < Y.card := by
    obtain ⟨q, hq⟩ := Finset.card_pos.mp hEpos
    rw [Finset.mem_filter] at hq
    exact Finset.card_pos.mpr ⟨q.2, (Finset.mem_product.mp hq.1).2⟩
  have hpa : ∀ i, 0 < mA X PL i := by
    intro i
    have hc : 0 < (PL.part i).card := Finset.card_pos.mpr (partL_nonempty PL hA i)
    unfold mA
    exact div_pos (by exact_mod_cast hc) (by exact_mod_cast hXpos)
  have hpb : ∀ i, 0 < mB Y PR i := by
    intro i
    have hc : 0 < (PR.part i).card := Finset.card_pos.mpr (partR_nonempty PR hB i)
    unfold mB
    exact div_pos (by exact_mod_cast hc) (by exact_mod_cast hYpos)
  have hsa : ∑ i, mA X PL i = 1 := by
    simp only [mA]
    rw [← Finset.sum_div,
      show (∑ i, ((PL.part i).card : ℝ)) = (X.card : ℝ) from by
        rw [← Nat.cast_sum, sum_card_part_L]]
    exact div_self (by exact_mod_cast hXpos.ne')
  have hsb : ∑ i, mB Y PR i = 1 := by
    simp only [mB]
    rw [← Finset.sum_div,
      show (∑ i, ((PR.part i).card : ℝ)) = (Y.card : ℝ) from by
        rw [← Nat.cast_sum, sum_card_part_R]]
    exact div_self (by exact_mod_cast hYpos.ne')
  have hee : ∀ i j, 0 ≤ mE (graphOn G.edge X Y) X Y PL PR i j := by
    intro i j
    unfold mE
    positivity
  have hse : ∑ i, ∑ j, mE (graphOn G.edge X Y) X Y PL PR i j = 1 := by
    have hc : ((∑ i, ∑ j, (graphOn G.edge X Y).edgeCount (PL.part i) (PR.part j) : ℕ) : ℝ)
        = ∑ i, ∑ j, ((graphOn G.edge X Y).edgeCount (PL.part i) (PR.part j) : ℝ) := by
      push_cast
      ring
    simp only [mE]
    simp_rw [← Finset.sum_div]
    rw [← hc, sum_edgeCount_parts]
    exact div_self (by exact_mod_cast hEpos.ne')
  have hss : ∀ i, 0 ≤ mS G X Y Gs i := fun i => mS_nonneg G X Y Gs i
  have hscale : normScale G X Y = normScale (graphOn G.edge X Y) X Y := by
    simp only [normScale, edgeCount_graphOn_self']
  rw [main_case_goal_normalised G X Y Gs hmax hpos χ]
  have hmain := hnum (fun i => mS G X Y Gs i) (fun i => mA X PL i) (fun i => mB Y PR i)
    (fun i j => mE (graphOn G.edge X Y) X Y PL PR i j) hpa hsa hpb hsb hee hse hss ?_ ?_ ?_ ?_ ?_
  · simpa only [mS, normScale, mul_div_assoc] using hmain
  · intro i j k hij hki hkj
    have h1 := (hb i j k hij hki hkj).1
    have hSn : 0 < (PL.part i ∪ PL.part j).card :=
      Finset.card_pos.mpr ((partL_nonempty PL hA i).mono (Finset.subset_union_left))
    have hTn : 0 < (PR.part i ∪ PR.part j).card :=
      Finset.card_pos.mpr ((partR_nonempty PR hB i).mono (Finset.subset_union_left))
    rw [hscale] at h1
    rw [relDensity_union_eq (graphOn G.edge X Y) X Y PL PR hij hXpos hYpos hSn hTn hEpos] at h1
    simpa [mS, normSGraph] using h1
  · intro i j k hij hki hkj
    have h1 := (hb i j k hij hki hkj).2.1
    have hSi : 0 < (PL.part i).card := Finset.card_pos.mpr (partL_nonempty PL hA i)
    have hTj : 0 < (PR.part j).card := Finset.card_pos.mpr (partR_nonempty PR hB j)
    rw [hscale] at h1
    rw [relDensity_pair_eq (graphOn G.edge X Y) X Y PL PR i j hXpos hYpos hSi hTj hEpos] at h1
    simpa [mS, normSGraph] using h1
  · intro i j k hij hki hkj
    have h1 := (hb i j k hij hki hkj).2.2.1
    have hSj : 0 < (PL.part j).card := Finset.card_pos.mpr (partL_nonempty PL hA j)
    have hTi : 0 < (PR.part i).card := Finset.card_pos.mpr (partR_nonempty PR hB i)
    rw [hscale] at h1
    rw [relDensity_pair_eq (graphOn G.edge X Y) X Y PL PR j i hXpos hYpos hSj hTi hEpos] at h1
    simpa [mS, normSGraph] using h1
  · intro i j k hij hki hkj
    have h1 := (hb i j k hij hki hkj).2.2.2.1
    have hSk : 0 < (PL.part k).card := Finset.card_pos.mpr (partL_nonempty PL hA k)
    rw [hscale] at h1
    rw [relDensity_row_eq (graphOn G.edge X Y) X Y PL PR k hXpos hYpos hSk hEpos] at h1
    simpa [mS, normSGraph, add_comm] using h1
  · intro i j k hij hki hkj
    have h1 := (hb i j k hij hki hkj).2.2.2.2
    have hPk : 0 < (PR.part k).card := Finset.card_pos.mpr (partR_nonempty PR hB k)
    rw [hscale] at h1
    rw [relDensity_col_eq (graphOn G.edge X Y) X Y PL PR k hXpos hYpos hPk hEpos] at h1
    simpa [mS, normSGraph, add_comm] using h1

/-! ### Elementary inequalities for the numeric core -/

theorem four_mul_le_sq (a b c d : ℝ) :
    (a + c) * (b + d) ≤ ((a + b + c + d) / 2) ^ 2 := by
  nlinarith [sq_nonneg (a + c - b - d)]

theorem sq_sqrt_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a + Real.sqrt b) ^ 2 ≤ 2 * (a + b) := by
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, sq_nonneg (Real.sqrt a - Real.sqrt b)]

theorem sqrt_mul_add_sqrt_mul_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) :
    Real.sqrt (a * b) + Real.sqrt (c * d) ≤ Real.sqrt ((a + c) * (b + d)) := by
  have h1 : 0 ≤ Real.sqrt (a * b) + Real.sqrt (c * d) := by positivity
  rw [← Real.sqrt_sq h1]
  apply Real.sqrt_le_sqrt
  have hkey : 2 * (Real.sqrt (a * b) * Real.sqrt (c * d)) ≤ a * d + c * b := by
    have hamgm : 2 * (Real.sqrt (a * d) * Real.sqrt (c * b)) ≤ a * d + c * b := by
      nlinarith [sq_nonneg (Real.sqrt (a * d) - Real.sqrt (c * b)),
        Real.sq_sqrt (mul_nonneg ha hd), Real.sq_sqrt (mul_nonneg hc hb)]
    have heq : Real.sqrt (a * b) * Real.sqrt (c * d)
        = Real.sqrt (a * d) * Real.sqrt (c * b) := by
      rw [Real.sqrt_mul ha b, Real.sqrt_mul hc d, Real.sqrt_mul ha d, Real.sqrt_mul hc b]
      ring
    linarith [hamgm, heq]
  nlinarith [Real.sq_sqrt (mul_nonneg ha hb), Real.sq_sqrt (mul_nonneg hc hd), hkey]

theorem sq_div_le_max_sq_div {x y c d : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 < c) (hd : 0 < d) :
    (x + y) ^ 2 / ((Real.sqrt c + Real.sqrt d) ^ 2) ≤ max (x ^ 2 / c) (y ^ 2 / d) := by
  set M : ℝ := max (x ^ 2 / c) (y ^ 2 / d) with hM
  have hM0 : 0 ≤ M := le_trans (by positivity) (le_max_left _ _)
  have hx2 : x ^ 2 ≤ M * c := by
    have h := le_max_left (x ^ 2 / c) (y ^ 2 / d)
    rw [hM]
    exact (div_le_iff₀ hc).mp h
  have hy2 : y ^ 2 ≤ M * d := by
    have h := le_max_right (x ^ 2 / c) (y ^ 2 / d)
    rw [hM]
    exact (div_le_iff₀ hd).mp h
  have hxle : x ≤ Real.sqrt M * Real.sqrt c := by
    rw [← Real.sqrt_sq hx, ← Real.sqrt_mul hM0]
    exact Real.sqrt_le_sqrt hx2
  have hyle : y ≤ Real.sqrt M * Real.sqrt d := by
    rw [← Real.sqrt_sq hy, ← Real.sqrt_mul hM0]
    exact Real.sqrt_le_sqrt hy2
  have hsum : x + y ≤ Real.sqrt M * (Real.sqrt c + Real.sqrt d) := by nlinarith
  have hnn : 0 ≤ Real.sqrt M * (Real.sqrt c + Real.sqrt d) := by positivity
  have h1 : (x + y) ^ 2 ≤ (Real.sqrt M * (Real.sqrt c + Real.sqrt d)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hsum 2
  rw [mul_pow, Real.sq_sqrt hM0] at h1
  exact (div_le_iff₀ (by positivity)).mpr (by linarith [h1])

theorem holder_sum_le {n : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (x y : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hsum : 1 ≤ ∑ i, x i * y i) (hB : 0 < ∑ i, y i ^ q) :
    1 / (∑ i, y i ^ q) ^ (p / q) ≤ ∑ i, x i ^ p := by
  have hp : 1 < p := (Real.holderConjugate_iff.mp hpq).1
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 < q := by
    have hq := hpq.conjugate_eq
    rw [hq]
    exact div_pos hp0 (by linarith)
  set A : ℝ := ∑ i, x i ^ p with hA
  set B : ℝ := ∑ i, y i ^ q with hBdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hx i) p)
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hy i) q)
  have hHolder := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ) hpq
    (f := x) (g := y) (fun i _ => hx i) (fun i _ => hy i)
  have hHolder' : ∑ i, x i * y i ≤ A ^ (1 / p) * B ^ (1 / q) := by
    simpa [A, B] using hHolder
  have h1 : (1 : ℝ) ≤ A ^ (1 / p) * B ^ (1 / q) := le_trans hsum hHolder'
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

/-! ### Case (I) of the numeric core: the one-variable estimate

The function `g t = (1-t)^q + (2√t)^q` is convex, vanishes at `t = 0` as `1`,
and is at most `1` at `t = 9314/100000`; hence it is at most `1` on the whole
interval.  The endpoint value is checked with exact rational arithmetic, using
`q = 769/269`. -/

set_option exponentiation.threshold 2000 in
set_option maxRecDepth 100000 in
theorem cert_nat₁ : 90686 ^ 769 * 100000 ^ 269 ≤ 75617 ^ 269 * 100000 ^ 769 := by
  decide

set_option exponentiation.threshold 2000 in
set_option maxRecDepth 100000 in
theorem cert_nat₂ : 37256 ^ 769 * 100000 ^ 538 ≤ 24383 ^ 538 * 100000 ^ 769 := by
  decide

theorem cert_rat₁ : ((90686 : ℚ) / 100000) ^ 769 ≤ ((75617 : ℚ) / 100000) ^ 269 := by
  rw [div_pow, div_pow, div_le_div_iff₀ (by norm_num) (by norm_num)]
  exact_mod_cast cert_nat₁

theorem cert_rat₂ : ((37256 : ℚ) / 100000) ^ 769 ≤ ((24383 : ℚ) / 100000) ^ 538 := by
  rw [div_pow, div_pow, div_le_div_iff₀ (by norm_num) (by norm_num)]
  exact_mod_cast cert_nat₂

theorem cert_real₁ : ((90686 : ℝ) / 100000) ^ 769 ≤ ((75617 : ℝ) / 100000) ^ 269 := by
  have h := (Rat.cast_le (K := ℝ)).mpr cert_rat₁
  simpa using h

theorem cert_real₂ : ((37256 : ℝ) / 100000) ^ 769 ≤ ((24383 : ℝ) / 100000) ^ 538 := by
  have h := (Rat.cast_le (K := ℝ)).mpr cert_rat₂
  simpa using h

/-- Comparison of a real power with rational exponent with an integer power. -/
theorem rpow_div_nat_le {x U : ℝ} (hx : 0 ≤ x) (hU : 0 ≤ U) {m n : ℕ} (hn : 0 < n)
    (h : x ^ m ≤ U ^ n) : x ^ ((m : ℝ) / n) ≤ U := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hx' : ((x ^ m : ℝ)) ^ ((1 : ℝ) / n) = x ^ ((m : ℝ) / n) := by
    rw [← Real.rpow_natCast x m, ← Real.rpow_mul hx]
    congr 1
    rw [div_eq_mul_inv]
    ring
  have hU' : ((U ^ n : ℝ)) ^ ((1 : ℝ) / n) = U := by
    rw [← Real.rpow_natCast U n, ← Real.rpow_mul hU,
      show (n : ℝ) * (1 / (n : ℝ)) = 1 by
        rw [div_eq_mul_inv, one_mul, mul_inv_cancel₀ hn']]
    exact Real.rpow_one U
  rw [← hx', ← hU']
  exact Real.rpow_le_rpow (by positivity) h (by positivity)

theorem two_sqrt_rpow' {t q : ℝ} (ht : 0 ≤ t) :
    (2 * Real.sqrt t) ^ q = (4 * t) ^ (q / 2) := by
  have h2 : 0 ≤ 2 * Real.sqrt t := by positivity
  have hsq_nat : (2 * Real.sqrt t) ^ 2 = 4 * t := by
    rw [mul_pow]
    nlinarith [Real.sq_sqrt ht]
  have hsq : (2 * Real.sqrt t) ^ (((2 : ℕ) : ℝ)) = 4 * t := by
    rw [Real.rpow_natCast]
    exact hsq_nat
  calc (2 * Real.sqrt t) ^ q
      = (2 * Real.sqrt t) ^ (((2 : ℕ) : ℝ) * (q / 2)) := by
        rw [show (((2 : ℕ) : ℝ)) * (q / 2) = q by ring]
    _ = ((2 * Real.sqrt t) ^ (((2 : ℕ) : ℝ))) ^ (q / 2) := Real.rpow_mul h2 _ _
    _ = (4 * t) ^ (q / 2) := by rw [hsq]

theorem g_endpoint :
    (1 - (9314 : ℝ) / 100000) ^ ((769 : ℝ) / 269)
      + (4 * ((9314 : ℝ) / 100000)) ^ ((769 : ℝ) / 538) ≤ 1 := by
  have h1 : (1 - (9314 : ℝ) / 100000) ^ ((769 : ℝ) / 269) ≤ 75617 / 100000 := by
    have hbase : (1 - (9314 : ℝ) / 100000) = 90686 / 100000 := by norm_num
    rw [hbase]
    exact rpow_div_nat_le (by norm_num) (by norm_num) (n := 269) (by norm_num) cert_real₁
  have h2 : (4 * ((9314 : ℝ) / 100000)) ^ ((769 : ℝ) / 538) ≤ 24383 / 100000 := by
    have hbase : 4 * ((9314 : ℝ) / 100000) = 37256 / 100000 := by norm_num
    rw [hbase]
    exact rpow_div_nat_le (by norm_num) (by norm_num) (n := 538) (by norm_num) cert_real₂
  linarith

theorem rpow_chord {p z0 z1 lam : ℝ} (hp : 1 ≤ p) (hz0 : 0 ≤ z0) (hz1 : 0 ≤ z1)
    (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    ((1 - lam) * z0 + lam * z1) ^ p ≤ (1 - lam) * z0 ^ p + lam * z1 ^ p := by
  have h := Real.rpow_arith_mean_le_arith_mean_rpow (s := (Finset.univ : Finset (Fin 2)))
    (w := fun i : Fin 2 => if i = 0 then 1 - lam else lam)
    (z := fun i : Fin 2 => if i = 0 then z0 else z1)
    (by
      intro i _
      fin_cases i
      · simpa using sub_nonneg.mpr hlam1
      · simpa using hlam0)
    ?_ (by
      intro i _
      fin_cases i
      · simpa using hz0
      · simpa using hz1) hp
  · simpa [Fin.sum_univ_two] using h
  · simp [Fin.sum_univ_two]

theorem g_le_one {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 9314 / 100000) :
    (1 - t) ^ ((769 : ℝ) / 269) + (2 * Real.sqrt t) ^ ((769 : ℝ) / 269) ≤ 1 := by
  have htpos : (0 : ℝ) < 9314 / 100000 := by norm_num
  have htle : t ≤ 9314 / 100000 := ht1
  set lam : ℝ := t / (9314 / 100000) with hlamdef
  have hlam0 : 0 ≤ lam := div_nonneg ht0 htpos.le
  have hlam1 : lam ≤ 1 := (div_le_one htpos).mpr ht1
  have ht_eq : t = lam * (9314 / 100000) := by
    rw [hlamdef]
    field_simp
  have h1 : (1 - t) ^ ((769 : ℝ) / 269)
      ≤ (1 - lam) * (1 : ℝ) ^ ((769 : ℝ) / 269)
        + lam * (1 - (9314 : ℝ) / 100000) ^ ((769 : ℝ) / 269) := by
    have hc1 : (1 - t) = (1 - lam) * 1 + lam * (1 - (9314 : ℝ) / 100000) := by
      rw [ht_eq]
      ring
    rw [hc1]
    exact rpow_chord (by norm_num) zero_le_one (by norm_num) hlam0 hlam1
  have h2 : (4 * t) ^ ((769 : ℝ) / 538)
      ≤ (1 - lam) * (0 : ℝ) ^ ((769 : ℝ) / 538)
        + lam * (4 * ((9314 : ℝ) / 100000)) ^ ((769 : ℝ) / 538) := by
    have hc2 : 4 * t = (1 - lam) * 0 + lam * (4 * ((9314 : ℝ) / 100000)) := by
      rw [ht_eq]
      ring
    rw [hc2]
    exact rpow_chord (by norm_num) (by norm_num) (by norm_num) hlam0 hlam1
  have hsq : (2 * Real.sqrt t) ^ ((769 : ℝ) / 269) = (4 * t) ^ ((769 : ℝ) / 538) := by
    rw [two_sqrt_rpow' ht0]
    congr 1
    norm_num
  rw [hsq]
  have h1' : (1 - t) ^ ((769 : ℝ) / 269)
      ≤ (1 - lam) + lam * (1 - (9314 : ℝ) / 100000) ^ ((769 : ℝ) / 269) := by
    simpa using h1
  have h2' : (4 * t) ^ ((769 : ℝ) / 538)
      ≤ lam * (4 * ((9314 : ℝ) / 100000)) ^ ((769 : ℝ) / 538) := by
    simpa using h2
  have hg := g_endpoint
  nlinarith [h1', h2', hg, hlam0, hlam1]

/-! ### Bookkeeping for the numeric core -/

theorem exists_pair_ne (k : Fin 3) : ∃ i j : Fin 3, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  fin_cases k
  · exact ⟨1, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 2, by decide, by decide, by decide⟩
  · exact ⟨0, 1, by decide, by decide, by decide⟩

theorem linear_le_max {α β y x : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    α * y + β * x ≤ (α + β) * max y x := by
  rcases le_total y x with h | h
  · rw [max_eq_right h]
    nlinarith
  · rw [max_eq_left h]
    nlinarith

theorem sq_max_sq {y x : ℝ} (hy : 0 ≤ y) (hx : 0 ≤ x) :
    (max y x) ^ 2 = max (y ^ 2) (x ^ 2) := by
  rcases le_total y x with h | h
  · rw [max_eq_right h, max_eq_right (by nlinarith)]
  · rw [max_eq_left h, max_eq_left (by nlinarith)]

theorem sq_rpow {t χ : ℝ} (ht : 0 ≤ t) : (t ^ 2 : ℝ) ^ χ = t ^ (2 * χ) := by
  rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht]
  congr 1

theorem sum_p_eq_one {a b : Fin 3 → ℝ} (ha : ∑ i, a i = 1) (hb : ∑ i, b i = 1) :
    ∑ i, (a i + b i) / 2 = 1 := by
  rw [← Finset.sum_div, Finset.sum_add_distrib, ha, hb]
  norm_num

theorem pair_sum_of_total {p : Fin 3 → ℝ} (hp : ∑ i, p i = 1) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : p i + p j = 1 - p k := by
  rw [Fin.sum_univ_three] at hp
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> linarith

theorem e_partition {e : Fin 3 → Fin 3 → ℝ} {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    e i i + e i j + e j i + e j j + (2 * e k k + e i k + e k i + e j k + e k j)
      = (∑ p, ∑ q, e p q) + e k k := by
  rw [Fin.sum_univ_three]
  simp only [Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring

theorem sum_three_perm {f : Fin 3 → ℝ} {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    f i + f j + f k = f 0 + f 1 + f 2 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring

theorem e_block_le_one {e : Fin 3 → Fin 3 → ℝ} (he0 : ∀ i j, 0 ≤ e i j)
    (he1 : ∑ i, ∑ j, e i j = 1) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    e i i + e i j + e j i + e j j ≤ 1 := by
  rw [Fin.sum_univ_three] at he1
  simp only [Fin.sum_univ_three] at he1
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;>
    linarith [he0 0 0, he0 0 1, he0 0 2, he0 1 0, he0 1 1, he0 1 2,
      he0 2 0, he0 2 1, he0 2 2]

/-! ### The averaged numeric data and the case-(I) estimate -/

noncomputable def avg (a b : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => (a i + b i) / 2

theorem avg_pos {a b : Fin 3 → ℝ} (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (i : Fin 3) :
    0 < avg a b i := by
  unfold avg
  linarith [ha i, hb i]

theorem avg_sum {a b : Fin 3 → ℝ} (ha : ∑ i, a i = 1) (hb : ∑ i, b i = 1) :
    ∑ i, avg a b i = 1 := sum_p_eq_one ha hb

/-- Sum of the four corners of the block on `{i,j}`. -/
noncomputable def nA (e : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  e i i + e i j + e j i + e j j

/-- The numerator of the row/column estimate: `2e_kk + e_ik + e_ki + e_jk + e_kj`. -/
noncomputable def nN (e : Fin 3 → Fin 3 → ℝ) (i j k : Fin 3) : ℝ :=
  2 * e k k + e i k + e k i + e j k + e k j

noncomputable def nS (p : Fin 3 → ℝ) (i j : Fin 3) : ℝ := p i + p j

noncomputable def nG (p : Fin 3 → ℝ) (k : Fin 3) : ℝ := 2 * Real.sqrt (p k)

noncomputable def nY (p : Fin 3 → ℝ) (e : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  nA e i j / nS p i j

noncomputable def nX (p : Fin 3 → ℝ) (e : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  (e i j + e j i) / (2 * Real.sqrt (p i * p j))

noncomputable def nC (p : Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  (Real.sqrt (p i) + Real.sqrt (p j)) ^ 2 / 2

theorem nA_nonneg {e : Fin 3 → Fin 3 → ℝ} (he0 : ∀ i j, 0 ≤ e i j) (i j : Fin 3) :
    0 ≤ nA e i j := by
  unfold nA
  linarith [he0 i i, he0 i j, he0 j i, he0 j j]

theorem nA_le_one {e : Fin 3 → Fin 3 → ℝ} (he0 : ∀ i j, 0 ≤ e i j)
    (he1 : ∑ i, ∑ j, e i j = 1) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : nA e i j ≤ 1 := by
  unfold nA
  exact e_block_le_one he0 he1 hij hik hjk

theorem nN_nonneg {e : Fin 3 → Fin 3 → ℝ} (he0 : ∀ i j, 0 ≤ e i j) (i j k : Fin 3) :
    0 ≤ nN e i j k := by
  unfold nN
  linarith [he0 k k, he0 i k, he0 k i, he0 j k, he0 k j]

theorem nA_add_nN {e : Fin 3 → Fin 3 → ℝ} (he1 : ∑ i, ∑ j, e i j = 1) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    nA e i j + nN e i j k = 1 + e k k := by
  unfold nA nN
  have h := e_partition (e := e) hij hik hjk
  rw [he1] at h
  exact h

theorem nS_eq_one {p : Fin 3 → ℝ} (hp1 : ∑ i, p i = 1) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : nS p i j = 1 - p k := by
  unfold nS
  exact pair_sum_of_total hp1 hij hik hjk

theorem nS_pos {p : Fin 3 → ℝ} (hp0 : ∀ i, 0 < p i) (i j : Fin 3) : 0 < nS p i j := by
  unfold nS
  exact add_pos (hp0 i) (hp0 j)

theorem nY_nonneg {p : Fin 3 → ℝ} {e : Fin 3 → Fin 3 → ℝ} (hp0 : ∀ i, 0 < p i)
    (he0 : ∀ i j, 0 ≤ e i j) (i j : Fin 3) : 0 ≤ nY p e i j := by
  unfold nY
  exact div_nonneg (nA_nonneg he0 i j) (nS_pos hp0 i j).le

theorem nS_mul_nY (p : Fin 3 → ℝ) (e : Fin 3 → Fin 3 → ℝ) (i j : Fin 3)
    (hp : nS p i j ≠ 0) : nS p i j * nY p e i j = nA e i j := by
  unfold nY
  field_simp

theorem nY_sq (p : Fin 3 → ℝ) (e : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) :
    nY p e i j ^ 2 = (nA e i j) ^ 2 / (nS p i j) ^ 2 := by
  unfold nY
  rw [div_pow]

theorem nX_nonneg {p : Fin 3 → ℝ} {e : Fin 3 → Fin 3 → ℝ} (hp0 : ∀ i, 0 < p i)
    (he0 : ∀ i j, 0 ≤ e i j) (i j : Fin 3) : 0 ≤ nX p e i j := by
  unfold nX
  have hpos : 0 < 2 * Real.sqrt (p i * p j) :=
    mul_pos (by norm_num) (Real.sqrt_pos_of_pos (mul_pos (hp0 i) (hp0 j)))
  exact div_nonneg (by linarith [he0 i j, he0 j i]) hpos.le

theorem nX_sq {p : Fin 3 → ℝ} (hp0 : ∀ i, 0 < p i) (e : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) :
    nX p e i j ^ 2 = (e i j + e j i) ^ 2 / (4 * p i * p j) := by
  unfold nX
  rw [div_pow]
  have h : (2 * Real.sqrt (p i * p j)) ^ 2 = 4 * p i * p j := by
    nlinarith [Real.sq_sqrt (mul_nonneg (hp0 i).le (hp0 j).le)]
  rw [h]

theorem nX_mul {p : Fin 3 → ℝ} (hp0 : ∀ i, 0 < p i) (e : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) :
    2 * Real.sqrt (p i * p j) * nX p e i j = e i j + e j i := by
  unfold nX
  have hne : Real.sqrt (p i * p j) ≠ 0 :=
    (Real.sqrt_pos_of_pos (mul_pos (hp0 i) (hp0 j))).ne'
  field_simp

theorem nG_pos {p : Fin 3 → ℝ} (hp0 : ∀ i, 0 < p i) (k : Fin 3) : 0 < nG p k := by
  unfold nG
  exact mul_pos (by norm_num) (Real.sqrt_pos_of_pos (hp0 k))

theorem nG_sq {p : Fin 3 → ℝ} (hp0 : ∀ i, 0 < p i) (k : Fin 3) : nG p k ^ 2 = 4 * p k := by
  unfold nG
  nlinarith [Real.sq_sqrt (hp0 k).le]

theorem nC_nonneg {p : Fin 3 → ℝ} (hp0 : ∀ i, 0 < p i) (i j : Fin 3) : 0 ≤ nC p i j := by
  unfold nC
  positivity

theorem nC_pos {p : Fin 3 → ℝ} (hp0 : ∀ i, 0 < p i) (i j : Fin 3) : 0 < nC p i j := by
  unfold nC
  have h1 := Real.sqrt_pos_of_pos (hp0 i)
  have h2 := Real.sqrt_pos_of_pos (hp0 j)
  positivity

theorem nC_eq {p : Fin 3 → ℝ} (hp0 : ∀ i, 0 < p i) (i j : Fin 3) :
    nC p i j = (nS p i j + 2 * Real.sqrt (p i * p j)) / 2 := by
  unfold nC nS
  rw [Real.sqrt_mul (hp0 i).le]
  have h := Real.sq_sqrt (hp0 i).le
  have h2 := Real.sq_sqrt (hp0 j).le
  field_simp
  nlinarith

theorem nN_eq_rows (e : Fin 3 → Fin 3 → ℝ) {i j k : Fin 3}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    nN e i j k = (e k 0 + e k 1 + e k 2) + (e 0 k + e 1 k + e 2 k) := by
  unfold nN
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all <;> ring

theorem holder_two_le {p q x1 x2 y1 y2 : ℝ} (hpq : p.HolderConjugate q)
    (hx1 : 0 ≤ x1) (hx2 : 0 ≤ x2) (hy1 : 0 ≤ y1) (hy2 : 0 ≤ y2)
    (hsum : 1 ≤ x1 * y1 + x2 * y2) (hB : 0 < y1 ^ q + y2 ^ q) :
    1 / (y1 ^ q + y2 ^ q) ^ (p / q) ≤ x1 ^ p + x2 ^ p := by
  have h := holder_sum_le (n := 2) hpq
    (fun t : Fin 2 => if t = 0 then x1 else x2)
    (fun t : Fin 2 => if t = 0 then y1 else y2)
    (by
      intro t
      fin_cases t
      · simpa using hx1
      · simpa using hx2)
    (by
      intro t
      fin_cases t
      · simpa using hy1
      · simpa using hy2)
    (by simpa [Fin.sum_univ_two] using hsum) (by simpa [Fin.sum_univ_two] using hB)
  simpa [Fin.sum_univ_two] using h

/-- Case (I) of the numeric core: one of the three normalised sizes is at most
`9314/100000`.  The proof uses the estimate (4.2) for `s k`, the row/column
estimate (4.3) for `s i + s j`, Hölder's inequality, and the one-variable bound
`g_le_one`. -/
theorem caseI_aux {s p : Fin 3 → ℝ} {e : Fin 3 → Fin 3 → ℝ}
    (hp0 : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (he0 : ∀ i j, 0 ≤ e i j) (he1 : ∑ i, ∑ j, e i j = 1)
    (hs0 : ∀ i, 0 ≤ s i)
    (hH : ∀ i j k : Fin 3, i ≠ j → k ≠ i → k ≠ j →
      s k ≥ (nA e i j) ^ 2 / (nS p i j) ^ 2)
    (hQ : ∀ i j k : Fin 3, i ≠ j → k ≠ i → k ≠ j →
      s k ≥ (e i j + e j i) ^ 2 / (4 * p i * p j))
    (hF : ∀ i j k : Fin 3, i ≠ j → k ≠ i → k ≠ j →
      s i + s j ≥ (nN e i j k) ^ 2 / (4 * p k))
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hk : p k ≤ 9314 / 100000) :
    1 ≤ ∑ t, (s t) ^ ((769 : ℝ) / 1000) := by
  have hki : k ≠ i := Ne.symm hik
  have hkj : k ≠ j := Ne.symm hjk
  have hSpos : 0 < nS p i j := nS_pos hp0 i j
  have hGpos : 0 < nG p k := nG_pos hp0 k
  have hGsq : nG p k ^ 2 = 4 * p k := nG_sq hp0 k
  have hSeq : nS p i j = 1 - p k := nS_eq_one hp1 hij hik hjk
  have hAy : nS p i j * nY p e i j = nA e i j := nS_mul_nY p e i j hSpos.ne'
  have hA1 : nA e i j ≤ 1 := nA_le_one he0 he1 hij hik hjk
  have hAy1 : 0 ≤ 1 - nS p i j * nY p e i j := by rw [hAy]; linarith
  have hpart : nA e i j + nN e i j k = 1 + e k k := nA_add_nN he1 hij hik hjk
  have hy0 : 0 ≤ nY p e i j := nY_nonneg hp0 he0 i j
  have hx0 : 0 ≤ nX p e i j := nX_nonneg hp0 he0 i j
  have h1 : s k ≥ (nY p e i j) ^ 2 := by
    rw [nY_sq]
    exact hH i j k hij hki hkj
  have h2 : s k ≥ (nX p e i j) ^ 2 := by
    rw [nX_sq hp0]
    exact hQ i j k hij hki hkj
  have hsk : s k ≥ (max (nY p e i j) (nX p e i j)) ^ 2 := by
    rw [sq_max_sq hy0 hx0]
    exact max_le h1 h2
  have hFnum : s i + s j ≥ ((1 - nS p i j * nY p e i j) / nG p k) ^ 2 := by
    have hf := hF i j k hij hki hkj
    have hNge : nN e i j k ≥ 1 - nA e i j := by linarith [hpart, he0 k k]
    have h1mA : 0 ≤ 1 - nA e i j := by linarith
    have hNsq : (1 - nA e i j) ^ 2 ≤ (nN e i j k) ^ 2 :=
      by nlinarith [hNge, nN_nonneg he0 i j k]
    have hdiv : (nN e i j k) ^ 2 / (4 * p k) = (nN e i j k / nG p k) ^ 2 := by
      rw [div_pow, hGsq]
    have hle : (1 - nA e i j) / nG p k ≤ nN e i j k / nG p k :=
      div_le_div_of_nonneg_right hNge hGpos.le
    have hnn : 0 ≤ (1 - nA e i j) / nG p k := div_nonneg h1mA hGpos.le
    have hsq : ((1 - nA e i j) / nG p k) ^ 2 ≤ (nN e i j k / nG p k) ^ 2 := by
      nlinarith
    calc s i + s j ≥ (nN e i j k) ^ 2 / (4 * p k) := hf
      _ = (nN e i j k / nG p k) ^ 2 := hdiv
      _ ≥ ((1 - nA e i j) / nG p k) ^ 2 := hsq
      _ = ((1 - nS p i j * nY p e i j) / nG p k) ^ 2 := by rw [hAy]
  have hbase_le : (nS p i j) ^ ((769 : ℝ) / 269) + (nG p k) ^ ((769 : ℝ) / 269) ≤ 1 := by
    rw [hSeq]
    unfold nG
    exact g_le_one (le_of_lt (hp0 k)) hk
  have hbase_pos : 0 < (nS p i j) ^ ((769 : ℝ) / 269) + (nG p k) ^ ((769 : ℝ) / 269) := by
    positivity
  have hpq : ((769 : ℝ) / 500).HolderConjugate ((769 : ℝ) / 269) := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hsum2 : 1 ≤ nY p e i j * (nS p i j)
      + ((1 - nS p i j * nY p e i j) / nG p k) * nG p k := by
    have hcancel : ((1 - nS p i j * nY p e i j) / nG p k) * nG p k
        = 1 - nS p i j * nY p e i j := by field_simp
    rw [hcancel, mul_comm (nY p e i j) (nS p i j), hAy]
    linarith
  have hHolder : ((nS p i j) ^ ((769 : ℝ) / 269) + (nG p k) ^ ((769 : ℝ) / 269))
        ^ (1 - 2 * ((769 : ℝ) / 1000))
      ≤ (nY p e i j) ^ (2 * ((769 : ℝ) / 1000))
        + ((1 - nS p i j * nY p e i j) / nG p k) ^ (2 * ((769 : ℝ) / 1000)) := by
    have h := holder_two_le hpq hy0 (div_nonneg hAy1 hGpos.le) hSpos.le hGpos.le hsum2
      hbase_pos
    have hneg : 1 - 2 * ((769 : ℝ) / 1000) = -(((769 : ℝ) / 500) / ((769 : ℝ) / 269)) := by
      norm_num
    rw [hneg, Real.rpow_neg (le_of_lt hbase_pos)]
    have hexp : 2 * ((769 : ℝ) / 1000) = (769 : ℝ) / 500 := by norm_num
    rw [hexp]
    simpa [one_div] using h
  have hone : (1 : ℝ) ≤ ((nS p i j) ^ ((769 : ℝ) / 269) + (nG p k) ^ ((769 : ℝ) / 269))
      ^ (1 - 2 * ((769 : ℝ) / 1000)) := by
    rw [show 1 - 2 * ((769 : ℝ) / 1000) = -(2 * ((769 : ℝ) / 1000) - 1) by ring,
      Real.rpow_neg (le_of_lt hbase_pos), one_le_inv₀ (by positivity)]
    exact Real.rpow_le_one hbase_pos.le hbase_le (by norm_num)
  have hskχ : (max (nY p e i j) (nX p e i j)) ^ (2 * ((769 : ℝ) / 1000))
      ≤ (s k) ^ ((769 : ℝ) / 1000) := by
    have hr := Real.rpow_le_rpow
      (by positivity : (0:ℝ) ≤ (max (nY p e i j) (nX p e i j)) ^ 2) hsk
      (by norm_num : (0:ℝ) ≤ (769:ℝ)/1000)
    rwa [sq_rpow (χ := (769:ℝ)/1000) (le_trans hx0 (le_max_right _ _))] at hr
  have hFχ : ((1 - nS p i j * nY p e i j) / nG p k) ^ (2 * ((769 : ℝ) / 1000))
      ≤ (s i + s j) ^ ((769 : ℝ) / 1000) := by
    have hnn : 0 ≤ (1 - nS p i j * nY p e i j) / nG p k := div_nonneg hAy1 hGpos.le
    have hr := Real.rpow_le_rpow
      (by positivity : (0:ℝ) ≤ ((1 - nS p i j * nY p e i j) / nG p k) ^ 2) hFnum
      (by norm_num : (0:ℝ) ≤ (769:ℝ)/1000)
    rwa [sq_rpow (χ := (769:ℝ)/1000) hnn] at hr
  have hymax : (nY p e i j) ^ (2 * ((769 : ℝ) / 1000))
      ≤ (max (nY p e i j) (nX p e i j)) ^ (2 * ((769 : ℝ) / 1000)) :=
    Real.rpow_le_rpow hy0 (le_max_left _ _) (by positivity)
  have hsplit : (s i) ^ ((769 : ℝ) / 1000) + (s j) ^ ((769 : ℝ) / 1000)
      ≥ (s i + s j) ^ ((769 : ℝ) / 1000) := by
    have := Real.rpow_add_le_add_rpow (hs0 i) (hs0 j) (by norm_num : (0:ℝ) ≤ (769:ℝ)/1000)
      (by norm_num : (769:ℝ)/1000 ≤ 1)
    linarith
  have hperm := sum_three_perm (f := fun t => (s t) ^ ((769 : ℝ) / 1000)) hij hik hjk
  rw [Fin.sum_univ_three]
  linarith [hone, hHolder, hymax, hskχ, hFχ, hsplit, hperm]

/-- The two-variable inequality left over in case (II): for normalised sizes
`p i >= 9314/100000` summing to `1`,
`sum_k c_k^(769/269) <= 1`, where `c_k` is `(sqrt (p i) + sqrt (p j))^2 / 2`
for the complementary pair `{i,j}` of `k`.  This is estimate (4.14) of the
paper (the numerical analysis of `max g <= 2^(theta/2)`). -/
def CaseIIBound : Prop :=
  ∀ p : Fin 3 → ℝ, (∀ i, 0 < p i) → (∑ i, p i = 1) →
    (∀ i, (9314 : ℝ) / 100000 ≤ p i) →
    (nC p 1 2) ^ ((769 : ℝ) / 269) + (nC p 0 2) ^ ((769 : ℝ) / 269)
      + (nC p 0 1) ^ ((769 : ℝ) / 269) ≤ 1


/-! ### The sharp numerical evaluation at the corner

The maximum in estimate (4.14) is attained at the corner
`p = (9314/100000, 45343/100000, 45343/100000)`.  The two powers appearing
there are bounded by rational certificates; the exponents `769` and `269` are
cleared by raising to the `269`-th power, and the resulting (huge) rational
inequalities are checked by kernel evaluation (`decide`). -/

/-- Criterion for a numerical bound `x ^ (769/269) ≤ M`: it suffices that
`x ≤ q` for a rational `q` with `q ^ 769 ≤ M ^ 269`.  Clearing the `269`-th
root and the denominators turns the check into a rational comparison. -/
theorem rpow_769_269_le {x q M : ℝ} (hx : 0 ≤ x) (hxq : x ≤ q) (hq : 0 ≤ q) (hM : 0 < M)
    (hbig : Real.rpow q 769 ≤ Real.rpow M 269) : x ^ ((769 : ℝ) / 269) ≤ M := by
  have h1 : x ^ ((769 : ℝ) / 269) ≤ q ^ ((769 : ℝ) / 269) :=
    Real.rpow_le_rpow hx hxq (by norm_num)
  have hq' : q ^ ((769 : ℝ) / 269) = (q ^ (769 : ℝ)) ^ ((1 : ℝ) / 269) := by
    rw [show (769 : ℝ) / 269 = (769 : ℝ) * (1 / 269) by norm_num, Real.rpow_mul hq]
  have hM' : M = (M ^ (269 : ℝ)) ^ ((1 : ℝ) / 269) := by
    conv_rhs => rw [← Real.rpow_mul (le_of_lt hM)]
    rw [show (269 : ℝ) * (1 / 269) = 1 by norm_num, Real.rpow_one]
  calc x ^ ((769 : ℝ) / 269) ≤ q ^ ((769 : ℝ) / 269) := h1
    _ = (q ^ (769 : ℝ)) ^ ((1 : ℝ) / 269) := hq'
    _ ≤ (M ^ (269 : ℝ)) ^ ((1 : ℝ) / 269) := by
        rw [Real.rpow_le_rpow_iff (by positivity) (by positivity) (by norm_num : (0 : ℝ) < 1 / 269)]
        exact hbig
    _ = M := hM'.symm

/-- The dominant term at the corner: `(45343/50000)^(769/269) ≤ 3781/5000`. -/
theorem corner_T1 : ((45343 : ℝ) / 50000) ^ ((769 : ℝ) / 269) ≤ (3781 : ℝ) / 5000 := by
  apply rpow_769_269_le (le_of_lt (by norm_num)) (le_refl _) (by norm_num) (by norm_num)
  have q : ((45343 : ℚ) / 50000) ^ 769 ≤ ((3781 : ℚ) / 5000) ^ 269 := by decide +kernel
  have h : ((((45343 : ℚ) / 50000) ^ 769 : ℚ) : ℝ) ≤ ((((3781 : ℚ) / 5000) ^ 269 : ℚ) : ℝ) :=
    Rat.cast_le.mpr q
  push_cast at h
  rwa [← Real.rpow_natCast, ← Real.rpow_natCast] at h

/-- The irrational base at the corner is below `1197/2500`. -/
theorem corner_sqrt_bound :
    (54657 : ℝ) / 200000 + Real.sqrt ((211162351 : ℝ) / 5000000000) ≤ (1197 : ℝ) / 2500 := by
  have h : Real.sqrt ((211162351 : ℝ) / 5000000000) ≤ (41103 : ℝ) / 200000 :=
    Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  linarith

/-- The two equal terms at the corner: `(54657/200000 + sqrt (211162351/5000000000))^(769/269) ≤ 609/5000`. -/
theorem corner_T2 :
    ((54657 : ℝ) / 200000 + Real.sqrt ((211162351 : ℝ) / 5000000000)) ^ ((769 : ℝ) / 269)
      ≤ (609 : ℝ) / 5000 := by
  apply rpow_769_269_le (by positivity) corner_sqrt_bound (by norm_num) (by norm_num)
  have q : ((1197 : ℚ) / 2500) ^ 769 ≤ ((609 : ℚ) / 5000) ^ 269 := by decide +kernel
  have h : ((((1197 : ℚ) / 2500) ^ 769 : ℚ) : ℝ) ≤ ((((609 : ℚ) / 5000) ^ 269 : ℚ) : ℝ) :=
    Rat.cast_le.mpr q
  push_cast at h
  rwa [← Real.rpow_natCast, ← Real.rpow_natCast] at h

/-- The corner value of the normalised sum is `< 1`. -/
theorem cornerBound :
    ((45343 : ℝ) / 50000) ^ ((769 : ℝ) / 269)
      + 2 * (((54657 : ℝ) / 200000 + Real.sqrt ((211162351 : ℝ) / 5000000000)) ^ ((769 : ℝ) / 269))
      ≤ 1 := by
  have h1 := corner_T1
  have h2 := corner_T2
  linarith


theorem holder_three_le {p q a1 a2 a3 b1 b2 b3 : ℝ} (hpq : p.HolderConjugate q)
    (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hb3 : 0 ≤ b3)
    (hsum : 1 ≤ a1 * b1 + a2 * b2 + a3 * b3) (hB : 0 < b1 ^ q + b2 ^ q + b3 ^ q) :
    1 / (b1 ^ q + b2 ^ q + b3 ^ q) ^ (p / q) ≤ a1 ^ p + a2 ^ p + a3 ^ p := by
  have h := holder_sum_le (n := 3) hpq
    (fun t : Fin 3 => if t = 0 then a1 else if t = 1 then a2 else a3)
    (fun t : Fin 3 => if t = 0 then b1 else if t = 1 then b2 else b3)
    (by
      intro t
      fin_cases t
      · simpa using ha1
      · simpa using ha2
      · simpa using ha3)
    (by
      intro t
      fin_cases t
      · simpa using hb1
      · simpa using hb2
      · simpa using hb3)
    (by simpa [Fin.sum_univ_three] using hsum) (by simpa [Fin.sum_univ_three] using hB)
  simpa [Fin.sum_univ_three] using h

/-- Case (II) of the numeric core: all three normalised sizes are at least
`9314/100000`. -/
theorem caseII_aux {s p : Fin 3 → ℝ} {e : Fin 3 → Fin 3 → ℝ}
    (hp0 : ∀ i, 0 < p i) (hp1 : ∑ i, p i = 1)
    (he0 : ∀ i j, 0 ≤ e i j) (he1 : ∑ i, ∑ j, e i j = 1)
    (hs0 : ∀ i, 0 ≤ s i)
    (hH : ∀ i j k : Fin 3, i ≠ j → k ≠ i → k ≠ j →
      s k ≥ (nA e i j) ^ 2 / (nS p i j) ^ 2)
    (hQ : ∀ i j k : Fin 3, i ≠ j → k ≠ i → k ≠ j →
      s k ≥ (e i j + e j i) ^ 2 / (4 * p i * p j))
    (hF : ∀ i j k : Fin 3, i ≠ j → k ≠ i → k ≠ j →
      s i + s j ≥ (nN e i j k) ^ 2 / (4 * p k))
    (ht : ∀ i, (9314 : ℝ) / 100000 ≤ p i) (hII : CaseIIBound) :
    1 ≤ ∑ t, (s t) ^ ((769 : ℝ) / 1000) := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  -- the three pair estimates
  have h0 : s 0 ≥ (max (nY p e 1 2) (nX p e 1 2)) ^ 2 := by
    have h1 : s 0 ≥ (nY p e 1 2) ^ 2 := by
      rw [nY_sq]; exact hH 1 2 0 h12 (by decide) (by decide)
    have h2 : s 0 ≥ (nX p e 1 2) ^ 2 := by
      rw [nX_sq hp0]; exact hQ 1 2 0 h12 (by decide) (by decide)
    rw [sq_max_sq (nY_nonneg hp0 he0 1 2) (nX_nonneg hp0 he0 1 2)]
    exact max_le h1 h2
  have h1 : s 1 ≥ (max (nY p e 0 2) (nX p e 0 2)) ^ 2 := by
    have h1' : s 1 ≥ (nY p e 0 2) ^ 2 := by
      rw [nY_sq]; exact hH 0 2 1 h02 (by decide) (by decide)
    have h2' : s 1 ≥ (nX p e 0 2) ^ 2 := by
      rw [nX_sq hp0]; exact hQ 0 2 1 h02 (by decide) (by decide)
    rw [sq_max_sq (nY_nonneg hp0 he0 0 2) (nX_nonneg hp0 he0 0 2)]
    exact max_le h1' h2'
  have h2 : s 2 ≥ (max (nY p e 0 1) (nX p e 0 1)) ^ 2 := by
    have h1' : s 2 ≥ (nY p e 0 1) ^ 2 := by
      rw [nY_sq]; exact hH 0 1 2 h01 (by decide) (by decide)
    have h2' : s 2 ≥ (nX p e 0 1) ^ 2 := by
      rw [nX_sq hp0]; exact hQ 0 1 2 h01 (by decide) (by decide)
    rw [sq_max_sq (nY_nonneg hp0 he0 0 1) (nX_nonneg hp0 he0 0 1)]
    exact max_le h1' h2'
  -- the linear constraint sum c_k m_k >= 1
  have hcon : 1 ≤ nC p 1 2 * max (nY p e 1 2) (nX p e 1 2)
      + nC p 0 2 * max (nY p e 0 2) (nX p e 0 2)
      + nC p 0 1 * max (nY p e 0 1) (nX p e 0 1) := by
    have l0 := linear_le_max (α := nS p 1 2) (β := 2 * Real.sqrt (p 1 * p 2))
      (y := nY p e 1 2) (x := nX p e 1 2) (nS_pos hp0 1 2).le (by positivity)
    have l1 := linear_le_max (α := nS p 0 2) (β := 2 * Real.sqrt (p 0 * p 2))
      (y := nY p e 0 2) (x := nX p e 0 2) (nS_pos hp0 0 2).le (by positivity)
    have l2 := linear_le_max (α := nS p 0 1) (β := 2 * Real.sqrt (p 0 * p 1))
      (y := nY p e 0 1) (x := nX p e 0 1) (nS_pos hp0 0 1).le (by positivity)
    have c0 : 2 * nC p 1 2 = nS p 1 2 + 2 * Real.sqrt (p 1 * p 2) := by
      rw [nC_eq hp0]; ring
    have c1 : 2 * nC p 0 2 = nS p 0 2 + 2 * Real.sqrt (p 0 * p 2) := by
      rw [nC_eq hp0]; ring
    have c2 : 2 * nC p 0 1 = nS p 0 1 + 2 * Real.sqrt (p 0 * p 1) := by
      rw [nC_eq hp0]; ring
    have a0 := nS_mul_nY p e 1 2 (nS_pos hp0 1 2).ne'
    have a1 := nS_mul_nY p e 0 2 (nS_pos hp0 0 2).ne'
    have a2 := nS_mul_nY p e 0 1 (nS_pos hp0 0 1).ne'
    have b0 := nX_mul hp0 e 1 2
    have b1 := nX_mul hp0 e 0 2
    have b2 := nX_mul hp0 e 0 1
    have htot : (nA e 1 2 + (e 1 2 + e 2 1)) + (nA e 0 2 + (e 0 2 + e 2 0))
        + (nA e 0 1 + (e 0 1 + e 1 0)) = 2 := by
      unfold nA
      rw [Fin.sum_univ_three] at he1
      simp only [Fin.sum_univ_three] at he1
      linarith
    have l0' : nA e 1 2 + (e 1 2 + e 2 1)
        ≤ 2 * nC p 1 2 * max (nY p e 1 2) (nX p e 1 2) := by
      have h := l0
      rw [a0, b0, ← c0] at h
      exact h
    have l1' : nA e 0 2 + (e 0 2 + e 2 0)
        ≤ 2 * nC p 0 2 * max (nY p e 0 2) (nX p e 0 2) := by
      have h := l1
      rw [a1, b1, ← c1] at h
      exact h
    have l2' : nA e 0 1 + (e 0 1 + e 1 0)
        ≤ 2 * nC p 0 1 * max (nY p e 0 1) (nX p e 0 1) := by
      have h := l2
      rw [a2, b2, ← c2] at h
      exact h
    linarith [l0', l1', l2', htot]
  -- the three-term Hölder estimate
  have hbase : (nC p 1 2) ^ ((769 : ℝ) / 269) + (nC p 0 2) ^ ((769 : ℝ) / 269)
      + (nC p 0 1) ^ ((769 : ℝ) / 269) ≤ 1 := hII p hp0 hp1 ht
  have hbase_pos : 0 < (nC p 1 2) ^ ((769 : ℝ) / 269) + (nC p 0 2) ^ ((769 : ℝ) / 269)
      + (nC p 0 1) ^ ((769 : ℝ) / 269) := by
    have p1 := Real.rpow_pos_of_pos (nC_pos hp0 1 2) ((769 : ℝ) / 269)
    have p2 := Real.rpow_pos_of_pos (nC_pos hp0 0 2) ((769 : ℝ) / 269)
    have p3 := Real.rpow_pos_of_pos (nC_pos hp0 0 1) ((769 : ℝ) / 269)
    linarith
  have hpqt : ((769 : ℝ) / 500).HolderConjugate ((769 : ℝ) / 269) := by
    rw [Real.holderConjugate_iff]
    constructor <;> norm_num
  have hHölder : ((nC p 1 2) ^ ((769 : ℝ) / 269) + (nC p 0 2) ^ ((769 : ℝ) / 269)
        + (nC p 0 1) ^ ((769 : ℝ) / 269)) ^ (1 - 2 * ((769 : ℝ) / 1000))
      ≤ (max (nY p e 1 2) (nX p e 1 2)) ^ (2 * ((769 : ℝ) / 1000))
        + (max (nY p e 0 2) (nX p e 0 2)) ^ (2 * ((769 : ℝ) / 1000))
        + (max (nY p e 0 1) (nX p e 0 1)) ^ (2 * ((769 : ℝ) / 1000)) := by
    have h := holder_three_le hpqt
      (le_trans (nX_nonneg hp0 he0 1 2) (le_max_right _ _))
      (le_trans (nX_nonneg hp0 he0 0 2) (le_max_right _ _))
      (le_trans (nX_nonneg hp0 he0 0 1) (le_max_right _ _))
      (nC_nonneg hp0 1 2) (nC_nonneg hp0 0 2) (nC_nonneg hp0 0 1)
      (by simpa [mul_comm] using hcon) hbase_pos
    have hneg : 1 - 2 * ((769 : ℝ) / 1000) = -(((769 : ℝ) / 500) / ((769 : ℝ) / 269)) := by
      norm_num
    rw [hneg, Real.rpow_neg (le_of_lt hbase_pos)]
    have hexp : 2 * ((769 : ℝ) / 1000) = (769 : ℝ) / 500 := by norm_num
    rw [hexp]
    simpa [one_div] using h
  have hone : (1 : ℝ) ≤ ((nC p 1 2) ^ ((769 : ℝ) / 269) + (nC p 0 2) ^ ((769 : ℝ) / 269)
      + (nC p 0 1) ^ ((769 : ℝ) / 269)) ^ (1 - 2 * ((769 : ℝ) / 1000)) := by
    rw [show 1 - 2 * ((769 : ℝ) / 1000) = -(2 * ((769 : ℝ) / 1000) - 1) by ring,
      Real.rpow_neg (le_of_lt hbase_pos), one_le_inv₀ (by positivity)]
    exact Real.rpow_le_one hbase_pos.le hbase (by norm_num)
  -- pass to `s`
  have e0 : (max (nY p e 1 2) (nX p e 1 2)) ^ (2 * ((769 : ℝ) / 1000))
      ≤ (s 0) ^ ((769 : ℝ) / 1000) := by
    have hr := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (max (nY p e 1 2) (nX p e 1 2)) ^ 2)
      h0 (by norm_num : (0:ℝ) ≤ (769:ℝ)/1000)
    rwa [sq_rpow (χ := (769:ℝ)/1000) (le_trans (nX_nonneg hp0 he0 1 2) (le_max_right _ _))] at hr
  have e1 : (max (nY p e 0 2) (nX p e 0 2)) ^ (2 * ((769 : ℝ) / 1000))
      ≤ (s 1) ^ ((769 : ℝ) / 1000) := by
    have hr := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (max (nY p e 0 2) (nX p e 0 2)) ^ 2)
      h1 (by norm_num : (0:ℝ) ≤ (769:ℝ)/1000)
    rwa [sq_rpow (χ := (769:ℝ)/1000) (le_trans (nX_nonneg hp0 he0 0 2) (le_max_right _ _))] at hr
  have e2 : (max (nY p e 0 1) (nX p e 0 1)) ^ (2 * ((769 : ℝ) / 1000))
      ≤ (s 2) ^ ((769 : ℝ) / 1000) := by
    have hr := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (max (nY p e 0 1) (nX p e 0 1)) ^ 2)
      h2 (by norm_num : (0:ℝ) ≤ (769:ℝ)/1000)
    rwa [sq_rpow (χ := (769:ℝ)/1000) (le_trans (nX_nonneg hp0 he0 0 1) (le_max_right _ _))] at hr
  rw [Fin.sum_univ_three]
  linarith [hone, hHölder, e0, e1, e2]

/-- The numeric core of the main case, conditional on the sharp two-variable
bound `CaseIIBound`.  This is the formal counterpart of estimates
(4.6)--(4.14) of the paper. -/
theorem mainNumeric_0_769 (hII : CaseIIBound) : MainNumeric ((769 : ℝ) / 1000) := by
  intro s a b e ha0 ha1 hb0 hb1 he0 he1 hs0 hH hQ1 hQ2 hF1 hF2
  have hH' : ∀ i j k : Fin 3, i ≠ j → k ≠ i → k ≠ j →
      s k ≥ (nA e i j) ^ 2 / (nS (avg a b) i j) ^ 2 := by
    intro i j k hij hki hkj
    have h1 := hH i j k hij hki hkj
    have hpos : 0 < (a i + a j) * (b i + b j) :=
      mul_pos (by linarith [ha0 i, ha0 j]) (by linarith [hb0 i, hb0 j])
    have heq : nS (avg a b) i j = (a i + b i + a j + b j) / 2 := by
      unfold nS avg
      ring
    have hle : (a i + a j) * (b i + b j) ≤ (nS (avg a b) i j) ^ 2 := by
      rw [heq]
      exact four_mul_le_sq (a i) (b i) (a j) (b j)
    calc s k ≥ (nA e i j) ^ 2 / ((a i + a j) * (b i + b j)) := h1
      _ ≥ (nA e i j) ^ 2 / (nS (avg a b) i j) ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg (nA e i j)) hpos hle
  have hQ' : ∀ i j k : Fin 3, i ≠ j → k ≠ i → k ≠ j →
      s k ≥ (e i j + e j i) ^ 2 / (4 * avg a b i * avg a b j) := by
    intro i j k hij hki hkj
    have h1 := hQ1 i j k hij hki hkj
    have h2 := hQ2 i j k hij hki hkj
    have hab : 0 < a i * b j := mul_pos (ha0 i) (hb0 j)
    have hcd : 0 < a j * b i := mul_pos (ha0 j) (hb0 i)
    have hmax := sq_div_le_max_sq_div (x := e i j) (y := e j i) (c := a i * b j)
      (d := a j * b i) (he0 i j) (he0 j i) hab hcd
    have hβ : (Real.sqrt (a i * b j) + Real.sqrt (a j * b i)) ^ 2
        ≤ 4 * avg a b i * avg a b j := by
      have hs := sqrt_mul_add_sqrt_mul_le (a := a i) (b := b j) (c := b i) (d := a j)
        (ha0 i).le (hb0 j).le (hb0 i).le (ha0 j).le
      have hs' : Real.sqrt (a i * b j) + Real.sqrt (a j * b i)
          ≤ Real.sqrt ((a i + b i) * (a j + b j)) := by
        simpa [add_comm, mul_comm] using hs
      have hsq : (Real.sqrt (a i * b j) + Real.sqrt (a j * b i)) ^ 2
          ≤ (a i + b i) * (a j + b j) := by
        have h := Real.sq_sqrt (mul_nonneg (by linarith [ha0 i, hb0 i])
          (by linarith [ha0 j, hb0 j]) : (0:ℝ) ≤ (a i + b i) * (a j + b j))
        rw [← h]
        exact pow_le_pow_left₀ (by positivity) hs' 2
      unfold avg
      nlinarith [hsq]
    have hstep : (e i j + e j i) ^ 2 / (4 * avg a b i * avg a b j) ≤ s k := by
      refine le_trans ?_ (max_le h1 h2)
      calc (e i j + e j i) ^ 2 / (4 * avg a b i * avg a b j)
          ≤ (e i j + e j i) ^ 2
              / ((Real.sqrt (a i * b j) + Real.sqrt (a j * b i)) ^ 2) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hβ
        _ ≤ max ((e i j) ^ 2 / (a i * b j)) ((e j i) ^ 2 / (a j * b i)) := hmax
    exact hstep
  have hF' : ∀ i j k : Fin 3, i ≠ j → k ≠ i → k ≠ j →
      s i + s j ≥ (nN e i j k) ^ 2 / (4 * avg a b k) := by
    intro i j k hij hki hkj
    have h1 := hF1 i j k hij hki hkj
    have h2 := hF2 i j k hij hki hkj
    have hrow : 0 ≤ e k 0 + e k 1 + e k 2 := by linarith [he0 k 0, he0 k 1, he0 k 2]
    have hcol : 0 ≤ e 0 k + e 1 k + e 2 k := by linarith [he0 0 k, he0 1 k, he0 2 k]
    have hmax := sq_div_le_max_sq_div (x := e k 0 + e k 1 + e k 2)
      (y := e 0 k + e 1 k + e 2 k) (c := a k) (d := b k) hrow hcol (ha0 k) (hb0 k)
    have hβ : (Real.sqrt (a k) + Real.sqrt (b k)) ^ 2 ≤ 4 * avg a b k := by
      have h := sq_sqrt_add_le (ha0 k).le (hb0 k).le
      unfold avg
      nlinarith [h]
    have hstep : ((e k 0 + e k 1 + e k 2) + (e 0 k + e 1 k + e 2 k)) ^ 2 / (4 * avg a b k) ≤ s i + s j := by
      refine le_trans ?_ (max_le h1 h2)
      calc ((e k 0 + e k 1 + e k 2) + (e 0 k + e 1 k + e 2 k)) ^ 2 / (4 * avg a b k)
          ≤ ((e k 0 + e k 1 + e k 2) + (e 0 k + e 1 k + e 2 k)) ^ 2
              / ((Real.sqrt (a k) + Real.sqrt (b k)) ^ 2) :=
            div_le_div_of_nonneg_left (sq_nonneg _)
              (pow_pos (by have := Real.sqrt_pos_of_pos (ha0 k); have := Real.sqrt_pos_of_pos (hb0 k); linarith) 2) hβ
        _ ≤ max ((e k 0 + e k 1 + e k 2) ^ 2 / a k) ((e 0 k + e 1 k + e 2 k) ^ 2 / b k) := hmax
    rw [nN_eq_rows e hij (Ne.symm hki) (Ne.symm hkj)]
    exact hstep
  by_cases hcase : ∃ k : Fin 3, avg a b k ≤ 9314 / 100000
  · obtain ⟨k, hk⟩ := hcase
    obtain ⟨i, j, hij, hik, hjk⟩ := exists_pair_ne k
    exact caseI_aux (avg_pos ha0 hb0) (avg_sum ha1 hb1) he0 he1 hs0 hH' hQ' hF'
      hij hik hjk hk
  · push Not at hcase
    exact caseII_aux (avg_pos ha0 hb0) (avg_sum ha1 hb1) he0 he1 hs0 hH' hQ' hF'
      (fun i => le_of_lt (hcase i)) hII

/-- Theorem 3, conditional on the explicit two-variable inequality
`CaseIIBound`. -/
theorem theorem3_of_caseII (hII : CaseIIBound) :
    IsMonotoneGraphExponent 3 ((769 : ℝ) / 1000) :=
  theorem3_of_main_0_769 (mainCase_of_numeric (mainNumeric_0_769 hII))

noncomputable section

/-! ### Section VII: the edge maximum of the normalised sum

We formalise the one-variable analysis of the boundary `z = t_chi` of the
domain `{p_i >= t_chi}`.  With `u = sqrt x`, `v = sqrt y`, `w = sqrt t`,
`x + y = 1 - t` and `theta = 1538/269`, the boundary estimate reduces to
`EdgePsi : phi x <= phi (thrS - x)` on `(t_chi, thrS / 2)`, where

`phi x = sqrt x * ((sqrt x + sqrt y)^(theta-1) + (sqrt y + sqrt t)^(theta-1))`.

`EdgePsi` is proved below from the pointwise Hermite--Hadamard estimate `edgeS`
and the trapezoid inequality `rpow_sec_le_trap`. -/




def thrT : ℝ := 9314 / 100000
def thrS : ℝ := 90686 / 100000
def thrTheta : ℝ := 1538 / 269

lemma thrT_pos : 0 < thrT := by unfold thrT; norm_num
lemma thrS_eq : thrS = 1 - thrT := by unfold thrS thrT; norm_num
lemma thrS_pos : 0 < thrS := by unfold thrS; norm_num
/-- The auxiliary one-variable function entering the edge inequality `EdgePsi`. -/
def phi (x : ℝ) : ℝ :=
  Real.sqrt x * ((Real.sqrt x + Real.sqrt (thrS - x)) ^ (thrTheta - 1)
    + (Real.sqrt (thrS - x) + Real.sqrt thrT) ^ (thrTheta - 1))

def edgeG (x : ℝ) : ℝ :=
  (Real.sqrt x + Real.sqrt (thrS - x)) ^ thrTheta + (Real.sqrt x + Real.sqrt thrT) ^ thrTheta
    + (Real.sqrt (thrS - x) + Real.sqrt thrT) ^ thrTheta

lemma phi_eS_sub (x : ℝ) : phi (thrS - x) =
    Real.sqrt (thrS - x) * ((Real.sqrt x + Real.sqrt (thrS - x)) ^ (thrTheta - 1)
      + (Real.sqrt x + Real.sqrt thrT) ^ (thrTheta - 1)) := by
  unfold phi
  rw [show thrS - (thrS - x) = x by ring, add_comm (Real.sqrt (thrS - x)) (Real.sqrt x)]

def edgeGde (x : ℝ) : ℝ := thrTheta * (phi (thrS - x) - phi x) / (2 * Real.sqrt x * Real.sqrt (thrS - x))

theorem hasDerivAt_gOne {x : ℝ} (hx0 : 0 < x) (hy0 : 0 < thrS - x) :
    HasDerivAt edgeG (edgeGde x) x := by
  have hs1 : HasDerivAt (fun x : ℝ => Real.sqrt x) (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt hx0.ne'
  have hs2 : HasDerivAt (fun x : ℝ => Real.sqrt (thrS - x)) (-(1 / (2 * Real.sqrt (thrS - x)))) x := by
    have hinner : HasDerivAt (fun x : ℝ => thrS - x) (-1) x := by
      have h := (hasDerivAt_const (x := x) thrS).sub (hasDerivAt_id (x := x) : HasDerivAt (fun y : ℝ => y) 1 x)
      convert h using 1
      · ext y; simp
      · norm_num
    have hout : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (thrS - x))) (thrS - x) :=
      Real.hasDerivAt_sqrt hy0.ne'
    have := hout.comp x hinner
    simpa [Function.comp_def] using this
  have hA1 : (0:ℝ) < Real.sqrt x + Real.sqrt (thrS - x) := by
    have h2 := Real.sqrt_pos_of_pos hy0; have h3 := Real.sqrt_pos_of_pos hx0; linarith
  have hB1 : (0:ℝ) < Real.sqrt x + Real.sqrt thrT := by
    have h2 := Real.sqrt_pos_of_pos hx0; have h3 := Real.sqrt_pos_of_pos thrT_pos; linarith
  have hC1 : (0:ℝ) < Real.sqrt (thrS - x) + Real.sqrt thrT := by
    have h2 := Real.sqrt_pos_of_pos hy0; have h3 := Real.sqrt_pos_of_pos thrT_pos; linarith
  have hA : HasDerivAt (fun x : ℝ => Real.sqrt x + Real.sqrt (thrS - x))
      (1 / (2 * Real.sqrt x) + -(1 / (2 * Real.sqrt (thrS - x)))) x := hs1.add hs2
  have hB : HasDerivAt (fun x : ℝ => Real.sqrt x + Real.sqrt thrT) (1 / (2 * Real.sqrt x) + 0) x :=
    hs1.add (hasDerivAt_const (x := x) (Real.sqrt thrT))
  have hC : HasDerivAt (fun x : ℝ => Real.sqrt (thrS - x) + Real.sqrt thrT)
      (-(1 / (2 * Real.sqrt (thrS - x))) + 0) x :=
    hs2.add (hasDerivAt_const (x := x) (Real.sqrt thrT))
  have hAp : HasDerivAt (fun x : ℝ => (Real.sqrt x + Real.sqrt (thrS - x)) ^ thrTheta)
      (thrTheta * (Real.sqrt x + Real.sqrt (thrS - x)) ^ (thrTheta - 1)
        * (1 / (2 * Real.sqrt x) + -(1 / (2 * Real.sqrt (thrS - x))))) x := by
    have h := (Real.hasDerivAt_rpow_const (x := Real.sqrt x + Real.sqrt (thrS - x)) (p := thrTheta)
      (Or.inl hA1.ne')).comp x hA
    simpa [Function.comp_def] using h
  have hBp : HasDerivAt (fun x : ℝ => (Real.sqrt x + Real.sqrt thrT) ^ thrTheta)
      (thrTheta * (Real.sqrt x + Real.sqrt thrT) ^ (thrTheta - 1) * (1 / (2 * Real.sqrt x) + 0)) x := by
    have h := (Real.hasDerivAt_rpow_const (x := Real.sqrt x + Real.sqrt thrT) (p := thrTheta)
      (Or.inl hB1.ne')).comp x hB
    simpa [Function.comp_def] using h
  have hCp : HasDerivAt (fun x : ℝ => (Real.sqrt (thrS - x) + Real.sqrt thrT) ^ thrTheta)
      (thrTheta * (Real.sqrt (thrS - x) + Real.sqrt thrT) ^ (thrTheta - 1)
        * (-(1 / (2 * Real.sqrt (thrS - x))) + 0)) x := by
    have h := (Real.hasDerivAt_rpow_const (x := Real.sqrt (thrS - x) + Real.sqrt thrT) (p := thrTheta)
      (Or.inl hC1.ne')).comp x hC
    simpa [Function.comp_def] using h
  have hsum := (hAp.add hBp).add hCp
  rw [show edgeG = (((fun x : ℝ => (Real.sqrt x + Real.sqrt (thrS - x)) ^ thrTheta)
      + fun x => (Real.sqrt x + Real.sqrt thrT) ^ thrTheta) + fun x => (Real.sqrt (thrS - x) + Real.sqrt thrT) ^ thrTheta) by
    ext y; simp [edgeG]]
  convert hsum using 1
  unfold edgeGde
  rw [phi_eS_sub]
  unfold phi
  have hx : Real.sqrt x ≠ 0 := (Real.sqrt_pos_of_pos hx0).ne'
  have hy : Real.sqrt (thrS - x) ≠ 0 := (Real.sqrt_pos_of_pos hy0).ne'
  field_simp
  ring

/-- The remaining analytic inequality of the edge analysis: `phi (s - x) >= phi x`. -/
def EdgePsi : Prop := ∀ x : ℝ, thrT < x → x < thrS / 2 → phi x ≤ phi (thrS - x)

theorem gOne_monoOn_of_edgePsi (hpsi : EdgePsi) : MonotoneOn edgeG (Set.Icc thrT (thrS / 2)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
  · intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le thrT_pos hx.1
    have hy0 : 0 < thrS - x := by linarith [hx.2, thrS_pos]
    exact (hasDerivAt_gOne hx0 hy0).continuousAt.continuousWithinAt
  · intro x hx
    have hxI := interior_subset hx
    have hx0 : 0 < x := lt_of_lt_of_le thrT_pos hxI.1
    have hy0 : 0 < thrS - x := by linarith [hxI.2, thrS_pos]
    exact (hasDerivAt_gOne hx0 hy0).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hx0 : 0 < x := lt_trans thrT_pos hx.1
    have hy0 : 0 < thrS - x := by linarith [hx.2, thrS_pos]
    rw [(hasDerivAt_gOne hx0 hy0).deriv]
    unfold edgeGde
    have hge : 0 ≤ phi (thrS - x) - phi x := by have := hpsi x hx.1 hx.2; linarith
    have hth : 0 < thrTheta := by unfold thrTheta; norm_num
    have hnum : 0 ≤ thrTheta * (phi (thrS - x) - phi x) := mul_nonneg hth.le hge
    exact div_nonneg hnum (by positivity)

theorem edgeBound_of_edgePsi (hpsi : EdgePsi) {x : ℝ} (hx : x ∈ Set.Icc thrT (thrS / 2)) :
    edgeG x ≤ edgeG (thrS / 2) := by
  have hmem : thrS / 2 ∈ Set.Icc thrT (thrS / 2) := by
    refine ⟨?_, le_refl _⟩
    unfold thrT thrS; norm_num
  exact gOne_monoOn_of_edgePsi hpsi hx hmem hx.2

/-- The value of the normalised sum at the corner. -/
def cornerVal3 : ℝ :=
  ((45343 : ℝ) / 50000) ^ ((769 : ℝ) / 269)
    + 2 * (((54657 : ℝ) / 200000 + Real.sqrt ((211162351 : ℝ) / 5000000000)) ^ ((769 : ℝ) / 269))

/-- Converting the `θ = 1538/269` form to the `(A^2/2)^(769/269)` form. -/
theorem sq_half_rpow {A : ℝ} (hA : 0 ≤ A) :
    (A ^ 2 / 2) ^ ((769 : ℝ) / 269)
      = (2 : ℝ) ^ (-((769 : ℝ) / 269)) * A ^ (1538 / 269 : ℝ) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hA2 : A ^ 2 = A ^ (2 : ℝ) := (Real.rpow_natCast A 2).symm
  have h3 : (A ^ 2) ^ ((769 : ℝ) / 269) = A ^ (1538 / 269 : ℝ) := by
    rw [hA2, ← Real.rpow_mul hA]
    norm_num
  rw [Real.div_rpow (sq_nonneg A) h2.le, h3, Real.rpow_neg h2.le, div_eq_inv_mul]

/-- The normalised sum on the edge equals `2^(-q)` times the `θ`-power form. -/
theorem edge_sum_eq {x : ℝ} (hx0 : 0 ≤ x) (hy0 : 0 ≤ thrS - x) :
    ((Real.sqrt x + Real.sqrt (thrS - x)) ^ 2 / 2) ^ ((769 : ℝ) / 269)
      + ((Real.sqrt x + Real.sqrt thrT) ^ 2 / 2) ^ ((769 : ℝ) / 269)
      + ((Real.sqrt (thrS - x) + Real.sqrt thrT) ^ 2 / 2) ^ ((769 : ℝ) / 269)
    = (2 : ℝ) ^ (-((769 : ℝ) / 269)) * edgeG x := by
  rw [sq_half_rpow (by positivity), sq_half_rpow (by positivity), sq_half_rpow (by positivity)]
  unfold edgeG thrTheta
  ring

/-- The value of the edge function at the midpoint, in normalised form. -/
theorem edgeG_mid_val :
    (2 : ℝ) ^ (-((769 : ℝ) / 269)) * edgeG (thrS / 2) = cornerVal3 := by
  have hs2 : (0 : ℝ) < thrS / 2 := by unfold thrS; norm_num
  have hA2 : (2 * Real.sqrt (thrS / 2)) ^ 2 / 2 = thrS := by
    have h : Real.sqrt (thrS / 2) ^ 2 = thrS / 2 := Real.sq_sqrt hs2.le
    nlinarith
  have hB2 : (Real.sqrt (thrS / 2) + Real.sqrt thrT) ^ 2 / 2
      = (54657 : ℝ) / 200000 + Real.sqrt ((211162351 : ℝ) / 5000000000) := by
    have h1 : Real.sqrt (thrS / 2) ^ 2 = thrS / 2 := Real.sq_sqrt hs2.le
    have h2 : Real.sqrt thrT ^ 2 = thrT := Real.sq_sqrt thrT_pos.le
    have h3 : Real.sqrt (thrS / 2) * Real.sqrt thrT = Real.sqrt ((thrS / 2) * thrT) :=
      (Real.sqrt_mul hs2.le thrT).symm
    have h4 : (thrS / 2) * thrT = (211162351 : ℝ) / 5000000000 := by unfold thrS thrT; norm_num
    rw [h4] at h3
    have h5 : (Real.sqrt (thrS / 2) + Real.sqrt thrT) ^ 2
        = thrS / 2 + thrT + 2 * Real.sqrt ((211162351 : ℝ) / 5000000000) := by
      nlinarith [h1, h2, h3]
    rw [h5]
    have hsum : thrS / 2 + thrT = (54657 : ℝ) / 100000 := by unfold thrS thrT; norm_num
    rw [hsum]
    ring
  have hfirst : (2 : ℝ) ^ (-((769 : ℝ) / 269)) * (2 * Real.sqrt (thrS / 2)) ^ thrTheta
      = ((45343 : ℝ) / 50000) ^ ((769 : ℝ) / 269) := by
    unfold thrTheta
    rw [← sq_half_rpow (by positivity : (0:ℝ) ≤ 2 * Real.sqrt (thrS / 2)), hA2]
    have : thrS = (45343 : ℝ) / 50000 := by unfold thrS; norm_num
    rw [this]
  have hsecond : (2 : ℝ) ^ (-((769 : ℝ) / 269)) * (Real.sqrt (thrS / 2) + Real.sqrt thrT) ^ thrTheta
      = ((54657 : ℝ) / 200000 + Real.sqrt ((211162351 : ℝ) / 5000000000)) ^ ((769 : ℝ) / 269) := by
    unfold thrTheta
    rw [← sq_half_rpow (by positivity), hB2]
  unfold edgeG cornerVal3
  rw [show thrS - thrS / 2 = thrS / 2 by ring]
  rw [show Real.sqrt (thrS / 2) + Real.sqrt (thrS / 2) = 2 * Real.sqrt (thrS / 2) by ring]
  linear_combination hfirst + 2 * hsecond

theorem edge_one_dim (hpsi : EdgePsi) {x y : ℝ} (hx : thrT ≤ x) (hy : thrT ≤ y) (hxy : x + y = thrS) :
    ((Real.sqrt x + Real.sqrt y) ^ 2 / 2) ^ ((769 : ℝ) / 269)
      + ((Real.sqrt x + Real.sqrt thrT) ^ 2 / 2) ^ ((769 : ℝ) / 269)
      + ((Real.sqrt y + Real.sqrt thrT) ^ 2 / 2) ^ ((769 : ℝ) / 269) ≤ cornerVal3 := by
  have hq : (0:ℝ) < (2:ℝ) ^ (-((769 : ℝ) / 269)) := Real.rpow_pos_of_pos (by norm_num) _
  have key : ∀ a b : ℝ, thrT ≤ a → a ≤ thrS / 2 → a + b = thrS →
      ((Real.sqrt a + Real.sqrt b) ^ 2 / 2) ^ ((769 : ℝ) / 269)
        + ((Real.sqrt a + Real.sqrt thrT) ^ 2 / 2) ^ ((769 : ℝ) / 269)
        + ((Real.sqrt b + Real.sqrt thrT) ^ 2 / 2) ^ ((769 : ℝ) / 269) ≤ cornerVal3 := by
    intro a b ha ha2 hab
    have hb : b = thrS - a := by linarith
    rw [hb, edge_sum_eq (by linarith [thrT_pos]) (by linarith [thrS_pos]), ← edgeG_mid_val]
    exact mul_le_mul_of_nonneg_left (edgeBound_of_edgePsi hpsi ⟨ha, ha2⟩) hq.le
  rcases lt_or_ge x y with hlt | hge
  · exact key x y hx (by linarith) hxy
  · have hs : ((Real.sqrt x + Real.sqrt y) ^ 2 / 2) ^ ((769 : ℝ) / 269)
        + ((Real.sqrt x + Real.sqrt thrT) ^ 2 / 2) ^ ((769 : ℝ) / 269)
        + ((Real.sqrt y + Real.sqrt thrT) ^ 2 / 2) ^ ((769 : ℝ) / 269)
        = ((Real.sqrt y + Real.sqrt x) ^ 2 / 2) ^ ((769 : ℝ) / 269)
        + ((Real.sqrt y + Real.sqrt thrT) ^ 2 / 2) ^ ((769 : ℝ) / 269)
        + ((Real.sqrt x + Real.sqrt thrT) ^ 2 / 2) ^ ((769 : ℝ) / 269) := by
      rw [add_comm (Real.sqrt x) (Real.sqrt y)]
      ring
    rw [hs]
    exact key y x hy (by linarith) (by linarith)

/-! ### Auxiliary power inequalities for the edge certificate -/

theorem rpow_div_le {z M : ℝ} {m n : ℕ} (hn : 0 < n) (hz : 0 ≤ z) (hM : 0 < M)
    (h : z ^ m ≤ M ^ n) : z ^ ((m : ℝ) / n) ≤ M := by
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have h1 : z ^ ((m : ℝ) / n) = (z ^ (m:ℝ)) ^ ((1:ℝ)/n) := by
    rw [show ((m:ℝ)/n) = (m:ℝ) * (1/(n:ℝ)) by field_simp, Real.rpow_mul hz]
  have h2 : M = (M ^ (n:ℝ)) ^ ((1:ℝ)/n) := by
    rw [← Real.rpow_mul (le_of_lt hM)]
    rw [show (n:ℝ) * (1/(n:ℝ)) = 1 by field_simp, Real.rpow_one]
  rw [h1, h2]
  refine Real.rpow_le_rpow ?_ ?_ (by positivity)
  · rw [Real.rpow_natCast]; positivity
  · rwa [Real.rpow_natCast, Real.rpow_natCast]

theorem le_rpow_div {z M : ℝ} {m n : ℕ} (hn : 0 < n) (hz : 0 < z) (hM : 0 ≤ M)
    (h : M ^ n ≤ z ^ m) : M ≤ z ^ ((m : ℝ) / n) := by
  have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have h1 : M = (M ^ (n:ℝ)) ^ ((1:ℝ)/n) := by
    rw [← Real.rpow_mul hM]
    rw [show (n:ℝ) * (1/(n:ℝ)) = 1 by field_simp, Real.rpow_one]
  have h2 : z ^ ((m : ℝ) / n) = (z ^ (m:ℝ)) ^ ((1:ℝ)/n) := by
    rw [show ((m:ℝ)/n) = (m:ℝ) * (1/(n:ℝ)) by field_simp, Real.rpow_mul hz.le]
  rw [h1, h2]
  refine Real.rpow_le_rpow ?_ ?_ (by positivity)
  · rw [Real.rpow_natCast]; positivity
  · rwa [Real.rpow_natCast, Real.rpow_natCast]

/-- Tangent inequality at `u` for `z ↦ z ^ p`, evaluated at `1`. -/
theorem rpow_sub_one_le {u p : ℝ} (hu : 1 < u) (hp : 1 ≤ p) :
    u ^ p - 1 ≤ p * (u - 1) * u ^ (p - 1) := by
  have hu0 : (0:ℝ) < u := by linarith
  have hconv : ConvexOn ℝ (Set.Ici (0:ℝ)) (fun z : ℝ => z ^ p) := convexOn_rpow hp
  have hsl := hconv.slope_le_of_hasDerivAt (x := 1) (y := u) (by norm_num)
    (Set.mem_Ici.mpr hu0.le) hu (Real.hasDerivAt_rpow_const (p := p) (Or.inl hu0.ne'))
  rw [slope_def_field, Real.one_rpow] at hsl
  rw [div_le_iff₀ (by linarith : (0:ℝ) < u - 1)] at hsl
  linarith

/-- Trapezoid inequality for `z ↦ z ^ q` on `[c, b]`, `q ≥ 2`. -/
theorem rpow_sec_le_trap {q : ℝ} (hq : 2 ≤ q) {c b : ℝ} (hc : 0 < c) (hcb : c ≤ b) :
    b ^ q - c ^ q ≤ q * (b - c) * (b ^ (q - 1) + c ^ (q - 1)) / 2 := by
  rcases lt_or_eq_of_le hcb with hlt | heq
  swap
  · subst heq; simp
  have hb0 : 0 < b := lt_trans hc hlt
  set r := b / c with hr
  have hr0 : 0 < r := by rw [hr]; exact div_pos hb0 hc
  have hr1 : 1 < r := by rw [hr, lt_div_iff₀ hc]; linarith
  have hb : b = r * c := by rw [hr]; field_simp
  have hq1 : (1:ℝ) ≤ q - 1 := by linarith
  have hq2 : q - 1 - 1 = q - 2 := by ring
  have key : r ^ q - 1 ≤ q * (r - 1) * (r ^ (q - 1) + 1) / 2 := by
    set F : ℝ → ℝ := fun t => q / 2 * ((t - 1) * (t ^ (q - 1) + 1)) - (t ^ q - 1) with hF
    have hF1 : F 1 = 0 := by simp [hF]
    have hda : ∀ t : ℝ, 0 < t → HasDerivAt F
        (q / 2 * (1 * (t ^ (q - 1) + 1) + (t - 1) * ((q - 1) * t ^ (q - 2))) - q * t ^ (q - 1)) t := by
      intro t ht0
      rw [hF]
      have h1 : HasDerivAt (fun t : ℝ => t ^ (q - 1) + 1) ((q - 1) * t ^ (q - 2)) t := by
        have hh := (Real.hasDerivAt_rpow_const (p := q - 1) (Or.inl ht0.ne')).add_const 1
        rw [hq2] at hh
        simpa using hh
      have h2 : HasDerivAt (fun t : ℝ => t - 1) 1 t := by
        simpa using (hasDerivAt_id t).sub_const 1
      have h3 := h2.mul h1
      have h4 := h3.const_mul (q / 2)
      have h5 : HasDerivAt (fun t : ℝ => t ^ q - 1) (q * t ^ (q - 1)) t := by
        simpa using (Real.hasDerivAt_rpow_const (p := q) (Or.inl ht0.ne')).sub_const 1
      exact h4.sub h5
    have hnonneg : ∀ t ∈ interior (Set.Ici (1:ℝ)), 0 ≤ deriv F t := by
      intro t ht
      rw [interior_Ici, Set.mem_Ioi] at ht
      have ht0 : 0 < t := by linarith
      rw [(hda t ht0).deriv]
      have htan := rpow_sub_one_le ht hq1
      rw [hq2] at htan
      have hP : 0 ≤ 1 + (q - 1) * (t - 1) * t ^ (q - 2) - t ^ (q - 1) := by linarith
      have hq0 : (0:ℝ) ≤ q / 2 := by linarith
      nlinarith [mul_nonneg hq0 hP, Real.rpow_pos_of_pos ht0 (q - 1)]
    have hmono : MonotoneOn F (Set.Ici (1:ℝ)) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici (1:ℝ)) ?_ ?_ hnonneg
      · intro t ht
        rw [Set.mem_Ici] at ht
        exact (hda t (by linarith)).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Ici, Set.mem_Ioi] at ht
        exact (hda t (by linarith)).differentiableAt.differentiableWithinAt
    have hstep := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hr1.le) hr1.le
    rw [hF1] at hstep
    simp only [hF] at hstep
    linarith
  have hcq : (0:ℝ) < c ^ q := Real.rpow_pos_of_pos hc q
  have hcqq : c * c ^ (q - 1) = c ^ q := by
    nth_rewrite 1 [← Real.rpow_one c]
    rw [← Real.rpow_add hc]
    congr 1
    ring
  rw [hb, Real.mul_rpow hr0.le hc.le, Real.mul_rpow hr0.le hc.le]
  have h1 : r ^ q * c ^ q - c ^ q = c ^ q * (r ^ q - 1) := by ring
  have h2 : q * (r * c - c) * (r ^ (q - 1) * c ^ (q - 1) + c ^ (q - 1)) / 2
      = c ^ q * (q * (r - 1) * (r ^ (q - 1) + 1) / 2) := by
    linear_combination (q * (r - 1) * (r ^ (q - 1) + 1) / 2) * hcqq
  rw [h1, h2]
  exact mul_le_mul_of_nonneg_left key hcq.le

/-- `c ≤ z ^ (193/269)` from a rational kernel check `c ^ 269 ≤ z ^ 193`. -/
theorem rpow_frac_le {c z : ℚ} (hc : 0 ≤ c) (hz : 0 < z) (h : c ^ 269 ≤ z ^ 193) :
    (c : ℝ) ≤ (z : ℝ) ^ ((193 : ℝ) / 269) := by
  have hh : (c : ℝ) ^ 269 ≤ (z : ℝ) ^ 193 := by exact_mod_cast h
  exact le_rpow_div (z := (z:ℝ)) (M := (c:ℝ)) (m := 193) (n := 269) (by norm_num) (by exact_mod_cast hz) (by exact_mod_cast hc) hh

/-- `z ^ (193/269) ≤ c` from a rational kernel check `z ^ 193 ≤ c ^ 269`. -/
theorem le_rpow_frac {c z : ℚ} (hc : 0 < c) (hz : 0 < z) (h : z ^ 193 ≤ c ^ 269) :
    (z : ℝ) ^ ((193 : ℝ) / 269) ≤ (c : ℝ) := by
  have hh : (z : ℝ) ^ 193 ≤ (c : ℝ) ^ 269 := by exact_mod_cast h
  exact rpow_div_le (z := (z:ℝ)) (M := (c:ℝ)) (m := 193) (n := 269) (by norm_num) (by exact_mod_cast hz.le) (by exact_mod_cast hc) hh

lemma p_split : thrTheta - 1 = 4 + ((193 : ℝ) / 269) := by unfold thrTheta; norm_num
lemma q_split : thrTheta - 2 = 3 + ((193 : ℝ) / 269) := by unfold thrTheta; norm_num

lemma rpow_p_eq {Z : ℝ} (hZ : 0 < Z) : Z ^ (thrTheta - 1) = Z ^ 4 * Z ^ ((193 : ℝ) / 269) := by
  rw [p_split, Real.rpow_add hZ]
  norm_num

lemma rpow_q_eq {Z : ℝ} (hZ : 0 < Z) : Z ^ (thrTheta - 2) = Z ^ 3 * Z ^ ((193 : ℝ) / 269) := by
  rw [q_split, Real.rpow_add hZ]
  norm_num

set_option maxHeartbeats 2000000

theorem edgeS_0 {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hs : u ^ 2 + v ^ 2 = thrS)
    (ha : ((61 : ℝ)/200) ≤ u) (hb : u ≤ ((177 : ℝ)/500)) :
    u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (u + v) ^ (thrTheta - 1) + (u + Real.sqrt thrT) ^ (thrTheta - 1) := by
  have hv0 : 0 < v := lt_of_lt_of_le hu huv
  have hth1 : thrTheta - 1 = ((1269:ℝ)/269) := by unfold thrTheta; norm_num
  have hwlo : ((3051 : ℝ)/10000) ≤ Real.sqrt thrT := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num [thrT]
  have hwhi : Real.sqrt thrT ≤ ((763 : ℝ)/2500) := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num [thrT]
  have hv2 : v ^ 2 = thrS - u ^ 2 := by linarith
  have hvlo : ((221 : ℝ)/250) ≤ v := by
    have h1 : (((221 : ℝ)/250)) ^ 2 ≤ v ^ 2 := by rw [hv2]; unfold thrS; nlinarith
    nlinarith [h1, hv0, (by norm_num : (0:ℝ) ≤ ((221 : ℝ)/250))]
  have hvhi : v ≤ ((4511 : ℝ)/5000) := by
    have h1 : v ^ 2 ≤ (((4511 : ℝ)/5000)) ^ 2 := by rw [hv2]; unfold thrS; nlinarith
    nlinarith [h1, hv0, (by norm_num : (0:ℝ) ≤ ((4511 : ℝ)/5000))]
  have hL1 : (((1189 : ℝ)/1000))^4 * (((283 : ℝ)/250)) ≤ (u + v) ^ (thrTheta - 1) := by
    rw [rpow_p_eq (by positivity)]
    have hce : ((283 : ℝ)/250) ≤ (((1189 : ℝ)/1000)) ^ ((193:ℝ)/269) := by
      simpa using rpow_frac_le (c := ((283 : ℚ)/250)) (z := ((1189 : ℚ)/1000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : ((1189 : ℝ)/1000) ≤ u + v := by linarith
    have hZ : (((1189 : ℝ)/1000))^4 ≤ (u + v)^4 := pow_le_pow_left₀ (by norm_num) hA 4
    have he : (((1189 : ℝ)/1000)) ^ ((193:ℝ)/269) ≤ (u + v) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by norm_num) hA (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hce (by positivity)) (mul_le_mul hZ he (by positivity) (by positivity))
  have hL2 : (((6101 : ℝ)/10000))^4 * (((701 : ℝ)/1000)) ≤ (u + Real.sqrt thrT) ^ (thrTheta - 1) := by
    rw [rpow_p_eq (by positivity)]
    have hce : ((701 : ℝ)/1000) ≤ (((6101 : ℝ)/10000)) ^ ((193:ℝ)/269) := by
      simpa using rpow_frac_le (c := ((701 : ℚ)/1000)) (z := ((6101 : ℚ)/10000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : ((6101 : ℝ)/10000) ≤ u + Real.sqrt thrT := by linarith
    have hZ : (((6101 : ℝ)/10000))^4 ≤ (u + Real.sqrt thrT)^4 := pow_le_pow_left₀ (by norm_num) hA 4
    have he : (((6101 : ℝ)/10000)) ^ ((193:ℝ)/269) ≤ (u + Real.sqrt thrT) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by norm_num) hA (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hce (by positivity)) (mul_le_mul hZ he (by positivity) (by positivity))
  have hQ1 : (u + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((412 : ℝ)/625))^3 * (((371 : ℝ)/500)) := by
    rw [rpow_q_eq (by positivity)]
    have hce : (((412 : ℝ)/625)) ^ ((193:ℝ)/269) ≤ ((371 : ℝ)/500) := by
      simpa using le_rpow_frac (c := ((371 : ℚ)/500)) (z := ((412 : ℚ)/625)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : u + Real.sqrt thrT ≤ ((412 : ℝ)/625) := by linarith
    have hZ : (u + Real.sqrt thrT)^3 ≤ (((412 : ℝ)/625))^3 := pow_le_pow_left₀ (by positivity) hA 3
    have he : (u + Real.sqrt thrT) ^ ((193:ℝ)/269) ≤ (((412 : ℝ)/625)) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by positivity) hA (by norm_num)
    calc (u + Real.sqrt thrT)^3 * (u + Real.sqrt thrT)^((193:ℝ)/269)
        ≤ (((412 : ℝ)/625))^3 * (((412 : ℝ)/625))^((193:ℝ)/269) := mul_le_mul hZ he (by positivity) (by positivity)
      _ ≤ (((412 : ℝ)/625))^3 * (((371 : ℝ)/500)) := mul_le_mul_of_nonneg_left hce (by positivity)
  have hQ2 : (v + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((6037 : ℝ)/5000))^3 * (((229 : ℝ)/200)) := by
    rw [rpow_q_eq (by positivity)]
    have hce : (((6037 : ℝ)/5000)) ^ ((193:ℝ)/269) ≤ ((229 : ℝ)/200) := by
      simpa using le_rpow_frac (c := ((229 : ℚ)/200)) (z := ((6037 : ℚ)/5000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : v + Real.sqrt thrT ≤ ((6037 : ℝ)/5000) := by linarith
    have hZ : (v + Real.sqrt thrT)^3 ≤ (((6037 : ℝ)/5000))^3 := pow_le_pow_left₀ (by positivity) hA 3
    have he : (v + Real.sqrt thrT) ^ ((193:ℝ)/269) ≤ (((6037 : ℝ)/5000)) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by positivity) hA (by norm_num)
    calc (v + Real.sqrt thrT)^3 * (v + Real.sqrt thrT)^((193:ℝ)/269)
        ≤ (((6037 : ℝ)/5000))^3 * (((6037 : ℝ)/5000))^((193:ℝ)/269) := mul_le_mul hZ he (by positivity) (by positivity)
      _ ≤ (((6037 : ℝ)/5000))^3 * (((229 : ℝ)/200)) := mul_le_mul_of_nonneg_left hce (by positivity)
  have hkey : ((177 : ℝ)/500) * ((1269:ℝ)/269) * ((((412 : ℝ)/625))^3 * (((371 : ℝ)/500)) + (((6037 : ℝ)/5000))^3 * (((229 : ℝ)/200))) / 2 ≤ (((1189 : ℝ)/1000))^4 * (((283 : ℝ)/250)) + (((6101 : ℝ)/10000))^4 * (((701 : ℝ)/1000)) := by
    norm_num
  have hs0 : (0:ℝ) ≤ (v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2) := by
    have h1 : (0:ℝ) ≤ (v + Real.sqrt thrT) ^ (thrTheta - 2) := Real.rpow_nonneg (by linarith) _
    have h2 : (0:ℝ) ≤ (u + Real.sqrt thrT) ^ (thrTheta - 2) := Real.rpow_nonneg (by linarith) _
    linarith
  have hZ0 : (0:ℝ) ≤ (((412 : ℝ)/625))^3 * (((371 : ℝ)/500)) + (((6037 : ℝ)/5000))^3 * (((229 : ℝ)/200)) := by positivity
  have hb0 : (0:ℝ) ≤ ((177 : ℝ)/500) := by norm_num
  have hsumle : (v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((412 : ℝ)/625))^3 * (((371 : ℝ)/500)) + (((6037 : ℝ)/5000))^3 * (((229 : ℝ)/200)) := by linarith
  have hprod : u * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2))
      ≤ ((177 : ℝ)/500) * ((((412 : ℝ)/625))^3 * (((371 : ℝ)/500)) + (((6037 : ℝ)/5000))^3 * (((229 : ℝ)/200))) := mul_le_mul hb hsumle hs0 hb0
  have hprod2 := mul_le_mul_of_nonneg_left hprod (by rw [hth1]; norm_num : (0:ℝ) ≤ (thrTheta - 1) / 2)
  have hfin : u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (((1189 : ℝ)/1000))^4 * (((283 : ℝ)/250)) + (((6101 : ℝ)/10000))^4 * (((701 : ℝ)/1000)) := by
    calc u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
        = (thrTheta - 1) / 2 * (u * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2))) := by ring
      _ ≤ (thrTheta - 1) / 2 * (((177 : ℝ)/500) * ((((412 : ℝ)/625))^3 * (((371 : ℝ)/500)) + (((6037 : ℝ)/5000))^3 * (((229 : ℝ)/200)))) := hprod2
      _ = ((177 : ℝ)/500) * ((1269:ℝ)/269) * ((((412 : ℝ)/625))^3 * (((371 : ℝ)/500)) + (((6037 : ℝ)/5000))^3 * (((229 : ℝ)/200))) / 2 := by rw [hth1]; ring
      _ ≤ (((1189 : ℝ)/1000))^4 * (((283 : ℝ)/250)) + (((6101 : ℝ)/10000))^4 * (((701 : ℝ)/1000)) := hkey
  calc u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (((1189 : ℝ)/1000))^4 * (((283 : ℝ)/250)) + (((6101 : ℝ)/10000))^4 * (((701 : ℝ)/1000)) := hfin
    _ ≤ (u + v) ^ (thrTheta - 1) + (u + Real.sqrt thrT) ^ (thrTheta - 1) := by linarith [hL1, hL2]

theorem edgeS_1 {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hs : u ^ 2 + v ^ 2 = thrS)
    (ha : ((177 : ℝ)/500) ≤ u) (hb : u ≤ ((101 : ℝ)/250)) :
    u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (u + v) ^ (thrTheta - 1) + (u + Real.sqrt thrT) ^ (thrTheta - 1) := by
  have hv0 : 0 < v := lt_of_lt_of_le hu huv
  have hth1 : thrTheta - 1 = ((1269:ℝ)/269) := by unfold thrTheta; norm_num
  have hwlo : ((3051 : ℝ)/10000) ≤ Real.sqrt thrT := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num [thrT]
  have hwhi : Real.sqrt thrT ≤ ((763 : ℝ)/2500) := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num [thrT]
  have hv2 : v ^ 2 = thrS - u ^ 2 := by linarith
  have hvlo : ((8623 : ℝ)/10000) ≤ v := by
    have h1 : (((8623 : ℝ)/10000)) ^ 2 ≤ v ^ 2 := by rw [hv2]; unfold thrS; nlinarith
    nlinarith [h1, hv0, (by norm_num : (0:ℝ) ≤ ((8623 : ℝ)/10000))]
  have hvhi : v ≤ ((8841 : ℝ)/10000) := by
    have h1 : v ^ 2 ≤ (((8841 : ℝ)/10000)) ^ 2 := by rw [hv2]; unfold thrS; nlinarith
    nlinarith [h1, hv0, (by norm_num : (0:ℝ) ≤ ((8841 : ℝ)/10000))]
  have hL1 : (((12163 : ℝ)/10000))^4 * (((23 : ℝ)/20)) ≤ (u + v) ^ (thrTheta - 1) := by
    rw [rpow_p_eq (by positivity)]
    have hce : ((23 : ℝ)/20) ≤ (((12163 : ℝ)/10000)) ^ ((193:ℝ)/269) := by
      simpa using rpow_frac_le (c := ((23 : ℚ)/20)) (z := ((12163 : ℚ)/10000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : ((12163 : ℝ)/10000) ≤ u + v := by linarith
    have hZ : (((12163 : ℝ)/10000))^4 ≤ (u + v)^4 := pow_le_pow_left₀ (by norm_num) hA 4
    have he : (((12163 : ℝ)/10000)) ^ ((193:ℝ)/269) ≤ (u + v) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by norm_num) hA (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hce (by positivity)) (mul_le_mul hZ he (by positivity) (by positivity))
  have hL2 : (((6591 : ℝ)/10000))^4 * (((741 : ℝ)/1000)) ≤ (u + Real.sqrt thrT) ^ (thrTheta - 1) := by
    rw [rpow_p_eq (by positivity)]
    have hce : ((741 : ℝ)/1000) ≤ (((6591 : ℝ)/10000)) ^ ((193:ℝ)/269) := by
      simpa using rpow_frac_le (c := ((741 : ℚ)/1000)) (z := ((6591 : ℚ)/10000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : ((6591 : ℝ)/10000) ≤ u + Real.sqrt thrT := by linarith
    have hZ : (((6591 : ℝ)/10000))^4 ≤ (u + Real.sqrt thrT)^4 := pow_le_pow_left₀ (by norm_num) hA 4
    have he : (((6591 : ℝ)/10000)) ^ ((193:ℝ)/269) ≤ (u + Real.sqrt thrT) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by norm_num) hA (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hce (by positivity)) (mul_le_mul hZ he (by positivity) (by positivity))
  have hQ1 : (u + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((1773 : ℝ)/2500))^3 * (((391 : ℝ)/500)) := by
    rw [rpow_q_eq (by positivity)]
    have hce : (((1773 : ℝ)/2500)) ^ ((193:ℝ)/269) ≤ ((391 : ℝ)/500) := by
      simpa using le_rpow_frac (c := ((391 : ℚ)/500)) (z := ((1773 : ℚ)/2500)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : u + Real.sqrt thrT ≤ ((1773 : ℝ)/2500) := by linarith
    have hZ : (u + Real.sqrt thrT)^3 ≤ (((1773 : ℝ)/2500))^3 := pow_le_pow_left₀ (by positivity) hA 3
    have he : (u + Real.sqrt thrT) ^ ((193:ℝ)/269) ≤ (((1773 : ℝ)/2500)) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by positivity) hA (by norm_num)
    calc (u + Real.sqrt thrT)^3 * (u + Real.sqrt thrT)^((193:ℝ)/269)
        ≤ (((1773 : ℝ)/2500))^3 * (((1773 : ℝ)/2500))^((193:ℝ)/269) := mul_le_mul hZ he (by positivity) (by positivity)
      _ ≤ (((1773 : ℝ)/2500))^3 * (((391 : ℝ)/500)) := mul_le_mul_of_nonneg_left hce (by positivity)
  have hQ2 : (v + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((11893 : ℝ)/10000))^3 * (((1133 : ℝ)/1000)) := by
    rw [rpow_q_eq (by positivity)]
    have hce : (((11893 : ℝ)/10000)) ^ ((193:ℝ)/269) ≤ ((1133 : ℝ)/1000) := by
      simpa using le_rpow_frac (c := ((1133 : ℚ)/1000)) (z := ((11893 : ℚ)/10000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : v + Real.sqrt thrT ≤ ((11893 : ℝ)/10000) := by linarith
    have hZ : (v + Real.sqrt thrT)^3 ≤ (((11893 : ℝ)/10000))^3 := pow_le_pow_left₀ (by positivity) hA 3
    have he : (v + Real.sqrt thrT) ^ ((193:ℝ)/269) ≤ (((11893 : ℝ)/10000)) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by positivity) hA (by norm_num)
    calc (v + Real.sqrt thrT)^3 * (v + Real.sqrt thrT)^((193:ℝ)/269)
        ≤ (((11893 : ℝ)/10000))^3 * (((11893 : ℝ)/10000))^((193:ℝ)/269) := mul_le_mul hZ he (by positivity) (by positivity)
      _ ≤ (((11893 : ℝ)/10000))^3 * (((1133 : ℝ)/1000)) := mul_le_mul_of_nonneg_left hce (by positivity)
  have hkey : ((101 : ℝ)/250) * ((1269:ℝ)/269) * ((((1773 : ℝ)/2500))^3 * (((391 : ℝ)/500)) + (((11893 : ℝ)/10000))^3 * (((1133 : ℝ)/1000))) / 2 ≤ (((12163 : ℝ)/10000))^4 * (((23 : ℝ)/20)) + (((6591 : ℝ)/10000))^4 * (((741 : ℝ)/1000)) := by
    norm_num
  have hs0 : (0:ℝ) ≤ (v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2) := by
    have h1 : (0:ℝ) ≤ (v + Real.sqrt thrT) ^ (thrTheta - 2) := Real.rpow_nonneg (by linarith) _
    have h2 : (0:ℝ) ≤ (u + Real.sqrt thrT) ^ (thrTheta - 2) := Real.rpow_nonneg (by linarith) _
    linarith
  have hZ0 : (0:ℝ) ≤ (((1773 : ℝ)/2500))^3 * (((391 : ℝ)/500)) + (((11893 : ℝ)/10000))^3 * (((1133 : ℝ)/1000)) := by positivity
  have hb0 : (0:ℝ) ≤ ((101 : ℝ)/250) := by norm_num
  have hsumle : (v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((1773 : ℝ)/2500))^3 * (((391 : ℝ)/500)) + (((11893 : ℝ)/10000))^3 * (((1133 : ℝ)/1000)) := by linarith
  have hprod : u * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2))
      ≤ ((101 : ℝ)/250) * ((((1773 : ℝ)/2500))^3 * (((391 : ℝ)/500)) + (((11893 : ℝ)/10000))^3 * (((1133 : ℝ)/1000))) := mul_le_mul hb hsumle hs0 hb0
  have hprod2 := mul_le_mul_of_nonneg_left hprod (by rw [hth1]; norm_num : (0:ℝ) ≤ (thrTheta - 1) / 2)
  have hfin : u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (((12163 : ℝ)/10000))^4 * (((23 : ℝ)/20)) + (((6591 : ℝ)/10000))^4 * (((741 : ℝ)/1000)) := by
    calc u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
        = (thrTheta - 1) / 2 * (u * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2))) := by ring
      _ ≤ (thrTheta - 1) / 2 * (((101 : ℝ)/250) * ((((1773 : ℝ)/2500))^3 * (((391 : ℝ)/500)) + (((11893 : ℝ)/10000))^3 * (((1133 : ℝ)/1000)))) := hprod2
      _ = ((101 : ℝ)/250) * ((1269:ℝ)/269) * ((((1773 : ℝ)/2500))^3 * (((391 : ℝ)/500)) + (((11893 : ℝ)/10000))^3 * (((1133 : ℝ)/1000))) / 2 := by rw [hth1]; ring
      _ ≤ (((12163 : ℝ)/10000))^4 * (((23 : ℝ)/20)) + (((6591 : ℝ)/10000))^4 * (((741 : ℝ)/1000)) := hkey
  calc u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (((12163 : ℝ)/10000))^4 * (((23 : ℝ)/20)) + (((6591 : ℝ)/10000))^4 * (((741 : ℝ)/1000)) := hfin
    _ ≤ (u + v) ^ (thrTheta - 1) + (u + Real.sqrt thrT) ^ (thrTheta - 1) := by linarith [hL1, hL2]

theorem edgeS_2 {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hs : u ^ 2 + v ^ 2 = thrS)
    (ha : ((101 : ℝ)/250) ≤ u) (hb : u ≤ ((453 : ℝ)/1000)) :
    u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (u + v) ^ (thrTheta - 1) + (u + Real.sqrt thrT) ^ (thrTheta - 1) := by
  have hv0 : 0 < v := lt_of_lt_of_le hu huv
  have hth1 : thrTheta - 1 = ((1269:ℝ)/269) := by unfold thrTheta; norm_num
  have hwlo : ((3051 : ℝ)/10000) ≤ Real.sqrt thrT := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num [thrT]
  have hwhi : Real.sqrt thrT ≤ ((763 : ℝ)/2500) := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num [thrT]
  have hv2 : v ^ 2 = thrS - u ^ 2 := by linarith
  have hvlo : ((1047 : ℝ)/1250) ≤ v := by
    have h1 : (((1047 : ℝ)/1250)) ^ 2 ≤ v ^ 2 := by rw [hv2]; unfold thrS; nlinarith
    nlinarith [h1, hv0, (by norm_num : (0:ℝ) ≤ ((1047 : ℝ)/1250))]
  have hvhi : v ≤ ((539 : ℝ)/625) := by
    have h1 : v ^ 2 ≤ (((539 : ℝ)/625)) ^ 2 := by rw [hv2]; unfold thrS; nlinarith
    nlinarith [h1, hv0, (by norm_num : (0:ℝ) ≤ ((539 : ℝ)/625))]
  have hL1 : (((776 : ℝ)/625))^4 * (((1167 : ℝ)/1000)) ≤ (u + v) ^ (thrTheta - 1) := by
    rw [rpow_p_eq (by positivity)]
    have hce : ((1167 : ℝ)/1000) ≤ (((776 : ℝ)/625)) ^ ((193:ℝ)/269) := by
      simpa using rpow_frac_le (c := ((1167 : ℚ)/1000)) (z := ((776 : ℚ)/625)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : ((776 : ℝ)/625) ≤ u + v := by linarith
    have hZ : (((776 : ℝ)/625))^4 ≤ (u + v)^4 := pow_le_pow_left₀ (by norm_num) hA 4
    have he : (((776 : ℝ)/625)) ^ ((193:ℝ)/269) ≤ (u + v) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by norm_num) hA (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hce (by positivity)) (mul_le_mul hZ he (by positivity) (by positivity))
  have hL2 : (((7091 : ℝ)/10000))^4 * (((781 : ℝ)/1000)) ≤ (u + Real.sqrt thrT) ^ (thrTheta - 1) := by
    rw [rpow_p_eq (by positivity)]
    have hce : ((781 : ℝ)/1000) ≤ (((7091 : ℝ)/10000)) ^ ((193:ℝ)/269) := by
      simpa using rpow_frac_le (c := ((781 : ℚ)/1000)) (z := ((7091 : ℚ)/10000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : ((7091 : ℝ)/10000) ≤ u + Real.sqrt thrT := by linarith
    have hZ : (((7091 : ℝ)/10000))^4 ≤ (u + Real.sqrt thrT)^4 := pow_le_pow_left₀ (by norm_num) hA 4
    have he : (((7091 : ℝ)/10000)) ^ ((193:ℝ)/269) ≤ (u + Real.sqrt thrT) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by norm_num) hA (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hce (by positivity)) (mul_le_mul hZ he (by positivity) (by positivity))
  have hQ1 : (u + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((3791 : ℝ)/5000))^3 * (((41 : ℝ)/50)) := by
    rw [rpow_q_eq (by positivity)]
    have hce : (((3791 : ℝ)/5000)) ^ ((193:ℝ)/269) ≤ ((41 : ℝ)/50) := by
      simpa using le_rpow_frac (c := ((41 : ℚ)/50)) (z := ((3791 : ℚ)/5000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : u + Real.sqrt thrT ≤ ((3791 : ℝ)/5000) := by linarith
    have hZ : (u + Real.sqrt thrT)^3 ≤ (((3791 : ℝ)/5000))^3 := pow_le_pow_left₀ (by positivity) hA 3
    have he : (u + Real.sqrt thrT) ^ ((193:ℝ)/269) ≤ (((3791 : ℝ)/5000)) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by positivity) hA (by norm_num)
    calc (u + Real.sqrt thrT)^3 * (u + Real.sqrt thrT)^((193:ℝ)/269)
        ≤ (((3791 : ℝ)/5000))^3 * (((3791 : ℝ)/5000))^((193:ℝ)/269) := mul_le_mul hZ he (by positivity) (by positivity)
      _ ≤ (((3791 : ℝ)/5000))^3 * (((41 : ℝ)/50)) := mul_le_mul_of_nonneg_left hce (by positivity)
  have hQ2 : (v + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((2919 : ℝ)/2500))^3 * (((559 : ℝ)/500)) := by
    rw [rpow_q_eq (by positivity)]
    have hce : (((2919 : ℝ)/2500)) ^ ((193:ℝ)/269) ≤ ((559 : ℝ)/500) := by
      simpa using le_rpow_frac (c := ((559 : ℚ)/500)) (z := ((2919 : ℚ)/2500)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : v + Real.sqrt thrT ≤ ((2919 : ℝ)/2500) := by linarith
    have hZ : (v + Real.sqrt thrT)^3 ≤ (((2919 : ℝ)/2500))^3 := pow_le_pow_left₀ (by positivity) hA 3
    have he : (v + Real.sqrt thrT) ^ ((193:ℝ)/269) ≤ (((2919 : ℝ)/2500)) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by positivity) hA (by norm_num)
    calc (v + Real.sqrt thrT)^3 * (v + Real.sqrt thrT)^((193:ℝ)/269)
        ≤ (((2919 : ℝ)/2500))^3 * (((2919 : ℝ)/2500))^((193:ℝ)/269) := mul_le_mul hZ he (by positivity) (by positivity)
      _ ≤ (((2919 : ℝ)/2500))^3 * (((559 : ℝ)/500)) := mul_le_mul_of_nonneg_left hce (by positivity)
  have hkey : ((453 : ℝ)/1000) * ((1269:ℝ)/269) * ((((3791 : ℝ)/5000))^3 * (((41 : ℝ)/50)) + (((2919 : ℝ)/2500))^3 * (((559 : ℝ)/500))) / 2 ≤ (((776 : ℝ)/625))^4 * (((1167 : ℝ)/1000)) + (((7091 : ℝ)/10000))^4 * (((781 : ℝ)/1000)) := by
    norm_num
  have hs0 : (0:ℝ) ≤ (v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2) := by
    have h1 : (0:ℝ) ≤ (v + Real.sqrt thrT) ^ (thrTheta - 2) := Real.rpow_nonneg (by linarith) _
    have h2 : (0:ℝ) ≤ (u + Real.sqrt thrT) ^ (thrTheta - 2) := Real.rpow_nonneg (by linarith) _
    linarith
  have hZ0 : (0:ℝ) ≤ (((3791 : ℝ)/5000))^3 * (((41 : ℝ)/50)) + (((2919 : ℝ)/2500))^3 * (((559 : ℝ)/500)) := by positivity
  have hb0 : (0:ℝ) ≤ ((453 : ℝ)/1000) := by norm_num
  have hsumle : (v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((3791 : ℝ)/5000))^3 * (((41 : ℝ)/50)) + (((2919 : ℝ)/2500))^3 * (((559 : ℝ)/500)) := by linarith
  have hprod : u * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2))
      ≤ ((453 : ℝ)/1000) * ((((3791 : ℝ)/5000))^3 * (((41 : ℝ)/50)) + (((2919 : ℝ)/2500))^3 * (((559 : ℝ)/500))) := mul_le_mul hb hsumle hs0 hb0
  have hprod2 := mul_le_mul_of_nonneg_left hprod (by rw [hth1]; norm_num : (0:ℝ) ≤ (thrTheta - 1) / 2)
  have hfin : u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (((776 : ℝ)/625))^4 * (((1167 : ℝ)/1000)) + (((7091 : ℝ)/10000))^4 * (((781 : ℝ)/1000)) := by
    calc u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
        = (thrTheta - 1) / 2 * (u * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2))) := by ring
      _ ≤ (thrTheta - 1) / 2 * (((453 : ℝ)/1000) * ((((3791 : ℝ)/5000))^3 * (((41 : ℝ)/50)) + (((2919 : ℝ)/2500))^3 * (((559 : ℝ)/500)))) := hprod2
      _ = ((453 : ℝ)/1000) * ((1269:ℝ)/269) * ((((3791 : ℝ)/5000))^3 * (((41 : ℝ)/50)) + (((2919 : ℝ)/2500))^3 * (((559 : ℝ)/500))) / 2 := by rw [hth1]; ring
      _ ≤ (((776 : ℝ)/625))^4 * (((1167 : ℝ)/1000)) + (((7091 : ℝ)/10000))^4 * (((781 : ℝ)/1000)) := hkey
  calc u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (((776 : ℝ)/625))^4 * (((1167 : ℝ)/1000)) + (((7091 : ℝ)/10000))^4 * (((781 : ℝ)/1000)) := hfin
    _ ≤ (u + v) ^ (thrTheta - 1) + (u + Real.sqrt thrT) ^ (thrTheta - 1) := by linarith [hL1, hL2]

theorem edgeS_3 {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hs : u ^ 2 + v ^ 2 = thrS)
    (ha : ((453 : ℝ)/1000) ≤ u) (hb : u ≤ ((503 : ℝ)/1000)) :
    u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (u + v) ^ (thrTheta - 1) + (u + Real.sqrt thrT) ^ (thrTheta - 1) := by
  have hv0 : 0 < v := lt_of_lt_of_le hu huv
  have hth1 : thrTheta - 1 = ((1269:ℝ)/269) := by unfold thrTheta; norm_num
  have hwlo : ((3051 : ℝ)/10000) ≤ Real.sqrt thrT := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num [thrT]
  have hwhi : Real.sqrt thrT ≤ ((763 : ℝ)/2500) := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num [thrT]
  have hv2 : v ^ 2 = thrS - u ^ 2 := by linarith
  have hvlo : ((4043 : ℝ)/5000) ≤ v := by
    have h1 : (((4043 : ℝ)/5000)) ^ 2 ≤ v ^ 2 := by rw [hv2]; unfold thrS; nlinarith
    nlinarith [h1, hv0, (by norm_num : (0:ℝ) ≤ ((4043 : ℝ)/5000))]
  have hvhi : v ≤ ((8377 : ℝ)/10000) := by
    have h1 : v ^ 2 ≤ (((8377 : ℝ)/10000)) ^ 2 := by rw [hv2]; unfold thrS; nlinarith
    nlinarith [h1, hv0, (by norm_num : (0:ℝ) ≤ ((8377 : ℝ)/10000))]
  have hL1 : (((1577 : ℝ)/1250))^4 * (((1181 : ℝ)/1000)) ≤ (u + v) ^ (thrTheta - 1) := by
    rw [rpow_p_eq (by positivity)]
    have hce : ((1181 : ℝ)/1000) ≤ (((1577 : ℝ)/1250)) ^ ((193:ℝ)/269) := by
      simpa using rpow_frac_le (c := ((1181 : ℚ)/1000)) (z := ((1577 : ℚ)/1250)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : ((1577 : ℝ)/1250) ≤ u + v := by linarith
    have hZ : (((1577 : ℝ)/1250))^4 ≤ (u + v)^4 := pow_le_pow_left₀ (by norm_num) hA 4
    have he : (((1577 : ℝ)/1250)) ^ ((193:ℝ)/269) ≤ (u + v) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by norm_num) hA (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hce (by positivity)) (mul_le_mul hZ he (by positivity) (by positivity))
  have hL2 : (((7581 : ℝ)/10000))^4 * (((819 : ℝ)/1000)) ≤ (u + Real.sqrt thrT) ^ (thrTheta - 1) := by
    rw [rpow_p_eq (by positivity)]
    have hce : ((819 : ℝ)/1000) ≤ (((7581 : ℝ)/10000)) ^ ((193:ℝ)/269) := by
      simpa using rpow_frac_le (c := ((819 : ℚ)/1000)) (z := ((7581 : ℚ)/10000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : ((7581 : ℝ)/10000) ≤ u + Real.sqrt thrT := by linarith
    have hZ : (((7581 : ℝ)/10000))^4 ≤ (u + Real.sqrt thrT)^4 := pow_le_pow_left₀ (by norm_num) hA 4
    have he : (((7581 : ℝ)/10000)) ^ ((193:ℝ)/269) ≤ (u + Real.sqrt thrT) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by norm_num) hA (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hce (by positivity)) (mul_le_mul hZ he (by positivity) (by positivity))
  have hQ1 : (u + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((4041 : ℝ)/5000))^3 * (((859 : ℝ)/1000)) := by
    rw [rpow_q_eq (by positivity)]
    have hce : (((4041 : ℝ)/5000)) ^ ((193:ℝ)/269) ≤ ((859 : ℝ)/1000) := by
      simpa using le_rpow_frac (c := ((859 : ℚ)/1000)) (z := ((4041 : ℚ)/5000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : u + Real.sqrt thrT ≤ ((4041 : ℝ)/5000) := by linarith
    have hZ : (u + Real.sqrt thrT)^3 ≤ (((4041 : ℝ)/5000))^3 := pow_le_pow_left₀ (by positivity) hA 3
    have he : (u + Real.sqrt thrT) ^ ((193:ℝ)/269) ≤ (((4041 : ℝ)/5000)) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by positivity) hA (by norm_num)
    calc (u + Real.sqrt thrT)^3 * (u + Real.sqrt thrT)^((193:ℝ)/269)
        ≤ (((4041 : ℝ)/5000))^3 * (((4041 : ℝ)/5000))^((193:ℝ)/269) := mul_le_mul hZ he (by positivity) (by positivity)
      _ ≤ (((4041 : ℝ)/5000))^3 * (((859 : ℝ)/1000)) := mul_le_mul_of_nonneg_left hce (by positivity)
  have hQ2 : (v + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((11429 : ℝ)/10000))^3 * (((1101 : ℝ)/1000)) := by
    rw [rpow_q_eq (by positivity)]
    have hce : (((11429 : ℝ)/10000)) ^ ((193:ℝ)/269) ≤ ((1101 : ℝ)/1000) := by
      simpa using le_rpow_frac (c := ((1101 : ℚ)/1000)) (z := ((11429 : ℚ)/10000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : v + Real.sqrt thrT ≤ ((11429 : ℝ)/10000) := by linarith
    have hZ : (v + Real.sqrt thrT)^3 ≤ (((11429 : ℝ)/10000))^3 := pow_le_pow_left₀ (by positivity) hA 3
    have he : (v + Real.sqrt thrT) ^ ((193:ℝ)/269) ≤ (((11429 : ℝ)/10000)) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by positivity) hA (by norm_num)
    calc (v + Real.sqrt thrT)^3 * (v + Real.sqrt thrT)^((193:ℝ)/269)
        ≤ (((11429 : ℝ)/10000))^3 * (((11429 : ℝ)/10000))^((193:ℝ)/269) := mul_le_mul hZ he (by positivity) (by positivity)
      _ ≤ (((11429 : ℝ)/10000))^3 * (((1101 : ℝ)/1000)) := mul_le_mul_of_nonneg_left hce (by positivity)
  have hkey : ((503 : ℝ)/1000) * ((1269:ℝ)/269) * ((((4041 : ℝ)/5000))^3 * (((859 : ℝ)/1000)) + (((11429 : ℝ)/10000))^3 * (((1101 : ℝ)/1000))) / 2 ≤ (((1577 : ℝ)/1250))^4 * (((1181 : ℝ)/1000)) + (((7581 : ℝ)/10000))^4 * (((819 : ℝ)/1000)) := by
    norm_num
  have hs0 : (0:ℝ) ≤ (v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2) := by
    have h1 : (0:ℝ) ≤ (v + Real.sqrt thrT) ^ (thrTheta - 2) := Real.rpow_nonneg (by linarith) _
    have h2 : (0:ℝ) ≤ (u + Real.sqrt thrT) ^ (thrTheta - 2) := Real.rpow_nonneg (by linarith) _
    linarith
  have hZ0 : (0:ℝ) ≤ (((4041 : ℝ)/5000))^3 * (((859 : ℝ)/1000)) + (((11429 : ℝ)/10000))^3 * (((1101 : ℝ)/1000)) := by positivity
  have hb0 : (0:ℝ) ≤ ((503 : ℝ)/1000) := by norm_num
  have hsumle : (v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((4041 : ℝ)/5000))^3 * (((859 : ℝ)/1000)) + (((11429 : ℝ)/10000))^3 * (((1101 : ℝ)/1000)) := by linarith
  have hprod : u * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2))
      ≤ ((503 : ℝ)/1000) * ((((4041 : ℝ)/5000))^3 * (((859 : ℝ)/1000)) + (((11429 : ℝ)/10000))^3 * (((1101 : ℝ)/1000))) := mul_le_mul hb hsumle hs0 hb0
  have hprod2 := mul_le_mul_of_nonneg_left hprod (by rw [hth1]; norm_num : (0:ℝ) ≤ (thrTheta - 1) / 2)
  have hfin : u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (((1577 : ℝ)/1250))^4 * (((1181 : ℝ)/1000)) + (((7581 : ℝ)/10000))^4 * (((819 : ℝ)/1000)) := by
    calc u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
        = (thrTheta - 1) / 2 * (u * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2))) := by ring
      _ ≤ (thrTheta - 1) / 2 * (((503 : ℝ)/1000) * ((((4041 : ℝ)/5000))^3 * (((859 : ℝ)/1000)) + (((11429 : ℝ)/10000))^3 * (((1101 : ℝ)/1000)))) := hprod2
      _ = ((503 : ℝ)/1000) * ((1269:ℝ)/269) * ((((4041 : ℝ)/5000))^3 * (((859 : ℝ)/1000)) + (((11429 : ℝ)/10000))^3 * (((1101 : ℝ)/1000))) / 2 := by rw [hth1]; ring
      _ ≤ (((1577 : ℝ)/1250))^4 * (((1181 : ℝ)/1000)) + (((7581 : ℝ)/10000))^4 * (((819 : ℝ)/1000)) := hkey
  calc u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (((1577 : ℝ)/1250))^4 * (((1181 : ℝ)/1000)) + (((7581 : ℝ)/10000))^4 * (((819 : ℝ)/1000)) := hfin
    _ ≤ (u + v) ^ (thrTheta - 1) + (u + Real.sqrt thrT) ^ (thrTheta - 1) := by linarith [hL1, hL2]

theorem edgeS_4 {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hs : u ^ 2 + v ^ 2 = thrS)
    (ha : ((503 : ℝ)/1000) ≤ u) (hb : u ≤ ((69 : ℝ)/125)) :
    u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (u + v) ^ (thrTheta - 1) + (u + Real.sqrt thrT) ^ (thrTheta - 1) := by
  have hv0 : 0 < v := lt_of_lt_of_le hu huv
  have hth1 : thrTheta - 1 = ((1269:ℝ)/269) := by unfold thrTheta; norm_num
  have hwlo : ((3051 : ℝ)/10000) ≤ Real.sqrt thrT := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num [thrT]
  have hwhi : Real.sqrt thrT ≤ ((763 : ℝ)/2500) := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num [thrT]
  have hv2 : v ^ 2 = thrS - u ^ 2 := by linarith
  have hvlo : ((7759 : ℝ)/10000) ≤ v := by
    have h1 : (((7759 : ℝ)/10000)) ^ 2 ≤ v ^ 2 := by rw [hv2]; unfold thrS; nlinarith
    nlinarith [h1, hv0, (by norm_num : (0:ℝ) ≤ ((7759 : ℝ)/10000))]
  have hvhi : v ≤ ((8087 : ℝ)/10000) := by
    have h1 : v ^ 2 ≤ (((8087 : ℝ)/10000)) ^ 2 := by rw [hv2]; unfold thrS; nlinarith
    nlinarith [h1, hv0, (by norm_num : (0:ℝ) ≤ ((8087 : ℝ)/10000))]
  have hL1 : (((12789 : ℝ)/10000))^4 * (((1193 : ℝ)/1000)) ≤ (u + v) ^ (thrTheta - 1) := by
    rw [rpow_p_eq (by positivity)]
    have hce : ((1193 : ℝ)/1000) ≤ (((12789 : ℝ)/10000)) ^ ((193:ℝ)/269) := by
      simpa using rpow_frac_le (c := ((1193 : ℚ)/1000)) (z := ((12789 : ℚ)/10000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : ((12789 : ℝ)/10000) ≤ u + v := by linarith
    have hZ : (((12789 : ℝ)/10000))^4 ≤ (u + v)^4 := pow_le_pow_left₀ (by norm_num) hA 4
    have he : (((12789 : ℝ)/10000)) ^ ((193:ℝ)/269) ≤ (u + v) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by norm_num) hA (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hce (by positivity)) (mul_le_mul hZ he (by positivity) (by positivity))
  have hL2 : (((8081 : ℝ)/10000))^4 * (((429 : ℝ)/500)) ≤ (u + Real.sqrt thrT) ^ (thrTheta - 1) := by
    rw [rpow_p_eq (by positivity)]
    have hce : ((429 : ℝ)/500) ≤ (((8081 : ℝ)/10000)) ^ ((193:ℝ)/269) := by
      simpa using rpow_frac_le (c := ((429 : ℚ)/500)) (z := ((8081 : ℚ)/10000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : ((8081 : ℝ)/10000) ≤ u + Real.sqrt thrT := by linarith
    have hZ : (((8081 : ℝ)/10000))^4 ≤ (u + Real.sqrt thrT)^4 := pow_le_pow_left₀ (by norm_num) hA 4
    have he : (((8081 : ℝ)/10000)) ^ ((193:ℝ)/269) ≤ (u + Real.sqrt thrT) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by norm_num) hA (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hce (by positivity)) (mul_le_mul hZ he (by positivity) (by positivity))
  have hQ1 : (u + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((2143 : ℝ)/2500))^3 * (((112 : ℝ)/125)) := by
    rw [rpow_q_eq (by positivity)]
    have hce : (((2143 : ℝ)/2500)) ^ ((193:ℝ)/269) ≤ ((112 : ℝ)/125) := by
      simpa using le_rpow_frac (c := ((112 : ℚ)/125)) (z := ((2143 : ℚ)/2500)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : u + Real.sqrt thrT ≤ ((2143 : ℝ)/2500) := by linarith
    have hZ : (u + Real.sqrt thrT)^3 ≤ (((2143 : ℝ)/2500))^3 := pow_le_pow_left₀ (by positivity) hA 3
    have he : (u + Real.sqrt thrT) ^ ((193:ℝ)/269) ≤ (((2143 : ℝ)/2500)) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by positivity) hA (by norm_num)
    calc (u + Real.sqrt thrT)^3 * (u + Real.sqrt thrT)^((193:ℝ)/269)
        ≤ (((2143 : ℝ)/2500))^3 * (((2143 : ℝ)/2500))^((193:ℝ)/269) := mul_le_mul hZ he (by positivity) (by positivity)
      _ ≤ (((2143 : ℝ)/2500))^3 * (((112 : ℝ)/125)) := mul_le_mul_of_nonneg_left hce (by positivity)
  have hQ2 : (v + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((11139 : ℝ)/10000))^3 * (((1081 : ℝ)/1000)) := by
    rw [rpow_q_eq (by positivity)]
    have hce : (((11139 : ℝ)/10000)) ^ ((193:ℝ)/269) ≤ ((1081 : ℝ)/1000) := by
      simpa using le_rpow_frac (c := ((1081 : ℚ)/1000)) (z := ((11139 : ℚ)/10000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : v + Real.sqrt thrT ≤ ((11139 : ℝ)/10000) := by linarith
    have hZ : (v + Real.sqrt thrT)^3 ≤ (((11139 : ℝ)/10000))^3 := pow_le_pow_left₀ (by positivity) hA 3
    have he : (v + Real.sqrt thrT) ^ ((193:ℝ)/269) ≤ (((11139 : ℝ)/10000)) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by positivity) hA (by norm_num)
    calc (v + Real.sqrt thrT)^3 * (v + Real.sqrt thrT)^((193:ℝ)/269)
        ≤ (((11139 : ℝ)/10000))^3 * (((11139 : ℝ)/10000))^((193:ℝ)/269) := mul_le_mul hZ he (by positivity) (by positivity)
      _ ≤ (((11139 : ℝ)/10000))^3 * (((1081 : ℝ)/1000)) := mul_le_mul_of_nonneg_left hce (by positivity)
  have hkey : ((69 : ℝ)/125) * ((1269:ℝ)/269) * ((((2143 : ℝ)/2500))^3 * (((112 : ℝ)/125)) + (((11139 : ℝ)/10000))^3 * (((1081 : ℝ)/1000))) / 2 ≤ (((12789 : ℝ)/10000))^4 * (((1193 : ℝ)/1000)) + (((8081 : ℝ)/10000))^4 * (((429 : ℝ)/500)) := by
    norm_num
  have hs0 : (0:ℝ) ≤ (v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2) := by
    have h1 : (0:ℝ) ≤ (v + Real.sqrt thrT) ^ (thrTheta - 2) := Real.rpow_nonneg (by linarith) _
    have h2 : (0:ℝ) ≤ (u + Real.sqrt thrT) ^ (thrTheta - 2) := Real.rpow_nonneg (by linarith) _
    linarith
  have hZ0 : (0:ℝ) ≤ (((2143 : ℝ)/2500))^3 * (((112 : ℝ)/125)) + (((11139 : ℝ)/10000))^3 * (((1081 : ℝ)/1000)) := by positivity
  have hb0 : (0:ℝ) ≤ ((69 : ℝ)/125) := by norm_num
  have hsumle : (v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((2143 : ℝ)/2500))^3 * (((112 : ℝ)/125)) + (((11139 : ℝ)/10000))^3 * (((1081 : ℝ)/1000)) := by linarith
  have hprod : u * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2))
      ≤ ((69 : ℝ)/125) * ((((2143 : ℝ)/2500))^3 * (((112 : ℝ)/125)) + (((11139 : ℝ)/10000))^3 * (((1081 : ℝ)/1000))) := mul_le_mul hb hsumle hs0 hb0
  have hprod2 := mul_le_mul_of_nonneg_left hprod (by rw [hth1]; norm_num : (0:ℝ) ≤ (thrTheta - 1) / 2)
  have hfin : u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (((12789 : ℝ)/10000))^4 * (((1193 : ℝ)/1000)) + (((8081 : ℝ)/10000))^4 * (((429 : ℝ)/500)) := by
    calc u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
        = (thrTheta - 1) / 2 * (u * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2))) := by ring
      _ ≤ (thrTheta - 1) / 2 * (((69 : ℝ)/125) * ((((2143 : ℝ)/2500))^3 * (((112 : ℝ)/125)) + (((11139 : ℝ)/10000))^3 * (((1081 : ℝ)/1000)))) := hprod2
      _ = ((69 : ℝ)/125) * ((1269:ℝ)/269) * ((((2143 : ℝ)/2500))^3 * (((112 : ℝ)/125)) + (((11139 : ℝ)/10000))^3 * (((1081 : ℝ)/1000))) / 2 := by rw [hth1]; ring
      _ ≤ (((12789 : ℝ)/10000))^4 * (((1193 : ℝ)/1000)) + (((8081 : ℝ)/10000))^4 * (((429 : ℝ)/500)) := hkey
  calc u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (((12789 : ℝ)/10000))^4 * (((1193 : ℝ)/1000)) + (((8081 : ℝ)/10000))^4 * (((429 : ℝ)/500)) := hfin
    _ ≤ (u + v) ^ (thrTheta - 1) + (u + Real.sqrt thrT) ^ (thrTheta - 1) := by linarith [hL1, hL2]

theorem edgeS_5 {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hs : u ^ 2 + v ^ 2 = thrS)
    (ha : ((69 : ℝ)/125) ≤ u) (hb : u ≤ ((601 : ℝ)/1000)) :
    u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (u + v) ^ (thrTheta - 1) + (u + Real.sqrt thrT) ^ (thrTheta - 1) := by
  have hv0 : 0 < v := lt_of_lt_of_le hu huv
  have hth1 : thrTheta - 1 = ((1269:ℝ)/269) := by unfold thrTheta; norm_num
  have hwlo : ((3051 : ℝ)/10000) ≤ Real.sqrt thrT := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num [thrT]
  have hwhi : Real.sqrt thrT ≤ ((763 : ℝ)/2500) := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num [thrT]
  have hv2 : v ^ 2 = thrS - u ^ 2 := by linarith
  have hvlo : ((3693 : ℝ)/5000) ≤ v := by
    have h1 : (((3693 : ℝ)/5000)) ^ 2 ≤ v ^ 2 := by rw [hv2]; unfold thrS; nlinarith
    nlinarith [h1, hv0, (by norm_num : (0:ℝ) ≤ ((3693 : ℝ)/5000))]
  have hvhi : v ≤ ((97 : ℝ)/125) := by
    have h1 : v ^ 2 ≤ (((97 : ℝ)/125)) ^ 2 := by rw [hv2]; unfold thrS; nlinarith
    nlinarith [h1, hv0, (by norm_num : (0:ℝ) ≤ ((97 : ℝ)/125))]
  have hL1 : (((6453 : ℝ)/5000))^4 * (((6 : ℝ)/5)) ≤ (u + v) ^ (thrTheta - 1) := by
    rw [rpow_p_eq (by positivity)]
    have hce : ((6 : ℝ)/5) ≤ (((6453 : ℝ)/5000)) ^ ((193:ℝ)/269) := by
      simpa using rpow_frac_le (c := ((6 : ℚ)/5)) (z := ((6453 : ℚ)/5000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : ((6453 : ℝ)/5000) ≤ u + v := by linarith
    have hZ : (((6453 : ℝ)/5000))^4 ≤ (u + v)^4 := pow_le_pow_left₀ (by norm_num) hA 4
    have he : (((6453 : ℝ)/5000)) ^ ((193:ℝ)/269) ≤ (u + v) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by norm_num) hA (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hce (by positivity)) (mul_le_mul hZ he (by positivity) (by positivity))
  have hL2 : (((8571 : ℝ)/10000))^4 * (((179 : ℝ)/200)) ≤ (u + Real.sqrt thrT) ^ (thrTheta - 1) := by
    rw [rpow_p_eq (by positivity)]
    have hce : ((179 : ℝ)/200) ≤ (((8571 : ℝ)/10000)) ^ ((193:ℝ)/269) := by
      simpa using rpow_frac_le (c := ((179 : ℚ)/200)) (z := ((8571 : ℚ)/10000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : ((8571 : ℝ)/10000) ≤ u + Real.sqrt thrT := by linarith
    have hZ : (((8571 : ℝ)/10000))^4 ≤ (u + Real.sqrt thrT)^4 := pow_le_pow_left₀ (by norm_num) hA 4
    have he : (((8571 : ℝ)/10000)) ^ ((193:ℝ)/269) ≤ (u + Real.sqrt thrT) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by norm_num) hA (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hce (by positivity)) (mul_le_mul hZ he (by positivity) (by positivity))
  have hQ1 : (u + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((4531 : ℝ)/5000))^3 * (((233 : ℝ)/250)) := by
    rw [rpow_q_eq (by positivity)]
    have hce : (((4531 : ℝ)/5000)) ^ ((193:ℝ)/269) ≤ ((233 : ℝ)/250) := by
      simpa using le_rpow_frac (c := ((233 : ℚ)/250)) (z := ((4531 : ℚ)/5000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : u + Real.sqrt thrT ≤ ((4531 : ℝ)/5000) := by linarith
    have hZ : (u + Real.sqrt thrT)^3 ≤ (((4531 : ℝ)/5000))^3 := pow_le_pow_left₀ (by positivity) hA 3
    have he : (u + Real.sqrt thrT) ^ ((193:ℝ)/269) ≤ (((4531 : ℝ)/5000)) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by positivity) hA (by norm_num)
    calc (u + Real.sqrt thrT)^3 * (u + Real.sqrt thrT)^((193:ℝ)/269)
        ≤ (((4531 : ℝ)/5000))^3 * (((4531 : ℝ)/5000))^((193:ℝ)/269) := mul_le_mul hZ he (by positivity) (by positivity)
      _ ≤ (((4531 : ℝ)/5000))^3 * (((233 : ℝ)/250)) := mul_le_mul_of_nonneg_left hce (by positivity)
  have hQ2 : (v + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((2703 : ℝ)/2500))^3 * (((529 : ℝ)/500)) := by
    rw [rpow_q_eq (by positivity)]
    have hce : (((2703 : ℝ)/2500)) ^ ((193:ℝ)/269) ≤ ((529 : ℝ)/500) := by
      simpa using le_rpow_frac (c := ((529 : ℚ)/500)) (z := ((2703 : ℚ)/2500)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : v + Real.sqrt thrT ≤ ((2703 : ℝ)/2500) := by linarith
    have hZ : (v + Real.sqrt thrT)^3 ≤ (((2703 : ℝ)/2500))^3 := pow_le_pow_left₀ (by positivity) hA 3
    have he : (v + Real.sqrt thrT) ^ ((193:ℝ)/269) ≤ (((2703 : ℝ)/2500)) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by positivity) hA (by norm_num)
    calc (v + Real.sqrt thrT)^3 * (v + Real.sqrt thrT)^((193:ℝ)/269)
        ≤ (((2703 : ℝ)/2500))^3 * (((2703 : ℝ)/2500))^((193:ℝ)/269) := mul_le_mul hZ he (by positivity) (by positivity)
      _ ≤ (((2703 : ℝ)/2500))^3 * (((529 : ℝ)/500)) := mul_le_mul_of_nonneg_left hce (by positivity)
  have hkey : ((601 : ℝ)/1000) * ((1269:ℝ)/269) * ((((4531 : ℝ)/5000))^3 * (((233 : ℝ)/250)) + (((2703 : ℝ)/2500))^3 * (((529 : ℝ)/500))) / 2 ≤ (((6453 : ℝ)/5000))^4 * (((6 : ℝ)/5)) + (((8571 : ℝ)/10000))^4 * (((179 : ℝ)/200)) := by
    norm_num
  have hs0 : (0:ℝ) ≤ (v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2) := by
    have h1 : (0:ℝ) ≤ (v + Real.sqrt thrT) ^ (thrTheta - 2) := Real.rpow_nonneg (by linarith) _
    have h2 : (0:ℝ) ≤ (u + Real.sqrt thrT) ^ (thrTheta - 2) := Real.rpow_nonneg (by linarith) _
    linarith
  have hZ0 : (0:ℝ) ≤ (((4531 : ℝ)/5000))^3 * (((233 : ℝ)/250)) + (((2703 : ℝ)/2500))^3 * (((529 : ℝ)/500)) := by positivity
  have hb0 : (0:ℝ) ≤ ((601 : ℝ)/1000) := by norm_num
  have hsumle : (v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((4531 : ℝ)/5000))^3 * (((233 : ℝ)/250)) + (((2703 : ℝ)/2500))^3 * (((529 : ℝ)/500)) := by linarith
  have hprod : u * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2))
      ≤ ((601 : ℝ)/1000) * ((((4531 : ℝ)/5000))^3 * (((233 : ℝ)/250)) + (((2703 : ℝ)/2500))^3 * (((529 : ℝ)/500))) := mul_le_mul hb hsumle hs0 hb0
  have hprod2 := mul_le_mul_of_nonneg_left hprod (by rw [hth1]; norm_num : (0:ℝ) ≤ (thrTheta - 1) / 2)
  have hfin : u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (((6453 : ℝ)/5000))^4 * (((6 : ℝ)/5)) + (((8571 : ℝ)/10000))^4 * (((179 : ℝ)/200)) := by
    calc u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
        = (thrTheta - 1) / 2 * (u * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2))) := by ring
      _ ≤ (thrTheta - 1) / 2 * (((601 : ℝ)/1000) * ((((4531 : ℝ)/5000))^3 * (((233 : ℝ)/250)) + (((2703 : ℝ)/2500))^3 * (((529 : ℝ)/500)))) := hprod2
      _ = ((601 : ℝ)/1000) * ((1269:ℝ)/269) * ((((4531 : ℝ)/5000))^3 * (((233 : ℝ)/250)) + (((2703 : ℝ)/2500))^3 * (((529 : ℝ)/500))) / 2 := by rw [hth1]; ring
      _ ≤ (((6453 : ℝ)/5000))^4 * (((6 : ℝ)/5)) + (((8571 : ℝ)/10000))^4 * (((179 : ℝ)/200)) := hkey
  calc u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (((6453 : ℝ)/5000))^4 * (((6 : ℝ)/5)) + (((8571 : ℝ)/10000))^4 * (((179 : ℝ)/200)) := hfin
    _ ≤ (u + v) ^ (thrTheta - 1) + (u + Real.sqrt thrT) ^ (thrTheta - 1) := by linarith [hL1, hL2]

theorem edgeS_6 {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hs : u ^ 2 + v ^ 2 = thrS)
    (ha : ((601 : ℝ)/1000) ≤ u) (hb : u ≤ ((651 : ℝ)/1000)) :
    u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (u + v) ^ (thrTheta - 1) + (u + Real.sqrt thrT) ^ (thrTheta - 1) := by
  have hv0 : 0 < v := lt_of_lt_of_le hu huv
  have hth1 : thrTheta - 1 = ((1269:ℝ)/269) := by unfold thrTheta; norm_num
  have hwlo : ((3051 : ℝ)/10000) ≤ Real.sqrt thrT := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num [thrT]
  have hwhi : Real.sqrt thrT ≤ ((763 : ℝ)/2500) := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num [thrT]
  have hv2 : v ^ 2 = thrS - u ^ 2 := by linarith
  have hvlo : ((139 : ℝ)/200) ≤ v := by
    have h1 : (((139 : ℝ)/200)) ^ 2 ≤ v ^ 2 := by rw [hv2]; unfold thrS; nlinarith
    nlinarith [h1, hv0, (by norm_num : (0:ℝ) ≤ ((139 : ℝ)/200))]
  have hvhi : v ≤ ((7387 : ℝ)/10000) := by
    have h1 : v ^ 2 ≤ (((7387 : ℝ)/10000)) ^ 2 := by rw [hv2]; unfold thrS; nlinarith
    nlinarith [h1, hv0, (by norm_num : (0:ℝ) ≤ ((7387 : ℝ)/10000))]
  have hL1 : (((162 : ℝ)/125))^4 * (((301 : ℝ)/250)) ≤ (u + v) ^ (thrTheta - 1) := by
    rw [rpow_p_eq (by positivity)]
    have hce : ((301 : ℝ)/250) ≤ (((162 : ℝ)/125)) ^ ((193:ℝ)/269) := by
      simpa using rpow_frac_le (c := ((301 : ℚ)/250)) (z := ((162 : ℚ)/125)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : ((162 : ℝ)/125) ≤ u + v := by linarith
    have hZ : (((162 : ℝ)/125))^4 ≤ (u + v)^4 := pow_le_pow_left₀ (by norm_num) hA 4
    have he : (((162 : ℝ)/125)) ^ ((193:ℝ)/269) ≤ (u + v) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by norm_num) hA (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hce (by positivity)) (mul_le_mul hZ he (by positivity) (by positivity))
  have hL2 : (((9061 : ℝ)/10000))^4 * (((931 : ℝ)/1000)) ≤ (u + Real.sqrt thrT) ^ (thrTheta - 1) := by
    rw [rpow_p_eq (by positivity)]
    have hce : ((931 : ℝ)/1000) ≤ (((9061 : ℝ)/10000)) ^ ((193:ℝ)/269) := by
      simpa using rpow_frac_le (c := ((931 : ℚ)/1000)) (z := ((9061 : ℚ)/10000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : ((9061 : ℝ)/10000) ≤ u + Real.sqrt thrT := by linarith
    have hZ : (((9061 : ℝ)/10000))^4 ≤ (u + Real.sqrt thrT)^4 := pow_le_pow_left₀ (by norm_num) hA 4
    have he : (((9061 : ℝ)/10000)) ^ ((193:ℝ)/269) ≤ (u + Real.sqrt thrT) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by norm_num) hA (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hce (by positivity)) (mul_le_mul hZ he (by positivity) (by positivity))
  have hQ1 : (u + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((4781 : ℝ)/5000))^3 * (((969 : ℝ)/1000)) := by
    rw [rpow_q_eq (by positivity)]
    have hce : (((4781 : ℝ)/5000)) ^ ((193:ℝ)/269) ≤ ((969 : ℝ)/1000) := by
      simpa using le_rpow_frac (c := ((969 : ℚ)/1000)) (z := ((4781 : ℚ)/5000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : u + Real.sqrt thrT ≤ ((4781 : ℝ)/5000) := by linarith
    have hZ : (u + Real.sqrt thrT)^3 ≤ (((4781 : ℝ)/5000))^3 := pow_le_pow_left₀ (by positivity) hA 3
    have he : (u + Real.sqrt thrT) ^ ((193:ℝ)/269) ≤ (((4781 : ℝ)/5000)) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by positivity) hA (by norm_num)
    calc (u + Real.sqrt thrT)^3 * (u + Real.sqrt thrT)^((193:ℝ)/269)
        ≤ (((4781 : ℝ)/5000))^3 * (((4781 : ℝ)/5000))^((193:ℝ)/269) := mul_le_mul hZ he (by positivity) (by positivity)
      _ ≤ (((4781 : ℝ)/5000))^3 * (((969 : ℝ)/1000)) := mul_le_mul_of_nonneg_left hce (by positivity)
  have hQ2 : (v + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((10439 : ℝ)/10000))^3 * (((129 : ℝ)/125)) := by
    rw [rpow_q_eq (by positivity)]
    have hce : (((10439 : ℝ)/10000)) ^ ((193:ℝ)/269) ≤ ((129 : ℝ)/125) := by
      simpa using le_rpow_frac (c := ((129 : ℚ)/125)) (z := ((10439 : ℚ)/10000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : v + Real.sqrt thrT ≤ ((10439 : ℝ)/10000) := by linarith
    have hZ : (v + Real.sqrt thrT)^3 ≤ (((10439 : ℝ)/10000))^3 := pow_le_pow_left₀ (by positivity) hA 3
    have he : (v + Real.sqrt thrT) ^ ((193:ℝ)/269) ≤ (((10439 : ℝ)/10000)) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by positivity) hA (by norm_num)
    calc (v + Real.sqrt thrT)^3 * (v + Real.sqrt thrT)^((193:ℝ)/269)
        ≤ (((10439 : ℝ)/10000))^3 * (((10439 : ℝ)/10000))^((193:ℝ)/269) := mul_le_mul hZ he (by positivity) (by positivity)
      _ ≤ (((10439 : ℝ)/10000))^3 * (((129 : ℝ)/125)) := mul_le_mul_of_nonneg_left hce (by positivity)
  have hkey : ((651 : ℝ)/1000) * ((1269:ℝ)/269) * ((((4781 : ℝ)/5000))^3 * (((969 : ℝ)/1000)) + (((10439 : ℝ)/10000))^3 * (((129 : ℝ)/125))) / 2 ≤ (((162 : ℝ)/125))^4 * (((301 : ℝ)/250)) + (((9061 : ℝ)/10000))^4 * (((931 : ℝ)/1000)) := by
    norm_num
  have hs0 : (0:ℝ) ≤ (v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2) := by
    have h1 : (0:ℝ) ≤ (v + Real.sqrt thrT) ^ (thrTheta - 2) := Real.rpow_nonneg (by linarith) _
    have h2 : (0:ℝ) ≤ (u + Real.sqrt thrT) ^ (thrTheta - 2) := Real.rpow_nonneg (by linarith) _
    linarith
  have hZ0 : (0:ℝ) ≤ (((4781 : ℝ)/5000))^3 * (((969 : ℝ)/1000)) + (((10439 : ℝ)/10000))^3 * (((129 : ℝ)/125)) := by positivity
  have hb0 : (0:ℝ) ≤ ((651 : ℝ)/1000) := by norm_num
  have hsumle : (v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((4781 : ℝ)/5000))^3 * (((969 : ℝ)/1000)) + (((10439 : ℝ)/10000))^3 * (((129 : ℝ)/125)) := by linarith
  have hprod : u * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2))
      ≤ ((651 : ℝ)/1000) * ((((4781 : ℝ)/5000))^3 * (((969 : ℝ)/1000)) + (((10439 : ℝ)/10000))^3 * (((129 : ℝ)/125))) := mul_le_mul hb hsumle hs0 hb0
  have hprod2 := mul_le_mul_of_nonneg_left hprod (by rw [hth1]; norm_num : (0:ℝ) ≤ (thrTheta - 1) / 2)
  have hfin : u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (((162 : ℝ)/125))^4 * (((301 : ℝ)/250)) + (((9061 : ℝ)/10000))^4 * (((931 : ℝ)/1000)) := by
    calc u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
        = (thrTheta - 1) / 2 * (u * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2))) := by ring
      _ ≤ (thrTheta - 1) / 2 * (((651 : ℝ)/1000) * ((((4781 : ℝ)/5000))^3 * (((969 : ℝ)/1000)) + (((10439 : ℝ)/10000))^3 * (((129 : ℝ)/125)))) := hprod2
      _ = ((651 : ℝ)/1000) * ((1269:ℝ)/269) * ((((4781 : ℝ)/5000))^3 * (((969 : ℝ)/1000)) + (((10439 : ℝ)/10000))^3 * (((129 : ℝ)/125))) / 2 := by rw [hth1]; ring
      _ ≤ (((162 : ℝ)/125))^4 * (((301 : ℝ)/250)) + (((9061 : ℝ)/10000))^4 * (((931 : ℝ)/1000)) := hkey
  calc u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (((162 : ℝ)/125))^4 * (((301 : ℝ)/250)) + (((9061 : ℝ)/10000))^4 * (((931 : ℝ)/1000)) := hfin
    _ ≤ (u + v) ^ (thrTheta - 1) + (u + Real.sqrt thrT) ^ (thrTheta - 1) := by linarith [hL1, hL2]

theorem edgeS_7 {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hs : u ^ 2 + v ^ 2 = thrS)
    (ha : ((651 : ℝ)/1000) ≤ u) (hb : u ≤ ((7 : ℝ)/10)) :
    u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (u + v) ^ (thrTheta - 1) + (u + Real.sqrt thrT) ^ (thrTheta - 1) := by
  have hv0 : 0 < v := lt_of_lt_of_le hu huv
  have hth1 : thrTheta - 1 = ((1269:ℝ)/269) := by unfold thrTheta; norm_num
  have hwlo : ((3051 : ℝ)/10000) ≤ Real.sqrt thrT := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num [thrT]
  have hwhi : Real.sqrt thrT ≤ ((763 : ℝ)/2500) := by
    rw [Real.sqrt_le_iff]; constructor <;> norm_num [thrT]
  have hv2 : v ^ 2 = thrS - u ^ 2 := by linarith
  have hvlo : ((807 : ℝ)/1250) ≤ v := by
    have h1 : (((807 : ℝ)/1250)) ^ 2 ≤ v ^ 2 := by rw [hv2]; unfold thrS; nlinarith
    nlinarith [h1, hv0, (by norm_num : (0:ℝ) ≤ ((807 : ℝ)/1250))]
  have hvhi : v ≤ ((6951 : ℝ)/10000) := by
    have h1 : v ^ 2 ≤ (((6951 : ℝ)/10000)) ^ 2 := by rw [hv2]; unfold thrS; nlinarith
    nlinarith [h1, hv0, (by norm_num : (0:ℝ) ≤ ((6951 : ℝ)/10000))]
  have hL1 : (((6483 : ℝ)/5000))^4 * (((301 : ℝ)/250)) ≤ (u + v) ^ (thrTheta - 1) := by
    rw [rpow_p_eq (by positivity)]
    have hce : ((301 : ℝ)/250) ≤ (((6483 : ℝ)/5000)) ^ ((193:ℝ)/269) := by
      simpa using rpow_frac_le (c := ((301 : ℚ)/250)) (z := ((6483 : ℚ)/5000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : ((6483 : ℝ)/5000) ≤ u + v := by linarith
    have hZ : (((6483 : ℝ)/5000))^4 ≤ (u + v)^4 := pow_le_pow_left₀ (by norm_num) hA 4
    have he : (((6483 : ℝ)/5000)) ^ ((193:ℝ)/269) ≤ (u + v) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by norm_num) hA (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hce (by positivity)) (mul_le_mul hZ he (by positivity) (by positivity))
  have hL2 : (((9561 : ℝ)/10000))^4 * (((121 : ℝ)/125)) ≤ (u + Real.sqrt thrT) ^ (thrTheta - 1) := by
    rw [rpow_p_eq (by positivity)]
    have hce : ((121 : ℝ)/125) ≤ (((9561 : ℝ)/10000)) ^ ((193:ℝ)/269) := by
      simpa using rpow_frac_le (c := ((121 : ℚ)/125)) (z := ((9561 : ℚ)/10000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : ((9561 : ℝ)/10000) ≤ u + Real.sqrt thrT := by linarith
    have hZ : (((9561 : ℝ)/10000))^4 ≤ (u + Real.sqrt thrT)^4 := pow_le_pow_left₀ (by norm_num) hA 4
    have he : (((9561 : ℝ)/10000)) ^ ((193:ℝ)/269) ≤ (u + Real.sqrt thrT) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by norm_num) hA (by norm_num)
    exact le_trans (mul_le_mul_of_nonneg_left hce (by positivity)) (mul_le_mul hZ he (by positivity) (by positivity))
  have hQ1 : (u + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((2513 : ℝ)/2500))^3 * (((251 : ℝ)/250)) := by
    rw [rpow_q_eq (by positivity)]
    have hce : (((2513 : ℝ)/2500)) ^ ((193:ℝ)/269) ≤ ((251 : ℝ)/250) := by
      simpa using le_rpow_frac (c := ((251 : ℚ)/250)) (z := ((2513 : ℚ)/2500)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : u + Real.sqrt thrT ≤ ((2513 : ℝ)/2500) := by linarith
    have hZ : (u + Real.sqrt thrT)^3 ≤ (((2513 : ℝ)/2500))^3 := pow_le_pow_left₀ (by positivity) hA 3
    have he : (u + Real.sqrt thrT) ^ ((193:ℝ)/269) ≤ (((2513 : ℝ)/2500)) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by positivity) hA (by norm_num)
    calc (u + Real.sqrt thrT)^3 * (u + Real.sqrt thrT)^((193:ℝ)/269)
        ≤ (((2513 : ℝ)/2500))^3 * (((2513 : ℝ)/2500))^((193:ℝ)/269) := mul_le_mul hZ he (by positivity) (by positivity)
      _ ≤ (((2513 : ℝ)/2500))^3 * (((251 : ℝ)/250)) := mul_le_mul_of_nonneg_left hce (by positivity)
  have hQ2 : (v + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((10003 : ℝ)/10000))^3 * (((1001 : ℝ)/1000)) := by
    rw [rpow_q_eq (by positivity)]
    have hce : (((10003 : ℝ)/10000)) ^ ((193:ℝ)/269) ≤ ((1001 : ℝ)/1000) := by
      simpa using le_rpow_frac (c := ((1001 : ℚ)/1000)) (z := ((10003 : ℚ)/10000)) (by norm_num) (by norm_num) (by decide +kernel)
    have hA : v + Real.sqrt thrT ≤ ((10003 : ℝ)/10000) := by linarith
    have hZ : (v + Real.sqrt thrT)^3 ≤ (((10003 : ℝ)/10000))^3 := pow_le_pow_left₀ (by positivity) hA 3
    have he : (v + Real.sqrt thrT) ^ ((193:ℝ)/269) ≤ (((10003 : ℝ)/10000)) ^ ((193:ℝ)/269) := Real.rpow_le_rpow (by positivity) hA (by norm_num)
    calc (v + Real.sqrt thrT)^3 * (v + Real.sqrt thrT)^((193:ℝ)/269)
        ≤ (((10003 : ℝ)/10000))^3 * (((10003 : ℝ)/10000))^((193:ℝ)/269) := mul_le_mul hZ he (by positivity) (by positivity)
      _ ≤ (((10003 : ℝ)/10000))^3 * (((1001 : ℝ)/1000)) := mul_le_mul_of_nonneg_left hce (by positivity)
  have hkey : ((7 : ℝ)/10) * ((1269:ℝ)/269) * ((((2513 : ℝ)/2500))^3 * (((251 : ℝ)/250)) + (((10003 : ℝ)/10000))^3 * (((1001 : ℝ)/1000))) / 2 ≤ (((6483 : ℝ)/5000))^4 * (((301 : ℝ)/250)) + (((9561 : ℝ)/10000))^4 * (((121 : ℝ)/125)) := by
    norm_num
  have hs0 : (0:ℝ) ≤ (v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2) := by
    have h1 : (0:ℝ) ≤ (v + Real.sqrt thrT) ^ (thrTheta - 2) := Real.rpow_nonneg (by linarith) _
    have h2 : (0:ℝ) ≤ (u + Real.sqrt thrT) ^ (thrTheta - 2) := Real.rpow_nonneg (by linarith) _
    linarith
  have hZ0 : (0:ℝ) ≤ (((2513 : ℝ)/2500))^3 * (((251 : ℝ)/250)) + (((10003 : ℝ)/10000))^3 * (((1001 : ℝ)/1000)) := by positivity
  have hb0 : (0:ℝ) ≤ ((7 : ℝ)/10) := by norm_num
  have hsumle : (v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2) ≤ (((2513 : ℝ)/2500))^3 * (((251 : ℝ)/250)) + (((10003 : ℝ)/10000))^3 * (((1001 : ℝ)/1000)) := by linarith
  have hprod : u * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2))
      ≤ ((7 : ℝ)/10) * ((((2513 : ℝ)/2500))^3 * (((251 : ℝ)/250)) + (((10003 : ℝ)/10000))^3 * (((1001 : ℝ)/1000))) := mul_le_mul hb hsumle hs0 hb0
  have hprod2 := mul_le_mul_of_nonneg_left hprod (by rw [hth1]; norm_num : (0:ℝ) ≤ (thrTheta - 1) / 2)
  have hfin : u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (((6483 : ℝ)/5000))^4 * (((301 : ℝ)/250)) + (((9561 : ℝ)/10000))^4 * (((121 : ℝ)/125)) := by
    calc u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
        = (thrTheta - 1) / 2 * (u * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2))) := by ring
      _ ≤ (thrTheta - 1) / 2 * (((7 : ℝ)/10) * ((((2513 : ℝ)/2500))^3 * (((251 : ℝ)/250)) + (((10003 : ℝ)/10000))^3 * (((1001 : ℝ)/1000)))) := hprod2
      _ = ((7 : ℝ)/10) * ((1269:ℝ)/269) * ((((2513 : ℝ)/2500))^3 * (((251 : ℝ)/250)) + (((10003 : ℝ)/10000))^3 * (((1001 : ℝ)/1000))) / 2 := by rw [hth1]; ring
      _ ≤ (((6483 : ℝ)/5000))^4 * (((301 : ℝ)/250)) + (((9561 : ℝ)/10000))^4 * (((121 : ℝ)/125)) := hkey
  calc u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (((6483 : ℝ)/5000))^4 * (((301 : ℝ)/250)) + (((9561 : ℝ)/10000))^4 * (((121 : ℝ)/125)) := hfin
    _ ≤ (u + v) ^ (thrTheta - 1) + (u + Real.sqrt thrT) ^ (thrTheta - 1) := by linarith [hL1, hL2]

theorem edgeS {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) (hs : u ^ 2 + v ^ 2 = thrS)
    (hwu : Real.sqrt thrT ≤ u) :
    u * (thrTheta - 1) * ((v + Real.sqrt thrT) ^ (thrTheta - 2) + (u + Real.sqrt thrT) ^ (thrTheta - 2)) / 2
      ≤ (u + v) ^ (thrTheta - 1) + (u + Real.sqrt thrT) ^ (thrTheta - 1) := by
  have hwlo : ((3051 : ℝ)/10000) ≤ Real.sqrt thrT := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num [thrT]
  have hw305 : ((61 : ℝ)/200) ≤ Real.sqrt thrT := le_trans (by norm_num) hwlo
  have hu2 : u ^ 2 ≤ thrS / 2 := by nlinarith [hs, sq_nonneg (v - u)]
  have hs7 : thrS / 2 ≤ ((7:ℝ)/10) * ((7:ℝ)/10) := by unfold thrS; norm_num
  have hu7 : u ≤ (7:ℝ)/10 := by nlinarith [hu2, hs7, hu]
  rcases lt_or_ge u ((177 : ℝ)/500) with h1 | h1
  · exact edgeS_0 hu huv hs (le_trans hw305 hwu) h1.le
  rcases lt_or_ge u ((101 : ℝ)/250) with h2 | h2
  · exact edgeS_1 hu huv hs (h1) h2.le
  rcases lt_or_ge u ((453 : ℝ)/1000) with h3 | h3
  · exact edgeS_2 hu huv hs (h2) h3.le
  rcases lt_or_ge u ((503 : ℝ)/1000) with h4 | h4
  · exact edgeS_3 hu huv hs (h3) h4.le
  rcases lt_or_ge u ((69 : ℝ)/125) with h5 | h5
  · exact edgeS_4 hu huv hs (h4) h5.le
  rcases lt_or_ge u ((601 : ℝ)/1000) with h6 | h6
  · exact edgeS_5 hu huv hs (h5) h6.le
  rcases lt_or_ge u ((651 : ℝ)/1000) with h7 | h7
  · exact edgeS_6 hu huv hs (h6) h7.le
  · exact edgeS_7 hu huv hs (h7) hu7


theorem edgePsi : EdgePsi := by
  intro x hx1 hx2
  have hx0 : 0 < x := lt_trans thrT_pos hx1
  have hy0 : 0 < thrS - x := by linarith [hx2, thrS_pos]
  have hu0 : 0 < Real.sqrt x := Real.sqrt_pos_of_pos hx0
  have hv0 : 0 < Real.sqrt (thrS - x) := Real.sqrt_pos_of_pos hy0
  have hu2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  have hv2 : Real.sqrt (thrS - x) ^ 2 = thrS - x := Real.sq_sqrt hy0.le
  have hs : Real.sqrt x ^ 2 + Real.sqrt (thrS - x) ^ 2 = thrS := by rw [hu2, hv2]; ring
  have huv : Real.sqrt x ≤ Real.sqrt (thrS - x) := Real.sqrt_le_sqrt (by linarith)
  have hrw : Real.sqrt thrT ≤ Real.sqrt x := Real.sqrt_le_sqrt hx1.le
  have hS := edgeS hu0 huv hs hrw
  have hw0 : (0:ℝ) < Real.sqrt thrT := Real.sqrt_pos_of_pos thrT_pos
  have hC0 : (0:ℝ) < Real.sqrt x + Real.sqrt thrT := by linarith
  have hCB : Real.sqrt x + Real.sqrt thrT ≤ Real.sqrt (thrS - x) + Real.sqrt thrT := by linarith
  have hq : (2:ℝ) ≤ thrTheta - 1 := by unfold thrTheta; norm_num
  have htrap := rpow_sec_le_trap (q := thrTheta - 1) hq hC0 hCB
  have htrap' : (Real.sqrt (thrS - x) + Real.sqrt thrT) ^ (thrTheta - 1) - (Real.sqrt x + Real.sqrt thrT) ^ (thrTheta - 1)
      ≤ (thrTheta - 1) * (Real.sqrt (thrS - x) - Real.sqrt x)
        * ((Real.sqrt (thrS - x) + Real.sqrt thrT) ^ (thrTheta - 2) + (Real.sqrt x + Real.sqrt thrT) ^ (thrTheta - 2)) / 2 := by
    rw [show thrTheta - 1 - 1 = thrTheta - 2 by ring] at htrap
    rw [show (Real.sqrt (thrS - x) + Real.sqrt thrT) - (Real.sqrt x + Real.sqrt thrT) = Real.sqrt (thrS - x) - Real.sqrt x by ring] at htrap
    exact htrap
  have hstep := mul_le_mul_of_nonneg_left htrap' hu0.le
  have hvu : 0 ≤ Real.sqrt (thrS - x) - Real.sqrt x := by linarith
  rw [phi_eS_sub]
  unfold phi
  have hbr : 0 ≤ (Real.sqrt x + Real.sqrt (thrS - x)) ^ (thrTheta - 1) + (Real.sqrt x + Real.sqrt thrT) ^ (thrTheta - 1)
      - Real.sqrt x * ((thrTheta - 1) * ((Real.sqrt (thrS - x) + Real.sqrt thrT) ^ (thrTheta - 2) + (Real.sqrt x + Real.sqrt thrT) ^ (thrTheta - 2))) / 2 := by linarith [hS]
  have hkey2 : 0 ≤ (Real.sqrt (thrS - x) - Real.sqrt x)
      * ((Real.sqrt x + Real.sqrt (thrS - x)) ^ (thrTheta - 1) + (Real.sqrt x + Real.sqrt thrT) ^ (thrTheta - 1)
        - Real.sqrt x * ((thrTheta - 1) * ((Real.sqrt (thrS - x) + Real.sqrt thrT) ^ (thrTheta - 2) + (Real.sqrt x + Real.sqrt thrT) ^ (thrTheta - 2))) / 2) :=
    mul_nonneg hvu hbr
  nlinarith [hstep, hkey2]


/-! ### Section VI: the interior critical point, unconditionally

The boundary of the corner domain is handled by `edge_one_dim` (Section VII,
using the unconditional `EdgePsi`).  At an interior maximum of the branch sum
the two directional derivatives along the simplex vanish; the resulting
relations force two of the three branch bases `a = sqrt x`, `b = sqrt y`,
`c = sqrt z` to coincide, because the three numbers `a + b - c`, `b + c - a`,
`a + c - b` are roots of one strictly convex equation.  The value is then the
one-variable profile `xiProf` on the collision families, which is bounded by
the interval certificate `xiSeg_all`. -/


open scoped Topology

noncomputable def bProf (v : ℝ) : ℝ := v + Real.sqrt ((1 - v ^ 2) / 2)

lemma hasDerivAt_bProf {v : ℝ} (hv : 0 < 1 - v ^ 2) :
    HasDerivAt bProf (1 - v / (2 * Real.sqrt ((1 - v ^ 2) / 2))) v := by
  have h1 : HasDerivAt (fun v : ℝ => 1 - v ^ 2) (-2 * v) v := by
    simpa using ((hasDerivAt_pow 2 v).const_sub 1)
  have h2 : HasDerivAt (fun v : ℝ => (1 - v ^ 2) / 2) ((-2 * v) / 2) v := h1.div_const 2
  have hpos : 0 < (1 - v ^ 2) / 2 := by linarith
  have h3 := (Real.hasDerivAt_sqrt hpos.ne').comp v h2
  have h4 : HasDerivAt (fun v : ℝ => v + Real.sqrt ((1 - v ^ 2) / 2))
      (1 + (1 / (2 * Real.sqrt ((1 - v ^ 2) / 2)) * ((-2 * v) / 2))) v :=
    (hasDerivAt_id v).add h3
  have h5 : bProf = fun v : ℝ => v + Real.sqrt ((1 - v ^ 2) / 2) := rfl
  rw [h5]
  convert h4 using 1
  have hs : 0 < Real.sqrt ((1 - v ^ 2) / 2) := Real.sqrt_pos_of_pos hpos
  field_simp
  ring

lemma deriv_bProf_eq {v : ℝ} (hv : 0 < 1 - v ^ 2) :
    deriv bProf v = 1 - v / (2 * Real.sqrt ((1 - v ^ 2) / 2)) :=
  (hasDerivAt_bProf hv).deriv

lemma bProf_monoOn : MonotoneOn bProf (Set.Icc 0 (408/500)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
  · exact (by unfold bProf; fun_prop : Continuous bProf).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    obtain ⟨h1, h2⟩ := hx
    have hp : 0 < 1 - x ^ 2 := by
      nlinarith [mul_pos (by linarith : (0:ℝ) < x) (by linarith : (0:ℝ) < 408/500 - x)]
    exact (hasDerivAt_bProf hp).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    obtain ⟨h1, h2⟩ := hx
    have hp : 0 < 1 - x ^ 2 := by
      nlinarith [mul_pos (by linarith : (0:ℝ) < x) (by linarith : (0:ℝ) < 408/500 - x)]
    rw [deriv_bProf_eq hp]
    have h3 : x ^ 2 ≤ 2/3 := by
      nlinarith [mul_pos (by linarith : (0:ℝ) < x) (by linarith : (0:ℝ) < 408/500 - x)]
    have hs : 0 < Real.sqrt ((1 - x ^ 2) / 2) := Real.sqrt_pos_of_pos (by linarith)
    rw [sub_nonneg, div_le_one (by linarith)]
    have hle : x / 2 ≤ Real.sqrt ((1 - x ^ 2) / 2) := by
      rw [Real.le_sqrt' (by linarith : (0:ℝ) < x / 2)]
      nlinarith
    linarith

lemma bProf_antiOn : AntitoneOn bProf (Set.Icc (817/1000) 1) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
  · exact (by unfold bProf; fun_prop : Continuous bProf).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    obtain ⟨h1, h2⟩ := hx
    have hp : 0 < 1 - x ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x) (by linarith : (0:ℝ) ≤ 1 - x)]
    exact (hasDerivAt_bProf hp).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    obtain ⟨h1, h2⟩ := hx
    have hp : 0 < 1 - x ^ 2 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ x) (by linarith : (0:ℝ) ≤ 1 - x)]
    rw [deriv_bProf_eq hp]
    have h3 : 2/3 ≤ x ^ 2 := by nlinarith [sq_nonneg (x - 817/1000)]
    have hs : 0 < Real.sqrt ((1 - x ^ 2) / 2) := Real.sqrt_pos_of_pos (by linarith)
    rw [sub_nonpos, le_div_iff₀ (by linarith : (0:ℝ) < 2 * Real.sqrt ((1 - x ^ 2) / 2))]
    have hle : Real.sqrt ((1 - x ^ 2) / 2) ≤ x / 2 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by linarith, by nlinarith⟩
    linarith

lemma bProf_le {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) : bProf v ≤ Real.sqrt (3/2) := by
  have hb : 0 ≤ bProf v := by unfold bProf; positivity
  rw [Real.le_sqrt hb (by norm_num)]
  set s := Real.sqrt ((1 - v ^ 2) / 2) with hsdef
  have hs2 : s ^ 2 = (1 - v ^ 2) / 2 := Real.sq_sqrt (by nlinarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hbs : bProf v = v + s := by unfold bProf; rw [hsdef]
  have key : 4 * v * s ≤ 2 - v ^ 2 := by
    have h : (4 * v * s) ^ 2 ≤ (2 - v ^ 2) ^ 2 := by nlinarith [sq_nonneg (3 * v ^ 2 - 2), hs2]
    nlinarith [h, hs0, h0, h1, sq_nonneg (4 * v * s + (2 - v ^ 2)), sq_nonneg (4 * v * s - (2 - v ^ 2))]
  rw [hbs]
  nlinarith [key, hs2, hs0]

lemma xiSeg_core {v M N : ℝ} (hv0 : 0 < v) (hB : bProf v ≤ M) (hM : 0 < M)
    (hN : M ^ ((193:ℝ)/269) ≤ N) (hnum : 2 * M^4 * N ≤ (29/4) * v) :
    2 * bProf v ^ (thrTheta - 1) ≤ (29/4) * v := by
  have hb : 0 < bProf v := by unfold bProf; nlinarith [Real.sqrt_nonneg ((1 - v^2)/2)]
  have h1 : bProf v ^ (thrTheta - 1) ≤ M ^ (thrTheta - 1) :=
    Real.rpow_le_rpow hb.le hB (by unfold thrTheta; norm_num)
  have h2 : M ^ (thrTheta - 1) = M^4 * M ^ ((193:ℝ)/269) := rpow_p_eq hM
  have h3 : M^4 * M ^ ((193:ℝ)/269) ≤ M^4 * N := mul_le_mul_of_nonneg_left hN (by positivity)
  linarith

-- segment 0: L on [3051/10000, 697/2000]
lemma xiSeg_0 {v : ℝ} (hlo : (3051/10000 : ℝ) ≤ v) (hhi : v ≤ (697/2000 : ℝ)) :
    2 * bProf v ^ (thrTheta - 1) ≤ (29/4 : ℝ) * v := by
  refine xiSeg_core (M := (505639/500000 : ℝ)) (N := (1008079/1000000 : ℝ)) (by linarith) ?_ (by norm_num) ?_ ?_
  · have hm : bProf v ≤ bProf (697/2000 : ℝ) := bProf_monoOn (by constructor <;> linarith) (by constructor <;> norm_num) hhi
    have hc : bProf (697/2000 : ℝ) ≤ (505639/500000 : ℝ) := by
      unfold bProf
      have hs : Real.sqrt ((1 - ((697/2000 : ℝ))^2)/2) ≤ (331389/500000 : ℝ) := by
        rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
      linarith
    linarith
  · simpa using le_rpow_frac (c := ((1008079:ℚ)/1000000)) (z := ((505639:ℚ)/500000)) (by norm_num) (by norm_num) (by decide +kernel)
  · have hnum : 2 * (505639/500000 : ℝ)^4 * (1008079/1000000 : ℝ) ≤ (29/4) * (3051/10000 : ℝ) := by norm_num
    linarith

-- segment 1: L on [697/2000, 973/2500]
lemma xiSeg_1 {v : ℝ} (hlo : (697/2000 : ℝ) ≤ v) (hhi : v ≤ (973/2500 : ℝ)) :
    2 * bProf v ^ (thrTheta - 1) ≤ (29/4 : ℝ) * v := by
  refine xiSeg_core (M := (520277/500000 : ℝ)) (N := (1028933/1000000 : ℝ)) (by linarith) ?_ (by norm_num) ?_ ?_
  · have hm : bProf v ≤ bProf (973/2500 : ℝ) := bProf_monoOn (by constructor <;> linarith) (by constructor <;> norm_num) hhi
    have hc : bProf (973/2500 : ℝ) ≤ (520277/500000 : ℝ) := by
      unfold bProf
      have hs : Real.sqrt ((1 - ((973/2500 : ℝ))^2)/2) ≤ (325677/500000 : ℝ) := by
        rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
      linarith
    linarith
  · simpa using le_rpow_frac (c := ((1028933:ℚ)/1000000)) (z := ((520277:ℚ)/500000)) (by norm_num) (by norm_num) (by decide +kernel)
  · have hnum : 2 * (520277/500000 : ℝ)^4 * (1028933/1000000 : ℝ) ≤ (29/4) * (697/2000 : ℝ) := by norm_num
    linarith

-- segment 2: L on [973/2500, 4273/10000]
lemma xiSeg_2 {v : ℝ} (hlo : (973/2500 : ℝ) ≤ v) (hhi : v ≤ (4273/10000 : ℝ)) :
    2 * bProf v ^ (thrTheta - 1) ≤ (29/4 : ℝ) * v := by
  refine xiSeg_core (M := (1066603/1000000 : ℝ)) (N := (1047349/1000000 : ℝ)) (by linarith) ?_ (by norm_num) ?_ ?_
  · have hm : bProf v ≤ bProf (4273/10000 : ℝ) := bProf_monoOn (by constructor <;> linarith) (by constructor <;> norm_num) hhi
    have hc : bProf (4273/10000 : ℝ) ≤ (1066603/1000000 : ℝ) := by
      unfold bProf
      have hs : Real.sqrt ((1 - ((4273/10000 : ℝ))^2)/2) ≤ (639303/1000000 : ℝ) := by
        rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
      linarith
    linarith
  · simpa using le_rpow_frac (c := ((1047349:ℚ)/1000000)) (z := ((1066603:ℚ)/1000000)) (by norm_num) (by norm_num) (by decide +kernel)
  · have hnum : 2 * (1066603/1000000 : ℝ)^4 * (1047349/1000000 : ℝ) ≤ (29/4) * (973/2500 : ℝ) := by norm_num
    linarith

-- segment 3: L on [4273/10000, 463/1000]
lemma xiSeg_3 {v : ℝ} (hlo : (4273/10000 : ℝ) ≤ v) (hhi : v ≤ (463/1000 : ℝ)) :
    2 * bProf v ^ (thrTheta - 1) ≤ (29/4 : ℝ) * v := by
  refine xiSeg_core (M := (4359/4000 : ℝ)) (N := (1063607/1000000 : ℝ)) (by linarith) ?_ (by norm_num) ?_ ?_
  · have hm : bProf v ≤ bProf (463/1000 : ℝ) := bProf_monoOn (by constructor <;> linarith) (by constructor <;> norm_num) hhi
    have hc : bProf (463/1000 : ℝ) ≤ (4359/4000 : ℝ) := by
      unfold bProf
      have hs : Real.sqrt ((1 - ((463/1000 : ℝ))^2)/2) ≤ (2507/4000 : ℝ) := by
        rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
      linarith
    linarith
  · simpa using le_rpow_frac (c := ((1063607:ℚ)/1000000)) (z := ((4359:ℚ)/4000)) (by norm_num) (by norm_num) (by decide +kernel)
  · have hnum : 2 * (4359/4000 : ℝ)^4 * (1063607/1000000 : ℝ) ≤ (29/4) * (4273/10000 : ℝ) := by norm_num
    linarith

-- segment 4: L on [463/1000, 993/2000]
lemma xiSeg_4 {v : ℝ} (hlo : (463/1000 : ℝ) ≤ v) (hhi : v ≤ (993/2000 : ℝ)) :
    2 * bProf v ^ (thrTheta - 1) ≤ (29/4 : ℝ) * v := by
  refine xiSeg_core (M := (222059/200000 : ℝ)) (N := (269489/250000 : ℝ)) (by linarith) ?_ (by norm_num) ?_ ?_
  · have hm : bProf v ≤ bProf (993/2000 : ℝ) := bProf_monoOn (by constructor <;> linarith) (by constructor <;> norm_num) hhi
    have hc : bProf (993/2000 : ℝ) ≤ (222059/200000 : ℝ) := by
      unfold bProf
      have hs : Real.sqrt ((1 - ((993/2000 : ℝ))^2)/2) ≤ (122759/200000 : ℝ) := by
        rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
      linarith
    linarith
  · simpa using le_rpow_frac (c := ((269489:ℚ)/250000)) (z := ((222059:ℚ)/200000)) (by norm_num) (by norm_num) (by decide +kernel)
  · have hnum : 2 * (222059/200000 : ℝ)^4 * (269489/250000 : ℝ) ≤ (29/4) * (463/1000 : ℝ) := by norm_num
    linarith

-- segment 5: L on [993/2000, 5279/10000]
lemma xiSeg_5 {v : ℝ} (hlo : (993/2000 : ℝ) ≤ v) (hhi : v ≤ (5279/10000 : ℝ)) :
    2 * bProf v ^ (thrTheta - 1) ≤ (29/4 : ℝ) * v := by
  refine xiSeg_core (M := (1128451/1000000 : ℝ)) (N := (545287/500000 : ℝ)) (by linarith) ?_ (by norm_num) ?_ ?_
  · have hm : bProf v ≤ bProf (5279/10000 : ℝ) := bProf_monoOn (by constructor <;> linarith) (by constructor <;> norm_num) hhi
    have hc : bProf (5279/10000 : ℝ) ≤ (1128451/1000000 : ℝ) := by
      unfold bProf
      have hs : Real.sqrt ((1 - ((5279/10000 : ℝ))^2)/2) ≤ (600551/1000000 : ℝ) := by
        rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
      linarith
    linarith
  · simpa using le_rpow_frac (c := ((545287:ℚ)/500000)) (z := ((1128451:ℚ)/1000000)) (by norm_num) (by norm_num) (by decide +kernel)
  · have hnum : 2 * (1128451/1000000 : ℝ)^4 * (545287/500000 : ℝ) ≤ (29/4) * (993/2000 : ℝ) := by norm_num
    linarith

-- segment 6: L on [5279/10000, 2787/5000]
lemma xiSeg_6 {v : ℝ} (hlo : (5279/10000 : ℝ) ≤ v) (hhi : v ≤ (2787/5000 : ℝ)) :
    2 * bProf v ^ (thrTheta - 1) ≤ (29/4 : ℝ) * v := by
  refine xiSeg_core (M := (143059/125000 : ℝ)) (N := (55083/50000 : ℝ)) (by linarith) ?_ (by norm_num) ?_ ?_
  · have hm : bProf v ≤ bProf (2787/5000 : ℝ) := bProf_monoOn (by constructor <;> linarith) (by constructor <;> norm_num) hhi
    have hc : bProf (2787/5000 : ℝ) ≤ (143059/125000 : ℝ) := by
      unfold bProf
      have hs : Real.sqrt ((1 - ((2787/5000 : ℝ))^2)/2) ≤ (9173/15625 : ℝ) := by
        rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
      linarith
    linarith
  · simpa using le_rpow_frac (c := ((55083:ℚ)/50000)) (z := ((143059:ℚ)/125000)) (by norm_num) (by norm_num) (by decide +kernel)
  · have hnum : 2 * (143059/125000 : ℝ)^4 * (55083/50000 : ℝ) ≤ (29/4) * (5279/10000 : ℝ) := by norm_num
    linarith

-- segment 7: L on [2787/5000, 117/200]
lemma xiSeg_7 {v : ℝ} (hlo : (2787/5000 : ℝ) ≤ v) (hhi : v ≤ (117/200 : ℝ)) :
    2 * bProf v ^ (thrTheta - 1) ≤ (29/4 : ℝ) * v := by
  refine xiSeg_core (M := (144811/125000 : ℝ)) (N := (277831/250000 : ℝ)) (by linarith) ?_ (by norm_num) ?_ ?_
  · have hm : bProf v ≤ bProf (117/200 : ℝ) := bProf_monoOn (by constructor <;> linarith) (by constructor <;> norm_num) hhi
    have hc : bProf (117/200 : ℝ) ≤ (144811/125000 : ℝ) := by
      unfold bProf
      have hs : Real.sqrt ((1 - ((117/200 : ℝ))^2)/2) ≤ (35843/62500 : ℝ) := by
        rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
      linarith
    linarith
  · simpa using le_rpow_frac (c := ((277831:ℚ)/250000)) (z := ((144811:ℚ)/125000)) (by norm_num) (by norm_num) (by decide +kernel)
  · have hnum : 2 * (144811/125000 : ℝ)^4 * (277831/250000 : ℝ) ≤ (29/4) * (2787/5000 : ℝ) := by norm_num
    linarith

-- segment 8: L on [117/200, 6109/10000]
lemma xiSeg_8 {v : ℝ} (hlo : (117/200 : ℝ) ≤ v) (hhi : v ≤ (6109/10000 : ℝ)) :
    2 * bProf v ^ (thrTheta - 1) ≤ (29/4 : ℝ) * v := by
  refine xiSeg_core (M := (585361/500000 : ℝ)) (N := (1119731/1000000 : ℝ)) (by linarith) ?_ (by norm_num) ?_ ?_
  · have hm : bProf v ≤ bProf (6109/10000 : ℝ) := bProf_monoOn (by constructor <;> linarith) (by constructor <;> norm_num) hhi
    have hc : bProf (6109/10000 : ℝ) ≤ (585361/500000 : ℝ) := by
      unfold bProf
      have hs : Real.sqrt ((1 - ((6109/10000 : ℝ))^2)/2) ≤ (279911/500000 : ℝ) := by
        rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
      linarith
    linarith
  · simpa using le_rpow_frac (c := ((1119731:ℚ)/1000000)) (z := ((585361:ℚ)/500000)) (by norm_num) (by norm_num) (by decide +kernel)
  · have hnum : 2 * (585361/500000 : ℝ)^4 * (1119731/1000000 : ℝ) ≤ (29/4) * (117/200 : ℝ) := by norm_num
    linarith

-- segment 9: L on [6109/10000, 397/625]
lemma xiSeg_9 {v : ℝ} (hlo : (6109/10000 : ℝ) ≤ v) (hhi : v ≤ (397/625 : ℝ)) :
    2 * bProf v ^ (thrTheta - 1) ≤ (29/4 : ℝ) * v := by
  refine xiSeg_core (M := (1181333/1000000 : ℝ)) (N := (281751/250000 : ℝ)) (by linarith) ?_ (by norm_num) ?_ ?_
  · have hm : bProf v ≤ bProf (397/625 : ℝ) := bProf_monoOn (by constructor <;> linarith) (by constructor <;> norm_num) hhi
    have hc : bProf (397/625 : ℝ) ≤ (1181333/1000000 : ℝ) := by
      unfold bProf
      have hs : Real.sqrt ((1 - ((397/625 : ℝ))^2)/2) ≤ (546133/1000000 : ℝ) := by
        rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
      linarith
    linarith
  · simpa using le_rpow_frac (c := ((281751:ℚ)/250000)) (z := ((1181333:ℚ)/1000000)) (by norm_num) (by norm_num) (by decide +kernel)
  · have hnum : 2 * (1181333/1000000 : ℝ)^4 * (281751/250000 : ℝ) ≤ (29/4) * (6109/10000 : ℝ) := by norm_num
    linarith

-- segment 10: L on [397/625, 6579/10000]
lemma xiSeg_10 {v : ℝ} (hlo : (397/625 : ℝ) ≤ v) (hhi : v ≤ (6579/10000 : ℝ)) :
    2 * bProf v ^ (thrTheta - 1) ≤ (29/4 : ℝ) * v := by
  refine xiSeg_core (M := (595213/500000 : ℝ)) (N := (1133221/1000000 : ℝ)) (by linarith) ?_ (by norm_num) ?_ ?_
  · have hm : bProf v ≤ bProf (6579/10000 : ℝ) := bProf_monoOn (by constructor <;> linarith) (by constructor <;> norm_num) hhi
    have hc : bProf (6579/10000 : ℝ) ≤ (595213/500000 : ℝ) := by
      unfold bProf
      have hs : Real.sqrt ((1 - ((6579/10000 : ℝ))^2)/2) ≤ (266263/500000 : ℝ) := by
        rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
      linarith
    linarith
  · simpa using le_rpow_frac (c := ((1133221:ℚ)/1000000)) (z := ((595213:ℚ)/500000)) (by norm_num) (by norm_num) (by decide +kernel)
  · have hnum : 2 * (595213/500000 : ℝ)^4 * (1133221/1000000 : ℝ) ≤ (29/4) * (397/625 : ℝ) := by norm_num
    linarith

-- segment 11: L on [6579/10000, 6777/10000]
lemma xiSeg_11 {v : ℝ} (hlo : (6579/10000 : ℝ) ≤ v) (hhi : v ≤ (6777/10000 : ℝ)) :
    2 * bProf v ^ (thrTheta - 1) ≤ (29/4 : ℝ) * v := by
  refine xiSeg_core (M := (1197663/1000000 : ℝ)) (N := (1138159/1000000 : ℝ)) (by linarith) ?_ (by norm_num) ?_ ?_
  · have hm : bProf v ≤ bProf (6777/10000 : ℝ) := bProf_monoOn (by constructor <;> linarith) (by constructor <;> norm_num) hhi
    have hc : bProf (6777/10000 : ℝ) ≤ (1197663/1000000 : ℝ) := by
      unfold bProf
      have hs : Real.sqrt ((1 - ((6777/10000 : ℝ))^2)/2) ≤ (519963/1000000 : ℝ) := by
        rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
      linarith
    linarith
  · simpa using le_rpow_frac (c := ((1138159:ℚ)/1000000)) (z := ((1197663:ℚ)/1000000)) (by norm_num) (by norm_num) (by decide +kernel)
  · have hnum : 2 * (1197663/1000000 : ℝ)^4 * (1138159/1000000 : ℝ) ≤ (29/4) * (6579/10000 : ℝ) := by norm_num
    linarith

-- segment 12: L on [6777/10000, 57/80]
lemma xiSeg_12 {v : ℝ} (hlo : (6777/10000 : ℝ) ≤ v) (hhi : v ≤ (57/80 : ℝ)) :
    2 * bProf v ^ (thrTheta - 1) ≤ (29/4 : ℝ) * v := by
  refine xiSeg_core (M := (604329/500000 : ℝ)) (N := (572823/500000 : ℝ)) (by linarith) ?_ (by norm_num) ?_ ?_
  · have hm : bProf v ≤ bProf (57/80 : ℝ) := bProf_monoOn (by constructor <;> linarith) (by constructor <;> norm_num) hhi
    have hc : bProf (57/80 : ℝ) ≤ (604329/500000 : ℝ) := by
      unfold bProf
      have hs : Real.sqrt ((1 - ((57/80 : ℝ))^2)/2) ≤ (248079/500000 : ℝ) := by
        rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
      linarith
    linarith
  · simpa using le_rpow_frac (c := ((572823:ℚ)/500000)) (z := ((604329:ℚ)/500000)) (by norm_num) (by norm_num) (by decide +kernel)
  · have hnum : 2 * (604329/500000 : ℝ)^4 * (572823/500000 : ℝ) ≤ (29/4) * (6777/10000 : ℝ) := by norm_num
    linarith

-- segment 13: L on [57/80, 7647/10000]
lemma xiSeg_13 {v : ℝ} (hlo : (57/80 : ℝ) ≤ v) (hhi : v ≤ (7647/10000 : ℝ)) :
    2 * bProf v ^ (thrTheta - 1) ≤ (29/4 : ℝ) * v := by
  refine xiSeg_core (M := (1220351/1000000 : ℝ)) (N := (288397/250000 : ℝ)) (by linarith) ?_ (by norm_num) ?_ ?_
  · have hm : bProf v ≤ bProf (7647/10000 : ℝ) := bProf_monoOn (by constructor <;> linarith) (by constructor <;> norm_num) hhi
    have hc : bProf (7647/10000 : ℝ) ≤ (1220351/1000000 : ℝ) := by
      unfold bProf
      have hs : Real.sqrt ((1 - ((7647/10000 : ℝ))^2)/2) ≤ (455651/1000000 : ℝ) := by
        rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
      linarith
    linarith
  · simpa using le_rpow_frac (c := ((288397:ℚ)/250000)) (z := ((1220351:ℚ)/1000000)) (by norm_num) (by norm_num) (by decide +kernel)
  · have hnum : 2 * (1220351/1000000 : ℝ)^4 * (288397/250000 : ℝ) ≤ (29/4) * (57/80 : ℝ) := by norm_num
    linarith

-- segment 14: X on [7647/10000, 817/1000]
lemma xiSeg_14 {v : ℝ} (hlo : (7647/10000 : ℝ) ≤ v) (hhi : v ≤ (817/1000 : ℝ)) :
    2 * bProf v ^ (thrTheta - 1) ≤ (29/4 : ℝ) * v := by
  refine xiSeg_core (M := (244949/200000 : ℝ)) (N := (578283/500000 : ℝ)) (by linarith) ?_ (by norm_num) ?_ ?_
  · have hm : bProf v ≤ Real.sqrt (3/2) := bProf_le (by linarith) (by linarith)
    have hc : Real.sqrt (3/2) ≤ (244949/200000 : ℝ) := by
      rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
    linarith
  · simpa using le_rpow_frac (c := ((578283:ℚ)/500000)) (z := ((244949:ℚ)/200000)) (by norm_num) (by norm_num) (by decide +kernel)
  · have hnum : 2 * (244949/200000 : ℝ)^4 * (578283/500000 : ℝ) ≤ (29/4) * (7647/10000 : ℝ) := by norm_num
    linarith

-- segment 15: R on [817/1000, 1]
lemma xiSeg_15 {v : ℝ} (hlo : (817/1000 : ℝ) ≤ v) (hhi : v ≤ (1 : ℝ)) :
    2 * bProf v ^ (thrTheta - 1) ≤ (29/4 : ℝ) * v := by
  refine xiSeg_core (M := (244949/200000 : ℝ)) (N := (578283/500000 : ℝ)) (by linarith) ?_ (by norm_num) ?_ ?_
  · have hm : bProf v ≤ bProf (817/1000 : ℝ) := bProf_antiOn (by constructor <;> norm_num) (by constructor <;> linarith) hlo
    have hc : bProf (817/1000 : ℝ) ≤ (244949/200000 : ℝ) := by
      unfold bProf
      have hs : Real.sqrt ((1 - ((817/1000 : ℝ))^2)/2) ≤ (81549/200000 : ℝ) := by
        rw [Real.sqrt_le_iff]; exact ⟨by norm_num, by norm_num⟩
      linarith
    linarith
  · simpa using le_rpow_frac (c := ((578283:ℚ)/500000)) (z := ((244949:ℚ)/200000)) (by norm_num) (by norm_num) (by decide +kernel)
  · have hnum : 2 * (244949/200000 : ℝ)^4 * (578283/500000 : ℝ) ≤ (29/4) * (817/1000 : ℝ) := by norm_num
    linarith

lemma xiSeg_all {v : ℝ} (h0 : (3051/10000 : ℝ) ≤ v) (h1 : v ≤ 1) :
    2 * bProf v ^ (thrTheta - 1) ≤ (29/4 : ℝ) * v := by
  rcases le_or_gt v (697/2000 : ℝ) with h | h
  · exact xiSeg_0 h0 h
  rcases le_or_gt v (973/2500 : ℝ) with h_ | h_
  · exact xiSeg_1 (le_of_lt h) h_
  rcases le_or_gt v (4273/10000 : ℝ) with h__ | h__
  · exact xiSeg_2 (le_of_lt h_) h__
  rcases le_or_gt v (463/1000 : ℝ) with h___ | h___
  · exact xiSeg_3 (le_of_lt h__) h___
  rcases le_or_gt v (993/2000 : ℝ) with h____ | h____
  · exact xiSeg_4 (le_of_lt h___) h____
  rcases le_or_gt v (5279/10000 : ℝ) with h_____ | h_____
  · exact xiSeg_5 (le_of_lt h____) h_____
  rcases le_or_gt v (2787/5000 : ℝ) with h______ | h______
  · exact xiSeg_6 (le_of_lt h_____) h______
  rcases le_or_gt v (117/200 : ℝ) with h_______ | h_______
  · exact xiSeg_7 (le_of_lt h______) h_______
  rcases le_or_gt v (6109/10000 : ℝ) with h________ | h________
  · exact xiSeg_8 (le_of_lt h_______) h________
  rcases le_or_gt v (397/625 : ℝ) with h_________ | h_________
  · exact xiSeg_9 (le_of_lt h________) h_________
  rcases le_or_gt v (6579/10000 : ℝ) with h__________ | h__________
  · exact xiSeg_10 (le_of_lt h_________) h__________
  rcases le_or_gt v (6777/10000 : ℝ) with h___________ | h___________
  · exact xiSeg_11 (le_of_lt h__________) h___________
  rcases le_or_gt v (57/80 : ℝ) with h____________ | h____________
  · exact xiSeg_12 (le_of_lt h___________) h____________
  rcases le_or_gt v (7647/10000 : ℝ) with h_____________ | h_____________
  · exact xiSeg_13 (le_of_lt h____________) h_____________
  rcases le_or_gt v (817/1000 : ℝ) with h______________ | h______________
  · exact xiSeg_14 (le_of_lt h_____________) h______________
  rcases le_or_gt v (1 : ℝ) with h_______________ | h_______________
  · exact xiSeg_15 (le_of_lt h______________) h_______________
  · exact absurd h_______________ (by linarith)


lemma seven_le_two : (29/4 : ℝ) ≤ (2:ℝ) ^ ((769:ℝ)/269) := by
  refine le_rpow_div (z := (2:ℝ)) (M := (29/4:ℝ)) (m := 769) (n := 269) (by norm_num) (by norm_num) (by norm_num) ?_
  have hnat : ((29:ℚ)/4)^269 ≤ (2:ℚ)^769 := by decide +kernel
  have hcast : ((((29:ℚ)/4)^269 : ℚ) : ℝ) ≤ ((((2:ℚ)^769 : ℚ)) : ℝ) := by exact_mod_cast hnat
  push_cast at hcast
  simpa using hcast

noncomputable def xiProf (u : ℝ) : ℝ :=
  2 * (Real.sqrt u + Real.sqrt ((1 - u) / 2)) ^ (thrTheta - 1) / Real.sqrt u

theorem xiProf_le (u : ℝ) (hu : thrT ≤ u) (hu1 : u ≤ 1) :
    xiProf u ≤ (2:ℝ) ^ ((769:ℝ)/269) := by
  have hu0 : 0 < u := lt_of_lt_of_le thrT_pos hu
  have hv0 : 0 < Real.sqrt u := Real.sqrt_pos_of_pos hu0
  have hsq : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
  have hw3051 : ((3051 : ℝ)/10000) ≤ Real.sqrt thrT := by
    rw [Real.le_sqrt' (by norm_num)]; norm_num [thrT]
  have hlo : (3051/10000 : ℝ) ≤ Real.sqrt u := le_trans hw3051 (Real.sqrt_le_sqrt hu)
  have hhi : Real.sqrt u ≤ 1 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hu1
  have hkey := xiSeg_all hlo hhi
  have hB : bProf (Real.sqrt u) = Real.sqrt u + Real.sqrt ((1-u)/2) := by
    unfold bProf; rw [hsq]
  have hseven := seven_le_two
  unfold xiProf
  rw [← hB, div_le_iff₀ hv0]
  nlinarith [hkey, hseven, hv0, Real.sqrt_nonneg u]


/-! ### The critical point algebra -/

noncomputable def Axy (x y : ℝ) : ℝ := (Real.sqrt x + Real.sqrt y) ^ (thrTheta - 1)

noncomputable def G3 (x y z : ℝ) : ℝ :=
  (Real.sqrt x + Real.sqrt y) ^ thrTheta + (Real.sqrt x + Real.sqrt z) ^ thrTheta
    + (Real.sqrt y + Real.sqrt z) ^ thrTheta

/-- The normalised sum is `2^(-769/269)` times the branch sum `G3`. -/
theorem corner_sum_eq (p : Fin 3 → ℝ) :
    (nC p 1 2) ^ ((769:ℝ)/269) + (nC p 0 2) ^ ((769:ℝ)/269)
      + (nC p 0 1) ^ ((769:ℝ)/269)
      = (2:ℝ) ^ (-((769:ℝ)/269)) * G3 (p 0) (p 1) (p 2) := by
  unfold nC G3 thrTheta
  rw [sq_half_rpow (by positivity), sq_half_rpow (by positivity), sq_half_rpow (by positivity)]
  ring

lemma rpow_theta_succ {A : ℝ} (hA : 0 < A) : A ^ thrTheta = A ^ (thrTheta - 1) * A := by
  conv_lhs => rw [show thrTheta = (thrTheta - 1) + 1 by ring]
  rw [Real.rpow_add hA, Real.rpow_one]

lemma G3_eq_lin {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    G3 x y z = Real.sqrt x * (Axy x y + Axy x z) + Real.sqrt y * (Axy x y + Axy y z)
      + Real.sqrt z * (Axy x z + Axy y z) := by
  have h1 : (0:ℝ) < Real.sqrt x + Real.sqrt y := by positivity
  have h2 : (0:ℝ) < Real.sqrt x + Real.sqrt z := by positivity
  have h3 : (0:ℝ) < Real.sqrt y + Real.sqrt z := by positivity
  unfold G3 Axy
  rw [rpow_theta_succ h1, rpow_theta_succ h2, rpow_theta_succ h3]
  ring

lemma G3_eq_mu {x y z mu : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hsum : x + y + z = 1)
    (h1 : Axy x y + Axy x z = mu * Real.sqrt x)
    (h2 : Axy x y + Axy y z = mu * Real.sqrt y)
    (h3 : Axy x z + Axy y z = mu * Real.sqrt z) :
    G3 x y z = mu := by
  rw [G3_eq_lin hx hy hz, h1, h2, h3]
  have hx2 : Real.sqrt x * Real.sqrt x = x := by rw [← sq, Real.sq_sqrt hx.le]
  have hy2 : Real.sqrt y * Real.sqrt y = y := by rw [← sq, Real.sq_sqrt hy.le]
  have hz2 : Real.sqrt z * Real.sqrt z = z := by rw [← sq, Real.sq_sqrt hz.le]
  have e1 : Real.sqrt x * (mu * Real.sqrt x) = mu * x := by
    rw [show Real.sqrt x * (mu * Real.sqrt x) = mu * (Real.sqrt x * Real.sqrt x) by ring, hx2]
  have e2 : Real.sqrt y * (mu * Real.sqrt y) = mu * y := by
    rw [show Real.sqrt y * (mu * Real.sqrt y) = mu * (Real.sqrt y * Real.sqrt y) by ring, hy2]
  have e3 : Real.sqrt z * (mu * Real.sqrt z) = mu * z := by
    rw [show Real.sqrt z * (mu * Real.sqrt z) = mu * (Real.sqrt z * Real.sqrt z) by ring, hz2]
  rw [e1, e2, e3]
  have hm : mu * x + mu * y + mu * z = mu * (x + y + z) := by ring
  rw [hm, hsum, mul_one]

lemma no_three_roots {S mu p q r : ℝ} (hpq : p < q) (hqr : q < r)
    (hu : 0 < (S + p)/2) (hw : 0 < (S + r)/2)
    (hp : ((S+p)/2) ^ (thrTheta-1) = mu * p / 2)
    (hq : ((S+q)/2) ^ (thrTheta-1) = mu * q / 2)
    (hr : ((S+r)/2) ^ (thrTheta-1) = mu * r / 2) : False := by
  have hθ : 1 < thrTheta - 1 := by unfold thrTheta; norm_num
  have huv : (S+p)/2 < (S+q)/2 := by linarith
  have hvw : (S+q)/2 < (S+r)/2 := by linarith
  have hslope := (strictConvexOn_rpow hθ).slope_strict_mono_adjacent
    (x := (S+p)/2) (y := (S+q)/2) (z := (S+r)/2)
    (Set.mem_Ici.mpr hu.le) (Set.mem_Ici.mpr hw.le) huv hvw
  have hs1 : (((S+q)/2) ^ (thrTheta-1) - ((S+p)/2) ^ (thrTheta-1)) / ((S+q)/2 - (S+p)/2) = mu := by
    rw [hp, hq, div_eq_iff (by linarith : (S+q)/2 - (S+p)/2 ≠ 0)]
    ring
  have hs2 : (((S+r)/2) ^ (thrTheta-1) - ((S+q)/2) ^ (thrTheta-1)) / ((S+r)/2 - (S+q)/2) = mu := by
    rw [hq, hr, div_eq_iff (by linarith : (S+r)/2 - (S+q)/2 ≠ 0)]
    ring
  rw [hs1, hs2] at hslope
  exact lt_irrefl mu hslope

lemma two_equal {a b c P Q R mu : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hP : P = (a + b) ^ (thrTheta - 1)) (hQ : Q = (a + c) ^ (thrTheta - 1))
    (hR : R = (b + c) ^ (thrTheta - 1))
    (h1 : P + Q = mu * a) (h2 : Q + R = mu * c) (h3 : P + R = mu * b) :
    a = c ∨ b = c ∨ a = b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hac, hbc, hab⟩ := hcon
  have hP2 : 2*P = mu*(a+b-c) := by linarith [h1, h2, h3]
  have hQ2 : 2*Q = mu*(a+c-b) := by linarith [h1, h2, h3]
  have hR2 : 2*R = mu*(b+c-a) := by linarith [h1, h2, h3]
  have eα : ((a+b+c + (a+b-c))/2) ^ (thrTheta-1) = mu * (a+b-c)/2 := by
    rw [show (a+b+c + (a+b-c))/2 = a+b by ring, ← hP]; linarith
  have eβ : ((a+b+c + (b+c-a))/2) ^ (thrTheta-1) = mu * (b+c-a)/2 := by
    rw [show (a+b+c + (b+c-a))/2 = b+c by ring, ← hR]; linarith
  have eγ : ((a+b+c + (a+c-b))/2) ^ (thrTheta-1) = mu * (a+c-b)/2 := by
    rw [show (a+b+c + (a+c-b))/2 = a+c by ring, ← hQ]; linarith
  have hposα : (0:ℝ) < (a+b+c + (a+b-c))/2 := by
    rw [show (a+b+c + (a+b-c))/2 = a+b by ring]; linarith
  have hposβ : (0:ℝ) < (a+b+c + (b+c-a))/2 := by
    rw [show (a+b+c + (b+c-a))/2 = b+c by ring]; linarith
  have hposγ : (0:ℝ) < (a+b+c + (a+c-b))/2 := by
    rw [show (a+b+c + (a+c-b))/2 = a+c by ring]; linarith
  have hαβ : a+b-c ≠ b+c-a := by intro h; exact hac (by linarith)
  have hαγ : a+b-c ≠ a+c-b := by intro h; exact hbc (by linarith)
  have hβγ : b+c-a ≠ a+c-b := by intro h; exact hab (by linarith)
  rcases lt_or_gt_of_ne hαβ with hab1 | hab1
  · rcases lt_or_gt_of_ne hαγ with hac1 | hac1
    · rcases lt_or_gt_of_ne hβγ with hbc1 | hbc1
      · exact no_three_roots hab1 hbc1 hposα hposγ eα eβ eγ
      · exact no_three_roots hac1 hbc1 hposα hposβ eα eγ eβ
    · exact no_three_roots hac1 hab1 hposγ hposβ eγ eα eβ
  · rcases lt_or_gt_of_ne hαγ with hac1 | hac1
    · exact no_three_roots hab1 hac1 hposβ hposγ eβ eα eγ
    · rcases lt_or_gt_of_ne hβγ with hbc1 | hbc1
      · exact no_three_roots hbc1 hac1 hposβ hposα eβ eγ eα
      · exact no_three_roots hbc1 hab1 hposγ hposα eγ eβ eα


/-- At an interior critical point the value is bounded by `2^(769/269)`. -/
lemma critical_le {x y z mu : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1)
    (h1 : Axy x y + Axy x z = mu * Real.sqrt x)
    (h2 : Axy x y + Axy y z = mu * Real.sqrt y)
    (h3 : Axy x z + Axy y z = mu * Real.sqrt z)
    (htx : thrT < x) (hty : thrT < y) (htz : thrT < z) :
    G3 x y z ≤ (2:ℝ)^((769:ℝ)/269) := by
  have hG : G3 x y z = mu := G3_eq_mu hx hy hz hsum h1 h2 h3
  have htwo := two_equal (Real.sqrt_pos_of_pos hx) (Real.sqrt_pos_of_pos hy) (Real.sqrt_pos_of_pos hz)
    (rfl : Axy x y = (Real.sqrt x + Real.sqrt y) ^ (thrTheta - 1))
    (rfl : Axy x z = (Real.sqrt x + Real.sqrt z) ^ (thrTheta - 1))
    (rfl : Axy y z = (Real.sqrt y + Real.sqrt z) ^ (thrTheta - 1)) h1 h3 h2
  rw [hG]
  rcases htwo with hxz | hyz | hxy
  · have hxz' : x = z := (Real.sqrt_inj hx.le hz.le).mp hxz
    have hPR : (Real.sqrt x + Real.sqrt y)^(thrTheta-1) = (Real.sqrt y + Real.sqrt z)^(thrTheta-1) := by
      rw [← hxz]; ring_nf
    have hmu2 : mu * Real.sqrt y = 2 * (Real.sqrt x + Real.sqrt y)^(thrTheta-1) := by
      unfold Axy at h2; linarith [h2, hPR]
    have hy1 : (1 - y)/2 = x := by linarith
    have hxi : mu = xiProf y := by
      unfold xiProf
      rw [show Real.sqrt ((1 - y)/2) = Real.sqrt x by rw [hy1],
        show Real.sqrt y + Real.sqrt x = Real.sqrt x + Real.sqrt y by ring]
      rw [eq_div_iff (Real.sqrt_pos_of_pos hy).ne', mul_comm mu (Real.sqrt y)]
      linarith [hmu2]
    rw [hxi]
    exact xiProf_le y (le_of_lt hty) (by linarith)
  · have hyz' : y = z := (Real.sqrt_inj hy.le hz.le).mp hyz
    have hPQ : (Real.sqrt x + Real.sqrt y)^(thrTheta-1) = (Real.sqrt x + Real.sqrt z)^(thrTheta-1) := by
      rw [← hyz]
    have hmu2 : mu * Real.sqrt x = 2 * (Real.sqrt x + Real.sqrt y)^(thrTheta-1) := by
      unfold Axy at h1; linarith [h1, hPQ]
    have hx1 : (1 - x)/2 = y := by linarith
    have hxi : mu = xiProf x := by
      unfold xiProf
      rw [show Real.sqrt ((1 - x)/2) = Real.sqrt y by rw [hx1]]
      rw [eq_div_iff (Real.sqrt_pos_of_pos hx).ne', mul_comm mu (Real.sqrt x)]
      linarith [hmu2]
    rw [hxi]
    exact xiProf_le x (le_of_lt htx) (by linarith)
  · have hxy' : x = y := (Real.sqrt_inj hx.le hy.le).mp hxy
    have hQR : (Real.sqrt x + Real.sqrt z)^(thrTheta-1) = (Real.sqrt y + Real.sqrt z)^(thrTheta-1) := by
      rw [hxy']
    have hmu2 : mu * Real.sqrt z = 2 * (Real.sqrt x + Real.sqrt z)^(thrTheta-1) := by
      unfold Axy at h3; linarith [h3, hQR]
    have hz1 : (1 - z)/2 = x := by linarith
    have hxi : mu = xiProf z := by
      unfold xiProf
      rw [show Real.sqrt ((1 - z)/2) = Real.sqrt x by rw [hz1],
        show Real.sqrt z + Real.sqrt x = Real.sqrt x + Real.sqrt z by ring]
      rw [eq_div_iff (Real.sqrt_pos_of_pos hz).ne', mul_comm mu (Real.sqrt z)]
      linarith [hmu2]
    rw [hxi]
    exact xiProf_le z (le_of_lt htz) (by linarith)


/-! ### Directional derivatives of `G3` and the critical equations -/

lemma hasDerivAt_sqrt_add {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => Real.sqrt (x + t)) (1 / (2 * Real.sqrt x)) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => x + t) 1 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_add x
  have h2 := (Real.hasDerivAt_sqrt (by simpa using hx.ne')).comp 0 h1
  simpa [Function.comp_def] using h2

lemma hasDerivAt_sqrt_sub {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun t : ℝ => Real.sqrt (z - t)) (-(1 / (2 * Real.sqrt z))) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => z - t) (-1) 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_sub z
  have h2 := (Real.hasDerivAt_sqrt (by simpa using hz.ne')).comp 0 h1
  simpa [Function.comp_def] using h2

lemma hasDerivAt_G3_dir1 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    HasDerivAt (fun t : ℝ => G3 (x + t) y (z - t))
      ((thrTheta/2) * ((Real.sqrt x + Real.sqrt y) ^ (thrTheta-1) / Real.sqrt x
        + (Real.sqrt x + Real.sqrt z) ^ (thrTheta-1) * (1/Real.sqrt x - 1/Real.sqrt z)
        - (Real.sqrt y + Real.sqrt z) ^ (thrTheta-1) / Real.sqrt z)) 0 := by
  have hUA := hasDerivAt_sqrt_add hx
  have hWC := hasDerivAt_sqrt_sub hz
  have hA : HasDerivAt (fun t : ℝ => Real.sqrt (x + t) + Real.sqrt y) (1/(2*Real.sqrt x)) 0 := by
    simpa using hUA.add_const (Real.sqrt y)
  have hW : HasDerivAt (fun t : ℝ => Real.sqrt (z - t) + Real.sqrt y) (-(1/(2*Real.sqrt z))) 0 := by
    simpa using hWC.add_const (Real.sqrt y)
  have hB : HasDerivAt (fun t : ℝ => Real.sqrt (x + t) + Real.sqrt (z - t))
      (1/(2*Real.sqrt x) + -(1/(2*Real.sqrt z))) 0 := hUA.add hWC
  have hpA : (0:ℝ) < Real.sqrt (x + 0) + Real.sqrt y := by positivity
  have hpB : (0:ℝ) < Real.sqrt (x + 0) + Real.sqrt (z - 0) := by positivity
  have hpW : (0:ℝ) < Real.sqrt (z - 0) + Real.sqrt y := by positivity
  have h1 := (Real.hasDerivAt_rpow_const (p := thrTheta) (Or.inl hpA.ne')).comp 0 hA
  have h2 := (Real.hasDerivAt_rpow_const (p := thrTheta) (Or.inl hpB.ne')).comp 0 hB
  have h3 := (Real.hasDerivAt_rpow_const (p := thrTheta) (Or.inl hpW.ne')).comp 0 hW
  have hsum := (h1.add h2).add h3
  have hsum' : HasDerivAt (fun t : ℝ => (Real.sqrt (x + t) + Real.sqrt y) ^ thrTheta
      + (Real.sqrt (x + t) + Real.sqrt (z - t)) ^ thrTheta
      + (Real.sqrt y + Real.sqrt (z - t)) ^ thrTheta)
      (thrTheta * (Real.sqrt (x + 0) + Real.sqrt y) ^ (thrTheta - 1) * (1 / (2 * Real.sqrt x))
        + thrTheta * (Real.sqrt (x + 0) + Real.sqrt (z - 0)) ^ (thrTheta - 1)
          * (1 / (2 * Real.sqrt x) + -(1 / (2 * Real.sqrt z)))
        + thrTheta * (Real.sqrt (z - 0) + Real.sqrt y) ^ (thrTheta - 1) * -(1 / (2 * Real.sqrt z))) 0 := by
    refine HasDerivAt.congr_of_eventuallyEq hsum ?_
    filter_upwards with t
    simp only [Function.comp_apply, Pi.add_apply]
    ring_nf
  have hfun : (fun t : ℝ => (Real.sqrt (x + t) + Real.sqrt y) ^ thrTheta
      + (Real.sqrt (x + t) + Real.sqrt (z - t)) ^ thrTheta
      + (Real.sqrt y + Real.sqrt (z - t)) ^ thrTheta)
      = (fun t : ℝ => G3 (x + t) y (z - t)) := by
    funext t; unfold G3; ring
  rw [← hfun]
  convert hsum' using 1
  field_simp
  ring

lemma hasDerivAt_G3_dir2 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    HasDerivAt (fun t : ℝ => G3 x (y + t) (z - t))
      ((thrTheta/2) * ((Real.sqrt x + Real.sqrt y) ^ (thrTheta-1) / Real.sqrt y
        - (Real.sqrt x + Real.sqrt z) ^ (thrTheta-1) / Real.sqrt z
        + (Real.sqrt y + Real.sqrt z) ^ (thrTheta-1) * (1/Real.sqrt y - 1/Real.sqrt z))) 0 := by
  have hUA := hasDerivAt_sqrt_add hy
  have hWC := hasDerivAt_sqrt_sub hz
  have hA : HasDerivAt (fun t : ℝ => Real.sqrt (y + t) + Real.sqrt x) (1/(2*Real.sqrt y)) 0 := by
    simpa using hUA.add_const (Real.sqrt x)
  have hW : HasDerivAt (fun t : ℝ => Real.sqrt (z - t) + Real.sqrt x) (-(1/(2*Real.sqrt z))) 0 := by
    simpa using hWC.add_const (Real.sqrt x)
  have hB : HasDerivAt (fun t : ℝ => Real.sqrt (y + t) + Real.sqrt (z - t))
      (1/(2*Real.sqrt y) + -(1/(2*Real.sqrt z))) 0 := hUA.add hWC
  have hpA : (0:ℝ) < Real.sqrt (y + 0) + Real.sqrt x := by positivity
  have hpB : (0:ℝ) < Real.sqrt (y + 0) + Real.sqrt (z - 0) := by positivity
  have hpW : (0:ℝ) < Real.sqrt (z - 0) + Real.sqrt x := by positivity
  have h1 := (Real.hasDerivAt_rpow_const (p := thrTheta) (Or.inl hpA.ne')).comp 0 hA
  have h2 := (Real.hasDerivAt_rpow_const (p := thrTheta) (Or.inl hpB.ne')).comp 0 hB
  have h3 := (Real.hasDerivAt_rpow_const (p := thrTheta) (Or.inl hpW.ne')).comp 0 hW
  have hsum := (h1.add h2).add h3
  have hsum' : HasDerivAt (fun t : ℝ => (Real.sqrt (y + t) + Real.sqrt x) ^ thrTheta
      + (Real.sqrt (z - t) + Real.sqrt x) ^ thrTheta
      + (Real.sqrt (y + t) + Real.sqrt (z - t)) ^ thrTheta)
      (thrTheta * (Real.sqrt (y + 0) + Real.sqrt x) ^ (thrTheta - 1) * (1 / (2 * Real.sqrt y))
        + thrTheta * (Real.sqrt (z - 0) + Real.sqrt x) ^ (thrTheta - 1) * -(1 / (2 * Real.sqrt z))
        + thrTheta * (Real.sqrt (y + 0) + Real.sqrt (z - 0)) ^ (thrTheta - 1)
          * (1 / (2 * Real.sqrt y) + -(1 / (2 * Real.sqrt z)))) 0 := by
    refine HasDerivAt.congr_of_eventuallyEq ((h1.add h3).add h2) ?_
    filter_upwards with t
    simp only [Function.comp_apply, Pi.add_apply]
  have hfun : (fun t : ℝ => (Real.sqrt (y + t) + Real.sqrt x) ^ thrTheta
      + (Real.sqrt (z - t) + Real.sqrt x) ^ thrTheta
      + (Real.sqrt (y + t) + Real.sqrt (z - t)) ^ thrTheta)
      = (fun t : ℝ => G3 x (y + t) (z - t)) := by
    funext t; unfold G3; ring
  rw [← hfun]
  convert hsum' using 1
  field_simp
  ring


lemma critical_of_localmax {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hloc1 : IsLocalMax (fun t : ℝ => G3 (x + t) y (z - t)) 0)
    (hloc2 : IsLocalMax (fun t : ℝ => G3 x (y + t) (z - t)) 0) :
    ∃ mu, (Axy x y + Axy x z = mu * Real.sqrt x) ∧ (Axy x y + Axy y z = mu * Real.sqrt y)
      ∧ (Axy x z + Axy y z = mu * Real.sqrt z) := by
  have hd1 := hloc1.hasDerivAt_eq_zero (hasDerivAt_G3_dir1 hx hy hz)
  have hd2 := hloc2.hasDerivAt_eq_zero (hasDerivAt_G3_dir2 hx hy hz)
  have hth : (thrTheta/2) ≠ 0 := by unfold thrTheta; norm_num
  have e1 : (Real.sqrt x + Real.sqrt y) ^ (thrTheta-1) / Real.sqrt x
      + (Real.sqrt x + Real.sqrt z) ^ (thrTheta-1) * (1/Real.sqrt x - 1/Real.sqrt z)
      - (Real.sqrt y + Real.sqrt z) ^ (thrTheta-1) / Real.sqrt z = 0 := by
    rcases mul_eq_zero.mp hd1 with h | h
    · exact absurd h hth
    · exact h
  have e2 : (Real.sqrt x + Real.sqrt y) ^ (thrTheta-1) / Real.sqrt y
      - (Real.sqrt x + Real.sqrt z) ^ (thrTheta-1) / Real.sqrt z
      + (Real.sqrt y + Real.sqrt z) ^ (thrTheta-1) * (1/Real.sqrt y - 1/Real.sqrt z) = 0 := by
    rcases mul_eq_zero.mp hd2 with h | h
    · exact absurd h hth
    · exact h
  refine ⟨((Real.sqrt x + Real.sqrt z) ^ (thrTheta-1) + (Real.sqrt y + Real.sqrt z) ^ (thrTheta-1)) / Real.sqrt z, ?_, ?_, ?_⟩
  · unfold Axy
    have hx0 := (Real.sqrt_pos_of_pos hx).ne'
    have hz0 := (Real.sqrt_pos_of_pos hz).ne'
    field_simp at e1 ⊢
    ring_nf at e1 ⊢
    linarith [e1]
  · unfold Axy
    have hy0 := (Real.sqrt_pos_of_pos hy).ne'
    have hz0 := (Real.sqrt_pos_of_pos hz).ne'
    field_simp at e2 ⊢
    ring_nf at e2 ⊢
    linarith [e2]
  · unfold Axy
    have hz0 := (Real.sqrt_pos_of_pos hz).ne'
    rw [div_mul_cancel₀ _ hz0]


/-! ### The corner maximum principle, unconditionally -/

lemma edge_pair_le {a b : ℝ} (ha : thrT ≤ a) (hb : thrT ≤ b) (hab : a + b = thrS) :
    ((Real.sqrt a + Real.sqrt b) ^ 2 / 2) ^ ((769:ℝ)/269)
      + ((Real.sqrt a + Real.sqrt thrT) ^ 2 / 2) ^ ((769:ℝ)/269)
      + ((Real.sqrt b + Real.sqrt thrT) ^ 2 / 2) ^ ((769:ℝ)/269) ≤ 1 :=
  le_trans (edge_one_dim edgePsi ha hb hab) cornerBound

theorem cornerMaxOne (p : Fin 3 → ℝ) (hsum : ∑ i, p i = 1) (ht : ∀ i, thrT ≤ p i) :
    (nC p 1 2) ^ ((769:ℝ)/269) + (nC p 0 2) ^ ((769:ℝ)/269)
      + (nC p 0 1) ^ ((769:ℝ)/269) ≤ 1 := by
  classical
  set S : Set (Fin 3 → ℝ) := {q | (∀ i, thrT ≤ q i) ∧ ∑ i, q i = 1} with hS
  have hcont : ContinuousOn (fun q : Fin 3 → ℝ => (nC q 1 2) ^ ((769:ℝ)/269)
      + (nC q 0 2) ^ ((769:ℝ)/269) + (nC q 0 1) ^ ((769:ℝ)/269)) S := by
    refine ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_
    · exact (by unfold nC; fun_prop : Continuous (fun q : Fin 3 → ℝ => nC q 1 2)).continuousOn.rpow_const
        (fun q _ => Or.inr (by norm_num))
    · exact (by unfold nC; fun_prop : Continuous (fun q : Fin 3 → ℝ => nC q 0 2)).continuousOn.rpow_const
        (fun q _ => Or.inr (by norm_num))
    · exact (by unfold nC; fun_prop : Continuous (fun q : Fin 3 → ℝ => nC q 0 1)).continuousOn.rpow_const
        (fun q _ => Or.inr (by norm_num))
  have hSclosed : IsClosed S := by
    rw [hS]
    have h1 : IsClosed {q : Fin 3 → ℝ | ∀ i, thrT ≤ q i} := by
      rw [show {q : Fin 3 → ℝ | ∀ i, thrT ≤ q i} = ⋂ i, {q | thrT ≤ q i} by
        ext q; simp]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    exact h1.inter (isClosed_eq (by fun_prop) continuous_const)
  have hK : IsCompact (Set.univ.pi (fun _ : Fin 3 => Set.Icc thrT 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub : S ⊆ Set.univ.pi (fun _ : Fin 3 => Set.Icc thrT 1) := by
    rw [hS]
    intro q hq
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc]
    intro i _
    refine ⟨hq.1 i, ?_⟩
    have h1 : q i ≤ ∑ j, q j :=
      Finset.single_le_sum (f := q) (fun j _ => le_trans thrT_pos.le (hq.1 j)) (Finset.mem_univ i)
    rw [hq.2] at h1; exact h1
  have hSne : S.Nonempty := ⟨p, by rw [hS]; exact ⟨ht, hsum⟩⟩
  obtain ⟨q, hqS, hmax⟩ := (hK.of_isClosed_subset hSclosed hsub).exists_isMaxOn hSne hcont
  have hpq : (nC p 1 2) ^ ((769:ℝ)/269) + (nC p 0 2) ^ ((769:ℝ)/269)
      + (nC p 0 1) ^ ((769:ℝ)/269)
      ≤ (nC q 1 2) ^ ((769:ℝ)/269) + (nC q 0 2) ^ ((769:ℝ)/269)
        + (nC q 0 1) ^ ((769:ℝ)/269) := hmax (by rw [hS]; exact ⟨ht, hsum⟩)
  have hq0 : 0 < q 0 := lt_of_lt_of_le thrT_pos (hqS.1 0)
  have hq1 : 0 < q 1 := lt_of_lt_of_le thrT_pos (hqS.1 1)
  have hq2 : 0 < q 2 := lt_of_lt_of_le thrT_pos (hqS.1 2)
  have hqsum : q 0 + q 1 + q 2 = 1 := by
    have := hqS.2; rw [Fin.sum_univ_three] at this; exact this
  by_cases hcase : ∃ i, q i = thrT
  · obtain ⟨i, hi⟩ := hcase
    have key : (nC q 1 2) ^ ((769:ℝ)/269) + (nC q 0 2) ^ ((769:ℝ)/269)
        + (nC q 0 1) ^ ((769:ℝ)/269) ≤ 1 := by
      fin_cases i
      · have hk : q 0 = thrT := hi
        have hpair : q 1 + q 2 = thrS := by rw [hk] at hqsum; linarith [thrS_eq]
        have h := edge_pair_le (hqS.1 1) (hqS.1 2) hpair
        have eB : ((Real.sqrt thrT + Real.sqrt (q 2))^2/2)^((769:ℝ)/269)
            = ((Real.sqrt (q 2) + Real.sqrt thrT)^2/2)^((769:ℝ)/269) := by rw [add_comm (Real.sqrt thrT)]
        have eC : ((Real.sqrt thrT + Real.sqrt (q 1))^2/2)^((769:ℝ)/269)
            = ((Real.sqrt (q 1) + Real.sqrt thrT)^2/2)^((769:ℝ)/269) := by rw [add_comm (Real.sqrt thrT)]
        simp only [nC, hk]
        rw [eB, eC]
        linarith [h]
      · have hk : q 1 = thrT := hi
        have hpair : q 2 + q 0 = thrS := by rw [hk] at hqsum; linarith [thrS_eq]
        have h := edge_pair_le (hqS.1 2) (hqS.1 0) hpair
        have eB : ((Real.sqrt thrT + Real.sqrt (q 2))^2/2)^((769:ℝ)/269)
            = ((Real.sqrt (q 2) + Real.sqrt thrT)^2/2)^((769:ℝ)/269) := by rw [add_comm (Real.sqrt thrT)]
        have eC : ((Real.sqrt (q 0) + Real.sqrt (q 2))^2/2)^((769:ℝ)/269)
            = ((Real.sqrt (q 2) + Real.sqrt (q 0))^2/2)^((769:ℝ)/269) := by rw [add_comm (Real.sqrt (q 0))]
        simp only [nC, hk]
        rw [eB, eC]
        linarith [h]
      · have hk : q 2 = thrT := hi
        have hpair : q 0 + q 1 = thrS := by rw [hk] at hqsum; linarith [thrS_eq]
        have h := edge_pair_le (hqS.1 0) (hqS.1 1) hpair
        simp only [nC, hk]
        linarith [h]
    linarith
  · push Not at hcase
    have hgt0 : thrT < q 0 := lt_of_le_of_ne (hqS.1 0) (Ne.symm (hcase 0))
    have hgt1 : thrT < q 1 := lt_of_le_of_ne (hqS.1 1) (Ne.symm (hcase 1))
    have hgt2 : thrT < q 2 := lt_of_le_of_ne (hqS.1 2) (Ne.symm (hcase 2))
    have hqpos : (0:ℝ) < (2:ℝ) ^ (-((769:ℝ)/269)) := Real.rpow_pos_of_pos (by norm_num) _
    have slice1 : ∀ t : ℝ, thrT ≤ q 0 + t → thrT ≤ q 2 - t →
        G3 (q 0 + t) (q 1) (q 2 - t) ≤ G3 (q 0) (q 1) (q 2) := by
      intro t h1 h2
      have hmem : (![q 0 + t, q 1, q 2 - t] : Fin 3 → ℝ) ∈ S := by
        rw [hS]
        refine ⟨?_, ?_⟩
        · intro j
          fin_cases j
          · simpa using h1
          · simpa using hqS.1 1
          · simpa using h2
        · rw [Fin.sum_univ_three]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.tail_cons]
          linarith [hqsum]
      have hle := hmax hmem
      simp only [Set.mem_ofPred_eq] at hle
      rw [corner_sum_eq, corner_sum_eq] at hle
      have e0 : (![q 0 + t, q 1, q 2 - t] : Fin 3 → ℝ) 0 = q 0 + t := rfl
      have e1 : (![q 0 + t, q 1, q 2 - t] : Fin 3 → ℝ) 1 = q 1 := rfl
      have e2 : (![q 0 + t, q 1, q 2 - t] : Fin 3 → ℝ) 2 = q 2 - t := rfl
      rw [e0, e1, e2] at hle
      exact le_of_mul_le_mul_left hle hqpos
    have slice2 : ∀ t : ℝ, thrT ≤ q 1 + t → thrT ≤ q 2 - t →
        G3 (q 0) (q 1 + t) (q 2 - t) ≤ G3 (q 0) (q 1) (q 2) := by
      intro t h1 h2
      have hmem : (![q 0, q 1 + t, q 2 - t] : Fin 3 → ℝ) ∈ S := by
        rw [hS]
        refine ⟨?_, ?_⟩
        · intro j
          fin_cases j
          · simpa using hqS.1 0
          · simpa using h1
          · simpa using h2
        · rw [Fin.sum_univ_three]
          simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
            Matrix.cons_val_two, Matrix.tail_cons]
          linarith [hqsum]
      have hle := hmax hmem
      simp only [Set.mem_ofPred_eq] at hle
      rw [corner_sum_eq, corner_sum_eq] at hle
      have e0 : (![q 0, q 1 + t, q 2 - t] : Fin 3 → ℝ) 0 = q 0 := rfl
      have e1 : (![q 0, q 1 + t, q 2 - t] : Fin 3 → ℝ) 1 = q 1 + t := rfl
      have e2 : (![q 0, q 1 + t, q 2 - t] : Fin 3 → ℝ) 2 = q 2 - t := rfl
      rw [e0, e1, e2] at hle
      exact le_of_mul_le_mul_left hle hqpos
    have ev1 : ∀ᶠ t : ℝ in 𝓝 0, thrT ≤ q 0 + t := by
      have h := eventually_gt_nhds (a := (0:ℝ)) (b := thrT - q 0) (show thrT - q 0 < 0 by linarith)
      filter_upwards [h] with t ht'; linarith
    have ev2 : ∀ᶠ t : ℝ in 𝓝 0, thrT ≤ q 2 - t := by
      have h := eventually_lt_nhds (a := (0:ℝ)) (b := q 2 - thrT) (show (0:ℝ) < q 2 - thrT by linarith)
      filter_upwards [h] with t ht'; linarith
    have ev3 : ∀ᶠ t : ℝ in 𝓝 0, thrT ≤ q 1 + t := by
      have h := eventually_gt_nhds (a := (0:ℝ)) (b := thrT - q 1) (show thrT - q 1 < 0 by linarith)
      filter_upwards [h] with t ht'; linarith
    have hloc1 : IsLocalMax (fun t : ℝ => G3 (q 0 + t) (q 1) (q 2 - t)) 0 := by
      rw [IsLocalMax]
      filter_upwards [ev1, ev2] with t h1 h2
      simpa using slice1 t h1 h2
    have hloc2 : IsLocalMax (fun t : ℝ => G3 (q 0) (q 1 + t) (q 2 - t)) 0 := by
      rw [IsLocalMax]
      filter_upwards [ev3, ev2] with t h1 h2
      simpa using slice2 t h1 h2
    obtain ⟨mu, hm1, hm2, hm3⟩ := critical_of_localmax hq0 hq1 hq2 hloc1 hloc2
    have hbound := critical_le hq0 hq1 hq2 hqsum hm1 hm2 hm3 hgt0 hgt1 hgt2
    have hfin : (nC q 1 2) ^ ((769:ℝ)/269) + (nC q 0 2) ^ ((769:ℝ)/269)
        + (nC q 0 1) ^ ((769:ℝ)/269) ≤ 1 := by
      rw [corner_sum_eq]
      calc (2:ℝ) ^ (-((769:ℝ)/269)) * G3 (q 0) (q 1) (q 2)
          ≤ (2:ℝ) ^ (-((769:ℝ)/269)) * (2:ℝ) ^ ((769:ℝ)/269) :=
            mul_le_mul_of_nonneg_left hbound hqpos.le
        _ = 1 := by
            rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
            norm_num
    linarith


/-- The sharp two-variable inequality `CaseIIBound`, unconditionally. -/
theorem caseIIBound_direct : CaseIIBound := by
  intro p hp0 hp1 ht
  exact cornerMaxOne p hp1 ht

/-- **Theorem 3** (the paper's `chi3`): the monotone complexity exponent of
`U_k` is at least `0.769` for `k = 3`.  Unconditional. -/
theorem theorem3 : IsMonotoneGraphExponent 3 ((769 : ℝ) / 1000) :=
  theorem3_of_caseII caseIIBound_direct

end

end T3

end UnateLin
