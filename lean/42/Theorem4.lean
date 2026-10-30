/-
# Theorem 4 of (Sergeev, Math. Notes 115 (3), 2024), self-contained

This file proves Theorem 4 of I. S. Sergeev, *On the additive complexity of some integer
sequences*:

`Theorem 4`. Let `B ⊂ ℕ` be a sum-free `B_k`-set with `2 ≤ k`. Then
`L(B) [+ 1] ≥ |B| + (1/5) |B|^{k/(k+1)}`.

The file is self-contained: it only imports `Mathlib` and reproduces, in addition to the proof of
Theorem 4, the two results that the proof relies on:

* **Lemma 3** (`AchainsComplexity.lemma3_graph`, `AchainsComplexity.lemma3_graph'`):
  `ex(n, 𝒞_{2k}) ≤ n^{1+1/k} + 2n` — the extremal bound for graphs without short even cycles;
* **Statement 1** (`BkSet.statement1`): if `B ⊆ A + A` is a `B_k`-set, then
  `|B| ≤ |A|^{1+1/k} + 3|A|`.

The notions of a `B_k`-set (`BkSet.IsBkSeq`), of the Minkowski sum (`BkSet.minkowskiSum`) and of a
pseudograph (`BkSet.Pseudograph`) are those already used in the workspace for Statement 1.

Because these results are reproduced here, the file re-declares names such as
`AchainsComplexity.lemma3_graph` and `BkSet.statement1`: it must not be imported together with the
modules `AchainsComplexity` or `H-is-Bk-set`, and it needs neither (its only import is `Mathlib`).

## The chain model and the precise form of the conclusion

`L(B)` is modeled by `Theorem4.setL B`: the minimal length of an ordinary addition chain
`1, y 0, …, y (L-1)` (each entry a sum of two earlier values, where `1` counts as available)
computing every element of `B` (`Theorem4.AddChain.Computes`); the length counts the additions, not
the initial `1`. This is the convention of the paper, under which e.g. `L({1, 3}) = 2`.

Two small corrections to the literal reading of the paper are needed:

* the counting argument produces the initial `1` as an element of the chain, hence only
  `L(B) + 1 ≥ |B| + (1/5) |B|^{k/(k+1)}` is proved (the paper writes `L(B) ≥ …`). Equivalently, the
  bound holds for the complexity that also counts the initial `1`. 

* no hypothesis on `1` is needed, but `1` must be removed from the *counted* set: every `b ∈ B` is
  analysed through the chain step that produces it, and `b = 1` is produced by no step.  Since `1` is
  available for free, the sharp form of the conclusion is
  `|B| + (1/5) |B \ {1}|^{k/(k+1)} ≤ L(B) + 1`; for `1 ∉ B` this is exactly the paper's inequality,
  and with no condition at all it can also be written as
  `|B| + (1/5) (|B| - 1)^{k/(k+1)} ≤ L(B) + 1`.

## Main results

* `Theorem4.theorem4` : `|B| + (1/5)|B \ {1}|^{k/(k+1)} ≤ L(B) + 1` for a sum-free `B_k`-set `B` with
  `2 ≤ k` (any `B`, in particular with `1 ∈ B`); `Theorem4.theorem4_chain` is the same bound for an
  arbitrary chain computing `B`;
* `Theorem4.theorem4_of_notMem_one` (and `Theorem4.theorem4_chain_of_notMem_one`) : the paper's
  form `|B| + (1/5)|B|^{k/(k+1)} ≤ L(B) + 1` when `1 ∉ B`; `Theorem4.theorem4_six_fifths` (and
  `Theorem4.theorem4_chain_six_fifths`) : `|B| + (1/5)|B|^{k/(k+1)} ≤ L(B) + 6/5` with no condition
  on `1`;
* `BkSet.statement1` (Statement 1) and `AchainsComplexity.lemma3_graph` (Lemma 3), reproduced, are
  the two inputs of the proof;
* `Theorem4.diff_unique` : the uniqueness of the differences inside a `B_2`-set (footnote 11);
* `Theorem4.card_le` : the counting step `|B \ {1}| ≤ 5 |A ∪ C|^{1+1/k}`.
-/
import Mathlib


set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 2000000
noncomputable section
namespace AchainsComplexity
open SimpleGraph Finset
open scoped Classical

/-! ## Graphs without short even cycles -/

/-- `HasNoEvenCycleUpTo G k` says that `G` has no cycle of length `2 * m` with `1 ≤ m ≤ k`, i.e.
that `G` contains no subgraph isomorphic to one of `C₄, C₆, …, C_{2k}` (a cycle of length `2` is
impossible in a simple graph, so the lower bound `1 ≤ m` costs nothing; it matters only for
`k = 1`, where the family `𝒞₂ = {C₄}` must not be empty). -/
def HasNoEvenCycleUpTo {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (m : ℕ), 1 ≤ m → m ≤ k → ∀ (v : V) (c : G.Walk v v), c.IsCycle → c.length ≠ 2 * m

namespace HasNoEvenCycleUpTo

variable {V : Type*} {G : SimpleGraph V} {k : ℕ}

protected theorem mono (h : HasNoEvenCycleUpTo G k) {k' : ℕ} (hk : k' ≤ k) :
    HasNoEvenCycleUpTo G k' :=
  fun m h2 hk' => h m h2 (hk'.trans hk)

protected theorem bot (k : ℕ) : HasNoEvenCycleUpTo (⊥ : SimpleGraph V) k := by
  intro m _ _ v c hc _
  have hpos : 0 < c.length := by
    rw [← Walk.not_nil_iff_lt_length]
    exact hc.not_nil
  have hadj : (⊥ : SimpleGraph V).Adj (c.getVert 0) (c.getVert 1) := c.adj_getVert_succ hpos
  simp at hadj

protected theorem mono_graph (h : HasNoEvenCycleUpTo G k) {H : SimpleGraph V} (hHG : H ≤ G) :
    HasNoEvenCycleUpTo H k := by
  intro m h2 hk v c hc hlen
  exact h m h2 hk v (c.mapLe hHG) (hc.mapLe hHG) (by rw [Walk.length_mapLe, hlen])

protected theorem induce (h : HasNoEvenCycleUpTo G k) (s : Set V) :
    HasNoEvenCycleUpTo (G.induce s) k := by
  intro m h2 hk v c hc hlen
  let φ : G.induce s →g G :=
    { toFun := fun x => (x : V), map_rel' := fun {_ _} h => h }
  refine h m h2 hk (v : V) (c.map φ) ?_ ?_
  · rw [Walk.isCycle_map_iff_of_injective]
    · exact hc
    · exact Subtype.val_injective
  · rw [Walk.length_map, hlen]

end HasNoEvenCycleUpTo

/-! ## The extremal number `ex(n, 𝒞_{2k})` -/

/-- `ex(n, 𝒞_{2k})`: the extremal number of the paper, i.e. the maximum number of edges of a graph
on `n` vertices having no cycle of length `2 * m` with `1 ≤ m ≤ k` (in other words, no subgraph
isomorphic to one of `C₄, C₆, …, C_{2k}`). Taking the supremum over all graphs on `Fin n` is the
same as taking it over all isomorphism classes of `n`-vertex graphs. -/
noncomputable def exEvenCycles (n k : ℕ) : ℕ :=
  (Finset.univ : Finset (SimpleGraph (Fin n))).sup
    (fun G => if HasNoEvenCycleUpTo G k then #G.edgeFinset else 0)

theorem exEvenCycles_le {n k m : ℕ}
    (h : ∀ G : SimpleGraph (Fin n), HasNoEvenCycleUpTo G k → #G.edgeFinset ≤ m) :
    exEvenCycles n k ≤ m := by
  rw [exEvenCycles, Finset.sup_le_iff]
  intro G _
  split_ifs with hG
  · exact h G hG
  · exact Nat.zero_le _

/-! ## Elementary facts about walks in a `Type*`-valued graph -/

section WalkBasics

variable {G : SimpleGraph V} {v w a b z x : V}

/-- The support of a walk is its start followed by its tail. -/
lemma support_eq_start_cons_tail (p : G.Walk v w) : p.support = v :: p.support.tail := by
  cases p <;> rfl

/-- A vertex of the tail of the support of a path is reached at a positive time. -/
lemma mem_support_tail_iff {p : G.Walk v w} (hp : p.IsPath) {x : V} :
    x ∈ p.support.tail ↔ ∃ j, 1 ≤ j ∧ j ≤ p.length ∧ p.getVert j = x := by
  constructor
  · intro hx
    obtain ⟨j, hj, hjl⟩ := p.mem_support_iff_exists_getVert.mp (List.mem_of_mem_tail hx)
    refine ⟨j, ?_, hjl, hj⟩
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · exfalso
      rw [h0, Walk.getVert_zero] at hj
      have hnd := hp.support_nodup
      rw [support_eq_start_cons_tail] at hnd
      rw [List.nodup_cons] at hnd
      exact hnd.1 (hj.symm ▸ hx)
    · exact hpos
  · rintro ⟨j, hj1, hjl, rfl⟩
    have hmem : p.getVert j ∈ p.support := p.getVert_mem_support j
    rw [Walk.mem_support_iff p] at hmem
    rcases hmem with heq | h
    · exact absurd (hp.getVert_eq_start_iff hjl |>.mp heq) (by omega)
    · exact h

end WalkBasics

/-! ## Geodesics and distances -/

section Geodesic

variable {G : SimpleGraph V} {v w a b z x : V}

/-- On a walk of length equal to the distance, the distance from the start of the `t`-th vertex
equals `t`. -/
theorem dist_getVert_of_geodesic {P : G.Walk v w} (hP : P.length = G.dist v w) {t : ℕ}
    (ht : t ≤ P.length) : G.dist v (P.getVert t) = t := by
  refine le_antisymm ?_ ?_
  · have h := dist_le (P.take t)
    rwa [Walk.take_length, Nat.min_eq_left ht] at h
  · by_contra hlt
    push Not at hlt
    have hreach : G.Reachable v (P.getVert t) := ⟨P.take t⟩
    obtain ⟨W, hW⟩ := hreach.exists_walk_length_eq_dist
    have hlen : G.dist v w ≤ (W.append (P.drop t)).length := dist_le _
    rw [Walk.length_append, hW, Walk.drop_length] at hlen
    omega

/-- Every vertex of a geodesic is at distance at most its length. -/
lemma dist_le_of_mem_support {p : G.Walk v a} (hp : p.length = G.dist v a) {u : V}
    (hu : u ∈ p.support) : G.dist v u ≤ p.length := by
  obtain ⟨j, hj, hjl⟩ := p.mem_support_iff_exists_getVert.mp hu
  rw [← hj, dist_getVert_of_geodesic hp hjl]
  omega

/-- A vertex of a geodesic at distance equal to its length is its endpoint. -/
lemma eq_end_of_mem_support {p : G.Walk v a} (hp : p.length = G.dist v a) {u : V}
    (hu : u ∈ p.support) (he : G.dist v u = p.length) : u = a := by
  obtain ⟨j, hj, hjl⟩ := p.mem_support_iff_exists_getVert.mp hu
  have h3 := dist_getVert_of_geodesic hp hjl
  rw [hj] at h3
  have h1 : j = p.length := by omega
  rw [← hj, h1, Walk.getVert_length]

/-- In a graph with no short even cycles every geodesic of length at most `k` between two
vertices is unique. -/
theorem geodesic_unique (h : HasNoEvenCycleUpTo G k) {P Q : G.Walk v w}
    (hP : P.IsPath) (hQ : Q.IsPath) (hPd : P.length = G.dist v w) (hQd : Q.length = G.dist v w)
    (hk : G.dist v w ≤ k) : P = Q := by
  by_contra hne
  obtain ⟨u', v', P', Q', hP', hQ', hcyc⟩ := hP.exists_isCycle_of_ne hQ hne
  have h1 : P'.length = G.dist u' v' := length_eq_dist_of_subwalk hPd hP'
  have h2 : Q'.length = G.dist u' v' := length_eq_dist_of_subwalk hQd hQ'
  have hlen : (P'.append Q'.reverse).length = 2 * G.dist u' v' := by
    rw [Walk.length_append, Walk.length_reverse, h1, h2]
    ring
  have h3 : 3 ≤ (P'.append Q'.reverse).length := hcyc.isCircuit.three_le_length
  have hPl : P'.length ≤ P.length := Walk.length_le_of_isSubwalk hP'
  have hQl : Q'.length ≤ Q.length := Walk.length_le_of_isSubwalk hQ'
  refine h (G.dist u' v') ?_ ?_ u' _ hcyc hlen
  · omega
  · omega

end Geodesic

/-! ## Two branches through a common neighbour give a cycle -/

section Branches

variable {G : SimpleGraph V} {v w a b z : V}

/-- Two internally disjoint paths starting at the same vertex, whose endpoints are both adjacent to
a further vertex `w` not lying on either path, produce a cycle of length `2 * s + 2`, where `s` is
their common length. In particular the cycle has even length. -/
lemma exists_cycle_of_branches {A : G.Walk z a} {B : G.Walk z b}
    (hA : A.IsPath) (hB : B.IsPath) (hlen : A.length = B.length) (hlen0 : 1 ≤ A.length)
    (hdisj : A.support.tail.Disjoint B.support.tail)
    (ha : G.Adj a w) (hb : G.Adj b w) (hwA : w ∉ A.support) (hwB : w ∉ B.support) :
    ∃ c : G.Walk z z, c.IsCycle ∧ c.length = 2 * A.length + 2 := by
  refine ⟨(A.concat ha).append (Walk.cons hb.symm B.reverse), ?_, ?_⟩
  · refine Walk.IsPath.isCycle_append (hA.concat hwA ha) ?_ ?_ (Or.inl ?_)
    · refine (Walk.isPath_reverse_iff B).mpr hB |>.cons ?_
      simpa [Walk.support_reverse] using hwB
    · rw [Walk.support_concat, Walk.support_cons, Walk.support_reverse]
      have hAsup : A.support = z :: A.support.tail := support_eq_start_cons_tail A
      have hBsup : B.support = z :: B.support.tail := support_eq_start_cons_tail B
      have hzA : z ∉ A.support.tail := by
        have hnd := hA.support_nodup
        rw [hAsup, List.nodup_cons] at hnd
        exact hnd.1
      have hzB : z ∉ B.support.tail := by
        have hnd := hB.support_nodup
        rw [hBsup, List.nodup_cons] at hnd
        exact hnd.1
      have hwBt : w ∉ B.support.tail := by
        intro hmem
        exact hwB (by rw [hBsup]; exact List.mem_cons_of_mem z hmem)
      have hwz : w ≠ z := by
        intro heq
        exact hwB (heq ▸ Walk.start_mem_support B)
      rw [List.tail_append_of_ne_nil (Walk.support_ne_nil A), List.tail_cons, List.disjoint_left]
      intro y hy hy'
      rw [List.mem_append, List.mem_singleton] at hy
      rw [List.mem_reverse, hBsup, List.mem_cons] at hy'
      rcases hy with hy | rfl
      · rcases hy' with rfl | hy'
        · exact hzA hy
        · exact hdisj hy hy'
      · rcases hy' with heq | hy'
        · exact hwz heq
        · exact hwBt hy'
    · simp only [Walk.length_concat]
      omega
  · rw [Walk.length_append, Walk.length_concat, Walk.length_cons, Walk.length_reverse, hlen]
    omega

/-- **Two neighbours at the same distance give a short even cycle.** If `a` and `b` are two
distinct neighbours of `w`, both at distance `s0` from `v`, and `w` lies on none of the geodesics
from `v` to `a` or `b`, then a cycle of even length `2s + 2 ≤ 2 * (s0 + 1)` exists, whence a
forbidden cycle of length `2m` with `2 ≤ m ≤ k`. -/
theorem not_adj_two_of_dist {k : ℕ} (h : HasNoEvenCycleUpTo G k) {v w a b : V} {s0 : ℕ}
    (hs0 : 1 ≤ s0) (hva : G.dist v a = s0) (hvb : G.dist v b = s0) (hne : a ≠ b)
    (hk : s0 + 1 ≤ k) (ha : G.Adj a w) (hb : G.Adj b w)
    (hw : G.dist v w = s0 + 1 ∨ G.dist v w = s0 ∧ w ≠ a ∧ w ≠ b) : False := by
  classical
  obtain ⟨P, hP, hPd⟩ := (Reachable.of_dist_ne_zero (by omega : G.dist v a ≠ 0)).exists_path_of_dist
  obtain ⟨Q, hQ, hQd⟩ := (Reachable.of_dist_ne_zero (by omega : G.dist v b ≠ 0)).exists_path_of_dist
  have hPL : P.length = s0 := by rw [hPd, hva]
  have hQL : Q.length = s0 := by rw [hQd, hvb]
  -- the last index at which the two geodesics agree
  set m := Nat.findGreatest (fun j => P.getVert j = Q.getVert j) s0 with hm_def
  have hm_eq : Nat.findGreatest (fun j => P.getVert j = Q.getVert j) s0 = m := hm_def.symm
  have h0eq : (fun j => P.getVert j = Q.getVert j) 0 := by
    show P.getVert 0 = Q.getVert 0
    rw [Walk.getVert_zero, Walk.getVert_zero]
  have hmP : P.getVert m = Q.getVert m := by
    rw [hm_def]
    exact Nat.findGreatest_spec (P := fun j => P.getVert j = Q.getVert j) (Nat.zero_le s0) h0eq
  have hmle : m ≤ s0 := by
    rw [hm_def]
    exact Nat.findGreatest_le s0
  have hmmax : ∀ j, m < j → j ≤ s0 → P.getVert j ≠ Q.getVert j :=
    fun j hj hjle => (Nat.findGreatest_eq_iff.mp hm_eq).2.2 hj hjle
  have hm_lt : m < s0 := by
    rcases Nat.lt_or_ge m s0 with h' | h'
    · exact h'
    · exfalso
      have hms : m = s0 := by omega
      have h1 : P.getVert s0 = a := by rw [← hPL, Walk.getVert_length]
      have h2 : Q.getVert s0 = b := by rw [← hQL, Walk.getVert_length]
      exact hne (by rw [hms] at hmP; rw [h1, h2] at hmP; exact hmP)
  -- the two branches starting at the last common vertex
  set z := P.getVert m with hz_def
  set A : G.Walk z a := P.drop m with hA_def
  set B : G.Walk z b := (Q.drop m).copy hmP.symm rfl with hB_def
  have hApath : A.IsPath := hP.drop m
  have hBpath : B.IsPath := (Walk.isPath_copy _ _ _).mpr (hQ.drop m)
  have hAlen : A.length = s0 - m := by rw [hA_def, Walk.drop_length, hPL]
  have hBlen : B.length = s0 - m := by rw [hB_def, Walk.length_copy, Walk.drop_length, hQL]
  have hlenAB : A.length = B.length := by rw [hAlen, hBlen]
  have hdisj : A.support.tail.Disjoint B.support.tail := by
    rw [List.disjoint_left]
    intro y hy hy'
    rw [mem_support_tail_iff hApath] at hy
    rw [mem_support_tail_iff hBpath] at hy'
    obtain ⟨j, hj1, hjlen, hjy⟩ := hy
    obtain ⟨j', hj'1, hj'len, hj'y⟩ := hy'
    have key1 : P.getVert (m + j) = y := by
      rw [← Walk.drop_getVert (p := P) m j]
      exact hjy
    have key2 : Q.getVert (m + j') = y := by
      rw [← Walk.drop_getVert (p := Q) m j']
      rw [hB_def] at hj'y
      simpa using hj'y
    have hdj : G.dist v (P.getVert (m + j)) = m + j :=
      dist_getVert_of_geodesic hPd (by omega)
    have hdj' : G.dist v (Q.getVert (m + j')) = m + j' :=
      dist_getVert_of_geodesic hQd (by omega)
    have heq : m + j = m + j' := by rw [← hdj, ← hdj', key1, key2]
    have hjeq : j = j' := by omega
    have hcontr : P.getVert (m + j) = Q.getVert (m + j) := by
      have hkey2 : Q.getVert (m + j) = y := by
        rw [hjeq]
        exact key2
      exact key1.trans hkey2.symm
    exact hmmax (m + j) (by omega) (by omega) hcontr
  have hwA : w ∉ A.support := by
    intro hmem
    have huP : w ∈ P.support :=
      (Walk.isSubwalk_drop P m).support_subset (show w ∈ (P.drop m).support from hmem)
    rcases hw with h2 | ⟨h2, h3, h4⟩
    · have := dist_le_of_mem_support hPd huP
      omega
    · exact h3 (eq_end_of_mem_support hPd huP (by omega))
  have hwB : w ∉ B.support := by
    intro hmem
    have huQ : w ∈ Q.support := by
      rw [hB_def, Walk.support_copy] at hmem
      exact (Walk.isSubwalk_drop Q m).support_subset hmem
    rcases hw with h2 | ⟨h2, h3, h4⟩
    · have := dist_le_of_mem_support hQd huQ
      omega
    · exact h4 (eq_end_of_mem_support hQd huQ (by omega))
  have hA1 : 1 ≤ A.length := by rw [hAlen]; omega
  have hA2 : A.length + 1 ≤ k := by rw [hAlen]; omega
  obtain ⟨c, hcyc, hclen⟩ := exists_cycle_of_branches hApath hBpath hlenAB hA1 hdisj ha hb hwA hwB
  refine h (A.length + 1) (by omega) hA2 z c hcyc ?_
  rw [hclen]; ring

end Branches

/-! ## BFS layers around a vertex -/

section Layers

variable {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {v : V} {d k r : ℕ}

/-- The `r`-th BFS layer around `v`: the set of vertices at distance exactly `r` from `v`. -/
def layer (G : SimpleGraph V) (v : V) (r : ℕ) : Finset V :=
  Finset.univ.filter fun w => G.dist v w = r

@[simp] lemma mem_layer {G : SimpleGraph V} {v w : V} {r : ℕ} :
    w ∈ layer G v r ↔ G.dist v w = r := by
  simp [layer]

/-- A neighbour of a vertex at distance `r` from `v` lies at distance `r - 1`, `r` or `r + 1`. -/
lemma dist_adj_cases {G : SimpleGraph V} {v w u : V} {r : ℕ} (h : G.Adj w u)
    (hw : G.dist v w = r) : G.dist v u = r - 1 ∨ G.dist v u = r ∨ G.dist v u = r + 1 := by
  have hc := SimpleGraph.Adj.diff_dist_adj h (u := v)
  rw [hw] at hc
  tauto

/-- A vertex of a graph without short even cycles has at most one neighbour one layer closer to
`v`. -/
lemma card_inter_layer_pred_le_one {G : SimpleGraph V} {v w : V} {k r : ℕ}
    (h : HasNoEvenCycleUpTo G k) (hr : 1 ≤ r) (hrk : r + 1 ≤ k) (hw : G.dist v w = r) :
    #(G.neighborFinset w ∩ layer G v (r - 1)) ≤ 1 := by
  rcases eq_or_lt_of_le hr with rfl | hr2
  · rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_inter, mem_neighborFinset, mem_layer] at ha hb
    have hreach : G.Reachable v w := Reachable.of_dist_ne_zero (by omega)
    have ha' : a = v := by
      rcases SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp ha.2 with h' | h'
      · exact h'.symm
      · exact absurd (hreach.trans ha.1.reachable) h'
    have hb' : b = v := by
      rcases SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp hb.2 with h' | h'
      · exact h'.symm
      · exact absurd (hreach.trans hb.1.reachable) h'
    rw [ha', hb']
  · rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_inter, mem_neighborFinset, mem_layer] at ha hb
    by_contra hne
    exact not_adj_two_of_dist h (by omega) ha.2 hb.2 hne (by omega) ha.1.symm hb.1.symm
      (Or.inl (by omega))

/-- A vertex of a graph without short even cycles has at most one neighbour in the same layer. -/
lemma card_inter_layer_eq_le_one {G : SimpleGraph V} {v w : V} {k r : ℕ}
    (h : HasNoEvenCycleUpTo G k) (hr : 1 ≤ r) (hrk : r + 1 ≤ k) (hw : G.dist v w = r) :
    #(G.neighborFinset w ∩ layer G v r) ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_inter, mem_neighborFinset, mem_layer] at ha hb
  by_contra hne
  exact not_adj_two_of_dist h hr ha.2 hb.2 hne hrk ha.1.symm hb.1.symm
    (Or.inr ⟨hw, ha.1.ne, hb.1.ne⟩)

/-- Every vertex of the `r`-th layer has at least `d - 1` neighbours in the `(r+1)`-st layer when
all degrees exceed `d`. -/
lemma card_inter_succ_layer_ge {G : SimpleGraph V} {v w : V} {k d r : ℕ}
    (h : HasNoEvenCycleUpTo G k) (hdeg : ∀ x, d + 1 ≤ G.degree x) (hr : 1 ≤ r)
    (hrk : r + 1 ≤ k) (hw : G.dist v w = r) :
    d - 1 ≤ #(G.neighborFinset w ∩ layer G v (r + 1)) := by
  set A1 := G.neighborFinset w ∩ layer G v (r - 1) with hA1
  set A2 := G.neighborFinset w ∩ layer G v r with hA2
  set A3 := G.neighborFinset w ∩ layer G v (r + 1) with hA3
  have hcover : G.neighborFinset w ⊆ A1 ∪ A2 ∪ A3 := by
    intro u hu
    have huadj : G.Adj w u := by simpa using hu
    rcases dist_adj_cases huadj hw with h1 | h2 | h3
    · refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
      rw [hA1]
      exact Finset.mem_inter.mpr ⟨hu, mem_layer.mpr h1⟩
    · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      rw [hA2]
      exact Finset.mem_inter.mpr ⟨hu, mem_layer.mpr h2⟩
    · refine Finset.mem_union_right _ ?_
      rw [hA3]
      exact Finset.mem_inter.mpr ⟨hu, mem_layer.mpr h3⟩
  have h1 : #A1 ≤ 1 := card_inter_layer_pred_le_one h hr hrk hw
  have h2 : #A2 ≤ 1 := card_inter_layer_eq_le_one h hr hrk hw
  have hdeg' : d + 1 ≤ #(G.neighborFinset w) := by
    have := hdeg w
    rwa [← card_neighborFinset_eq_degree] at this
  have hle : #(G.neighborFinset w) ≤ #A1 + #A2 + #A3 := by
    have hu1 : #(A1 ∪ A2 ∪ A3) ≤ #(A1 ∪ A2) + #A3 := Finset.card_union_le _ _
    have hu2 : #(A1 ∪ A2) ≤ #A1 + #A2 := Finset.card_union_le _ _
    exact (Finset.card_le_card hcover).trans (by omega)
  omega

/-- In a graph without short even cycles all of whose degrees exceed `d`, the BFS layers around
any vertex grow at least by the factor `d - 1`. -/
theorem layer_step {G : SimpleGraph V} {v : V} {k d r : ℕ}
    (h : HasNoEvenCycleUpTo G k) (hdeg : ∀ x, d + 1 ≤ G.degree x) (hr : 1 ≤ r)
    (hrk : r + 1 ≤ k) : (d - 1) * #(layer G v r) ≤ #(layer G v (r + 1)) := by
  have hA : ∀ w ∈ layer G v r, d - 1 ≤ #(G.neighborFinset w ∩ layer G v (r + 1)) := by
    intro w hw
    exact card_inter_succ_layer_ge h hdeg hr hrk (mem_layer.mp hw)
  have hdisj : (layer G v r : Set V).PairwiseDisjoint
      (fun w => G.neighborFinset w ∩ layer G v (r + 1)) := by
    intro a ha b hb hne
    show Disjoint (G.neighborFinset a ∩ layer G v (r + 1)) (G.neighborFinset b ∩ layer G v (r + 1))
    rw [Finset.disjoint_left]
    intro u hua hub
    simp only [Finset.mem_inter, mem_neighborFinset, mem_layer] at hua hub
    exact not_adj_two_of_dist h hr (mem_layer.mp ha) (mem_layer.mp hb) hne hrk
      hua.1 hub.1 (Or.inl hua.2)
  calc (d - 1) * #(layer G v r)
      = ∑ w ∈ layer G v r, (d - 1) := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ w ∈ layer G v r, #(G.neighborFinset w ∩ layer G v (r + 1)) := Finset.sum_le_sum hA
    _ = #((layer G v r).biUnion (fun w => G.neighborFinset w ∩ layer G v (r + 1))) :=
        (Finset.card_biUnion hdisj).symm
    _ ≤ #(layer G v (r + 1)) :=
        Finset.card_le_card (Finset.biUnion_subset.mpr fun _ _ => Finset.inter_subset_right)

end Layers
/-! ## Claim II: layer growth -/

section Prune

variable {G : SimpleGraph V} [Fintype V]
variable {v : V} {d k r : ℕ}

/-- **Claim II.** In a graph without short even cycles all of whose degrees exceed `d`, the `r`-th
BFS layer around any vertex has at least `(d - 1) ^ r` vertices. -/
theorem layer_card_ge (h : HasNoEvenCycleUpTo G k) (hdeg : ∀ x, d + 1 ≤ G.degree x) {r : ℕ}
    (hr : 1 ≤ r) (hrk : r ≤ k) : (d - 1) ^ r ≤ #(layer G v r) := by
  classical
  revert hrk
  induction r, hr using Nat.le_induction with
  | base =>
    intro _
    have hsub : G.neighborFinset v ⊆ layer G v 1 := by
      intro u hu
      have hvu : G.Adj v u := by simpa using hu
      exact mem_layer.mpr (SimpleGraph.dist_eq_one_iff_adj.mpr hvu)
    have h1 : #(G.neighborFinset v) ≤ #(layer G v 1) := Finset.card_le_card hsub
    have h2 : d + 1 ≤ #(G.neighborFinset v) := by
      have := hdeg v
      rwa [← card_neighborFinset_eq_degree] at this
    simp only [pow_one]
    omega
  | succ n hn ih =>
    intro hnk
    have hIH : (d - 1) ^ n ≤ #(layer G v n) := ih (by omega)
    have hstep := layer_step (G := G) (v := v) h hdeg hn (by omega : n + 1 ≤ k)
    rw [pow_succ]
    calc (d - 1) ^ n * (d - 1) ≤ #(layer G v n) * (d - 1) := Nat.mul_le_mul_right _ hIH
      _ = (d - 1) * #(layer G v n) := by ring
      _ ≤ #(layer G v (n + 1)) := hstep

/-- A nonempty graph without short even cycles all of whose degrees exceed `d` has strictly more
than `(d - 1) ^ k` vertices. -/
theorem lt_card_of_min_degree {v : V} (h : HasNoEvenCycleUpTo G k) (hd : 1 ≤ d) (hk : 1 ≤ k)
    (hdeg : ∀ x, d + 1 ≤ G.degree x) : (d - 1) ^ k < Fintype.card V := by
  classical
  have h1 : (d - 1) ^ k ≤ #(layer G v k) := layer_card_ge h hdeg hk le_rfl
  have hv : v ∉ layer G v k := by
    simp only [mem_layer, SimpleGraph.dist_self]
    omega
  have h2 : #(layer G v k) ≤ Fintype.card V - 1 := by
    have hsub : layer G v k ⊆ Finset.univ.erase v := by
      intro u hu
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ u⟩
      rintro rfl
      exact hv hu
    have := Finset.card_le_card hsub
    rwa [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ] at this
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  omega

end Prune

/-! ## Pruning vertices of small degree -/

universe u

/-- **Counting step.** A graph without short even cycles has at most `d * n` edges whenever
`n ≤ (d - 1) ^ k`. The proof repeatedly deletes a vertex of degree at most `d` (each deletion
removes at most `d` edges); the remaining graph would have minimum degree `> d`, which is
impossible by `lt_card_of_min_degree`. The statement is phrased with `Set.ncard` so that the
recursive call on the induced subgraph can be combined with the edge count without depending on
the particular `Fintype` instance of the edge set. -/
theorem edgeSet_ncard_le_aux :
    ∀ (N : ℕ) (W : Type u) [Fintype W] (G : SimpleGraph W)
      (d k : ℕ), 1 ≤ d → 1 ≤ k → HasNoEvenCycleUpTo G k →
      Fintype.card W ≤ (d - 1) ^ k → Fintype.card W ≤ N →
      G.edgeSet.ncard ≤ d * Fintype.card W := by
  intro N
  induction N with
  | zero =>
    intro W _ G d k hd hk h hcard hN
    classical
    have hz : Fintype.card W = 0 := Nat.le_zero.mp hN
    have hEmp : IsEmpty W := Fintype.card_eq_zero_iff.mp hz
    haveI := hEmp
    have hempe : G.edgeSet = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp fun hne => hne.elim fun e _ => isEmptyElim e
    rw [hempe, hz, mul_zero]
    simp
  | succ N ih =>
    intro W _ G d k hd hk h hcard hN
    classical
    by_cases hlow : ∃ x : W, G.degree x ≤ d
    · obtain ⟨x, hx⟩ := hlow
      have hcardc : Fintype.card (↥({x}ᶜ : Set W)) = Fintype.card W - 1 := by
        rw [Fintype.card_compl_set]
        simp
      have hIH := ih (↥({x}ᶜ : Set W)) (G.induce {x}ᶜ) d k hd hk (h.induce {x}ᶜ)
        (by rw [hcardc]; exact le_trans (Nat.sub_le _ _) hcard)
        (by rw [hcardc]; omega)
      rw [hcardc] at hIH
      have hdel : G.edgeSet.ncard ≤ (G.induce {x}ᶜ).edgeSet.ncard + G.degree x := by
        have h1 : G.edgeSet.ncard ≤
            (G.edgeSet \ G.incidenceSet x).ncard + (G.incidenceSet x).ncard :=
          Set.ncard_le_ncard_sdiff_add_ncard _ _
        rw [SimpleGraph.ncard_incidenceSet] at h1
        have h2 : (G.edgeSet \ G.incidenceSet x).ncard = (G.induce {x}ᶜ).edgeSet.ncard := by
          rw [← SimpleGraph.edgeSet_deleteIncidenceSet]
          rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
          exact (SimpleGraph.card_edgeFinset_induce_compl_singleton G x).symm
        rwa [h2] at h1
      have hW : 1 ≤ Fintype.card W := Fintype.card_pos_iff.mpr ⟨x⟩
      have hmul : d * (Fintype.card W - 1) + d = d * Fintype.card W := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
        exact Nat.sub_add_cancel (by
          calc d = d * 1 := (mul_one d).symm
            _ ≤ d * Fintype.card W := Nat.mul_le_mul_left d hW)
      calc G.edgeSet.ncard ≤ (G.induce {x}ᶜ).edgeSet.ncard + G.degree x := hdel
        _ ≤ d * (Fintype.card W - 1) + d := Nat.add_le_add hIH hx
        _ = d * Fintype.card W := hmul
    · push_neg at hlow
      have hdeg : ∀ x : W, d + 1 ≤ G.degree x := fun x => by
        have := hlow x
        omega
      rcases isEmpty_or_nonempty W with hemp | hne
      · haveI := hemp
        have hz : Fintype.card W = 0 := Fintype.card_eq_zero_iff.mpr hemp
        have hempe : G.edgeSet = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp fun hne => hne.elim fun e _ => isEmptyElim e
        rw [hempe, hz, mul_zero]
        simp
      · obtain ⟨x⟩ := hne
        have hlt := lt_card_of_min_degree (G := G) (v := x) (d := d) h hd hk hdeg
        omega

/-- **Lemma 3, counting form (`ncard` version).** -/
theorem edgeSet_ncard_le {G : SimpleGraph V} [Fintype V]
    {d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k) (h : HasNoEvenCycleUpTo G k)
    (hcard : Fintype.card V ≤ (d - 1) ^ k) : G.edgeSet.ncard ≤ d * Fintype.card V :=
  edgeSet_ncard_le_aux (Fintype.card V) V G d k hd hk h hcard le_rfl

/-- **Lemma 3, counting form.** A graph on `n` vertices without cycles of length
`2, 4, …, 2k` has at most `d * n` edges whenever `n ≤ (d - 1) ^ k`. -/
theorem edgeFinset_card_le {G : SimpleGraph V} [Fintype V]
    {d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k) (h : HasNoEvenCycleUpTo G k)
    (hcard : Fintype.card V ≤ (d - 1) ^ k) : #G.edgeFinset ≤ d * Fintype.card V := by
  classical
  have h1 := edgeSet_ncard_le (G := G) hd hk h hcard
  rwa [Set.ncard_eq_toFinset_card'] at h1

/-! ## Lemma 3 -/

/-- **Lemma 3, extremal form.** `ex(n, 𝒞_{2k}) ≤ d * n` with `d = ⌈n^{1/k}⌉ + 1`. -/
theorem exEvenCycles_le_ceil (n k : ℕ) (hk : 1 ≤ k) :
    exEvenCycles n k ≤ (Nat.ceil ((n : ℝ) ^ ((k : ℝ)⁻¹)) + 1) * n := by
  classical
  set c := Nat.ceil ((n : ℝ) ^ ((k : ℝ)⁻¹)) with hc
  have hle : (n : ℝ) ^ ((k : ℝ)⁻¹) ≤ (c : ℝ) := Nat.le_ceil _
  have hpow : ((n : ℝ) ^ ((k : ℝ)⁻¹)) ^ k = (n : ℝ) :=
    Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) (by omega : k ≠ 0)
  have hck : n ≤ c ^ k := by
    have h1 : (n : ℝ) ≤ (c : ℝ) ^ k := by
      rw [← hpow]
      exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg n) _) hle k
    have h2 : (n : ℝ) ≤ ((c ^ k : ℕ) : ℝ) := by
      rw [Nat.cast_pow]
      exact h1
    exact_mod_cast h2
  refine exEvenCycles_le (m := (c + 1) * n) fun G hG => ?_
  have hcard : Fintype.card (Fin n) ≤ (c + 1 - 1) ^ k := by
    rw [Nat.add_sub_cancel]
    simpa using hck
  have := edgeFinset_card_le (G := G) (d := c + 1) (k := k) (by omega) hk hG hcard
  simpa using this

/-- The paper's form of **Lemma 3**: `ex(n, 𝒞_{2k}) ≤ n^{1 + 1/k} + 2n`. -/
theorem lemma3_graph (n k : ℕ) (hk : 1 ≤ k) :
    (exEvenCycles n k : ℝ) ≤ (n : ℝ) ^ (1 + (k : ℝ)⁻¹) + 2 * (n : ℝ) := by
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hinv : (k : ℝ)⁻¹ ≠ 0 := (inv_pos.mpr hkr).ne'
  have hb := exEvenCycles_le_ceil n k hk
  have hcast : (exEvenCycles n k : ℝ) ≤ ((Nat.ceil ((n : ℝ) ^ ((k : ℝ)⁻¹)) + 1 : ℕ) : ℝ) * (n : ℝ) := by
    exact_mod_cast hb
  have hx0 : (0 : ℝ) ≤ (n : ℝ) ^ ((k : ℝ)⁻¹) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hd : ((Nat.ceil ((n : ℝ) ^ ((k : ℝ)⁻¹)) + 1 : ℕ) : ℝ) ≤
      (n : ℝ) ^ ((k : ℝ)⁻¹) + 2 := by
    have := Nat.ceil_lt_add_one hx0
    have hcast' : ((Nat.ceil ((n : ℝ) ^ ((k : ℝ)⁻¹)) : ℕ) : ℝ) <
        (n : ℝ) ^ ((k : ℝ)⁻¹) + 1 := this
    push_cast
    linarith
  have hkey : (n : ℝ) ^ (1 + (k : ℝ)⁻¹) = (n : ℝ) ^ ((k : ℝ)⁻¹) * (n : ℝ) := by
    rcases eq_or_lt_of_le (Nat.cast_nonneg n : (0 : ℝ) ≤ n) with h0 | h0
    · rw [← h0, Real.zero_rpow (by positivity : 1 + (k : ℝ)⁻¹ ≠ 0), Real.zero_rpow hinv,
        mul_zero]
    · rw [add_comm, Real.rpow_add h0, Real.rpow_one]
  have hmain : ((Nat.ceil ((n : ℝ) ^ ((k : ℝ)⁻¹)) + 1 : ℕ) : ℝ) * (n : ℝ) ≤
      (n : ℝ) ^ (1 + (k : ℝ)⁻¹) + 2 * (n : ℝ) := by
    rw [hkey]
    have := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg n)
    linarith
  linarith

/-- **Lemma 3**, in the equivalent form `ex(n, 𝒞_{2k}) ≤ n · n^{1/k} + 2n`. -/
theorem lemma3_graph' (n k : ℕ) (hk : 1 ≤ k) :
    (exEvenCycles n k : ℝ) ≤ (n : ℝ) * (n : ℝ) ^ ((k : ℝ)⁻¹) + 2 * (n : ℝ) := by
  have h := lemma3_graph n k hk
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hx0 : (0 : ℝ) ≤ (n : ℝ) ^ ((k : ℝ)⁻¹) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  rcases eq_or_lt_of_le (Nat.cast_nonneg n : (0 : ℝ) ≤ n) with h0 | h0
  · have hn : n = 0 := Nat.cast_eq_zero.mp h0.symm
    subst hn
    have hz : exEvenCycles 0 k = 0 := by
      have hle := exEvenCycles_le_ceil 0 k hk
      simp at hle
      omega
    rw [hz]
    simp
  · have hkey : (n : ℝ) ^ (1 + (k : ℝ)⁻¹) = (n : ℝ) ^ ((k : ℝ)⁻¹) * (n : ℝ) := by
      rw [add_comm, Real.rpow_add h0, Real.rpow_one]
    rw [hkey] at h
    have := mul_comm ((n : ℝ) ^ ((k : ℝ)⁻¹)) (n : ℝ)
    linarith

end AchainsComplexity

/-! ## Part 2: Statement 1 of “Math notes 2024”, pp. 385–386

The notions of a `B_k`-set, of the Minkowski sum and of a pseudograph, and the proof of Statement 1
(which rests on Lemma 3 reproduced above). -/

namespace BkSet

noncomputable section

/-- A `k`-sum-distinct set. -/
def IsBkSeq {G : Type*} [AddCommMonoid G] (k : ℕ) (B : Finset G) : Prop :=
  ∀ s t : Multiset G, (∀ x ∈ s, x ∈ B) → (∀ x ∈ t, x ∈ B) →
    s.card = k → t.card = k → s.sum = t.sum → s = t

end

end BkSet

/-! ## Statement 1 of "Math notes 2024", pp. 385-386

The notes introduce `B_k`-sets (already defined above as `IsBkSeq`), the Minkowski sum
`A + B = {a + b | a ∈ A, b ∈ B}` (`minkowskiSum`) and pseudographs, i.e. graphs in which loops are
admitted (`Pseudograph`). They then prove:

`Statement 1`. Let `A ⊂ ℕ`, and let `B ⊂ (A + A)` be a `B_k`-set. Then `|B| ≤ |A|^{1+1/k} + 3|A|`.

The proof builds the pseudograph `G_B` on the vertex set `A` whose edges are the pairs `(a, a')`
with `a + a' ∈ B`, keeping a single edge for each sum, so that `G_B` has exactly `|B|` edges. The
representative of a sum is fixed once and for all by `Classical.choose`; this choice is immaterial
because distinct edges of `G_B` have distinct sums (`esum_injOn`). Then one
observes that the graph `G*_B` obtained by deleting the loops has no even cycle of length `2r` for
`2 ≤ r ≤ k` (a cycle of length `2r` would give two different `r`-term sums of elements of `B` that
coincide, contradicting the `B_k` property), applies Lemma 3 to `G*_B`, and finally adds the bound
`|A|` on the number of loops.

## Main results

* `BkSet.statement1` : `|B| ≤ |A|^{1+1/k} + 3|A|` for a `B_k`-set `B ⊆ A + A`.
* `BkSet.card_le_ceil` : the counting form `|B| ≤ |A| + (⌈|A|^{1/k}⌉ + 1)·|A|`.
* `BkSet.no_short_even_cycle` : `G*_B` has no even cycle of length `2, 4, …, 2k`.
-/

noncomputable section

open Finset

open scoped BigOperators Classical

namespace BkSet

/-! ## Minkowski sums and pseudographs -/

/-- The Minkowski sum `A + C = {a + c | a ∈ A, c ∈ C}` of two finite sets of naturals. -/
def minkowskiSum (A C : Finset ℕ) : Finset ℕ := (A ×ˢ C).image fun p => p.1 + p.2

@[simp]
theorem mem_minkowskiSum {A C : Finset ℕ} {x : ℕ} :
    x ∈ minkowskiSum A C ↔ ∃ a ∈ A, ∃ c ∈ C, a + c = x := by
  simp only [minkowskiSum, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨a, c, ⟨ha, hc⟩, rfl⟩
    exact ⟨a, ha, c, hc, rfl⟩
  · rintro ⟨a, ha, c, hc, rfl⟩
    exact ⟨a, c, ⟨ha, hc⟩, rfl⟩

/-- The sum of the two entries of an unordered pair of vertices. -/
def pairSum {V : Type*} (f : V → ℕ) (e : Sym2 V) : ℕ :=
  Sym2.lift ⟨fun a b => f a + f b, fun _ _ => Nat.add_comm _ _⟩ e

@[simp]
theorem pairSum_mk {V : Type*} (f : V → ℕ) (a b : V) : pairSum f s(a, b) = f a + f b :=
  Sym2.lift_mk _ a b

/-- A pseudograph on `V`: a finite set of unordered pairs of vertices in which loops, i.e. edges
with identical ends, are admitted. An ordinary graph is a pseudograph without loops. -/
structure Pseudograph (V : Type*) where
  /-- The edges of the pseudograph, loops allowed. -/
  edge : Finset (Sym2 V)

namespace Pseudograph

variable {V : Type*}

/-- The loops of a pseudograph. -/
def loops [DecidableEq V] (P : Pseudograph V) : Finset (Sym2 V) := P.edge.filter Sym2.IsDiag

/-- The ordinary graph obtained from a pseudograph by deleting all loops. -/
def toSimpleGraph (P : Pseudograph V) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (P.edge : Set (Sym2 V))

theorem adj_toSimpleGraph {P : Pseudograph V} {u v : V} :
    P.toSimpleGraph.Adj u v ↔ u ≠ v ∧ s(u, v) ∈ P.edge := by
  rw [toSimpleGraph, SimpleGraph.fromEdgeSet_adj]
  simp [and_comm]

theorem edgeSet_toSimpleGraph (P : Pseudograph V) :
    P.toSimpleGraph.edgeSet = (P.edge : Set (Sym2 V)) \ Sym2.diagSet := by
  rw [toSimpleGraph, SimpleGraph.edgeSet_fromEdgeSet]

theorem edgeFinset_toSimpleGraph [Fintype V] [DecidableEq V] (P : Pseudograph V) :
    P.toSimpleGraph.edgeFinset = P.edge.filter fun e => ¬ e.IsDiag := by
  ext e
  rw [SimpleGraph.mem_edgeFinset, edgeSet_toSimpleGraph]
  simp [Set.mem_sdiff, Sym2.mem_diagSet]

/-- The edges of a pseudograph are its loops together with the edges of the graph obtained by
deleting the loops. -/
theorem card_edge_eq_loops_add [Fintype V] [DecidableEq V] (P : Pseudograph V) :
    P.edge.card = P.loops.card + P.toSimpleGraph.edgeFinset.card := by
  rw [loops, edgeFinset_toSimpleGraph]
  exact (Finset.card_filter_add_card_filter_not (s := P.edge) (p := Sym2.IsDiag)).symm

/-- A pseudograph has at most one loop per vertex, hence at most `|V|` loops. -/
theorem card_loops_le [Fintype V] [DecidableEq V] (P : Pseudograph V) :
    P.loops.card ≤ Fintype.card V := by
  have hsub : P.loops ⊆ Finset.univ.image Sym2.diag := by
    intro e he
    simp only [loops, Finset.mem_filter] at he
    exact Finset.mem_image.mpr ⟨e.diagElem he.2, Finset.mem_univ _, Sym2.diag_diagElem he.2⟩
  calc P.loops.card ≤ (Finset.univ.image Sym2.diag).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset V).card := Finset.card_image_le
    _ = Fintype.card V := Finset.card_univ

end Pseudograph

/-- A `B_k`-set is a `B_l`-set for every `l ≤ k`. -/
theorem IsBkSeq.mono {G : Type*} [AddCommMonoid G] {B : Finset G} {k l : ℕ}
    (h : IsBkSeq k B) (hl : l ≤ k) : IsBkSeq l B := by
  intro s t hs ht hcs hct hsum
  rcases Nat.lt_or_ge l k with hlt | hge
  · rcases Nat.eq_zero_or_pos l with hl0 | hlpos
    · rw [hl0] at hcs hct
      have hs0 : s = 0 := Multiset.card_eq_zero.mp hcs
      have ht0 : t = 0 := Multiset.card_eq_zero.mp hct
      rw [hs0, ht0]
    obtain ⟨c, hc⟩ := Multiset.exists_mem_of_ne_zero (s := s) fun h0 => by
      have hz : (0:ℕ) = l := by simpa [h0] using hcs
      omega
    have hcB : c ∈ B := hs c hc
    have hN : l + (k - l) = k := Nat.add_sub_cancel' hl
    have hmems : ∀ x ∈ s + Multiset.replicate (k - l) c, x ∈ B := by
      intro x hx
      rcases Multiset.mem_add.mp hx with h' | h'
      · exact hs x h'
      · rw [(Multiset.mem_replicate.mp h').2]; exact hcB
    have hmemt : ∀ x ∈ t + Multiset.replicate (k - l) c, x ∈ B := by
      intro x hx
      rcases Multiset.mem_add.mp hx with h' | h'
      · exact ht x h'
      · rw [(Multiset.mem_replicate.mp h').2]; exact hcB
    have hcard_s : (s + Multiset.replicate (k - l) c).card = k := by
      rw [Multiset.card_add, Multiset.card_replicate, hcs, hN]
    have hcard_t : (t + Multiset.replicate (k - l) c).card = k := by
      rw [Multiset.card_add, Multiset.card_replicate, hct, hN]
    have hsum' : (s + Multiset.replicate (k - l) c).sum
        = (t + Multiset.replicate (k - l) c).sum := by
      simp only [Multiset.sum_add, Multiset.sum_replicate, hsum]
    have heq := h _ _ hmems hmemt hcard_s hcard_t hsum'
    refine Multiset.ext.mpr fun a => ?_
    have hcount := congrArg (fun u => u.count a) heq
    simp only [Multiset.count_add, Multiset.count_replicate] at hcount
    split_ifs at hcount
    all_goals omega
  · have : l = k := le_antisymm hl hge
    subst this
    exact h s t hs ht hcs hct hsum

/-! ## Splitting a sum into its even and odd parts -/

/-- A sum over `Finset.range (2 * r)` splits into the sums over even and odd indices. -/
theorem sum_range_two_mul (r : ℕ) (g : ℕ → ℤ) :
    (∑ i ∈ Finset.range (2 * r), g i) =
      (∑ j ∈ Finset.range r, g (2 * j)) + ∑ j ∈ Finset.range r, g (2 * j + 1) := by
  induction r with
  | zero => simp
  | succ n ih =>
    have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ (f := fun j => g (2 * j)),
      Finset.sum_range_succ (f := fun j => g (2 * j + 1)), ih]
    ring

/-- A sum over `Fin (2 * r)` splits into the sums over even and odd indices. -/
theorem sum_fin_two_mul (r : ℕ) (g : ℕ → ℤ) :
    (∑ i : Fin (2 * r), g (i : ℕ)) =
      (∑ j : Fin r, g (2 * (j : ℕ))) + ∑ j : Fin r, g (2 * (j : ℕ) + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i => g i) (2 * r),
    Fin.sum_univ_eq_sum_range (fun j => g (2 * j)) r,
    Fin.sum_univ_eq_sum_range (fun j => g (2 * j + 1)) r]
  exact sum_range_two_mul r g

/-- Shifting the even-indexed sum by one step does not change it, provided the index `2 * r`
wraps around to `0`. -/
theorem sum_even_shift (r : ℕ) (b : ℕ → ℤ) (hper : b (2 * r) = b 0) :
    (∑ j : Fin r, b (2 * (j : ℕ) + 2)) = ∑ j : Fin r, b (2 * (j : ℕ)) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => b (2 * j + 2)) r,
    Fin.sum_univ_eq_sum_range (fun j => b (2 * j)) r]
  set f : ℕ → ℤ := fun j => b (2 * j) with hf
  have hstep : (∑ k ∈ Finset.range r, b (2 * k + 2)) = ∑ k ∈ Finset.range r, f (k + 1) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    show b (2 * k + 2) = b (2 * (k + 1))
    ring_nf
  rw [hstep]
  have h1 := Finset.sum_range_succ' f r
  have h2 := Finset.sum_range_succ f r
  have h3 : f r = f 0 := by
    show b (2 * r) = b (2 * 0)
    simpa using hper
  linarith

/-- For a closed walk of even length `2 * r` whose consecutive vertex labels satisfy
`e i = a i + a (i + 1)`, the sum of the edge labels at even positions equals the sum of the edge
labels at odd positions. -/
theorem alternating_sum_eq (r : ℕ) (a : ℕ → ℤ) (hper : a (2 * r) = a 0) :
    (∑ j : Fin r, (a (2 * (j : ℕ)) + a (2 * (j : ℕ) + 1))) =
      ∑ j : Fin r, (a (2 * (j : ℕ) + 1) + a (2 * (j : ℕ) + 2)) := by
  have hsplit := sum_fin_two_mul r a
  have hshift := sum_even_shift r a hper
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  linarith

/-! ## The pseudograph `G_B` of a `B_k`-set -/

/-- The sum of the two labels of an edge of the pseudograph on `A`. -/
def esum (A : Finset ℕ) (e : Sym2 A) : ℕ := pairSum (fun v : A => (v : ℕ)) e

@[simp]
theorem esum_mk (A : Finset ℕ) (u v : A) : esum A s(u, v) = (u : ℕ) + (v : ℕ) :=
  pairSum_mk _ _ _

section Construction

variable (A B : Finset ℕ)

/-- Every `b ∈ B` is the sum of two elements of `A`, packaged as a pair of vertices. -/
theorem exists_pair (hA : ∀ b ∈ B, ∃ a ∈ A, ∃ a' ∈ A, a + a' = b) (b : B) :
    ∃ p : A × A, (p.1 : ℕ) + (p.2 : ℕ) = (b : ℕ) := by
  obtain ⟨a, ha, a', ha', h⟩ := hA b b.2
  exact ⟨(⟨a, ha⟩, ⟨a', ha'⟩), h⟩

/-- A chosen representation of `b ∈ B ⊂ A + A` as a sum `a + a'` with `a, a' ∈ A`. -/
noncomputable def wit (hA : ∀ b ∈ B, ∃ a ∈ A, ∃ a' ∈ A, a + a' = b) (b : B) : A × A :=
  Classical.choose (exists_pair A B hA b)

theorem wit_sum (hA : ∀ b ∈ B, ∃ a ∈ A, ∃ a' ∈ A, a + a' = b) (b : B) :
    ((wit A B hA b).1 : ℕ) + ((wit A B hA b).2 : ℕ) = (b : ℕ) :=
  Classical.choose_spec (exists_pair A B hA b)

/-- The edge of `G_B` that represents the relation `a + a' = b`. -/
def gEdge (hA : ∀ b ∈ B, ∃ a ∈ A, ∃ a' ∈ A, a + a' = b) (b : B) : Sym2 A :=
  s((wit A B hA b).1, (wit A B hA b).2)

theorem esum_gEdge (hA : ∀ b ∈ B, ∃ a ∈ A, ∃ a' ∈ A, a + a' = b) (b : B) :
    esum A (gEdge A B hA b) = (b : ℕ) := by
  rw [esum, gEdge, pairSum_mk, wit_sum]

theorem gEdge_injective (hA : ∀ b ∈ B, ∃ a ∈ A, ∃ a' ∈ A, a + a' = b) :
    Function.Injective (gEdge A B hA) := by
  intro b1 b2 h
  have h1 := esum_gEdge A B hA b1
  have h2 := esum_gEdge A B hA b2
  rw [h] at h1
  exact Subtype.ext (h1.symm.trans h2)

/-- The edge set of `G_B`: one edge per element of `B` (edges with the same sum are identified). -/
def gEdgeFinset (hA : ∀ b ∈ B, ∃ a ∈ A, ∃ a' ∈ A, a + a' = b) : Finset (Sym2 A) :=
  B.attach.image (gEdge A B hA)

theorem card_gEdgeFinset (hA : ∀ b ∈ B, ∃ a ∈ A, ∃ a' ∈ A, a + a' = b) :
    (gEdgeFinset A B hA).card = B.card := by
  rw [gEdgeFinset, Finset.card_image_of_injective _ (gEdge_injective A B hA),
    Finset.card_attach]

/-- The pseudograph `G_B` of the paper: vertices `A`, and one edge `(a, a')` for every `b ∈ B`
with `a + a' = b` (loops are allowed). -/
def gPseudo (hA : ∀ b ∈ B, ∃ a ∈ A, ∃ a' ∈ A, a + a' = b) : Pseudograph A :=
  ⟨gEdgeFinset A B hA⟩

theorem edge_gPseudo (hA : ∀ b ∈ B, ∃ a ∈ A, ∃ a' ∈ A, a + a' = b) :
    (gPseudo A B hA).edge = gEdgeFinset A B hA := rfl

theorem esum_mem_B (hA : ∀ b ∈ B, ∃ a ∈ A, ∃ a' ∈ A, a + a' = b) {e : Sym2 A}
    (he : e ∈ (gPseudo A B hA).edge) : esum A e ∈ B := by
  rw [edge_gPseudo, gEdgeFinset, Finset.mem_image] at he
  obtain ⟨b, -, rfl⟩ := he
  rw [esum_gEdge]
  exact b.2

theorem esum_injOn (hA : ∀ b ∈ B, ∃ a ∈ A, ∃ a' ∈ A, a + a' = b) {e : Sym2 A}
    (he : e ∈ (gPseudo A B hA).edge) {e' : Sym2 A} (he' : e' ∈ (gPseudo A B hA).edge)
    (h : esum A e = esum A e') : e = e' := by
  rw [edge_gPseudo, gEdgeFinset, Finset.mem_image] at he he'
  obtain ⟨b, -, rfl⟩ := he
  obtain ⟨b', -, rfl⟩ := he'
  rw [esum_gEdge, esum_gEdge] at h
  exact congrArg (gEdge A B hA) (Subtype.ext h)

/-! ## `G_B*` has no short even cycles -/

/-- A cycle of length `2 * m`, `m ≥ 2`, in `G_B*` yields an equality between two different
`m`-fold sums of elements of `B`, contradicting that `B` is a `B_k`-set. -/
theorem cycle_contradiction (hA : ∀ b ∈ B, ∃ a ∈ A, ∃ a' ∈ A, a + a' = b) (k : ℕ)
    (hBk : IsBkSeq k B) (m : ℕ) (hm2 : 2 ≤ m) (hmk : m ≤ k) (v : A)
    (c : (gPseudo A B hA).toSimpleGraph.Walk v v) (hc : c.IsCycle)
    (hlen : c.length = 2 * m) : False := by
  classical
  have hBm : IsBkSeq m B := IsBkSeq.mono hBk hmk
  have heslen : c.edges.length = 2 * m := by
    rw [SimpleGraph.Walk.length_edges, hlen]
  have hnodup : c.edges.Nodup := hc.edges_nodup
  set a : ℕ → ℤ := fun i => ((c.getVert i : A) : ℤ) with ha
  have hper : a (2 * m) = a 0 := by
    simp only [ha]
    rw [show 2 * m = c.length from hlen.symm, SimpleGraph.Walk.getVert_length,
      SimpleGraph.Walk.getVert_zero]
  set idxE : Fin m → Fin c.edges.length :=
    fun j => ⟨2 * (j : ℕ), by rw [heslen]; have := j.isLt; omega⟩ with hidxE
  set idxO : Fin m → Fin c.edges.length :=
    fun j => ⟨2 * (j : ℕ) + 1, by rw [heslen]; have := j.isLt; omega⟩ with hidxO
  have hedge : ∀ i : Fin c.edges.length, c.edges.get i ∈ (gPseudo A B hA).edge := by
    intro i
    have h1 : c.edges.get i ∈ c.edges := List.get_mem _ _
    have h2 : c.edges.get i ∈ (gPseudo A B hA).toSimpleGraph.edgeSet :=
      SimpleGraph.Walk.edges_subset_edgeSet c h1
    rw [Pseudograph.edgeSet_toSimpleGraph] at h2
    exact Finset.mem_coe.mp ((Set.mem_sdiff _).mp h2).1
  have hEven : ∀ j : Fin m,
      ((esum A (c.edges.get (idxE j)) : ℕ) : ℤ) = a (2 * (j : ℕ)) + a (2 * (j : ℕ) + 1) := by
    intro j
    have hget : c.edges.get (idxE j)
        = s(c.getVert (2 * (j : ℕ)), c.getVert (2 * (j : ℕ) + 1)) := by
      simpa [idxE] using SimpleGraph.Walk.getElem_edges (p := c) (idxE j).2
    rw [hget]
    show ((pairSum (fun v : A => (v : ℕ)) s(c.getVert (2 * (j : ℕ)),
      c.getVert (2 * (j : ℕ) + 1)) : ℕ) : ℤ) = a (2 * (j : ℕ)) + a (2 * (j : ℕ) + 1)
    rw [pairSum_mk, Nat.cast_add]
  have hOdd : ∀ j : Fin m,
      ((esum A (c.edges.get (idxO j)) : ℕ) : ℤ) = a (2 * (j : ℕ) + 1) + a (2 * (j : ℕ) + 2) := by
    intro j
    have hget : c.edges.get (idxO j)
        = s(c.getVert (2 * (j : ℕ) + 1), c.getVert (2 * (j : ℕ) + 1 + 1)) := by
      simpa [idxO] using SimpleGraph.Walk.getElem_edges (p := c) (idxO j).2
    rw [hget]
    show ((pairSum (fun v : A => (v : ℕ)) s(c.getVert (2 * (j : ℕ) + 1),
      c.getVert (2 * (j : ℕ) + 1 + 1)) : ℕ) : ℤ)
      = a (2 * (j : ℕ) + 1) + a (2 * (j : ℕ) + 2)
    rw [pairSum_mk, Nat.cast_add]
  let s : Multiset ℕ := ((List.ofFn fun j : Fin m => esum A (c.edges.get (idxE j)) : List ℕ) : Multiset ℕ)
  let t : Multiset ℕ := ((List.ofFn fun j : Fin m => esum A (c.edges.get (idxO j)) : List ℕ) : Multiset ℕ)
  have hs_card : s.card = m := by simp [s]
  have ht_card : t.card = m := by simp [t]
  have hs_mem : ∀ x ∈ s, x ∈ B := by
    intro x hx
    simp only [s, Multiset.mem_coe, List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    exact esum_mem_B A B hA (hedge (idxE j))
  have ht_mem : ∀ x ∈ t, x ∈ B := by
    intro x hx
    simp only [t, Multiset.mem_coe, List.mem_ofFn] at hx
    obtain ⟨j, rfl⟩ := hx
    exact esum_mem_B A B hA (hedge (idxO j))
  have hsum : s.sum = t.sum := by
    have h1 : ((s.sum : ℕ) : ℤ) = ∑ j : Fin m, ((esum A (c.edges.get (idxE j)) : ℕ) : ℤ) := by
      simp [s, List.sum_ofFn, Nat.cast_sum]
    have h2 : ((t.sum : ℕ) : ℤ) = ∑ j : Fin m, ((esum A (c.edges.get (idxO j)) : ℕ) : ℤ) := by
      simp [t, List.sum_ofFn, Nat.cast_sum]
    have h3 : (∑ j : Fin m, ((esum A (c.edges.get (idxE j)) : ℕ) : ℤ))
        = ∑ j : Fin m, ((esum A (c.edges.get (idxO j)) : ℕ) : ℤ) := by
      rw [Finset.sum_congr rfl (fun j _ => hEven j),
        Finset.sum_congr rfl (fun j _ => hOdd j)]
      exact alternating_sum_eq m a hper
    exact Nat.cast_injective (h1.trans (h3.trans h2.symm))
  have hne : s ≠ t := by
    intro hst
    have h0 : esum A (c.edges.get (idxE ⟨0, by omega⟩)) ∈ t := by
      rw [← hst]
      simp only [s, Multiset.mem_coe, List.mem_ofFn]
      exact ⟨⟨0, by omega⟩, rfl⟩
    simp only [t, Multiset.mem_coe, List.mem_ofFn] at h0
    obtain ⟨j, hj⟩ := h0
    have heq := esum_injOn A B hA (hedge (idxO j)) (hedge (idxE ⟨0, by omega⟩)) hj
    have hidx := (List.Nodup.get_inj_iff hnodup).mp heq
    have hval := congrArg Fin.val hidx
    simp only [idxO, idxE] at hval
    omega
  exact hne (hBm s t hs_mem ht_mem hs_card ht_card hsum)

/-- The loop-free part `G_B*` of `G_B` has no cycle of even length `2, 4, …, 2k`. -/
theorem no_short_even_cycle (hA : ∀ b ∈ B, ∃ a ∈ A, ∃ a' ∈ A, a + a' = b) (k : ℕ)
    (hBk : IsBkSeq k B) :
    AchainsComplexity.HasNoEvenCycleUpTo (gPseudo A B hA).toSimpleGraph k := by
  intro m hm1 hmk v c hc hlen
  rcases Nat.lt_or_ge m 2 with hsmall | hbig
  · have hm1' : m = 1 := by omega
    subst hm1'
    have h3 := hc.three_le_length
    omega
  · exact cycle_contradiction A B hA k hBk m hbig hmk v c hc hlen

end Construction

/-! ## Statement 1 -/

section Bound

variable (A B : Finset ℕ)

/-- **Statement 1, counting form**: `|B| ≤ |A| + (⌈|A|^{1/k}⌉ + 1) · |A|`. -/
theorem card_le_ceil (hA : ∀ b ∈ B, ∃ a ∈ A, ∃ a' ∈ A, a + a' = b) (k : ℕ) (hk : 1 ≤ k)
    (hBk : IsBkSeq k B) :
    B.card ≤ A.card + (Nat.ceil ((A.card : ℝ) ^ ((k : ℝ)⁻¹)) + 1) * A.card := by
  classical
  set n := A.card with hn
  set c := Nat.ceil ((n : ℝ) ^ ((k : ℝ)⁻¹)) with hc
  have hle : (n : ℝ) ^ ((k : ℝ)⁻¹) ≤ (c : ℝ) := Nat.le_ceil _
  have hpow : ((n : ℝ) ^ ((k : ℝ)⁻¹)) ^ k = (n : ℝ) :=
    Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) (by omega : k ≠ 0)
  have hck : n ≤ c ^ k := by
    have h1 : (n : ℝ) ≤ (c : ℝ) ^ k := by
      rw [← hpow]
      exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg n) _) hle k
    have h2 : (n : ℝ) ≤ ((c ^ k : ℕ) : ℝ) := by
      rw [Nat.cast_pow]
      exact h1
    exact_mod_cast h2
  have hG := no_short_even_cycle A B hA k hBk
  have hcard : Fintype.card ↥A ≤ (c + 1 - 1) ^ k := by
    rw [Fintype.card_coe, Nat.add_sub_cancel]
    exact hck
  have hd := AchainsComplexity.edgeFinset_card_le
    (G := (gPseudo A B hA).toSimpleGraph) (d := c + 1) (k := k) (by omega) hk hG hcard
  rw [Fintype.card_coe] at hd
  have h1 : B.card = (gPseudo A B hA).edge.card := (card_gEdgeFinset A B hA).symm
  have h2 : (gPseudo A B hA).loops.card ≤ n := by
    have := Pseudograph.card_loops_le (gPseudo A B hA)
    rwa [Fintype.card_coe] at this
  have h3 : (gPseudo A B hA).edge.card
      = (gPseudo A B hA).loops.card + (gPseudo A B hA).toSimpleGraph.edgeFinset.card :=
    Pseudograph.card_edge_eq_loops_add _
  rw [h1, h3]
  have : (gPseudo A B hA).toSimpleGraph.edgeFinset.card ≤ (c + 1) * n := hd
  nlinarith

/-- **Statement 1**, pointwise form: if every `b ∈ B` is a sum of two elements of `A` and `B` is a
`B_k`-set, then `|B| ≤ |A|^{1 + 1/k} + 3|A|`. -/
theorem statement1' (k : ℕ) (hk : 1 ≤ k) (hA : ∀ b ∈ B, ∃ a ∈ A, ∃ a' ∈ A, a + a' = b)
    (hBk : IsBkSeq k B) :
    (B.card : ℝ) ≤ (A.card : ℝ) ^ (1 + (k : ℝ)⁻¹) + 3 * (A.card : ℝ) := by
  have hkr : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hinv : (k : ℝ)⁻¹ ≠ 0 := (inv_pos.mpr hkr).ne'
  set n := A.card with hn
  set c := Nat.ceil ((n : ℝ) ^ ((k : ℝ)⁻¹)) with hc
  have hcast : (B.card : ℝ) ≤ (n : ℝ) + ((c + 1 : ℕ) : ℝ) * (n : ℝ) := by
    have h := card_le_ceil A B hA k hk hBk
    rw [← hn, ← hc] at h
    exact_mod_cast h
  have hx0 : (0 : ℝ) ≤ (n : ℝ) ^ ((k : ℝ)⁻¹) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hd : ((c + 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ ((k : ℝ)⁻¹) + 2 := by
    have := Nat.ceil_lt_add_one hx0
    have hcast' : ((c : ℕ) : ℝ) < (n : ℝ) ^ ((k : ℝ)⁻¹) + 1 := this
    push_cast
    linarith
  have hkey : (n : ℝ) ^ (1 + (k : ℝ)⁻¹) = (n : ℝ) ^ ((k : ℝ)⁻¹) * (n : ℝ) := by
    rcases eq_or_lt_of_le (Nat.cast_nonneg n : (0 : ℝ) ≤ n) with h0 | h0
    · rw [← h0, Real.zero_rpow (by positivity : 1 + (k : ℝ)⁻¹ ≠ 0), Real.zero_rpow hinv,
        mul_zero]
    · rw [add_comm, Real.rpow_add h0, Real.rpow_one]
  have hmain : ((c + 1 : ℕ) : ℝ) * (n : ℝ) ≤
      (n : ℝ) ^ (1 + (k : ℝ)⁻¹) + 2 * (n : ℝ) := by
    rw [hkey]
    have := mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg n)
    linarith
  linarith

/-- **Statement 1** of the notes (p. 386). Let `A ⊂ ℕ` and let `B ⊂ (A + A)` be a `B_k`-set. Then
`|B| ≤ |A|^{1 + 1/k} + 3|A|`.

(As in the notes we only need `1 ≤ k`; the notes introduce `B_k`-sets for `k ≥ 2`.) -/
theorem statement1 (k : ℕ) (hk : 1 ≤ k) {A B : Finset ℕ} (hB : B ⊆ minkowskiSum A A)
    (hBk : IsBkSeq k B) :
    (B.card : ℝ) ≤ (A.card : ℝ) ^ (1 + (k : ℝ)⁻¹) + 3 * (A.card : ℝ) :=
  statement1' A B k hk (fun _ hb => mem_minkowskiSum.mp (hB hb)) hBk

end Bound

end BkSet

/-! ## Part 3: Theorem 4 -/

open Finset
open scoped Classical

namespace Theorem4

/-! ### Ordinary addition chains -/

/-- The pool of values available at step `k` of an ordinary addition chain: the initial value `1`
together with the entries computed so far. -/
def npPool (y : ℕ → ℕ) (k : ℕ) : Option (Fin k) → ℕ
  | none => 1
  | some j => y (j : ℕ)

@[simp]
theorem npPool_none (y : ℕ → ℕ) (k : ℕ) : npPool y k none = 1 := rfl

@[simp]
theorem npPool_some (y : ℕ → ℕ) {k : ℕ} (j : Fin k) : npPool y k (some j) = y (j : ℕ) := rfl

/-- An ordinary addition chain `1, y 0, …, y (L-1)`: every entry is the sum of two values available
before it, namely `1` or an earlier entry. -/
structure AddChain where
  /-- the length of the chain, i.e. the number of additions -/
  L : ℕ
  /-- the entries of the chain -/
  y : ℕ → ℕ
  /-- every entry is the sum of two available values -/
  valid : ∀ k < L, ∃ x z : Option (Fin k), y k = npPool y k x + npPool y k z

namespace AddChain

/-- The chain computes every number of the finite set `S`: each element of `S` is either `1` or one
of the entries of the chain. -/
def Computes (c : AddChain) (S : Finset ℕ) : Prop := ∀ a ∈ S, a = 1 ∨ ∃ k < c.L, c.y k = a

/-- `Computes` is monotone in the set. -/
theorem Computes.mono {c : AddChain} {S T : Finset ℕ} (h : c.Computes T) (hST : S ⊆ T) :
    c.Computes S := fun a ha => h a (hST ha)

theorem one_le_npPool (y : ℕ → ℕ) {k : ℕ} (hy : ∀ j < k, 1 ≤ y j) (u : Option (Fin k)) :
    1 ≤ npPool y k u := by
  rcases u with _ | ⟨j, hj⟩
  · simp
  · simpa using hy j hj

/-- Every entry of an addition chain is at least `2`. -/
theorem two_le_y (c : AddChain) : ∀ k < c.L, 2 ≤ c.y k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    obtain ⟨x, z, hxz⟩ := c.valid k hk
    have h1 : ∀ j < k, 1 ≤ c.y j := fun j hj => le_trans (by norm_num) (ih j hj (lt_trans hj hk))
    have hx := one_le_npPool c.y h1 x
    have hz := one_le_npPool c.y h1 z
    rw [hxz]
    omega

/-- The "increment" chain `1, 2, 3, …, M` of length `M - 1`, which computes every number up to
`M`. -/
def incr (M : ℕ) : AddChain where
  L := M - 1
  y := fun k => k + 2
  valid := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      exact ⟨none, none, by norm_num⟩
    · refine ⟨some ⟨k - 1, by omega⟩, none, ?_⟩
      simp only [npPool_some, npPool_none, Fin.val_mk]
      omega

@[simp]
theorem incr_L (M : ℕ) : (incr M).L = M - 1 := rfl

@[simp]
theorem incr_y (M k : ℕ) : (incr M).y k = k + 2 := rfl

/-- The increment chain computes every number in the interval `[1, M]`. -/
theorem incr_computes (M : ℕ) {S : Finset ℕ} (h : ∀ a ∈ S, 1 ≤ a ∧ a ≤ M) :
    (incr M).Computes S := by
  intro a ha
  obtain ⟨ha1, haM⟩ := h a ha
  rcases Nat.eq_or_lt_of_le ha1 with h1 | h2
  · exact Or.inl h1.symm
  · refine Or.inr ⟨a - 2, ?_, ?_⟩
    · simp only [incr_L]
      omega
    · simp only [incr_y]
      omega

/-- Some chain computes `S`, provided `S` contains no zero. -/
theorem exists_computes (S : Finset ℕ) (h : ∀ a ∈ S, 1 ≤ a) : ∃ c : AddChain, c.Computes S := by
  refine ⟨incr (∑ a ∈ S, a), incr_computes _ ?_⟩
  intro a ha
  exact ⟨h a ha, Finset.single_le_sum (f := fun x => x) (fun x _ => Nat.zero_le x) ha⟩

end AddChain

/-- `L(S)`: the length of a shortest ordinary addition chain computing the finite set `S`. -/
def setL (S : Finset ℕ) : ℕ := sInf {l | ∃ c : AddChain, c.L = l ∧ c.Computes S}

/-- A chain computing `S` bounds `setL S` from above. -/
theorem setL_le {S : Finset ℕ} {c : AddChain} (h : c.Computes S) : setL S ≤ c.L :=
  Nat.sInf_le ⟨c, rfl, h⟩

/-- The set of lengths of chains computing `S` is nonempty. -/
theorem setL_nonempty {S : Finset ℕ} (h : ∀ a ∈ S, 1 ≤ a) :
    {l | ∃ c : AddChain, c.L = l ∧ c.Computes S}.Nonempty := by
  obtain ⟨c, hc⟩ := AddChain.exists_computes S h
  exact ⟨c.L, c, rfl, hc⟩

/-- A shortest chain computing `S` exists. -/
theorem exists_optimal {S : Finset ℕ} (h : ∀ a ∈ S, 1 ≤ a) :
    ∃ c : AddChain, c.L = setL S ∧ c.Computes S :=
  Nat.sInf_mem (setL_nonempty h)

/-- The values appearing in the chain: the initial `1` and all entries. -/
def chainVals (c : AddChain) : Finset ℕ := insert 1 ((Finset.range c.L).image c.y)

theorem mem_chainVals {c : AddChain} {x : ℕ} :
    x ∈ chainVals c ↔ x = 1 ∨ ∃ k < c.L, c.y k = x := by
  simp only [chainVals, Finset.mem_insert, Finset.mem_image, Finset.mem_range]

theorem one_le_chainVals {c : AddChain} {x : ℕ} (h : x ∈ chainVals c) : 1 ≤ x := by
  rcases mem_chainVals.mp h with rfl | ⟨k, hk, rfl⟩
  · exact le_rfl
  · exact le_trans (by norm_num) (AddChain.two_le_y c k hk)

theorem AddChain.subset_chainVals {c : AddChain} {B : Finset ℕ} (h : c.Computes B) :
    B ⊆ chainVals c := by
  intro b hb
  rcases h b hb with rfl | ⟨k, hk, hy⟩
  · exact mem_chainVals.mpr (Or.inl rfl)
  · exact mem_chainVals.mpr (Or.inr ⟨k, hk, hy⟩)

/-! ### Sum-free `B_k`-sets and the Sidon property -/

/-- A set is sum-free if `B + B` is disjoint from `B`. -/
def SumFree (B : Finset ℕ) : Prop := ∀ a ∈ B, ∀ b ∈ B, a + b ∉ B

theorem isBkSeq_subset {k : ℕ} {B C : Finset ℕ} (h : BkSet.IsBkSeq k B) (hCB : C ⊆ B) :
    BkSet.IsBkSeq k C :=
  fun s t hs ht => h s t (fun x hx => hCB (hs x hx)) (fun x hx => hCB (ht x hx))

/-- **Sidon property**, membership form: if `a + b = c + d` with all four elements in a `B_2`-set
`B`, then `a` is one of `c`, `d`. -/
theorem sidon_mem_left {B : Finset ℕ} (hB : BkSet.IsBkSeq 2 B) {a b c d : ℕ}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B) (hd : d ∈ B) (h : a + b = c + d) :
    a = c ∨ a = d := by
  have hm1 : ∀ x ∈ ({a, b} : Multiset ℕ), x ∈ B := by
    intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact ha
    rw [Multiset.mem_singleton.mp hx]
    exact hb
  have hm2 : ∀ x ∈ ({c, d} : Multiset ℕ), x ∈ B := by
    intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact hc
    rw [Multiset.mem_singleton.mp hx]
    exact hd
  have hsum : ({a, b} : Multiset ℕ).sum = ({c, d} : Multiset ℕ).sum := by
    simpa using h
  have heq := hB {a, b} {c, d} hm1 hm2 (by simp) (by simp) hsum
  have hmem : a ∈ ({c, d} : Multiset ℕ) := heq ▸ (by simp : a ∈ ({a, b} : Multiset ℕ))
  rcases Multiset.mem_cons.mp hmem with h' | h'
  · exact Or.inl h'
  · exact Or.inr (Multiset.mem_singleton.mp h')

/-- **Sidon property**: the second summand is determined as well. -/
theorem sidon_mem_right {B : Finset ℕ} (hB : BkSet.IsBkSeq 2 B) {a b c d : ℕ}
    (ha : a ∈ B) (hb : b ∈ B) (hc : c ∈ B) (hd : d ∈ B) (h : a + b = c + d) :
    b = c ∨ b = d := by
  have hm1 : ∀ x ∈ ({a, b} : Multiset ℕ), x ∈ B := by
    intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact ha
    rw [Multiset.mem_singleton.mp hx]
    exact hb
  have hm2 : ∀ x ∈ ({c, d} : Multiset ℕ), x ∈ B := by
    intro x hx
    rcases Multiset.mem_cons.mp hx with rfl | hx
    · exact hc
    rw [Multiset.mem_singleton.mp hx]
    exact hd
  have hsum : ({a, b} : Multiset ℕ).sum = ({c, d} : Multiset ℕ).sum := by
    simpa using h
  have heq := hB {a, b} {c, d} hm1 hm2 (by simp) (by simp) hsum
  have hmem : b ∈ ({c, d} : Multiset ℕ) := heq ▸ (by simp : b ∈ ({a, b} : Multiset ℕ))
  rcases Multiset.mem_cons.mp hmem with h' | h'
  · exact Or.inl h'
  · exact Or.inr (Multiset.mem_singleton.mp h')

/-- The (nonzero) differences inside a `B_2`-set are unique: `b₁ - b₁' = b₂ - b₂' ≠ 0` forces
`b₁ = b₂` (and then also `b₁' = b₂'`). -/
theorem diff_unique {B : Finset ℕ} (hB : BkSet.IsBkSeq 2 B) {b₁ b₁' b₂ b₂' : ℕ}
    (h1 : b₁ ∈ B) (h1' : b₁' ∈ B) (h2 : b₂ ∈ B) (h2' : b₂' ∈ B)
    (hb₁ : b₁' ≤ b₁) (hb₂ : b₂' ≤ b₂) (h : b₁ - b₁' = b₂ - b₂') (hne : b₁ - b₁' ≠ 0) :
    b₁ = b₂ := by
  set c := b₁ - b₁' with hc
  have hc0 : 0 < c := Nat.pos_of_ne_zero hne
  have e1 : b₁ = b₁' + c := by omega
  have e2 : b₂ = b₂' + c := by omega
  have hsum : b₁ + b₂' = b₂ + b₁' := by omega
  rcases sidon_mem_left hB h1 h2' h2 h1' hsum with h' | h'
  · exact h'
  · exact absurd (by omega : c = 0) (Nat.pos_iff_ne_zero.mp hc0)

/-! ### The sets `C`, `B'` and `A` of the proof of Theorem 4 -/

/-- `C`: the chain values that are differences of two elements of `B`. -/
def diffSet (c : AddChain) (B : Finset ℕ) : Finset ℕ :=
  (chainVals c).filter fun x => ∃ b ∈ B, ∃ b' ∈ B, b = b' + x

theorem mem_diffSet {c : AddChain} {B : Finset ℕ} {x : ℕ} :
    x ∈ diffSet c B ↔ x ∈ chainVals c ∧ ∃ b ∈ B, ∃ b' ∈ B, b = b' + x := by
  simp only [diffSet, Finset.mem_filter]

/-- `B'`: the elements of `B` that are obtained from another element of `B` by adding a chain
difference. -/
def hitSet (c : AddChain) (B : Finset ℕ) : Finset ℕ :=
  B.filter fun b => ∃ x ∈ diffSet c B, ∃ b' ∈ B, b = b' + x

theorem mem_hitSet {c : AddChain} {B : Finset ℕ} {b : ℕ} :
    b ∈ hitSet c B ↔ b ∈ B ∧ ∃ x ∈ diffSet c B, ∃ b' ∈ B, b = b' + x := by
  simp only [hitSet, Finset.mem_filter]

/-- `A`: the summands occurring in the chain steps that produce an element of `B \ B'`. -/
def splitSet (c : AddChain) (B : Finset ℕ) : Finset ℕ :=
  (chainVals c).filter fun x => ∃ b ∈ B, b ∉ hitSet c B ∧ ∃ z ∈ chainVals c, x + z = b

theorem mem_splitSet {c : AddChain} {B : Finset ℕ} {x : ℕ} :
    x ∈ splitSet c B ↔
      x ∈ chainVals c ∧ ∃ b ∈ B, b ∉ hitSet c B ∧ ∃ z ∈ chainVals c, x + z = b := by
  simp only [splitSet, Finset.mem_filter]

/-- A chain difference is never an element of the sum-free set `B`. -/
theorem not_mem_diffSet_of_mem {c : AddChain} {B : Finset ℕ} (hsf : SumFree B) {x : ℕ}
    (hx : x ∈ B) : x ∉ diffSet c B := by
  intro h
  obtain ⟨-, b, hb, b', hb', hbx⟩ := mem_diffSet.mp h
  exact hsf b' hb' x hx (hbx ▸ hb)

/-- A summand from `A` is never an element of the sum-free set `B`. -/
theorem not_mem_splitSet_of_mem {c : AddChain} {B : Finset ℕ} (hsf : SumFree B) {x : ℕ}
    (hx : x ∈ B) : x ∉ splitSet c B := by
  intro h
  obtain ⟨-, b, hb, hb', z, hz, hxz⟩ := mem_splitSet.mp h
  have hbz : b = x + z := by omega
  by_cases hzB : z ∈ B
  · exact hsf x hx z hzB (hbz ▸ hb)
  · exact hb' (mem_hitSet.mpr ⟨hb, z, mem_diffSet.mpr ⟨hz, b, hb, x, hx, hbz⟩, x, hx, hbz⟩)

/-- The map sending `b ∈ B'` to the chain difference `b - b'` is injective, so `|B'| ≤ |C|`. -/
theorem hitSet_card_le_diffSet (c : AddChain) (B : Finset ℕ) (hB : BkSet.IsBkSeq 2 B) :
    (hitSet c B).card ≤ (diffSet c B).card := by
  classical
  have hex : ∀ b ∈ hitSet c B, ∃ x ∈ diffSet c B, ∃ b' ∈ B, b = b' + x :=
    fun b hb => (mem_hitSet.mp hb).2
  set φ : ℕ → ℕ := fun b => if h : b ∈ hitSet c B then Classical.choose (hex b h) else 0 with hφ
  have hφ_apply : ∀ b (hb : b ∈ hitSet c B), φ b = Classical.choose (hex b hb) := by
    intro b hb
    rw [hφ]
    exact dif_pos hb
  have hspec : ∀ b (hb : b ∈ hitSet c B), φ b ∈ diffSet c B ∧ ∃ b' ∈ B, b = b' + φ b := by
    intro b hb
    rw [hφ_apply b hb]
    exact Classical.choose_spec (hex b hb)
  have hinj : Set.InjOn φ ↑(hitSet c B) := by
    intro b₁ hb₁ b₂ hb₂ heq
    obtain ⟨-, b₁', hb₁'B, h₁⟩ := hspec b₁ hb₁
    obtain ⟨-, b₂', hb₂'B, h₂⟩ := hspec b₂ hb₂
    have hpos : 0 < φ b₁ := by
      have := one_le_chainVals (mem_diffSet.mp (hspec b₁ hb₁).1).1
      omega
    have hd : b₁ - b₁' = b₂ - b₂' := by omega
    have hne : b₁ - b₁' ≠ 0 := by omega
    exact diff_unique hB (mem_hitSet.mp hb₁).1 hb₁'B (mem_hitSet.mp hb₂).1 hb₂'B
      (by omega) (by omega) hd hne
  calc (hitSet c B).card = ((hitSet c B).image φ).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (diffSet c B).card := Finset.card_le_card fun x hx => by
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
        exact (hspec b hb).1

/-- `1` is never a chain difference inside a sum-free set: a difference of two elements of `B` is
at least `2`. -/
theorem one_notMem_hitSet {c : AddChain} {B : Finset ℕ} (hsf : SumFree B) : 1 ∉ hitSet c B := by
  intro h
  obtain ⟨-, x, hx, b', hb', hbx⟩ := mem_hitSet.mp h
  have hx1 : 1 ≤ x := one_le_chainVals (mem_diffSet.mp hx).1
  have hb'1 : 1 ≤ b' := by
    rcases Nat.eq_zero_or_pos b' with h0 | h0
    · subst h0
      exact absurd hb' (hsf 0 hb' 0 hb')
    · omega
  omega

/-- Every element of `B \ (B' ∪ {1})` is the sum of two elements of `A`.  The initial value `1` has
to be excluded: it is the only element of `B` that no chain step produces. -/
theorem sdiff_hitSet_subset (c : AddChain) (B : Finset ℕ) (hc : c.Computes B) :
    B \ (hitSet c B ∪ {1}) ⊆ BkSet.minkowskiSum (splitSet c B) (splitSet c B) := by
  intro b hb
  obtain ⟨hbB, hbh⟩ := Finset.mem_sdiff.mp hb
  have hbh' : b ∉ hitSet c B := fun h => hbh (Finset.mem_union_left _ h)
  have hb1 : b ≠ 1 := by
    intro h
    refine hbh ?_
    rw [h]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self 1)
  have hexk : ∃ k < c.L, c.y k = b := by
    rcases hc b hbB with h | h
    · exact absurd h hb1
    · exact h
  obtain ⟨k, hkL, hky⟩ := hexk
  obtain ⟨x, z, hxz⟩ := c.valid k hkL
  have hmem : ∀ u : Option (Fin k), npPool c.y k u ∈ chainVals c := by
    intro u
    rcases u with _ | ⟨j, hj⟩
    · rw [npPool_none]
      exact mem_chainVals.mpr (Or.inl rfl)
    · rw [npPool_some]
      exact mem_chainVals.mpr (Or.inr ⟨j, lt_trans hj hkL, rfl⟩)
  have hxV := hmem x
  have hzV := hmem z
  have hsum : b = npPool c.y k x + npPool c.y k z := by rw [← hky]; exact hxz
  rw [BkSet.mem_minkowskiSum]
  refine ⟨npPool c.y k x, ?_, npPool c.y k z, ?_, hsum.symm⟩
  · rw [mem_splitSet]
    exact ⟨hxV, b, hbB, hbh', npPool c.y k z, hzV, hsum.symm⟩
  · rw [mem_splitSet]
    refine ⟨hzV, b, hbB, hbh', npPool c.y k x, hxV, ?_⟩
    rw [add_comm]
    exact hsum.symm

/-- The counting step of Theorem 4: `|B \ {1}| ≤ 5 |A ∪ C|^{1 + 1/k}`.  The initial `1` is free and
is the only element of `B` that the argument does not account for. -/
theorem card_le (c : AddChain) {B : Finset ℕ} (hc : c.Computes B) (k : ℕ) (hk : 2 ≤ k)
    (hsf : SumFree B) (hBk : BkSet.IsBkSeq k B) :
    ((B.erase 1).card : ℝ) ≤ 5 * (((diffSet c B ∪ splitSet c B).card : ℝ) ^ (1 + (k : ℝ)⁻¹)) := by
  classical
  set D := diffSet c B with hD
  set A := splitSet c B with hA
  set m : ℕ := (D ∪ A).card with hm
  set e : ℝ := 1 + (k : ℝ)⁻¹ with he
  have he1 : 1 ≤ e := by
    rw [he]
    have h : (0 : ℝ) ≤ (k : ℝ)⁻¹ := by positivity
    linarith
  have he0 : 0 < e := lt_of_lt_of_le one_pos he1
  have h2 : BkSet.IsBkSeq 2 B := hBk.mono (by omega)
  have hsub : (B.erase 1) \ hitSet c B ⊆ B := by
    intro x hx
    exact Finset.mem_of_mem_erase (Finset.mem_sdiff.mp hx).1
  have hsplit : (((B.erase 1) \ hitSet c B).card : ℝ) ≤ (A.card : ℝ) ^ e + 3 * (A.card : ℝ) := by
    have hsum : ∀ b ∈ (B.erase 1) \ hitSet c B, ∃ a ∈ A, ∃ a' ∈ A, a + a' = b := by
      intro b hb
      obtain ⟨hbE, hbh⟩ := Finset.mem_sdiff.mp hb
      have hbne : b ≠ 1 := Finset.ne_of_mem_erase hbE
      have hmem : b ∈ B \ (hitSet c B ∪ {1}) := by
        rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
        exact ⟨Finset.mem_of_mem_erase hbE,
          fun h => h.elim hbh (fun h1 => hbne h1)⟩
      have := sdiff_hitSet_subset c B hc hmem
      rwa [BkSet.mem_minkowskiSum] at this
    have := BkSet.statement1' A ((B.erase 1) \ hitSet c B) k (by omega) hsum
      (isBkSeq_subset hBk hsub)
    simpa [he] using this
  have hhit : hitSet c B ⊆ B.erase 1 := by
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨fun h => one_notMem_hitSet hsf (h ▸ hx), Finset.filter_subset _ _ hx⟩
  have hcard : ((B.erase 1).card : ℝ)
      = ((hitSet c B).card : ℝ) + (((B.erase 1) \ hitSet c B).card : ℝ) := by
    have h := Finset.card_sdiff_add_card_eq_card hhit
    rw [← h]
    push_cast
    ring
  have hB' : ((hitSet c B).card : ℝ) ≤ (D.card : ℝ) := by
    exact_mod_cast hitSet_card_le_diffSet c B h2
  have hDm : (D.card : ℝ) ≤ (m : ℝ) := by
    have : D.card ≤ m := by rw [hm]; exact Finset.card_le_card Finset.subset_union_left
    exact_mod_cast this
  have hAm : (A.card : ℝ) ≤ (m : ℝ) := by
    have : A.card ≤ m := by rw [hm]; exact Finset.card_le_card Finset.subset_union_right
    exact_mod_cast this
  have hAe : (A.card : ℝ) ^ e ≤ (m : ℝ) ^ e :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hAm (le_of_lt he0)
  have hm_le : (m : ℝ) ≤ (m : ℝ) ^ e := by
    rcases Nat.eq_zero_or_pos m with hmz | hmp
    · rw [hmz]
      simp [Real.zero_rpow he0.ne']
    · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmp
      have h := Real.rpow_le_rpow_of_exponent_le (x := (m : ℝ)) hm1 he1
      rwa [Real.rpow_one] at h
  have h3A : 3 * (A.card : ℝ) ≤ 3 * (m : ℝ) ^ e := by
    rcases Nat.eq_zero_or_pos m with hmz | hmp
    · have hA0 : A.card = 0 := by
        have : A.card ≤ m := by rw [hm]; exact Finset.card_le_card Finset.subset_union_right
        omega
      rw [hA0, hmz]
      simp [Real.zero_rpow he0.ne']
    · nlinarith [hm_le]
  have hbound : ((B.erase 1).card : ℝ) ≤ (m : ℝ) + ((A.card : ℝ) ^ e + 3 * (A.card : ℝ)) := by
    linarith
  have : ((B.erase 1).card : ℝ) ≤ 5 * (m : ℝ) ^ e := by linarith
  simpa [hD, hA, hm, he] using this

/-- **Theorem 4**, for an arbitrary chain computing `B`.  No hypothesis on `1` is needed: the sharp
form of the statement has `|B \ {1}|` in the power. -/
theorem theorem4_chain (k : ℕ) (hk : 2 ≤ k) {B : Finset ℕ} (c : AddChain) (hc : c.Computes B)
    (hsf : SumFree B) (hBk : BkSet.IsBkSeq k B) :
    (B.card : ℝ) + (1 / 5) * ((B.erase 1).card : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)) ≤
      (c.L : ℝ) + 1 := by
  classical
  set D := diffSet c B with hD
  set A := splitSet c B with hA
  set m : ℕ := (D ∪ A).card with hm
  set e : ℝ := 1 + (k : ℝ)⁻¹ with he
  set r : ℝ := (k : ℝ) / ((k : ℝ) + 1) with hr
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have he1 : 1 ≤ e := by
    rw [he]
    have h : (0 : ℝ) ≤ (k : ℝ)⁻¹ := by positivity
    linarith
  have he0 : 0 < e := lt_of_lt_of_le one_pos he1
  have hr0 : 0 < r := by
    rw [hr]
    exact div_pos hkR (by linarith)
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one (by linarith : (0 : ℝ) < (k : ℝ) + 1)]
    linarith
  have her : e * r = 1 := by
    have hk0 : (k : ℝ) ≠ 0 := hkR.ne'
    have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
    rw [he, hr]
    field_simp
  -- the counting estimate `|B| + |A ∪ C| ≤ L + 1`
  have hcount : B.card + m ≤ c.L + 1 := by
    have hdisj : Disjoint B (D ∪ A) := by
      rw [Finset.disjoint_left]
      intro x hxB hx
      rcases Finset.mem_union.mp hx with h' | h'
      · exact not_mem_diffSet_of_mem hsf hxB h'
      · exact not_mem_splitSet_of_mem hsf hxB h'
    have hsub1 : B ⊆ chainVals c := AddChain.subset_chainVals hc
    have hsub2 : D ∪ A ⊆ chainVals c :=
      Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hunion : (B ∪ (D ∪ A)).card = B.card + (D ∪ A).card :=
      Finset.card_union_of_disjoint hdisj
    have h2' : (B ∪ (D ∪ A)).card ≤ (chainVals c).card :=
      Finset.card_le_card (Finset.union_subset hsub1 hsub2)
    have h3' : (chainVals c).card ≤ c.L + 1 := by
      have h1' : (chainVals c).card ≤ ((Finset.range c.L).image c.y).card + 1 :=
        Finset.card_insert_le _ _
      have h2'' : ((Finset.range c.L).image c.y).card ≤ c.L := by
        simpa using Finset.card_image_le (s := Finset.range c.L) (f := c.y)
      omega
    rw [hm, ← hunion]
    omega
  -- the counting step `|B \ {1}| ≤ 5 |A ∪ C|^{1 + 1/k}`
  have hbound : ((B.erase 1).card : ℝ) ≤ 5 * (m : ℝ) ^ e := by
    have hcl := card_le c hc k hk hsf hBk
    simpa [hD, hA, hm, he] using hcl
  have hE0 : (0 : ℝ) ≤ ((B.erase 1).card : ℝ) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  -- extracting the power of `|B \ {1}|`
  have hstep : (((B.erase 1).card : ℝ) / 5) ^ r ≤ (m : ℝ) := by
    have h1 : (((B.erase 1).card : ℝ) / 5) ^ r ≤ ((m : ℝ) ^ e) ^ r :=
      Real.rpow_le_rpow (by positivity) (by linarith) (le_of_lt hr0)
    have h2 : ((m : ℝ) ^ e) ^ r = (m : ℝ) ^ (e * r) := (Real.rpow_mul hm0 e r).symm
    rw [h2, her, Real.rpow_one] at h1
    exact h1
  have h5r : (5 : ℝ) ^ r ≤ 5 := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (5 : ℝ)) (by norm_num) hr1
    simpa using h
  have hfin : (1 / 5) * ((B.erase 1).card : ℝ) ^ r ≤ (m : ℝ) := by
    have h5pos : (0 : ℝ) < (5 : ℝ) ^ r := Real.rpow_pos_of_pos (by norm_num) r
    have hcmp : ((B.erase 1).card : ℝ) ^ r / 5 ≤ ((B.erase 1).card : ℝ) ^ r / (5 : ℝ) ^ r :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hE0 r) h5pos h5r
    calc (1 / 5) * ((B.erase 1).card : ℝ) ^ r = ((B.erase 1).card : ℝ) ^ r / 5 := by ring
      _ ≤ ((B.erase 1).card : ℝ) ^ r / (5 : ℝ) ^ r := hcmp
      _ = (((B.erase 1).card : ℝ) / 5) ^ r := (Real.div_rpow hE0 (by norm_num) r).symm
      _ ≤ (m : ℝ) := hstep
  have hcm : (B.card : ℝ) + (m : ℝ) ≤ (c.L : ℝ) + 1 := by
    have h : ((B.card + m : ℕ) : ℝ) ≤ (c.L : ℝ) + 1 := by exact_mod_cast hcount
    push_cast at h
    linarith
  linarith

/-- A sum-free set of natural numbers does not contain `0`, so all its elements are at least `1`. -/
theorem one_le_of_sumFree {B : Finset ℕ} (hsf : SumFree B) : ∀ a ∈ B, 1 ≤ a := by
  intro a ha
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  · subst ha0
    exact absurd ha (hsf 0 ha 0 ha)
  · omega

/-- **Theorem 4** of the notes, sharp form, with no condition on `1`:
`|B| + (1/5) |B \ {1}|^{k/(k+1)} ≤ L(B) + 1` for a sum-free `B_k`-set `B` and `2 ≤ k`. -/
theorem theorem4 (k : ℕ) (hk : 2 ≤ k) {B : Finset ℕ} (hsf : SumFree B)
    (hBk : BkSet.IsBkSeq k B) :
    (B.card : ℝ) + (1 / 5) * ((B.erase 1).card : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)) ≤
      (setL B : ℝ) + 1 := by
  obtain ⟨c, hL, hc⟩ := exists_optimal (one_le_of_sumFree hsf)
  rw [← hL]
  exact theorem4_chain k hk c hc hsf hBk

/-- Theorem 4 in the shape of the paper, for sets not containing `1`. -/
theorem theorem4_chain_of_notMem_one (k : ℕ) (hk : 2 ≤ k) {B : Finset ℕ} (c : AddChain)
    (hc : c.Computes B) (hsf : SumFree B) (hBk : BkSet.IsBkSeq k B) (h1 : 1 ∉ B) :
    (B.card : ℝ) + (1 / 5) * (B.card : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)) ≤ (c.L : ℝ) + 1 := by
  have h := theorem4_chain k hk c hc hsf hBk
  rwa [Finset.erase_eq_of_notMem h1] at h

/-- Theorem 4 in the shape of the paper, with no condition on `1`: dropping `1 ∉ B` costs the
constant `1/5`, and this is sharp — `B = {1}` has `L = 0` and `|B| = 1`. -/
theorem theorem4_chain_six_fifths (k : ℕ) (hk : 2 ≤ k) {B : Finset ℕ} (c : AddChain)
    (hc : c.Computes B) (hsf : SumFree B) (hBk : BkSet.IsBkSeq k B) :
    (B.card : ℝ) + (1 / 5) * (B.card : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)) ≤ (c.L : ℝ) + 6 / 5 := by
  set r : ℝ := (k : ℝ) / ((k : ℝ) + 1) with hr
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hr0 : 0 ≤ r := by
    rw [hr]
    exact le_of_lt (div_pos hkR (by linarith))
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one (by linarith : (0 : ℝ) < (k : ℝ) + 1)]
    linarith
  have hmain := theorem4_chain k hk c hc hsf hBk
  have hErNat : B.card ≤ (B.erase 1).card + 1 := by
    have := Finset.pred_card_le_card_erase (s := B) (a := 1)
    omega
  have hEr : (B.card : ℝ) ≤ ((B.erase 1).card : ℝ) + 1 := by exact_mod_cast hErNat
  have hpow : (B.card : ℝ) ^ r ≤ ((B.erase 1).card : ℝ) ^ r + 1 := by
    have h1 : (B.card : ℝ) ^ r ≤ (((B.erase 1).card : ℝ) + 1) ^ r :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hEr hr0
    have h2 : (((B.erase 1).card : ℝ) + 1) ^ r
        ≤ ((B.erase 1).card : ℝ) ^ r + (1 : ℝ) ^ r :=
      Real.rpow_add_le_add_rpow (Nat.cast_nonneg _) (by norm_num) hr0 hr1
    rw [Real.one_rpow] at h2
    linarith
  linarith

/-- Theorem 4 in the shape of the paper, for sets not containing `1`. -/
theorem theorem4_of_notMem_one (k : ℕ) (hk : 2 ≤ k) {B : Finset ℕ} (hsf : SumFree B)
    (hBk : BkSet.IsBkSeq k B) (h1 : 1 ∉ B) :
    (B.card : ℝ) + (1 / 5) * (B.card : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)) ≤ (setL B : ℝ) + 1 := by
  have h := theorem4 k hk hsf hBk
  rwa [Finset.erase_eq_of_notMem h1] at h

/-- Theorem 4 in the shape of the paper, with no condition at all on `1`: the only price of allowing
`1 ∈ B` is the additive constant `1/5`, and it is attained by `B = {1}`. -/
theorem theorem4_six_fifths (k : ℕ) (hk : 2 ≤ k) {B : Finset ℕ} (hsf : SumFree B)
    (hBk : BkSet.IsBkSeq k B) :
    (B.card : ℝ) + (1 / 5) * (B.card : ℝ) ^ ((k : ℝ) / ((k : ℝ) + 1)) ≤
      (setL B : ℝ) + 6 / 5 := by
  obtain ⟨c, hL, hc⟩ := exists_optimal (one_le_of_sumFree hsf)
  rw [← hL]
  exact theorem4_chain_six_fifths k hk c hc hsf hBk

end Theorem4
