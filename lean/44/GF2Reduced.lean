import Mathlib

/-!
# Reduced complexity and direct sums over `GF(2)`

This module formalizes Section 2 of `lower_lin4.pdf` (I. S. Sergeev, *Lower bounds on the
additive complexity of linear operators and bilinear algorithms...*):

* extended circuits/chains, the *type* of an element (its coefficient vector at the
  inessential variables) and the *reduced complexity* `L*` of a circuit and of a matrix;
* direct sums `A1 ⊞ A2` of matrices;
* Lemma 1: `L*(A1 ⊞ A2) = L*(A1) + L*(A2)` and `L(A1 ⊞ A2) ≥ L(A1) + L*(A2)`;
* Theorem 1: `L*(A) ≤ 2m + n` for every `m × n` matrix over `GF(2)` (the second half of the
  file constructs the witnessing extended chain and bounds its reduced complexity).

The definitions are phrased for vector addition chains, which are equivalent to the
(unbounded fan-in) additive circuits of Section 1.  An extended chain is a chain over `m`
variables together with a finite set `aux` of *inessential* variables: the type of a step
is the projection of its vector onto `aux`.

The file is self-contained: its only import is `Mathlib`.

## Contents

1. Vectors, chains and circuits over `GF(2)`: the basic material of Section 1 -- vectors,
   addition chains, additive circuits, the chain `C.toChain` of a circuit, the counting
   inequality, and the star circuit of a matrix.
2. Reduced complexity, direct sums of matrices, and the two inequalities of Lemma 1.
3. Compressing a vector addition chain: the construction behind Theorem 1.

-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## Part 1: vectors, chains and circuits over `GF(2)` -/

namespace AchainsComplexityGF2

open scoped BigOperators

/-! ### Vectors over `GF(2)` -/

/-- Vectors of dimension `n` over `GF(2) = ZMod 2`. -/
abbrev Vec (n : ℕ) := Fin n → (ZMod 2)

/-- The `i`-th standard basis vector `eᵢ = (0,…,0,1,0,…,0)`, with a `1` in position `i`
and zeros elsewhere. -/
def basisVec {n : ℕ} (i : Fin n) : Vec n := fun j => if j = i then 1 else 0

@[simp] theorem basisVec_apply {n : ℕ} (i j : Fin n) :
    basisVec i j = if j = i then (1 : (ZMod 2)) else 0 := rfl

/-! ### Vector addition chains -/

/-- The vectors available to an addition chain at step `k`: the basis vectors
`e₁,…,eₙ` together with the earlier vectors `y₁,…,y_{k-1}`. -/
def chainPool {n L : ℕ} (y : Fin L → Vec n) (k : ℕ) (hk : k ≤ L) : Fin n ⊕ Fin k → Vec n
  | Sum.inl i => basisVec i
  | Sum.inr j => y ⟨j.1, lt_of_lt_of_le j.2 hk⟩

/-- A vector addition chain in `(ZMod 2)ⁿ`, i.e. a sequence `e₁,…,eₙ, y₁,…,y_L` in which every
`y_k` is the sum of two vectors available strictly earlier (a basis vector or some `y_j`
with `j < k`). -/
structure VecAddChain (n : ℕ) where

  L : ℕ

  y : Fin L → Vec n

  valid : ∀ k : Fin L, ∃ a b : Fin n ⊕ Fin k.1,
    y k = chainPool y k.1 (le_of_lt k.2) a + chainPool y k.1 (le_of_lt k.2) b

/-- A vector addition chain `c` computes a matrix `A` of size `m × n` if every row of `A`
occurs among the basis vectors `eᵢ`, the computed vectors `y_k`, or is the zero vector. -/
def VecAddChain.Computes {m n : ℕ} (c : VecAddChain n) (A : Matrix (Fin m) (Fin n) (ZMod 2)) : Prop :=
  ∀ i : Fin m, A i ∈ Set.range basisVec ∪ Set.range c.y ∪ {0}

/-- The additive complexity `L(A)` defined through addition chains: the length of the
shortest chain computing `A` (and `0` if no chain computes `A`). -/
noncomputable def chainComplexity {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) : ℕ :=
  sInf { l | ∃ c : VecAddChain n, c.L = l ∧ c.Computes A }

/-! ### Additive circuits -/

/-- An unbounded fan-in additive circuit over `(ZMod 2)ⁿ`. Vertices are `Fin N`; the first `n`
vertices are inputs representing `e₁,…,eₙ`; every non-input vertex carries a list of
incoming edges (parallel edges are allowed, their order is irrelevant). Acyclicity is
enforced by orienting every edge from a lower-indexed to a higher-indexed vertex.

A circuit is required to be *reduced*: every non-input vertex has at least one incoming
edge. -/
structure Circuit (n : ℕ) where

  N : ℕ

  hN : n ≤ N

  preds : Fin (N - n) → List (Fin N)

  acyclic : ∀ (t : Fin (N - n)) (u : Fin N), u ∈ preds t → u.1 < n + t.1

  reduced : ∀ t : Fin (N - n), 0 < (preds t).length

namespace Circuit

variable {n : ℕ}

/-- The vertex index of the `t`-th non-input vertex. -/
def idx (C : Circuit n) (t : Fin (C.N - n)) : Fin C.N :=
  ⟨n + t.1, by have := t.2; omega⟩

/-- The well-founded relation (by vertex index) used to define represented vectors. -/
abbrev vrel (C : Circuit n) : Fin C.N → Fin C.N → Prop := fun a b => a.1 < b.1

theorem vrel_wf (C : Circuit n) : WellFounded (C.vrel) :=
  (measure (fun v : Fin C.N => v.1)).wf

/-- The recursive step computing the `j`-th component of a represented vector: at an input
vertex the component is a basis-vector coefficient; at a non-input vertex it is the sum of
the components over the incoming edges. -/
noncomputable def foldStep (C : Circuit n) (j : Fin n) :
    (v : Fin C.N) → ((u : Fin C.N) → u.1 < v.1 → (ZMod 2)) → (ZMod 2) :=
  fun v ih =>
    if h : v.1 < n then (if j = (⟨v.1, h⟩ : Fin n) then (1 : (ZMod 2)) else 0)
    else
      ∑ i : Fin (C.preds ⟨v.1 - n, by omega⟩).length,
        ih ((C.preds ⟨v.1 - n, by omega⟩).get i)
          (by
            have hac := C.acyclic ⟨v.1 - n, by omega⟩ _
              (List.get_mem (C.preds ⟨v.1 - n, by omega⟩) i)
            have hc : (⟨v.1 - n, by omega⟩ : Fin (C.N - n)).1 = v.1 - n := rfl
            have hv : n ≤ v.1 := by omega
            omega)

/-- The `j`-th component represented by a vertex of the circuit; also the number of oriented
paths from the `j`-th input to `v`. -/
noncomputable def comp (C : Circuit n) (j : Fin n) : Fin C.N → (ZMod 2) :=
  WellFounded.fix (C.vrel_wf) (C.foldStep j)

/-- The vector represented by a vertex of the circuit. -/
noncomputable def repr (C : Circuit n) (v : Fin C.N) : Vec n := fun j => C.comp j v

theorem comp_eq (C : Circuit n) (j : Fin n) (v : Fin C.N) :
    C.comp j v =
      (if h : v.1 < n then (if j = (⟨v.1, h⟩ : Fin n) then (1 : (ZMod 2)) else 0)
       else ∑ i : Fin (C.preds ⟨v.1 - n, by omega⟩).length,
              C.comp j ((C.preds ⟨v.1 - n, by omega⟩).get i)) := by
  unfold comp
  rw [WellFounded.fix_eq]
  rfl

/-- An input vertex represents the corresponding basis vector. -/
theorem repr_input (C : Circuit n) (i : Fin n) :
    C.repr ⟨i.1, lt_of_lt_of_le i.2 C.hN⟩ = basisVec i := by
  funext j
  show C.comp j ⟨i.1, lt_of_lt_of_le i.2 C.hN⟩ = basisVec i j
  rw [comp_eq, dif_pos (show (⟨i.1, lt_of_lt_of_le i.2 C.hN⟩ : Fin C.N).1 < n from i.2)]
  simp only [basisVec, Fin.val_mk, Fin.ext_iff]

/-- A non-input vertex represents the sum of the vectors of its predecessors. -/
theorem repr_idx (C : Circuit n) (t : Fin (C.N - n)) :
    C.repr (C.idx t) = ∑ i : Fin (C.preds t).length, C.repr ((C.preds t).get i) := by
  funext j
  show C.comp j (C.idx t) = (∑ i : Fin (C.preds t).length, C.repr ((C.preds t).get i)) j
  rw [comp_eq]
  have hlt : ¬ (C.idx t).1 < n := by simp only [idx, Fin.val_mk]; omega
  rw [dif_neg hlt]
  have hidx : (⟨(C.idx t).1 - n, by omega⟩ : Fin (C.N - n)) = t := by
    apply Fin.ext; simp only [Fin.val_mk, idx]; omega
  rw [hidx, Finset.sum_apply]
  rfl

/-- An additive circuit computes (represents) a matrix `A` if every row of `A` is represented
by some vertex of the circuit; the all-zero vector is assumed always represented (as in the
paper). -/
def Computes {m : ℕ} (C : Circuit n) (A : Matrix (Fin m) (Fin n) (ZMod 2)) : Prop :=
  ∀ i : Fin m, A i ∈ Set.range C.repr ∪ {0}

end Circuit

theorem castLE_sum {k : ℕ} (g : Fin k → ℕ) {m : ℕ} (hm : m ≤ k) :
    (∑ i : Fin m, g (Fin.castLE hm i))
      = ∑ i ∈ Finset.range m, (if h : i < k then g ⟨i, h⟩ else 0) := by
  have key : (∑ i : Fin m, g (Fin.castLE hm i))
      = ∑ i : Fin m, (fun x => if h : x < k then g ⟨x, h⟩ else 0) i.1 := by
    apply Finset.sum_congr rfl
    intro i _
    have hi : i.1 < k := lt_of_lt_of_le i.2 hm
    change g (Fin.castLE hm i) = (if h : i.1 < k then g ⟨i.1, h⟩ else 0)
    rw [dif_pos hi]
    exact congrArg g (Fin.ext rfl)
  rw [key, Fin.sum_univ_eq_sum_range (fun x => if h : x < k then g ⟨x, h⟩ else 0) m]

theorem pos_lt_same {k : ℕ} (g : Fin k → ℕ) (t : Fin k) {a b : Fin (g t)} (h : a < b) :
    finSigmaFinEquiv (⟨t, a⟩ : Sigma (fun i : Fin k => Fin (g i)))
      < finSigmaFinEquiv (⟨t, b⟩ : Sigma (fun i : Fin k => Fin (g i))) := by
  rw [Fin.lt_def, finSigmaFinEquiv_apply, finSigmaFinEquiv_apply]
  simp only
  omega

theorem pos_lt_cross {k : ℕ} (g : Fin k → ℕ) {s t : Fin k} (hst : s.1 < t.1)
    (j' : Fin (g s)) (j : Fin (g t)) :
    finSigmaFinEquiv (⟨s, j'⟩ : Sigma (fun i : Fin k => Fin (g i)))
      < finSigmaFinEquiv (⟨t, j⟩ : Sigma (fun i : Fin k => Fin (g i))) := by
  have hle : s.1 ≤ t.1 := le_of_lt hst
  rw [Fin.lt_def, finSigmaFinEquiv_apply, finSigmaFinEquiv_apply,
    castLE_sum g s.2.le, castLE_sum g t.2.le]
  show (∑ i ∈ Finset.range s.1, (if h : i < k then g ⟨i, h⟩ else 0)) + j'.1
      < (∑ i ∈ Finset.range t.1, (if h : i < k then g ⟨i, h⟩ else 0)) + j.1
  have hsplit : (∑ i ∈ Finset.range t.1, (if h : i < k then g ⟨i, h⟩ else 0))
      = (∑ i ∈ Finset.range s.1, (if h : i < k then g ⟨i, h⟩ else 0))
        + ∑ i ∈ Finset.range (t.1 - s.1),
            (fun x => if h : x < k then g ⟨x, h⟩ else 0) (s.1 + i) := by
    rw [← Finset.sum_range_add (fun x => if h : x < k then g ⟨x, h⟩ else 0) s.1 (t.1 - s.1),
      Nat.add_sub_of_le hle]
  have hmem : (0 : ℕ) ∈ Finset.range (t.1 - s.1) := Finset.mem_range.mpr (by omega)
  have hge : g s ≤ ∑ i ∈ Finset.range (t.1 - s.1),
            (fun x => if h : x < k then g ⟨x, h⟩ else 0) (s.1 + i) := by
    have h1 : (fun x => if h : x < k then g ⟨x, h⟩ else 0) (s.1 + 0) ≤
        ∑ i ∈ Finset.range (t.1 - s.1),
          (fun x => if h : x < k then g ⟨x, h⟩ else 0) (s.1 + i) :=
      Finset.single_le_sum (s := Finset.range (t.1 - s.1))
        (f := fun i => (fun x => if h : x < k then g ⟨x, h⟩ else 0) (s.1 + i))
        (fun i _ => Nat.zero_le _) hmem
    have h2 : (fun x => if h : x < k then g ⟨x, h⟩ else 0) (s.1 + 0) = g s := by
      show (if h : s.1 + 0 < k then g ⟨s.1 + 0, h⟩ else 0) = g s
      rw [dif_pos (show s.1 + 0 < k by omega)]
      exact congrArg g (Fin.ext rfl)
    rwa [h2] at h1
  have hj : j'.1 < ∑ i ∈ Finset.range (t.1 - s.1),
      (fun x => if h : x < k then g ⟨x, h⟩ else 0) (s.1 + i) := lt_of_lt_of_le j'.2 hge
  rw [hsplit]
  rw [Nat.add_assoc]
  exact Nat.add_lt_add_left (lt_of_lt_of_le hj (Nat.le_add_right _ _)) _

namespace Circuit

variable {n : ℕ}

def gsteps (C : Circuit n) (t : Fin (C.N - n)) : ℕ := (C.preds t).length - 1

theorem gsteps_add (C : Circuit n) (t : Fin (C.N - n)) :
    C.gsteps t + 1 = (C.preds t).length :=
  Nat.sub_add_cancel (C.reduced t)

def stepsTotal (C : Circuit n) : ℕ := ∑ t : Fin (C.N - n), C.gsteps t

noncomputable def step (C : Circuit n) (t : Fin (C.N - n)) (i : Fin (C.gsteps t)) :
    Fin C.stepsTotal := finSigmaFinEquiv ⟨t, i⟩

noncomputable def acc (C : Circuit n) (t : Fin (C.N - n)) (i : ℕ) : Vec n :=
  ∑ j ∈ Finset.range i,
    (if hj : j < (C.preds t).length then C.repr ((C.preds t).get ⟨j, hj⟩) else 0)

noncomputable def chainY (C : Circuit n) (k : Fin C.stepsTotal) : Vec n :=
  let d := finSigmaFinEquiv.symm k
  C.acc d.1 (d.2.1 + 2)

@[simp] theorem acc_zero (C : Circuit n) (t : Fin (C.N - n)) : C.acc t 0 = 0 := by
  simp [acc]

theorem acc_succ (C : Circuit n) (t : Fin (C.N - n)) (i : ℕ) :
    C.acc t (i + 1) = C.acc t i +
      (if hj : i < (C.preds t).length then C.repr ((C.preds t).get ⟨i, hj⟩) else 0) := by
  unfold acc
  rw [Finset.sum_range_succ]

theorem acc_succ_of_lt (C : Circuit n) (t : Fin (C.N - n)) {i : ℕ}
    (h : i < (C.preds t).length) :
    C.acc t (i + 1) = C.acc t i + C.repr ((C.preds t).get ⟨i, h⟩) := by
  rw [acc_succ, dif_pos h]

theorem chainY_step (C : Circuit n) (t : Fin (C.N - n)) (i : Fin (C.gsteps t)) :
    C.chainY (C.step t i) = C.acc t (i.1 + 2) := by
  unfold chainY step
  rw [Equiv.symm_apply_apply]

theorem repr_idx_eq_acc (C : Circuit n) (t : Fin (C.N - n)) :
    C.repr (C.idx t) = C.acc t (C.preds t).length := by
  rw [repr_idx]
  unfold acc
  have key : (∑ x : Fin (C.preds t).length, C.repr ((C.preds t).get x))
      = ∑ j : Fin (C.preds t).length,
          (fun x => if hj : x < (C.preds t).length then
              C.repr ((C.preds t).get ⟨x, hj⟩) else 0) j.1 := by
    apply Finset.sum_congr rfl
    intro i _
    change C.repr ((C.preds t).get i)
      = (if hj : i.1 < (C.preds t).length then C.repr ((C.preds t).get ⟨i.1, hj⟩) else 0)
    rw [dif_pos i.2]
  rw [key, Fin.sum_univ_eq_sum_range
    (fun x => if hj : x < (C.preds t).length then
      C.repr ((C.preds t).get ⟨x, hj⟩) else 0) (C.preds t).length]

variable {n : ℕ}

theorem repr_lt_repr_pool (C : Circuit n) (t : Fin (C.N - n)) (i : Fin (C.gsteps t)) :
    ∀ (u : Fin C.N), u.1 < n + t.1 →
      ∃ a : Fin n ⊕ Fin (C.step t i).1,
        chainPool C.chainY (C.step t i).1 (le_of_lt (C.step t i).2) a = C.repr u := by
  intro u
  induction u using C.vrel_wf.induction with
  | _ u ih =>
    intro hu
    by_cases hin : u.1 < n
    · refine ⟨Sum.inl ⟨u.1, hin⟩, ?_⟩
      have hR : C.repr u = basisVec ⟨u.1, hin⟩ :=
        (congrArg C.repr (Fin.ext rfl : u = (⟨u.1, lt_of_lt_of_le hin C.hN⟩ : Fin C.N))).trans
          (C.repr_input ⟨u.1, hin⟩)
      rw [hR]
      rfl
    · set tu : Fin (C.N - n) := ⟨u.1 - n, by omega⟩ with htu
      have hval : u.1 = n + tu.1 := by simp only [htu, Fin.val_mk]; omega
      have hidx : C.idx tu = u := by
        apply Fin.ext; simp only [idx, htu, Fin.val_mk]; omega
      by_cases hlen : (C.preds tu).length = 1
      · have h0 : 0 < (C.preds tu).length := C.reduced tu
        have hrepr : C.repr u = C.repr ((C.preds tu).get ⟨0, h0⟩) := by
          rw [← hidx, repr_idx]
          refine Finset.sum_eq_single (⟨0, h0⟩ : Fin (C.preds tu).length) ?_ ?_
          · intro b _ hb
            exfalso; apply hb
            apply Fin.ext
            have hb2 := b.2
            simp only [Fin.val_zero]
            omega
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hrepr]
        have hpredlt : ((C.preds tu).get ⟨0, h0⟩).1 < n + t.1 := by
          have hlt := C.acyclic tu _ (List.get_mem (C.preds tu) ⟨0, h0⟩)
          have : n + tu.1 < n + t.1 := by rw [← hval]; exact hu
          omega
        have hpred_lt_u : ((C.preds tu).get ⟨0, h0⟩).1 < u.1 := by
          have hlt := C.acyclic tu _ (List.get_mem (C.preds tu) ⟨0, h0⟩)
          omega
        exact ih _ hpred_lt_u hpredlt
      · have hq : 2 ≤ (C.preds tu).length := by
          have := C.reduced tu; omega
        let i' : Fin (C.gsteps tu) := ⟨C.gsteps tu - 1, by simp only [gsteps]; omega⟩
        have hrepr : C.repr u = C.chainY (C.step tu i') := by
          rw [← hidx, C.repr_idx_eq_acc tu, C.chainY_step tu i']
          congr 1
          have hg := C.gsteps_add tu
          simp only [i']
          omega
        have hst : tu.1 < t.1 := by simp only [htu, Fin.val_mk]; omega
        have hlt : (C.step tu i').1 < (C.step t i).1 :=
          Fin.lt_def.mp (pos_lt_cross C.gsteps hst i' i)
        refine ⟨Sum.inr ⟨(C.step tu i').1, hlt⟩, ?_⟩
        have hcp : chainPool C.chainY (C.step t i).1 (le_of_lt (C.step t i).2)
              (Sum.inr ⟨(C.step tu i').1, hlt⟩) = C.chainY (C.step tu i') := by
          show C.chainY (⟨(C.step tu i').1, _⟩ : Fin C.stepsTotal) = C.chainY (C.step tu i')
          exact congrArg C.chainY (Fin.ext rfl)
        rw [hcp, ← hrepr]

theorem acc_pool (C : Circuit n) (t : Fin (C.N - n)) (i : Fin (C.gsteps t)) :
    ∃ a : Fin n ⊕ Fin (C.step t i).1,
      chainPool C.chainY (C.step t i).1 (le_of_lt (C.step t i).2) a = C.acc t (i.1 + 1) := by
  by_cases hz : i.1 = 0
  · have h1 : C.acc t (i.1 + 1) = C.repr ((C.preds t).get ⟨0, C.reduced t⟩) := by
      rw [hz, acc_succ_of_lt (C := C) (t := t) (i := 0) (C.reduced t)]
      simp
    obtain ⟨a, ha⟩ := C.repr_lt_repr_pool t i ((C.preds t).get ⟨0, C.reduced t⟩)
        (C.acyclic t _ (List.get_mem (C.preds t) ⟨0, C.reduced t⟩))
    exact ⟨a, ha.trans h1.symm⟩
  · have hi1 : 1 ≤ i.1 := by omega
    let i'' : Fin (C.gsteps t) := ⟨i.1 - 1, by have := i.2; simp only [gsteps] at this; omega⟩
    obtain ⟨a, ha⟩ : ∃ a : Fin n ⊕ Fin (C.step t i).1,
        chainPool C.chainY (C.step t i).1 (le_of_lt (C.step t i).2) a = C.chainY (C.step t i'') := by
      refine ⟨Sum.inr ⟨(C.step t i'').1, ?_⟩, ?_⟩
      · exact Fin.lt_def.mp (pos_lt_same C.gsteps t (show i'' < i from by rw [Fin.lt_def]; simp only [i'']; omega))
      · show C.chainY (⟨(C.step t i'').1, _⟩ : Fin C.stepsTotal) = C.chainY (C.step t i'')
        exact congrArg C.chainY (Fin.ext rfl)
    refine ⟨a, ?_⟩
    rw [ha, C.chainY_step t i'']
    rw [show i''.1 + 2 = i.1 + 1 from by simp only [i'']; omega]

theorem repr_mem_chainY (C : Circuit n) (u : Fin C.N) :
    C.repr u ∈ Set.range basisVec ∨ C.repr u ∈ Set.range C.chainY := by
  induction u using C.vrel_wf.induction with
  | _ u ih =>
    by_cases hin : u.1 < n
    · left
      refine ⟨⟨u.1, hin⟩, ?_⟩
      exact ((congrArg C.repr (Fin.ext rfl : u = (⟨u.1, lt_of_lt_of_le hin C.hN⟩ : Fin C.N))).trans
        (C.repr_input ⟨u.1, hin⟩)).symm
    · set tu : Fin (C.N - n) := ⟨u.1 - n, by omega⟩ with htu
      have hidx : C.idx tu = u := by apply Fin.ext; simp only [idx, htu, Fin.val_mk]; omega
      by_cases hlen : (C.preds tu).length = 1
      · have h0 : 0 < (C.preds tu).length := C.reduced tu
        have hrepr : C.repr u = C.repr ((C.preds tu).get ⟨0, h0⟩) := by
          rw [← hidx, repr_idx]
          refine Finset.sum_eq_single (⟨0, h0⟩ : Fin (C.preds tu).length) ?_ ?_
          · intro b _ hb; exfalso; apply hb; apply Fin.ext
            have := b.2; simp only [Fin.val_zero]; omega
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hrepr]
        have hval : u.1 = n + tu.1 := by simp only [htu, Fin.val_mk]; omega
        have hpred_lt_u : ((C.preds tu).get ⟨0, h0⟩).1 < u.1 := by
          have hlt := C.acyclic tu _ (List.get_mem (C.preds tu) ⟨0, h0⟩)
          omega
        exact ih _ hpred_lt_u
      · have hq : 2 ≤ (C.preds tu).length := by have := C.reduced tu; omega
        let i' : Fin (C.gsteps tu) := ⟨C.gsteps tu - 1, by simp only [gsteps]; omega⟩
        right
        refine ⟨C.step tu i', ?_⟩
        rw [C.chainY_step tu i', ← hidx, C.repr_idx_eq_acc tu]
        rw [show i'.1 + 2 = (C.preds tu).length from by have := C.gsteps_add tu; simp only [i']; omega]

noncomputable def toChain (C : Circuit n) : VecAddChain n where
  L := C.stepsTotal
  y := C.chainY
  valid := by
    intro k
    set d : Sigma (fun t : Fin (C.N - n) => Fin (C.gsteps t)) := finSigmaFinEquiv.symm k with hd
    have hk : C.step d.1 d.2 = k := by
      have h1 : C.step d.1 d.2 = finSigmaFinEquiv d := rfl
      rw [h1]
      exact (congrArg finSigmaFinEquiv hd).trans (Equiv.apply_symm_apply finSigmaFinEquiv k)
    rw [← hk, C.chainY_step]
    have hlt2 : d.2.1 + 1 < (C.preds d.1).length := by
      have := d.2.2; simp only [gsteps] at this; omega
    obtain ⟨b, hb⟩ := C.repr_lt_repr_pool d.1 d.2 ((C.preds d.1).get ⟨d.2.1 + 1, hlt2⟩)
        (C.acyclic d.1 _ (List.get_mem _ _))
    obtain ⟨a, ha⟩ := C.acc_pool d.1 d.2
    refine ⟨a, b, ?_⟩
    have htel : C.acc d.1 (d.2.1 + 2)
        = C.acc d.1 (d.2.1 + 1) + C.repr ((C.preds d.1).get ⟨d.2.1 + 1, hlt2⟩) := by
      rw [show d.2.1 + 2 = (d.2.1 + 1) + 1 from by omega,
        acc_succ_of_lt (C := C) (t := d.1) (i := d.2.1 + 1) hlt2]
    rw [htel, ha, hb]

theorem toChain_y (C : Circuit n) (k : Fin C.stepsTotal) : C.toChain.y k = C.chainY k := rfl

theorem toChain_computes {m : ℕ} (C : Circuit n) (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (hA : C.Computes A) : C.toChain.Computes A := by
  intro i
  rcases hA i with ⟨v, hv⟩ | h0
  · rcases C.repr_mem_chainY v with ⟨b, hb⟩ | ⟨kk, hkk⟩
    · exact Or.inl (Or.inl ⟨b, hb.trans hv⟩)
    · exact Or.inl (Or.inr ⟨kk, by rw [toChain_y]; exact hkk.trans hv⟩)
  · exact Or.inr h0

end Circuit

/-- A lower bound of the `sInf` of a set of naturals, valid even when the set is empty
(in which case the `sInf` is `0` and we additionally require `a = 0`). -/
theorem le_sInf_of_forall {s : Set ℕ} {a : ℕ} (h0 : s = ∅ → a = 0)
    (h : ∀ b ∈ s, a ≤ b) : a ≤ sInf s := by
  by_cases hs : s = ∅
  · have hz : a = 0 := h0 hs
    rw [hs, hz]; simp
  · exact h _ (Nat.sInf_mem (Set.nonempty_iff_ne_empty.mpr hs))

/-! ### The set of lengths of the chains computing a matrix -/

/-- Lengths of vector addition chains computing `A`. -/
def ChainSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) : Set ℕ :=
  { l | ∃ c : VecAddChain n, c.L = l ∧ c.Computes A }

@[simp] theorem chainComplexity_eq_sInf {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    chainComplexity A = sInf (ChainSet A) := rfl

namespace Circuit

variable {n : ℕ}

/-- The input vertex corresponding to the `j`-th basis vector. -/
def inputVertex (C : Circuit n) (j : Fin n) : Fin C.N := ⟨j.1, lt_of_lt_of_le j.2 C.hN⟩

variable {n : ℕ}

variable {n : ℕ} {C : Circuit n} {m : ℕ} {ρ : Fin m → Fin C.N}

/-! ### The counting inequality -/

theorem sum_get_map {α β : Type*} [AddCommMonoid β] (l : List α) (f : α → β) :
    (∑ i : Fin l.length, f (l.get i)) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  have h : (List.ofFn (fun i : Fin l.length => f (l.get i))) = List.map f (List.ofFn l.get) :=
    (List.map_ofFn).symm
  rw [h, List.ofFn_get]

/-! ### The star circuit -/

/-- In `(ZMod 2)`, a nonzero element is one. -/
theorem zmod2_eq_one_of_ne_zero (x : (ZMod 2)) (h : x ≠ 0) : x = 1 := by
  have hv := ZMod.val_lt x
  have h' : x.val = 0 ∨ x.val = 1 := by omega
  rcases h' with h0 | h1
  · exact absurd (by rw [← ZMod.natCast_zmod_val x, h0]; norm_num) h
  · rw [← ZMod.natCast_zmod_val x, h1]
    norm_num

/-- The predecessor list of the `t`-th non-input vertex of the star circuit: the input
vertices `j` with `A t j = 1`. -/
noncomputable def starPreds {m : ℕ} (A : Matrix (Fin m) (Fin n) ((ZMod 2))) (t : Fin m) :
    List (Fin (n + m)) :=
  ((List.finRange n).filter (fun j => A t j ≠ 0)).map
    (fun j => ⟨j.1, lt_of_lt_of_le j.2 (Nat.le_add_right n m)⟩)

theorem starPreds_mem_lt {m : ℕ} (A : Matrix (Fin m) (Fin n) ((ZMod 2))) (t : Fin m)
    {u : Fin (n + m)} (hu : u ∈ starPreds A t) : u.1 < n := by
  rw [starPreds, List.mem_map] at hu
  obtain ⟨j, -, rfl⟩ := hu
  exact j.2

/-- The star circuit of a matrix with no zero row: one non-input vertex per row, whose
incoming edges are the inputs carrying a `1` in that row. -/
noncomputable def star {m : ℕ} (A : Matrix (Fin m) (Fin n) ((ZMod 2)))
    (hrow : ∀ i, ∃ j, A i j ≠ 0) : Circuit n where
  N := n + m
  hN := Nat.le_add_right n m
  preds := fun t => starPreds A (Fin.cast (by simp) t)
  acyclic := by
    intro t u hu
    have h1 : u.1 < n := starPreds_mem_lt A (Fin.cast (by simp) t) hu
    have h2 := t.2
    omega
  reduced := by
    intro t
    obtain ⟨j0, hj0⟩ := hrow (Fin.cast (by simp) t)
    rw [starPreds]
    apply List.length_pos_of_mem
    exact List.mem_map.mpr ⟨j0,
      (List.mem_filter.mpr ⟨List.mem_finRange j0, decide_eq_true_eq.mpr hj0⟩), rfl⟩

theorem star_preds {m : ℕ} (A : Matrix (Fin m) (Fin n) ((ZMod 2)))
    (hrow : ∀ i, ∃ j, A i j ≠ 0) (t : Fin m) :
    (star A hrow).preds (Fin.cast (by simp : m = (n + m) - n) t) = starPreds A t := by
  show starPreds A (Fin.cast (by simp) (Fin.cast (by simp : m = (n + m) - n) t)) = starPreds A t
  rw [show Fin.cast (by simp : (n + m) - n = m)
        (Fin.cast (by simp : m = (n + m) - n) t) = t from Fin.ext (by simp)]

/-- An input vertex represents the corresponding basis vector, in the `comp` formulation. -/
theorem comp_inputVertex (C : Circuit n) (i j : Fin n) :
    C.comp i (C.inputVertex j) = if i = j then (1 : (ZMod 2)) else 0 := by
  rw [Circuit.comp_eq, dif_pos (show (C.inputVertex j).1 < n from j.2)]
  have hfin : (⟨(C.inputVertex j).1, show (C.inputVertex j).1 < n from j.2⟩ : Fin n) = j :=
    Fin.ext rfl
  rw [hfin]

/-- The vertex of the star circuit representing row `t`. -/
noncomputable def starRow {m : ℕ} (A : Matrix (Fin m) (Fin n) ((ZMod 2)))
    (hrow : ∀ i, ∃ j, A i j ≠ 0) (t : Fin m) : Fin (n + m) :=
  ⟨n + t.1, by have := t.2; omega⟩

theorem star_repr {m : ℕ} (A : Matrix (Fin m) (Fin n) ((ZMod 2)))
    (hrow : ∀ i, ∃ j, A i j ≠ 0) (t : Fin m) :
    (star A hrow).repr (starRow A hrow t) = A t := by
  funext i
  show (star A hrow).comp i (starRow A hrow t) = A t i
  have hidx : (star A hrow).idx (Fin.cast (by simp : m = (n + m) - n) t)
      = starRow A hrow t := by
    apply Fin.ext
    show n + (Fin.cast (by simp : m = (n + m) - n) t).1 = n + t.1
    rfl
  have hstep : (star A hrow).comp i (starRow A hrow t)
      = ∑ x : Fin (starPreds A t).length,
          (star A hrow).comp i ((starPreds A t).get x) := by
    have h := congrFun (Circuit.repr_idx (C := star A hrow)
      (t := Fin.cast (by simp : m = (n + m) - n) t)) i
    rw [star_preds A hrow t, hidx] at h
    simp only [Circuit.repr, Finset.sum_apply] at h
    exact h
  rw [hstep]
  let l := (List.finRange n).filter (fun j => A t j ≠ 0)
  have hl : l.Nodup := (List.nodup_finRange n).filter _
  have hmap : (∑ x : Fin (starPreds A t).length,
      (star A hrow).comp i ((starPreds A t).get x))
      = (l.map (fun j => (star A hrow).comp i
          ⟨j.1, lt_of_lt_of_le j.2 (Nat.le_add_right n m)⟩)).sum := by
    have hstar : starPreds A t = l.map
        (fun j => ⟨j.1, lt_of_lt_of_le j.2 (Nat.le_add_right n m)⟩) := rfl
    refine (sum_get_map (starPreds A t)
      (fun u => (star A hrow).comp i u)).trans ?_
    rw [hstar]
    simp only [List.map_map, Function.comp_apply]
    rfl
  rw [hmap]
  have hterm : ∀ j ∈ l, (star A hrow).comp i
      ⟨j.1, lt_of_lt_of_le j.2 (Nat.le_add_right n m)⟩ = if i = j then (1 : (ZMod 2)) else 0 := by
    intro j _
    exact comp_inputVertex (C := star A hrow) i j
  rw [List.map_congr_left hterm]
  rw [List.sum_map_eq_nsmul_single i (fun j => if i = j then (1 : (ZMod 2)) else 0)]
  · have hcount : l.count i = if A t i ≠ 0 then 1 else 0 := by
      by_cases h : A t i ≠ 0
      · rw [if_pos h, List.count_eq_one_of_mem hl]
        exact List.mem_filter.mpr ⟨List.mem_finRange i, decide_eq_true_eq.mpr h⟩
      · rw [if_neg h, List.count_eq_zero_of_not_mem]
        intro hi
        exact h (decide_eq_true_eq.mp (List.mem_filter.mp hi).2)
    rw [hcount]
    by_cases h : A t i ≠ 0
    · rw [if_pos h, if_pos rfl, one_smul]
      exact (zmod2_eq_one_of_ne_zero (A t i) h).symm
    · rw [if_neg h]
      exact (not_not.mp h).symm
  · intro a' ha' _
    rw [if_neg (Ne.symm ha')]

/-- The star circuit computes its matrix. -/
theorem star_computes {m : ℕ} (A : Matrix (Fin m) (Fin n) ((ZMod 2)))
    (hrow : ∀ i, ∃ j, A i j ≠ 0) : (star A hrow).Computes A := by
  intro i
  exact Or.inl ⟨starRow A hrow i, star_repr A hrow i⟩

end Circuit

/-! ## Part 2: reduced complexity and direct sums over `GF(2)` -/

/-! ### Projections, supports and weights -/

/-- Projection of a vector onto the coordinates in `W`; all other coordinates are set to `0`. -/
def proj {m : ℕ} (W : Finset (Fin m)) (v : Vec m) : Vec m :=
  fun i => if i ∈ W then v i else 0

@[simp] theorem proj_apply_mem {m : ℕ} (W : Finset (Fin m)) (v : Vec m) {i : Fin m}
    (hi : i ∈ W) : proj W v i = v i := by
  simp [proj, hi]

@[simp] theorem proj_apply_not_mem {m : ℕ} (W : Finset (Fin m)) (v : Vec m) {i : Fin m}
    (hi : i ∉ W) : proj W v i = 0 := by
  simp [proj, hi]

@[simp] theorem proj_zero {m : ℕ} (W : Finset (Fin m)) : proj W (0 : Vec m) = 0 := by
  funext i
  by_cases hi : i ∈ W <;> simp [proj, hi]

theorem proj_add {m : ℕ} (W : Finset (Fin m)) (u v : Vec m) :
    proj W (u + v) = proj W u + proj W v := by
  funext i
  by_cases hi : i ∈ W <;> simp [proj, hi]

theorem proj_idem {m : ℕ} (W : Finset (Fin m)) (v : Vec m) : proj W (proj W v) = proj W v := by
  funext i
  by_cases hi : i ∈ W <;> simp [proj, hi]

theorem proj_congr {m : ℕ} (W : Finset (Fin m)) {u v : Vec m}
    (h : ∀ i ∈ W, u i = v i) : proj W u = proj W v := by
  funext i
  by_cases hi : i ∈ W
  · simp [proj, hi, h i hi]
  · simp [proj, hi]

theorem proj_eq_iff {m : ℕ} (W : Finset (Fin m)) {u v : Vec m} :
    proj W u = proj W v ↔ ∀ i ∈ W, u i = v i := by
  constructor
  · intro h i hi
    have := congrFun h i
    simpa [proj, hi] using this
  · intro h; exact proj_congr W h

@[simp] theorem proj_basisVec {m : ℕ} (W : Finset (Fin m)) (i : Fin m) :
    proj W (basisVec i) = if i ∈ W then basisVec i else 0 := by
  funext j
  by_cases hi : i ∈ W
  · by_cases hj : j ∈ W
    · simp [proj, basisVec, hi, hj]
    · have hji : j ≠ i := fun h => hj (h ▸ hi)
      simp [proj, basisVec, hi, hj, hji]
  · by_cases hj : j ∈ W
    · have hji : j ≠ i := fun h => hi (h ▸ hj)
      simp [proj, basisVec, hi, hj, hji]
    · simp [proj, hi, hj]

/-- Weight of a vector relative to a set of coordinates: the number of nonzero entries. -/
def weight {m : ℕ} (W : Finset (Fin m)) (v : Vec m) : ℕ :=
  (W.filter (fun i => v i ≠ 0)).card

theorem weight_proj {m : ℕ} (W : Finset (Fin m)) (v : Vec m) :
    weight W (proj W v) = weight W v := by
  unfold weight
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [proj_apply_mem W v hi]

theorem weight_eq_zero_iff {m : ℕ} (W : Finset (Fin m)) (v : Vec m) :
    weight W v = 0 ↔ proj W v = 0 := by
  constructor
  · intro h
    have h0 : (W.filter (fun i => v i ≠ 0)).card = 0 := h
    funext i
    by_cases hi : i ∈ W
    · rw [proj_apply_mem W v hi]
      by_contra hne
      have hmem : i ∈ W.filter (fun i => v i ≠ 0) := Finset.mem_filter.mpr ⟨hi, hne⟩
      have hpos : 0 < (W.filter (fun i => v i ≠ 0)).card := Finset.card_pos.mpr ⟨i, hmem⟩
      omega
    · rw [proj_apply_not_mem W v hi]
      rfl
  · intro h
    unfold weight
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro i hi
    have hh := congrFun h i
    rw [proj_apply_mem W v hi] at hh
    have hv : v i = 0 := by simpa using hh
    rw [hv]
    simp

theorem weight_le_one_basis {m : ℕ} (W : Finset (Fin m)) (i : Fin m) :
    weight W (basisVec i) ≤ 1 := by
  unfold weight
  have hsub : W.filter (fun j => basisVec i j ≠ 0) ⊆ {i} := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_singleton]
    by_contra hji
    exact hj.2 (by simp [basisVec, hji])
  calc (W.filter (fun j => basisVec i j ≠ 0)).card ≤ ({i} : Finset (Fin m)).card :=
        Finset.card_le_card hsub
    _ ≤ 1 := by simp

theorem proj_eq_basisVec_of_weight_eq_one {m : ℕ} (W : Finset (Fin m)) (v : Vec m)
    (h : weight W v = 1) : ∃ i, proj W v = basisVec i := by
  unfold weight at h
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h
  have hmem : i ∈ W.filter (fun j => v j ≠ 0) := by rw [hi]; simp
  rw [Finset.mem_filter] at hmem
  refine ⟨i, ?_⟩
  funext j
  by_cases hj : j ∈ W
  · rw [proj_apply_mem W v hj]
    by_cases hji : j = i
    · subst hji
      have hv : v j = 1 := Circuit.zmod2_eq_one_of_ne_zero (v j) hmem.2
      simp [basisVec, hv]
    · have hnot : j ∉ W.filter (fun j => v j ≠ 0) := by
        rw [hi]; simp [hji]
      rw [Finset.mem_filter] at hnot
      have hv : v j = 0 := by
        by_contra hne
        exact hnot ⟨hj, hne⟩
      simp [basisVec, hji, hv]
  · have hji : j ≠ i := fun hji => hj (hji ▸ hmem.1)
    rw [proj_apply_not_mem W v hj]
    simp [basisVec, hji]

theorem proj_eq_zero_or_basisVec_of_weight_le_one {m : ℕ} (W : Finset (Fin m)) (v : Vec m)
    (h : weight W v ≤ 1) : proj W v = 0 ∨ ∃ i, proj W v = basisVec i := by
  rcases Nat.eq_zero_or_pos (weight W v) with h0 | hpos
  · exact Or.inl ((weight_eq_zero_iff W v).mp h0)
  · have h1 : weight W v = 1 := by omega
    exact Or.inr (proj_eq_basisVec_of_weight_eq_one W v h1)

/-! ### Extended chains, types and reduced complexity -/

/-- An *extended* vector addition chain over `m` variables, together with a finite set `aux`
of inessential variables.  The chain itself is an ordinary chain over the `m` basis vectors;
the variables in `aux` are the ones on which the computed operator is allowed to depend
inessentially.  The fields `L`, `y`, `valid` are those of the underlying chain (kept flat so
that the length of a direct sum is literally the sum of the lengths). -/
structure ExtChain (m : ℕ) where
  /-- the number of elements of the chain -/
  L : ℕ
  /-- the vectors computed by the steps of the chain -/
  y : Fin L → Vec m
  /-- every step is the sum of two available vectors -/
  valid : ∀ k : Fin L, ∃ a b : Fin m ⊕ Fin k.1,
    y k = chainPool y k.1 (le_of_lt k.2) a + chainPool y k.1 (le_of_lt k.2) b
  /-- the inessential variables -/
  aux : Finset (Fin m)

namespace ExtChain

variable {m : ℕ}

/-- The underlying ordinary vector addition chain of an extended chain. -/
def toChain (c : ExtChain m) : VecAddChain m where
  L := c.L
  y := c.y
  valid := c.valid

/-- Read an ordinary chain as an extended chain with prescribed inessential variables. -/
def ofChain (c : VecAddChain m) (aux : Finset (Fin m)) : ExtChain m where
  L := c.L
  y := c.y
  valid := c.valid
  aux := aux

/-- The *type* of the `k`-th element: its coefficient vector at the inessential variables. -/
noncomputable abbrev stepType (c : ExtChain m) (k : Fin c.L) : Vec m :=
  proj c.aux (c.y k)

/-- The weight of the type of the `k`-th element. -/
noncomputable abbrev typeWeight (c : ExtChain m) (k : Fin c.L) : ℕ :=
  weight c.aux (c.y k)

/-- The elements whose type has weight at least `2`. -/
noncomputable abbrev heavySteps (c : ExtChain m) : Finset (Fin c.L) :=
  Finset.univ.filter (fun k => 2 ≤ c.typeWeight k)

/-- The set of distinct types of weight at least `2` occurring in the chain. -/
noncomputable abbrev typeSet (c : ExtChain m) : Finset (Vec m) :=
  c.heavySteps.image c.stepType

/-- The reduced complexity (приведенная сложность) of an extended chain:
the number of elements minus the number of distinct types of weight at least `2`. -/
noncomputable abbrev reducedComplexity (c : ExtChain m) : ℕ :=
  c.L - c.typeSet.card

theorem mem_heavySteps {c : ExtChain m} {k : Fin c.L} :
    k ∈ c.heavySteps ↔ 2 ≤ c.typeWeight k := by
  simp [heavySteps]

theorem typeWeight_eq_weight {c : ExtChain m} (k : Fin c.L) :
    c.typeWeight k = weight c.aux (c.stepType k) := by
  rw [typeWeight, stepType, weight_proj]

theorem typeSet_card_le_L (c : ExtChain m) : c.typeSet.card ≤ c.L := by
  calc c.typeSet.card ≤ c.heavySteps.card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin c.L)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = c.L := by rw [Finset.card_univ, Fintype.card_fin]

theorem reducedComplexity_le_L (c : ExtChain m) : c.reducedComplexity ≤ c.L :=
  Nat.sub_le _ _

/-- Extended chains with an empty set of inessential variables have reduced complexity equal
to their ordinary length. -/
theorem reducedComplexity_aux_empty (c : VecAddChain m) :
    (ExtChain.ofChain c ∅).reducedComplexity = c.L := by
  have hheavy : (ExtChain.ofChain c ∅).heavySteps = ∅ := by
    rw [← Finset.not_nonempty_iff_eq_empty]
    rintro ⟨k, hk⟩
    rw [mem_heavySteps] at hk
    change 2 ≤ weight (∅ : Finset (Fin m)) (c.y k) at hk
    have hz : weight (∅ : Finset (Fin m)) (c.y k) = 0 := by
      unfold weight; simp
    omega
  have hts : (ExtChain.ofChain c ∅).typeSet = ∅ := by simp [typeSet, hheavy]
  rw [reducedComplexity, hts]
  simp [ofChain]

end ExtChain

namespace ExtChain

variable {m : ℕ}

/-- An extended chain computes a matrix `A` (with `col` naming the essential variables) if every
row of `A` is represented by an input vertex, by a step, or is zero, and that representing
vector agrees with the row on the essential variables and vanishes on the inessential ones.
The last condition is the paper's requirement that the outputs do not depend on `Y`: an
output element computes `⟨a, X⟩ + ⟨b, Y⟩` with `b = 0`. -/
def Computes (c : ExtChain m) {k n : ℕ} (A : Matrix (Fin k) (Fin n) (ZMod 2))
    (col : Fin n → Fin m) : Prop :=
  Function.Injective col ∧ (∀ j, col j ∉ c.aux) ∧
    ∀ i : Fin k, ∃ w : Vec m,
      w ∈ Set.range (basisVec (n := m)) ∪ Set.range c.y ∪ ({0} : Set (Vec m)) ∧
      (∀ j : Fin n, w (col j) = A i j) ∧
      (∀ j ∈ c.aux, w j = 0)

/-- A representing vector of a row of a computed matrix. -/
theorem exists_rep {m k n : ℕ} {c : ExtChain m} {A : Matrix (Fin k) (Fin n) (ZMod 2)}
    {col : Fin n → Fin m} (h : c.Computes A col) (i : Fin k) :
    ∃ w : Vec m, w ∈ Set.range (basisVec (n := m)) ∪ Set.range c.y ∪ ({0} : Set (Vec m)) ∧
      (∀ j : Fin n, w (col j) = A i j) ∧ (∀ j ∈ c.aux, w j = 0) :=
  h.2.2 i

end ExtChain

/-- The reduced complexity `L*(A)` of a matrix: the minimum reduced complexity of an extended
chain computing `A`. -/
noncomputable def Lstar {k n : ℕ} (A : Matrix (Fin k) (Fin n) (ZMod 2)) : ℕ :=
  sInf { l | ∃ (m : ℕ) (c : ExtChain m) (col : Fin n → Fin m),
              c.Computes A col ∧ c.reducedComplexity = l }

theorem Lstar_le_of_computes {k n m : ℕ} {A : Matrix (Fin k) (Fin n) (ZMod 2)}
    (c : ExtChain m) (col : Fin n → Fin m) (h : c.Computes A col) :
    Lstar A ≤ c.reducedComplexity :=
  Nat.sInf_le ⟨m, c, col, h, rfl⟩

/-! ### Existence of an extended chain computing a given matrix -/

/-- Every matrix over `GF(2)` is computed by some vector addition chain. -/
theorem exists_chain_computes {k n : ℕ} (A : Matrix (Fin k) (Fin n) (ZMod 2)) :
    ∃ c : VecAddChain n, c.Computes A := by
  classical
  let ι := {i : Fin k // A i ≠ 0}
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let A' : Matrix (Fin (Fintype.card ι)) (Fin n) (ZMod 2) :=
    fun i j => A (e.symm i).1 j
  have hrow : ∀ i : Fin (Fintype.card ι), ∃ j, A' i j ≠ 0 := by
    intro i
    by_contra h
    push Not at h
    have h0 : A' i = 0 := funext h
    have hne : A (e.symm i).1 ≠ 0 := (e.symm i).2
    exact hne h0
  let C : Circuit n := Circuit.star A' hrow
  refine ⟨C.toChain, ?_⟩
  have hC : C.Computes A' := Circuit.star_computes A' hrow
  have hc : C.toChain.Computes A' := C.toChain_computes A' hC
  intro i
  by_cases hi : A i = 0
  · exact Or.inr hi
  · specialize hc (e ⟨i, hi⟩)
    rw [show A' (e ⟨i, hi⟩) = A i from by
      simp only [A', e, Equiv.symm_apply_apply]] at hc
    exact hc

theorem chainSet_nonempty {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    (ChainSet A).Nonempty := by
  obtain ⟨c, hc⟩ := exists_chain_computes A
  exact ⟨c.L, c, rfl, hc⟩

theorem Lstar_witness_nonempty {k n : ℕ} (A : Matrix (Fin k) (Fin n) (ZMod 2)) :
    { l | ∃ (m : ℕ) (c : ExtChain m) (col : Fin n → Fin m),
          c.Computes A col ∧ c.reducedComplexity = l }.Nonempty := by
  obtain ⟨c, hc⟩ := exists_chain_computes A
  refine ⟨c.L, n, ExtChain.ofChain c ∅, id, ?_, ?_⟩
  · refine ⟨Function.injective_id, ?_, ?_⟩
    · intro j; simp [ExtChain.ofChain]
    · intro i
      obtain h | h := hc i
      · exact ⟨_, Or.inl h, fun j => rfl, by intro j hj; simp [ExtChain.ofChain] at hj⟩
      · exact ⟨0, Or.inr (by simp), fun j => by rw [h]; rfl,
          by intro j hj; simp [ExtChain.ofChain] at hj⟩
  · rw [ExtChain.reducedComplexity_aux_empty]

/-- `L*(A) ≤ L(A)`: an ordinary chain is an extended chain with no inessential variables. -/
theorem Lstar_le_chainComplexity {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Lstar A ≤ chainComplexity A := by
  rw [chainComplexity_eq_sInf]
  refine le_sInf_of_forall ?_ ?_
  · intro h
    have hne := chainSet_nonempty A
    rw [h] at hne
    simp at hne
  · rintro l ⟨c, hL, hc⟩
    have hcomp : (ExtChain.ofChain c ∅).Computes A id := by
      refine ⟨Function.injective_id, ?_, ?_⟩
      · intro j; simp [ExtChain.ofChain]
      · intro i
        obtain h | h := hc i
        · exact ⟨_, Or.inl h, fun j => rfl, by intro j hj; simp [ExtChain.ofChain] at hj⟩
        · exact ⟨0, Or.inr (by simp), fun j => by rw [h]; rfl,
            by intro j hj; simp [ExtChain.ofChain] at hj⟩
    calc Lstar A ≤ (ExtChain.ofChain c ∅).reducedComplexity := Lstar_le_of_computes _ _ hcomp
      _ = c.L := ExtChain.reducedComplexity_aux_empty c
      _ = l := hL

/-! ### Direct sums of matrices -/

/-- The direct sum (block-diagonal matrix) `A ⊞ B`. -/
noncomputable def dsum {k1 n1 k2 n2 : ℕ}
    (A : Matrix (Fin k1) (Fin n1) (ZMod 2)) (B : Matrix (Fin k2) (Fin n2) (ZMod 2)) :
    Matrix (Fin (k1 + k2)) (Fin (n1 + n2)) (ZMod 2) :=
  fun i j => Fin.append
    (fun i1 => Fin.append (fun j1 => A i1 j1) (fun _ => 0) j)
    (fun i2 => Fin.append (fun _ => 0) (fun j2 => B i2 j2) j) i

@[simp] theorem dsum_castAdd_castAdd {k1 n1 k2 n2 : ℕ}
    (A : Matrix (Fin k1) (Fin n1) (ZMod 2)) (B : Matrix (Fin k2) (Fin n2) (ZMod 2))
    (i : Fin k1) (j : Fin n1) :
    dsum A B (Fin.castAdd k2 i) (Fin.castAdd n2 j) = A i j := by
  simp [dsum, Fin.append_left]

@[simp] theorem dsum_castAdd_natAdd {k1 n1 k2 n2 : ℕ}
    (A : Matrix (Fin k1) (Fin n1) (ZMod 2)) (B : Matrix (Fin k2) (Fin n2) (ZMod 2))
    (i : Fin k1) (j : Fin n2) :
    dsum A B (Fin.castAdd k2 i) (Fin.natAdd n1 j) = 0 := by
  simp [dsum, Fin.append_left, Fin.append_right]

@[simp] theorem dsum_natAdd_castAdd {k1 n1 k2 n2 : ℕ}
    (A : Matrix (Fin k1) (Fin n1) (ZMod 2)) (B : Matrix (Fin k2) (Fin n2) (ZMod 2))
    (i : Fin k2) (j : Fin n1) :
    dsum A B (Fin.natAdd k1 i) (Fin.castAdd n2 j) = 0 := by
  simp [dsum, Fin.append_right, Fin.append_left]

@[simp] theorem dsum_natAdd_natAdd {k1 n1 k2 n2 : ℕ}
    (A : Matrix (Fin k1) (Fin n1) (ZMod 2)) (B : Matrix (Fin k2) (Fin n2) (ZMod 2))
    (i : Fin k2) (j : Fin n2) :
    dsum A B (Fin.natAdd k1 i) (Fin.natAdd n1 j) = B i j := by
  simp [dsum, Fin.append_right]

/-! ### Combining chains: the direct sum construction -/

section Concat

variable {n1 n2 : ℕ}

/-- Embed a vector in the first block of `Vec (n1+n2)`. -/
noncomputable def emb1 (v : Vec n1) : Vec (n1 + n2) := Fin.append v 0

/-- Embed a vector in the second block of `Vec (n1+n2)`. -/
noncomputable def emb2 (v : Vec n2) : Vec (n1 + n2) := Fin.append 0 v

@[simp] theorem emb1_apply_castAdd (v : Vec n1) (j : Fin n1) :
    emb1 (n2 := n2) v (Fin.castAdd n2 j) = v j := by
  simp [emb1]

@[simp] theorem emb1_apply_natAdd (v : Vec n1) (j : Fin n2) :
    emb1 (n2 := n2) v (Fin.natAdd n1 j) = 0 := by
  simp [emb1]

@[simp] theorem emb2_apply_castAdd (v : Vec n2) (j : Fin n1) :
    emb2 (n1 := n1) v (Fin.castAdd n2 j) = 0 := by
  simp [emb2]

@[simp] theorem emb2_apply_natAdd (v : Vec n2) (j : Fin n2) :
    emb2 (n1 := n1) v (Fin.natAdd n1 j) = v j := by
  simp [emb2]

theorem emb1_add (u v : Vec n1) : emb1 (n2 := n2) (u + v) = emb1 u + emb1 v := by
  funext j
  induction j using Fin.addCases with
  | left i => simp
  | right i => simp

theorem emb2_add (u v : Vec n2) : emb2 (n1 := n1) (u + v) = emb2 u + emb2 v := by
  funext j
  induction j using Fin.addCases with
  | left i => simp
  | right i => simp

@[simp] theorem emb1_zero : emb1 (n2 := n2) (0 : Vec n1) = 0 := by
  funext j
  induction j using Fin.addCases with
  | left i => simp
  | right i => simp

@[simp] theorem emb2_zero : emb2 (n1 := n1) (0 : Vec n2) = 0 := by
  funext j
  induction j using Fin.addCases with
  | left i => simp
  | right i => simp

theorem emb1_basisVec (i : Fin n1) :
    emb1 (n2 := n2) (basisVec i) = basisVec (Fin.castAdd n2 i) := by
  funext j
  induction j using Fin.addCases with
  | left j =>
      simp only [emb1_apply_castAdd]
      by_cases h : j = i
      · subst h; simp [basisVec]
      · have h' : Fin.castAdd n2 j ≠ Fin.castAdd n2 i := by
          intro hh; exact h (by simpa using hh)
        simp [basisVec, h, h']
  | right j =>
      have hne : (Fin.natAdd n1 j : Fin (n1 + n2)) ≠ Fin.castAdd n2 i := by
        intro hh
        have hv := congrArg Fin.val hh
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
        have hi := i.isLt
        have hj := j.isLt
        omega
      simp [basisVec, hne]

theorem emb2_basisVec (i : Fin n2) :
    emb2 (n1 := n1) (basisVec i) = basisVec (Fin.natAdd n1 i) := by
  funext j
  induction j using Fin.addCases with
  | left j =>
      have hne : (Fin.castAdd n2 j : Fin (n1 + n2)) ≠ Fin.natAdd n1 i := by
        intro hh
        have hv := congrArg Fin.val hh
        simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
        have hi := i.isLt
        have hj := j.isLt
        omega
      simp [basisVec, hne]
  | right j =>
      simp only [emb2_apply_natAdd]
      by_cases h : j = i
      · subst h; simp [basisVec]
      · have h' : Fin.natAdd n1 j ≠ Fin.natAdd n1 i := by
          intro hh; exact h (by simpa using hh)
        simp [basisVec, h, h']

/-! ### Concatenating two chains -/

theorem castAdd_ne_natAdd {m n : ℕ} (i : Fin m) (j : Fin n) :
    (Fin.castAdd n i : Fin (m + n)) ≠ Fin.natAdd m j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  have hi := i.isLt
  omega

theorem castAdd_mem_image_union {A : Finset (Fin n1)} {B : Finset (Fin n2)} (i : Fin n1) :
    (Fin.castAdd n2 i ∈ A.image (Fin.castAdd n2) ∪ B.image (Fin.natAdd n1)) ↔ i ∈ A := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨i', hi', hii⟩ := Finset.mem_image.mp h
      rwa [Fin.castAdd_injective n1 n2 hii] at hi'
    · obtain ⟨j, _, hji⟩ := Finset.mem_image.mp h
      exact absurd hji.symm (castAdd_ne_natAdd i j)
  · intro h
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)

theorem natAdd_mem_image_union {A : Finset (Fin n1)} {B : Finset (Fin n2)} (j : Fin n2) :
    (Fin.natAdd n1 j ∈ A.image (Fin.castAdd n2) ∪ B.image (Fin.natAdd n1)) ↔ j ∈ B := by
  constructor
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨i, _, hij⟩ := Finset.mem_image.mp h
      exact absurd hij (castAdd_ne_natAdd i j)
    · obtain ⟨j', hj', hjj⟩ := Finset.mem_image.mp h
      rwa [Fin.natAdd_injective n2 n1 hjj] at hj'
  · intro h
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ h)

theorem emb1_injective : Function.Injective (emb1 (n2 := n2) : Vec n1 → Vec (n1 + n2)) := by
  intro u v h
  funext i
  have := congrFun h (Fin.castAdd n2 i)
  simpa using this

theorem emb2_injective : Function.Injective (emb2 (n1 := n1) : Vec n2 → Vec (n1 + n2)) := by
  intro u v h
  funext i
  have := congrFun h (Fin.natAdd n1 i)
  simpa using this

theorem proj_emb1 (A : Finset (Fin n1)) (B : Finset (Fin n2)) (v : Vec n1) :
    proj (A.image (Fin.castAdd n2) ∪ B.image (Fin.natAdd n1)) (emb1 (n2 := n2) v)
      = emb1 (n2 := n2) (proj A v) := by
  funext x
  induction x using Fin.addCases with
  | left i =>
      simp only [emb1_apply_castAdd, proj, castAdd_mem_image_union]
  | right j =>
      simp [proj, emb1]

theorem proj_emb2 (A : Finset (Fin n1)) (B : Finset (Fin n2)) (v : Vec n2) :
    proj (A.image (Fin.castAdd n2) ∪ B.image (Fin.natAdd n1)) (emb2 (n1 := n1) v)
      = emb2 (n1 := n1) (proj B v) := by
  funext x
  induction x using Fin.addCases with
  | left i => simp [proj, emb2]
  | right j =>
      simp only [emb2_apply_natAdd, proj, natAdd_mem_image_union]

theorem weight_emb1 (A : Finset (Fin n1)) (B : Finset (Fin n2)) (v : Vec n1) :
    weight (A.image (Fin.castAdd n2) ∪ B.image (Fin.natAdd n1)) (emb1 (n2 := n2) v)
      = weight A v := by
  unfold weight
  have hf : (A.image (Fin.castAdd n2) ∪ B.image (Fin.natAdd n1)).filter
        (fun x => emb1 (n2 := n2) v x ≠ 0)
      = (A.filter (fun i => v i ≠ 0)).image (Fin.castAdd n2) := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_filter, Finset.mem_union] at hx
      rcases hx with ⟨hxA | hxB, hx0⟩
      · rcases Finset.mem_image.mp hxA with ⟨i, hiA, rfl⟩
        exact Finset.mem_image.mpr ⟨i, by
          rw [Finset.mem_filter]
          exact ⟨hiA, by simpa using hx0⟩, rfl⟩
      · rcases Finset.mem_image.mp hxB with ⟨j, hjB, rfl⟩
        simp [emb1_apply_natAdd] at hx0
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_filter, Finset.mem_union]
      exact ⟨Or.inl (Finset.mem_image_of_mem _ hi.1), by simpa using hi.2⟩
  rw [hf, Finset.card_image_of_injective _ (Fin.castAdd_injective n1 n2)]

theorem weight_emb2 (A : Finset (Fin n1)) (B : Finset (Fin n2)) (v : Vec n2) :
    weight (A.image (Fin.castAdd n2) ∪ B.image (Fin.natAdd n1)) (emb2 (n1 := n1) v)
      = weight B v := by
  unfold weight
  have hf : (A.image (Fin.castAdd n2) ∪ B.image (Fin.natAdd n1)).filter
        (fun x => emb2 (n1 := n1) v x ≠ 0)
      = (B.filter (fun i => v i ≠ 0)).image (Fin.natAdd n1) := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_filter, Finset.mem_union] at hx
      rcases hx with ⟨hxA | hxB, hx0⟩
      · rcases Finset.mem_image.mp hxA with ⟨i, hiA, rfl⟩
        simp [emb2_apply_castAdd] at hx0
      · rcases Finset.mem_image.mp hxB with ⟨j, hjB, rfl⟩
        exact Finset.mem_image.mpr ⟨j, by
          rw [Finset.mem_filter]
          exact ⟨hjB, by simpa using hx0⟩, rfl⟩
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
      rw [Finset.mem_filter] at hi
      rw [Finset.mem_filter, Finset.mem_union]
      exact ⟨Or.inr (Finset.mem_image_of_mem _ hi.1), by simpa using hi.2⟩
  rw [hf, Finset.card_image_of_injective _ (Fin.natAdd_injective n2 n1)]

theorem ne_zero_of_two_le_weight {m : ℕ} {W : Finset (Fin m)} {v : Vec m}
    (h : 2 ≤ weight W v) : v ≠ 0 := by
  intro hv
  rw [hv] at h
  simp [weight] at h

/-- Map a summand of the pool of the first chain into the pool of the concatenation. -/
def poolMapLeft {k : ℕ} (s : Fin n1 ⊕ Fin k) : Fin (n1 + n2) ⊕ Fin k :=
  match s with
  | Sum.inl i => Sum.inl (Fin.castAdd n2 i)
  | Sum.inr j => Sum.inr j

/-- Map a summand of the pool of the second chain into the pool of the concatenation.
The parameter `off` is the offset (the length of the first chain) at which the second block
of steps starts. -/
def poolMapRight {k : ℕ} (off : ℕ) (s : Fin n2 ⊕ Fin k) : Fin (n1 + n2) ⊕ Fin (off + k) :=
  match s with
  | Sum.inl i => Sum.inl (Fin.natAdd n1 i)
  | Sum.inr j => Sum.inr ⟨off + j.1, by omega⟩

/-- The sequence of vectors of the concatenated chain. -/
noncomputable def appendY (c1 : VecAddChain n1) (c2 : VecAddChain n2) :
    Fin (c1.L + c2.L) → Vec (n1 + n2) :=
  Fin.append (fun k => emb1 (n2 := n2) (c1.y k))
    (fun k => emb2 (n1 := n1) (c2.y k))

@[simp] theorem appendY_castAdd (c1 : VecAddChain n1) (c2 : VecAddChain n2) (k : Fin c1.L) :
    appendY c1 c2 (Fin.castAdd c2.L k) = emb1 (n2 := n2) (c1.y k) := by
  simp [appendY]

@[simp] theorem appendY_natAdd (c1 : VecAddChain n1) (c2 : VecAddChain n2) (k : Fin c2.L) :
    appendY c1 c2 (Fin.natAdd c1.L k) = emb2 (n1 := n1) (c2.y k) := by
  simp [appendY]

theorem chainPool_appendY_left (c1 : VecAddChain n1) (c2 : VecAddChain n2)
    (k1 : Fin c1.L) (s : Fin n1 ⊕ Fin k1.val) :
    chainPool (appendY c1 c2) k1.val (by omega)
        (poolMapLeft (n2 := n2) s)
      = emb1 (n2 := n2) (chainPool c1.y k1.val (le_of_lt k1.2) s) := by
  cases s with
  | inl i => simpa [chainPool, poolMapLeft] using (emb1_basisVec (n1 := n1) (n2 := n2) i).symm
  | inr j =>
      simp only [chainPool, poolMapLeft]
      rw [show (⟨j.1, by omega⟩ : Fin (c1.L + c2.L))
            = Fin.castAdd c2.L (⟨j.1, lt_trans j.2 k1.2⟩ : Fin c1.L) from Fin.ext rfl,
        appendY_castAdd]

theorem chainPool_appendY_right (c1 : VecAddChain n1) (c2 : VecAddChain n2)
    (k2 : Fin c2.L) (s : Fin n2 ⊕ Fin k2.val) :
    chainPool (appendY c1 c2) (c1.L + k2.val) (by omega)
        (poolMapRight (n1 := n1) c1.L s)
      = emb2 (n1 := n1) (chainPool c2.y k2.val (le_of_lt k2.2) s) := by
  cases s with
  | inl i => simpa [chainPool, poolMapRight] using (emb2_basisVec (n1 := n1) i).symm
  | inr j =>
      simp only [chainPool, poolMapRight]
      rw [show (⟨c1.L + j.1, by omega⟩ : Fin (c1.L + c2.L))
            = Fin.natAdd c1.L (⟨j.1, lt_trans j.2 k2.2⟩ : Fin c2.L) from by
              apply Fin.ext; simp [Fin.natAdd],
        appendY_natAdd]

/-- Concatenate two vector addition chains, acting on the two blocks of `Vec (n1+n2)`. -/
noncomputable def VecAddChain.append (c1 : VecAddChain n1) (c2 : VecAddChain n2) :
    VecAddChain (n1 + n2) where
  L := c1.L + c2.L
  y := appendY c1 c2
  valid := by
    intro k
    induction k using Fin.addCases with
    | left k1 =>
        obtain ⟨a, b, hab⟩ := c1.valid k1
        refine ⟨poolMapLeft (n2 := n2) a, poolMapLeft (n2 := n2) b, ?_⟩
        rw [appendY_castAdd, hab, emb1_add]
        simp only [Fin.val_castAdd]
        rw [chainPool_appendY_left, chainPool_appendY_left]
    | right k2 =>
        obtain ⟨a, b, hab⟩ := c2.valid k2
        refine ⟨poolMapRight (n1 := n1) c1.L a, poolMapRight (n1 := n1) c1.L b, ?_⟩
        rw [appendY_natAdd, hab, emb2_add]
        simp only [Fin.val_natAdd]
        rw [chainPool_appendY_right, chainPool_appendY_right]

theorem dsum_apply_castAdd {k1 k2 : ℕ}
    (A1 : Matrix (Fin k1) (Fin n1) (ZMod 2)) (A2 : Matrix (Fin k2) (Fin n2) (ZMod 2))
    (i1 : Fin k1) :
    dsum A1 A2 (Fin.castAdd k2 i1) = emb1 (n2 := n2) (A1 i1) := by
  funext j
  simp only [dsum, emb1]
  rw [Fin.append_left]
  rfl

theorem dsum_apply_natAdd {k1 k2 : ℕ}
    (A1 : Matrix (Fin k1) (Fin n1) (ZMod 2)) (A2 : Matrix (Fin k2) (Fin n2) (ZMod 2))
    (i2 : Fin k2) :
    dsum A1 A2 (Fin.natAdd k1 i2) = emb2 (n1 := n1) (A2 i2) := by
  funext j
  simp only [dsum, emb2]
  rw [Fin.append_right]
  rfl

/-- The concatenation of chains computing `A1` and `A2` computes the direct sum `A1 ⊞ A2`. -/
theorem VecAddChain.append_computes {k1 k2 : ℕ} (c1 : VecAddChain n1) (c2 : VecAddChain n2)
    (A1 : Matrix (Fin k1) (Fin n1) (ZMod 2)) (A2 : Matrix (Fin k2) (Fin n2) (ZMod 2))
    (h1 : c1.Computes A1) (h2 : c2.Computes A2) :
    (c1.append c2).Computes (dsum A1 A2) := by
  intro i
  induction i using Fin.addCases with
  | left i1 =>
      rw [dsum_apply_castAdd]
      rcases h1 i1 with (⟨j, hj⟩ | ⟨t, ht⟩) | h0
      · refine Or.inl (Or.inl ⟨Fin.castAdd n2 j, ?_⟩)
        rw [← hj, emb1_basisVec]
      · refine Or.inl (Or.inr ⟨Fin.castAdd c2.L t, ?_⟩)
        change appendY c1 c2 (Fin.castAdd c2.L t) = emb1 (A1 i1)
        rw [appendY_castAdd, ← ht]
      · rw [h0]
        simp
  | right i2 =>
      rw [dsum_apply_natAdd]
      rcases h2 i2 with (⟨j, hj⟩ | ⟨t, ht⟩) | h0
      · refine Or.inl (Or.inl ⟨Fin.natAdd n1 j, ?_⟩)
        rw [← hj, emb2_basisVec]
      · refine Or.inl (Or.inr ⟨Fin.natAdd c1.L t, ?_⟩)
        change appendY c1 c2 (Fin.natAdd c1.L t) = emb2 (A2 i2)
        rw [appendY_natAdd, ← ht]
      · rw [h0]
        simp

end Concat

namespace ExtChain

/-! ### Concatenating extended chains: the direct-sum upper bound -/

variable {m1 m2 : ℕ}

/-- Concatenate two extended chains, keeping the inessential variables of the two summands in
separate blocks. -/
@[reducible] noncomputable def append (c1 : ExtChain m1) (c2 : ExtChain m2) :
    ExtChain (m1 + m2) where
  L := c1.L + c2.L
  y := appendY c1.toChain c2.toChain
  valid := (VecAddChain.append c1.toChain c2.toChain).valid
  aux := c1.aux.image (Fin.castAdd m2) ∪ c2.aux.image (Fin.natAdd m1)

theorem append_L (c1 : ExtChain m1) (c2 : ExtChain m2) : (c1.append c2).L = c1.L + c2.L := rfl

theorem append_stepType_castAdd (c1 : ExtChain m1) (c2 : ExtChain m2) (k : Fin c1.L) :
    (c1.append c2).stepType (Fin.castAdd c2.L k) = emb1 (n2 := m2) (c1.stepType k) := by
  show proj (c1.append c2).aux ((c1.append c2).y (Fin.castAdd c2.L k)) = _
  rw [show (c1.append c2).y (Fin.castAdd c2.L k)
        = emb1 (n2 := m2) (c1.y k) from appendY_castAdd c1.toChain c2.toChain k]
  exact proj_emb1 c1.aux c2.aux (c1.y k)

theorem append_stepType_natAdd (c1 : ExtChain m1) (c2 : ExtChain m2) (k : Fin c2.L) :
    (c1.append c2).stepType (Fin.natAdd c1.L k) = emb2 (n1 := m1) (c2.stepType k) := by
  show proj (c1.append c2).aux ((c1.append c2).y (Fin.natAdd c1.L k)) = _
  rw [show (c1.append c2).y (Fin.natAdd c1.L k)
        = emb2 (n1 := m1) (c2.y k) from appendY_natAdd c1.toChain c2.toChain k]
  exact proj_emb2 c1.aux c2.aux (c2.y k)

theorem append_typeWeight_castAdd (c1 : ExtChain m1) (c2 : ExtChain m2) (k : Fin c1.L) :
    (c1.append c2).typeWeight (Fin.castAdd c2.L k) = c1.typeWeight k := by
  show weight (c1.append c2).aux ((c1.append c2).y (Fin.castAdd c2.L k)) = _
  rw [show (c1.append c2).y (Fin.castAdd c2.L k)
        = emb1 (n2 := m2) (c1.y k) from appendY_castAdd c1.toChain c2.toChain k]
  exact weight_emb1 c1.aux c2.aux (c1.y k)

theorem append_typeWeight_natAdd (c1 : ExtChain m1) (c2 : ExtChain m2) (k : Fin c2.L) :
    (c1.append c2).typeWeight (Fin.natAdd c1.L k) = c2.typeWeight k := by
  show weight (c1.append c2).aux ((c1.append c2).y (Fin.natAdd c1.L k)) = _
  rw [show (c1.append c2).y (Fin.natAdd c1.L k)
        = emb2 (n1 := m1) (c2.y k) from appendY_natAdd c1.toChain c2.toChain k]
  exact weight_emb2 c1.aux c2.aux (c2.y k)

theorem mem_heavySteps_append_castAdd (c1 : ExtChain m1) (c2 : ExtChain m2) (k : Fin c1.L) :
    Fin.castAdd c2.L k ∈ (c1.append c2).heavySteps ↔ k ∈ c1.heavySteps := by
  rw [mem_heavySteps, mem_heavySteps, append_typeWeight_castAdd]

theorem mem_heavySteps_append_natAdd (c1 : ExtChain m1) (c2 : ExtChain m2) (k : Fin c2.L) :
    Fin.natAdd c1.L k ∈ (c1.append c2).heavySteps ↔ k ∈ c2.heavySteps := by
  rw [mem_heavySteps, mem_heavySteps, append_typeWeight_natAdd]

theorem heavySteps_append (c1 : ExtChain m1) (c2 : ExtChain m2) :
    (c1.append c2).heavySteps
      = c1.heavySteps.image (Fin.castAdd c2.L) ∪ c2.heavySteps.image (Fin.natAdd c1.L) := by
  ext k
  induction k using Fin.addCases with
  | left k1 =>
      rw [mem_heavySteps_append_castAdd, Finset.mem_union, Finset.mem_image, Finset.mem_image]
      constructor
      · intro h; exact Or.inl ⟨k1, h, rfl⟩
      · rintro (⟨k1', hk', hkk⟩ | ⟨k2', _, hkk⟩)
        · have hk : k1 = k1' := Fin.castAdd_injective c1.L c2.L hkk.symm
          simpa [← hk] using hk'
        · exact absurd hkk.symm (castAdd_ne_natAdd k1 k2')
  | right k2 =>
      rw [mem_heavySteps_append_natAdd, Finset.mem_union, Finset.mem_image, Finset.mem_image]
      constructor
      · intro h; exact Or.inr ⟨k2, h, rfl⟩
      · rintro (⟨k1', _, hkk⟩ | ⟨k2', hk', hkk⟩)
        · exact absurd hkk (castAdd_ne_natAdd k1' k2)
        · have hk : k2 = k2' := Fin.natAdd_injective c2.L c1.L hkk.symm
          simpa [← hk] using hk'

theorem typeSet_append (c1 : ExtChain m1) (c2 : ExtChain m2) :
    (c1.append c2).typeSet
      = c1.typeSet.image (emb1 (n2 := m2)) ∪ c2.typeSet.image (emb2 (n1 := m1)) := by
  rw [typeSet, heavySteps_append, Finset.image_union, Finset.image_image, Finset.image_image,
    typeSet, typeSet]
  rw [Finset.image_image, Finset.image_image]
  congr 1
  · apply Finset.image_congr
    intro k _
    exact append_stepType_castAdd c1 c2 k
  · apply Finset.image_congr
    intro k _
    exact append_stepType_natAdd c1 c2 k

theorem emb1_eq_emb2_iff {u : Vec m1} {v : Vec m2} :
    emb1 (n2 := m2) u = emb2 (n1 := m1) v ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    constructor
    · funext i
      have := congrFun h (Fin.castAdd m2 i)
      simpa using this
    · funext j
      have := congrFun h (Fin.natAdd m1 j)
      simpa using this.symm
  · rintro ⟨rfl, rfl⟩
    simp

theorem zero_not_mem_typeSet (c : ExtChain m) : (0 : Vec m) ∉ c.typeSet := by
  intro h
  rw [typeSet, Finset.mem_image] at h
  obtain ⟨k, hk, hk0⟩ := h
  rw [mem_heavySteps] at hk
  have hz : c.typeWeight k = 0 := by
    rw [typeWeight_eq_weight, hk0]
    simp [weight]
  omega

theorem disjoint_typeSet_image (c1 : ExtChain m1) (c2 : ExtChain m2) :
    Disjoint (c1.typeSet.image (emb1 (n2 := m2))) (c2.typeSet.image (emb2 (n1 := m1))) := by
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv1
  obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv2
  exact zero_not_mem_typeSet c1 ((emb1_eq_emb2_iff.mp hwv.symm).1 ▸ hu)

theorem typeSet_append_card (c1 : ExtChain m1) (c2 : ExtChain m2) :
    (c1.append c2).typeSet.card = c1.typeSet.card + c2.typeSet.card := by
  rw [typeSet_append, Finset.card_union_of_disjoint (disjoint_typeSet_image c1 c2),
    Finset.card_image_of_injective _ emb1_injective,
    Finset.card_image_of_injective _ emb2_injective]

theorem reducedComplexity_append (c1 : ExtChain m1) (c2 : ExtChain m2) :
    (c1.append c2).reducedComplexity = c1.reducedComplexity + c2.reducedComplexity := by
  have h1 := typeSet_card_le_L c1
  have h2 := typeSet_card_le_L c2
  show (c1.append c2).L - (c1.append c2).typeSet.card = _
  rw [append_L, typeSet_append_card]
  show c1.L + c2.L - (c1.typeSet.card + c2.typeSet.card)
    = c1.L - c1.typeSet.card + (c2.L - c2.typeSet.card)
  omega

variable {m1 m2 n1 n2 : ℕ}

/-- Injectivity of the map on essential variables induced by a direct sum. -/
theorem append_col_injective {col1 : Fin n1 → Fin m1} {col2 : Fin n2 → Fin m2}
    (h1 : Function.Injective col1) (h2 : Function.Injective col2) :
    Function.Injective (Fin.append (fun j1 => Fin.castAdd m2 (col1 j1))
      (fun j2 => Fin.natAdd m1 (col2 j2))) := by
  intro a b h
  induction a using Fin.addCases with
  | left a1 =>
      induction b using Fin.addCases with
      | left b1 =>
          simp only [Fin.append_left] at h
          rw [h1 (Fin.castAdd_injective m1 m2 h)]
      | right b2 =>
          simp only [Fin.append_left, Fin.append_right] at h
          exact absurd h (castAdd_ne_natAdd (col1 a1) (col2 b2))
  | right a2 =>
      induction b using Fin.addCases with
      | left b1 =>
          simp only [Fin.append_left, Fin.append_right] at h
          exact absurd h.symm (castAdd_ne_natAdd (col1 b1) (col2 a2))
      | right b2 =>
          simp only [Fin.append_right] at h
          rw [h2 (Fin.natAdd_injective m2 m1 h)]

/-- The direct sum of two extended chains computes the direct sum of the matrices. -/
theorem append_computes {k1 k2 : ℕ} (c1 : ExtChain m1) (c2 : ExtChain m2)
    (A1 : Matrix (Fin k1) (Fin n1) (ZMod 2)) (A2 : Matrix (Fin k2) (Fin n2) (ZMod 2))
    {col1 : Fin n1 → Fin m1} {col2 : Fin n2 → Fin m2}
    (h1 : c1.Computes A1 col1) (h2 : c2.Computes A2 col2) :
    (c1.append c2).Computes (dsum A1 A2)
      (Fin.append (fun j1 => Fin.castAdd m2 (col1 j1)) (fun j2 => Fin.natAdd m1 (col2 j2))) := by
  obtain ⟨hinj1, hdisj1, hrow1⟩ := h1
  obtain ⟨hinj2, hdisj2, hrow2⟩ := h2
  refine ⟨append_col_injective hinj1 hinj2, ?_, ?_⟩
  · intro j
    revert j
    refine Fin.addCases (m := n1) (n := n2) ?_ ?_
    · intro j1 hmem
      rw [Fin.append_left] at hmem
      exact hdisj1 j1 ((castAdd_mem_image_union (A := c1.aux) (B := c2.aux) (col1 j1)).mp hmem)
    · intro j2 hmem
      rw [Fin.append_right] at hmem
      exact hdisj2 j2 ((natAdd_mem_image_union (A := c1.aux) (B := c2.aux) (col2 j2)).mp hmem)
  · intro i
    revert i
    refine Fin.addCases (m := k1) (n := k2) ?_ ?_
    · intro i1
      rw [dsum_apply_castAdd]
      obtain ⟨w, hw, hval, hzero⟩ := hrow1 i1
      refine ⟨emb1 (n2 := m2) w, ?_, ?_, ?_⟩
      · rcases hw with (hw | hw) | hw
        · obtain ⟨a, rfl⟩ := hw
          exact Or.inl (Or.inl ⟨Fin.castAdd m2 a, (emb1_basisVec a).symm⟩)
        · obtain ⟨t, rfl⟩ := hw
          exact Or.inl (Or.inr ⟨Fin.castAdd c2.L t,
            appendY_castAdd c1.toChain c2.toChain t⟩)
        · rw [hw]; exact Or.inr (by simp)
      · intro j
        revert j
        refine Fin.addCases (m := n1) (n := n2) ?_ ?_
        · intro j1
          simpa [Fin.append_left] using hval j1
        · intro j2
          simp [Fin.append_right]
      · intro j hj
        rw [show (c1.append c2).aux
              = c1.aux.image (Fin.castAdd m2) ∪ c2.aux.image (Fin.natAdd m1) from rfl] at hj
        induction j using Fin.addCases with
        | left j1 =>
            simp only [emb1, Fin.append_left]
            exact hzero j1 ((castAdd_mem_image_union (A := c1.aux) (B := c2.aux) j1).mp hj)
        | right j2 =>
            simp only [emb1, Fin.append_right, Pi.zero_apply]
    · intro i2
      rw [dsum_apply_natAdd]
      obtain ⟨w, hw, hval, hzero⟩ := hrow2 i2
      refine ⟨emb2 (n1 := m1) w, ?_, ?_, ?_⟩
      · rcases hw with (hw | hw) | hw
        · obtain ⟨a, rfl⟩ := hw
          exact Or.inl (Or.inl ⟨Fin.natAdd m1 a, (emb2_basisVec a).symm⟩)
        · obtain ⟨t, rfl⟩ := hw
          exact Or.inl (Or.inr ⟨Fin.natAdd c1.L t,
            appendY_natAdd c1.toChain c2.toChain t⟩)
        · rw [hw]; exact Or.inr (by simp)
      · intro j
        revert j
        refine Fin.addCases (m := n1) (n := n2) ?_ ?_
        · intro j1
          simp [Fin.append_left]
        · intro j2
          simpa [Fin.append_right] using hval j2
      · intro j hj
        rw [show (c1.append c2).aux
              = c1.aux.image (Fin.castAdd m2) ∪ c2.aux.image (Fin.natAdd m1) from rfl] at hj
        induction j using Fin.addCases with
        | left j1 =>
            simp only [emb2, Fin.append_left, Pi.zero_apply]
        | right j2 =>
            simp only [emb2, Fin.append_right]
            exact hzero j2 ((natAdd_mem_image_union (A := c1.aux) (B := c2.aux) j2).mp hj)

/-- **Upper bound in Lemma 1**: `L*(A1 ⊞ A2) ≤ L*(A1) + L*(A2)`. -/
theorem Lstar_dsum_le {k1 k2 : ℕ} (A1 : Matrix (Fin k1) (Fin n1) (ZMod 2))
    (A2 : Matrix (Fin k2) (Fin n2) (ZMod 2)) :
    Lstar (dsum A1 A2) ≤ Lstar A1 + Lstar A2 := by
  obtain ⟨m1, c1, col1, hcomp1, hrc1⟩ := Nat.sInf_mem (Lstar_witness_nonempty A1)
  obtain ⟨m2, c2, col2, hcomp2, hrc2⟩ := Nat.sInf_mem (Lstar_witness_nonempty A2)
  have hcomp := ExtChain.append_computes c1 c2 A1 A2 hcomp1 hcomp2
  calc Lstar (dsum A1 A2) ≤ (c1.append c2).reducedComplexity := Lstar_le_of_computes _ _ hcomp
    _ = c1.reducedComplexity + c2.reducedComplexity := ExtChain.reducedComplexity_append c1 c2
    _ = Lstar A1 + Lstar A2 := by
        simp only [Lstar]
        rw [hrc1, hrc2]

end ExtChain

/-! ### Lower bound in Lemma 1: compressing a chain to one representative per type

Given a chain that computes `A1 ⊞ A2` (possibly an extended chain, with essential variables
named by an injective map `col`), we regard it as computing `A2` after declaring the
variables of `A1` inessential, and we compress it by keeping only the first occurrence of
each nonzero, non-basis value of the `A1`-projection.  The compressed chain computes `A1`
and has at most as many elements as there are distinct types of weight at least `2`; this
is the counting content of Lemma 1. -/

section LowerBound

variable {n1 n2 m : ℕ}

@[simp] theorem proj_univ {m : ℕ} (v : Vec m) : proj (Finset.univ : Finset (Fin m)) v = v := by
  funext i
  simp [proj]

theorem weight_mono {m : ℕ} {W₁ W₂ : Finset (Fin m)} (h : W₁ ⊆ W₂) (v : Vec m) :
    weight W₁ v ≤ weight W₂ v := by
  unfold weight
  exact Finset.card_le_card (Finset.filter_subset_filter (p := fun i => v i ≠ 0) h)

/-- A vector with at least two nonzero coordinates is neither zero nor a basis vector. -/
theorem two_le_weight_univ_of_ne_zero_not_basis {m : ℕ} {v : Vec m}
    (hv : v ≠ 0) (hb : ∀ i : Fin m, v ≠ basisVec i) :
    2 ≤ weight (Finset.univ : Finset (Fin m)) v := by
  by_contra h
  push Not at h
  have h1 : weight (Finset.univ : Finset (Fin m)) v ≤ 1 := by omega
  rcases proj_eq_zero_or_basisVec_of_weight_le_one (Finset.univ : Finset (Fin m)) v h1 with
    h0 | ⟨i, hi⟩
  · exact hv (by simpa using h0)
  · exact hb i (by simpa using hi)

/-- The first block of essential variables, seen as a set of coordinates of `Vec m`. -/
noncomputable def colLeft (col : Fin (n1 + n2) → Fin m) : Finset (Fin m) :=
  Finset.univ.image (fun i : Fin n1 => col (Fin.castAdd n2 i))

theorem mem_colLeft {col : Fin (n1 + n2) → Fin m} {x : Fin m} :
    x ∈ colLeft (n1 := n1) (n2 := n2) col ↔ ∃ i : Fin n1, col (Fin.castAdd n2 i) = x := by
  simp [colLeft]

/-- Coordinate projection onto the variables of the first summand. -/
def projFst (col : Fin (n1 + n2) → Fin m) (v : Vec m) : Vec n1 :=
  fun j => v (col (Fin.castAdd n2 j))

/-- Coordinate projection onto the variables of the second summand. -/
def projSnd (col : Fin (n1 + n2) → Fin m) (v : Vec m) : Vec n2 :=
  fun j => v (col (Fin.natAdd n1 j))

@[simp] theorem projFst_zero (col : Fin (n1 + n2) → Fin m) :
    projFst (n1 := n1) (n2 := n2) col (0 : Vec m) = 0 := rfl

@[simp] theorem projSnd_zero (col : Fin (n1 + n2) → Fin m) :
    projSnd (n1 := n1) (n2 := n2) col (0 : Vec m) = 0 := rfl

theorem projFst_add (col : Fin (n1 + n2) → Fin m) (u v : Vec m) :
    projFst (n1 := n1) (n2 := n2) col (u + v) = projFst col u + projFst col v := rfl

theorem projSnd_add (col : Fin (n1 + n2) → Fin m) (u v : Vec m) :
    projSnd (n1 := n1) (n2 := n2) col (u + v) = projSnd col u + projSnd col v := rfl

theorem projFst_congr (col : Fin (n1 + n2) → Fin m) {u v : Vec m} (h : ∀ x, u x = v x) :
    projFst (n1 := n1) (n2 := n2) col u = projFst col v := by
  funext j
  exact h _

/-- The projection of a basis vector is either zero or a basis vector. -/
theorem projFst_basisVec (col : Fin (n1 + n2) → Fin m) (hcol : Function.Injective col)
    (d : Fin m) :
    projFst (n1 := n1) (n2 := n2) col (basisVec d) = 0 ∨
      ∃ i : Fin n1, projFst col (basisVec d) = basisVec i := by
  by_cases hd : ∃ i : Fin n1, col (Fin.castAdd n2 i) = d
  · obtain ⟨i, hi⟩ := hd
    refine Or.inr ⟨i, ?_⟩
    funext j
    simp only [projFst, basisVec]
    rw [← hi]
    by_cases hj : col (Fin.castAdd n2 j) = col (Fin.castAdd n2 i)
    · have hji : j = i := Fin.castAdd_injective n1 n2 (hcol hj)
      subst hji
      simp
    · have hne : j ≠ i := fun hh => hj (by rw [hh])
      simp [hj, hne]
  · refine Or.inl ?_
    funext j
    simp only [projFst, basisVec]
    have hne : col (Fin.castAdd n2 j) ≠ d := fun hh => hd ⟨j, hh⟩
    simp [hne]

/-- The weight of a vector on the essential variables of `A1` equals the weight of its
first-block projection. -/
theorem weight_colLeft (col : Fin (n1 + n2) → Fin m) (hcol : Function.Injective col)
    (v : Vec m) :
    weight (colLeft (n1 := n1) (n2 := n2) col) v
      = weight (Finset.univ : Finset (Fin n1)) (projFst col v) := by
  unfold weight colLeft
  have hf : (Finset.univ.image (fun i : Fin n1 => col (Fin.castAdd n2 i))).filter
        (fun x => v x ≠ 0)
      = (Finset.univ.filter (fun i : Fin n1 => v (col (Fin.castAdd n2 i)) ≠ 0)).image
          (fun i => col (Fin.castAdd n2 i)) := by
    ext x
    constructor
    · intro hx
      rw [Finset.mem_filter, Finset.mem_image] at hx
      obtain ⟨⟨i, _, rfl⟩, hne⟩ := hx
      exact Finset.mem_image.mpr ⟨i, by simp [hne], rfl⟩
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      rw [Finset.mem_filter] at hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ hi.1, hi.2⟩
  rw [hf, Finset.card_image_of_injOn (f := fun i : Fin n1 => col (Fin.castAdd n2 i))]
  · rfl
  · intro a _ b _ hab
    exact Fin.castAdd_injective n1 n2 (hcol hab)

end LowerBound
/-! ### The set of representatives and the compressed chain -/

/-- The kept step indices: the first occurrence of every nonzero, non-basis value of the
projection onto the variables of the first summand. -/
noncomputable def keepSet (col : Fin (n1 + n2) → Fin m) (c : ExtChain m) : Finset (Fin c.L) :=
  Finset.univ.filter (fun k =>
    projFst col (c.y k) ≠ 0 ∧
      (∀ i : Fin n1, projFst col (c.y k) ≠ basisVec i) ∧
      (∀ k' : Fin c.L, k' < k → projFst col (c.y k') ≠ projFst col (c.y k)))

theorem mem_keepSet {col : Fin (n1 + n2) → Fin m} {c : ExtChain m} {k : Fin c.L} :
    k ∈ keepSet (n1 := n1) (n2 := n2) col c ↔
      projFst col (c.y k) ≠ 0 ∧
        (∀ i : Fin n1, projFst col (c.y k) ≠ basisVec i) ∧
        (∀ k' : Fin c.L, k' < k → projFst col (c.y k') ≠ projFst col (c.y k)) := by
  simp [keepSet]

/-- The first occurrence of a nonzero, non-basis value of the projection is kept. -/
theorem exists_keep_of_value_le {col : Fin (n1 + n2) → Fin m} {c : ExtChain m} {v : Vec n1}
    {j : Fin c.L} (hj : projFst col (c.y j) = v) (hv : v ≠ 0)
    (hb : ∀ i : Fin n1, v ≠ basisVec i) :
    ∃ j₀ : Fin c.L, j₀ ≤ j ∧ j₀ ∈ keepSet col c ∧ projFst col (c.y j₀) = v := by
  classical
  let s : Finset (Fin c.L) := Finset.univ.filter (fun k => projFst col (c.y k) = v)
  have hs : s.Nonempty := ⟨j, by simp [s, hj]⟩
  have hmin : projFst col (c.y (s.min' hs)) = v := by
    have h := Finset.min'_mem s hs
    simpa [s] using h
  refine ⟨s.min' hs, Finset.min'_le s j (by simp [s, hj]), ?_, hmin⟩
  rw [mem_keepSet]
  refine ⟨by rw [hmin]; exact hv, ?_, ?_⟩
  · intro i
    rw [hmin]
    exact hb i
  · intro k' hk' hcon
    have hmem : k' ∈ s := by
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hcon]
      exact hmin
    exact absurd hk' (not_lt.mpr (Finset.min'_le s k' hmem))

/-- The vectors computed by the compressed chain. -/
noncomputable def compY (col : Fin (n1 + n2) → Fin m) (c : ExtChain m) :
    Fin (keepSet col c).card → Vec n1 :=
  fun t => projFst col (c.y ((keepSet col c).orderEmbOfFin rfl t))

/-- Every nonzero, non-basis projection value occurs among the values of the compressed
chain, at a position no later than any given occurrence. -/
theorem exists_compY_eq_le {col : Fin (n1 + n2) → Fin m} {c : ExtChain m} {v : Vec n1}
    {j : Fin c.L} (hj : projFst col (c.y j) = v) (hv : v ≠ 0)
    (hb : ∀ i : Fin n1, v ≠ basisVec i) :
    ∃ t : Fin (keepSet col c).card,
      (keepSet col c).orderEmbOfFin rfl t ≤ j ∧ compY col c t = v := by
  obtain ⟨j₀, hj₀le, hj₀mem, hj₀val⟩ := exists_keep_of_value_le hj hv hb
  have hrange : j₀ ∈ Set.range ((keepSet col c).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hj₀mem
  obtain ⟨t, ht⟩ := hrange
  refine ⟨t, ?_, ?_⟩
  · rw [ht]
    exact hj₀le
  · show projFst col (c.y ((keepSet col c).orderEmbOfFin rfl t)) = v
    rw [ht, hj₀val]

theorem orderEmb_lt_iff {col : Fin (n1 + n2) → Fin m} (c : ExtChain m)
    (t t' : Fin (keepSet col c).card) :
    (keepSet col c).orderEmbOfFin rfl t < (keepSet col c).orderEmbOfFin rfl t' ↔ t < t' :=
  (keepSet col c).orderEmbOfFin rfl |>.lt_iff_lt

/-- The type weight is the weight of the computed vector on the inessential variables. -/
theorem typeWeight_eq_weight_y {m : ℕ} (c : ExtChain m) (k : Fin c.L) :
    c.typeWeight k = weight c.aux (c.y k) := by
  rw [ExtChain.typeWeight_eq_weight, ExtChain.stepType, weight_proj]

/-- Kept steps have a type of weight at least `2`. -/
theorem keepSet_subset_heavySteps {col : Fin (n1 + n2) → Fin m}
    (hcol : Function.Injective col) (c : ExtChain m)
    (hU : colLeft (n1 := n1) (n2 := n2) col ⊆ c.aux) :
    keepSet col c ⊆ c.heavySteps := by
  intro k hk
  rw [ExtChain.mem_heavySteps, typeWeight_eq_weight_y]
  rw [mem_keepSet] at hk
  obtain ⟨h0, hb, _⟩ := hk
  have hw : 2 ≤ weight (Finset.univ : Finset (Fin n1)) (projFst col (c.y k)) :=
    two_le_weight_univ_of_ne_zero_not_basis h0 hb
  calc 2 ≤ weight (Finset.univ : Finset (Fin n1)) (projFst col (c.y k)) := hw
    _ = weight (colLeft col) (c.y k) := (weight_colLeft col hcol (c.y k)).symm
    _ ≤ weight c.aux (c.y k) := weight_mono hU (c.y k)

/-- Distinct kept steps have distinct types. -/
theorem keepSet_typeInjOn {col : Fin (n1 + n2) → Fin m}
    (hcol : Function.Injective col) (c : ExtChain m)
    (hU : colLeft (n1 := n1) (n2 := n2) col ⊆ c.aux) :
    Set.InjOn c.stepType (keepSet col c : Set (Fin c.L)) := by
  intro k1 hk1 k2 hk2 hst
  have hval : projFst col (c.y k1) = projFst col (c.y k2) := by
    funext i
    have hi : col (Fin.castAdd n2 i) ∈ colLeft (n1 := n1) (n2 := n2) col :=
      Finset.mem_image_of_mem _ (Finset.mem_univ i)
    have h1 : projFst col (c.y k1) i = c.stepType k1 (col (Fin.castAdd n2 i)) := by
      show c.y k1 (col (Fin.castAdd n2 i)) = proj c.aux (c.y k1) (col (Fin.castAdd n2 i))
      rw [proj_apply_mem c.aux (c.y k1) (hU hi)]
    have h2 : projFst col (c.y k2) i = c.stepType k2 (col (Fin.castAdd n2 i)) := by
      show c.y k2 (col (Fin.castAdd n2 i)) = proj c.aux (c.y k2) (col (Fin.castAdd n2 i))
      rw [proj_apply_mem c.aux (c.y k2) (hU hi)]
    rw [h1, h2, hst]
  have hk1' : k1 ∈ keepSet col c := hk1
  have hk2' : k2 ∈ keepSet col c := hk2
  rcases lt_trichotomy k1 k2 with h | h | h
  · rw [mem_keepSet] at hk2'
    exact absurd hval (hk2'.2.2 k1 h)
  · exact h
  · rw [mem_keepSet] at hk1'
    exact absurd hval.symm (hk1'.2.2 k2 h)

/-- The compressed chain has at most as many elements as there are distinct types of weight
at least `2`. -/
theorem keepSet_card_le_typeSet_card {col : Fin (n1 + n2) → Fin m}
    (hcol : Function.Injective col) (c : ExtChain m)
    (hU : colLeft (n1 := n1) (n2 := n2) col ⊆ c.aux) :
    (keepSet col c).card ≤ c.typeSet.card := by
  have hsub := keepSet_subset_heavySteps (n1 := n1) (n2 := n2) hcol c hU
  have hinj := keepSet_typeInjOn (n1 := n1) (n2 := n2) hcol c hU
  have himg : (keepSet col c).image c.stepType ⊆ c.typeSet := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨k, hsub hk, rfl⟩
  calc (keepSet col c).card = ((keepSet col c).image c.stepType).card :=
        (Finset.card_image_of_injOn hinj).symm
    _ ≤ c.typeSet.card := Finset.card_le_card himg

/-- Classification of a summand at a kept step: its projection is either zero, a basis
vector, or the value of an earlier step of the compressed chain. -/
theorem pool_proj_cases {col : Fin (n1 + n2) → Fin m} (hcol : Function.Injective col)
    (c : ExtChain m) {K : Fin c.L} (hK : K ∈ keepSet col c) {k : ℕ} (hk : k ≤ K.1)
    (a : Fin m ⊕ Fin k) :
    projFst col (chainPool c.y k (le_trans hk (le_of_lt K.2)) a) = 0 ∨
      (∃ i : Fin n1, projFst col (chainPool c.y k (le_trans hk (le_of_lt K.2)) a) = basisVec i) ∨
      ∃ t' : Fin (keepSet col c).card,
        (keepSet col c).orderEmbOfFin rfl t' < K ∧
        compY col c t' = projFst col (chainPool c.y k (le_trans hk (le_of_lt K.2)) a) := by
  have hkL : k ≤ c.L := le_trans hk (le_of_lt K.2)
  cases a with
  | inl d =>
      have hval : chainPool c.y k hkL (Sum.inl d) = basisVec d := rfl
      rcases projFst_basisVec col hcol d with h | ⟨i, hi⟩
      · exact Or.inl (by rw [hval, h])
      · exact Or.inr (Or.inl ⟨i, by rw [hval, hi]⟩)
  | inr j =>
      let j' : Fin c.L := ⟨j.1, lt_of_lt_of_le j.2 hkL⟩
      have hval : chainPool c.y k hkL (Sum.inr j) = c.y j' := rfl
      by_cases h0 : projFst col (c.y j') = 0
      · exact Or.inl (by rw [hval, h0])
      · by_cases hb : ∃ i : Fin n1, projFst col (c.y j') = basisVec i
        · obtain ⟨i, hi⟩ := hb
          exact Or.inr (Or.inl ⟨i, by rw [hval, hi]⟩)
        · push Not at hb
          obtain ⟨t', ht'le, ht'val⟩ :=
            exists_compY_eq_le (col := col) (c := c) (j := j') rfl h0 hb
          refine Or.inr (Or.inr ⟨t', ?_, ?_⟩)
          · have h1 : ((keepSet col c).orderEmbOfFin rfl t').1 ≤ j'.1 := ht'le
            have h2 : j'.1 < K.1 := lt_of_lt_of_le j.2 hk
            exact lt_of_le_of_lt h1 h2
          · rw [hval, ht'val]

/-- The compressed chain: it keeps only the first occurrence of each nonzero, non-basis value
of the projection onto the variables of the first summand. -/
noncomputable def comp (col : Fin (n1 + n2) → Fin m) (hcol : Function.Injective col)
    (c : ExtChain m) : VecAddChain n1 where
  L := (keepSet col c).card
  y := compY col c
  valid := by
    intro t
    let K : Fin c.L := (keepSet col c).orderEmbOfFin rfl t
    obtain ⟨a, b, hab⟩ := c.valid K
    have hK : K ∈ keepSet col c := Finset.orderEmbOfFin_mem _ _ t
    have hK0 : projFst col (c.y K) ≠ 0 := (mem_keepSet.mp hK).1
    have hKb : ∀ i : Fin n1, projFst col (c.y K) ≠ basisVec i := (mem_keepSet.mp hK).2.1
    have hKmin : ∀ k' : Fin c.L, k' < K → projFst col (c.y k') ≠ projFst col (c.y K) :=
      (mem_keepSet.mp hK).2.2
    have hsplit : projFst col (c.y K)
        = projFst col (chainPool c.y K.1 (le_of_lt K.2) a)
          + projFst col (chainPool c.y K.1 (le_of_lt K.2) b) := by
      rw [hab, projFst_add]
    have key : ∀ (a : Fin m ⊕ Fin K.1),
        projFst col (chainPool c.y K.1 (le_of_lt K.2) a) ≠ 0 →
        ∃ a' : Fin n1 ⊕ Fin t.1,
          chainPool (compY col c) t.1 (le_of_lt t.2) a'
            = projFst col (chainPool c.y K.1 (le_of_lt K.2) a) := by
      intro a hne
      rcases pool_proj_cases (n1 := n1) (n2 := n2) hcol c hK (le_refl K.1) a with
        h0 | hbas | hkept
      · exact absurd h0 hne
      · obtain ⟨i, hi⟩ := hbas
        exact ⟨Sum.inl i, by rw [hi]; rfl⟩
      · obtain ⟨t', ht'lt, ht'val⟩ := hkept
        have htt : t' < t := (orderEmb_lt_iff c t' t).mp ht'lt
        refine ⟨Sum.inr ⟨t'.1, htt⟩, ?_⟩
        rw [← ht'val]
        simp only [chainPool]
    have hane : projFst col (chainPool c.y K.1 (le_of_lt K.2) a) ≠ 0 := by
      intro h0
      have hsum : projFst col (c.y K)
          = projFst col (chainPool c.y K.1 (le_of_lt K.2) b) := by
        rw [hsplit, h0, zero_add]
      rcases pool_proj_cases (n1 := n1) (n2 := n2) hcol c hK (le_refl K.1) b with
        hb0 | hbas | hkept
      · rw [hb0] at hsum
        exact hK0 hsum
      · obtain ⟨i, hi⟩ := hbas
        rw [hi] at hsum
        exact hKb i hsum
      · obtain ⟨t', ht'lt, ht'val⟩ := hkept
        have hval' : projFst col (c.y ((keepSet col c).orderEmbOfFin rfl t'))
            = projFst col (c.y K) := by
          have hc : compY col c t'
              = projFst col (c.y ((keepSet col c).orderEmbOfFin rfl t')) := rfl
          rw [← hc, ht'val, hsum]
        exact hKmin _ ht'lt hval'
    have hbne : projFst col (chainPool c.y K.1 (le_of_lt K.2) b) ≠ 0 := by
      intro h0
      have hsum : projFst col (c.y K)
          = projFst col (chainPool c.y K.1 (le_of_lt K.2) a) := by
        rw [hsplit, h0, add_zero]
      rcases pool_proj_cases (n1 := n1) (n2 := n2) hcol c hK (le_refl K.1) a with
        ha0 | hbas | hkept
      · rw [ha0] at hsum
        exact hK0 hsum
      · obtain ⟨i, hi⟩ := hbas
        rw [hi] at hsum
        exact hKb i hsum
      · obtain ⟨t', ht'lt, ht'val⟩ := hkept
        have hval' : projFst col (c.y ((keepSet col c).orderEmbOfFin rfl t'))
            = projFst col (c.y K) := by
          have hc : compY col c t'
              = projFst col (c.y ((keepSet col c).orderEmbOfFin rfl t')) := rfl
          rw [← hc, ht'val, hsum]
        exact hKmin _ ht'lt hval'
    obtain ⟨a', ha'⟩ := key a hane
    obtain ⟨b', hb'⟩ := key b hbne
    refine ⟨a', b', ?_⟩
    rw [ha', hb']
    exact hsplit

/-! ### General type sets and representatives

For the lower bound of Lemma 1 we regard a chain computing `A1 ⊞ A2` as an extended chain
whose inessential variables are `aux ∪ colLeft`: the type of a step is then the pair formed by
its coefficients at the inessential variables of the chain and at the variables of `A1`.
We keep one representative per type of weight at least `2`; the representatives form a chain
computing `A1`, and its reduced complexity is the number of types minus the number of types
already present in the original chain. -/

section GeneralTypes

variable {m : ℕ}

/-- The projection of a vector supported on `W₁` onto `W₂` coincides with its projection onto
`W₁`, provided `W₁ ⊆ W₂`. -/
theorem proj_proj_of_subset {W₁ W₂ : Finset (Fin m)} (h : W₁ ⊆ W₂) (v : Vec m) :
    proj W₁ (proj W₂ v) = proj W₁ v := by
  funext i
  by_cases hi : i ∈ W₁
  · rw [proj_apply_mem W₁ _ hi, proj_apply_mem W₂ _ (h hi), proj_apply_mem W₁ _ hi]
  · rw [proj_apply_not_mem W₁ _ hi, proj_apply_not_mem W₁ _ hi]

/-- The weight on `W₁` of the projection onto `W₂` equals the weight on `W₁`. -/
theorem weight_proj_of_subset {W₁ W₂ : Finset (Fin m)} (h : W₁ ⊆ W₂) (v : Vec m) :
    weight W₁ (proj W₂ v) = weight W₁ v := by
  unfold weight
  congr 1
  apply Finset.filter_congr
  intro i hi
  rw [proj_apply_mem W₂ v (h hi)]

/-- A vector supported on `W` has the same weight counted on `W` and on all coordinates. -/
theorem weight_eq_weight_univ_of_supported (W : Finset (Fin m)) {v : Vec m}
    (h : ∀ i, i ∉ W → v i = 0) :
    weight W v = weight (Finset.univ : Finset (Fin m)) v := by
  unfold weight
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hi, hne⟩; exact hne
  · intro hne
    refine ⟨?_, hne⟩
    by_contra hi
    exact hne (h i hi)

/-- A nonzero vector supported on `W` which is not a basis vector has weight at least `2`
counted on `W`. -/
theorem two_le_weight_of_ne_zero_not_basis (W : Finset (Fin m)) {v : Vec m}
    (hsup : ∀ i, i ∉ W → v i = 0) (hv : v ≠ 0) (hb : ∀ d : Fin m, v ≠ basisVec d) :
    2 ≤ weight W v := by
  rw [weight_eq_weight_univ_of_supported W hsup]
  exact two_le_weight_univ_of_ne_zero_not_basis hv hb

/-- The projection of a basis vector is either zero or the basis vector itself. -/
theorem proj_basisVec_eq_zero_or_self (W : Finset (Fin m)) (d : Fin m) :
    proj W (basisVec d) = 0 ∨ proj W (basisVec d) = basisVec d := by
  rw [proj_basisVec]
  by_cases hd : d ∈ W
  · exact Or.inr (by simp [hd])
  · exact Or.inl (by simp [hd])

/-- Steps whose type on `W` has weight at least `2`. -/
noncomputable def heavyOf (W : Finset (Fin m)) (c : ExtChain m) : Finset (Fin c.L) :=
  Finset.univ.filter (fun k => 2 ≤ weight W (c.y k))

/-- Distinct types of weight at least `2` realized by the chain, relative to `W`. -/
noncomputable def typeOf (W : Finset (Fin m)) (c : ExtChain m) : Finset (Vec m) :=
  (heavyOf W c).image (fun k => proj W (c.y k))

theorem mem_heavyOf {W : Finset (Fin m)} {c : ExtChain m} {k : Fin c.L} :
    k ∈ heavyOf W c ↔ 2 ≤ weight W (c.y k) := by
  simp [heavyOf]

theorem heavyOf_aux (c : ExtChain m) : heavyOf c.aux c = c.heavySteps := rfl

theorem typeOf_aux (c : ExtChain m) : typeOf c.aux c = c.typeSet := rfl

theorem heavyOf_mono {W₁ W₂ : Finset (Fin m)} (h : W₁ ⊆ W₂) (c : ExtChain m) :
    heavyOf W₁ c ⊆ heavyOf W₂ c := by
  intro k hk
  rw [mem_heavyOf] at hk ⊢
  exact le_trans hk (weight_mono h (c.y k))

/-- Passing to more inessential variables can only decrease the number of distinct heavy
types. -/
theorem typeOf_card_le {W₁ W₂ : Finset (Fin m)} (h : W₁ ⊆ W₂) (c : ExtChain m) :
    (typeOf W₁ c).card ≤ (typeOf W₂ c).card := by
  have hsub : typeOf W₁ c ⊆ (typeOf W₂ c).image (proj W₁) := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨proj W₂ (c.y k),
      Finset.mem_image.mpr ⟨k, heavyOf_mono h c hk, rfl⟩,
      proj_proj_of_subset h (c.y k)⟩
  calc (typeOf W₁ c).card ≤ ((typeOf W₂ c).image (proj W₁)).card := Finset.card_le_card hsub
    _ ≤ (typeOf W₂ c).card := Finset.card_image_le

/-- The representatives: the first occurrence of every type of weight at least `2`. -/
noncomputable def repSet (W : Finset (Fin m)) (c : ExtChain m) : Finset (Fin c.L) :=
  Finset.univ.filter (fun k => k ∈ heavyOf W c ∧
    ∀ k' : Fin c.L, k' < k → proj W (c.y k') ≠ proj W (c.y k))

theorem mem_repSet {W : Finset (Fin m)} {c : ExtChain m} {k : Fin c.L} :
    k ∈ repSet W c ↔ k ∈ heavyOf W c ∧
      ∀ k' : Fin c.L, k' < k → proj W (c.y k') ≠ proj W (c.y k) := by
  simp [repSet]

theorem repSet_subset_heavyOf (W : Finset (Fin m)) (c : ExtChain m) :
    repSet W c ⊆ heavyOf W c := by
  intro k hk
  rw [mem_repSet] at hk
  exact hk.1

theorem repSet_type_injOn (W : Finset (Fin m)) (c : ExtChain m) :
    Set.InjOn (fun k : Fin c.L => proj W (c.y k)) (repSet W c : Set (Fin c.L)) := by
  intro k1 hk1 k2 hk2 hval
  have hk1' : k1 ∈ repSet W c := hk1
  have hk2' : k2 ∈ repSet W c := hk2
  rw [mem_repSet] at hk1' hk2'
  clear hk1 hk2
  rcases lt_trichotomy k1 k2 with h | h | h
  · exact absurd hval (hk2'.2 k1 h)
  · exact h
  · exact absurd hval.symm (hk1'.2 k2 h)

theorem exists_repSet_of_heavy {W : Finset (Fin m)} {c : ExtChain m} {j : Fin c.L}
    (hj : j ∈ heavyOf W c) :
    ∃ j₀ : Fin c.L, j₀ ≤ j ∧ j₀ ∈ repSet W c ∧ proj W (c.y j₀) = proj W (c.y j) := by
  classical
  let v := proj W (c.y j)
  let s : Finset (Fin c.L) := Finset.univ.filter (fun k => proj W (c.y k) = v)
  have hs : s.Nonempty := ⟨j, by simp [s, v]⟩
  have hmin : proj W (c.y (s.min' hs)) = v := by
    have h := Finset.min'_mem s hs
    simpa [s] using h
  refine ⟨s.min' hs, Finset.min'_le s j (by simp [s, v]), ?_, hmin⟩
  rw [mem_repSet]
  refine ⟨?_, ?_⟩
  · rw [mem_heavyOf]
    have hwj : 2 ≤ weight W (c.y j) := by
      rw [mem_heavyOf] at hj; exact hj
    have htype : proj W (c.y (s.min' hs)) = proj W (c.y j) := hmin
    have hw : weight W (c.y (s.min' hs)) = weight W (c.y j) := by
      rw [← weight_proj W (c.y (s.min' hs)), ← weight_proj W (c.y j), htype]
    omega
  · intro k' hk' hcon
    have hmem : k' ∈ s := by
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hcon]
      exact hmin
    exact absurd hk' (not_lt.mpr (Finset.min'_le s k' hmem))

theorem typeOf_eq_image_repSet (W : Finset (Fin m)) (c : ExtChain m) :
    typeOf W c = (repSet W c).image (fun k => proj W (c.y k)) := by
  ext v
  constructor
  · intro hv
    obtain ⟨k, hk, hkv⟩ := Finset.mem_image.mp hv
    obtain ⟨k₀, -, hk₀mem, hk₀val⟩ := exists_repSet_of_heavy hk
    exact Finset.mem_image.mpr ⟨k₀, hk₀mem, hk₀val.trans hkv⟩
  · intro hv
    obtain ⟨k, hk, hkv⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr ⟨k, repSet_subset_heavyOf W c hk, hkv⟩

theorem card_repSet (W : Finset (Fin m)) (c : ExtChain m) :
    (repSet W c).card = (typeOf W c).card := by
  rw [typeOf_eq_image_repSet]
  exact (Finset.card_image_of_injOn (repSet_type_injOn W c)).symm

end GeneralTypes

section CompressW

variable {m : ℕ}

/-- The vectors computed by the chain compressed to one representative per heavy type. -/
noncomputable def compYW (W : Finset (Fin m)) (c : ExtChain m) :
    Fin (repSet W c).card → Vec m :=
  fun t => proj W (c.y ((repSet W c).orderEmbOfFin rfl t))

/-- A heavy step's type occurs among the values of the compressed chain, no later than the
step itself. -/
theorem exists_compYW_eq_le_of_heavy {W : Finset (Fin m)} {c : ExtChain m} {j : Fin c.L}
    (hj : 2 ≤ weight W (c.y j)) :
    ∃ t : Fin (repSet W c).card,
      (repSet W c).orderEmbOfFin rfl t ≤ j ∧ compYW W c t = proj W (c.y j) := by
  have hheavy : j ∈ heavyOf W c := by rw [mem_heavyOf]; exact hj
  obtain ⟨j₀, hj₀le, hj₀mem, hj₀val⟩ := exists_repSet_of_heavy hheavy
  have hrange : j₀ ∈ Set.range ((repSet W c).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hj₀mem
  obtain ⟨t, ht⟩ := hrange
  refine ⟨t, ?_, ?_⟩
  · rw [ht]
    exact hj₀le
  · show proj W (c.y ((repSet W c).orderEmbOfFin rfl t)) = proj W (c.y j)
    rw [ht, hj₀val]

theorem orderEmbW_lt_iff (W : Finset (Fin m)) (c : ExtChain m)
    (t t' : Fin (repSet W c).card) :
    (repSet W c).orderEmbOfFin rfl t < (repSet W c).orderEmbOfFin rfl t' ↔ t < t' :=
  (repSet W c).orderEmbOfFin rfl |>.lt_iff_lt

/-- Classification of a summand at a representative step: its `W`-type is either zero, a
basis vector, or the value of an earlier step of the compressed chain. -/
theorem pool_W_cases (c : ExtChain m) (W : Finset (Fin m)) {K : Fin c.L}
    (hK : K ∈ repSet W c) {k : ℕ} (hk : k ≤ K.1) (a : Fin m ⊕ Fin k) :
    proj W (chainPool c.y k (le_trans hk (le_of_lt K.2)) a) = 0 ∨
      (∃ d : Fin m, proj W (chainPool c.y k (le_trans hk (le_of_lt K.2)) a) = basisVec d) ∨
      ∃ t' : Fin (repSet W c).card,
        (repSet W c).orderEmbOfFin rfl t' < K ∧
        compYW W c t' = proj W (chainPool c.y k (le_trans hk (le_of_lt K.2)) a) := by
  have hkL : k ≤ c.L := le_trans hk (le_of_lt K.2)
  cases a with
  | inl d =>
      have hval : chainPool c.y k hkL (Sum.inl d) = basisVec d := rfl
      rcases proj_basisVec_eq_zero_or_self W d with h | h
      · exact Or.inl (by rw [hval, h])
      · exact Or.inr (Or.inl ⟨d, by rw [hval, h]⟩)
  | inr j =>
      have hjlt : j.1 < K.1 := lt_of_lt_of_le j.2 hk
      let j' : Fin c.L := ⟨j.1, lt_of_lt_of_le j.2 hkL⟩
      have hval : chainPool c.y k hkL (Sum.inr j) = c.y j' := rfl
      by_cases hw : weight W (c.y j') ≤ 1
      · rcases proj_eq_zero_or_basisVec_of_weight_le_one W (c.y j') hw with h0 | ⟨d, hd⟩
        · exact Or.inl (by rw [hval, h0])
        · exact Or.inr (Or.inl ⟨d, by rw [hval, hd]⟩)
      · push Not at hw
        obtain ⟨t', ht'le, ht'val⟩ := exists_compYW_eq_le_of_heavy hw
        refine Or.inr (Or.inr ⟨t', ?_, ?_⟩)
        · have h1 : ((repSet W c).orderEmbOfFin rfl t').1 ≤ j'.1 := ht'le
          have h2 : j'.1 < K.1 := hjlt
          exact lt_of_le_of_lt h1 h2
        · rw [hval, ← ht'val]

/-- The chain obtained by keeping one representative per heavy `W`-type. -/
noncomputable def compChain (W : Finset (Fin m)) (c : ExtChain m) : VecAddChain m where
  L := (repSet W c).card
  y := compYW W c
  valid := by
    intro t
    let K : Fin c.L := (repSet W c).orderEmbOfFin rfl t
    obtain ⟨a, b, hab⟩ := c.valid K
    have hK : K ∈ repSet W c := Finset.orderEmbOfFin_mem _ _ t
    have hKheavy : 2 ≤ weight W (c.y K) := by
      have hK' : K ∈ heavyOf W c := repSet_subset_heavyOf W c hK
      rw [mem_heavyOf] at hK'
      exact hK'
    have hK0 : proj W (c.y K) ≠ 0 := by
      intro h0
      have : weight W (c.y K) = 0 := by
        rw [← weight_proj W (c.y K), h0]
        simp [weight]
      omega
    have hKb : ∀ d : Fin m, proj W (c.y K) ≠ basisVec d := by
      intro d hd
      have hle : weight W (c.y K) ≤ 1 := by
        rw [← weight_proj W (c.y K), hd]
        exact weight_le_one_basis W d
      omega
    have hKmin : ∀ k' : Fin c.L, k' < K → proj W (c.y k') ≠ proj W (c.y K) := by
      rw [mem_repSet] at hK
      exact hK.2
    have hsplit : proj W (c.y K)
        = proj W (chainPool c.y K.1 (le_of_lt K.2) a)
          + proj W (chainPool c.y K.1 (le_of_lt K.2) b) := by
      rw [hab, proj_add]
    have key : ∀ (a : Fin m ⊕ Fin K.1),
        proj W (chainPool c.y K.1 (le_of_lt K.2) a) ≠ 0 →
        ∃ a' : Fin m ⊕ Fin t.1,
          chainPool (compYW W c) t.1 (le_of_lt t.2) a'
            = proj W (chainPool c.y K.1 (le_of_lt K.2) a) := by
      intro a hne
      rcases pool_W_cases c W hK (le_refl K.1) a with h0 | hbas | hkept
      · exact absurd h0 hne
      · obtain ⟨d, hd⟩ := hbas
        exact ⟨Sum.inl d, by rw [hd]; rfl⟩
      · obtain ⟨t', ht'lt, ht'val⟩ := hkept
        have htt : t' < t := (orderEmbW_lt_iff W c t' t).mp ht'lt
        refine ⟨Sum.inr ⟨t'.1, htt⟩, ?_⟩
        rw [← ht'val]
        simp only [chainPool]
    have hane : proj W (chainPool c.y K.1 (le_of_lt K.2) a) ≠ 0 := by
      intro h0
      have hsum : proj W (c.y K)
          = proj W (chainPool c.y K.1 (le_of_lt K.2) b) := by
        rw [hsplit, h0, zero_add]
      rcases pool_W_cases c W hK (le_refl K.1) b with hb0 | hbas | hkept
      · rw [hb0] at hsum
        exact hK0 hsum
      · obtain ⟨d, hd⟩ := hbas
        rw [hd] at hsum
        exact hKb d hsum
      · obtain ⟨t', ht'lt, ht'val⟩ := hkept
        have hval' : proj W (c.y ((repSet W c).orderEmbOfFin rfl t')) = proj W (c.y K) := by
          have hc : compYW W c t'
              = proj W (c.y ((repSet W c).orderEmbOfFin rfl t')) := rfl
          rw [← hc, ht'val, hsum]
        exact hKmin _ ht'lt hval'
    have hbne : proj W (chainPool c.y K.1 (le_of_lt K.2) b) ≠ 0 := by
      intro h0
      have hsum : proj W (c.y K)
          = proj W (chainPool c.y K.1 (le_of_lt K.2) a) := by
        rw [hsplit, h0, add_zero]
      rcases pool_W_cases c W hK (le_refl K.1) a with ha0 | hbas | hkept
      · rw [ha0] at hsum
        exact hK0 hsum
      · obtain ⟨d, hd⟩ := hbas
        rw [hd] at hsum
        exact hKb d hsum
      · obtain ⟨t', ht'lt, ht'val⟩ := hkept
        have hval' : proj W (c.y ((repSet W c).orderEmbOfFin rfl t')) = proj W (c.y K) := by
          have hc : compYW W c t'
              = proj W (c.y ((repSet W c).orderEmbOfFin rfl t')) := rfl
          rw [← hc, ht'val, hsum]
        exact hKmin _ ht'lt hval'
    obtain ⟨a', ha'⟩ := key a hane
    obtain ⟨b', hb'⟩ := key b hbne
    refine ⟨a', b', ?_⟩
    rw [ha', hb']
    exact hsplit

/-- The type-compressed chain computes `A1`: every row of `A1` is represented, on the essential
variables of the first summand, by the projection onto `W` of a vector representing the
corresponding row of `A1 ⊞ A2`. -/
theorem compChain_computes {k1 k2 n1 n2 : ℕ} {A1 : Matrix (Fin k1) (Fin n1) (ZMod 2)}
    {A2 : Matrix (Fin k2) (Fin n2) (ZMod 2)} {W : Finset (Fin m)}
    {col : Fin (n1 + n2) → Fin m}
    (hW : colLeft (n1 := n1) (n2 := n2) col ⊆ W)
    {c : ExtChain m} (hauxW : c.aux ⊆ W) (h : c.Computes (dsum A1 A2) col) :
    (ExtChain.ofChain (compChain W c) c.aux).Computes A1
      (fun j => col (Fin.castAdd n2 j)) := by
  obtain ⟨hcol, hdisj, hrow⟩ := h
  have hinj : Function.Injective (fun j : Fin n1 => col (Fin.castAdd n2 j)) := by
    intro j1 j2 hjj
    exact Fin.castAdd_injective n1 n2 (hcol hjj)
  have haux : ∀ j : Fin n1, col (Fin.castAdd n2 j) ∉ c.aux :=
    fun j => hdisj (Fin.castAdd n2 j)
  refine ⟨hinj, haux, ?_⟩
  intro i1
  obtain ⟨w, hw, hval, hzero⟩ := hrow (Fin.castAdd k2 i1)
  have hproj : ∀ j : Fin n1, proj W w (col (Fin.castAdd n2 j)) = A1 i1 j := by
    intro j
    have hmem : col (Fin.castAdd n2 j) ∈ colLeft (n1 := n1) (n2 := n2) col :=
      Finset.mem_image_of_mem _ (Finset.mem_univ j)
    rw [proj_apply_mem W w (hW hmem), hval (Fin.castAdd n2 j), dsum_castAdd_castAdd]
  refine ⟨proj W w, ?_, hproj, ?_⟩
  rcases hw with (hw | hw) | hw
  · obtain ⟨d, rfl⟩ := hw
    rcases proj_basisVec_eq_zero_or_self W d with h0 | hb
    · exact Or.inr h0
    · exact Or.inl (Or.inl ⟨d, hb.symm⟩)
  · obtain ⟨j, rfl⟩ := hw
    by_cases hwt : weight W (c.y j) ≤ 1
    · rcases proj_eq_zero_or_basisVec_of_weight_le_one W (c.y j) hwt with h0 | ⟨d, hd⟩
      · exact Or.inr h0
      · exact Or.inl (Or.inl ⟨d, hd.symm⟩)
    · push Not at hwt
      obtain ⟨t, -, ht⟩ := exists_compYW_eq_le_of_heavy hwt
      refine Or.inl (Or.inr ⟨t, ?_⟩)
      show compYW W c t = proj W (c.y j)
      exact ht
  · rw [hw]
    simp
  · intro j hj
    rw [proj_apply_mem W w (hauxW hj)]
    exact hzero j hj

end CompressW

/-! ### Lemma 1: the lower bounds

Faithful to the paper: a chain computing `A1 ⊞ A2` is viewed as an extended chain computing
`A2` after declaring the variables of `A1` inessential.  One keeps a single representative per
type of weight at least `2`; the representatives form a chain computing `A1`, and the elements
removed number at least `L*(A2)`. -/

section Lemma1

variable {n1 n2 m : ℕ}

/-- The number of distinct types of weight at least `2` is bounded by the length. -/
theorem typeOf_card_le_L (W : Finset (Fin m)) (c : ExtChain m) :
    (typeOf W c).card ≤ c.L := by
  calc (typeOf W c).card ≤ (heavyOf W c).card := Finset.card_image_le
    _ ≤ (Finset.univ : Finset (Fin c.L)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = c.L := by rw [Finset.card_univ, Fintype.card_fin]

/-- Passing to more inessential variables can only decrease the number of types. -/
theorem typeSet_card_le_typeOf {c : ExtChain m} {W : Finset (Fin m)} (h : c.aux ⊆ W) :
    c.typeSet.card ≤ (typeOf W c).card := by
  have h' := typeOf_card_le h c
  rwa [typeOf_aux] at h'

/-- The projection onto the variables of the second summand is injective. -/
theorem projSnd_injective {col : Fin (n1 + n2) → Fin m} (hcol : Function.Injective col) :
    Function.Injective (fun j : Fin n2 => col (Fin.natAdd n1 j)) := by
  intro j1 j2 h
  exact Fin.natAdd_injective n2 n1 (hcol h)

/-- The variables of the second summand are neither inessential nor variables of the first. -/
theorem secondBlock_not_mem {col : Fin (n1 + n2) → Fin m} {aux : Finset (Fin m)}
    (hcol : Function.Injective col) (hdisj : ∀ j : Fin (n1 + n2), col j ∉ aux) (j : Fin n2) :
    col (Fin.natAdd n1 j) ∉ aux ∪ colLeft (n1 := n1) (n2 := n2) col := by
  intro hmem
  rcases Finset.mem_union.mp hmem with h | h
  · exact hdisj _ h
  · rw [mem_colLeft] at h
    obtain ⟨i, hi⟩ := h
    exact absurd (hcol hi) (castAdd_ne_natAdd i j)

/-- Declaring the variables of the first summand inessential turns a chain for `A1 ⊞ A2` into
an extended chain for `A2` of reduced complexity `L - #types`.  Hence `L*(A2) ≤ L - #types`. -/
theorem Lstar_A2_le_of_computes {k1 k2 : ℕ} {A1 : Matrix (Fin k1) (Fin n1) (ZMod 2)}
    {A2 : Matrix (Fin k2) (Fin n2) (ZMod 2)} {c : ExtChain m}
    {col : Fin (n1 + n2) → Fin m} (h : c.Computes (dsum A1 A2) col) :
    Lstar A2 ≤ c.L - (typeOf (c.aux ∪ colLeft (n1 := n1) (n2 := n2) col) c).card := by
  classical
  obtain ⟨hcol, hdisj, hrow⟩ := h
  set W := c.aux ∪ colLeft (n1 := n1) (n2 := n2) col with hW
  let col₂ : Fin n2 → Fin m := fun j => col (Fin.natAdd n1 j)
  have hcol₂ : Function.Injective col₂ := by
    intro j1 j2 h
    exact Fin.natAdd_injective n2 n1 (hcol h)
  have hcomp : (ExtChain.ofChain c.toChain W).Computes A2 col₂ := by
    refine ⟨hcol₂, ?_, ?_⟩
    · intro j
      exact secondBlock_not_mem hcol hdisj j
    · intro i2
      obtain ⟨w, hw, hval, hzero⟩ := hrow (Fin.natAdd k1 i2)
      refine ⟨w, ?_, ?_, ?_⟩
      · exact hw
      · intro j
        have hv := hval (Fin.natAdd n1 j)
        simpa [col₂, dsum_natAdd_natAdd] using hv
      · intro j hj
        rcases Finset.mem_union.mp hj with hj | hj
        · exact hzero j hj
        · rw [mem_colLeft] at hj
          obtain ⟨j1, hj1⟩ := hj
          rw [← hj1, hval (Fin.castAdd n2 j1)]
          exact dsum_natAdd_castAdd A1 A2 i2 j1
  have htype : (ExtChain.ofChain c.toChain W).typeSet = typeOf W c := rfl
  calc Lstar A2 ≤ (ExtChain.ofChain c.toChain W).reducedComplexity :=
        Lstar_le_of_computes _ _ hcomp
    _ = c.L - (typeOf W c).card := by
        rw [ExtChain.reducedComplexity, htype]
        rfl

/-- The chain compressed to one representative per nonzero, non-basis value of the
`A1`-projection computes `A1`. -/
theorem comp_computes {k1 k2 : ℕ} {A1 : Matrix (Fin k1) (Fin n1) (ZMod 2)}
    {A2 : Matrix (Fin k2) (Fin n2) (ZMod 2)} {c : ExtChain m}
    {col : Fin (n1 + n2) → Fin m} (hcol : Function.Injective col)
    (hrow : ∀ i : Fin (k1 + k2), ∃ w : Vec m,
      w ∈ Set.range (basisVec (n := m)) ∪ Set.range c.y ∪ ({0} : Set (Vec m)) ∧
      ∀ j : Fin (n1 + n2), w (col j) = dsum A1 A2 i j) :
    (comp col hcol c).Computes A1 := by
  classical
  intro i1
  obtain ⟨w, hw, hval⟩ := hrow (Fin.castAdd k2 i1)
  have hrowval : projFst col w = A1 i1 := by
    funext j
    show w (col (Fin.castAdd n2 j)) = A1 i1 j
    rw [hval (Fin.castAdd n2 j), dsum_castAdd_castAdd]
  rw [← hrowval]
  rcases hw with (hw | hw) | hw
  · obtain ⟨d, rfl⟩ := hw
    rcases projFst_basisVec (n1 := n1) (n2 := n2) col hcol d with h0 | ⟨i, hi⟩
    · exact Or.inr h0
    · exact Or.inl (Or.inl ⟨i, hi.symm⟩)
  · obtain ⟨j, rfl⟩ := hw
    by_cases hz : projFst col (c.y j) = 0
    · exact Or.inr hz
    · by_cases hb : ∃ i : Fin n1, projFst col (c.y j) = basisVec i
      · obtain ⟨i, hi⟩ := hb
        exact Or.inl (Or.inl ⟨i, hi.symm⟩)
      · push Not at hb
        obtain ⟨t, -, ht⟩ := exists_compY_eq_le (col := col) (c := c) rfl hz hb
        refine Or.inl (Or.inr ⟨t, ?_⟩)
        show compY col c t = projFst col (c.y j)
        exact ht
  · rw [hw]
    exact Or.inr (projFst_zero col)

/-- The compressed chain computes `A1`, so `L(A1)` is at most the number of types. -/
theorem chainComplexity_A1_le {k1 k2 : ℕ} {A1 : Matrix (Fin k1) (Fin n1) (ZMod 2)}
    {A2 : Matrix (Fin k2) (Fin n2) (ZMod 2)} {c : ExtChain m}
    {col : Fin (n1 + n2) → Fin m} (hcol : Function.Injective col)
    (hrow : ∀ i : Fin (k1 + k2), ∃ w : Vec m,
      w ∈ Set.range (basisVec (n := m)) ∪ Set.range c.y ∪ ({0} : Set (Vec m)) ∧
      ∀ j : Fin (n1 + n2), w (col j) = dsum A1 A2 i j)
    (hU : colLeft (n1 := n1) (n2 := n2) col ⊆ c.aux) :
    chainComplexity A1 ≤ c.typeSet.card := by
  calc chainComplexity A1 ≤ (comp col hcol c).L :=
        Nat.sInf_le ⟨_, rfl, comp_computes hcol hrow⟩
    _ = (keepSet col c).card := rfl
    _ ≤ c.typeSet.card := keepSet_card_le_typeSet_card hcol c hU

/-- Every type of the original chain occurs among the types of the compressed chain. -/
theorem typeSet_subset_compChain_typeSet {W : Finset (Fin m)} {c : ExtChain m}
    (haux : c.aux ⊆ W) :
    c.typeSet ⊆ (ExtChain.ofChain (compChain W c) c.aux).typeSet := by
  classical
  intro v hv
  change v ∈ typeOf c.aux c at hv
  obtain ⟨k, hk, hkv⟩ := Finset.mem_image.mp hv
  have hk2 : 2 ≤ weight c.aux (c.y k) := mem_heavyOf.mp hk
  have hkW : k ∈ heavyOf W c :=
    mem_heavyOf.mpr (le_trans hk2 (weight_mono haux (c.y k)))
  obtain ⟨K, -, hKmem, hKval⟩ := exists_repSet_of_heavy hkW
  have hrange : K ∈ Set.range ((repSet W c).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hKmem
  obtain ⟨t, ht⟩ := hrange
  have hKaux : proj c.aux (c.y K) = proj c.aux (c.y k) := by
    have h1 := congrArg (proj c.aux) hKval
    rw [proj_proj_of_subset haux (c.y K), proj_proj_of_subset haux (c.y k)] at h1
    exact h1
  have hKweight : weight c.aux (c.y K) = weight c.aux (c.y k) := by
    calc weight c.aux (c.y K) = weight c.aux (proj W (c.y K)) :=
          (weight_proj_of_subset haux (c.y K)).symm
      _ = weight c.aux (proj W (c.y k)) := by rw [hKval]
      _ = weight c.aux (c.y k) := weight_proj_of_subset haux (c.y k)
  refine Finset.mem_image.mpr ⟨t, ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    show 2 ≤ weight c.aux (proj W (c.y ((repSet W c).orderEmbOfFin rfl t)))
    rw [weight_proj_of_subset haux, ht, hKweight]
    exact hk2
  · show proj c.aux ((compChain W c).y t) = v
    show proj c.aux (proj W (c.y ((repSet W c).orderEmbOfFin rfl t))) = v
    rw [ht, proj_proj_of_subset haux, hKaux, hkv]

/-- Keeping one representative per type and retaining the inessential variables yields an
extended chain computing `A1` whose reduced complexity is at most `#types - #types(c)`. -/
theorem Lstar_A1_le_of_computes {k1 k2 : ℕ} {A1 : Matrix (Fin k1) (Fin n1) (ZMod 2)}
    {A2 : Matrix (Fin k2) (Fin n2) (ZMod 2)} {c : ExtChain m}
    {col : Fin (n1 + n2) → Fin m} (h : c.Computes (dsum A1 A2) col) :
    Lstar A1 ≤
      (typeOf (c.aux ∪ colLeft (n1 := n1) (n2 := n2) col) c).card - c.typeSet.card := by
  classical
  have hc := h
  obtain ⟨hcol, hdisj, -⟩ := h
  set W := c.aux ∪ colLeft (n1 := n1) (n2 := n2) col with hW
  have hcomp := compChain_computes (n1 := n1) (n2 := n2) (W := W)
    Finset.subset_union_right Finset.subset_union_left hc
  have hsub : c.typeSet ⊆ (ExtChain.ofChain (compChain W c) c.aux).typeSet :=
    typeSet_subset_compChain_typeSet (Finset.subset_union_left)
  have hcard : c.typeSet.card ≤ (ExtChain.ofChain (compChain W c) c.aux).typeSet.card :=
    Finset.card_le_card hsub
  calc Lstar A1 ≤ (ExtChain.ofChain (compChain W c) c.aux).reducedComplexity :=
        Lstar_le_of_computes _ _ hcomp
    _ = (repSet W c).card - (ExtChain.ofChain (compChain W c) c.aux).typeSet.card := rfl
    _ = (typeOf W c).card - (ExtChain.ofChain (compChain W c) c.aux).typeSet.card := by
        rw [card_repSet]
    _ ≤ (typeOf W c).card - c.typeSet.card := Nat.sub_le_sub_left hcard _

/-- **Lemma 1, additive lower bound**: `L*(A1) + L*(A2) ≤ L*(A1 ⊞ A2)`. -/
theorem Lstar_dsum_ge {k1 k2 : ℕ} (A1 : Matrix (Fin k1) (Fin n1) (ZMod 2))
    (A2 : Matrix (Fin k2) (Fin n2) (ZMod 2)) :
    Lstar A1 + Lstar A2 ≤ Lstar (dsum A1 A2) := by
  refine le_sInf_of_forall ?_ ?_
  · intro hs
    exact absurd hs (Set.nonempty_iff_ne_empty.mp (Lstar_witness_nonempty (dsum A1 A2)))
  · rintro l ⟨m, c, col, hcomp, hl⟩
    have hA2 := Lstar_A2_le_of_computes (A1 := A1) (A2 := A2) hcomp
    have hA1 := Lstar_A1_le_of_computes (A1 := A1) (A2 := A2) hcomp
    have hS : c.typeSet.card ≤
        (typeOf (c.aux ∪ colLeft (n1 := n1) (n2 := n2) col) c).card :=
      typeSet_card_le_typeOf Finset.subset_union_left
    have hT : (typeOf (c.aux ∪ colLeft (n1 := n1) (n2 := n2) col) c).card ≤ c.L :=
      typeOf_card_le_L _ c
    have hb : l = c.L - c.typeSet.card := hl.symm
    omega

/-- **Lemma 1, second inequality**: `L(A1) + L*(A2) ≤ L(A1 ⊞ A2)`. -/
theorem chainComplexity_dsum_ge {k1 k2 : ℕ} (A1 : Matrix (Fin k1) (Fin n1) (ZMod 2))
    (A2 : Matrix (Fin k2) (Fin n2) (ZMod 2)) :
    chainComplexity A1 + Lstar A2 ≤ chainComplexity (dsum A1 A2) := by
  rw [chainComplexity_eq_sInf]
  refine le_sInf_of_forall ?_ ?_
  · intro hs
    exact absurd hs (Set.nonempty_iff_ne_empty.mp (chainSet_nonempty (dsum A1 A2)))
  · rintro l ⟨cc, hL, hcomp⟩
    let U : Finset (Fin (n1 + n2)) :=
      colLeft (n1 := n1) (n2 := n2) (id : Fin (n1 + n2) → Fin (n1 + n2))
    let cU : ExtChain (n1 + n2) := ExtChain.ofChain cc U
    let c0 : ExtChain (n1 + n2) := ExtChain.ofChain cc ∅
    have hrowU : ∀ i : Fin (k1 + k2), ∃ w : Vec (n1 + n2),
        w ∈ Set.range (basisVec (n := n1 + n2)) ∪ Set.range cU.y ∪
          ({0} : Set (Vec (n1 + n2))) ∧ ∀ j : Fin (n1 + n2), w j = dsum A1 A2 i j := by
      intro i
      exact ⟨dsum A1 A2 i, hcomp i, fun j => rfl⟩
    have hU : colLeft (n1 := n1) (n2 := n2) (id : Fin (n1 + n2) → Fin (n1 + n2))
        ⊆ cU.aux := fun _ hx => hx
    have hA1 : chainComplexity A1 ≤ cU.typeSet.card :=
      chainComplexity_A1_le (col := id) Function.injective_id hrowU hU
    have hcomp0 : c0.Computes (dsum A1 A2) (id : Fin (n1 + n2) → Fin (n1 + n2)) :=
      ⟨Function.injective_id, fun j => by simp [c0, ExtChain.ofChain],
        fun i => ⟨dsum A1 A2 i, hcomp i, fun j => rfl,
          by intro j hj; simp [c0, ExtChain.ofChain] at hj⟩⟩
    have hA2 : Lstar A2 ≤ cc.L - cU.typeSet.card := by
      have h' := Lstar_A2_le_of_computes (A1 := A1) (A2 := A2) hcomp0
      have h'' : Lstar A2 ≤ cc.L -
          (typeOf (colLeft (n1 := n1) (n2 := n2)
            (id : Fin (n1 + n2) → Fin (n1 + n2))) c0).card := by
        simpa [c0, ExtChain.ofChain] using h'
      have htype : typeOf (colLeft (n1 := n1) (n2 := n2)
            (id : Fin (n1 + n2) → Fin (n1 + n2))) c0 = cU.typeSet := rfl
      rwa [htype] at h''
    have hle : cU.typeSet.card ≤ cc.L := by
      have h' := ExtChain.typeSet_card_le_L cU
      simpa [cU, ExtChain.ofChain] using h'
    have hmain : chainComplexity A1 + Lstar A2 ≤ cc.L := by
      calc chainComplexity A1 + Lstar A2 ≤ cU.typeSet.card + (cc.L - cU.typeSet.card) :=
            Nat.add_le_add hA1 hA2
        _ = cc.L := Nat.add_sub_of_le hle
    have hb : l = cc.L := hL.symm
    rw [hb]
    exact hmain

/-- **Lemma 1** (Section 2): `L*(A1 ⊞ A2) = L*(A1) + L*(A2)` and
`L(A1 ⊞ A2) ≥ L(A1) + L*(A2)`. -/
theorem lemma1_reduced {k1 k2 : ℕ} (A1 : Matrix (Fin k1) (Fin n1) (ZMod 2))
    (A2 : Matrix (Fin k2) (Fin n2) (ZMod 2)) :
    Lstar (dsum A1 A2) = Lstar A1 + Lstar A2 ∧
      chainComplexity (dsum A1 A2) ≥ chainComplexity A1 + Lstar A2 :=
  ⟨(ExtChain.Lstar_dsum_le A1 A2).antisymm (Lstar_dsum_ge A1 A2), chainComplexity_dsum_ge A1 A2⟩

end Lemma1
end AchainsComplexityGF2

/-! # Theorem 1 of Section 2: `L*(A) ≤ 2m + n`

This part of the file proves Theorem 1 of the paper.  It is kept together with the
reduced-complexity theory because the construction of the chain and the bound on its reduced
complexity use the type machinery of this module.
-/

/-!
### Coordinates for the proof of Theorem 1

Set-up of the coordinate system underlying the construction, which proves Theorem 1 of
Section 2 : `L*(A) ≤ 2m + n` for every `m × n` matrix over `GF(2)`.

The ambient space is `Vec (2n+1)`: the first `n` coordinates are the essential variables `X`
(`iX`), the next `n` are the inessential variables `Y` (`iY`), and the last one is the
inessential variable `z` (`iZ`).  The inessential coordinates form `auxSet n`.

An element of the constructed chain then has the shape `⟨a, X⟩ + ⟨b, Y⟩ + ε z`, with type
`(b, ε)`; the embeddings `bX`, `bY` and `bz` place `X`-, `Y`- and `z`-parts into the ambient
space, and the lemmas below record how they behave under addition, projection to the
inessential coordinates, and weight (`proj_aux_bX`, `proj_aux_bY`, `weight_aux_bX`,
`weight_aux_bY`, …).
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false

namespace AchainsComplexityGF2

open scoped BigOperators

/-! ### The three groups of coordinates

The ambient space is `Vec (2n+1)`: coordinates `0,…,n-1` are the essential variables `X`,
coordinates `n,…,2n-1` are the inessential variables `Y`, and coordinate `2n` is the
inessential variable `z`. -/

/-- The `X`-coordinate of the `j`-th column. -/
def iX (n : ℕ) (j : Fin n) : Fin (2 * n + 1) := ⟨j.1, by omega⟩

/-- The `Y`-coordinate of the `j`-th column. -/
def iY (n : ℕ) (j : Fin n) : Fin (2 * n + 1) := ⟨n + j.1, by omega⟩

/-- The coordinate of `z`. -/
def iZ (n : ℕ) : Fin (2 * n + 1) := ⟨2 * n, by omega⟩

/-- The set of inessential coordinates (all of `Y` and `z`). -/
def auxSet (n : ℕ) : Finset (Fin (2 * n + 1)) :=
  Finset.univ.filter (fun p => n ≤ p.1)

theorem mem_auxSet {n : ℕ} {p : Fin (2 * n + 1)} : p ∈ auxSet n ↔ n ≤ p.1 := by
  simp [auxSet]

theorem iX_not_mem_aux (n : ℕ) (j : Fin n) : iX n j ∉ auxSet n := by
  simp [iX, mem_auxSet]

theorem iY_mem_aux (n : ℕ) (j : Fin n) : iY n j ∈ auxSet n := by
  simp [iY, mem_auxSet]

theorem iZ_mem_aux (n : ℕ) : iZ n ∈ auxSet n := by
  rw [mem_auxSet]
  show n ≤ 2 * n
  omega

/-- The vector with `v` on the `X` coordinates and zeros elsewhere. -/
def bX (n : ℕ) (v : Vec n) : Vec (2 * n + 1) :=
  fun p => if h : p.1 < n then v ⟨p.1, h⟩ else 0

/-- The vector with `v` on the `Y` coordinates and zeros elsewhere. -/
def bY (n : ℕ) (v : Vec n) : Vec (2 * n + 1) :=
  fun p => if h : n ≤ p.1 ∧ p.1 < 2 * n then v ⟨p.1 - n, by omega⟩ else 0

/-- The vector with `1` at the coordinate of `z` and zeros elsewhere. -/
def bz (n : ℕ) : Vec (2 * n + 1) := fun p => if p.1 = 2 * n then 1 else 0

@[simp] theorem bX_iX (n : ℕ) (v : Vec n) (j : Fin n) : bX n v (iX n j) = v j := by
  have h : (iX n j).1 < n := by simp [iX]
  simp [bX, h, iX]

@[simp] theorem bX_iY (n : ℕ) (v : Vec n) (j : Fin n) : bX n v (iY n j) = 0 := by
  have h : ¬ (iY n j).1 < n := by simp [iY]
  simp [bX, h]

@[simp] theorem bX_iZ (n : ℕ) (v : Vec n) : bX n v (iZ n) = 0 := by
  have h : ¬ (iZ n).1 < n := by simp only [iZ]; omega
  simp [bX, h]

theorem bX_eq_zero (n : ℕ) (v : Vec n) {p : Fin (2 * n + 1)} (hp : n ≤ p.1) : bX n v p = 0 := by
  have h : ¬ p.1 < n := by omega
  simp [bX, h]

@[simp] theorem bY_iY (n : ℕ) (v : Vec n) (j : Fin n) : bY n v (iY n j) = v j := by
  have h1 : n ≤ (iY n j).1 := by simp [iY]
  have h2 : (iY n j).1 < 2 * n := by simp [iY]; omega
  simp only [bY, dif_pos (show n ≤ (iY n j).1 ∧ (iY n j).1 < 2 * n from ⟨h1, h2⟩)]
  congr 1
  exact Fin.ext (by simp [iY])

@[simp] theorem bY_iX (n : ℕ) (v : Vec n) (j : Fin n) : bY n v (iX n j) = 0 := by
  have h : ¬ (n ≤ (iX n j).1 ∧ (iX n j).1 < 2 * n) := by simp [iX]
  simp [bY, h]

@[simp] theorem bY_iZ (n : ℕ) (v : Vec n) : bY n v (iZ n) = 0 := by
  have h : ¬ (n ≤ (iZ n).1 ∧ (iZ n).1 < 2 * n) := by simp [iZ]
  simp [bY, h]

theorem bY_eq_zero_of_le {n : ℕ} {v : Vec n} {p : Fin (2 * n + 1)} (hp : ¬ n ≤ p.1) :
    bY n v p = 0 := by
  have h : ¬ (n ≤ p.1 ∧ p.1 < 2 * n) := fun hh => hp hh.1
  simp [bY, h]

theorem bY_eq_zero_of_ge {n : ℕ} {v : Vec n} {p : Fin (2 * n + 1)} (hp : 2 * n ≤ p.1) :
    bY n v p = 0 := by
  have h : ¬ (n ≤ p.1 ∧ p.1 < 2 * n) := fun hh => by omega
  simp [bY, h]

@[simp] theorem bz_iZ (n : ℕ) : bz n (iZ n) = 1 := by simp [bz, iZ]

@[simp] theorem bz_iX (n : ℕ) (j : Fin n) : bz n (iX n j) = 0 := by
  have h : (iX n j).1 ≠ 2 * n := by simp [iX]; omega
  simp [bz, h]

@[simp] theorem bz_iY (n : ℕ) (j : Fin n) : bz n (iY n j) = 0 := by
  have h : (iY n j).1 ≠ 2 * n := by simp [iY]; omega
  simp [bz, h]

theorem bz_eq_zero {n : ℕ} {p : Fin (2 * n + 1)} (hp : p.1 ≠ 2 * n) : bz n p = 0 := by
  simp [bz, hp]

/-! ### Additivity of the coordinate embeddings -/

theorem bX_add (n : ℕ) (u v : Vec n) : bX n (u + v) = bX n u + bX n v := by
  funext p
  by_cases h : p.1 < n
  · simp [bX, h]
  · simp [bX, h]

theorem bY_add (n : ℕ) (u v : Vec n) : bY n (u + v) = bY n u + bY n v := by
  funext p
  by_cases h : n ≤ p.1 ∧ p.1 < 2 * n
  · simp [bY, h]
  · simp [bY, h]

theorem sub_self_zmod2 (x : ZMod 2) : x + x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc x + x = 2 * x := by ring
    _ = 0 := by rw [h2, zero_mul]

theorem add_self_vec {n : ℕ} (v : Vec n) : v + v = 0 :=
  funext fun j => sub_self_zmod2 (v j)

theorem bX_add_self (n : ℕ) (v : Vec n) : bX n v + bX n v = 0 := by
  rw [← bX_add, add_self_vec]
  funext p
  simp [bX]

theorem bY_add_self (n : ℕ) (v : Vec n) : bY n v + bY n v = 0 := by
  rw [← bY_add, add_self_vec]
  funext p
  simp [bY]

@[simp] theorem bz_add_self (n : ℕ) : bz n + bz n = 0 := by
  funext p
  by_cases h : p.1 = 2 * n
  · simp [bz, h, sub_self_zmod2]
  · simp [bz, h]

/-! ### Projections and weights -/

theorem proj_aux_bX (n : ℕ) (v : Vec n) : proj (auxSet n) (bX n v) = 0 := by
  funext p
  simp only [Pi.zero_apply]
  by_cases hp : p ∈ auxSet n
  · have := mem_auxSet.mp hp
    rw [proj_apply_mem _ _ hp, bX_eq_zero n v this]
  · rw [proj_apply_not_mem _ _ hp]

theorem proj_aux_bY (n : ℕ) (v : Vec n) : proj (auxSet n) (bY n v) = bY n v := by
  funext p
  by_cases hp : p ∈ auxSet n
  · rw [proj_apply_mem _ _ hp]
  · have h : ¬ n ≤ p.1 := by simpa [mem_auxSet] using hp
    rw [proj_apply_not_mem _ _ hp, bY_eq_zero_of_le h]

theorem proj_aux_bz (n : ℕ) : proj (auxSet n) (bz n) = bz n := by
  funext p
  by_cases hp : p ∈ auxSet n
  · rw [proj_apply_mem _ _ hp]
  · have h : ¬ n ≤ p.1 := by simpa [mem_auxSet] using hp
    rw [proj_apply_not_mem _ _ hp]
    exact (bz_eq_zero (by omega)).symm

theorem weight_aux_bX (n : ℕ) (v : Vec n) : weight (auxSet n) (bX n v) = 0 := by
  unfold weight
  rw [Finset.card_eq_zero, Finset.filter_false_of_mem]
  intro p hp
  rw [bX_eq_zero n v (mem_auxSet.mp hp)]
  simp

theorem weight_aux_bz_le (n : ℕ) : weight (auxSet n) (bz n) = 1 := by
  unfold weight
  have h : (auxSet n).filter (fun p => bz n p ≠ 0) = {iZ n} := by
    ext p
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hne⟩
      by_contra hp
      exact hne (bz_eq_zero (fun h => hp (Fin.ext (by simpa [iZ] using h))))
    · rintro rfl
      exact ⟨iZ_mem_aux n, by simp⟩
  rw [h]
  exact Finset.card_singleton _

theorem weight_aux_bY (n : ℕ) (v : Vec n) :
    weight (auxSet n) (bY n v) = weight (Finset.univ : Finset (Fin n)) v := by
  unfold weight
  have himg : (auxSet n).filter (fun p => bY n v p ≠ 0) =
      (Finset.univ.filter (fun j => v j ≠ 0)).image (iY n) := by
    ext p
    constructor
    · intro hp
      rw [Finset.mem_filter] at hp
      obtain ⟨haux, hne⟩ := hp
      have hn : n ≤ p.1 := mem_auxSet.mp haux
      have hpz : p.1 ≠ 2 * n := by
        intro h
        exact hne (bY_eq_zero_of_ge (by omega))
      have hlt : p.1 < 2 * n := by
        have : p.1 < 2 * n + 1 := p.2
        omega
      have hvne : v ⟨p.1 - n, by omega⟩ ≠ 0 := by
        intro h0
        exact hne (by
          simp only [bY, dif_pos (show n ≤ p.1 ∧ p.1 < 2 * n from ⟨hn, hlt⟩), h0])
      rw [Finset.mem_image]
      refine ⟨⟨p.1 - n, by omega⟩, ?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hvne⟩
      · exact Fin.ext (by simp [iY]; omega)
    · intro hp
      rw [Finset.mem_image] at hp
      obtain ⟨j, hj, rfl⟩ := hp
      rw [Finset.mem_filter] at hj
      rw [Finset.mem_filter]
      exact ⟨iY_mem_aux n j, by simp [hj.2]⟩
  rw [himg, Finset.card_image_of_injective _ (fun a b hab => by
    have := congrArg Fin.val hab
    simp [iY] at this
    exact Fin.ext (by omega))]

end AchainsComplexityGF2

/-! ## Part 3: compressing a vector addition chain -/

/-!
### Compressing a vector addition chain

The first stage of the proof of Theorem 1 of Section 2: from an arbitrary
chain `c` computing a matrix `A` we remove every step that is zero, a basis vector, or a repeat
of an earlier value.

The kept steps are `keepSteps c`, enumerated in order by the order embedding `keepEmb c`; the
resulting chain is `compressedChain c`, whose values are `keepY c`.  In it the values are
pairwise distinct (`keepY_injective`), nonzero and not basis vectors
(`compressedChain_nontrivial`, `compressedChain_first`), hence of weight at least two
(`compressedChain_weight_ge_two`).  It still computes `A` (`compressedChain_computes`) and is
no longer than `c` (`compressedChain_L_le`).

The heavy, pairwise distinct types produced by this compression are what makes the simulation
block of the construction below free of charge.
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace AchainsComplexityGF2

open scoped BigOperators

/-! ### Compressing a chain -/

variable {n : ℕ}

/-- A step of a chain is nontrivial if its value is neither `0` nor a standard basis vector. -/
def ChainStepNontrivial (c : VecAddChain n) (k : Fin c.L) : Prop :=
  c.y k ≠ 0 ∧ ∀ i : Fin n, c.y k ≠ basisVec i

/-- Step `k` is the first occurrence of its value in the chain. -/
def ChainStepFirst (c : VecAddChain n) (k : Fin c.L) : Prop :=
  ∀ j : Fin c.L, j.1 < k.1 → c.y j ≠ c.y k

/-- The steps kept when compressing a chain: first occurrences of nontrivial values. -/
noncomputable def keepSteps (c : VecAddChain n) : Finset (Fin c.L) := by
  classical
  exact Finset.univ.filter (fun k => ChainStepNontrivial c k ∧ ChainStepFirst c k)

@[simp] theorem mem_keepSteps {c : VecAddChain n} {k : Fin c.L} :
    k ∈ keepSteps c ↔ ChainStepNontrivial c k ∧ ChainStepFirst c k := by
  simp [keepSteps]

/-- The increasing enumeration of the kept steps. -/
noncomputable def keepEmb (c : VecAddChain n) : Fin (keepSteps c).card ↪o Fin c.L :=
  (keepSteps c).orderEmbOfFin rfl

theorem keepEmb_mem (c : VecAddChain n) (t : Fin (keepSteps c).card) :
    keepEmb c t ∈ keepSteps c :=
  Finset.orderEmbOfFin_mem _ _ t

/-- Every step value has a first occurrence. -/
theorem exists_first_occ (c : VecAddChain n) (j : Fin c.L) :
    ∃ k : Fin c.L, k.1 ≤ j.1 ∧ c.y k = c.y j ∧ ChainStepFirst c k := by
  classical
  let P : ℕ → Prop := fun m => ∃ h : m < c.L, c.y ⟨m, h⟩ = c.y j
  have hP : ∃ m, P m := ⟨j.1, j.2, rfl⟩
  obtain ⟨hklt, hky⟩ := Nat.find_spec hP
  refine ⟨⟨Nat.find hP, hklt⟩, Nat.find_min' hP ⟨j.2, rfl⟩, hky, ?_⟩
  intro j' hj' hEq
  exact Nat.find_min hP hj' ⟨j'.2, by simpa using hEq.trans hky⟩

/-- A nontrivial step value is the value of some kept step, at an index no larger than the
given one. -/
theorem exists_keepEmb_of_nontrivial (c : VecAddChain n) (j : Fin c.L)
    (h0 : c.y j ≠ 0) (hb : ∀ i : Fin n, c.y j ≠ basisVec i) :
    ∃ t : Fin (keepSteps c).card,
      (keepEmb c t).1 ≤ j.1 ∧ c.y (keepEmb c t) = c.y j := by
  classical
  obtain ⟨k, hkj, hky, hfirst⟩ := exists_first_occ c j
  have hk : k ∈ keepSteps c := by
    refine mem_keepSteps.mpr ⟨⟨?_, ?_⟩, hfirst⟩
    · rwa [hky]
    · intro i; rw [hky]; exact hb i
  have hmem : k ∈ Set.range (keepEmb c) := by
    rw [keepEmb, Finset.range_orderEmbOfFin]
    exact hk
  obtain ⟨t, ht⟩ := hmem
  exact ⟨t, by rw [ht]; exact hkj, by rw [ht]; exact hky⟩

/-- The step of the compressed chain corresponding to a nontrivial value. -/
theorem exists_compress_y_eq (c : VecAddChain n) (j : Fin c.L)
    (h0 : c.y j ≠ 0) (hb : ∀ i : Fin n, c.y j ≠ basisVec i) :
    ∃ t : Fin (keepSteps c).card, c.y (keepEmb c t) = c.y j := by
  obtain ⟨t, -, ht⟩ := exists_keepEmb_of_nontrivial c j h0 hb
  exact ⟨t, ht⟩

/-! ### The compressed chain

A chain is *compressed* by keeping only the first occurrences of its nonzero, non-basis
values.  No value is lost (zero and the basis vectors are always available), so the
compressed chain still computes the same matrix, and all of its steps are nontrivial and
pairwise distinct. -/

/-- The step values of the compressed chain. -/
noncomputable def keepY (c : VecAddChain n) (t : Fin (keepSteps c).card) : Vec n :=
  c.y (keepEmb c t)

/-- A nontrivial value of an earlier step has a first occurrence at a position strictly
before the position of `k` in the compressed chain. -/
theorem exists_resolve (c : VecAddChain n) {t : Fin (keepSteps c).card}
    (j : Fin (keepEmb c t).1)
    (hv : c.y ⟨j.1, lt_trans j.2 (keepEmb c t).2⟩ ≠ 0) :
    ∃ (r : Fin n ⊕ Fin t.1),
      c.y ⟨j.1, lt_trans j.2 (keepEmb c t).2⟩ =
        chainPool (keepY c) t.1 (le_of_lt t.2) r := by
  classical
  by_cases hnt : ChainStepNontrivial c ⟨j.1, lt_trans j.2 (keepEmb c t).2⟩
  · obtain ⟨t', ht'le, ht'val⟩ :=
      exists_keepEmb_of_nontrivial c ⟨j.1, lt_trans j.2 (keepEmb c t).2⟩ hnt.1 hnt.2
    have hlt : (keepEmb c t').1 < (keepEmb c t).1 := lt_of_le_of_lt ht'le j.2
    have htt : t' < t := (keepEmb c).lt_iff_lt.mp hlt
    refine ⟨Sum.inr (⟨t'.1, htt⟩ : Fin t.1), ?_⟩
    show c.y ⟨j.1, lt_trans j.2 (keepEmb c t).2⟩ = keepY c t'
    rw [keepY]
    exact ht'val.symm
  · have hb : ∃ i : Fin n, c.y ⟨j.1, lt_trans j.2 (keepEmb c t).2⟩ = basisVec i := by
      by_contra hcon
      push Not at hcon
      exact hnt ⟨hv, hcon⟩
    obtain ⟨i, hi⟩ := hb
    exact ⟨Sum.inl i, by simpa [chainPool] using hi⟩

/-- The compressed chain: first occurrences of nonzero, non-basis values. -/
noncomputable def compressedChain (c : VecAddChain n) : VecAddChain n where
  L := (keepSteps c).card
  y := keepY c
  valid := by
    intro t
    obtain ⟨hnt, hfirst⟩ := mem_keepSteps.mp (keepEmb_mem c t)
    obtain ⟨a, b, hab⟩ := c.valid (keepEmb c t)
    rcases a with i | j <;> rcases b with i' | j'
    · refine ⟨Sum.inl i, Sum.inl i', ?_⟩
      show keepY c t = chainPool (keepY c) t.1 (le_of_lt t.2) (Sum.inl i) +
        chainPool (keepY c) t.1 (le_of_lt t.2) (Sum.inl i')
      rw [keepY]
      simpa [chainPool] using hab
    · have hj' : c.y ⟨j'.1, lt_trans j'.2 (keepEmb c t).2⟩ ≠ 0 := by
        intro h0
        have hb : c.y (keepEmb c t) = basisVec i := by
          simpa [chainPool, h0] using hab
        exact hnt.2 i hb
      obtain ⟨r, hr⟩ := exists_resolve c j' hj'
      refine ⟨Sum.inl i, r, ?_⟩
      rw [keepY]
      calc c.y (keepEmb c t)
          = basisVec i + c.y ⟨j'.1, lt_trans j'.2 (keepEmb c t).2⟩ := by
            simpa [chainPool] using hab
        _ = chainPool (keepY c) t.1 (le_of_lt t.2) (Sum.inl i) +
              chainPool (keepY c) t.1 (le_of_lt t.2) r := by rw [hr]; rfl
    · have hj : c.y ⟨j.1, lt_trans j.2 (keepEmb c t).2⟩ ≠ 0 := by
        intro h0
        have hb : c.y (keepEmb c t) = basisVec i' := by
          simpa [chainPool, h0] using hab
        exact hnt.2 i' hb
      obtain ⟨r, hr⟩ := exists_resolve c j hj
      refine ⟨r, Sum.inl i', ?_⟩
      rw [keepY]
      calc c.y (keepEmb c t)
          = c.y ⟨j.1, lt_trans j.2 (keepEmb c t).2⟩ + basisVec i' := by
            simpa [chainPool] using hab
        _ = chainPool (keepY c) t.1 (le_of_lt t.2) r +
              chainPool (keepY c) t.1 (le_of_lt t.2) (Sum.inl i') := by rw [hr]; rfl
    · have hj : c.y ⟨j.1, lt_trans j.2 (keepEmb c t).2⟩ ≠ 0 := by
        intro h0
        have he : c.y (keepEmb c t) = c.y ⟨j'.1, lt_trans j'.2 (keepEmb c t).2⟩ := by
          simpa [chainPool, h0] using hab
        exact hfirst ⟨j'.1, lt_trans j'.2 (keepEmb c t).2⟩ j'.2 he.symm
      have hj' : c.y ⟨j'.1, lt_trans j'.2 (keepEmb c t).2⟩ ≠ 0 := by
        intro h0
        have he : c.y (keepEmb c t) = c.y ⟨j.1, lt_trans j.2 (keepEmb c t).2⟩ := by
          simpa [chainPool, h0] using hab
        exact hfirst ⟨j.1, lt_trans j.2 (keepEmb c t).2⟩ j.2 he.symm
      obtain ⟨r1, hr1⟩ := exists_resolve c j hj
      obtain ⟨r2, hr2⟩ := exists_resolve c j' hj'
      refine ⟨r1, r2, ?_⟩
      rw [keepY]
      calc c.y (keepEmb c t)
          = c.y ⟨j.1, lt_trans j.2 (keepEmb c t).2⟩ +
              c.y ⟨j'.1, lt_trans j'.2 (keepEmb c t).2⟩ := by
            simpa [chainPool] using hab
        _ = chainPool (keepY c) t.1 (le_of_lt t.2) r1 +
              chainPool (keepY c) t.1 (le_of_lt t.2) r2 := by rw [hr1, hr2]

/-- Every step of the compressed chain is nontrivial. -/
theorem compressedChain_nontrivial (c : VecAddChain n) (t : Fin (keepSteps c).card) :
    ChainStepNontrivial (compressedChain c) t :=
  (mem_keepSteps.mp (keepEmb_mem c t)).1

/-- Every step of the compressed chain is the first occurrence of its value. -/
theorem compressedChain_first (c : VecAddChain n) (t : Fin (keepSteps c).card) :
    ChainStepFirst (compressedChain c) t := by
  intro t' ht' heq
  exact (mem_keepSteps.mp (keepEmb_mem c t)).2 (keepEmb c t')
    ((keepEmb c).lt_iff_lt.mpr ht') heq

/-- The values of the steps of the compressed chain are pairwise distinct. -/
theorem keepY_injective (c : VecAddChain n) : Function.Injective (keepY c) := by
  intro t t' h
  rcases lt_trichotomy t t' with hlt | heq | hgt
  · have hfirst := (mem_keepSteps.mp (keepEmb_mem c t')).2
    exact absurd (by simpa [keepY] using h)
      (hfirst (keepEmb c t) ((keepEmb c).lt_iff_lt.mpr hlt))
  · exact heq
  · have hfirst := (mem_keepSteps.mp (keepEmb_mem c t)).2
    exact absurd (by simpa [keepY] using h.symm)
      (hfirst (keepEmb c t') ((keepEmb c).lt_iff_lt.mpr hgt))

/-- A nonzero non-basis vector has weight at least two. -/
theorem two_le_weight_of_not_basis {v : Vec n} (h0 : v ≠ 0) (hb : ∀ i, v ≠ basisVec i) :
    2 ≤ weight (Finset.univ : Finset (Fin n)) v := by
  by_contra h
  have h1 : weight (Finset.univ : Finset (Fin n)) v ≤ 1 := by omega
  have hproj : proj (Finset.univ : Finset (Fin n)) v = v := by
    funext j; simp [proj]
  rcases proj_eq_zero_or_basisVec_of_weight_le_one (Finset.univ : Finset (Fin n)) v h1 with
    hz | ⟨i, hi⟩
  · exact h0 (by rw [← hproj]; exact hz)
  · exact hb i (by rw [← hproj]; exact hi)

/-- Every step of the compressed chain has weight at least two. -/
theorem compressedChain_weight_ge_two (c : VecAddChain n) (t : Fin (keepSteps c).card) :
    2 ≤ weight (Finset.univ : Finset (Fin n)) (keepY c t) := by
  have h := compressedChain_nontrivial c t
  exact two_le_weight_of_not_basis h.1 h.2

/-- A vector representable in the original chain is representable in the compressed one. -/
theorem mem_compressed_of_mem (c : VecAddChain n) (a : Vec n)
    (ha : a ∈ Set.range basisVec ∪ Set.range c.y ∪ {0}) :
    a ∈ Set.range basisVec ∪ Set.range (compressedChain c).y ∪ {0} := by
  have ha' : a ∈ Set.range basisVec ∨ a ∈ Set.range c.y ∨ a = 0 := by
    simpa only [Set.mem_union, Set.mem_singleton_iff, or_assoc] using ha
  have key : a ∈ Set.range basisVec ∨ a ∈ Set.range (compressedChain c).y ∨ a = 0 := by
    rcases ha' with hb | hy | hz
    · exact Or.inl hb
    · obtain ⟨j, hj⟩ := hy
      by_cases h0 : c.y j = 0
      · exact Or.inr (Or.inr (by rw [← hj]; exact h0))
      · by_cases hbasis : ∃ i, c.y j = basisVec i
        · obtain ⟨i, hi⟩ := hbasis
          exact Or.inl ⟨i, by rw [← hj]; exact hi.symm⟩
        · push Not at hbasis
          obtain ⟨t, -, ht⟩ := exists_keepEmb_of_nontrivial c j h0 hbasis
          refine Or.inr (Or.inl ⟨t, ?_⟩)
          show keepY c t = a
          rw [keepY, ht]
          exact hj
    · exact Or.inr (Or.inr hz)
  simpa only [Set.mem_union, Set.mem_singleton_iff, or_assoc] using key

/-- The compressed chain still computes the matrix. -/
theorem compressedChain_computes {m : ℕ} (c : VecAddChain n)
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (h : c.Computes A) :
    (compressedChain c).Computes A := by
  intro i
  exact mem_compressed_of_mem c (A i) (h i)

/-- The compressed chain is no longer than the original one. -/
theorem compressedChain_L_le (c : VecAddChain n) : (compressedChain c).L ≤ c.L := by
  classical
  show (keepSteps c).card ≤ c.L
  calc (keepSteps c).card ≤ (Finset.univ : Finset (Fin c.L)).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = c.L := by simp

end AchainsComplexityGF2

/-!
### The chain of Theorem 1 and its reduced complexity

The construction proving Theorem 1:

`Lstar A ≤ 2 * m + n` for every matrix `A` over `GF(2)` with `m` rows and `n` columns.

It follows the paper.  Let `X = (x₁,…,xₙ)` be the essential variables and let
`Y = (y₁,…,yₙ)`, `z` be inessential ones.  Working from a *compressed* chain for `A` (all its
values are nonzero, not basis vectors, and pairwise distinct), we build an extended chain whose
steps fall in four blocks:

* `n` steps `xⱼ + yⱼ`, whose types are `eⱼ` and have weight `1` (the only light steps besides
  the last ones of the rows);
* for every nonzero `a ∈ GF(2)ⁿ` one step computing `z + ⟨a, Y⟩`; its type has weight
  `|a| + 1 ≥ 2` and the types are pairwise distinct, so these steps cost nothing;
* a simulation of the compressed chain: every value `v` is replaced by `(v, v)`; the types are
  the values `v` themselves, of weight `|v| ≥ 2` and pairwise distinct, so again free;
* for every row `aᵢ` which is neither `0` nor a basis vector, two steps `⟨aᵢ, Y⟩` and
  `⟨aᵢ, X⟩`.  The type of the first one is `aᵢ`, already present among the simulation types,
  and the second one has type `0`.  Both therefore contribute one unit each.

The reduced complexity is thus `n + 2·#{i | aᵢ ∉ {0} ∪ {eⱼ}} ≤ n + 2m`.
-/

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option warn.classDefReducibility false

namespace AchainsComplexityGF2

open scoped BigOperators

/-! ### A linear order on `Vec n` compatible with the weight

To enumerate the nonzero vectors in an order in which the support can be built up one
coordinate at a time, we order them lexicographically by `(weight, position)`. -/

variable {n : ℕ}

/-- The sort key of a vector: its weight, then its position in a fixed enumeration. -/
noncomputable def vecKey (n : ℕ) (v : Vec n) : Lex (ℕ × ℕ) :=
  toLex (weight (Finset.univ : Finset (Fin n)) v, (Fintype.equivFin (Vec n) v).val)

theorem vecKey_injective (n : ℕ) : Function.Injective (vecKey n) := by
  intro u v h
  have h' : (weight (Finset.univ : Finset (Fin n)) u, (Fintype.equivFin (Vec n) u).val) =
      (weight (Finset.univ : Finset (Fin n)) v, (Fintype.equivFin (Vec n) v).val) := by
    simpa [vecKey] using h
  have h2 : (Fintype.equivFin (Vec n) u).val = (Fintype.equivFin (Vec n) v).val :=
    congrArg Prod.snd h'
  exact (Fintype.equivFin (Vec n)).injective (Fin.ext h2)

/-- The linear order on `Vec n` induced by `vecKey`. -/
noncomputable def vecOrder (n : ℕ) : LinearOrder (Vec n) :=
  LinearOrder.lift' (vecKey n) (vecKey_injective n)

attribute [local instance] vecOrder

/-- The set of nonzero vectors. -/
noncomputable def nzSet (n : ℕ) : Finset (Vec n) := Finset.univ.filter (fun v => v ≠ 0)

theorem card_vec (n : ℕ) : Fintype.card (Vec n) = 2 ^ n := by
  simp [Vec, ZMod.card]

theorem nzSet_card (n : ℕ) : (nzSet n).card = 2 ^ n - 1 := by
  have h : nzSet n = Finset.univ.erase (0 : Vec n) := by
    ext v
    simp [nzSet, Finset.mem_erase]
  rw [h, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_vec]

/-- The increasing enumeration of the nonzero vectors. -/
noncomputable def nzEmb (n : ℕ) : Fin (2 ^ n - 1) ↪o Vec n :=
  (nzSet n).orderEmbOfFin (nzSet_card n)

theorem nzEmb_mem (n : ℕ) (k : Fin (2 ^ n - 1)) : nzEmb n k ∈ nzSet n :=
  Finset.orderEmbOfFin_mem (nzSet n) (nzSet_card n) k

theorem nzEmb_ne_zero (n : ℕ) (k : Fin (2 ^ n - 1)) : nzEmb n k ≠ 0 := by
  have := nzEmb_mem n k
  simpa [nzSet] using this

theorem nzEmb_injective (n : ℕ) : Function.Injective (nzEmb n) := (nzEmb n).injective

theorem nzEmb_range (n : ℕ) : Set.range (nzEmb n) = (nzSet n : Set (Vec n)) := by
  rw [show nzEmb n = (nzSet n).orderEmbOfFin (nzSet_card n) from rfl]
  exact Finset.range_orderEmbOfFin _ _

theorem exists_nzEmb_eq (n : ℕ) {v : Vec n} (hv : v ∈ nzSet n) :
    ∃ k : Fin (2 ^ n - 1), nzEmb n k = v := by
  have h : v ∈ Set.range (nzEmb n) := by
    rw [nzEmb_range]
    exact hv
  exact h

theorem vecOrder_lt_of_weight_lt {u v : Vec n}
    (h : weight (Finset.univ : Finset (Fin n)) u < weight (Finset.univ : Finset (Fin n)) v) :
    u < v := by
  change vecKey n u < vecKey n v
  exact Prod.Lex.left _ _ h

theorem nzEmb_lt_of_weight_lt (n : ℕ) {k l : Fin (2 ^ n - 1)}
    (h : weight (Finset.univ : Finset (Fin n)) (nzEmb n k) <
         weight (Finset.univ : Finset (Fin n)) (nzEmb n l)) : k < l :=
  (nzEmb n).lt_iff_lt.mp (vecOrder_lt_of_weight_lt h)

/-! ### Extending a chain by a block of steps

A block of `K` new steps may use the basis vectors, the values of the prefix chain and the
values of the earlier steps of the block itself. -/

/-- The pool of a block of `K` steps at position `k`. -/
abbrev BlockPool (m L k : ℕ) := Fin m ⊕ (Fin L ⊕ Fin k)

/-- The value of an element of a block pool: a basis vector, a value of the prefix chain, or a
value of an earlier step of the block. -/
def blockPoolVal {m : ℕ} (c : VecAddChain m) {K : ℕ} (w : Fin K → Vec m) {k : ℕ} (hk : k ≤ K) :
    BlockPool m c.L k → Vec m
  | Sum.inl i => basisVec i
  | Sum.inr (Sum.inl j) => c.y j
  | Sum.inr (Sum.inr j) => w ⟨j.1, lt_of_lt_of_le j.2 hk⟩

/-- Embed a block pool element into the pool of the extended chain. -/
def blockPoolMap {m L : ℕ} (k : ℕ) :
    BlockPool m L k → Fin m ⊕ Fin (L + k)
  | Sum.inl i => Sum.inl i
  | Sum.inr (Sum.inl j) => Sum.inr (Fin.castAdd k j)
  | Sum.inr (Sum.inr j) => Sum.inr (Fin.natAdd L j)

theorem append_apply_castAdd {m : ℕ} (c : VecAddChain m) (K : ℕ) (w : Fin K → Vec m)
    (j : Fin c.L) : Fin.append c.y w (Fin.castAdd K j) = c.y j :=
  Fin.append_left _ _ j

theorem append_apply_natAdd {m : ℕ} (c : VecAddChain m) (K : ℕ) (w : Fin K → Vec m)
    (k : Fin K) : Fin.append c.y w (Fin.natAdd c.L k) = w k :=
  Fin.append_right _ _ k

theorem chainPool_append_castAdd {m : ℕ} (c : VecAddChain m) (K : ℕ) (w : Fin K → Vec m)
    {k : ℕ} (hk : k < K) (hkL : c.L + k ≤ c.L + K) (j : Fin c.L) :
    chainPool (Fin.append c.y w) (c.L + k) hkL (Sum.inr (Fin.castAdd k j)) = c.y j := by
  simp only [chainPool]
  exact append_apply_castAdd c K w j

theorem chainPool_append_natAdd {m : ℕ} (c : VecAddChain m) (K : ℕ) (w : Fin K → Vec m)
    {k : ℕ} (hk : k < K) (hkL : c.L + k ≤ c.L + K) (j : Fin k) :
    chainPool (Fin.append c.y w) (c.L + k) hkL (Sum.inr (Fin.natAdd c.L j))
      = w ⟨j.1, lt_trans j.2 hk⟩ := by
  simp only [chainPool]
  exact append_apply_natAdd c K w ⟨j.1, lt_trans j.2 hk⟩

theorem chainPool_append_prefix {m : ℕ} (c : VecAddChain m) (K : ℕ) (w : Fin K → Vec m)
    {k : ℕ} (hk : k ≤ c.L + K) (hk' : k ≤ c.L) (s : Fin m ⊕ Fin k) :
    chainPool (Fin.append c.y w) k hk s = chainPool c.y k hk' s := by
  cases s with
  | inl i => rfl
  | inr j =>
      simp only [chainPool]
      exact append_apply_castAdd c K w ⟨j.1, lt_of_lt_of_le j.2 hk'⟩

theorem chainPool_blockPoolMap {m : ℕ} (c : VecAddChain m) (K : ℕ) (w : Fin K → Vec m)
    {k : ℕ} (hk : k < K) (hkL : c.L + k ≤ c.L + K) (s : BlockPool m c.L k) :
    chainPool (Fin.append c.y w) (c.L + k) hkL (blockPoolMap k s)
      = blockPoolVal c w (le_of_lt hk) s := by
  cases s with
  | inl i => rfl
  | inr s' =>
      cases s' with
      | inl j => exact chainPool_append_castAdd c K w hk hkL j
      | inr j => exact chainPool_append_natAdd c K w hk hkL j

/-- Extend the sequence of a chain by a block of `K` steps. -/
theorem exists_extend_y {m : ℕ} (c : VecAddChain m) (K : ℕ) (w : Fin K → Vec m)
    (h : ∀ k : Fin K, ∃ a b : BlockPool m c.L k.1,
      w k = blockPoolVal c w (le_of_lt k.2) a + blockPoolVal c w (le_of_lt k.2) b) :
    ∃ y' : Fin (c.L + K) → Vec m,
      (∀ j : Fin c.L, y' (Fin.castAdd K j) = c.y j) ∧
      (∀ k : Fin K, y' (Fin.natAdd c.L k) = w k) ∧
      (∀ i : Fin (c.L + K), ∃ a b : Fin m ⊕ Fin i.1,
        y' i = chainPool y' i.1 (le_of_lt i.2) a + chainPool y' i.1 (le_of_lt i.2) b) := by
  classical
  refine ⟨Fin.append c.y w, fun j => append_apply_castAdd c K w j,
    fun k => append_apply_natAdd c K w k, ?_⟩
  intro i
  induction i using Fin.addCases with
  | left j =>
      obtain ⟨a, b, hab⟩ := c.valid j
      refine ⟨a, b, ?_⟩
      rw [append_apply_castAdd, hab]
      simp only [Fin.val_castAdd]
      rw [chainPool_append_prefix c K w (by omega) (le_of_lt j.2),
        chainPool_append_prefix c K w (by omega) (le_of_lt j.2)]
  | right k =>
      obtain ⟨a, b, hab⟩ := h k
      refine ⟨blockPoolMap k.1 a, blockPoolMap k.1 b, ?_⟩
      rw [append_apply_natAdd, hab]
      simp only [Fin.val_natAdd]
      rw [chainPool_blockPoolMap c K w k.2 (by omega) a,
        chainPool_blockPoolMap c K w k.2 (by omega) b]

/-- The empty chain. -/
def emptyChain (m : ℕ) : VecAddChain m where
  L := 0
  y := fun k => k.elim0
  valid := fun k => k.elim0

/-! ### The basic step vectors of the construction

The ambient space is `Vec (2n+1)`: the essential coordinates `X = iX`, the inessential
coordinates `Y = iY` and the inessential coordinate `z = iZ`. -/

/-- The support of a vector. -/
noncomputable def supp (n : ℕ) (v : Vec n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => v j ≠ 0)

theorem weight_eq_card_supp {n : ℕ} (v : Vec n) :
    weight (Finset.univ : Finset (Fin n)) v = (supp n v).card := rfl

theorem bX_basisVec (n : ℕ) (j : Fin n) : bX n (basisVec j) = basisVec (iX n j) := by
  funext p
  simp only [bX, basisVec]
  by_cases hp : p.1 < n
  · rw [dif_pos hp]
    by_cases h : (⟨p.1, hp⟩ : Fin n) = j
    · have hpi : p = iX n j := Fin.ext (by simpa [iX] using congrArg Fin.val h)
      rw [if_pos h, if_pos hpi]
    · have hpi : p ≠ iX n j := by
        intro hh
        exact h (Fin.ext (by simpa [iX] using congrArg Fin.val hh))
      rw [if_neg h, if_neg hpi]
  · rw [dif_neg hp]
    have hpi : p ≠ iX n j := by
      intro hh
      have hv := congrArg Fin.val hh
      simp [iX] at hv
      omega
    rw [if_neg hpi]

theorem bY_basisVec (n : ℕ) (j : Fin n) : bY n (basisVec j) = basisVec (iY n j) := by
  funext p
  simp only [bY, basisVec]
  by_cases hp : n ≤ p.1 ∧ p.1 < 2 * n
  · rw [dif_pos hp]
    by_cases h : (⟨p.1 - n, by omega⟩ : Fin n) = j
    · have hv : p.1 - n = j.1 := congrArg Fin.val h
      have hpi : p = iY n j := Fin.ext (by simp [iY]; omega)
      rw [if_pos h, if_pos hpi]
    · have hpi : p ≠ iY n j := by
        intro hh
        have hv : p.1 = n + j.1 := by
          have := congrArg Fin.val hh
          simpa [iY] using this
        exact h (Fin.ext (by show p.1 - n = j.1; omega))
      rw [if_neg h, if_neg hpi]
  · rw [dif_neg hp]
    have hpi : p ≠ iY n j := by
      intro hh
      have hv : p.1 = n + j.1 := by
        have := congrArg Fin.val hh
        simpa [iY] using this
      exact hp ⟨by omega, by omega⟩
    rw [if_neg hpi]

/-- The light step `xⱼ + yⱼ`. -/
noncomputable def lightY (n : ℕ) (j : Fin n) : Vec (2 * n + 1) :=
  basisVec (iX n j) + basisVec (iY n j)

/-- The step `z + ⟨a, Y⟩`. -/
noncomputable def lamY (n : ℕ) (a : Vec n) : Vec (2 * n + 1) := bz n + bY n a

/-- The simulation step `⟨a, X⟩ + ⟨a, Y⟩` of a value `a`. -/
noncomputable def simY (n : ℕ) (a : Vec n) : Vec (2 * n + 1) := bX n a + bY n a

theorem lightY_eq (n : ℕ) (j : Fin n) :
    lightY n j = bX n (basisVec j) + bY n (basisVec j) := by
  simp [lightY, bX_basisVec, bY_basisVec]

/-! ### Weights and types of the three families of steps -/

theorem iZ_not_mem_image_iY (n : ℕ) : iZ n ∉ (Finset.univ : Finset (Fin n)).image (iY n) := by
  intro h
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
  have hv : iY n j = iZ n := hj
  have := congrArg Fin.val hv
  simp [iY, iZ] at this
  omega

theorem iZ_not_mem_image_iY_supp (n : ℕ) (a : Vec n) :
    iZ n ∉ (supp n a).image (iY n) := by
  intro h
  obtain ⟨j, -, hj⟩ := Finset.mem_image.mp h
  exact iZ_not_mem_image_iY n (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)

theorem filter_aux_lamY (n : ℕ) (a : Vec n) :
    (auxSet n).filter (fun p => (bz n + bY n a) p ≠ 0)
      = insert (iZ n) ((supp n a).image (iY n)) := by
  ext p
  rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨haux, hne⟩
    have hn : n ≤ p.1 := mem_auxSet.mp haux
    by_cases hz : p.1 = 2 * n
    · left
      exact Fin.ext (by simp [iZ, hz])
    · right
      have hlt : p.1 < 2 * n := by have := p.2; omega
      refine ⟨⟨p.1 - n, by omega⟩, ?_, ?_⟩
      · rw [supp, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        intro h0
        apply hne
        rw [Pi.add_apply, bz_eq_zero hz, bY, dif_pos (show n ≤ p.1 ∧ p.1 < 2 * n from ⟨hn, hlt⟩),
          h0, add_zero]
      · exact Fin.ext (by simp [iY]; omega)
  · rintro (hp | ⟨j, hj, hj'⟩)
    · rw [hp]
      exact ⟨iZ_mem_aux n, by simp⟩
    · rw [supp, Finset.mem_filter] at hj
      rw [← hj']
      exact ⟨iY_mem_aux n j, by simp [bY_iY, hj.2]⟩

theorem weight_aux_lamY (n : ℕ) (a : Vec n) :
    weight (auxSet n) (bz n + bY n a) = weight (Finset.univ : Finset (Fin n)) a + 1 := by
  unfold weight
  rw [filter_aux_lamY, Finset.card_insert_of_notMem (iZ_not_mem_image_iY_supp n a),
    Finset.card_image_of_injective _ (fun x y h => by
      have hv : iY n x = iY n y := h
      have := congrArg Fin.val hv
      simp [iY] at this
      exact Fin.ext (by omega))]
  rfl

theorem filter_aux_simY (n : ℕ) (a : Vec n) :
    (auxSet n).filter (fun p => (bX n a + bY n a) p ≠ 0) = (supp n a).image (iY n) := by
  ext p
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨haux, hne⟩
    have hn : n ≤ p.1 := mem_auxSet.mp haux
    have hz : p.1 ≠ 2 * n := by
      intro h
      apply hne
      rw [Pi.add_apply, bX_eq_zero n a hn, bY_eq_zero_of_ge (by omega)]
      simp
    have hlt : p.1 < 2 * n := by have := p.2; omega
    refine ⟨⟨p.1 - n, by omega⟩, ?_, ?_⟩
    · rw [supp, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      intro h0
      apply hne
      rw [Pi.add_apply, bX_eq_zero n a hn,
        bY, dif_pos (show n ≤ p.1 ∧ p.1 < 2 * n from ⟨hn, hlt⟩), h0, add_zero]
    · exact Fin.ext (by simp [iY]; omega)
  · rintro ⟨j, hj, hj'⟩
    rw [supp, Finset.mem_filter] at hj
    rw [← hj']
    exact ⟨iY_mem_aux n j, by simp [bX_iY, bY_iY, hj.2]⟩

theorem weight_aux_simY (n : ℕ) (a : Vec n) :
    weight (auxSet n) (bX n a + bY n a) = weight (Finset.univ : Finset (Fin n)) a := by
  unfold weight
  rw [filter_aux_simY, Finset.card_image_of_injective _ (fun x y h => by
    have hv : iY n x = iY n y := h
    have := congrArg Fin.val hv
    simp [iY] at this
    exact Fin.ext (by omega))]
  rfl

theorem weight_aux_lightY (n : ℕ) (j : Fin n) : weight (auxSet n) (lightY n j) = 1 := by
  have h : lightY n j = simY n (basisVec j) := by
    simp [lightY, simY, bX_basisVec, bY_basisVec]
  rw [h, simY, weight_aux_simY]
  unfold weight
  have hsupp : (Finset.univ : Finset (Fin n)).filter (fun i => basisVec j i ≠ 0) = {j} := by
    ext i
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hne⟩
      by_contra hji
      exact hne (by simp [basisVec, hji])
    · rintro rfl
      exact ⟨Finset.mem_univ _, by simp⟩
  rw [hsupp]
  simp

/-! ### Algebra of the step vectors -/

theorem bz_eq_basisVec (n : ℕ) : bz n = basisVec (iZ n) := by
  funext p
  simp only [bz, basisVec]
  by_cases h : p = iZ n
  · subst h
    simp [iZ]
  · have hv : p.1 ≠ 2 * n := by
      intro hh
      exact h (Fin.ext (by simp [iZ, hh]))
    simp [h, hv]

theorem simY_eq (n : ℕ) (a : Vec n) : simY n a = bX n a + bY n a := rfl

theorem simY_add (n : ℕ) (u v : Vec n) :
    simY n (u + v) = simY n u + simY n v := by
  simp only [simY, bX_add, bY_add]
  abel

theorem proj_aux_lamY (n : ℕ) (a : Vec n) : proj (auxSet n) (lamY n a) = lamY n a := by
  rw [lamY, proj_add, proj_aux_bz, proj_aux_bY]

theorem proj_aux_simY (n : ℕ) (a : Vec n) : proj (auxSet n) (simY n a) = bY n a := by
  rw [simY, proj_add, proj_aux_bX, proj_aux_bY, zero_add]

theorem lamY_type_injective {n : ℕ} {a a' : Vec n}
    (h : proj (auxSet n) (lamY n a) = proj (auxSet n) (lamY n a')) : a = a' := by
  funext j
  have hc := congrFun h (iY n j)
  rw [proj_apply_mem (auxSet n) (lamY n a) (iY_mem_aux n j),
    proj_apply_mem (auxSet n) (lamY n a') (iY_mem_aux n j)] at hc
  simpa [lamY, bz_iY, bY_iY] using hc

theorem simY_type_injective {n : ℕ} {a a' : Vec n}
    (h : proj (auxSet n) (simY n a) = proj (auxSet n) (simY n a')) : a = a' := by
  funext j
  have hc := congrFun h (iY n j)
  simpa [proj_aux_simY, bY_iY] using hc

theorem lamY_type_ne_simY_type (n : ℕ) (a v : Vec n) :
    proj (auxSet n) (lamY n a) ≠ proj (auxSet n) (simY n v) := by
  intro h
  have hc := congrFun h (iZ n)
  rw [proj_apply_mem (auxSet n) (lamY n a) (iZ_mem_aux n),
    proj_apply_mem (auxSet n) (simY n v) (iZ_mem_aux n)] at hc
  simp [lamY, simY, bz_iZ, bY_iZ, bX_iZ] at hc

theorem weight_aux_lamY_ge_two (n : ℕ) {a : Vec n} (ha : a ≠ 0) :
    2 ≤ weight (auxSet n) (lamY n a) := by
  rw [lamY, weight_aux_lamY]
  have hpos : 0 < weight (Finset.univ : Finset (Fin n)) a := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    have hp : proj (Finset.univ : Finset (Fin n)) a = 0 := (weight_eq_zero_iff _ _).mp h0
    exact ha (by
      have hid : proj (Finset.univ : Finset (Fin n)) a = a := by
        funext i; simp [proj]
      rw [hid] at hp
      exact hp)
  omega

theorem weight_aux_simY_ge_two (n : ℕ) {a : Vec n}
    (ha : 2 ≤ weight (Finset.univ : Finset (Fin n)) a) :
    2 ≤ weight (auxSet n) (simY n a) := by
  rw [simY, weight_aux_simY]
  exact ha

theorem bY_eq_lamY_add_bz (n : ℕ) (a : Vec n) : bY n a = lamY n a + bz n := by
  rw [lamY]
  calc bY n a = bY n a + (bz n + bz n) := by rw [bz_add_self, add_zero]
    _ = (bz n + bY n a) + bz n := by abel

theorem bX_eq_simY_add_bY (n : ℕ) (a : Vec n) : bX n a = simY n a + bY n a := by
  rw [simY, add_assoc, bY_add_self, add_zero]

theorem lamY_add_basisVec (n : ℕ) (a : Vec n) (i : Fin n) :
    lamY n (a + basisVec i) + basisVec (iY n i) = lamY n a := by
  rw [lamY, lamY, bY_add, bY_basisVec]
  calc bz n + (bY n a + basisVec (iY n i)) + basisVec (iY n i)
      = bz n + bY n a + (basisVec (iY n i) + basisVec (iY n i)) := by abel
    _ = bz n + bY n a := by rw [add_self_vec, add_zero]

theorem exists_apply_ne_zero {n : ℕ} {a : Vec n} (ha : a ≠ 0) : ∃ i, a i ≠ 0 := by
  by_contra h
  push Not at h
  exact ha (funext h)

theorem supp_add_basisVec {n : ℕ} (a : Vec n) {i : Fin n} (hi : a i ≠ 0) :
    supp n (a + basisVec i) = (supp n a).erase i := by
  ext j
  simp only [supp, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and]
  by_cases hji : j = i
  · subst hji
    have hai : a j = 1 := Circuit.zmod2_eq_one_of_ne_zero (a j) hi
    simp [basisVec, hai]
    decide
  · have hb : basisVec i j = 0 := by simp [basisVec, hji]
    simp [hb, hji]

theorem weight_add_basisVec {n : ℕ} (a : Vec n) {i : Fin n} (hi : a i ≠ 0) :
    weight (Finset.univ : Finset (Fin n)) (a + basisVec i)
      = weight (Finset.univ : Finset (Fin n)) a - 1 := by
  have hsupp := supp_add_basisVec a hi
  have h1 : weight (Finset.univ : Finset (Fin n)) (a + basisVec i)
      = (supp n (a + basisVec i)).card := rfl
  have h2 : weight (Finset.univ : Finset (Fin n)) a = (supp n a).card := rfl
  rw [h1, h2, hsupp, Finset.card_erase_of_mem]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩

theorem weight_add_basisVec_lt {n : ℕ} {a : Vec n} {i : Fin n} (hi : a i ≠ 0)
    (h2 : 2 ≤ weight (Finset.univ : Finset (Fin n)) a) :
    weight (Finset.univ : Finset (Fin n)) (a + basisVec i)
      < weight (Finset.univ : Finset (Fin n)) a := by
  rw [weight_add_basisVec a hi]
  omega

theorem add_basisVec_ne_zero {n : ℕ} {a : Vec n} {i : Fin n} (hi : a i ≠ 0)
    (h2 : 2 ≤ weight (Finset.univ : Finset (Fin n)) a) : a + basisVec i ≠ 0 := by
  intro h0
  have hw : weight (Finset.univ : Finset (Fin n)) (a + basisVec i) = 0 := by
    rw [h0]; simp [weight]
  rw [weight_add_basisVec a hi] at hw
  omega

theorem add_basisVec_add_basisVec {n : ℕ} (a : Vec n) (i : Fin n) :
    (a + basisVec i) + basisVec i = a := by
  rw [add_assoc, add_self_vec, add_zero]

/-! ### The rows that need explicit work

A row of `A` is already available in the chain, free of charge, when it is `0` or a basis
vector.  The remaining rows are the ones we have to compute explicitly, at a cost of two
steps each. -/

variable {m n : ℕ}

/-- The rows of `A` which are neither zero nor basis vectors. -/
noncomputable def workRows (A : Matrix (Fin m) (Fin n) (ZMod 2)) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => A i ≠ 0 ∧ ∀ j : Fin n, A i ≠ basisVec j)

theorem mem_workRows {A : Matrix (Fin m) (Fin n) (ZMod 2)} {i : Fin m} :
    i ∈ workRows A ↔ A i ≠ 0 ∧ ∀ j : Fin n, A i ≠ basisVec j := by
  simp [workRows]

/-- The increasing enumeration of the rows of `A` that are neither zero nor basis vectors. -/
noncomputable def workEmb (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Fin (workRows A).card ↪o Fin m :=
  (workRows A).orderEmbOfFin rfl

theorem workEmb_mem (A : Matrix (Fin m) (Fin n) (ZMod 2)) (r : Fin (workRows A).card) :
    workEmb A r ∈ workRows A :=
  Finset.orderEmbOfFin_mem (workRows A) rfl r

/-- A nonzero non-basis row of a computed matrix occurs among the values of the compressed
chain. -/
theorem exists_keepY_eq_of_computes {c : VecAddChain n} {A : Matrix (Fin m) (Fin n) (ZMod 2)}
    (h : c.Computes A) {i : Fin m} (h0 : A i ≠ 0) (hb : ∀ j : Fin n, A i ≠ basisVec j) :
    ∃ t : Fin (keepSteps c).card, keepY c t = A i := by
  have ha := h i
  rw [Set.mem_union, Set.mem_union] at ha
  refine ha.elim ?_ ?_
  · intro hpq
    refine hpq.elim ?_ ?_
    · intro h1
      obtain ⟨j, hj⟩ := h1
      exact absurd hj.symm (hb j)
    · intro h2
      obtain ⟨j, hj⟩ := h2
      have hv : c.y j ≠ 0 := by rw [hj]; exact h0
      have hb' : ∀ k : Fin n, c.y j ≠ basisVec k := by rw [hj]; exact hb
      obtain ⟨t, ht⟩ := exists_compress_y_eq c j hv hb'
      exact ⟨t, by rw [keepY, ht, hj]⟩
  · intro h3
    exact absurd h3 h0

/-- The compressed-chain step which computes the row `workEmb A r`. -/
noncomputable def rowIdx (A : Matrix (Fin m) (Fin n) (ZMod 2)) {c : VecAddChain n}
    (h : c.Computes A) (r : Fin (workRows A).card) : Fin (keepSteps c).card :=
  Classical.choose (exists_keepY_eq_of_computes h (i := workEmb A r)
    (mem_workRows.mp (workEmb_mem A r)).1 (mem_workRows.mp (workEmb_mem A r)).2)

theorem rowIdx_spec (A : Matrix (Fin m) (Fin n) (ZMod 2)) {c : VecAddChain n}
    (h : c.Computes A) (r : Fin (workRows A).card) :
    keepY c (rowIdx A h r) = A (workEmb A r) :=
  Classical.choose_spec (exists_keepY_eq_of_computes h (i := workEmb A r)
    (mem_workRows.mp (workEmb_mem A r)).1 (mem_workRows.mp (workEmb_mem A r)).2)

/-! ### The four blocks of the construction

The extended chain is built over `2n + 1` variables: `n` essential variables `X`, `n`
inessential variables `Y` and one inessential variable `z`.  Its steps are concatenated from
four blocks:

* `wA`: the `n` light steps `xⱼ + yⱼ`;
* `wB`: the steps `z + ⟨a, Y⟩` for all nonzero `a`, built up coordinate by coordinate in the
  order of `nzEmb`;
* `wC`: the simulation `⟨v, X⟩ + ⟨v, Y⟩` of every value `v` of the compressed chain;
* `wD`: for every row `aᵢ` that is neither zero nor a basis vector, the two steps
  `⟨aᵢ, Y⟩` and `⟨aᵢ, X⟩`.
-/

/-- The length of the first block. -/
abbrev lenA (n : ℕ) : ℕ := n

/-- The length of the second block. -/
abbrev lenB (n : ℕ) : ℕ := 2 ^ n - 1

/-- The length of the third block. -/
noncomputable abbrev lenC {n : ℕ} (c : VecAddChain n) : ℕ := (keepSteps c).card

/-- The length of the fourth block. -/
noncomputable abbrev lenD {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) : ℕ :=
  2 * (workRows A).card

/-- The total length of the constructed chain. -/
noncomputable abbrev chainLen {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (c : VecAddChain n) : ℕ :=
  lenA n + (lenB n + (lenC c + lenD A))

/-- The values of the first block: `xⱼ + yⱼ`. -/
noncomputable def wA (n : ℕ) : Fin (lenA n) → Vec (2 * n + 1) :=
  fun j => lightY n j

/-- The values of the second block: `z + ⟨a, Y⟩` for all nonzero `a`. -/
noncomputable def wB (n : ℕ) : Fin (lenB n) → Vec (2 * n + 1) :=
  fun k => lamY n (nzEmb n k)

/-- The values of the third block: the simulation `⟨v, X⟩ + ⟨v, Y⟩`. -/
noncomputable def wC {n : ℕ} (c : VecAddChain n) : Fin (lenC c) → Vec (2 * n + 1) :=
  fun t => simY n (keepY c t)

/-- The row of `A` addressed by an element of `workRows`. -/
noncomputable def rowA (A : Matrix (Fin m) (Fin n) (ZMod 2)) (r : Fin (workRows A).card) :
    Vec n :=
  A (workEmb A r)

/-- The values of the fourth block: `⟨aᵢ, Y⟩` and then `⟨aᵢ, X⟩` for every row which is
neither zero nor a basis vector. -/
noncomputable def wD (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Fin (lenD A) → Vec (2 * n + 1) :=
  fun d => if hd : d.1 < (workRows A).card
    then bY n (rowA A ⟨d.1, hd⟩)
    else bX n (rowA A ⟨d.1 - (workRows A).card, by
      have h := d.2
      simp only [lenD] at h
      omega⟩)

/-- The sequence of the constructed chain: the concatenation of the four blocks. -/
noncomputable def chainY (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n) :
    Fin (chainLen A c) → Vec (2 * n + 1) :=
  Fin.addCases (wA n) (Fin.addCases (wB n) (Fin.addCases (wC c) (wD A)))

theorem chainY_A (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n) (j : Fin (lenA n)) :
    chainY A c (Fin.castAdd (lenB n + (lenC c + lenD A)) j) = lightY n j := by
  simp [chainY, wA]

theorem chainY_B (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n) (k : Fin (lenB n)) :
    chainY A c (Fin.natAdd (lenA n) (Fin.castAdd (lenC c + lenD A) k))
      = lamY n (nzEmb n k) := by
  simp [chainY, wB]

theorem chainY_C (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n) (t : Fin (lenC c)) :
    chainY A c (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.castAdd (lenD A) t)))
      = simY n (keepY c t) := by
  simp [chainY, wC]

theorem chainY_D (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n) (d : Fin (lenD A)) :
    chainY A c (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.natAdd (lenC c) d)))
      = wD A d := by
  simp [chainY, wD]

/-! ### Elementary facts used by the construction -/

theorem iX_injective (n : ℕ) : Function.Injective (iX n) := by
  intro j j' h
  have hv := congrArg Fin.val h
  simp [iX] at hv
  exact Fin.ext hv

theorem weight_pos_of_ne_zero {n : ℕ} {a : Vec n} (ha : a ≠ 0) :
    0 < weight (Finset.univ : Finset (Fin n)) a := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  have hp : proj (Finset.univ : Finset (Fin n)) a = 0 := (weight_eq_zero_iff _ _).mp h0
  exact ha (by
    have hid : proj (Finset.univ : Finset (Fin n)) a = a := by funext i; simp [proj]
    rw [hid] at hp
    exact hp)

theorem eq_basisVec_of_weight_eq_one {n : ℕ} {a : Vec n}
    (h : weight (Finset.univ : Finset (Fin n)) a = 1) : ∃ i : Fin n, a = basisVec i := by
  obtain ⟨i, hi⟩ := proj_eq_basisVec_of_weight_eq_one (Finset.univ : Finset (Fin n)) a h
  exact ⟨i, by rw [← hi]; funext j; simp [proj]⟩

theorem nzSet_of_ne_zero {n : ℕ} {a : Vec n} (ha : a ≠ 0) : a ∈ nzSet n := by
  simp [nzSet, ha]

/-- The first half of the fourth block fits into the block length. -/
theorem lt_lenD_left {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (r : Fin (workRows A).card) : r.1 < lenD A := by
  have h := r.2
  show r.1 < 2 * (workRows A).card
  omega

/-- The second half of the fourth block fits into the block length. -/
theorem lt_lenD_right {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (r : Fin (workRows A).card) : (workRows A).card + r.1 < lenD A := by
  have h := r.2
  show (workRows A).card + r.1 < 2 * (workRows A).card
  omega

/-- The `Y`-half of the fourth block. -/
theorem wD_left {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (r : Fin (workRows A).card) :
    wD A (⟨r.1, lt_lenD_left A r⟩ : Fin (lenD A)) = bY n (rowA A r) := by
  simp only [wD]
  rw [dif_pos r.2]

/-- The `X`-half of the fourth block. -/
theorem wD_right {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (r : Fin (workRows A).card) :
    wD A (⟨(workRows A).card + r.1, lt_lenD_right A r⟩ : Fin (lenD A))
      = bX n (rowA A r) := by
  simp only [wD]
  have hpos : ¬ ((⟨(workRows A).card + r.1, lt_lenD_right A r⟩ : Fin (lenD A)).1
        < (workRows A).card) := by
    show ¬ ((workRows A).card + r.1 < (workRows A).card)
    omega
  rw [dif_neg hpos]
  have hfin : (⟨(workRows A).card + r.1 - (workRows A).card, by
      have h := r.2; omega⟩ : Fin (workRows A).card) = r := by
    apply Fin.ext
    show (workRows A).card + r.1 - (workRows A).card = r.1
    omega
  rw [hfin]

/-- The `Y`-block step computing the row of index `r`. -/
theorem chainY_bY (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (r : Fin (workRows A).card) :
    chainY A c (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.natAdd (lenC c)
      (⟨r.1, lt_lenD_left A r⟩ : Fin (lenD A)))))
      = bY n (rowA A r) := by
  rw [chainY_D, wD_left]

/-- The `X`-block step computing the row of index `r`. -/
theorem chainY_bX (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (r : Fin (workRows A).card) :
    chainY A c (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.natAdd (lenC c)
      (⟨(workRows A).card + r.1, lt_lenD_right A r⟩ : Fin (lenD A)))))
      = bX n (rowA A r) := by
  rw [chainY_D, wD_right]

/-! ### Validity of the constructed chain -/

/-- The block-`A` indices fit into the constructed chain. -/
theorem chainY_lt_A {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (j : Fin (lenA n)) : j.1 < chainLen A c := by
  have h : j.1 < n := j.2
  show j.1 < n + (lenB n + (lenC c + lenD A))
  omega

/-- The block-`B` indices fit into the constructed chain. -/
theorem chainY_lt_B {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (k : Fin (lenB n)) : n + k.1 < chainLen A c := by
  have h := k.2
  show n + k.1 < n + (lenB n + (lenC c + lenD A))
  omega

/-- The block-`C` indices fit into the constructed chain. -/
theorem chainY_lt_C {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (t : Fin (lenC c)) : n + (lenB n + t.1) < chainLen A c := by
  have h := t.2
  show n + (lenB n + t.1) < n + (lenB n + (lenC c + lenD A))
  omega

/-- The block-`D` indices fit into the constructed chain. -/
theorem chainY_lt_D {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (d : Fin (lenD A)) : n + (lenB n + (lenC c + d.1)) < chainLen A c := by
  have h := d.2
  show n + (lenB n + (lenC c + d.1)) < n + (lenB n + (lenC c + lenD A))
  omega

/-- The value of the constructed chain at the global index of the block-`A` step `j`. -/
theorem chainY_at_A {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (j : Fin (lenA n)) (h : j.1 < chainLen A c) :
    chainY A c ⟨j.1, h⟩ = lightY n j := by
  rw [show (⟨j.1, h⟩ : Fin (chainLen A c))
      = Fin.castAdd (lenB n + (lenC c + lenD A)) j from Fin.ext rfl, chainY_A]

/-- The value of the constructed chain at the global index of the block-`B` step `k`. -/
theorem chainY_at_B {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (k : Fin (lenB n)) (h : n + k.1 < chainLen A c) :
    chainY A c ⟨n + k.1, h⟩ = lamY n (nzEmb n k) := by
  rw [show (⟨n + k.1, h⟩ : Fin (chainLen A c))
      = Fin.natAdd (lenA n) (Fin.castAdd (lenC c + lenD A) k) from Fin.ext (by simp) ,
    chainY_B]

/-- The value of the constructed chain at the global index of the block-`C` step `t`. -/
theorem chainY_at_C {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (t : Fin (lenC c)) (h : n + (lenB n + t.1) < chainLen A c) :
    chainY A c ⟨n + (lenB n + t.1), h⟩ = simY n (keepY c t) := by
  rw [show (⟨n + (lenB n + t.1), h⟩ : Fin (chainLen A c))
      = Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.castAdd (lenD A) t)) from
        Fin.ext (by simp), chainY_C]

/-- The value of the constructed chain at the global index of the block-`D` step `d`. -/
theorem chainY_at_D {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (d : Fin (lenD A)) (h : n + (lenB n + (lenC c + d.1)) < chainLen A c) :
    chainY A c ⟨n + (lenB n + (lenC c + d.1)), h⟩ = wD A d := by
  rw [show (⟨n + (lenB n + (lenC c + d.1)), h⟩ : Fin (chainLen A c))
      = Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.natAdd (lenC c) d)) from
        Fin.ext (by simp), chainY_D]

/-- Accessing an earlier step of the constructed chain through the pool. -/
theorem chainPool_chainY_inr {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (c : VecAddChain n) {k : Fin (chainLen A c)} {p : ℕ} (hp : p < k.1) :
    chainPool (chainY A c) k.1 (le_of_lt k.2) (Sum.inr ⟨p, hp⟩)
      = chainY A c ⟨p, lt_trans hp k.2⟩ := by
  simp only [chainPool]

/-- Accessing a basis vector through the pool. -/
theorem chainPool_chainY_inl {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (c : VecAddChain n) (k : Fin (chainLen A c)) (i : Fin (2 * n + 1)) :
    chainPool (chainY A c) k.1 (le_of_lt k.2) (Sum.inl i) = basisVec i := rfl

/-- The `n` light steps are sums of two basis vectors. -/
theorem chainY_valid_A {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (j : Fin (lenA n)) :
    ∃ a b : Fin (2 * n + 1) ⊕ Fin (j.1),
      chainY A c (Fin.castAdd (lenB n + (lenC c + lenD A)) j)
        = chainPool (chainY A c) j.1 (le_of_lt (Fin.castAdd (lenB n + (lenC c + lenD A)) j).2) a
        + chainPool (chainY A c) j.1 (le_of_lt (Fin.castAdd (lenB n + (lenC c + lenD A)) j).2) b := by
  refine ⟨Sum.inl (iX n j), Sum.inl (iY n j), ?_⟩
  simp only [chainPool]
  rw [chainY_A A c j]
  rfl

/-- The steps `z + ⟨a, Y⟩` are built up coordinate by coordinate. -/
theorem chainY_valid_B {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (k : Fin (lenB n)) :
    ∃ a b : Fin (2 * n + 1) ⊕ Fin (n + k.1),
      chainY A c (Fin.natAdd (lenA n) (Fin.castAdd (lenC c + lenD A) k))
        = chainPool (chainY A c) (n + k.1)
            (le_of_lt (Fin.natAdd (lenA n) (Fin.castAdd (lenC c + lenD A) k)).2) a
        + chainPool (chainY A c) (n + k.1)
            (le_of_lt (Fin.natAdd (lenA n) (Fin.castAdd (lenC c + lenD A) k)).2) b := by
  have h0 : nzEmb n k ≠ 0 := nzEmb_ne_zero n k
  by_cases hw : weight (Finset.univ : Finset (Fin n)) (nzEmb n k) = 1
  · obtain ⟨i, hi⟩ := eq_basisVec_of_weight_eq_one hw
    refine ⟨Sum.inl (iZ n), Sum.inl (iY n i), ?_⟩
    simp only [chainPool]
    rw [chainY_B A c k, hi, lamY, bY_basisVec, bz_eq_basisVec]
  · have h2 : 2 ≤ weight (Finset.univ : Finset (Fin n)) (nzEmb n k) := by
      have hp := weight_pos_of_ne_zero h0
      omega
    obtain ⟨i, hi⟩ := exists_apply_ne_zero h0
    have hltw : weight (Finset.univ : Finset (Fin n)) (nzEmb n k + basisVec i)
        < weight (Finset.univ : Finset (Fin n)) (nzEmb n k) :=
      weight_add_basisVec_lt hi h2
    have hne : nzEmb n k + basisVec i ≠ 0 := add_basisVec_ne_zero hi h2
    obtain ⟨k', hk'⟩ := exists_nzEmb_eq n (nzSet_of_ne_zero hne)
    have hk'lt : k'.1 < k.1 := nzEmb_lt_of_weight_lt n (by rw [hk']; exact hltw)
    refine ⟨Sum.inr ⟨n + k'.1, by omega⟩, Sum.inl (iY n i), ?_⟩
    simp only [chainPool, Fin.val_natAdd, Fin.val_castAdd]
    rw [chainY_B A c k, chainY_at_B A c k' (chainY_lt_B A c k'), hk']
    have hkey := lamY_add_basisVec n (nzEmb n k + basisVec i) i
    rw [add_basisVec_add_basisVec] at hkey
    calc lamY n (nzEmb n k)
        = (lamY n (nzEmb n k) + basisVec (iY n i)) + basisVec (iY n i) := by
          rw [add_assoc, add_self_vec, add_zero]
      _ = lamY n (nzEmb n k + basisVec i) + basisVec (iY n i) := by rw [hkey]

/-- A value of the compressed chain, simulated in the constructed chain. -/
theorem simY_map_pool {m n : ℕ} {A : Matrix (Fin m) (Fin n) (ZMod 2)} {c : VecAddChain n}
    {t : Fin (lenC c)} {k : Fin (chainLen A c)} (hk : k.1 = n + (lenB n + t.1))
    (s : Fin n ⊕ Fin t.1) :
    ∃ s' : Fin (2 * n + 1) ⊕ Fin k.1,
      simY n (chainPool (keepY c) t.1 (le_of_lt t.2) s)
        = chainPool (chainY A c) k.1 (le_of_lt k.2) s' := by
  rcases s with i | t'
  · refine ⟨Sum.inr ⟨i.1, by omega⟩, ?_⟩
    simp only [chainPool]
    rw [chainY_at_A A c i (chainY_lt_A A c i)]
    exact (lightY_eq n i).symm
  · have ht' : t'.1 < lenC c := lt_trans t'.2 t.2
    refine ⟨Sum.inr ⟨n + (lenB n + t'.1), by omega⟩, ?_⟩
    simp only [chainPool]
    rw [chainY_at_C A c (⟨t'.1, ht'⟩ : Fin (lenC c))
      (chainY_lt_C A c (⟨t'.1, ht'⟩ : Fin (lenC c)))]

/-- The simulation steps are sums of two earlier values. -/
theorem chainY_valid_C {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (t : Fin (lenC c)) :
    ∃ a b : Fin (2 * n + 1) ⊕
        Fin ((Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.castAdd (lenD A) t))).1),
      chainY A c (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.castAdd (lenD A) t)))
        = chainPool (chainY A c)
            (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.castAdd (lenD A) t))).1
            (le_of_lt (Fin.natAdd (lenA n)
              (Fin.natAdd (lenB n) (Fin.castAdd (lenD A) t))).2) a
        + chainPool (chainY A c)
            (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.castAdd (lenD A) t))).1
            (le_of_lt (Fin.natAdd (lenA n)
              (Fin.natAdd (lenB n) (Fin.castAdd (lenD A) t))).2) b := by
  obtain ⟨s1, s2, hs⟩ := (compressedChain c).valid t
  have hs' : keepY c t = chainPool (keepY c) t.1 (le_of_lt t.2) s1 +
      chainPool (keepY c) t.1 (le_of_lt t.2) s2 := hs
  obtain ⟨s1', hs1⟩ :=
    simY_map_pool (A := A) (c := c)
      (k := Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.castAdd (lenD A) t))) (by rfl) s1
  obtain ⟨s2', hs2⟩ :=
    simY_map_pool (A := A) (c := c)
      (k := Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.castAdd (lenD A) t))) (by rfl) s2
  refine ⟨s1', s2', ?_⟩
  rw [chainY_C A c t, hs', simY_add, hs1, hs2]

/-- The steps `⟨aᵢ, Y⟩` and `⟨aᵢ, X⟩` are sums of two earlier values. -/
theorem chainY_valid_D {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (hc : c.Computes A) (d : Fin (lenD A)) :
    ∃ a b : Fin (2 * n + 1) ⊕
        Fin ((Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.natAdd (lenC c) d))).1),
      chainY A c (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.natAdd (lenC c) d)))
        = chainPool (chainY A c)
            (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.natAdd (lenC c) d))).1
            (le_of_lt (Fin.natAdd (lenA n)
              (Fin.natAdd (lenB n) (Fin.natAdd (lenC c) d))).2) a
        + chainPool (chainY A c)
            (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.natAdd (lenC c) d))).1
            (le_of_lt (Fin.natAdd (lenA n)
              (Fin.natAdd (lenB n) (Fin.natAdd (lenC c) d))).2) b := by
  obtain ⟨dv, hdv⟩ := d
  by_cases hd : dv < (workRows A).card
  · have hval : chainY A c (Fin.natAdd (lenA n) (Fin.natAdd (lenB n)
        (Fin.natAdd (lenC c) (⟨dv, hdv⟩ : Fin (lenD A)))))
        = bY n (rowA A (⟨dv, hd⟩ : Fin (workRows A).card)) := by
      rw [chainY_D]
      exact wD_left A ⟨dv, hd⟩
    have ha0 : rowA A (⟨dv, hd⟩ : Fin (workRows A).card) ≠ 0 :=
      (mem_workRows.mp (workEmb_mem A ⟨dv, hd⟩)).1
    obtain ⟨ka, hka⟩ := exists_nzEmb_eq n (nzSet_of_ne_zero ha0)
    refine ⟨Sum.inr ⟨n + ka.1, by
      simp only [Fin.val_natAdd, lenA, lenB, lenC, compressedChain]
      have h := ka.2
      omega⟩, Sum.inl (iZ n), ?_⟩
    simp only [chainPool]
    rw [hval, chainY_at_B A c ka (chainY_lt_B A c ka), hka, bY_eq_lamY_add_bz,
      bz_eq_basisVec]
  · have hle : (workRows A).card ≤ dv := by omega
    have hR : 0 < (workRows A).card := by
      have h := hdv
      simp only [lenD] at h
      omega
    set r : Fin (workRows A).card :=
      ⟨dv - (workRows A).card, by have h := hdv; simp only [lenD] at h; omega⟩ with hr
    have hrval : r.1 = dv - (workRows A).card := by rw [hr]
    clear hr
    have hdveq : (⟨dv, hdv⟩ : Fin (lenD A)) =
        (⟨(workRows A).card + r.1, lt_lenD_right A r⟩ : Fin (lenD A)) := by
      apply Fin.ext
      show dv = (workRows A).card + r.1
      rw [hrval]
      omega
    have hval : chainY A c (Fin.natAdd (lenA n) (Fin.natAdd (lenB n)
        (Fin.natAdd (lenC c) (⟨dv, hdv⟩ : Fin (lenD A)))))
        = bX n (rowA A r) := by
      rw [chainY_D, hdveq, wD_right A r]
    have hrow : keepY c (rowIdx A hc r) = rowA A r := rowIdx_spec A hc r
    refine ⟨Sum.inr ⟨n + (lenB n + (rowIdx A hc r).1), by
        simp only [Fin.val_natAdd, lenA, lenB, lenC, compressedChain]
        have h := (rowIdx A hc r).2
        omega⟩,
      Sum.inr ⟨n + (lenB n + (lenC c + r.1)), by
        simp only [Fin.val_natAdd, lenA, lenB, lenC, compressedChain]
        have h := hrval
        omega⟩, ?_⟩
    simp only [chainPool]
    rw [chainY_at_C A c (rowIdx A hc r) (chainY_lt_C A c (rowIdx A hc r)), hrow,
      chainY_at_D A c (⟨r.1, lt_lenD_left A r⟩ : Fin (lenD A))
        (chainY_lt_D A c ⟨r.1, lt_lenD_left A r⟩), wD_left A r,
      hval, bX_eq_simY_add_bY]

/-! ### The constructed extended chain -/

/-- The constructed chain is valid: every step is the sum of two earlier values. -/
theorem chainY_valid {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (hc : c.Computes A) :
    ∀ k : Fin (chainLen A c), ∃ a b : Fin (2 * n + 1) ⊕ Fin k.1,
      chainY A c k = chainPool (chainY A c) k.1 (le_of_lt k.2) a +
        chainPool (chainY A c) k.1 (le_of_lt k.2) b := by
  intro k
  refine Fin.addCases (motive := fun k => ∃ a b : Fin (2 * n + 1) ⊕ Fin k.1,
      chainY A c k = chainPool (chainY A c) k.1 (le_of_lt k.2) a +
        chainPool (chainY A c) k.1 (le_of_lt k.2) b) ?_ ?_ k
  · exact chainY_valid_A A c
  · refine Fin.addCases ?_ ?_
    · exact chainY_valid_B A c
    · refine Fin.addCases ?_ ?_
      · exact chainY_valid_C A c
      · exact chainY_valid_D A c hc

/-- The extended chain constructed in the proof of Theorem 1. -/
noncomputable def constructedChain {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (c : VecAddChain n) (hc : c.Computes A) : ExtChain (2 * n + 1) where
  L := chainLen A c
  y := chainY A c
  valid := chainY_valid A c hc
  aux := auxSet n

/-- The constructed extended chain computes the matrix `A` on the essential variables `X`. -/
theorem constructedChain_computes {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (c : VecAddChain n) (hc : c.Computes A) :
    (constructedChain A c hc).Computes A (iX n) := by
  refine ⟨iX_injective n, ?_, ?_⟩
  · intro j
    exact iX_not_mem_aux n j
  · intro i
    by_cases h0 : A i = 0
    · refine ⟨0, by simp, ?_, ?_⟩
      · intro j
        rw [h0]
        rfl
      · intro p hp
        rfl
    · by_cases hb : ∃ j : Fin n, A i = basisVec j
      · obtain ⟨j0, hj0⟩ := hb
        refine ⟨basisVec (iX n j0), ?_, ?_, ?_⟩
        · exact Or.inl (Or.inl ⟨iX n j0, rfl⟩)
        · intro j
          rw [hj0]
          simp only [basisVec]
          by_cases h : j = j0
          · subst h
            simp
          · have hne : iX n j ≠ iX n j0 := fun hh => h (iX_injective n hh)
            simp [h, hne]
        · intro p hp
          have hp' : n ≤ p.1 := mem_auxSet.mp hp
          have hlt : (iX n j0).1 < n := by simp [iX]
          have hne : p ≠ iX n j0 := by
            intro hh
            rw [hh] at hp'
            omega
          simp [basisVec, hne]
      · have hb' : ∀ j : Fin n, A i ≠ basisVec j := by
          intro j hj
          exact hb ⟨j, hj⟩
        have hi : i ∈ workRows A := by
          rw [mem_workRows]
          exact ⟨h0, hb'⟩
        have hmem : i ∈ Set.range (workEmb A) := by
          rw [workEmb, Finset.range_orderEmbOfFin]
          exact hi
        obtain ⟨r, hr⟩ := hmem
        refine ⟨bX n (rowA A r), ?_, ?_, ?_⟩
        · exact Or.inl (Or.inr ⟨_, chainY_bX A c r⟩)
        · intro j
          rw [← hr, bX_iX]
          rfl
        · intro p hp
          exact bX_eq_zero n (rowA A r) (mem_auxSet.mp hp)

/-! ### The set of heavy types of the constructed chain -/

/-- The types of the block-`B` steps: `z + ⟨a, Y⟩` for every nonzero `a`. -/
noncomputable def typeB (n : ℕ) : Finset (Vec (2 * n + 1)) :=
  (Finset.univ : Finset (Fin (lenB n))).image
    (fun k => proj (auxSet n) (lamY n (nzEmb n k)))

/-- The types of the block-`C` steps: the simulation of the compressed chain. -/
noncomputable def typeC {n : ℕ} (c : VecAddChain n) : Finset (Vec (2 * n + 1)) :=
  (Finset.univ : Finset (Fin (lenC c))).image
    (fun t => proj (auxSet n) (simY n (keepY c t)))

theorem typeB_card (n : ℕ) : (typeB n).card = 2 ^ n - 1 := by
  show (Finset.univ.image (fun k : Fin (lenB n) => proj (auxSet n) (lamY n (nzEmb n k)))).card
    = 2 ^ n - 1
  rw [Finset.card_image_of_injective _
    (fun k k' h => nzEmb_injective n (lamY_type_injective h)), Finset.card_univ, Fintype.card_fin]

theorem typeC_card {n : ℕ} (c : VecAddChain n) : (typeC c).card = (keepSteps c).card := by
  have hinj : Function.Injective
      (fun t : Fin (lenC c) => proj (auxSet n) (simY n (keepY c t))) := by
    intro t t' h
    exact keepY_injective c (simY_type_injective h)
  show (Finset.univ.image (fun t : Fin (lenC c) => proj (auxSet n) (simY n (keepY c t)))).card
    = (keepSteps c).card
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

theorem typeB_disjoint_typeC (n : ℕ) (c : VecAddChain n) :
    Disjoint (typeB n) (typeC c) := by
  rw [Finset.disjoint_left]
  intro x hx hy
  have hx' : x ∈ (Finset.univ : Finset (Fin (lenB n))).image
      (fun k => proj (auxSet n) (lamY n (nzEmb n k))) := hx
  have hy' : x ∈ (Finset.univ : Finset (Fin (lenC c))).image
      (fun t => proj (auxSet n) (simY n (keepY c t))) := hy
  rw [Finset.mem_image] at hx' hy'
  obtain ⟨k, -, hk⟩ := hx'
  obtain ⟨t, -, ht⟩ := hy'
  exact lamY_type_ne_simY_type n (nzEmb n k) (keepY c t) (hk.trans ht.symm)

/-! ### Types of the individual blocks -/

theorem typeWeight_at_A {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (hc : c.Computes A) (j : Fin (lenA n)) :
    (constructedChain A c hc).typeWeight (Fin.castAdd (lenB n + (lenC c + lenD A)) j) = 1 := by
  show weight (auxSet n) (chainY A c (Fin.castAdd (lenB n + (lenC c + lenD A)) j)) = 1
  rw [chainY_A A c j, weight_aux_lightY]

theorem typeWeight_at_B {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (hc : c.Computes A) (k : Fin (lenB n)) :
    (constructedChain A c hc).typeWeight
        (Fin.natAdd (lenA n) (Fin.castAdd (lenC c + lenD A) k))
      = weight (auxSet n) (lamY n (nzEmb n k)) := by
  show weight (auxSet n)
    (chainY A c (Fin.natAdd (lenA n) (Fin.castAdd (lenC c + lenD A) k))) = _
  rw [chainY_B A c k]

theorem stepType_at_B {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (hc : c.Computes A) (k : Fin (lenB n)) :
    (constructedChain A c hc).stepType
        (Fin.natAdd (lenA n) (Fin.castAdd (lenC c + lenD A) k))
      = proj (auxSet n) (lamY n (nzEmb n k)) := by
  show proj (auxSet n)
    (chainY A c (Fin.natAdd (lenA n) (Fin.castAdd (lenC c + lenD A) k))) = _
  rw [chainY_B A c k]

theorem typeWeight_at_C {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (hc : c.Computes A) (t : Fin (lenC c)) :
    (constructedChain A c hc).typeWeight
        (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.castAdd (lenD A) t)))
      = weight (auxSet n) (simY n (keepY c t)) := by
  show weight (auxSet n)
    (chainY A c (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.castAdd (lenD A) t)))) = _
  rw [chainY_C A c t]

theorem stepType_at_C {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n)
    (hc : c.Computes A) (t : Fin (lenC c)) :
    (constructedChain A c hc).stepType
        (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.castAdd (lenD A) t)))
      = proj (auxSet n) (simY n (keepY c t)) := by
  show proj (auxSet n)
    (chainY A c (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.castAdd (lenD A) t)))) = _
  rw [chainY_C A c t]

theorem stepType_at_D_left {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (c : VecAddChain n) (hc : c.Computes A) (r : Fin (workRows A).card) :
    (constructedChain A c hc).stepType
        (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.natAdd (lenC c)
          (⟨r.1, lt_lenD_left A r⟩ : Fin (lenD A)))))
      = bY n (rowA A r) := by
  show proj (auxSet n) (chainY A c (Fin.natAdd (lenA n) (Fin.natAdd (lenB n)
    (Fin.natAdd (lenC c) (⟨r.1, lt_lenD_left A r⟩ : Fin (lenD A)))))) = _
  rw [chainY_bY A c r, proj_aux_bY]

theorem typeWeight_at_D_left {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (c : VecAddChain n) (hc : c.Computes A) (r : Fin (workRows A).card) :
    (constructedChain A c hc).typeWeight
        (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.natAdd (lenC c)
          (⟨r.1, lt_lenD_left A r⟩ : Fin (lenD A)))))
      = weight (Finset.univ : Finset (Fin n)) (rowA A r) := by
  show weight (auxSet n) (chainY A c (Fin.natAdd (lenA n) (Fin.natAdd (lenB n)
    (Fin.natAdd (lenC c) (⟨r.1, lt_lenD_left A r⟩ : Fin (lenD A)))))) = _
  rw [chainY_bY A c r, weight_aux_bY]

theorem stepType_at_D_right {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (c : VecAddChain n) (hc : c.Computes A) (r : Fin (workRows A).card) :
    (constructedChain A c hc).stepType
        (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.natAdd (lenC c)
          (⟨(workRows A).card + r.1, lt_lenD_right A r⟩ : Fin (lenD A)))))
      = 0 := by
  show proj (auxSet n) (chainY A c (Fin.natAdd (lenA n) (Fin.natAdd (lenB n)
    (Fin.natAdd (lenC c) (⟨(workRows A).card + r.1, lt_lenD_right A r⟩ : Fin (lenD A)))))) = _
  rw [chainY_bX A c r, proj_aux_bX]

theorem typeWeight_at_D_right {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (c : VecAddChain n) (hc : c.Computes A) (r : Fin (workRows A).card) :
    (constructedChain A c hc).typeWeight
        (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.natAdd (lenC c)
          (⟨(workRows A).card + r.1, lt_lenD_right A r⟩ : Fin (lenD A)))))
      = 0 := by
  show weight (auxSet n) (chainY A c (Fin.natAdd (lenA n) (Fin.natAdd (lenB n)
    (Fin.natAdd (lenC c) (⟨(workRows A).card + r.1, lt_lenD_right A r⟩ : Fin (lenD A)))))) = _
  rw [chainY_bX A c r, weight_aux_bX]

/-! ### Every heavy type is a block-`B` or a block-`C` type -/

theorem stepType_mem_of_heavy {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (c : VecAddChain n) (hc : c.Computes A) :
    ∀ k : Fin (chainLen A c), 2 ≤ (constructedChain A c hc).typeWeight k →
      (constructedChain A c hc).stepType k ∈ typeB n ∪ typeC c := by
  intro k
  refine Fin.addCases (motive := fun k => 2 ≤ (constructedChain A c hc).typeWeight k →
    (constructedChain A c hc).stepType k ∈ typeB n ∪ typeC c) ?_ ?_ k
  · intro j hj
    rw [typeWeight_at_A A c hc j] at hj
    omega
  · intro k'
    refine Fin.addCases
      (motive := fun k' => 2 ≤ (constructedChain A c hc).typeWeight (Fin.natAdd (lenA n) k') →
        (constructedChain A c hc).stepType (Fin.natAdd (lenA n) k') ∈ typeB n ∪ typeC c)
      ?_ ?_ k'
    · intro k _
      refine Finset.mem_union_left (typeC c) ?_
      rw [stepType_at_B A c hc k]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
    · intro k''
      refine Fin.addCases
        (motive := fun k'' => 2 ≤ (constructedChain A c hc).typeWeight
            (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) k'')) →
          (constructedChain A c hc).stepType (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) k''))
            ∈ typeB n ∪ typeC c)
        ?_ ?_ k''
      · intro t _
        refine Finset.mem_union_right (typeB n) ?_
        rw [stepType_at_C A c hc t]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ t)
      · intro d hheavy
        obtain ⟨dv, hdv⟩ := d
        by_cases hdd : dv < (workRows A).card
        · set r : Fin (workRows A).card := ⟨dv, hdd⟩ with hr
          have hdeq : (⟨dv, hdv⟩ : Fin (lenD A)) =
              (⟨r.1, lt_lenD_left A r⟩ : Fin (lenD A)) := Fin.ext rfl
          refine Finset.mem_union_right (typeB n) ?_
          rw [show (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.natAdd (lenC c)
                (⟨dv, hdv⟩ : Fin (lenD A)))))
              = (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.natAdd (lenC c)
                (⟨r.1, lt_lenD_left A r⟩ : Fin (lenD A))))) from by rw [hdeq]]
          rw [stepType_at_D_left A c hc r]
          have heq : proj (auxSet n) (simY n (keepY c (rowIdx A hc r))) = bY n (rowA A r) := by
            rw [proj_aux_simY, rowIdx_spec]
            rfl
          rw [← heq]
          exact Finset.mem_image_of_mem _ (Finset.mem_univ (rowIdx A hc r))
        · have hle : (workRows A).card ≤ dv := by omega
          set r : Fin (workRows A).card :=
            ⟨dv - (workRows A).card, by have h := hdv; simp only [lenD] at h; omega⟩ with hr
          have hrval : r.1 = dv - (workRows A).card := rfl
          have hdeq : (⟨dv, hdv⟩ : Fin (lenD A)) =
              (⟨(workRows A).card + r.1, lt_lenD_right A r⟩ : Fin (lenD A)) := by
            apply Fin.ext
            show dv = (workRows A).card + r.1
            rw [hrval]; omega
          rw [show (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.natAdd (lenC c)
                (⟨dv, hdv⟩ : Fin (lenD A)))))
              = (Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.natAdd (lenC c)
                (⟨(workRows A).card + r.1, lt_lenD_right A r⟩ : Fin (lenD A))))) from by rw [hdeq]]
            at hheavy
          rw [typeWeight_at_D_right A c hc r] at hheavy
          omega

/-! ### The heavy types are exactly the block-`B` and block-`C` types -/

theorem constructedChain_typeSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (c : VecAddChain n) (hc : c.Computes A) :
    (constructedChain A c hc).typeSet = typeB n ∪ typeC c := by
  apply le_antisymm
  · intro x hx
    have hx' : x ∈ (constructedChain A c hc).heavySteps.image (constructedChain A c hc).stepType :=
      hx
    rw [Finset.mem_image] at hx'
    obtain ⟨k, hk, rfl⟩ := hx'
    exact stepType_mem_of_heavy A c hc k (ExtChain.mem_heavySteps.mp hk)
  · apply Finset.union_subset
    · intro x hx
      have hx' : x ∈ (Finset.univ : Finset (Fin (lenB n))).image
          (fun k => proj (auxSet n) (lamY n (nzEmb n k))) := hx
      rw [Finset.mem_image] at hx'
      obtain ⟨k, -, rfl⟩ := hx'
      refine Finset.mem_image.mpr
        ⟨(Fin.natAdd (lenA n) (Fin.castAdd (lenC c + lenD A) k) :
          Fin (constructedChain A c hc).L), ?_, ?_⟩
      · refine ExtChain.mem_heavySteps.mpr ?_
        rw [typeWeight_at_B A c hc k]
        exact weight_aux_lamY_ge_two n (nzEmb_ne_zero n k)
      · exact stepType_at_B A c hc k
    · intro x hx
      have hx' : x ∈ (Finset.univ : Finset (Fin (lenC c))).image
          (fun t => proj (auxSet n) (simY n (keepY c t))) := hx
      rw [Finset.mem_image] at hx'
      obtain ⟨t, -, rfl⟩ := hx'
      refine Finset.mem_image.mpr
        ⟨(Fin.natAdd (lenA n) (Fin.natAdd (lenB n) (Fin.castAdd (lenD A) t)) :
          Fin (constructedChain A c hc).L), ?_, ?_⟩
      · refine ExtChain.mem_heavySteps.mpr ?_
        rw [typeWeight_at_C A c hc t]
        exact weight_aux_simY_ge_two n (compressedChain_weight_ge_two c t)
      · exact stepType_at_C A c hc t

theorem constructedChain_typeSet_card {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (c : VecAddChain n) (hc : c.Computes A) :
    (constructedChain A c hc).typeSet.card = (2 ^ n - 1) + (keepSteps c).card := by
  rw [constructedChain_typeSet A c hc,
    Finset.card_union_of_disjoint (typeB_disjoint_typeC n c), typeB_card, typeC_card]

/-! ### The reduced complexity of the constructed chain -/

theorem constructedChain_reducedComplexity {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (c : VecAddChain n) (hc : c.Computes A) :
    (constructedChain A c hc).reducedComplexity = n + 2 * (workRows A).card := by
  show (constructedChain A c hc).L - (constructedChain A c hc).typeSet.card
    = n + 2 * (workRows A).card
  rw [constructedChain_typeSet_card A c hc]
  show chainLen A c - ((2 ^ n - 1) + (keepSteps c).card) = n + 2 * (workRows A).card
  simp only [chainLen, lenA, lenB, lenC, lenD, compressedChain]
  omega

/-! ### Theorem 1 -/

/-- **Theorem 1** of Section 2: every `m × n` matrix over `GF(2)` has reduced complexity at
most `2m + n`. -/
theorem theorem1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    Lstar A ≤ 2 * m + n := by
  obtain ⟨c, hc⟩ := exists_chain_computes A
  refine le_trans (Lstar_le_of_computes (constructedChain A c hc) (iX n)
    (constructedChain_computes A c hc)) ?_
  rw [constructedChain_reducedComplexity A c hc]
  have hcard : (workRows A).card ≤ m := by
    simpa using Finset.card_le_univ (workRows A)
  omega

end AchainsComplexityGF2
