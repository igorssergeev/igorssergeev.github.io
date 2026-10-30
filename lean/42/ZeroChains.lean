import Mathlib

/-!
# 0-chains: additive complexity in the basis of powers of two

This file formalizes Section 2 of (I. S. Sergeev, *On the additive
complexity of some integer sequences*, Math. Notes 115 (3), 2024): chains in the basis of powers of
two (0-chains), Theorem 2 on the complexity `L∗(2^n - 1)`, and the relation between 0-chains and
ordinary addition chains that the paper records just before Theorem 2.

A **0-chain** is an addition chain in which the powers of two `1, 2, 4, …, 2^(n-1)` are free:
each new element is the sum of two available values, a free power of two or an earlier element of
the chain, and the length `L` of the chain is the number of additions.  The complexity `L∗(m)` is
the length of a shortest 0-chain computing the number `m`.

The model is the coefficient model: a number `< 2^n` is represented by its vector of coefficients
in the basis `2^0, …, 2^(n-1)` (`Coef n = Fin n → ℕ`), so that a 0-chain is a sequence of
coefficient vectors.  Coefficients are not required to be digits (`0` or `1`): only the value
`eval v = ∑ i, v i * 2^i` matters, which keeps the model closed under addition.

Main results:

* `theorem2_lower` : `2 * √n - 2 ≤ L∗(2^n - 1)` (the transposition argument of the paper);
* `theorem2_upper` : `L∗(2^n - 1) ≤ 2 * √n + O(n^(1/4))` (the Brauer-type construction);
* `theorem2` : `L∗(2^n - 1) = 2 * √n + O(n^(1/4))`, in the explicit form
  `∃ C, ∀ n, |L∗(2^n - 1) - 2 * √n| ≤ C * n^(1/4)`, and its asymptotic form
  `theorem2_isBigO`;
* `setL_insert_powSet_eq` : the relation between the 0-chain complexity `L∗` and the ordinary
  additive complexity of number sets, `L(2, 2^2, …, 2^(n-1), m) = L∗(m) + n - 1` for `m < 2^n`
  (with the special case `setL_insert_powSet_two_pow_sub_one` for `m = 2^n - 1`).

In the upper-bound proof of the paper the cost of the addition chain for `2^k - 1` is
`k + L(k) - 1`; the correct reading is `k + L₀(k) - 1` (linear chains), i.e. `k - 1 + natL0 k`,
and that is what is used below (`lemma7`).

## Contents

* coefficient vectors `Coef n`, their values `eval`, and free powers of two (`eval_basisCoef`);
* the structure `StarChain n` of 0-chains with its operations `base`, `append`, `addFree`,
  `addFreeAll`, `dbl`, and the complexity functional `starComplexity m = L∗(m)`;
* bounds on the binary weight `nu`;
* **lower bound** (`theorem2_lower`): a shortest 0-chain computing `2^n - 1` is read as a vector
  chain computing a `(n × k)` matrix `a` of coefficients with `k` nonzero columns; the
  transposition principle `Circuit.chainComplexity_transpose`, `L(A) + m = L(Aᵀ) + n`, together
  with `L(x) ≥ ν(x) - 1` gives `2√n - 2 ≤ L∗(2^n - 1)`;
* **upper bound** (`theorem2_upper`): with `(m-1)^2 < n ≤ m^2` and `m^2 - t^2 < n ≤ m^2 - (t-1)^2`,
  the identity `2^n - 1 = (2^k - 1)(1 + 2^k + … + 2^(lk)) + (2^(m^2-t^2) + … + 2^(n-1))`
  (`k = m - t`, `l = m + t - 1`) is realised by a 0-chain of length `≤ 2m + 2t + L₀(k)`;
  the estimates `m ≤ √n + 1`, `t ≤ 2·n^(1/4) + 1` and `L₀(k) ≤ 8·n^(1/4)` then give
  `L∗(2^n - 1) ≤ 2√n + 20·n^(1/4)` for `n ≥ 26`;
* **Theorem 2** (`theorem2`, `theorem2_isBigO`): the two bounds combine into
  `|L∗(2^n - 1) - 2√n| ≤ 30·n^(1/4)` for every `n`, i.e. `L∗(2^n - 1) = 2√n + O(n^(1/4))`;
* **the relation to ordinary addition chains** (`setL_insert_powSet_eq`): ordinary addition chains
  `NatAddChain` for finite sets of numbers, with the minimal length `setL` and the set of free
  powers of two `powSet n`, so that `L(2, 2^2, …, 2^(n-1), m) = setL (insert m (powSet n))`; the
  two halves of the identity `L(2, 2^2, …, 2^(n-1), m) = L∗(m) + n - 1` are
  `exists_starChain_of_computes` (an ordinary chain is compacted into a 0-chain by deleting its
  `n - 1` free powers of two) and `setL_le_of_starChain` (a 0-chain is expanded by prepending
  them), and these are glued into `setL_le_starComplexity_add` and `starComplexity_add_le_setL`.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace AchainsComplexity

/-! ## Preliminaries: the general facts used below

The 0-chain argument of the paper uses three pieces of general theory, collected here so that the
file depends on `Mathlib` alone.  They are exactly the definitions and facts the proofs below
mention, with everything else omitted:

* vector addition chains `VecAddChain`, the basis vectors `basisVec` and the complexity `L(A)`
  (`chainComplexity`), together with additive circuits: Lemma 1 
  (`chainComplexity = ordinaryComplexity = minEquivComplexity`);
* path counts in a circuit and the transposition principle, Lemma 2: `L(A) + m = L(Aᵀ) + n`
  for a nonnegative matrix without zero rows or columns (`Circuit.chainComplexity_transpose`);
* ordinary addition chains of natural numbers: `NatChain`, `natL` (`= L`), linear chains and
  `natL0` (`= L₀`), the binary weight `nu` (`= ν`), Lemma 4 (`L₀(n) < 2 log₂ n`) and Lemma 7
  (`L(2^n - 1) ≤ n - 1 + L₀(n)`).

The relation between 0-chains and ordinary addition chains, at the end of this file, needs none of
this: it only uses the 0-chain definitions above (`Coef`, `StarChain`, `starComplexity`) and its own
ordinary chains of number sets (`NatAddChain`, `setL`, `powSet`).
-/

/-! ### Vectors, vector addition chains and circuits -/


open scoped BigOperators

/-! ## Integer vectors -/

/-- Integer vectors of dimension `n`, i.e. the elements of `ℤⁿ`. -/
abbrev Vec (n : ℕ) := Fin n → ℤ

/-- The `i`-th standard basis vector `eᵢ = (0,…,0,1,0,…,0)`, with a `1` in position `i`
and zeros elsewhere. -/
def basisVec {n : ℕ} (i : Fin n) : Vec n := fun j => if j = i then 1 else 0


/-! ## Vector addition chains -/

/-- The vectors available to an addition chain at step `k`: the basis vectors
`e₁,…,eₙ` together with the earlier vectors `y₁,…,y_{k-1}`. -/
def chainPool {n L : ℕ} (y : Fin L → Vec n) (k : ℕ) (hk : k ≤ L) : Fin n ⊕ Fin k → Vec n
  | Sum.inl i => basisVec i
  | Sum.inr j => y ⟨j.1, lt_of_lt_of_le j.2 hk⟩

/-- A vector addition chain in `ℤⁿ`, i.e. a sequence `e₁,…,eₙ, y₁,…,y_L` in which every
`y_k` is the sum of two vectors available strictly earlier (a basis vector or some `y_j`
with `j < k`). -/
structure VecAddChain (n : ℕ) where
  /-- the length `L ≥ 0` of the chain -/
  L : ℕ
  /-- the vectors `y₁,…,y_L` computed by the chain -/
  y : Fin L → Vec n
  /-- every `y_k` is the sum of two available vectors -/
  valid : ∀ k : Fin L, ∃ a b : Fin n ⊕ Fin k.1,
    y k = chainPool y k.1 (le_of_lt k.2) a + chainPool y k.1 (le_of_lt k.2) b

/-- A vector addition chain `c` computes a matrix `A` of size `m × n` if every row of `A`
occurs among the basis vectors `eᵢ`, the computed vectors `y_k`, or is the zero vector. -/
def VecAddChain.Computes {m n : ℕ} (c : VecAddChain n) (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∀ i : Fin m, A i ∈ Set.range basisVec ∪ Set.range c.y ∪ {0}

/-- The additive complexity `L(A)` defined through addition chains: the length of the
shortest chain computing `A` (and `0` if no chain computes `A`). -/
noncomputable def chainComplexity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : ℕ :=
  sInf { l | ∃ c : VecAddChain n, c.L = l ∧ c.Computes A }

/-! ## Additive circuits -/

/-- An unbounded fan-in additive circuit over `ℤⁿ`. Vertices are `Fin N`; the first `n`
vertices are inputs representing `e₁,…,eₙ`; every non-input vertex carries a list of
incoming edges (parallel edges are allowed, their order is irrelevant). Acyclicity is
enforced by orienting every edge from a lower-indexed to a higher-indexed vertex.

A circuit is required to be *reduced*: every non-input vertex has at least one incoming
edge. -/
structure Circuit (n : ℕ) where
  /-- total number of vertices of the circuit -/
  N : ℕ
  /-- there are at least the `n` input vertices -/
  hN : n ≤ N
  /-- incoming edges of every non-input vertex -/
  preds : Fin (N - n) → List (Fin N)
  /-- acyclicity: every edge points forward in the vertex ordering -/
  acyclic : ∀ (t : Fin (N - n)) (u : Fin N), u ∈ preds t → u.1 < n + t.1
  /-- no junk vertices: every non-input vertex has an incoming edge -/
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
    (v : Fin C.N) → ((u : Fin C.N) → u.1 < v.1 → ℤ) → ℤ :=
  fun v ih =>
    if h : v.1 < n then (if j = (⟨v.1, h⟩ : Fin n) then (1 : ℤ) else 0)
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
noncomputable def comp (C : Circuit n) (j : Fin n) : Fin C.N → ℤ :=
  WellFounded.fix (C.vrel_wf) (C.foldStep j)

/-- The vector represented by a vertex of the circuit. -/
noncomputable def repr (C : Circuit n) (v : Fin C.N) : Vec n := fun j => C.comp j v

theorem comp_eq (C : Circuit n) (j : Fin n) (v : Fin C.N) :
    C.comp j v =
      (if h : v.1 < n then (if j = (⟨v.1, h⟩ : Fin n) then (1 : ℤ) else 0)
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

/-- Complexity of a circuit: its number of non-input vertices.  This is the size measure used for
the ordinary (fan-in `≤ 2`) model; unbounded fan-in circuits are measured by `equivComplexity`. -/
def complexity (C : Circuit n) : ℕ := C.N - n

/-- Total number of edges of the circuit (parallel edges counted with multiplicity). -/
def edgeCount (C : Circuit n) : ℕ := ∑ t : Fin (C.N - n), (C.preds t).length

/-- Equivalent complexity of an unbounded fan-in circuit: the number of edges minus the
number of non-input vertices. -/
def equivComplexity (C : Circuit n) : ℕ := C.edgeCount - C.complexity

/-- A circuit is *ordinary* if every vertex has fan-in at most `2`. -/
def IsOrdinary (C : Circuit n) : Prop := ∀ t : Fin (C.N - n), (C.preds t).length ≤ 2


/-- For every circuit the equivalent complexity is a genuine (non-truncated) difference, and
it is the sum over non-input vertices of (fan-in − 1). -/
theorem equivComplexity_eq_sum (C : Circuit n) :
    C.equivComplexity = ∑ t : Fin (C.N - n), ((C.preds t).length - 1) := by
  have hne : ∀ t : Fin (C.N - n), ((C.preds t).length - 1) + 1 = (C.preds t).length :=
    fun t => Nat.sub_add_cancel (C.reduced t)
  have h : C.edgeCount
      = (∑ t : Fin (C.N - n), ((C.preds t).length - 1)) + C.complexity := by
    unfold Circuit.edgeCount Circuit.complexity
    rw [show (∑ t : Fin (C.N - n), (C.preds t).length)
          = ∑ t : Fin (C.N - n), (((C.preds t).length - 1) + 1) from
        Finset.sum_congr rfl (fun t _ => (hne t).symm),
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        smul_eq_mul, mul_one]
  unfold Circuit.equivComplexity
  rw [h, Nat.add_sub_cancel]

/-- Reducedness gives at least one edge per non-input vertex, so the complexity never exceeds
the number of edges. -/
theorem complexity_le_edgeCount (C : Circuit n) : C.complexity ≤ C.edgeCount := by
  have hcard : C.complexity = ∑ _t : Fin (C.N - n), (1 : ℕ) := by
    unfold Circuit.complexity
    simp
  rw [hcard, Circuit.edgeCount]
  exact Finset.sum_le_sum (fun t _ => C.reduced t)

/-- An additive circuit computes (represents) a matrix `A` if every row of `A` is represented
by some vertex of the circuit; the all-zero vector is assumed always represented (as in the
paper). -/
def Computes {m : ℕ} (C : Circuit n) (A : Matrix (Fin m) (Fin n) ℤ) : Prop :=
  ∀ i : Fin m, A i ∈ Set.range C.repr ∪ {0}

end Circuit

/-- The additive complexity of a matrix restricted to ordinary (fan-in `≤ 2`) circuits. -/
noncomputable def ordinaryComplexity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : ℕ :=
  sInf { k | ∃ C : Circuit n, C.IsOrdinary ∧ C.complexity = k ∧ C.Computes A }

/-- The minimal equivalent complexity of an unbounded fan-in circuit computing `A`.  (Every
circuit is reduced, so no junk vertices are present.) -/
noncomputable def minEquivComplexity {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : ℕ :=
  sInf { k | ∃ C : Circuit n, C.equivComplexity = k ∧ C.Computes A }


/-! ### Lemma 1: the additive models are equivalent -/



open scoped BigOperators

/-- Sum of the `f`-images of the two elements of a two-element list. -/
theorem sum_get_pair {α M : Type*} [AddCommMonoid M] (f : α → M) (a b : α) :
    (∑ i : Fin ([a, b] : List α).length, f ([a, b].get i)) = f a + f b := by
  change (∑ i : Fin 2, f ([a, b].get i)) = f a + f b
  rw [Fin.sum_univ_two]
  simp

namespace Circuit

/-- The vector represented by a node with exactly two predecessors is the sum of the vectors
represented by those two predecessors. -/
theorem repr_idx_pair {n : ℕ} (C : Circuit n) (t : Fin (C.N - n)) (a b : Fin C.N)
    (h : C.preds t = [a, b]) : C.repr (C.idx t) = C.repr a + C.repr b := by
  rw [repr_idx, h, sum_get_pair]

end Circuit

namespace VecAddChain

/-- Fuse a chain pool index (a basis vector `eᵢ` or one of the first `k` computed vectors)
into a vertex index of the associated circuit. -/
def fuse {n L : ℕ} (k : ℕ) (hk : k ≤ L) : Fin n ⊕ Fin k → Fin (n + L)
  | Sum.inl i => ⟨i.1, by omega⟩
  | Sum.inr j => ⟨n + j.1, by omega⟩

@[simp] theorem fuse_inl {n L k : ℕ} (hk : k ≤ L) (i : Fin n) :
    (fuse (n := n) (L := L) k hk (Sum.inl i)).1 = i.1 := rfl

@[simp] theorem fuse_inr {n L k : ℕ} (hk : k ≤ L) (j : Fin k) :
    (fuse (n := n) (L := L) k hk (Sum.inr j)).1 = n + j.1 := rfl

theorem fuse_lt {n L k : ℕ} (hk : k ≤ L) (s : Fin n ⊕ Fin k) :
    (fuse (n := n) (L := L) k hk s).1 < n + k := by
  cases s with
  | inl i => rw [fuse_inl]; omega
  | inr j => rw [fuse_inr]; omega

theorem mem_pair {α : Type*} (x y u : α) : u ∈ ([x, y] : List α) → u = x ∨ u = y := by
  intro h
  simpa using h

/-- `t` as a chain step index, from a circuit non-input vertex index. -/
def nodeCast {n : ℕ} (c : VecAddChain n) (t : Fin ((n + c.L) - n)) : Fin c.L :=
  ⟨t.1, by have := t.2; omega⟩

/-- The two summands used at step `t` of the chain. -/
noncomputable def summands {n : ℕ} (c : VecAddChain n) (t : Fin c.L) :
    (Fin n ⊕ Fin t.1) × (Fin n ⊕ Fin t.1) :=
  ((c.valid t).choose, (c.valid t).choose_spec.choose)

theorem summands_spec {n : ℕ} (c : VecAddChain n) (t : Fin c.L) :
    c.y t = chainPool c.y t.1 (le_of_lt t.2) (c.summands t).1
          + chainPool c.y t.1 (le_of_lt t.2) (c.summands t).2 :=
  (c.valid t).choose_spec.choose_spec

/-- Incoming edges of the `t`-th vertex of the circuit of a chain. -/
noncomputable def predsOf {n : ℕ} (c : VecAddChain n) (t : Fin ((n + c.L) - n)) :
    List (Fin (n + c.L)) :=
  [fuse (n := n) (nodeCast c t).1 (le_of_lt (nodeCast c t).2) (c.summands (nodeCast c t)).1,
   fuse (n := n) (nodeCast c t).1 (le_of_lt (nodeCast c t).2) (c.summands (nodeCast c t)).2]

/-- The circuit associated with a vector addition chain. -/
noncomputable def toCircuit {n : ℕ} (c : VecAddChain n) : Circuit n where
  N := n + c.L
  hN := Nat.le_add_right n c.L
  preds := predsOf c
  acyclic := by
    intro t u hu
    unfold predsOf at hu
    obtain h | h := mem_pair _ _ _ hu
    · rw [h]; exact fuse_lt _ _
    · rw [h]; exact fuse_lt _ _
  reduced := by
    intro t
    simp [predsOf]

@[simp] theorem toCircuit_N {n : ℕ} (c : VecAddChain n) : c.toCircuit.N = n + c.L := rfl

theorem toCircuit_complexity {n : ℕ} (c : VecAddChain n) : c.toCircuit.N - n = c.L :=
  Nat.add_sub_cancel_left n c.L

theorem toCircuit_lt {n : ℕ} (c : VecAddChain n) {a : ℕ} (h : a < c.L) :
    a < c.toCircuit.N - n := lt_of_lt_of_eq h (toCircuit_complexity c).symm

theorem toCircuit_preds_apply {n : ℕ} (c : VecAddChain n) (t : Fin (c.toCircuit.N - n)) :
    c.toCircuit.preds t =
      [fuse (n := n) (nodeCast c t).1 (le_of_lt (nodeCast c t).2) (c.summands (nodeCast c t)).1,
       fuse (n := n) (nodeCast c t).1 (le_of_lt (nodeCast c t).2) (c.summands (nodeCast c t)).2] :=
  rfl

theorem toCircuit_repr_idx_aux {n : ℕ} (c : VecAddChain n) :
    ∀ (k : ℕ) (t : Fin (c.toCircuit.N - n)), t.1 = k →
      c.toCircuit.repr (c.toCircuit.idx t) = c.y (nodeCast c t) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro t ht
    have key : ∀ s : Fin n ⊕ Fin (nodeCast c t).1,
        c.toCircuit.repr (fuse (n := n) (nodeCast c t).1 (le_of_lt (nodeCast c t).2) s)
          = chainPool c.y (nodeCast c t).1 (le_of_lt (nodeCast c t).2) s := by
      intro s
      cases s with
      | inl i => exact c.toCircuit.repr_input i
      | inr j =>
          have hj : j.1 < k := by
            have hnc : (c.nodeCast t).1 = k := ht
            omega
          let t' : Fin (c.toCircuit.N - n) :=
            ⟨j.1, by have h2 : j.1 < t.1 := j.2; have := t.2; omega⟩
          have hrec := ih j.1 hj t' rfl
          rw [show fuse (n := n) (nodeCast c t).1 (le_of_lt (nodeCast c t).2) (Sum.inr j)
                = c.toCircuit.idx t' from Fin.ext rfl, hrec]
          simp only [chainPool]
          exact congrArg c.y (Fin.ext rfl)
    rw [Circuit.repr_idx_pair c.toCircuit t _ _ (show c.toCircuit.preds t = _ from rfl),
        c.summands_spec (nodeCast c t), key _, key _]

theorem toCircuit_repr_idx {n : ℕ} (c : VecAddChain n) (t : Fin (c.toCircuit.N - n)) :
    c.toCircuit.repr (c.toCircuit.idx t) = c.y (nodeCast c t) :=
  toCircuit_repr_idx_aux c t.1 t rfl

theorem toCircuit_computes {m n : ℕ} (c : VecAddChain n) (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : c.Computes A) : c.toCircuit.Computes A := by
  intro i
  rcases hA i with (⟨j, hj⟩ | ⟨k, hk⟩) | h0
  · left
    refine ⟨⟨j.1, lt_of_lt_of_le j.2 c.toCircuit.hN⟩, ?_⟩
    rw [Circuit.repr_input]; exact hj
  · left
    refine ⟨c.toCircuit.idx ⟨k.1, toCircuit_lt c k.2⟩, ?_⟩
    rw [toCircuit_repr_idx, ← hk]
    congr 1
  · right; exact h0

end VecAddChain



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

theorem equivComplexity_eq_stepsTotal (C : Circuit n) :
    C.equivComplexity = C.stepsTotal := by
  rw [C.equivComplexity_eq_sum]; rfl

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

end Circuit


namespace Circuit

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

theorem toChain_L (C : Circuit n) : C.toChain.L = C.stepsTotal := rfl

theorem toChain_y (C : Circuit n) (k : Fin C.stepsTotal) : C.toChain.y k = C.chainY k := rfl

theorem toChain_computes {m : ℕ} (C : Circuit n) (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : C.Computes A) : C.toChain.Computes A := by
  intro i
  rcases hA i with ⟨v, hv⟩ | h0
  · rcases C.repr_mem_chainY v with ⟨b, hb⟩ | ⟨kk, hkk⟩
    · exact Or.inl (Or.inl ⟨b, hb.trans hv⟩)
    · exact Or.inl (Or.inr ⟨kk, by rw [toChain_y]; exact hkk.trans hv⟩)
  · exact Or.inr h0

theorem chainComplexity_le_equivComplexity {m : ℕ} (C : Circuit n)
    (A : Matrix (Fin m) (Fin n) ℤ) (hA : C.Computes A) :
    chainComplexity A ≤ C.equivComplexity := by
  have h1 : C.toChain.Computes A := C.toChain_computes A hA
  have hL : C.toChain.L = C.equivComplexity := by rw [toChain_L, ← equivComplexity_eq_stepsTotal]
  exact Nat.sInf_le ⟨C.toChain, hL, h1⟩

end Circuit


namespace VecAddChain

/-- The circuit associated with a vector addition chain is ordinary and has equivalent
complexity equal to the chain length (every non-input vertex has exactly two incoming edges). -/
theorem toCircuit_equivComplexity {n : ℕ} (c : VecAddChain n) :
    c.toCircuit.equivComplexity = c.L := by
  rw [Circuit.equivComplexity_eq_sum]
  have hlen : ∀ t : Fin (c.toCircuit.N - n), (c.toCircuit.preds t).length = 2 := by
    intro t; rw [toCircuit_preds_apply]; simp
  have hsub : ∀ t : Fin (c.toCircuit.N - n), ((c.toCircuit.preds t).length - 1) = 1 := by
    intro t; rw [hlen t]
  rw [Finset.sum_congr rfl (fun t _ => hsub t), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one]
  exact toCircuit_complexity c

/-- The circuit associated with a chain is ordinary (fan-in at most two). -/
theorem toCircuit_isOrdinary {n : ℕ} (c : VecAddChain n) : c.toCircuit.IsOrdinary := by
  intro t; rw [toCircuit_preds_apply]; simp

end VecAddChain

namespace Circuit

/-- In an ordinary (fan-in `≤ 2`) circuit the equivalent complexity is at most the complexity,
since every non-input vertex contributes `fan-in − 1 ≤ 1`. -/
theorem equivComplexity_le_complexity_of_ordinary {n : ℕ} (C : Circuit n)
    (h : C.IsOrdinary) : C.equivComplexity ≤ C.complexity := by
  rw [C.equivComplexity_eq_sum]
  show (∑ t : Fin (C.N - n), ((C.preds t).length - 1)) ≤ C.N - n
  calc ∑ t : Fin (C.N - n), ((C.preds t).length - 1)
      ≤ ∑ _t : Fin (C.N - n), (1 : ℕ) := by
        apply Finset.sum_le_sum
        intro t _
        have := h t
        omega
    _ = C.N - n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

end Circuit

/-- A lower bound of the `sInf` of a set of naturals, valid even when the set is empty
(in which case the `sInf` is `0` and we additionally require `a = 0`). -/
theorem le_sInf_of_forall {s : Set ℕ} {a : ℕ} (h0 : s = ∅ → a = 0)
    (h : ∀ b ∈ s, a ≤ b) : a ≤ sInf s := by
  by_cases hs : s = ∅
  · have hz : a = 0 := h0 hs
    rw [hs, hz]; simp
  · exact h _ (Nat.sInf_mem (Set.nonempty_iff_ne_empty.mpr hs))

/-! ## The sets of possible complexities, and their mutual inclusions -/

/-- Lengths of vector addition chains computing `A`. -/
def ChainSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Set ℕ :=
  { l | ∃ c : VecAddChain n, c.L = l ∧ c.Computes A }

/-- Equivalent complexities of unbounded fan-in circuits computing `A`. -/
def EquivSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Set ℕ :=
  { k | ∃ C : Circuit n, C.equivComplexity = k ∧ C.Computes A }

/-- Complexities of ordinary circuits computing `A`. -/
def OrdSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) : Set ℕ :=
  { k | ∃ C : Circuit n, C.IsOrdinary ∧ C.complexity = k ∧ C.Computes A }

@[simp] theorem chainComplexity_eq_sInf {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    chainComplexity A = sInf (ChainSet A) := rfl

@[simp] theorem ordinaryComplexity_eq_sInf {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    ordinaryComplexity A = sInf (OrdSet A) := rfl

@[simp] theorem minEquivComplexity_eq_sInf {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    minEquivComplexity A = sInf (EquivSet A) := rfl

/-- A chain computing `A`, read as its circuit, witnesses that the chain lengths are equivalent
complexities of circuits computing `A`. -/
theorem chainSet_subset_equivSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    ChainSet A ⊆ EquivSet A := by
  rintro l ⟨c, hL, hc⟩
  refine ⟨c.toCircuit, ?_, c.toCircuit_computes A hc⟩
  rw [c.toCircuit_equivComplexity]; exact hL

/-- Conversely, every circuit computing `A` yields a chain of the same equivalent complexity. -/
theorem equivSet_subset_chainSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    EquivSet A ⊆ ChainSet A := by
  rintro k ⟨C, hEq, hC⟩
  refine ⟨C.toChain, ?_, C.toChain_computes A hC⟩
  rw [C.toChain_L, ← Circuit.equivComplexity_eq_stepsTotal]; exact hEq

/-- A chain computing `A`, read as its circuit, is ordinary. -/
theorem chainSet_subset_ordSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    ChainSet A ⊆ OrdSet A := by
  rintro l ⟨c, hL, hc⟩
  refine ⟨c.toCircuit, c.toCircuit_isOrdinary, ?_, c.toCircuit_computes A hc⟩
  show c.toCircuit.N - n = l
  rw [c.toCircuit_complexity]; exact hL

/-- **Lemma 1**.  For every matrix `A`, the additive complexity `L(A)` defined through
vector addition chains, the additive complexity in the ordinary (fan-in `≤ 2`) circuit model,
and the minimal equivalent complexity of an unbounded fan-in circuit computing `A` all coincide:

  `chainComplexity A = ordinaryComplexity A = minEquivComplexity A`.

The ordinary model measures size by the number of non-input vertices; the unbounded fan-in model
measures it by the equivalent complexity, `#edges − #non-input vertices`. -/
theorem lemma1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) :
    chainComplexity A = ordinaryComplexity A ∧
    ordinaryComplexity A = minEquivComplexity A := by
  have h_co : chainComplexity A = ordinaryComplexity A := by
    apply le_antisymm
    · rw [ordinaryComplexity_eq_sInf]
      refine le_sInf_of_forall ?_ ?_
      · intro hO
        have hCh : ChainSet A = ∅ := Set.not_nonempty_iff_eq_empty.mp (fun hne => by
          obtain ⟨l, hl⟩ := hne
          exact Set.not_nonempty_iff_eq_empty.mpr hO ⟨l, chainSet_subset_ordSet A hl⟩)
        rw [chainComplexity_eq_sInf, hCh]; simp
      · intro k hk
        obtain ⟨C, hOrd, hComplexity, hC⟩ := hk
        calc chainComplexity A ≤ C.equivComplexity := Circuit.chainComplexity_le_equivComplexity C A hC
          _ ≤ C.complexity := C.equivComplexity_le_complexity_of_ordinary hOrd
          _ = k := hComplexity
    · rw [chainComplexity_eq_sInf]
      refine le_sInf_of_forall ?_ ?_
      · intro hCh
        have hO : OrdSet A = ∅ := Set.not_nonempty_iff_eq_empty.mp (fun hne => by
          obtain ⟨k, hk⟩ := hne
          obtain ⟨C, _hOrd, _hComplexity, hC⟩ := hk
          have hm : C.stepsTotal ∈ ChainSet A := ⟨C.toChain, C.toChain_L, C.toChain_computes A hC⟩
          rw [hCh] at hm; simp at hm)
        rw [ordinaryComplexity_eq_sInf, hO]; simp
      · intro l hl
        obtain ⟨c, hL, hc⟩ := hl
        calc ordinaryComplexity A ≤ c.toCircuit.complexity :=
              Nat.sInf_le ⟨c.toCircuit, c.toCircuit_isOrdinary, rfl, c.toCircuit_computes A hc⟩
          _ = c.L := by show c.toCircuit.N - n = c.L; exact c.toCircuit_complexity
          _ = l := hL
  have h_cm : chainComplexity A = minEquivComplexity A := by
    have hset : ChainSet A = EquivSet A :=
      Set.Subset.antisymm (chainSet_subset_equivSet A) (equivSet_subset_chainSet A)
    rw [chainComplexity_eq_sInf, minEquivComplexity_eq_sInf, hset]
  exact ⟨h_co, by rw [← h_co]; exact h_cm⟩


/-! ### Path counts in a circuit -/

open scoped BigOperators

namespace Circuit

variable {n : ℕ}

/-- The path-count step: number of oriented paths from `a` to `b`, by recursion on the target
`b` (a path is either empty or ends with an edge into `b`). -/
noncomputable def pcStep (C : Circuit n) (a : Fin C.N) :
    (b : Fin C.N) → ((u : Fin C.N) → u.1 < b.1 → ℤ) → ℤ :=
  fun b ih =>
    (if a = b then (1 : ℤ) else 0) +
      if h : b.1 < n then 0
      else
        ∑ i : Fin (C.preds ⟨b.1 - n, by omega⟩).length,
          ih ((C.preds ⟨b.1 - n, by omega⟩).get i)
            (by
              have hac := C.acyclic ⟨b.1 - n, by omega⟩ _
                (List.get_mem (C.preds ⟨b.1 - n, by omega⟩) i)
              have hc : (⟨b.1 - n, by omega⟩ : Fin (C.N - n)).1 = b.1 - n := rfl
              have hv : n ≤ b.1 := by omega
              omega)

/-- The number of oriented paths from `a` to `b` in the circuit. -/
noncomputable def pc (C : Circuit n) (a : Fin C.N) : Fin C.N → ℤ :=
  WellFounded.fix (measure (fun b : Fin C.N => b.1)).wf (C.pcStep a)

theorem pc_eq (C : Circuit n) (a b : Fin C.N) :
    C.pc a b =
      (if a = b then (1 : ℤ) else 0) +
        if h : b.1 < n then 0
        else ∑ i : Fin (C.preds ⟨b.1 - n, by omega⟩).length,
              C.pc a ((C.preds ⟨b.1 - n, by omega⟩).get i) := by
  unfold pc
  rw [WellFounded.fix_eq]
  rfl

/-- The sum over the outgoing edges of `a`, of `F` applied to the head of each edge. -/
noncomputable def Fwd (C : Circuit n) (a : Fin C.N) (F : Fin C.N → ℤ) : ℤ :=
  ∑ t : Fin (C.N - n), ∑ i : Fin (C.preds t).length,
    if (C.preds t).get i = a then F (C.idx t) else 0

/-- The input vertex corresponding to the `j`-th basis vector. -/
def inputVertex (C : Circuit n) (j : Fin n) : Fin C.N := ⟨j.1, lt_of_lt_of_le j.2 C.hN⟩


/-- The `j`-th component represented by a vertex equals the number of oriented paths from the
`j`-th input to it. -/
theorem comp_eq_pc (C : Circuit n) (j : Fin n) (b : Fin C.N) :
    C.comp j b = C.pc (C.inputVertex j) b := by
  refine WellFounded.induction (C.vrel_wf)
    (C := fun x => C.comp j x = C.pc (C.inputVertex j) x) b (fun b ih => ?_)
  rw [C.comp_eq j b, C.pc_eq (C.inputVertex j) b]
  by_cases hb : b.1 < n
  · rw [dif_pos hb, dif_pos hb]
    have hsafe : (if (j = (⟨b.1, hb⟩ : Fin n)) then (1 : ℤ) else 0)
        = (if (C.inputVertex j = b) then (1 : ℤ) else 0) := by
      by_cases hj : j = (⟨b.1, hb⟩ : Fin n)
      · have hiv : C.inputVertex j = b := by
          apply Fin.ext
          simp only [inputVertex, Fin.val_mk]
          rw [hj]
        rw [if_pos hj, if_pos hiv]
      · have hiv : ¬ (C.inputVertex j = b) := by
          intro h
          apply hj
          apply Fin.ext
          have := congrArg Fin.val h
          simpa only [inputVertex, Fin.val_mk] using this
        rw [if_neg hj, if_neg hiv]
    rw [hsafe, add_zero]
  · rw [dif_neg hb, dif_neg hb]
    have hz : (if (C.inputVertex j = b) then (1 : ℤ) else 0) = 0 := by
      rw [if_neg]
      intro h
      have := congrArg Fin.val h
      simp only [inputVertex, Fin.val_mk] at this
      omega
    rw [hz, zero_add]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact ih _ (by
      have hac := C.acyclic ⟨b.1 - n, by omega⟩ _
        (List.get_mem (C.preds ⟨b.1 - n, by omega⟩) i)
      have hv : n ≤ b.1 := by omega
      simp only [Fin.val_mk] at hac
      omega)


theorem idx_val (C : Circuit n) (t : Fin (C.N - n)) : (C.idx t).1 = n + t.1 := rfl

theorem idx_inj (C : Circuit n) : Function.Injective C.idx := by
  intro t t' h
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [idx, Fin.val_mk] at this
  omega

theorem idx_ne_input (C : Circuit n) {b : Fin C.N} (hb : b.1 < n) (t : Fin (C.N - n)) :
    C.idx t ≠ b := by
  intro h
  have := congrArg Fin.val h
  simp only [idx, Fin.val_mk] at this
  omega

abbrev tIdx (C : Circuit n) (b : Fin C.N) (hb : ¬ b.1 < n) : Fin (C.N - n) :=
  ⟨b.1 - n, by omega⟩

theorem idx_tIdx (C : Circuit n) {b : Fin C.N} (hb : ¬ b.1 < n) :
    C.idx (C.tIdx b hb) = b := by
  apply Fin.ext
  simp only [idx, tIdx, Fin.val_mk]
  omega

theorem pc_eq_noninput (C : Circuit n) (a b : Fin C.N) (hb : ¬ b.1 < n) :
    C.pc a b = (if a = b then (1 : ℤ) else 0) +
      ∑ i : Fin (C.preds (C.tIdx b hb)).length,
        C.pc a ((C.preds (C.tIdx b hb)).get i) := by
  rw [C.pc_eq a b, dif_neg hb]

/-- Every predecessor of a non-input vertex `b` has a smaller index than `b`. -/
theorem pred_get_lt (C : Circuit n) {b : Fin C.N} (hb : ¬ b.1 < n)
    (i : Fin (C.preds (C.tIdx b hb)).length) :
    ((C.preds (C.tIdx b hb)).get i).1 < b.1 := by
  have hac := C.acyclic (C.tIdx b hb) _ (List.get_mem _ i)
  have h1 : (C.tIdx b hb).1 = b.1 - n := rfl
  have h2 : n ≤ b.1 := by omega
  omega


theorem pc_fwd (C : Circuit n) (a b : Fin C.N) :
    C.pc a b = (if a = b then (1 : ℤ) else 0) + C.Fwd a (fun x => C.pc x b) := by
  revert b
  refine WellFounded.induction (measure (fun a : Fin C.N => C.N - a.1)).wf
    (C := fun a => ∀ b : Fin C.N,
      C.pc a b = (if a = b then (1 : ℤ) else 0) + C.Fwd a (fun x => C.pc x b)) a ?_
  intro a IHa b
  refine WellFounded.induction (measure (fun b : Fin C.N => b.1)).wf
    (C := fun b => C.pc a b = (if a = b then (1 : ℤ) else 0) + C.Fwd a (fun x => C.pc x b)) b ?_
  intro b IHb
  rw [C.pc_eq a b]
  by_cases hb : b.1 < n
  · rw [dif_pos hb]
    have hzero : C.Fwd a (fun x => C.pc x b) = 0 := by
      simp only [Fwd]
      refine Finset.sum_eq_zero (fun t _ => ?_)
      refine Finset.sum_eq_zero (fun i _ => ?_)
      have h0 : C.pc (C.idx t) b = 0 := by
        rw [C.pc_eq (C.idx t) b, dif_pos hb, if_neg (C.idx_ne_input hb t), add_zero]
      simp [h0]
    rw [hzero, add_zero]
  · rw [dif_neg hb]
    have hmain : (∑ i : Fin (C.preds (C.tIdx b hb)).length,
          C.pc a ((C.preds (C.tIdx b hb)).get i))
        = C.Fwd a (fun x => C.pc x b) := by
      have h1 : (∑ i : Fin (C.preds (C.tIdx b hb)).length,
            C.pc a ((C.preds (C.tIdx b hb)).get i))
          = ∑ i : Fin (C.preds (C.tIdx b hb)).length,
              ((if a = (C.preds (C.tIdx b hb)).get i then (1 : ℤ) else 0)
                + C.Fwd a (fun x => C.pc x ((C.preds (C.tIdx b hb)).get i))) := by
        apply Finset.sum_congr rfl
        intro i _
        exact IHb _ (C.pred_get_lt hb i)
      rw [h1, Finset.sum_add_distrib]
      have h2 : (∑ i : Fin (C.preds (C.tIdx b hb)).length,
            C.Fwd a (fun x => C.pc x ((C.preds (C.tIdx b hb)).get i)))
          = C.Fwd a (fun x => C.pc x b)
            - (∑ i : Fin (C.preds (C.tIdx b hb)).length,
                (if a = (C.preds (C.tIdx b hb)).get i then (1 : ℤ) else 0)) := by
        have hL : (∑ i : Fin (C.preds (C.tIdx b hb)).length,
              C.Fwd a (fun x => C.pc x ((C.preds (C.tIdx b hb)).get i)))
            = ∑ i : Fin (C.preds (C.tIdx b hb)).length,
                ∑ t : Fin (C.N - n), ∑ j : Fin (C.preds t).length,
                  if (C.preds t).get j = a
                  then C.pc (C.idx t) ((C.preds (C.tIdx b hb)).get i) else 0 := by
          apply Finset.sum_congr rfl; intro i _; simp only [Fwd]
        rw [hL]
        have hsig : (∑ i : Fin (C.preds (C.tIdx b hb)).length,
              ∑ t : Fin (C.N - n), ∑ j : Fin (C.preds t).length,
                if (C.preds t).get j = a
                then C.pc (C.idx t) ((C.preds (C.tIdx b hb)).get i) else 0)
            = ∑ i : Fin (C.preds (C.tIdx b hb)).length,
                ∑ p : (Σ t : Fin (C.N - n), Fin (C.preds t).length),
                  if (C.preds p.1).get p.2 = a
                  then C.pc (C.idx p.1) ((C.preds (C.tIdx b hb)).get i) else 0 := by
          apply Finset.sum_congr rfl; intro i _
          rw [Finset.sum_sigma', Finset.univ_sigma_univ]
        rw [hsig, Finset.sum_comm]
        have hfac : (∑ p : (Σ t : Fin (C.N - n), Fin (C.preds t).length),
              ∑ i : Fin (C.preds (C.tIdx b hb)).length,
                if (C.preds p.1).get p.2 = a
                then C.pc (C.idx p.1) ((C.preds (C.tIdx b hb)).get i) else 0)
            = ∑ p : (Σ t : Fin (C.N - n), Fin (C.preds t).length),
                if (C.preds p.1).get p.2 = a
                then (∑ i : Fin (C.preds (C.tIdx b hb)).length,
                  C.pc (C.idx p.1) ((C.preds (C.tIdx b hb)).get i)) else 0 := by
          apply Finset.sum_congr rfl; intro p _
          by_cases hp : (C.preds p.1).get p.2 = a
          · simp [hp]
          · simp [hp]
        rw [hfac]
        have hstep : ∀ t : Fin (C.N - n),
            (∑ i : Fin (C.preds (C.tIdx b hb)).length,
              C.pc (C.idx t) ((C.preds (C.tIdx b hb)).get i))
              = C.pc (C.idx t) b - (if C.idx t = b then (1 : ℤ) else 0) := by
          intro t
          have h := C.pc_eq_noninput (C.idx t) b hb
          omega
        simp only [hstep]
        have hsplit : (∑ p : (Σ t : Fin (C.N - n), Fin (C.preds t).length),
              (if (C.preds p.1).get p.2 = a
                then (C.pc (C.idx p.1) b - (if C.idx p.1 = b then (1 : ℤ) else 0)) else 0))
            = (∑ p : (Σ t : Fin (C.N - n), Fin (C.preds t).length),
                (if (C.preds p.1).get p.2 = a then C.pc (C.idx p.1) b else 0))
              - (∑ p : (Σ t : Fin (C.N - n), Fin (C.preds t).length),
                (if (C.preds p.1).get p.2 = a
                  then (if C.idx p.1 = b then (1 : ℤ) else 0) else 0)) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl; intro p _
          by_cases hp : (C.preds p.1).get p.2 = a
          · simp only [if_pos hp]
          · simp only [if_neg hp, sub_zero]
        rw [hsplit]
        have hA : (∑ p : (Σ t : Fin (C.N - n), Fin (C.preds t).length),
              (if (C.preds p.1).get p.2 = a then C.pc (C.idx p.1) b else 0))
            = C.Fwd a (fun x => C.pc x b) := by
          simp only [Fwd, Finset.sum_sigma', Finset.univ_sigma_univ]
        rw [hA]
        congr 1
        have hB : (∑ p : (Σ t : Fin (C.N - n), Fin (C.preds t).length),
              (if (C.preds p.1).get p.2 = a
                then (if C.idx p.1 = b then (1 : ℤ) else 0) else 0))
            = ∑ i : Fin (C.preds (C.tIdx b hb)).length,
                (if a = (C.preds (C.tIdx b hb)).get i then (1 : ℤ) else 0) := by
          rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
          refine (Finset.sum_eq_single (C.tIdx b hb) ?_ ?_).trans ?_
          · intro t _ ht
            apply Finset.sum_eq_zero; intro j _
            by_cases hp : (C.preds t).get j = a
            · rw [if_pos hp, if_neg]
              intro h
              exact ht (C.idx_inj (by rw [h, C.idx_tIdx hb]))
            · rw [if_neg hp]
          · intro h; exact absurd (Finset.mem_univ _) h
          · apply Finset.sum_congr rfl; intro j _
            rw [if_pos (C.idx_tIdx hb)]
            by_cases hp : (C.preds (C.tIdx b hb)).get j = a
            · rw [if_pos hp, if_pos hp.symm]
            · rw [if_neg hp, if_neg (fun h => hp h.symm)]
        rw [hB]
      rw [h2, add_sub_cancel]
    rw [hmain]

end Circuit

/-! ### Lemma 2: the transposition principle -/


open scoped BigOperators

/-! ## A list lemma used by the path counts -/

section ListLemmas

variable {α β M : Type*} [AddCommMonoid M]

theorem sum_get_eq_map_sum (l : List α) (f : α → M) :
    (∑ i : Fin l.length, f (l.get i)) = (l.map f).sum := by
  have h := List.map_ofFn (f := (fun i : Fin l.length => l.get i)) (g := f)
  simp only [List.ofFn_get, Function.comp_def] at h
  rw [← List.sum_ofFn, ← h]

end ListLemmas

namespace Circuit

variable {n : ℕ}

/-! ## Edges, reachability and the cone of the row witnesses -/

/-- The edge relation of a circuit: `v` is an incoming neighbour of `w`. -/
def Edge (C : Circuit n) (v w : Fin C.N) : Prop :=
  ∃ t : Fin (C.N - n), ∃ i : Fin (C.preds t).length, (C.preds t).get i = v ∧ C.idx t = w

/-- Reachability in the graph of a circuit. -/
def Reach (C : Circuit n) (v w : Fin C.N) : Prop := Relation.ReflTransGen C.Edge v w

theorem reach_refl (C : Circuit n) (v : Fin C.N) : C.Reach v v := Relation.ReflTransGen.refl

theorem reach_step (C : Circuit n) {v w : Fin C.N} (h : C.Edge v w) : C.Reach v w :=
  Relation.ReflTransGen.single h


theorem edge_lt (C : Circuit n) {v w : Fin C.N} (h : C.Edge v w) : v.1 < w.1 := by
  obtain ⟨t, i, rfl, rfl⟩ := h
  have hac := C.acyclic t _ (List.get_mem _ i)
  simpa [Circuit.idx_val] using hac


theorem reach_of_pc_ne_zero (C : Circuit n) (a b : Fin C.N) (h : C.pc a b ≠ 0) :
    C.Reach a b := by
  revert h
  refine WellFounded.induction (measure (fun b : Fin C.N => b.1)).wf
    (C := fun b => C.pc a b ≠ 0 → C.Reach a b) b ?_
  intro b ih hb
  rw [C.pc_eq a b] at hb
  by_cases hbn : b.1 < n
  · rw [dif_pos hbn, add_zero] at hb
    by_cases hab : a = b
    · rw [hab]; exact C.reach_refl b
    · rw [if_neg hab] at hb; exact absurd rfl hb
  · rw [dif_neg hbn] at hb
    by_cases hab : a = b
    · rw [hab]; exact C.reach_refl b
    · rw [if_neg hab, zero_add] at hb
      have hex : ∃ i : Fin (C.preds (C.tIdx b hbn)).length,
          C.pc a ((C.preds (C.tIdx b hbn)).get i) ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hb (Finset.sum_eq_zero (fun i _ => hc i))
      obtain ⟨i, hi⟩ := hex
      exact (ih _ (C.pred_get_lt hbn i) hi).trans
        (C.reach_step ⟨C.tIdx b hbn, i, rfl, C.idx_tIdx hbn⟩)

theorem pc_eq_zero_of_not_reach (C : Circuit n) (a b : Fin C.N)
    (h : ¬ C.Reach a b) : C.pc a b = 0 := by
  revert h
  refine WellFounded.induction (measure (fun b : Fin C.N => b.1)).wf
    (C := fun b => ¬ C.Reach a b → C.pc a b = 0) b ?_
  intro b ih hb
  rw [C.pc_eq a b]
  have hne : a ≠ b := fun hab => hb (hab ▸ C.reach_refl b)
  rw [if_neg hne]
  by_cases hbn : b.1 < n
  · rw [dif_pos hbn, add_zero]
  · rw [dif_neg hbn, zero_add]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    refine ih _ (C.pred_get_lt hbn i) ?_
    intro hr
    exact hb (hr.trans (C.reach_step ⟨C.tIdx b hbn, i, rfl, C.idx_tIdx hbn⟩))

/-- The set of vertices that can reach one of the row-witness vertices `ρ i`. -/
noncomputable def cone (C : Circuit n) {m : ℕ} (ρ : Fin m → Fin C.N) : Finset (Fin C.N) := by
  classical
  exact Finset.univ.filter (fun v => ∃ i, C.Reach v (ρ i))

theorem mem_cone {C : Circuit n} {m : ℕ} {ρ : Fin m → Fin C.N} {v : Fin C.N} :
    v ∈ C.cone ρ ↔ ∃ i, C.Reach v (ρ i) := by
  classical
  simp [cone]

theorem cone_rho (C : Circuit n) {m : ℕ} (ρ : Fin m → Fin C.N) (i : Fin m) :
    ρ i ∈ C.cone ρ := by
  rw [mem_cone]; exact ⟨i, C.reach_refl _⟩

theorem edge_tail_mem_cone {C : Circuit n} {m : ℕ} {ρ : Fin m → Fin C.N} {v w : Fin C.N}
    (he : C.Edge v w) (hw : w ∈ C.cone ρ) : v ∈ C.cone ρ := by
  rw [mem_cone] at hw ⊢
  obtain ⟨i, hi⟩ := hw
  exact ⟨i, (C.reach_step he).trans hi⟩

theorem cone_pred {C : Circuit n} {m : ℕ} {ρ : Fin m → Fin C.N} {t : Fin (C.N - n)}
    {u : Fin C.N} (hu : u ∈ C.preds t) (ht : C.idx t ∈ C.cone ρ) : u ∈ C.cone ρ := by
  obtain ⟨i, hi⟩ := List.get_of_mem hu
  exact C.edge_tail_mem_cone ⟨t, i, hi, rfl⟩ ht

theorem exists_succ_of_cone {C : Circuit n} {m : ℕ} {ρ : Fin m → Fin C.N} {v : Fin C.N}
    (hv : v ∈ C.cone ρ) (hrow : ∀ i, ρ i ≠ v) :
    ∃ w, C.Edge v w ∧ w ∈ C.cone ρ := by
  rw [mem_cone] at hv
  obtain ⟨i, hi⟩ := hv
  rcases Relation.ReflTransGen.cases_head hi with heq | ⟨w, hstep, hrest⟩
  · exact absurd heq.symm (hrow i)
  · exact ⟨w, hstep, by rw [mem_cone]; exact ⟨i, hrest⟩⟩

end Circuit

/-! ## The reversal construction -/

namespace Circuit

variable {n : ℕ} {C : Circuit n} {m : ℕ} {ρ : Fin m → Fin C.N}

/-- The increasing enumeration of the cone of row witnesses. -/
noncomputable def Kiso (C : Circuit n) (ρ : Fin m → Fin C.N) :
    Fin (C.cone ρ).card ≃o ↥(C.cone ρ) :=
  (C.cone ρ).orderIsoOfFin rfl

/-- The cone vertex sitting at (increasing) position `i`. -/
noncomputable def Kinc (C : Circuit n) (ρ : Fin m → Fin C.N) (i : Fin (C.cone ρ).card) :
    Fin C.N := (Kiso C ρ i).1

theorem Kinc_mem (C : Circuit n) (ρ : Fin m → Fin C.N) (i : Fin (C.cone ρ).card) :
    Kinc C ρ i ∈ C.cone ρ := (Kiso C ρ i).2

/-- The increasing position of a cone vertex. -/
noncomputable def KposInc (C : Circuit n) (ρ : Fin m → Fin C.N) (v : ↥(C.cone ρ)) :
    Fin (C.cone ρ).card :=
  (Kiso C ρ).symm v



/-- The cone vertex sitting at (decreasing) position `i`; this is the vertex numbering of the
transposed circuit. -/
noncomputable def Kdec (C : Circuit n) (ρ : Fin m → Fin C.N) (i : Fin (C.cone ρ).card) :
    Fin C.N :=
  Kinc C ρ (Fin.rev i)

theorem Kdec_mem (C : Circuit n) (ρ : Fin m → Fin C.N) (i : Fin (C.cone ρ).card) :
    Kdec C ρ i ∈ C.cone ρ := Kinc_mem C ρ (Fin.rev i)

/-- The decreasing position of a cone vertex. -/
noncomputable def Kpos (C : Circuit n) (ρ : Fin m → Fin C.N) (v : ↥(C.cone ρ)) :
    Fin (C.cone ρ).card :=
  Fin.rev (KposInc C ρ v)

theorem Kdec_Kpos (C : Circuit n) (ρ : Fin m → Fin C.N) (v : ↥(C.cone ρ)) :
    Kdec C ρ (Kpos C ρ v) = v.1 := by
  simp [Kdec, Kpos, Kinc, KposInc, Fin.rev_rev]

theorem Kpos_Kdec (C : Circuit n) (ρ : Fin m → Fin C.N) (t : Fin (C.cone ρ).card)
    (h : Kdec C ρ t ∈ C.cone ρ) :
    Kpos C ρ ⟨Kdec C ρ t, h⟩ = t := by
  simp [Kdec, Kpos, Kinc, KposInc, Fin.rev_rev]

/-- Edges point forward in the decreasing enumeration. -/
theorem Kpos_lt_of_edge (C : Circuit n) (ρ : Fin m → Fin C.N) {v w : Fin C.N}
    (hv : v ∈ C.cone ρ) (hw : w ∈ C.cone ρ) (he : C.Edge v w) :
    (Kpos C ρ ⟨w, hw⟩).1 < (Kpos C ρ ⟨v, hv⟩).1 := by
  have hlt : (⟨v, hv⟩ : ↥(C.cone ρ)) < ⟨w, hw⟩ := C.edge_lt he
  have h2 : (Kiso C ρ).symm ⟨v, hv⟩ < (Kiso C ρ).symm ⟨w, hw⟩ :=
    ((Kiso C ρ).symm.lt_iff_lt).mpr hlt
  have h2' : ((Kiso C ρ).symm ⟨v, hv⟩).1 < ((Kiso C ρ).symm ⟨w, hw⟩).1 := h2
  have hb : ((Kiso C ρ).symm ⟨w, hw⟩).1 < (C.cone ρ).card := ((Kiso C ρ).symm ⟨w, hw⟩).2
  have hb2 : ((Kiso C ρ).symm ⟨v, hv⟩).1 < (C.cone ρ).card := ((Kiso C ρ).symm ⟨v, hv⟩).2
  simp only [Kpos, KposInc, Fin.val_rev]
  omega

/-! ## The transposed circuit: vertices and edges -/

/-- The non-input vertices of `C` whose vertex lies in the cone, with the membership proof
attached. -/
noncomputable def KN (C : Circuit n) (ρ : Fin m → Fin C.N) :
    List { t' : Fin (C.N - n) // C.idx t' ∈ C.cone ρ } :=
  (List.finRange (C.N - n)).filterMap (fun t' =>
    if h : C.idx t' ∈ C.cone ρ then some ⟨t', h⟩ else none)

/-- The `i`-th input vertex of the transposed circuit. -/
def z (C : Circuit n) (ρ : Fin m → Fin C.N) (i : Fin m) : Fin (m + (C.cone ρ).card) :=
  ⟨i.1, by have := i.2; omega⟩

/-- The non-input vertex of the transposed circuit that corresponds to a cone vertex. -/
noncomputable def Dv (C : Circuit n) (ρ : Fin m → Fin C.N) (v : ↥(C.cone ρ)) :
    Fin (m + (C.cone ρ).card) :=
  ⟨m + (Kpos C ρ v).1, by have := (Kpos C ρ v).2; omega⟩

/-- A non-input index of the transposed circuit, read as a position in the decreasing
enumeration of the cone. -/
def Dpos (C : Circuit n) (ρ : Fin m → Fin C.N) (t : Fin (m + (C.cone ρ).card - m)) :
    Fin (C.cone ρ).card :=
  ⟨t.1, by have := t.2; omega⟩

@[simp] theorem z_val (C : Circuit n) (ρ : Fin m → Fin C.N) (i : Fin m) :
    (z C ρ i).1 = i.1 := rfl

@[simp] theorem Dv_val (C : Circuit n) (ρ : Fin m → Fin C.N) (v : ↥(C.cone ρ)) :
    (Dv C ρ v).1 = m + (Kpos C ρ v).1 := rfl

@[simp] theorem Dpos_val (C : Circuit n) (ρ : Fin m → Fin C.N)
    (t : Fin (m + (C.cone ρ).card - m)) : (Dpos C ρ t).1 = t.1 := rfl



theorem z_ne_Dv (C : Circuit n) (ρ : Fin m → Fin C.N) (i : Fin m) (v : ↥(C.cone ρ)) :
    z C ρ i ≠ Dv C ρ v := by
  intro h
  have h1 : i.1 = m + (Kpos C ρ v).1 := congrArg Fin.val h
  have := i.2
  omega


/-- Reversed edges entering a vertex of the transposed circuit. -/
noncomputable def DrevPreds (C : Circuit n) (ρ : Fin m → Fin C.N)
    (t : Fin (C.cone ρ).card) : List (Fin (m + (C.cone ρ).card)) :=
  (KN C ρ).flatMap (fun t' =>
    (C.preds t'.1).filterMap (fun x =>
      if x = Kdec C ρ t then some (Dv C ρ ⟨C.idx t'.1, t'.2⟩) else none))

/-- The fresh input edges of the transposed circuit. -/
noncomputable def DfreshPreds (C : Circuit n) (ρ : Fin m → Fin C.N)
    (t : Fin (C.cone ρ).card) : List (Fin (m + (C.cone ρ).card)) :=
  (List.finRange m).filterMap (fun i =>
    if ρ i = Kdec C ρ t then some (z C ρ i) else none)

/-- The incoming edges of the `t`-th non-input vertex of the transposed circuit: reversed
edges of `C` inside the cone, plus one fresh edge from the `i`-th input to the witness
`ρ i`. -/
noncomputable def Dpreds (C : Circuit n) (ρ : Fin m → Fin C.N)
    (t : Fin (C.cone ρ).card) : List (Fin (m + (C.cone ρ).card)) :=
  DrevPreds C ρ t ++ DfreshPreds C ρ t

theorem mem_DrevPreds {t : Fin (C.cone ρ).card} {y : Fin (m + (C.cone ρ).card)} :
    y ∈ DrevPreds C ρ t ↔
      ∃ (t' : Fin (C.N - n)) (h : C.idx t' ∈ C.cone ρ) (p : Fin (C.preds t').length),
        (C.preds t').get p = Kdec C ρ t ∧ y = Dv C ρ ⟨C.idx t', h⟩ := by
  constructor
  · intro hy
    simp only [DrevPreds, List.mem_flatMap, List.mem_filterMap] at hy
    obtain ⟨t', _, x, hx, hfx⟩ := hy
    by_cases hx' : x = Kdec C ρ t
    · rw [if_pos hx'] at hfx
      obtain rfl := Option.some.inj hfx
      obtain ⟨p, hp⟩ := List.get_of_mem (l := C.preds t'.1) hx
      exact ⟨t'.1, t'.2, p, hp.trans hx', rfl⟩
    · rw [if_neg hx'] at hfx
      exact absurd hfx (by simp)
  · rintro ⟨t', h, p, hp, rfl⟩
    simp only [DrevPreds, List.mem_flatMap, List.mem_filterMap]
    refine ⟨⟨t', h⟩, ?_, (C.preds t').get p, List.get_mem _ p, ?_⟩
    · simp only [KN, List.mem_filterMap]
      exact ⟨t', by simp, by rw [dif_pos h]⟩
    · rw [if_pos hp]

theorem mem_DfreshPreds {t : Fin (C.cone ρ).card} {y : Fin (m + (C.cone ρ).card)} :
    y ∈ DfreshPreds C ρ t ↔ ∃ i : Fin m, ρ i = Kdec C ρ t ∧ y = z C ρ i := by
  simp only [DfreshPreds, List.mem_filterMap]
  constructor
  · rintro ⟨i, _, hi⟩
    by_cases hρ : ρ i = Kdec C ρ t
    · rw [if_pos hρ] at hi
      exact ⟨i, hρ, (Option.some.inj hi).symm⟩
    · rw [if_neg hρ] at hi
      exact absurd hi (by simp)
  · rintro ⟨i, hρ, rfl⟩
    exact ⟨i, by simp, by rw [if_pos hρ]⟩

/-- The transposed circuit: `m` fresh inputs (one per row of the computed matrix) together with
the cone of the row witnesses, with all edges reversed. -/
@[reducible] noncomputable def D (C : Circuit n) (ρ : Fin m → Fin C.N) : Circuit m where
  N := m + (C.cone ρ).card
  hN := Nat.le_add_right _ _
  preds := fun t => Dpreds C ρ (Dpos C ρ t)
  acyclic := by
    intro t u hu
    simp only [Dpreds, List.mem_append] at hu
    rcases hu with hu | hu
    · rw [mem_DrevPreds] at hu
      obtain ⟨t', h, p, hp, rfl⟩ := hu
      have he : C.Edge (Kdec C ρ (Dpos C ρ t)) (C.idx t') := ⟨t', p, hp, rfl⟩
      have hlt := Kpos_lt_of_edge C ρ (Kdec_mem C ρ (Dpos C ρ t)) h he
      have h2 : (Kpos C ρ ⟨Kdec C ρ (Dpos C ρ t),
          Kdec_mem C ρ (Dpos C ρ t)⟩).1 = t.1 := by
        rw [Kpos_Kdec C ρ (Dpos C ρ t) (Kdec_mem C ρ (Dpos C ρ t)), Dpos_val]
      simp only [Dv_val]
      omega
    · rw [mem_DfreshPreds] at hu
      obtain ⟨i, _, rfl⟩ := hu
      simp only [z_val]
      have := i.2
      omega
  reduced := by
    intro t
    have hu : Kdec C ρ (Dpos C ρ t) ∈ C.cone ρ := Kdec_mem C ρ (Dpos C ρ t)
    by_cases hwit : ∃ i : Fin m, ρ i = Kdec C ρ (Dpos C ρ t)
    · obtain ⟨i, hi⟩ := hwit
      have hmem : z C ρ i ∈ DfreshPreds C ρ (Dpos C ρ t) :=
        mem_DfreshPreds.mpr ⟨i, hi, rfl⟩
      have hpos : 0 < (DfreshPreds C ρ (Dpos C ρ t)).length :=
        List.length_pos_iff.mpr (by intro h; rw [h] at hmem; simp at hmem)
      simp only [Dpreds, List.length_append]
      omega
    · push Not at hwit
      obtain ⟨w, he, hw⟩ := exists_succ_of_cone hu hwit
      obtain ⟨t', p, hp1, hp2⟩ := he
      have hidx : C.idx t' ∈ C.cone ρ := hp2 ▸ hw
      have hmem : Dv C ρ ⟨C.idx t', hidx⟩ ∈ DrevPreds C ρ (Dpos C ρ t) :=
        mem_DrevPreds.mpr ⟨t', hidx, p, hp1, rfl⟩
      have hpos : 0 < (DrevPreds C ρ (Dpos C ρ t)).length :=
        List.length_pos_iff.mpr (by intro h; rw [h] at hmem; simp at hmem)
      simp only [Dpreds, List.length_append]
      omega

/-- Paths between input vertices in any circuit. -/
theorem pc_input (C : Circuit n) (i i' : Fin n) :
    C.pc (C.inputVertex i) (C.inputVertex i') = if i = i' then (1 : ℤ) else 0 := by
  have hlt : (C.inputVertex i').1 < n := i'.2
  rw [C.pc_eq (C.inputVertex i) (C.inputVertex i'), dif_pos hlt, add_zero]
  by_cases h : i = i'
  · subst h
    rw [if_pos rfl, if_pos rfl]
  · have hne : C.inputVertex i ≠ C.inputVertex i' := by
      intro hh
      apply h
      have hv := congrArg Fin.val hh
      simp only [inputVertex, Fin.val_mk] at hv
      exact Fin.ext hv
    rw [if_neg hne, if_neg h]

theorem D_pc_z (C : Circuit n) (ρ : Fin m → Fin C.N) (i i' : Fin m) :
    (D C ρ).pc (z C ρ i) (z C ρ i') = if i = i' then (1 : ℤ) else 0 := by
  have h1 : z C ρ i = (D C ρ).inputVertex i := Fin.ext rfl
  have h2 : z C ρ i' = (D C ρ).inputVertex i' := Fin.ext rfl
  rw [h1, h2, pc_input]

end Circuit

/-! ## Path counts in the transposed circuit

The number of paths from the `i`-th fresh input of `D` to the vertex `Dv v` is the number of
paths from `v` to the row witness `ρ i` in `C` (`Circuit.pc_D_z_Dv`). -/
open scoped BigOperators


section GenericSums

variable {α β : Type*} {M : Type*} [AddCommMonoid M]

theorem sum_map_flatMap (l : List α) (g : α → List β) (F : β → M) :
    ((l.flatMap g).map F).sum = (l.map (fun a => ((g a).map F).sum)).sum := by
  rw [List.map_flatMap]
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, ih]

theorem sum_map_filterMap (l : List α) (g : α → Option β) (F : β → M) :
    ((l.filterMap g).map F).sum
      = (l.map (fun x => match g x with | some b => F b | none => 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases h : g a with
    | none =>
      simp only [List.filterMap_cons, h, List.map_cons, List.sum_cons, zero_add]
      exact ih
    | some b =>
      simp only [List.filterMap_cons, h, List.map_cons, List.sum_cons]
      rw [ih]

/-- Sum of `F c` over the entries of `l` equal to `v`, where `c` is attached to `v`. -/
theorem sum_map_filterMap_single [DecidableEq α] (l : List α) (v : α) (c : β) (F : β → M) :
    ((l.filterMap (fun x => if x = v then some c else none)).map F).sum
      = (∑ p : Fin l.length, if l.get p = v then F c else 0) := by
  rw [sum_map_filterMap, ← sum_get_eq_map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : l.get i = v
  · rw [if_pos hi, if_pos hi]
  · rw [if_neg hi, if_neg hi]

theorem sum_finRange_map {k : ℕ} (G : Fin k → M) :
    ((List.finRange k).map G).sum = ∑ i : Fin k, G i := by
  rw [show List.finRange k = List.ofFn (fun i : Fin k => i) from rfl, List.map_ofFn]
  simp [List.sum_ofFn]

end GenericSums

namespace Circuit

variable {n : ℕ}

theorem sum_KN_map {M : Type*} [AddCommMonoid M] (C : Circuit n) {m : ℕ}
    (ρ : Fin m → Fin C.N) (H : { t' : Fin (C.N - n) // C.idx t' ∈ C.cone ρ } → M) :
    ((KN C ρ).map H).sum
      = ∑ t' : Fin (C.N - n), if h : C.idx t' ∈ C.cone ρ then H ⟨t', h⟩ else 0 := by
  rw [KN, sum_map_filterMap, sum_finRange_map]
  refine Finset.sum_congr rfl (fun t' _ => ?_)
  by_cases h : C.idx t' ∈ C.cone ρ <;> simp [h]

theorem sum_DrevPreds {M : Type*} [AddCommMonoid M] {C : Circuit n} {m : ℕ}
    {ρ : Fin m → Fin C.N} (t : Fin (C.cone ρ).card)
    (F : Fin (m + (C.cone ρ).card) → M) :
    ((DrevPreds C ρ t).map F).sum
      = ∑ t' : Fin (C.N - n),
          if h : C.idx t' ∈ C.cone ρ then
            ∑ p : Fin (C.preds t').length,
              (if (C.preds t').get p = Kdec C ρ t
               then F (Dv C ρ ⟨C.idx t', h⟩) else 0)
          else 0 := by
  rw [DrevPreds, sum_map_flatMap, sum_KN_map]
  apply Finset.sum_congr rfl
  intro t' _
  by_cases h : C.idx t' ∈ C.cone ρ
  · rw [dif_pos h, dif_pos h]
    exact sum_map_filterMap_single (C.preds t') (Kdec C ρ t)
      (Dv C ρ ⟨C.idx t', h⟩) F
  · rw [dif_neg h, dif_neg h]

theorem sum_DfreshPreds {M : Type*} [AddCommMonoid M] {C : Circuit n} {m : ℕ}
    {ρ : Fin m → Fin C.N} (t : Fin (C.cone ρ).card)
    (F : Fin (m + (C.cone ρ).card) → M) :
    ((DfreshPreds C ρ t).map F).sum
      = ∑ j : Fin m, if ρ j = Kdec C ρ t then F (z C ρ j) else 0 := by
  rw [DfreshPreds, sum_map_filterMap, sum_finRange_map]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : ρ j = Kdec C ρ t <;> simp [h]


/-! ## Expanded recurrence for paths in the transposed circuit -/

theorem Dpos_val' (C : Circuit n) (ρ : Fin m → Fin C.N) (t : Fin ((D C ρ).N - m)) :
    (Dpos C ρ t).1 = t.1 := rfl

theorem Dpos_eq (C : Circuit n) (ρ : Fin m → Fin C.N)
    {t : Fin (C.cone ρ).card} {u : Fin ((D C ρ).N - m)} (h : u.1 = t.1) :
    Dpos C ρ u = t := by
  apply Fin.ext
  rw [Dpos_val']
  exact h

theorem sum_Dpreds_apply (C : Circuit n) (ρ : Fin m → Fin C.N) (v : ↥(C.cone ρ))
    (F : Fin (m + (C.cone ρ).card) → ℤ) :
    ((Dpreds C ρ (Kpos C ρ v)).map F).sum
      = (∑ t' : Fin (C.N - n),
          if h : C.idx t' ∈ C.cone ρ then
            ∑ p : Fin (C.preds t').length,
              (if (C.preds t').get p = v.1 then F (Dv C ρ ⟨C.idx t', h⟩) else 0)
          else 0)
        + (∑ j : Fin m, if ρ j = v.1 then F (z C ρ j) else 0) := by
  show ((DrevPreds C ρ (Kpos C ρ v) ++ DfreshPreds C ρ (Kpos C ρ v)).map F).sum = _
  rw [List.map_append, List.sum_append,
    sum_DrevPreds (Kpos C ρ v) F, sum_DfreshPreds (Kpos C ρ v) F,
    Kdec_Kpos C ρ v]

theorem D_pc_split (C : Circuit n) (ρ : Fin m → Fin C.N) (x : Fin (m + (C.cone ρ).card))
    (v : ↥(C.cone ρ)) :
    (D C ρ).pc x (Dv C ρ v)
      = (if x = Dv C ρ v then (1 : ℤ) else 0)
        + (∑ t' : Fin (C.N - n),
            if h : C.idx t' ∈ C.cone ρ then
              ∑ p : Fin (C.preds t').length,
                (if (C.preds t').get p = v.1
                 then (D C ρ).pc x (Dv C ρ ⟨C.idx t', h⟩) else 0)
            else 0)
        + (∑ j : Fin m, if ρ j = v.1 then (D C ρ).pc x (z C ρ j) else 0) := by
  set b := Dv C ρ v with hbdef
  have hbval : b.1 = m + (Kpos C ρ v).1 := Dv_val C ρ v
  have hDN : (D C ρ).N = m + (C.cone ρ).card := rfl
  have hKb : (Kpos C ρ v).1 < (C.cone ρ).card := (Kpos C ρ v).2
  rw [show (D C ρ).pc x b = (if x = b then (1 : ℤ) else 0)
      + (if h : b.1 < m then 0
         else ∑ k : Fin ((D C ρ).preds ⟨b.1 - m, by omega⟩).length,
            (D C ρ).pc x (((D C ρ).preds ⟨b.1 - m, by omega⟩).get k))
      from (D C ρ).pc_eq x b]
  rw [dif_neg (by omega : ¬ b.1 < m)]
  have hidx : Dpos C ρ (⟨b.1 - m, by omega⟩ : Fin ((D C ρ).N - m)) = Kpos C ρ v := by
    apply Dpos_eq
    show b.1 - m = (Kpos C ρ v).1
    omega
  have hstep : (∑ k : Fin ((D C ρ).preds ⟨b.1 - m, by omega⟩).length,
      (D C ρ).pc x (((D C ρ).preds ⟨b.1 - m, by omega⟩).get k))
      = ((Dpreds C ρ (Kpos C ρ v)).map (fun y => (D C ρ).pc x y)).sum := by
    rw [show (D C ρ).preds ⟨b.1 - m, by omega⟩ = Dpreds C ρ (Dpos C ρ ⟨b.1 - m, by omega⟩)
      from rfl, hidx]
    exact sum_get_eq_map_sum _ _
  rw [hstep, sum_Dpreds_apply, add_assoc]

/-! ## The path identity -/

theorem pc_D_z_Dv (C : Circuit n) (ρ : Fin m → Fin C.N) (i : Fin m) :
    ∀ v : ↥(C.cone ρ), (D C ρ).pc (z C ρ i) (Dv C ρ v) = C.pc v.1 (ρ i) := by
  intro v
  refine WellFounded.induction (measure (fun v : ↥(C.cone ρ) => (Kpos C ρ v).1)).wf
    (C := fun v => (D C ρ).pc (z C ρ i) (Dv C ρ v) = C.pc v.1 (ρ i)) v ?_
  intro v ih
  rw [D_pc_split C ρ (z C ρ i) v]
  have h1 : (if z C ρ i = Dv C ρ v then (1 : ℤ) else 0) = 0 := by
    rw [if_neg (z_ne_Dv C ρ i v)]
  have h2 : (∑ t' : Fin (C.N - n),
        if h : C.idx t' ∈ C.cone ρ then
          ∑ p : Fin (C.preds t').length,
            (if (C.preds t').get p = v.1 then
              (D C ρ).pc (z C ρ i) (Dv C ρ ⟨C.idx t', h⟩) else 0)
        else 0)
      = C.Fwd v.1 (fun x => C.pc x (ρ i)) := by
    simp only [Fwd]
    apply Finset.sum_congr rfl
    intro t' _
    by_cases h : C.idx t' ∈ C.cone ρ
    · rw [dif_pos h]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : (C.preds t').get p = v.1
      · rw [if_pos hp, if_pos hp]
        exact ih ⟨C.idx t', h⟩ (by
          have he : C.Edge v.1 (C.idx t') := ⟨t', p, hp, rfl⟩
          exact Kpos_lt_of_edge C ρ v.2 h he)
      · rw [if_neg hp, if_neg hp]
    · rw [dif_neg h]
      symm
      apply Finset.sum_eq_zero
      intro p _
      by_cases hp : (C.preds t').get p = v.1
      · rw [if_pos hp]
        apply pc_eq_zero_of_not_reach
        intro hr
        exact h (mem_cone.mpr ⟨i, hr⟩)
      · rw [if_neg hp]
  have h3 : (∑ j : Fin m, if ρ j = v.1 then (D C ρ).pc (z C ρ i) (z C ρ j) else 0)
      = if v.1 = ρ i then (1 : ℤ) else 0 := by
    have hstep : ∀ j : Fin m, (D C ρ).pc (z C ρ i) (z C ρ j) = if i = j then (1:ℤ) else 0 :=
      fun j => D_pc_z C ρ i j
    simp only [hstep]
    by_cases hri : ρ i = v.1
    · have hzero : ∀ j : Fin m, j ≠ i →
          (if ρ j = v.1 then (if i = j then (1:ℤ) else 0) else 0) = 0 := by
        intro j hj
        by_cases hρj : ρ j = v.1
        · rw [if_pos hρj, if_neg (Ne.symm hj)]
        · rw [if_neg hρj]
      rw [Finset.sum_eq_single i]
      · rw [if_pos hri, if_pos rfl, if_pos hri.symm]
      · intro j _ hj; exact hzero j hj
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · have hzero : ∀ j : Fin m,
          (if ρ j = v.1 then (if i = j then (1:ℤ) else 0) else 0) = 0 := by
        intro j
        by_cases hρj : ρ j = v.1
        · rw [if_pos hρj, if_neg]
          intro hij
          exact hri (by rw [hij]; exact hρj)
        · rw [if_neg hρj]
      rw [Finset.sum_eq_zero (fun j _ => hzero j), if_neg (fun h => hri h.symm)]
  rw [h1, h2, h3, C.pc_fwd v.1 (ρ i)]
  ring

theorem sum_fin_ite_one {k : ℕ} (p : Fin k → Prop) [DecidablePred p] :
    (∑ i : Fin k, if p i then (1:ℕ) else 0) = (Finset.univ.filter p).card := by
  rw [Finset.card_filter]

theorem length_eq_sum_map_one {β : Type*} (l : List β) :
    (l.map (fun _ => (1:ℕ))).sum = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, Nat.add_comm]


variable {n : ℕ} {C : Circuit n} {m : ℕ} {ρ : Fin m → Fin C.N}

/-- Edges of `C` whose head lies in the cone. -/
noncomputable def Ed (C : Circuit n) (ρ : Fin m → Fin C.N) : ℕ :=
  ∑ t : Fin (C.N - n), if h : C.idx t ∈ C.cone ρ then (C.preds t).length else 0

/-- Edges of `C` whose head lies outside the cone. -/
noncomputable def Eout (C : Circuit n) (ρ : Fin m → Fin C.N) : ℕ :=
  ∑ t : Fin (C.N - n), if h : C.idx t ∈ C.cone ρ then 0 else (C.preds t).length

theorem edgeCount_eq (C : Circuit n) (ρ : Fin m → Fin C.N) :
    C.edgeCount = C.Ed ρ + C.Eout ρ := by
  unfold Circuit.edgeCount Ed Eout
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : C.idx t ∈ C.cone ρ <;> simp [h]

theorem D_complexity (C : Circuit n) (ρ : Fin m → Fin C.N) :
    (D C ρ).complexity = (C.cone ρ).card := by
  show m + (C.cone ρ).card - m = (C.cone ρ).card
  exact Nat.add_sub_cancel_left m _

theorem length_DfreshPreds (C : Circuit n) (ρ : Fin m → Fin C.N) (t : Fin (C.cone ρ).card) :
    (DfreshPreds C ρ t).length
      = (Finset.univ.filter (fun j : Fin m => ρ j = Kdec C ρ t)).card := by
  rw [← length_eq_sum_map_one, sum_DfreshPreds, Finset.card_filter]

theorem length_DrevPreds (C : Circuit n) (ρ : Fin m → Fin C.N) (t : Fin (C.cone ρ).card) :
    (DrevPreds C ρ t).length
      = ∑ t' : Fin (C.N - n),
          if h : C.idx t' ∈ C.cone ρ then
            (Finset.univ.filter (fun p : Fin (C.preds t').length =>
              (C.preds t').get p = Kdec C ρ t)).card
          else 0 := by
  rw [← length_eq_sum_map_one, sum_DrevPreds]
  apply Finset.sum_congr rfl
  intro t' _
  by_cases h : C.idx t' ∈ C.cone ρ
  · rw [dif_pos h, dif_pos h, sum_fin_ite_one]
  · rw [dif_neg h, dif_neg h]


theorem Kinc_inj (C : Circuit n) (ρ : Fin m → Fin C.N) : Function.Injective (Kinc C ρ) := by
  intro i j h
  exact (Kiso C ρ).injective (Subtype.ext h)

theorem Kdec_inj (C : Circuit n) (ρ : Fin m → Fin C.N) : Function.Injective (Kdec C ρ) := by
  intro i j h
  exact Fin.rev_inj.mp (Kinc_inj C ρ h)

/-- Each edge of `C` into the cone distributes over the decreasing cone enumeration. -/
theorem card_fiber_Kdec (C : Circuit n) (ρ : Fin m → Fin C.N) {t' : Fin (C.N - n)}
    (h : C.idx t' ∈ C.cone ρ) :
    (∑ t : Fin (C.cone ρ).card,
      (Finset.univ.filter (fun p : Fin (C.preds t').length =>
        (C.preds t').get p = Kdec C ρ t)).card) = (C.preds t').length := by
  have hterm : ∀ t : Fin (C.cone ρ).card,
      (Finset.univ.filter (fun p : Fin (C.preds t').length =>
        (C.preds t').get p = Kdec C ρ t)).card
      = ∑ p : Fin (C.preds t').length,
          (if (C.preds t').get p = Kdec C ρ t then 1 else 0) :=
    fun t => (sum_fin_ite_one
      (fun p : Fin (C.preds t').length => (C.preds t').get p = Kdec C ρ t)).symm
  simp only [hterm]
  rw [Finset.sum_comm (β := ℕ)]
  have hinner : ∀ p : Fin (C.preds t').length,
      (∑ t : Fin (C.cone ρ).card,
        (if (C.preds t').get p = Kdec C ρ t then (1 : ℕ) else 0)) = (1 : ℕ) := by
    intro p
    have hv : (C.preds t').get p ∈ C.cone ρ :=
      C.cone_pred (List.get_mem (C.preds t') p) h
    refine (Finset.sum_eq_single
      (f := fun t : Fin (C.cone ρ).card =>
        (if (C.preds t').get p = Kdec C ρ t then (1 : ℕ) else 0))
      (s := Finset.univ) (Kpos C ρ ⟨(C.preds t').get p, hv⟩) ?_ ?_).trans ?_
    · intro b _ hb
      show (if (C.preds t').get p = Kdec C ρ b then (1 : ℕ) else 0) = 0
      rw [if_neg]
      intro hbv
      exact hb (Kdec_inj C ρ (by rw [hbv.symm, Kdec_Kpos]))
    · intro habs
      exact absurd (Finset.mem_univ _) habs
    · show (if (C.preds t').get p = Kdec C ρ
        (Kpos C ρ ⟨(C.preds t').get p, hv⟩) then (1 : ℕ) else 0) = 1
      rw [Kdec_Kpos, if_pos rfl]
  have hsum : (∑ p : Fin (C.preds t').length,
      ∑ t : Fin (C.cone ρ).card,
        (if (C.preds t').get p = Kdec C ρ t then 1 else 0))
      = ∑ p : Fin (C.preds t').length, (1 : ℕ) :=
    Finset.sum_congr rfl (fun p _ => hinner p)
  rw [hsum]
  simp

/-- The reversed edges of the transposed circuit amount to the cone-headed edges of `C`. -/
theorem sum_length_DrevPreds (C : Circuit n) (ρ : Fin m → Fin C.N) :
    (∑ t : Fin (C.cone ρ).card, (DrevPreds C ρ t).length) = C.Ed ρ := by
  have hterm : ∀ t : Fin (C.cone ρ).card,
      (DrevPreds C ρ t).length
      = ∑ t' : Fin (C.N - n),
          if h : C.idx t' ∈ C.cone ρ then
            (Finset.univ.filter (fun p : Fin (C.preds t').length =>
              (C.preds t').get p = Kdec C ρ t)).card
          else 0 := fun t => length_DrevPreds C ρ t
  simp only [hterm]
  rw [Finset.sum_comm (β := ℕ)]
  unfold Ed
  apply Finset.sum_congr rfl
  intro t' _
  by_cases h : C.idx t' ∈ C.cone ρ
  · simp only [dif_pos h]
    exact card_fiber_Kdec C ρ h
  · simp only [dif_neg h]
    simp

/-- The fresh edges of the transposed circuit amount to the `m` rows. -/
theorem sum_length_DfreshPreds (C : Circuit n) (ρ : Fin m → Fin C.N) :
    (∑ t : Fin (C.cone ρ).card, (DfreshPreds C ρ t).length) = m := by
  have hterm : ∀ t : Fin (C.cone ρ).card,
      (DfreshPreds C ρ t).length
      = ∑ i : Fin m, (if ρ i = Kdec C ρ t then 1 else 0) := by
    intro t
    rw [length_DfreshPreds]
    exact (sum_fin_ite_one (fun i : Fin m => ρ i = Kdec C ρ t)).symm
  simp only [hterm]
  rw [Finset.sum_comm (β := ℕ)]
  have hinner : ∀ i : Fin m,
      (∑ t : Fin (C.cone ρ).card, (if ρ i = Kdec C ρ t then (1 : ℕ) else 0)) = (1 : ℕ) := by
    intro i
    refine (Finset.sum_eq_single
      (f := fun t : Fin (C.cone ρ).card =>
        (if ρ i = Kdec C ρ t then (1 : ℕ) else 0))
      (s := Finset.univ) (Kpos C ρ ⟨ρ i, cone_rho C ρ i⟩) ?_ ?_).trans ?_
    · intro b _ hb
      show (if ρ i = Kdec C ρ b then (1 : ℕ) else 0) = 0
      rw [if_neg]
      intro hbv
      exact hb (Kdec_inj C ρ (by rw [hbv.symm, Kdec_Kpos]))
    · intro habs
      exact absurd (Finset.mem_univ _) habs
    · show (if ρ i = Kdec C ρ (Kpos C ρ ⟨ρ i, cone_rho C ρ i⟩) then (1 : ℕ) else 0) = 1
      rw [Kdec_Kpos, if_pos rfl]
  have hsum : (∑ i : Fin m,
      ∑ t : Fin (C.cone ρ).card, (if ρ i = Kdec C ρ t then 1 else 0))
      = ∑ i : Fin m, (1 : ℕ) :=
    Finset.sum_congr rfl (fun i _ => hinner i)
  rw [hsum]
  simp

/-- Reindexing the non-input vertices of the transposed circuit by the decreasing enumeration. -/
theorem sum_Dpos (C : Circuit n) (ρ : Fin m → Fin C.N) (F : Fin (C.cone ρ).card → ℕ) :
    (∑ t : Fin ((D C ρ).N - m), F (Dpos C ρ t)) = ∑ t : Fin (C.cone ρ).card, F t := by
  have hN : (D C ρ).N - m = (C.cone ρ).card := by
    show m + (C.cone ρ).card - m = _
    exact Nat.add_sub_cancel_left m _
  exact Fintype.sum_equiv (finCongr hN) (fun t => F (Dpos C ρ t)) (fun t => F t)
    (fun t => congrArg F (Fin.ext (by simp [Dpos, finCongr])))

/-- The transposed circuit has exactly `Ed + m` edges. -/
theorem D_edgeCount (C : Circuit n) (ρ : Fin m → Fin C.N) :
    (D C ρ).edgeCount = C.Ed ρ + m := by
  show (∑ t : Fin ((D C ρ).N - m), (Dpreds C ρ (Dpos C ρ t)).length) = C.Ed ρ + m
  have hsplit : ∀ t : Fin ((D C ρ).N - m),
      (Dpreds C ρ (Dpos C ρ t)).length
      = (DrevPreds C ρ (Dpos C ρ t)).length
        + (DfreshPreds C ρ (Dpos C ρ t)).length := by
    intro t
    rw [Dpreds, List.length_append]
  simp only [hsplit, Finset.sum_add_distrib]
  rw [sum_Dpos C ρ (fun t => (DrevPreds C ρ t).length),
      sum_Dpos C ρ (fun t => (DfreshPreds C ρ t).length),
      sum_length_DrevPreds, sum_length_DfreshPreds]


/-! ## Structural bounds on the cone -/

/-- Every input vertex lies in the cone, because no column of `A` is zero. -/
theorem inputVertex_mem_cone (C : Circuit n) (ρ : Fin m → Fin C.N)
    (A : Matrix (Fin m) (Fin n) ℤ) (hρ : ∀ i, C.repr (ρ i) = A i)
    (hcol : ∀ j : Fin n, ∃ i : Fin m, A i j ≠ 0) (j : Fin n) :
    C.inputVertex j ∈ C.cone ρ := by
  obtain ⟨i, hi⟩ := hcol j
  rw [mem_cone]
  refine ⟨i, reach_of_pc_ne_zero C _ _ ?_⟩
  rw [← comp_eq_pc]
  intro h
  apply hi
  have h2 := congrFun (hρ i) j
  simp only [Circuit.repr] at h2
  rw [h2] at h
  exact h

theorem n_le_cone_card (C : Circuit n) (ρ : Fin m → Fin C.N)
    (hin : ∀ j : Fin n, C.inputVertex j ∈ C.cone ρ) :
    n ≤ (C.cone ρ).card := by
  have hinj : Function.Injective
      (fun j : Fin n => (⟨C.inputVertex j, hin j⟩ : ↥(C.cone ρ))) := by
    intro a b hab
    have h2 := congrArg (fun v : ↥(C.cone ρ) => (v.1 : Fin C.N)) hab
    exact Fin.ext (by simpa [inputVertex] using h2)
  have := Fintype.card_le_of_injective _ hinj
  simpa [Fintype.card_coe] using this

/-- The vertices outside the cone, counted as non-input indices. -/
noncomputable def S (C : Circuit n) (ρ : Fin m → Fin C.N) : Finset (Fin (C.N - n)) :=
  Finset.univ.filter (fun t => C.idx t ∉ C.cone ρ)

theorem Eout_eq_sum_S (C : Circuit n) (ρ : Fin m → Fin C.N) :
    C.Eout ρ = ∑ t ∈ C.S ρ, (C.preds t).length := by
  unfold Eout S
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : C.idx t ∈ C.cone ρ
  · simp [h]
  · simp [h]

theorem S_card_le_Eout (C : Circuit n) (ρ : Fin m → Fin C.N) :
    (C.S ρ).card ≤ C.Eout ρ := by
  rw [Eout_eq_sum_S]
  have hcard : (C.S ρ).card = ∑ t ∈ C.S ρ, (1 : ℕ) := by simp
  rw [hcard]
  exact Finset.sum_le_sum (fun t _ => C.reduced t)

theorem N_le_Eout_add_cone (C : Circuit n) (ρ : Fin m → Fin C.N)
    (hin : ∀ j : Fin n, C.inputVertex j ∈ C.cone ρ) :
    C.N ≤ C.Eout ρ + (C.cone ρ).card := by
  classical
  have hsub : (Finset.univ : Finset (Fin C.N)) ⊆ C.cone ρ ∪ (C.S ρ).image C.idx := by
    intro v _
    by_cases hv : v ∈ C.cone ρ
    · exact Finset.mem_union_left _ hv
    · apply Finset.mem_union_right
      have hvn : ¬ v.1 < n := by
        intro hlt
        refine hv ?_
        have hv' : C.inputVertex ⟨v.1, hlt⟩ = v := Fin.ext rfl
        rw [← hv']
        exact hin ⟨v.1, hlt⟩
      refine Finset.mem_image.mpr ⟨C.tIdx v hvn, ?_, C.idx_tIdx hvn⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [C.idx_tIdx hvn]
      exact hv
  calc C.N = (Finset.univ : Finset (Fin C.N)).card := by simp
    _ ≤ (C.cone ρ ∪ (C.S ρ).image C.idx).card := Finset.card_le_card hsub
    _ ≤ (C.cone ρ).card + ((C.S ρ).image C.idx).card := Finset.card_union_le _ _
    _ ≤ (C.cone ρ).card + (C.S ρ).card :=
        Nat.add_le_add_left Finset.card_image_le _
    _ ≤ (C.cone ρ).card + C.Eout ρ := Nat.add_le_add_left (S_card_le_Eout C ρ) _
    _ = C.Eout ρ + (C.cone ρ).card := Nat.add_comm _ _

/-! ## The counting inequality -/

theorem D_equiv_add_le (C : Circuit n) (ρ : Fin m → Fin C.N)
    (hnk : n ≤ (C.cone ρ).card) (hN : C.N ≤ C.Eout ρ + (C.cone ρ).card) :
    (D C ρ).equivComplexity + n ≤ C.equivComplexity + m := by
  have hD : (D C ρ).edgeCount = C.Ed ρ + m := D_edgeCount C ρ
  have hDc : (D C ρ).complexity = (C.cone ρ).card := D_complexity C ρ
  have hE : C.edgeCount = C.Ed ρ + C.Eout ρ := edgeCount_eq C ρ
  have hL : (D C ρ).equivComplexity + n
      = (C.Ed ρ + m) - (C.cone ρ).card + n := by
    show (D C ρ).edgeCount - (D C ρ).complexity + n = _
    rw [hD, hDc]
  have hR : C.equivComplexity + m
      = (C.Ed ρ + C.Eout ρ) - (C.N - n) + m := by
    show C.edgeCount - (C.N - n) + m = _
    rw [hE]
  rw [hL, hR]
  have hkE : (C.cone ρ).card ≤ C.Ed ρ + m := by
    have h1 : (D C ρ).complexity ≤ (D C ρ).edgeCount := Circuit.complexity_le_edgeCount (D C ρ)
    rwa [hDc, hD] at h1
  have hEN : C.N - n ≤ C.Ed ρ + C.Eout ρ := by
    have h1 : C.complexity ≤ C.edgeCount := Circuit.complexity_le_edgeCount C
    rw [edgeCount_eq C ρ] at h1
    exact h1
  have arith : ∀ (e o k N m' n' : ℕ), n' ≤ k → k ≤ e + m' → N ≤ o + k →
      N - n' ≤ e + o → (e + m') - k + n' ≤ (e + o) - (N - n') + m' := by
    intro e o k N m' n' h1 h2 h3 h4
    omega
  exact arith (C.Ed ρ) (C.Eout ρ) (C.cone ρ).card C.N m n hnk hkE hN hEN


theorem sum_get_map {α β : Type*} [AddCommMonoid β] (l : List α) (f : α → β) :
    (∑ i : Fin l.length, f (l.get i)) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  have h : (List.ofFn (fun i : Fin l.length => f (l.get i))) = List.map f (List.ofFn l.get) :=
    (List.map_ofFn).symm
  rw [h, List.ofFn_get]

theorem sum_flatMap {α β : Type*} [AddCommMonoid β] (l : List α) (g : α → List β) :
    (l.flatMap g).sum = (l.map (fun a => (g a).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem sum_map_finRange {M : Type*} [AddCommMonoid M] {k : ℕ} (f : Fin k → M) :
    ((List.finRange k).map f).sum = ∑ i : Fin k, f i := by
  rw [← List.ofFn_id k, List.map_ofFn, List.sum_ofFn]
  rfl

/-! ## The star circuit -/

/-- The predecessor list of the `t`-th non-input vertex of the star circuit: the inputs,
repeated according to the entries of row `t`.  Used only for nonnegative rows. -/
noncomputable def starPreds {m : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (t : Fin m) :
    List (Fin (n + m)) :=
  (List.finRange n).flatMap
    (fun j => List.replicate (A t j).toNat
      ⟨j.1, lt_of_lt_of_le j.2 (Nat.le_add_right n m)⟩)

theorem starPreds_length {m : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (t : Fin m) :
    (starPreds A t).length = ∑ j : Fin n, (A t j).toNat := by
  rw [starPreds, List.length_flatMap, sum_map_finRange]
  exact Finset.sum_congr rfl (fun j _ => List.length_replicate)

theorem starPreds_mem_lt {m : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (t : Fin m)
    {u : Fin (n + m)} (hu : u ∈ starPreds A t) : u.1 < n := by
  rw [starPreds] at hu
  obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp hu
  rw [List.eq_of_mem_replicate hj]
  exact j.2

/-- The star circuit of a matrix with nonnegative entries and no zero row: one non-input
vertex per row, whose incoming edges are copies of the inputs. -/
noncomputable def star {m : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : ∀ i j, 0 ≤ A i j)
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
    rw [starPreds_length]
    obtain ⟨j0, hj0⟩ := hrow (Fin.cast (by simp) t)
    have hpos : 0 < (A (Fin.cast (by simp) t) j0).toNat := by
      have h1 : 0 < A (Fin.cast (by simp) t) j0 :=
        lt_of_le_of_ne (hA _ _) (Ne.symm hj0)
      omega
    exact lt_of_lt_of_le hpos (Finset.single_le_sum
      (f := fun j : Fin n => (A (Fin.cast (by simp) t) j).toNat)
      (s := Finset.univ) (fun j _ => Nat.zero_le _) (Finset.mem_univ j0))

theorem star_preds {m : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, A i j ≠ 0) (t : Fin m) :
    (star A hA hrow).preds (Fin.cast (by simp : m = (n + m) - n) t) = starPreds A t := by
  show starPreds A (Fin.cast (by simp) (Fin.cast (by simp : m = (n + m) - n) t)) = starPreds A t
  rw [show Fin.cast (by simp : (n + m) - n = m)
        (Fin.cast (by simp : m = (n + m) - n) t) = t from Fin.ext (by simp)]

/-- An input vertex represents the corresponding basis vector, in the `comp` formulation. -/
theorem comp_inputVertex (C : Circuit n) (i j : Fin n) :
    C.comp i (C.inputVertex j) = if i = j then (1 : ℤ) else 0 := by
  rw [Circuit.comp_eq, dif_pos (show (C.inputVertex j).1 < n from j.2)]
  have hfin : (⟨(C.inputVertex j).1, show (C.inputVertex j).1 < n from j.2⟩ : Fin n) = j :=
    Fin.ext rfl
  rw [hfin]

/-- The vertex of the star circuit representing row `t`. -/
noncomputable def starRow {m : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, A i j ≠ 0) (t : Fin m) : Fin (n + m) :=
  ⟨n + t.1, by have := t.2; omega⟩

theorem star_repr {m : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, A i j ≠ 0) (t : Fin m) :
    (star A hA hrow).repr (starRow A hA hrow t) = A t := by
  funext i
  show (star A hA hrow).comp i (starRow A hA hrow t) = A t i
  have hidx : (star A hA hrow).idx (Fin.cast (by simp : m = (n + m) - n) t)
      = starRow A hA hrow t := by
    apply Fin.ext
    show n + (Fin.cast (by simp : m = (n + m) - n) t).1 = n + t.1
    rfl
  have hstep : (star A hA hrow).comp i (starRow A hA hrow t)
      = ∑ x : Fin (starPreds A t).length,
          (star A hA hrow).comp i ((starPreds A t).get x) := by
    have h := congrFun (Circuit.repr_idx (C := star A hA hrow)
      (t := Fin.cast (by simp : m = (n + m) - n) t)) i
    rw [star_preds A hA hrow t, hidx] at h
    simp only [Circuit.repr, Finset.sum_apply] at h
    exact h
  rw [hstep]
  have hmain : (∑ x : Fin (starPreds A t).length,
      (star A hA hrow).comp i ((starPreds A t).get x)) = ((A t i).toNat : ℤ) := by
    refine (sum_get_map (starPreds A t) (fun u => (star A hA hrow).comp i u)).trans ?_
    rw [starPreds, List.map_flatMap, sum_flatMap, sum_map_finRange]
    have hterm : ∀ j : Fin n,
        ((List.replicate (A t j).toNat
            ⟨j.1, lt_of_lt_of_le j.2 (Nat.le_add_right n m)⟩).map
          (fun u => (star A hA hrow).comp i u)).sum
        = ((A t j).toNat : ℤ) * (if i = j then (1 : ℤ) else 0) := by
      intro j
      rw [List.map_replicate, List.sum_replicate, nsmul_eq_mul]
      congr 2
      exact comp_inputVertex (C := star A hA hrow) i j
    refine (Finset.sum_congr rfl (fun j _ => hterm j)).trans ?_
    refine (Finset.sum_eq_single
      (f := fun j : Fin n => ((A t j).toNat : ℤ) * (if i = j then (1 : ℤ) else 0))
      (s := Finset.univ) i ?_ ?_).trans ?_
    · intro b _ hb
      show ((A t b).toNat : ℤ) * (if i = b then (1 : ℤ) else 0) = 0
      rw [if_neg (fun h => hb h.symm), mul_zero]
    · intro habs
      exact absurd (Finset.mem_univ i) habs
    · show ((A t i).toNat : ℤ) * (if i = i then (1 : ℤ) else 0) = (A t i).toNat
      rw [if_pos rfl, mul_one]
  rw [hmain, Int.toNat_of_nonneg (hA t i)]

/-- The star circuit computes its matrix. -/
theorem star_computes {m : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : ∀ i j, 0 ≤ A i j)
    (hrow : ∀ i, ∃ j, A i j ≠ 0) : (star A hA hrow).Computes A := by
  intro i
  exact Or.inl ⟨starRow A hA hrow i, star_repr A hA hrow i⟩


/-! ## The transposition principle (Lemma 2) -/

/-- Every nonzero row is represented by some vertex. -/
theorem exists_repr_of_computes (C : Circuit n) {m : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hC : C.Computes A) (hrow : ∀ i, ∃ j, A i j ≠ 0) :
    ∃ ρ : Fin m → Fin C.N, ∀ i, C.repr (ρ i) = A i := by
  classical
  have hne : ∀ i : Fin m, A i ≠ 0 := by
    intro i h
    obtain ⟨j, hj⟩ := hrow i
    exact hj (by rw [h]; rfl)
  have hex : ∀ i : Fin m, ∃ v : Fin C.N, C.repr v = A i := by
    intro i
    rcases hC i with h | h
    · exact h
    · exact absurd h (hne i)
  exact ⟨fun i => Classical.choose (hex i), fun i => Classical.choose_spec (hex i)⟩

/-- The transposed circuit computes the transposed matrix. -/
theorem D_computes (C : Circuit n) (ρ : Fin m → Fin C.N) (A : Matrix (Fin m) (Fin n) ℤ)
    (hρ : ∀ i, C.repr (ρ i) = A i) (hcol : ∀ j : Fin n, ∃ i : Fin m, A i j ≠ 0) :
    (D C ρ).Computes (Matrix.transpose A) := by
  intro a
  have hca : C.inputVertex a ∈ C.cone ρ := by
    obtain ⟨i, hi⟩ := hcol a
    rw [mem_cone]
    refine ⟨i, reach_of_pc_ne_zero C _ _ ?_⟩
    rw [← comp_eq_pc]
    intro h
    apply hi
    have h2 := congrFun (hρ i) a
    simp only [Circuit.repr] at h2
    rw [h2] at h
    exact h

  refine Or.inl ⟨Dv C ρ ⟨C.inputVertex a, hca⟩, ?_⟩
  funext i
  show (D C ρ).comp i (Dv C ρ ⟨C.inputVertex a, hca⟩) = Matrix.transpose A a i
  have hzin : z C ρ i = (D C ρ).inputVertex i := Fin.ext rfl
  rw [comp_eq_pc, ← hzin, pc_D_z_Dv]
  have hpc : C.pc (C.inputVertex a) (ρ i) = A i a := by
    rw [← comp_eq_pc]
    have h2 := congrFun (hρ i) a
    simpa only [Circuit.repr] using h2
  show C.pc (C.inputVertex a) (ρ i) = Matrix.transpose A a i
  rw [hpc]
  rfl

theorem minEquiv_transpose_add_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, A i j ≠ 0)
    (hcol : ∀ j, ∃ i, A i j ≠ 0) :
    minEquivComplexity (Matrix.transpose A) + n ≤ minEquivComplexity A + m := by
  classical
  have hne : { k | ∃ C : Circuit n, C.equivComplexity = k ∧ C.Computes A }.Nonempty :=
    ⟨_, star A hA hrow, rfl, star_computes A hA hrow⟩
  obtain ⟨C, hCeq, hCcomp⟩ := Nat.sInf_mem hne
  obtain ⟨ρ, hρ⟩ := exists_repr_of_computes C A hCcomp hrow
  have hin : ∀ j : Fin n, C.inputVertex j ∈ C.cone ρ := inputVertex_mem_cone C ρ A hρ hcol
  have hDcomp : (D C ρ).Computes (Matrix.transpose A) := D_computes C ρ A hρ hcol
  have h1 : minEquivComplexity (Matrix.transpose A) ≤ (D C ρ).equivComplexity :=
    Nat.sInf_le ⟨D C ρ, rfl, hDcomp⟩
  have h2 : (D C ρ).equivComplexity + n ≤ C.equivComplexity + m :=
    D_equiv_add_le C ρ (n_le_cone_card C ρ hin) (N_le_Eout_add_cone C ρ hin)
  calc minEquivComplexity (Matrix.transpose A) + n
      ≤ (D C ρ).equivComplexity + n := Nat.add_le_add_right h1 n
    _ ≤ C.equivComplexity + m := h2
    _ = minEquivComplexity A + m := by rw [hCeq]; rfl

/-- **Lemma 2** (transposition principle): for a nonnegative integer matrix with no zero row
and no zero column, `L(A) + m = L(Aᵀ) + n`, in terms of the minimal equivalent complexity
(the size measure used for unbounded fan-in circuits). -/
theorem lemma2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, A i j ≠ 0)
    (hcol : ∀ j, ∃ i, A i j ≠ 0) :
    minEquivComplexity A + m = minEquivComplexity (Matrix.transpose A) + n := by
  have hAt : ∀ i j, 0 ≤ Matrix.transpose A i j := fun i j => hA j i
  have hrowAt : ∀ i, ∃ j, Matrix.transpose A i j ≠ 0 := hcol
  have hcolAt : ∀ j, ∃ i, Matrix.transpose A i j ≠ 0 := hrow
  have h1 := minEquiv_transpose_add_le A hA hrow hcol
  have h2 := minEquiv_transpose_add_le (Matrix.transpose A) hAt hrowAt hcolAt
  rw [Matrix.transpose_transpose] at h2
  omega

/-- Lemma 2 in the chain model: since all three size measures agree (`lemma1`), the identity
extends to the additive complexity `L` of vector addition chains, `L(A) + m = L(Aᵀ) + n`. -/
theorem chainComplexity_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ)
    (hA : ∀ i j, 0 ≤ A i j) (hrow : ∀ i, ∃ j, A i j ≠ 0)
    (hcol : ∀ j, ∃ i, A i j ≠ 0) :
    chainComplexity A + m = chainComplexity (Matrix.transpose A) + n := by
  have h := lemma2 A hA hrow hcol
  rw [(lemma1 A).1, (lemma1 A).2,
      (lemma1 (Matrix.transpose A)).1, (lemma1 (Matrix.transpose A)).2]
  exact h

end Circuit

/-! ### Availability of vectors in a chain; nonempty sets of chain lengths -/


open scoped BigOperators

namespace VecAddChain

variable {n : ℕ}

/-! ## Chains: availability of vectors, extensions, and appending a sum

The composition argument repeatedly needs to *extend* a chain by a new computed vector that is
the sum of two vectors already available to the chain.  A vector is `Available` if it is the zero
vector or a member of the chain's final pool; appending such sums is `VecAddChain.available_add`.
-/

/-- A vector is *available* to a chain `c` if it is the zero vector or one of the vectors in
the final pool of `c` (a basis vector or one of the computed `y`'s). -/
def Available (c : VecAddChain n) (v : Vec n) : Prop :=
  v = 0 ∨ ∃ a : Fin n ⊕ Fin c.L, chainPool c.y c.L (le_refl c.L) a = v

theorem available_zero (c : VecAddChain n) : c.Available 0 := Or.inl rfl


theorem available_basis (c : VecAddChain n) (i : Fin n) : c.Available (basisVec i) :=
  Or.inr ⟨Sum.inl i, rfl⟩


theorem available_of_mem {c : VecAddChain n} {v : Vec n}
    (h : v ∈ Set.range basisVec ∪ Set.range c.y ∪ {0}) : c.Available v := by
  rcases h with (⟨i, hi⟩ | ⟨j, hj⟩) | h0
  · exact Or.inr ⟨Sum.inl i, hi⟩
  · exact Or.inr ⟨Sum.inr j, hj⟩
  · exact Or.inl h0

theorem mem_of_available {c : VecAddChain n} {v : Vec n} (h : c.Available v) :
    v ∈ Set.range basisVec ∪ Set.range c.y ∪ {0} := by
  rcases h with rfl | ⟨a, ha⟩
  · exact Or.inr rfl
  · rcases a with i | j
    · exact Or.inl (Or.inl ⟨i, ha⟩)
    · exact Or.inl (Or.inr ⟨j, ha⟩)

theorem available_of_computes {m : ℕ} {c : VecAddChain n} {M : Matrix (Fin m) (Fin n) ℤ}
    (h : c.Computes M) (i : Fin m) : c.Available (M i) :=
  available_of_mem (h i)

/-- `Extends c c'` means the computed vectors of `c` all occur among those of `c'`. -/
def Extends (c c' : VecAddChain n) : Prop :=
  ∀ i : Fin c.L, ∃ j : Fin c'.L, c'.y j = c.y i

theorem Extends.refl (c : VecAddChain n) : c.Extends c := fun i => ⟨i, rfl⟩

theorem Extends.trans {c₁ c₂ c₃ : VecAddChain n} (h₁ : c₁.Extends c₂)
    (h₂ : c₂.Extends c₃) : c₁.Extends c₃ := by
  intro i
  obtain ⟨j, hj⟩ := h₁ i
  obtain ⟨k, hk⟩ := h₂ j
  exact ⟨k, hk.trans hj⟩

theorem Available.mono {c c' : VecAddChain n} (h : c.Extends c') {v : Vec n}
    (hv : c.Available v) : c'.Available v := by
  rcases hv with rfl | ⟨a, ha⟩
  · exact Or.inl rfl
  · rcases a with i | j
    · exact Or.inr ⟨Sum.inl i, ha⟩
    · obtain ⟨k, hk⟩ := h j
      refine Or.inr ⟨Sum.inr k, ?_⟩
      show c'.y k = v
      rw [hk]
      show c.y j = v
      rw [← ha]
      rfl

/-- The vector function of `snoc`: the old vectors, and one new vector at the end. -/
def snocY (c : VecAddChain n) (a b : Fin n ⊕ Fin c.L) (i : Fin (c.L + 1)) : Vec n :=
  if h : (i : ℕ) < c.L then c.y ⟨i.1, h⟩
  else chainPool c.y c.L (le_refl c.L) a + chainPool c.y c.L (le_refl c.L) b

theorem snocY_of_lt (c : VecAddChain n) (a b : Fin n ⊕ Fin c.L) {i : Fin (c.L + 1)}
    (h : (i : ℕ) < c.L) : snocY c a b i = c.y ⟨i.1, h⟩ := dif_pos h

theorem snocY_of_not_lt (c : VecAddChain n) (a b : Fin n ⊕ Fin c.L) {i : Fin (c.L + 1)}
    (h : ¬ (i : ℕ) < c.L) :
    snocY c a b i = chainPool c.y c.L (le_refl c.L) a + chainPool c.y c.L (le_refl c.L) b :=
  dif_neg h

theorem snocY_last (c : VecAddChain n) (a b : Fin n ⊕ Fin c.L) :
    snocY c a b ⟨c.L, by omega⟩
      = chainPool c.y c.L (le_refl c.L) a + chainPool c.y c.L (le_refl c.L) b :=
  snocY_of_not_lt c a b (lt_irrefl c.L)

theorem chainPool_snocY (c : VecAddChain n) (a b : Fin n ⊕ Fin c.L) (k : ℕ)
    (hk : k ≤ c.L) (hk' : k ≤ c.L + 1) (x : Fin n ⊕ Fin k) :
    chainPool (snocY c a b) k hk' x = chainPool c.y k hk x := by
  rcases x with i | j
  · rfl
  · show snocY c a b ⟨j.1, lt_of_lt_of_le j.2 hk'⟩ = c.y ⟨j.1, lt_of_lt_of_le j.2 hk⟩
    rw [snocY_of_lt c a b (lt_of_lt_of_le j.2 hk)]

/-- Append to a chain the sum of two available vectors (given by their pool indices). -/
def snoc (c : VecAddChain n) (a b : Fin n ⊕ Fin c.L) : VecAddChain n where
  L := c.L + 1
  y := snocY c a b
  valid := by
    rintro ⟨iv, hiv⟩
    by_cases h : iv < c.L
    · obtain ⟨ax, bx, hx⟩ := c.valid ⟨iv, h⟩
      refine ⟨ax, bx, ?_⟩
      rw [snocY_of_lt c a b h, hx, chainPool_snocY, chainPool_snocY]
    · have hie : iv = c.L := by omega
      subst hie
      refine ⟨a, b, ?_⟩
      rw [snocY_of_not_lt c a b h,
        chainPool_snocY c a b c.L (le_refl c.L) (by omega),
        chainPool_snocY c a b c.L (le_refl c.L) (by omega)]

theorem snoc_L (c : VecAddChain n) (a b : Fin n ⊕ Fin c.L) : (c.snoc a b).L = c.L + 1 := rfl

theorem extends_snoc (c : VecAddChain n) (a b : Fin n ⊕ Fin c.L) : c.Extends (c.snoc a b) := by
  intro i
  have hL : (c.snoc a b).L = c.L + 1 := rfl
  refine ⟨⟨i.1, by rw [hL]; omega⟩, ?_⟩
  show snocY c a b ⟨i.1, _⟩ = c.y i
  rw [snocY_of_lt c a b i.2]

theorem available_snoc_last (c : VecAddChain n) (a b : Fin n ⊕ Fin c.L) :
    (c.snoc a b).Available (chainPool c.y c.L (le_refl c.L) a
      + chainPool c.y c.L (le_refl c.L) b) := by
  have hL : (c.snoc a b).L = c.L + 1 := rfl
  refine Or.inr ⟨Sum.inr ⟨c.L, by rw [hL]; omega⟩, ?_⟩
  show snocY c a b ⟨c.L, _⟩ = _
  exact snocY_last c a b

/-- If two vectors are available to `c`, they can be made available to an extension of `c`
whose length grew by at most one, and their sum is available to that extension. -/
theorem available_add (c : VecAddChain n) {u v : Vec n} (hu : c.Available u) (hv : c.Available v) :
    ∃ c' : VecAddChain n, c'.L ≤ c.L + 1 ∧ c.Extends c' ∧ c'.Available (u + v) := by
  rcases hu with rfl | ⟨a, ha⟩
  · exact ⟨c, by omega, Extends.refl c, by rw [zero_add]; exact hv⟩
  rcases hv with rfl | ⟨b, hb⟩
  · exact ⟨c, by omega, Extends.refl c, by rw [add_zero]; exact Or.inr ⟨a, ha⟩⟩
  · refine ⟨c.snoc a b, by rw [snoc_L], extends_snoc c a b, ?_⟩
    rw [← ha, ← hb]
    exact available_snoc_last c a b

end VecAddChain

/-! ## Nonemptiness of the set of chain lengths for nonnegative matrices -/

/-- Replace the zero rows of a matrix with the first basis vector.  The nonzero rows are
unchanged, so a chain computing the result also computes the original matrix (the zero
vector is always assumed represented). -/
noncomputable def fixZeroRows {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hn : 0 < n) :
    Matrix (Fin m) (Fin n) ℤ := by
  classical
  exact fun i j => if _h : ∃ j, A i j ≠ 0 then A i j else if j = ⟨0, hn⟩ then 1 else 0

theorem fixZeroRows_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hn : 0 < n)
    (i : Fin m) (j : Fin n) :
    fixZeroRows A hn i j
      = if _h : ∃ j, A i j ≠ 0 then A i j else if j = ⟨0, hn⟩ then 1 else 0 := by
  classical
  rfl

theorem chainSet_nonempty {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (hA : ∀ i j, 0 ≤ A i j) :
    (ChainSet A).Nonempty := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨0, ⟨⟨0, fun i => i.elim0, fun k => k.elim0⟩, rfl, ?_⟩⟩
    intro i
    exact Or.inr (funext fun j => j.elim0)
  · have hA'nn : ∀ i j, 0 ≤ fixZeroRows A hn i j := by
      intro i j
      rw [fixZeroRows_apply]
      by_cases h : ∃ j, A i j ≠ 0
      · rw [dif_pos h]; exact hA i j
      · rw [dif_neg h]
        by_cases hj : j = (⟨0, hn⟩ : Fin n)
        · rw [if_pos hj]; norm_num
        · rw [if_neg hj]
    have hA'row : ∀ i, ∃ j, fixZeroRows A hn i j ≠ 0 := by
      intro i
      by_cases h : ∃ j, A i j ≠ 0
      · obtain ⟨j, hj⟩ := h
        refine ⟨j, ?_⟩
        rw [fixZeroRows_apply, dif_pos ⟨j, hj⟩]
        exact hj
      · refine ⟨⟨0, hn⟩, ?_⟩
        rw [fixZeroRows_apply, dif_neg h, if_pos rfl]
        norm_num
    have hcomp : (Circuit.star (fixZeroRows A hn) hA'nn hA'row).Computes (fixZeroRows A hn) :=
      Circuit.star_computes _ hA'nn hA'row
    refine ⟨_, ⟨(Circuit.star (fixZeroRows A hn) hA'nn hA'row).toChain, rfl, ?_⟩⟩
    intro i
    have h1 := (Circuit.star (fixZeroRows A hn) hA'nn hA'row).toChain_computes _ hcomp i
    by_cases h : ∃ j, A i j ≠ 0
    · have heq : A i = fixZeroRows A hn i := by
        funext j
        rw [fixZeroRows_apply, dif_pos h]
      rw [heq]
      exact h1
    · right
      funext j
      exact not_not.mp (not_exists.mp h j)

/-! ## Addition chains of natural numbers -/

/-- An addition chain for a natural number: a sequence `a 0, a 1, …, a L` with `a 0 = 1` in which
every element `a (i+1)` with `i < L` is the sum of two earlier elements.  The values `a i` for
`i > L` are irrelevant junk. -/
structure NatChain where
  /-- the length of the chain -/
  L : ℕ
  /-- the elements of the chain -/
  a : ℕ → ℕ
  /-- the chain starts at `1` -/
  h0 : a 0 = 1
  /-- every element is the sum of two earlier ones -/
  step : ∀ i < L, ∃ p q : ℕ, p ≤ i ∧ q ≤ i ∧ a (i + 1) = a p + a q

namespace NatChain

/-- A chain is *linear* if every element is the sum of the previous element and an earlier one:
`a (i+1) = a i + a p` with `p ≤ i`. -/
def IsLinear (c : NatChain) : Prop := ∀ i < c.L, ∃ p ≤ i, c.a (i + 1) = c.a i + c.a p

/-- Every element of a chain is positive. -/
theorem one_le_a (c : NatChain) : ∀ i, i ≤ c.L → 1 ≤ c.a i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    match i with
    | 0 => rw [c.h0]
    | k + 1 =>
      obtain ⟨p, q, hp, hq, heq⟩ := c.step k (by omega)
      rw [heq]
      have hp' := ih p (by omega) (by omega)
      omega


end NatChain

/-! ## The two complexity functions -/

/-- The set of lengths of addition chains computing `n`. -/
def NatChainSet (n : ℕ) : Set ℕ := {l | ∃ c : NatChain, c.L = l ∧ c.a c.L = n}

/-- The set of lengths of *linear* addition chains computing `n`. -/
def NatChainLinSet (n : ℕ) : Set ℕ :=
  {l | ∃ c : NatChain, c.IsLinear ∧ c.L = l ∧ c.a c.L = n}

/-- `L(n)`: the length of a shortest addition chain for `n` (and `0` if there is none, i.e. for
`n = 0`). -/
noncomputable def natL (n : ℕ) : ℕ := sInf (NatChainSet n)

/-- `L⁰(n)`: the length of a shortest *linear* addition chain for `n`. -/
noncomputable def natL0 (n : ℕ) : ℕ := sInf (NatChainLinSet n)

/-- The chain `1, 2, …, n` of length `n - 1` (all steps are increments by `1 = a 0`). -/
def incChain (n : ℕ) (hn : 1 ≤ n) : NatChain where
  L := n - 1
  a := fun i => min (i + 1) n
  h0 := by simp [Nat.min_eq_left hn]
  step := by
    intro i hi
    have h1 : i + 1 ≤ n := by omega
    have h2 : i + 1 + 1 ≤ n := by omega
    refine ⟨i, 0, le_rfl, Nat.zero_le _, ?_⟩
    simp only [Nat.min_eq_left h1, Nat.min_eq_left h2, Nat.min_eq_left hn]

theorem incChain_last (n : ℕ) (hn : 1 ≤ n) : (incChain n hn).a (incChain n hn).L = n := by
  simp only [incChain]
  exact Nat.min_eq_right (by omega)

theorem incChain_linear (n : ℕ) (hn : 1 ≤ n) : (incChain n hn).IsLinear := by
  intro i hi
  have h1 : i + 1 ≤ n := by simp [incChain] at hi; omega
  have h2 : i + 1 + 1 ≤ n := by simp [incChain] at hi; omega
  refine ⟨0, Nat.zero_le _, ?_⟩
  simp only [incChain, Nat.min_eq_left h1, Nat.min_eq_left h2, Nat.min_eq_left hn]

theorem NatChainSet_nonempty {n : ℕ} (hn : 1 ≤ n) : (NatChainSet n).Nonempty :=
  ⟨n - 1, incChain n hn, rfl, incChain_last n hn⟩

theorem NatChainLinSet_nonempty {n : ℕ} (hn : 1 ≤ n) : (NatChainLinSet n).Nonempty :=
  ⟨n - 1, incChain n hn, incChain_linear n hn, rfl, incChain_last n hn⟩


theorem natL0_le {n : ℕ} (hn : 1 ≤ n) : natL0 n ≤ n - 1 :=
  Nat.sInf_le ⟨incChain n hn, incChain_linear n hn, rfl, incChain_last n hn⟩


theorem NatChainSet_zero : NatChainSet 0 = ∅ := by
  ext l
  simp only [NatChainSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists,
    not_and]
  intro c _ hval
  have := c.one_le_a c.L le_rfl
  omega


/-- `L(0) = 0`: the infimum of the empty set of chain lengths. -/
theorem natL_zero : natL 0 = 0 := by
  rw [natL, NatChainSet_zero, Nat.sInf_empty]



/-! ## Constructions on chains -/

namespace NatChain

/-- The trivial chain `1` of length `0`. -/
def oneChain : NatChain where
  L := 0
  a := fun _ => 1
  h0 := rfl
  step := by intro i hi; omega

@[simp] theorem oneChain_L : oneChain.L = 0 := rfl

@[simp] theorem oneChain_a (i : ℕ) : oneChain.a i = 1 := rfl

theorem oneChain_isLinear : oneChain.IsLinear := by
  intro i hi
  exact absurd hi (by simp)

/-- Doubling the last element: if `c` ends with `v`, then `c.dbl` ends with `2v`. -/
def dbl (c : NatChain) : NatChain :=
  { L := c.L + 1
    a := fun i => if i ≤ c.L then c.a i else 2 * c.a c.L
    h0 := by
      simp only [Nat.zero_le, if_pos]
      exact c.h0
    step := by
      intro i hi
      rcases lt_or_ge i c.L with hlt | hge
      · obtain ⟨p, q, hp, hq, heq⟩ := c.step i hlt
        refine ⟨p, q, hp, hq, ?_⟩
        have h1 : i + 1 ≤ c.L := by omega
        have hp' : p ≤ c.L := by omega
        have hq' : q ≤ c.L := by omega
        simp only [if_pos h1, if_pos hp', if_pos hq', heq]
      · have hieq : i = c.L := by omega
        subst hieq
        refine ⟨c.L, c.L, le_rfl, le_rfl, ?_⟩
        simp only [if_neg (show ¬ c.L + 1 ≤ c.L by omega), if_pos le_rfl]
        ring }

theorem dbl_apply (c : NatChain) (i : ℕ) :
    c.dbl.a i = if i ≤ c.L then c.a i else 2 * c.a c.L := rfl

theorem dbl_apply_of_le (c : NatChain) {i : ℕ} (h : i ≤ c.L) : c.dbl.a i = c.a i := by
  rw [dbl_apply, if_pos h]

theorem dbl_apply_of_lt (c : NatChain) {i : ℕ} (h : c.L < i) : c.dbl.a i = 2 * c.a c.L := by
  rw [dbl_apply, if_neg (by omega)]

theorem dbl_L (c : NatChain) : c.dbl.L = c.L + 1 := rfl

theorem dbl_last (c : NatChain) : c.dbl.a (c.L + 1) = 2 * c.a c.L := by
  rw [dbl_apply, if_neg (by omega)]

theorem dbl_isLinear (c : NatChain) (hc : c.IsLinear) : c.dbl.IsLinear := by
  intro i hi
  have hiL : i ≤ c.L := by rw [dbl_L] at hi; omega
  rcases lt_or_eq_of_le hiL with hlt | heq
  · obtain ⟨p, hp, heq'⟩ := hc i hlt
    refine ⟨p, hp, ?_⟩
    have h1 : i + 1 ≤ c.L := by omega
    have hp' : p ≤ c.L := by omega
    rw [dbl_apply_of_le c h1, dbl_apply_of_le c hiL, dbl_apply_of_le c hp', heq']
  · subst heq
    refine ⟨c.L, le_rfl, ?_⟩
    rw [dbl_last, dbl_apply_of_le c le_rfl]
    ring

/-- Append the element `c.a c.L + c.a p` to the chain. -/
def addLast (c : NatChain) (p : ℕ) (hp : p ≤ c.L) : NatChain :=
  { L := c.L + 1
    a := fun i => if i ≤ c.L then c.a i else c.a c.L + c.a p
    h0 := by
      simp only [Nat.zero_le, if_pos]
      exact c.h0
    step := by
      intro i hi
      rcases lt_or_ge i c.L with hlt | hge
      · obtain ⟨p', q', hp', hq', heq⟩ := c.step i hlt
        refine ⟨p', q', hp', hq', ?_⟩
        have h1 : i + 1 ≤ c.L := by omega
        have hp2 : p' ≤ c.L := by omega
        have hq2 : q' ≤ c.L := by omega
        simp only [if_pos h1, if_pos hp2, if_pos hq2, heq]
      · have hieq : i = c.L := by omega
        subst hieq
        refine ⟨c.L, p, le_rfl, hp, ?_⟩
        simp only [if_neg (show ¬ c.L + 1 ≤ c.L by omega), if_pos le_rfl, if_pos hp] }

theorem addLast_apply (c : NatChain) (p : ℕ) (hp : p ≤ c.L) (i : ℕ) :
    (c.addLast p hp).a i = if i ≤ c.L then c.a i else c.a c.L + c.a p := rfl

theorem addLast_apply_of_le (c : NatChain) (p : ℕ) (hp : p ≤ c.L) {i : ℕ} (h : i ≤ c.L) :
    (c.addLast p hp).a i = c.a i := by
  rw [addLast_apply, if_pos h]

theorem addLast_apply_of_lt (c : NatChain) (p : ℕ) (hp : p ≤ c.L) {i : ℕ} (h : c.L < i) :
    (c.addLast p hp).a i = c.a c.L + c.a p := by
  rw [addLast_apply, if_neg (by omega)]

theorem addLast_L (c : NatChain) (p : ℕ) (hp : p ≤ c.L) : (c.addLast p hp).L = c.L + 1 := rfl

theorem addLast_last (c : NatChain) (p : ℕ) (hp : p ≤ c.L) :
    (c.addLast p hp).a (c.L + 1) = c.a c.L + c.a p := by
  rw [addLast_apply_of_lt c p hp (by omega)]

theorem addLast_isLinear (c : NatChain) (p : ℕ) (hp : p ≤ c.L) (hc : c.IsLinear) :
    (c.addLast p hp).IsLinear := by
  intro i hi
  have hiL : i ≤ c.L := by rw [addLast_L] at hi; omega
  rcases lt_or_eq_of_le hiL with hlt | heq
  · obtain ⟨p', hp', heq'⟩ := hc i hlt
    refine ⟨p', hp', ?_⟩
    have h1 : i + 1 ≤ c.L := by omega
    have hp'' : p' ≤ c.L := by omega
    rw [addLast_apply_of_le c p hp h1, addLast_apply_of_le c p hp hiL,
      addLast_apply_of_le c p hp hp'', heq']
  · subst heq
    refine ⟨p, hp, ?_⟩
    rw [addLast_last, addLast_apply_of_le c p hp le_rfl, addLast_apply_of_le c p hp hp]

/-- `t` successive doublings of the last element: if `c` ends with `v`, then `c.dblN t` ends with
`2^t v`. -/
def dblN (c : NatChain) : ℕ → NatChain
  | 0 => c
  | t + 1 => (dblN c t).dbl

@[simp] theorem dblN_zero (c : NatChain) : c.dblN 0 = c := rfl

theorem dblN_succ (c : NatChain) (t : ℕ) : c.dblN (t + 1) = (c.dblN t).dbl := rfl

theorem dblN_L (c : NatChain) (t : ℕ) : (c.dblN t).L = c.L + t := by
  induction t with
  | zero => simp
  | succ t ih => rw [dblN_succ, dbl_L, ih]; omega

theorem dblN_apply_of_le (c : NatChain) (t : ℕ) {i : ℕ} (h : i ≤ c.L) :
    (c.dblN t).a i = c.a i := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [dblN_succ, dbl_apply_of_le _ (by rw [dblN_L]; omega), ih]

theorem dblN_last (c : NatChain) (t : ℕ) :
    (c.dblN t).a (c.L + t) = 2 ^ t * c.a c.L := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hLt : (c.dblN t).L = c.L + t := dblN_L c t
    rw [dblN_succ, dbl_apply_of_lt _ (i := c.L + (t + 1)) (by rw [hLt]; omega), hLt, ih,
      pow_succ]
    ring

end NatChain

/-! ## Lemma 4: the binary (Horner) method -/

/-- The binary weight `ν(n)`: the number of `1`s in the binary expansion of `n`. -/
def nu (n : ℕ) : ℕ := (Nat.bits n).countP id

@[simp] theorem nu_zero : nu 0 = 0 := by simp [nu]

@[simp] theorem nu_one : nu 1 = 1 := by simp [nu]

/-- Doubling does not change the binary weight. -/
theorem nu_two_mul {n : ℕ} (hn : n ≠ 0) : nu (2 * n) = nu n := by
  simp [nu, Nat.bit0_bits n hn]

/-- Doubling and adding one increases the binary weight by one. -/
theorem nu_two_mul_add_one (n : ℕ) : nu (2 * n + 1) = nu n + 1 := by
  simp [nu, Nat.bit1_bits n]

/-- Powers of two have binary weight one. -/
theorem nu_two_pow (k : ℕ) : nu (2 ^ k) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ]
    have h : 2 ^ k ≠ 0 := by positivity
    rw [Nat.mul_comm, nu_two_mul h, ih]


theorem log_two_mul {m : ℕ} (hm : m ≠ 0) : Nat.log 2 (2 * m) = Nat.log 2 m + 1 := by
  rw [Nat.mul_comm 2 m, Nat.log_mul_base (by norm_num) hm]

theorem log_two_mul_add_one {m : ℕ} (hm : m ≠ 0) :
    Nat.log 2 (2 * m + 1) = Nat.log 2 m + 1 :=
  Nat.log_two_bit (n := m) (b := true) hm

/-- The binary weight is at most the binary length: `ν(n) ≤ log₂ n + 1`. -/
theorem nu_le_log_add_one (n : ℕ) (hn : 1 ≤ n) : nu n ≤ Nat.log 2 n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      simp
    · rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · have hn2 : n = 2 * m := by omega
        subst hn2
        have hm1 : 1 ≤ m := by omega
        have hlt : m < 2 * m := by omega
        rw [log_two_mul (by omega), nu_two_mul (by omega)]
        have := ih m hlt hm1
        omega
      · have hn2 : n = 2 * m + 1 := by omega
        subst hn2
        have hm1 : 1 ≤ m := by omega
        have hlt : m < 2 * m + 1 := by omega
        rw [log_two_mul_add_one (by omega), nu_two_mul_add_one]
        have := ih m hlt hm1
        omega

/-- The binary (Horner) method, in the sharp additive form: for `n ≥ 1` there is a linear chain
`c` for `n` with `c.L + 1 ≤ log₂ n + ν(n)`. -/
theorem exists_linear_chain (n : ℕ) (hn : 1 ≤ n) :
    ∃ c : NatChain, c.IsLinear ∧ c.a c.L = n ∧ c.L + 1 ≤ Nat.log 2 n + nu n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      exact ⟨NatChain.oneChain, NatChain.oneChain_isLinear, rfl, by simp⟩
    · rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · have hn2 : n = 2 * m := by omega
        subst hn2
        have hm1 : 1 ≤ m := by omega
        have hlt : m < 2 * m := by omega
        obtain ⟨c, hlin, hval, hlen⟩ := ih m hlt hm1
        have hd : c.dbl.a c.dbl.L = 2 * m := by
          rw [NatChain.dbl_L, NatChain.dbl_last, hval]
        refine ⟨c.dbl, c.dbl_isLinear hlin, hd, ?_⟩
        rw [NatChain.dbl_L, log_two_mul (by omega), nu_two_mul (by omega)]
        omega
      · have hn2 : n = 2 * m + 1 := by omega
        subst hn2
        have hm1 : 1 ≤ m := by omega
        have hlt : m < 2 * m + 1 := by omega
        obtain ⟨c, hlin, hval, hlen⟩ := ih m hlt hm1
        have hd : c.dbl.a c.dbl.L = 2 * m := by
          rw [NatChain.dbl_L, NatChain.dbl_last, hval]
        have h0 : c.dbl.a 0 = 1 := by
          rw [NatChain.dbl_apply_of_le c (Nat.zero_le _), c.h0]
        refine ⟨c.dbl.addLast 0 (Nat.zero_le _), ?_, ?_, ?_⟩
        · exact NatChain.addLast_isLinear c.dbl 0 (Nat.zero_le _)
            (NatChain.dbl_isLinear c hlin)
        · rw [NatChain.addLast_L, NatChain.addLast_last, hd, h0]
        · rw [NatChain.addLast_L, NatChain.dbl_L, log_two_mul_add_one (by omega),
            nu_two_mul_add_one]
          omega

/-- **Lemma 4**, first inequality: `L⁰(n) ≤ log₂ n + ν(n) - 1`, in the sharp additive form
`L⁰(n) + 1 ≤ log₂ n + ν(n)`. -/
theorem natL0_add_one_le {n : ℕ} (hn : 1 ≤ n) : natL0 n + 1 ≤ Nat.log 2 n + nu n := by
  obtain ⟨c, hlin, hval, hlen⟩ := exists_linear_chain n hn
  have hmem : c.L ∈ NatChainLinSet n := ⟨c, hlin, rfl, hval⟩
  have h : natL0 n ≤ c.L := Nat.sInf_le hmem
  omega


/-- `log₂` is bounded by the real logarithm: `Nat.log 2 n ≤ logb 2 n`. -/
theorem log_le_logb (n : ℕ) (hn : 1 ≤ n) : ((Nat.log 2 n : ℕ) : ℝ) ≤ Real.logb 2 n := by
  have hnat : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
  have hreal : ((2 : ℝ) ^ Nat.log 2 n) ≤ (n : ℝ) := by
    have : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnat
    simpa using this
  have hk : ((Nat.log 2 n : ℕ) : ℝ) = Real.logb 2 ((2 : ℝ) ^ Nat.log 2 n) := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  rw [hk]
  exact (Real.logb_le_logb (by norm_num : (1 : ℝ) < 2) (by positivity)
    (by positivity)).mpr hreal

/-- If `n` is not a power of two, then `Nat.log 2 n < logb 2 n` strictly. -/
theorem log_lt_logb_of_ne (n : ℕ) (hn0 : n ≠ 0) (hn : n ≠ 2 ^ Nat.log 2 n) :
    ((Nat.log 2 n : ℕ) : ℝ) < Real.logb 2 n := by
  have hnat : 2 ^ Nat.log 2 n < n :=
    lt_of_le_of_ne (Nat.pow_log_le_self 2 hn0) (Ne.symm hn)
  have hreal : ((2 : ℝ) ^ Nat.log 2 n) < (n : ℝ) := by
    have : ((2 ^ Nat.log 2 n : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast hnat
    simpa using this
  have hk : ((Nat.log 2 n : ℕ) : ℝ) = Real.logb 2 ((2 : ℝ) ^ Nat.log 2 n) := by
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]
  rw [hk]
  exact Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2) (by positivity) hreal

/-- **Lemma 4** (binary method).  For `n ≥ 2`, `L⁰(n) < 2 log₂ n` (with the real logarithm). -/
theorem lemma4 {n : ℕ} (hn : 2 ≤ n) : (natL0 n : ℝ) < 2 * Real.logb 2 n := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : n ≠ 0 := by omega
  have hk : 1 ≤ Nat.log 2 n := Nat.log_pos_iff.mpr ⟨hn, by norm_num⟩
  have hmain : natL0 n + 1 ≤ Nat.log 2 n + nu n := natL0_add_one_le hn1
  have hν : nu n ≤ Nat.log 2 n + 1 := nu_le_log_add_one n hn1
  have hle : ((Nat.log 2 n : ℕ) : ℝ) ≤ Real.logb 2 n := log_le_logb n hn1
  rcases Nat.lt_or_ge (nu n) (Nat.log 2 n + 1) with hlt | hge
  · have h1 : natL0 n < 2 * Nat.log 2 n := by omega
    have h2 : (natL0 n : ℝ) < ((2 * Nat.log 2 n : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 : ((2 * Nat.log 2 n : ℕ) : ℝ) ≤ 2 * Real.logb 2 n := by push_cast; linarith
    linarith
  · have hνeq : nu n = Nat.log 2 n + 1 := le_antisymm hν hge
    have hne : n ≠ 2 ^ Nat.log 2 n := by
      intro h
      have : nu n = 1 := by rw [h, nu_two_pow]
      omega
    have h1 : natL0 n ≤ 2 * Nat.log 2 n := by omega
    have h2 : (natL0 n : ℝ) ≤ ((2 * Nat.log 2 n : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 : ((Nat.log 2 n : ℕ) : ℝ) < Real.logb 2 n := log_lt_logb_of_ne n hn0 hne
    have h4 : ((2 * Nat.log 2 n : ℕ) : ℝ) < 2 * Real.logb 2 n := by push_cast; linarith
    linarith

/-! ## Lemma 7: the Brauer bound -/

theorem pow_sub_one_arith (A T : ℕ) (hA : 1 ≤ A) (hT : 1 ≤ T) :
    T * (A - 1) + (T - 1) = T * A - 1 := by
  have h1 : T * (A - 1) = T * A - T := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have h2 : T ≤ T * A := by
    calc T = T * 1 := (Nat.mul_one T).symm
      _ ≤ T * A := Nat.mul_le_mul_left T hA
  omega

namespace Brauer

variable (c : NatChain) (hlin : c.IsLinear)

noncomputable def pfun (k : ℕ) : ℕ :=
  if h : k < c.L then Classical.choose (hlin k h) else 0

theorem pfun_le {k : ℕ} (hk : k < c.L) : pfun c hlin k ≤ k := by
  unfold pfun
  rw [dif_pos hk]
  exact (Classical.choose_spec (hlin k hk)).1

theorem pfun_eq {k : ℕ} (hk : k < c.L) : c.a (k + 1) = c.a k + c.a (pfun c hlin k) := by
  unfold pfun
  rw [dif_pos hk]
  exact (Classical.choose_spec (hlin k hk)).2

noncomputable def Bpos : ℕ → ℕ
  | 0 => 0
  | k + 1 => Bpos k + c.a (pfun c hlin k) + 1

theorem Bpos_succ (k : ℕ) : Bpos c hlin (k + 1) = Bpos c hlin k + c.a (pfun c hlin k) + 1 :=
  rfl

theorem Bpos_mono : ∀ {i j : ℕ}, i ≤ j → Bpos c hlin i ≤ Bpos c hlin j := by
  intro i j h
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst this; exact le_rfl
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with hlt | hge
    · exact le_trans (ih (by omega)) (by rw [Bpos_succ]; omega)
    · have : i = j + 1 := by omega
      subst this; exact le_rfl

theorem Bpos_spec : ∀ k, k ≤ c.L → Bpos c hlin k = c.a k - 1 + k := by
  intro k
  induction k with
  | zero => intro _; simp [Bpos, c.h0]
  | succ k ih =>
    intro hk
    have hkL : k < c.L := by omega
    have hple := pfun_le c hlin hkL
    have hpeq := pfun_eq c hlin hkL
    have h1 : 1 ≤ c.a k := c.one_le_a k (by omega)
    rw [Bpos_succ, ih (by omega), hpeq]
    omega

structure Carry (k : ℕ) where
  ch : NatChain
  hL : ch.L = Bpos c hlin k
  hval : ∀ i, i ≤ k → ch.a (Bpos c hlin i) = 2 ^ c.a i - 1

noncomputable def bstep {k : ℕ} (hk : k < c.L) (s : Carry c hlin k) : Carry c hlin (k + 1) := by
  classical
  refine
    { ch := (s.ch.dblN (c.a (pfun c hlin k))).addLast (Bpos c hlin (pfun c hlin k)) ?_
      hL := ?_
      hval := ?_ }
  · rw [NatChain.dblN_L, s.hL]
    exact le_trans (Bpos_mono c hlin (pfun_le c hlin hk)) (Nat.le_add_right _ _)
  · rw [NatChain.addLast_L, NatChain.dblN_L, s.hL, Bpos_succ]
  · intro i hi
    rcases Nat.lt_or_ge i (k + 1) with hlt | hge
    · have hik : i ≤ k := by omega
      have h1 : Bpos c hlin i ≤ (s.ch.dblN (c.a (pfun c hlin k))).L := by
        rw [NatChain.dblN_L, s.hL]
        exact le_trans (Bpos_mono c hlin hik) (Nat.le_add_right _ _)
      have h2 : Bpos c hlin i ≤ s.ch.L := by
        rw [s.hL]
        exact Bpos_mono c hlin hik
      rw [NatChain.addLast_apply_of_le _ _ _ h1, NatChain.dblN_apply_of_le _ _ h2]
      exact s.hval i hik
    · have hik : i = k + 1 := by omega
      subst hik
      have hlast : Bpos c hlin (k + 1) = (s.ch.dblN (c.a (pfun c hlin k))).L + 1 := by
        rw [NatChain.dblN_L, s.hL, Bpos_succ]
      rw [hlast, NatChain.addLast_last]
      have h5 : (s.ch.dblN (c.a (pfun c hlin k))).a (s.ch.dblN (c.a (pfun c hlin k))).L
          = 2 ^ c.a (pfun c hlin k) * (2 ^ c.a k - 1) := by
        rw [show (s.ch.dblN (c.a (pfun c hlin k))).L = s.ch.L + c.a (pfun c hlin k) from
            NatChain.dblN_L s.ch (c.a (pfun c hlin k)),
          NatChain.dblN_last,
          show s.ch.a s.ch.L = s.ch.a (Bpos c hlin k) from by rw [s.hL], s.hval k le_rfl]
      have h6 : (s.ch.dblN (c.a (pfun c hlin k))).a (Bpos c hlin (pfun c hlin k))
          = 2 ^ c.a (pfun c hlin k) - 1 := by
        rw [NatChain.dblN_apply_of_le _ _ (by rw [s.hL]; exact Bpos_mono c hlin (pfun_le c hlin hk)),
          s.hval (pfun c hlin k) (pfun_le c hlin hk)]
      rw [h5, h6, pfun_eq c hlin hk, pow_add,
        Nat.mul_comm (2 ^ c.a k) (2 ^ c.a (pfun c hlin k))]
      exact pow_sub_one_arith (2 ^ c.a k) (2 ^ c.a (pfun c hlin k))
        (Nat.one_le_two_pow) (Nat.one_le_two_pow)

noncomputable def build : (k : ℕ) → k ≤ c.L → Carry c hlin k
  | 0, _ =>
    { ch := NatChain.oneChain
      hL := by simp [Bpos]
      hval := by
        intro i hi
        have hi0 : i = 0 := by omega
        subst hi0
        simp [Bpos, c.h0] }
  | k + 1, hk => bstep c hlin (by omega) (build k (by omega))

end Brauer

noncomputable def brauerChain (c : NatChain) (hlin : c.IsLinear) : NatChain :=
  (Brauer.build c hlin c.L le_rfl).ch

theorem brauerChain_L (c : NatChain) (hlin : c.IsLinear) :
    (brauerChain c hlin).L = c.a c.L - 1 + c.L := by
  rw [brauerChain, (Brauer.build c hlin c.L le_rfl).hL, Brauer.Bpos_spec c hlin c.L le_rfl]

theorem brauerChain_val (c : NatChain) (hlin : c.IsLinear) :
    (brauerChain c hlin).a (brauerChain c hlin).L = 2 ^ c.a c.L - 1 := by
  rw [brauerChain, (Brauer.build c hlin c.L le_rfl).hL,
    (Brauer.build c hlin c.L le_rfl).hval c.L le_rfl]

/-- **Lemma 7** (Brauer).  `L(2^n - 1) ≤ n - 1 + L⁰(n)`. -/
theorem lemma7 (n : ℕ) : natL (2 ^ n - 1) ≤ n - 1 + natL0 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pow_zero, Nat.sub_self, Nat.zero_sub, natL_zero]
    exact Nat.zero_le _
  · obtain ⟨c, hlin, hL, hval⟩ := Nat.sInf_mem (NatChainLinSet_nonempty hn)
    have hmem : (brauerChain c hlin).L ∈ NatChainSet (2 ^ n - 1) := by
      refine ⟨brauerChain c hlin, rfl, ?_⟩
      rw [brauerChain_val, hval]
    calc natL (2 ^ n - 1) ≤ (brauerChain c hlin).L := Nat.sInf_le hmem
      _ = c.a c.L - 1 + c.L := brauerChain_L c hlin
      _ = n - 1 + natL0 n := by rw [hval, hL]; rfl

/-! ## The value of the linear complexity at `1` -/

/-- `L⁰(1) = 0`. -/
theorem natL0_one : natL0 1 = 0 := by
  have h := natL0_le (n := 1) le_rfl
  omega

/-! ## 0-chains in the basis of powers of two -/

open scoped BigOperators

/-! ## Coefficient vectors and their values -/

/-- Coefficient vectors over the basis of powers of two: the coefficient of `2^i` is the `i`-th
entry. -/
abbrev Coef (n : ℕ) := Fin n → ℕ

/-- The basis vector `eᵢ`: the coefficient vector of the free number `2^i`. -/
def basisCoef {n : ℕ} (i : Fin n) : Coef n := fun j => if j = i then 1 else 0

/-- The number `∑ i, v i * 2^i` represented by a coefficient vector. -/
def eval {n : ℕ} (v : Coef n) : ℕ := ∑ i, v i * 2 ^ (i : ℕ)

theorem eval_add {n : ℕ} (u v : Coef n) : eval (u + v) = eval u + eval v := by
  simp only [eval, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem eval_zero {n : ℕ} : eval (0 : Coef n) = 0 := by simp [eval]

theorem eval_basisCoef {n : ℕ} (i : Fin n) : eval (basisCoef i) = 2 ^ (i : ℕ) := by
  simp [eval, basisCoef]

/-- Adding a free power of two: `eval (v + eᵢ) = eval v + 2^i`. -/
theorem eval_add_basisCoef {n : ℕ} (v : Coef n) (i : Fin n) :
    eval (v + basisCoef i) = eval v + 2 ^ (i : ℕ) := by
  rw [eval_add, eval_basisCoef]

/-- The values available at step `k` of a 0-chain: the free powers of two `2^i` with `i < n`,
together with the values `a j` of the chain for `j < k`. -/
def zPool {n : ℕ} (a : ℕ → Coef n) (k : ℕ) : Fin n ⊕ Fin k → Coef n
  | Sum.inl i => basisCoef i
  | Sum.inr j => a j.1

/-- The pool only depends on the values at indices below `k`. -/
theorem zPool_congr {n : ℕ} {a b : ℕ → Coef n} {k : ℕ} (h : ∀ j < k, a j = b j)
    (x : Fin n ⊕ Fin k) : zPool a k x = zPool b k x := by
  rcases x with i | j
  · rfl
  · exact h j.1 j.2

/-- The value of a pool element: a free power of two or the value of an earlier element. -/
theorem eval_zPool {n : ℕ} {a : ℕ → Coef n} {k : ℕ} (x : Fin n ⊕ Fin k) :
    eval (zPool a k x) = Sum.elim (fun i : Fin n => 2 ^ (i : ℕ)) (fun j => eval (a j.1)) x := by
  rcases x with i | j
  · exact eval_basisCoef i
  · rfl

/-! ## 0-chains -/

/-- A 0-chain over the free basis `1, 2, …, 2^(n-1)`: a sequence of coefficient vectors in which
every element is the sum of two available values (a free power of two or an earlier element),
together with a designated output value located in the pool at the last step.  The values `a k`
for `k ≥ L` are irrelevant junk. -/
structure StarChain (n : ℕ) where
  /-- the length of the chain, i.e. the number of additions -/
  L : ℕ
  /-- the values computed by the chain -/
  a : ℕ → Coef n
  /-- every value is the sum of two available values -/
  valid : ∀ k < L, ∃ x y : Fin n ⊕ Fin k, a k = zPool a k x + zPool a k y
  /-- the designated output value -/
  val : Coef n
  /-- the position of the output value in the pool at the last step -/
  src : Fin n ⊕ Fin L
  /-- the designated position indeed carries the output value -/
  hsrc : zPool a L src = val

namespace StarChain

variable {n : ℕ}

/-- The number computed by the chain. -/
def value (c : StarChain n) : ℕ := eval c.val

/-- The chain `1`, of length zero, with output the free value `2^0 = 1`. -/
def base (hn : 0 < n) : StarChain n where
  L := 0
  a := fun _ => 0
  valid := fun k hk => absurd hk (Nat.not_lt_zero k)
  val := basisCoef ⟨0, hn⟩
  src := Sum.inl ⟨0, hn⟩
  hsrc := rfl

@[simp] theorem base_L (hn : 0 < n) : (base hn).L = 0 := rfl

@[simp] theorem base_val (hn : 0 < n) : (base hn).val = basisCoef ⟨0, hn⟩ := rfl

theorem base_value (hn : 0 < n) : (base hn).value = 1 := by
  rw [value, base_val, eval_basisCoef, pow_zero]

/-- Append to a 0-chain the sum of two available values, given by their pool positions. -/
def append (c : StarChain n) (x y : Fin n ⊕ Fin c.L) : StarChain n where
  L := c.L + 1
  a := fun k => if k < c.L then c.a k else zPool c.a c.L x + zPool c.a c.L y
  valid := by
    intro k hk
    by_cases h : k < c.L
    · obtain ⟨u, v, huv⟩ := c.valid k h
      have key : ∀ z : Fin n ⊕ Fin k,
          zPool (fun k => if k < c.L then c.a k else zPool c.a c.L x + zPool c.a c.L y) k z
            = zPool c.a k z :=
        fun z => zPool_congr (fun j hj => if_pos (hj.trans h)) z
      refine ⟨u, v, ?_⟩
      show (if k < c.L then c.a k else zPool c.a c.L x + zPool c.a c.L y) = _
      rw [if_pos h, huv]
      rw [key u, key v]
    · have hk' : k = c.L := by omega
      subst hk'
      have key : ∀ z : Fin n ⊕ Fin c.L,
          zPool (fun k => if k < c.L then c.a k else zPool c.a c.L x + zPool c.a c.L y) c.L z
            = zPool c.a c.L z :=
        fun z => zPool_congr (fun j hj => if_pos hj) z
      refine ⟨x, y, ?_⟩
      show (if c.L < c.L then c.a c.L else zPool c.a c.L x + zPool c.a c.L y) = _
      rw [if_neg (Nat.lt_irrefl c.L), key x, key y]
  val := zPool c.a c.L x + zPool c.a c.L y
  src := Sum.inr ⟨c.L, by omega⟩
  hsrc := by
    show (if c.L < c.L then c.a c.L else zPool c.a c.L x + zPool c.a c.L y) = _
    rw [if_neg (Nat.lt_irrefl c.L)]

theorem append_L (c : StarChain n) (x y : Fin n ⊕ Fin c.L) : (c.append x y).L = c.L + 1 := rfl

theorem append_a_of_lt (c : StarChain n) (x y : Fin n ⊕ Fin c.L) {k : ℕ} (h : k < c.L) :
    (c.append x y).a k = c.a k := by
  show (if k < c.L then c.a k else _) = c.a k
  rw [if_pos h]

theorem append_a_last (c : StarChain n) (x y : Fin n ⊕ Fin c.L) :
    (c.append x y).a c.L = zPool c.a c.L x + zPool c.a c.L y := by
  show (if c.L < c.L then c.a c.L else _) = _
  rw [if_neg (Nat.lt_irrefl c.L)]

theorem append_value (c : StarChain n) (x y : Fin n ⊕ Fin c.L) :
    (c.append x y).value = eval (zPool c.a c.L x) + eval (zPool c.a c.L y) := by
  simp only [value, append, eval_add]

/-- Append one addition of an available value to the output. -/
def addVal (c : StarChain n) (x : Fin n ⊕ Fin c.L) : StarChain n := c.append c.src x

theorem addVal_value (c : StarChain n) (x : Fin n ⊕ Fin c.L) :
    (c.addVal x).value = c.value + eval (zPool c.a c.L x) := by
  rw [addVal, append_value, value, c.hsrc]

theorem addVal_L (c : StarChain n) (x : Fin n ⊕ Fin c.L) : (c.addVal x).L = c.L + 1 := rfl

/-- Append one addition of the free power of two `2^i`. -/
def addFree (c : StarChain n) (i : Fin n) : StarChain n := c.addVal (Sum.inl i)

theorem addFree_value (c : StarChain n) (i : Fin n) :
    (c.addFree i).value = c.value + 2 ^ (i : ℕ) := by
  rw [addFree, addVal_value, eval_zPool]
  rfl

theorem addFree_L (c : StarChain n) (i : Fin n) : (c.addFree i).L = c.L + 1 := rfl

/-- Append `t` additions of free powers of two, given by `f : Fin t → Fin n`. -/
def addFreeAll (c : StarChain n) : (t : ℕ) → (Fin t → Fin n) → StarChain n
  | 0, _ => c
  | t + 1, f => (addFreeAll c t (fun i => f i.castSucc)).addFree (f (Fin.last t))

@[simp] theorem addFreeAll_zero (c : StarChain n) (f : Fin 0 → Fin n) :
    c.addFreeAll 0 f = c := rfl

theorem addFreeAll_L (c : StarChain n) : ∀ (t : ℕ) (f : Fin t → Fin n),
    (c.addFreeAll t f).L = c.L + t
  | 0, f => by simp
  | t + 1, f => by
    rw [addFreeAll, addFree_L, addFreeAll_L, Nat.add_assoc]

theorem addFreeAll_value (c : StarChain n) : ∀ (t : ℕ) (f : Fin t → Fin n),
    (c.addFreeAll t f).value = c.value + ∑ i : Fin t, 2 ^ (f i : ℕ)
  | 0, f => by simp
  | t + 1, f => by
    rw [addFreeAll, addFree_value, addFreeAll_value, Fin.sum_univ_castSucc, Nat.add_assoc]

end StarChain

/-- `L∗(m)`: the length of a shortest 0-chain computing `m`, minimized over all choices of the
free basis of powers of two. -/
noncomputable def starComplexity (m : ℕ) : ℕ :=
  sInf { l | ∃ (n : ℕ) (c : StarChain n), c.L = l ∧ c.value = m }

/-- A 0-chain of length `L` computing `m` bounds `L∗(m)` by `L`. -/
theorem starComplexity_le {m n : ℕ} (c : StarChain n) (h : c.value = m) :
    starComplexity m ≤ c.L :=
  Nat.sInf_le ⟨n, c, rfl, h⟩

/-! ## Binary weight: bounds used in the proofs -/

/-- A nonzero number has binary weight at least one. -/
theorem nu_pos {n : ℕ} (hn : n ≠ 0) : 1 ≤ nu n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · have hn1 : n = 1 := by omega
      subst hn1; simp
    · rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · have hn2 : n = 2 * m := by omega
        subst hn2
        rw [nu_two_mul (by omega)]
        exact ih m (by omega) (by omega)
      · have hn2 : n = 2 * m + 1 := by omega
        subst hn2
        rw [nu_two_mul_add_one]
        omega

/-- Numbers below `2 ^ m` have binary weight at most `m`. -/
theorem nu_le_of_le : ∀ (m z : ℕ), z ≤ 2 ^ m - 1 → nu z ≤ m := by
  intro m
  induction m with
  | zero =>
    intro z hz
    have hz0 : z = 0 := by simp at hz; omega
    subst hz0
    simp
  | succ m ih =>
    intro z hz
    rcases Nat.even_or_odd z with ⟨u, hu⟩ | ⟨u, hu⟩
    · have hz2 : z = 2 * u := by omega
      subst hz2
      rcases Nat.eq_zero_or_pos u with rfl | hu0
      · simp
      · rw [nu_two_mul (by omega)]
        have hu : u ≤ 2 ^ m - 1 := by
          rw [Nat.pow_succ] at hz
          omega
        have := ih u hu
        omega
    · have hz2 : z = 2 * u + 1 := by omega
      subst hz2
      rw [nu_two_mul_add_one]
      have hu : u ≤ 2 ^ m - 1 := by
        rw [Nat.pow_succ] at hz
        omega
      have := ih u hu
      omega

/-- Adding one increases the binary weight by at most one. -/
theorem nu_succ_le (x : ℕ) : nu (x + 1) ≤ nu x + 1 := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.even_or_odd x with ⟨a, ha⟩ | ⟨a, ha⟩
    · have hx : x = 2 * a := by omega
      subst hx
      rcases Nat.eq_zero_or_pos a with rfl | ha0
      · simp
      · rw [show 2 * a + 1 = 2 * a + 1 from rfl, nu_two_mul_add_one, nu_two_mul (by omega)]
    · have hx : x = 2 * a + 1 := by omega
      subst hx
      rw [show 2 * a + 1 + 1 = 2 * (a + 1) from by ring, nu_two_mul (by omega),
        nu_two_mul_add_one]
      have := ih a (by omega)
      omega

/-- `ν` is subadditive. -/
theorem nu_add_le (x y : ℕ) : nu (x + y) ≤ nu x + nu y := by
  suffices h : ∀ s, ∀ x y, x + y = s → nu (x + y) ≤ nu x + nu y from h _ x y rfl
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro x y hxy
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · simp
    rcases Nat.even_or_odd x with ⟨a, ha⟩ | ⟨a, ha⟩ <;>
      rcases Nat.even_or_odd y with ⟨b, hb⟩ | ⟨b, hb⟩
    · have hx' : x = 2 * a := by omega
      have hy' : y = 2 * b := by omega
      subst hx'; subst hy'
      have h1 : nu (2 * a + 2 * b) = nu (a + b) := by
        rw [show 2 * a + 2 * b = 2 * (a + b) from by ring]
        exact nu_two_mul (by omega)
      have h2 : nu (2 * a) = nu a := nu_two_mul (by omega)
      have h3 : nu (2 * b) = nu b := nu_two_mul (by omega)
      have hab : a + b < s := by omega
      have := ih (a + b) hab a b rfl
      rw [h1, h2, h3]
      omega
    · have hx' : x = 2 * a := by omega
      have hy' : y = 2 * b + 1 := by omega
      subst hx'; subst hy'
      have h1 : nu (2 * a + (2 * b + 1)) = nu (a + b) + 1 := by
        rw [show 2 * a + (2 * b + 1) = 2 * (a + b) + 1 from by ring, nu_two_mul_add_one]
      have h2 : nu (2 * a) = nu a := nu_two_mul (by omega)
      have h3 : nu (2 * b + 1) = nu b + 1 := nu_two_mul_add_one b
      have hab : a + b < s := by omega
      have := ih (a + b) hab a b rfl
      rw [h1, h2, h3]
      omega
    · have hx' : x = 2 * a + 1 := by omega
      have hy' : y = 2 * b := by omega
      subst hx'; subst hy'
      have h1 : nu (2 * a + 1 + 2 * b) = nu (a + b) + 1 := by
        rw [show 2 * a + 1 + 2 * b = 2 * (a + b) + 1 from by ring, nu_two_mul_add_one]
      have h2 : nu (2 * a + 1) = nu a + 1 := nu_two_mul_add_one a
      have h3 : nu (2 * b) = nu b := nu_two_mul (by omega)
      have hab : a + b < s := by omega
      have := ih (a + b) hab a b rfl
      rw [h1, h2, h3]
      omega
    · have hx' : x = 2 * a + 1 := by omega
      have hy' : y = 2 * b + 1 := by omega
      subst hx'; subst hy'
      have h1 : nu (2 * a + 1 + (2 * b + 1)) = nu (a + (b + 1)) := by
        rw [show 2 * a + 1 + (2 * b + 1) = 2 * (a + (b + 1)) from by ring]
        exact nu_two_mul (by omega)
      have h2 : nu (2 * a + 1) = nu a + 1 := nu_two_mul_add_one a
      have h3 : nu (2 * b + 1) = nu b + 1 := nu_two_mul_add_one b
      have hab : a + (b + 1) < s := by omega
      have h4 := ih (a + (b + 1)) hab a (b + 1) rfl
      have h5 : nu (b + 1) ≤ nu b + 1 := nu_succ_le b
      rw [h1, h2, h3]
      omega

/-- Multiplying by a power of two does not change the binary weight. -/
theorem nu_mul_two_pow : ∀ (x i : ℕ), nu (x * 2 ^ i) = nu x := by
  intro x i
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Nat.pow_succ, ← Nat.mul_assoc]
    rcases Nat.eq_zero_or_pos (x * 2 ^ i) with h | h
    · have hx : x = 0 := by
        rcases Nat.mul_eq_zero.mp h with h' | h'
        · exact h'
        · exact absurd h' (by positivity)
      subst hx; simp
    · rw [Nat.mul_comm _ 2, nu_two_mul (Nat.pos_iff_ne_zero.mp h), ih]

/-- Subadditivity over a finite sum. -/
theorem nu_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℕ) :
    nu (∑ i ∈ s, f i) ≤ ∑ i ∈ s, nu (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc nu (f a + ∑ i ∈ s, f i) ≤ nu (f a) + nu (∑ i ∈ s, f i) := nu_add_le _ _
      _ ≤ nu (f a) + ∑ i ∈ s, nu (f i) := by omega

/-- `ν(2^n - 1) = n`. -/
theorem nu_two_pow_sub_one (n : ℕ) : nu (2 ^ n - 1) = n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : 2 ^ (n + 1) - 1 = 2 * (2 ^ n - 1) + 1 := by
      rw [Nat.pow_succ]
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
    rw [h, nu_two_mul_add_one, ih]

/-! ## Positivity of the values of a 0-chain -/

theorem eval_pos_basisCoef {n : ℕ} (i : Fin n) : 0 < eval (basisCoef i) := by
  rw [eval_basisCoef]; positivity

/-- Every pool element is positive, provided the earlier chain values are. -/
theorem eval_zPool_pos {n : ℕ} {a : ℕ → Coef n} {k : ℕ} (h : ∀ j < k, 0 < eval (a j)) :
    ∀ x : Fin n ⊕ Fin k, 0 < eval (zPool a k x) := by
  rintro (i | j)
  · exact eval_pos_basisCoef i
  · exact h j.1 j.2

namespace StarChain

variable {n : ℕ}

/-- Every value of a 0-chain is positive. -/
theorem eval_a_pos (c : StarChain n) : ∀ j < c.L, 0 < eval (c.a j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    obtain ⟨x, y, hxy⟩ := c.valid j hj
    have hx := eval_zPool_pos (a := c.a) (fun l hl => ih l hl (by omega)) x
    have hy := eval_zPool_pos (a := c.a) (fun l hl => ih l hl (by omega)) y
    rw [hxy, eval_add]
    omega

/-- A 0-chain computes a positive number. -/
theorem value_pos (c : StarChain n) : 0 < c.value := by
  rw [value, ← c.hsrc]
  rcases c.src with i | j
  · exact eval_pos_basisCoef i
  · exact c.eval_a_pos j.1 j.2

/-- Double the output value, using one addition. -/
def dbl (c : StarChain n) : StarChain n := c.append c.src c.src

theorem dbl_value (c : StarChain n) : c.dbl.value = 2 * c.value := by
  rw [dbl, append_value, c.hsrc, value]
  ring

end StarChain

/-- `L∗(0) = 0`: no 0-chain computes `0`. -/
theorem starComplexity_zero : starComplexity 0 = 0 := by
  have hempty : { l | ∃ (n : ℕ) (c : StarChain n), c.L = l ∧ c.value = 0 } = ∅ := by
    ext l
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists, not_and]
    intro n c _ hc
    exact absurd hc (StarChain.value_pos c).ne'
  rw [starComplexity, hempty, Nat.sInf_empty]

/-! ## The prefix chain for `2^N - 1` -/

/-- The coefficient vector with ones in the positions `0, …, k-1`; its value is `2^k - 1`. -/
def blockCoef {n : ℕ} (k : ℕ) : Coef n := fun j => if (j : ℕ) < k then 1 else 0

/-- `∑_{j<k} 2^j = 2^k - 1`. -/
theorem sum_range_two_pow : ∀ k : ℕ, ∑ j ∈ Finset.range k, 2 ^ j = 2 ^ k - 1
  | 0 => by simp
  | k + 1 => by
    rw [Finset.sum_range_succ, sum_range_two_pow k, Nat.pow_succ]
    have h : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    omega

/-- The value of a prefix vector. -/
theorem eval_blockCoef {n k : ℕ} (hk : k ≤ n) : eval (blockCoef (n := n) k) = 2 ^ k - 1 := by
  rw [eval]
  have h1 : (∑ i : Fin n, blockCoef (n := n) k i * 2 ^ (i : ℕ))
      = ∑ i : Fin n, (if (i : ℕ) < k then 2 ^ (i : ℕ) else 0) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [blockCoef]
    split_ifs <;> simp
  rw [h1, Fin.sum_univ_eq_sum_range (fun j => if j < k then 2 ^ j else 0)]
  have hfilter : (Finset.range n).filter (fun j => j < k) = Finset.range k := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hfilter]
  exact sum_range_two_pow k

/-- For `N ≥ 1`, the 0-chain over the basis `2^0, …, 2^N` computing `2^(N+1) - 1` by summing the
free powers of two one at a time.  It has length `N`. -/
def prefixChain (N : ℕ) (hN : 1 ≤ N) : StarChain (N + 1) where
  L := N
  a := fun k => blockCoef (k + 2)
  valid := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · refine ⟨Sum.inl ⟨0, by omega⟩, Sum.inl ⟨1, by omega⟩, ?_⟩
      funext j
      simp only [zPool, blockCoef, basisCoef, Pi.add_apply, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> omega
    · refine ⟨Sum.inr ⟨k - 1, by omega⟩, Sum.inl ⟨k + 1, by omega⟩, ?_⟩
      funext j
      simp only [zPool, blockCoef, basisCoef, Pi.add_apply, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> omega
  val := blockCoef (N + 1)
  src := Sum.inr ⟨N - 1, by omega⟩
  hsrc := by
    have h1 : N - 1 + 2 = N + 1 := by omega
    show blockCoef (N - 1 + 2) = blockCoef (N + 1)
    rw [h1]

theorem prefixChain_L (N : ℕ) (hN : 1 ≤ N) : (prefixChain N hN).L = N := rfl

theorem prefixChain_value (N : ℕ) (hN : 1 ≤ N) :
    (prefixChain N hN).value = 2 ^ (N + 1) - 1 := by
  show eval (blockCoef (n := N + 1) (N + 1)) = 2 ^ (N + 1) - 1
  exact eval_blockCoef le_rfl

/-- For every `N ≥ 1` there is a 0-chain of length `N - 1` computing `2^N - 1`: sum the free
powers of two `2^0, …, 2^(N-1)` one at a time. -/
theorem exists_starChain_two_pow_sub_one : ∀ N : ℕ, 1 ≤ N →
    ∃ c : StarChain N, c.value = 2 ^ N - 1 ∧ c.L = N - 1
  | 0, h => absurd h (by omega)
  | 1, _ => ⟨StarChain.base Nat.one_pos, by simp [StarChain.base_value], rfl⟩
  | M + 2, _ => ⟨prefixChain (M + 1) (by omega), prefixChain_value (M + 1) (by omega), rfl⟩

theorem starChainSet_two_pow_sub_one_nonempty {N : ℕ} (hN : 1 ≤ N) :
    { l | ∃ (n : ℕ) (c : StarChain n), c.L = l ∧ c.value = 2 ^ N - 1 }.Nonempty := by
  obtain ⟨c, hc, _⟩ := exists_starChain_two_pow_sub_one N hN
  exact ⟨c.L, N, c, rfl, hc⟩

/-- `L∗(2^N - 1) ≤ N - 1`. -/
theorem starComplexity_two_pow_sub_one_le (N : ℕ) (hN : 1 ≤ N) :
    starComplexity (2 ^ N - 1) ≤ N - 1 := by
  obtain ⟨c, hc, hL⟩ := exists_starChain_two_pow_sub_one N hN
  have := starComplexity_le c hc
  rwa [hL] at this

/-! ## Scaling: multiplying a 0-chain by a number -/

/-- Multiplication of a coefficient vector by a number. -/
def Coef.smul {n : ℕ} (v : Coef n) (m : ℕ) : Coef n := fun i => v i * m

theorem eval_smul {n : ℕ} (v : Coef n) (m : ℕ) : eval (v.smul m) = m * eval v := by
  rw [eval, eval, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by simp only [Coef.smul]; ring)

theorem Coef.smul_add {n : ℕ} (v : Coef n) (x y : ℕ) :
    v.smul (x + y) = v.smul x + v.smul y := by
  funext i
  simp only [Coef.smul, Pi.add_apply, mul_add]

theorem Coef.smul_one {n : ℕ} (v : Coef n) : v.smul 1 = v := by
  funext i
  simp only [Coef.smul, mul_one]

/-- The `p`-coordinate chosen minimal in the `i`-th step of an addition chain. -/
noncomputable def NatChain.mp (d : NatChain) (i : ℕ) : ℕ :=
  if h : i < d.L then (d.step i h).choose else 0

/-- The `q`-coordinate chosen minimal in the `i`-th step of an addition chain. -/
noncomputable def NatChain.mq (d : NatChain) (i : ℕ) : ℕ :=
  if h : i < d.L then (d.step i h).choose_spec.choose else 0

theorem NatChain.mp_le (d : NatChain) {i : ℕ} (h : i < d.L) : d.mp i ≤ i := by
  rw [NatChain.mp, dif_pos h]
  exact (d.step i h).choose_spec.choose_spec.1

theorem NatChain.mq_le (d : NatChain) {i : ℕ} (h : i < d.L) : d.mq i ≤ i := by
  rw [NatChain.mq, dif_pos h]
  exact (d.step i h).choose_spec.choose_spec.2.1

theorem NatChain.mp_add_mq (d : NatChain) {i : ℕ} (h : i < d.L) :
    d.a (i + 1) = d.a (d.mp i) + d.a (d.mq i) := by
  have hp : d.mp i = (d.step i h).choose := by rw [NatChain.mp, dif_pos h]
  have hq : d.mq i = (d.step i h).choose_spec.choose := by rw [NatChain.mq, dif_pos h]
  rw [hp, hq]
  exact (d.step i h).choose_spec.choose_spec.2.2

namespace StarChain

variable {n : ℕ}

/-- The coefficient vector of `m * c.value`. -/
def smul (c : StarChain n) (m : ℕ) : Coef n := c.val.smul m

theorem eval_smul_val (c : StarChain n) (m : ℕ) : eval (c.smul m) = m * c.value :=
  eval_smul c.val m

theorem smul_add (c : StarChain n) (x y : ℕ) : c.smul (x + y) = c.smul x + c.smul y :=
  Coef.smul_add c.val x y

theorem smul_one (c : StarChain n) : c.smul 1 = c.val := Coef.smul_one c.val

/-- The pool position, in an extension `cur` of `c` of length `c.L + i`, of the `j`-th element of
the multiplier chain: the output of `c` for `j = 0`, and the `(j-1)`-th appended element for
`j ≥ 1`. -/
def mpos (c : StarChain n) (cur : StarChain n) {i : ℕ} (hcur : cur.L = c.L + i) (j : ℕ)
    (hj : j ≤ i) : Fin n ⊕ Fin cur.L :=
  if h0 : j = 0 then Sum.map id (Fin.castLE (by omega)) c.src
  else Sum.inr ⟨c.L + j - 1, by omega⟩

/-- A pool position of `c` remains valid in a longer chain with the same entries below `c.L`. -/
theorem zPool_cast (c : StarChain n) (cur : StarChain n) (hle : c.L ≤ cur.L)
    (hagree : ∀ k < c.L, cur.a k = c.a k) (x : Fin n ⊕ Fin c.L) :
    zPool cur.a cur.L (Sum.map id (Fin.castLE hle) x) = zPool c.a c.L x := by
  rcases x with i | m
  · rfl
  · exact hagree m.1 m.2

/-- At `j = 0` the position `mpos` carries the output value of `c`. -/
theorem zPool_mpos_zero (c : StarChain n) (cur : StarChain n) {i : ℕ} (hcur : cur.L = c.L + i)
    (hagree : ∀ k < c.L, cur.a k = c.a k) :
    zPool cur.a cur.L (mpos c cur hcur 0 (Nat.zero_le i)) = c.val := by
  rw [mpos, dif_pos rfl]
  rw [zPool_cast c cur (by omega) hagree c.src, c.hsrc]

/-- At `j ≥ 1` the position `mpos` carries the `(j-1)`-th appended element. -/
theorem zPool_mpos_pos (c : StarChain n) (cur : StarChain n) {i : ℕ} (hcur : cur.L = c.L + i)
    (j : ℕ) (hj : j ≤ i) (hj1 : 1 ≤ j) :
    zPool cur.a cur.L (mpos c cur hcur j hj) = cur.a (c.L + j - 1) := by
  rw [mpos, dif_neg (by omega)]
  rfl

/-- Invariant of the loop that scales the output of `c` by the values of an addition chain `d`:
`cur` has length `c.L + i`, agrees with `c` below `c.L`, computes `c.value * d.a i`, and its last
`i` entries are the scaled values `c.value * d.a 1, …, c.value * d.a i`. -/
structure ScaleInv (c : StarChain n) (d : NatChain) (i : ℕ) (cur : StarChain n) : Prop where
  /-- the length grows by one per step -/
  len : cur.L = c.L + i
  /-- entries below `c.L` are unchanged -/
  agree : ∀ k < c.L, cur.a k = c.a k
  /-- the value is scaled by the current chain element -/
  value : cur.value = c.value * d.a i
  /-- the appended entries carry the scaled chain elements -/
  entry : ∀ j, 1 ≤ j → j ≤ i → cur.a (c.L + j - 1) = c.smul (d.a j)

theorem exists_scale_aux (c : StarChain n) (d : NatChain) :
    ∀ i, i ≤ d.L → ∃ cur : StarChain n, ScaleInv c d i cur := by
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨c, ?_, ?_, ?_, ?_⟩
    · simp
    · intro k hk; rfl
    · rw [d.h0, Nat.mul_one]
    · intro j hj1 hj2; omega
  | succ i ih =>
    intro hi
    obtain ⟨cur, hSI⟩ := ih (by omega)
    have hcur : cur.L = c.L + i := hSI.len
    have hle : c.L ≤ cur.L := by omega
    have hpq : d.a (i + 1) = d.a (d.mp i) + d.a (d.mq i) := d.mp_add_mq (by omega)
    have hp : d.mp i ≤ i := d.mp_le (by omega)
    have hq : d.mq i ≤ i := d.mq_le (by omega)
    have hpool : ∀ (r : ℕ) (hr : r ≤ i),
        zPool cur.a cur.L (mpos c cur hcur r hr) = c.smul (d.a r) := by
      intro r hr
      rcases Nat.eq_zero_or_pos r with h0 | h1
      · subst h0
        rw [zPool_mpos_zero c cur hcur hSI.agree, d.h0, smul_one]
      · rw [zPool_mpos_pos c cur hcur r hr h1]
        exact hSI.entry r h1 hr
    refine ⟨cur.append (mpos c cur hcur (d.mp i) hp) (mpos c cur hcur (d.mq i) hq), ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · show (cur.append (mpos c cur hcur (d.mp i) hp) (mpos c cur hcur (d.mq i) hq)).L
          = c.L + (i + 1)
      rw [append_L, hcur]
      omega
    · intro k hk
      rw [append_a_of_lt _ _ _ (by omega), hSI.agree k hk]
    · rw [append_value, hpool (d.mp i) hp, hpool (d.mq i) hq, eval_smul_val, eval_smul_val,
        hpq]
      ring
    · intro j hj1 hj2
      rcases Nat.lt_or_ge j (i + 1) with hlt | hge
      · have hidx : c.L + j - 1 < cur.L := by omega
        rw [append_a_of_lt _ _ _ hidx]
        exact hSI.entry j hj1 (by omega)
      · have hje : j = i + 1 := by omega
        subst hje
        have hidx : c.L + (i + 1) - 1 = cur.L := by omega
        rw [hidx, append_a_last, hpool (d.mp i) hp, hpool (d.mq i) hq, hpq, ← smul_add]

/-- Multiplying the output of a 0-chain by the value of an addition chain costs its length. -/
theorem exists_scale (c : StarChain n) (d : NatChain) :
    ∃ cur : StarChain n, cur.L = c.L + d.L ∧ cur.value = c.value * d.a d.L := by
  obtain ⟨cur, hSI⟩ := exists_scale_aux c d d.L le_rfl
  exact ⟨cur, hSI.len, hSI.value⟩

/-- Multiplying the output of a 0-chain by `2^k - 1` costs `L(2^k - 1)` additions. -/
theorem exists_mul_two_pow_sub_one {n : ℕ} (c : StarChain n) {k : ℕ} (hk : 1 ≤ k) :
    ∃ cur : StarChain n, cur.L = c.L + natL (2 ^ k - 1) ∧ cur.value = c.value * (2 ^ k - 1) := by
  have hpos : 1 ≤ 2 ^ k - 1 := by
    have h2 : 2 ≤ 2 ^ k := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  obtain ⟨d, hdL, hdval⟩ := Nat.sInf_mem (NatChainSet_nonempty hpos)
  obtain ⟨cur, hlen, hval⟩ := exists_scale c d
  refine ⟨cur, ?_, ?_⟩
  · rw [hlen, hdL]; rfl
  · rw [hval, hdval]

end StarChain

/-! ## The geometric sum `1 + 2^k + … + 2^(lk)` -/

namespace StarChain

variable {n : ℕ}

/-- `(l + 1) * k < n` as soon as `(l + 2) * k ≤ n` and `n > 0`. -/
theorem succ_mul_lt {l k n : ℕ} (hn : 0 < n) (h : (l + 2) * k ≤ n) : (l + 1) * k < n := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simpa using hn
  · have hlt : (l + 1) * k < (l + 2) * k := Nat.mul_lt_mul_of_pos_right (by omega) hk
    omega

/-- The free powers of two `2^0, 2^k, …, 2^(lk)` sum up with `l` additions. -/
theorem exists_geomChain : ∀ (l k n : ℕ), 0 < n → (l + 1) * k ≤ n →
    ∃ c : StarChain n, c.L = l ∧ c.value = ∑ j ∈ Finset.range (l + 1), 2 ^ (j * k)
  | 0, k, n, hn, _ =>
    ⟨StarChain.base hn, rfl, by simp [StarChain.base_value]⟩
  | l + 1, k, n, hn, hle => by
    have h1 : (l + 1) * k ≤ n :=
      le_trans (Nat.mul_le_mul_right k (by omega)) hle
    obtain ⟨c, hL, hval⟩ := exists_geomChain l k n hn h1
    have hlt : (l + 1) * k < n := succ_mul_lt hn hle
    refine ⟨c.addFree ⟨(l + 1) * k, hlt⟩, by rw [StarChain.addFree_L, hL], ?_⟩
    rw [StarChain.addFree_value, hval,
      Finset.sum_range_succ (fun j => 2 ^ (j * k)) (l + 1),
      Finset.sum_range_succ (fun j => 2 ^ (j * k)) l]

end StarChain

/-- `(2^k - 1) * ∑_{j<m} 2^(jk) = 2^(mk) - 1`. -/
theorem geom_two_pow (k m : ℕ) :
    (2 ^ k - 1) * ∑ j ∈ Finset.range m, 2 ^ (j * k) = 2 ^ (m * k) - 1 := by
  have h1 : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hmul := geom_sum_mul_add (2 ^ k - 1) m
  rw [Nat.sub_add_cancel h1] at hmul
  have hsum : ∑ i ∈ Finset.range m, (2 ^ k) ^ i = ∑ j ∈ Finset.range m, 2 ^ (j * k) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← pow_mul, Nat.mul_comm k j]
  rw [hsum] at hmul
  have h2 : (∑ j ∈ Finset.range m, 2 ^ (j * k)) * (2 ^ k - 1) = (2 ^ k) ^ m - 1 :=
    Nat.eq_sub_of_add_eq hmul
  rw [Nat.mul_comm (2 ^ k - 1) (∑ j ∈ Finset.range m, 2 ^ (j * k)), h2, ← Nat.pow_mul,
    Nat.mul_comm k m]

/-- `∑_{i<m} 2^(a+i) = 2^(a+m) - 2^a`. -/
theorem sum_range_two_pow_add : ∀ (a m : ℕ),
    ∑ i ∈ Finset.range m, 2 ^ (a + i) = 2 ^ (a + m) - 2 ^ a
  | a, 0 => by simp
  | a, m + 1 => by
    rw [Finset.sum_range_succ, sum_range_two_pow_add a m,
      show a + (m + 1) = a + m + 1 from by omega, Nat.pow_succ]
    have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
    have h2 : 2 ^ a ≤ 2 ^ (a + m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ (a + m) + 2 ^ (a + m) = 2 * 2 ^ (a + m) := by ring
    omega

namespace StarChain

variable {n : ℕ}

/-- Adding the free powers `2^a, …, 2^(b-1)` to the output costs `b - a` additions. -/
theorem exists_tail (c : StarChain n) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) :
    ∃ c' : StarChain n, c'.L = c.L + (b - a) ∧ c'.value = c.value + (2 ^ b - 2 ^ a) := by
  refine ⟨c.addFreeAll (b - a) (fun i => ⟨a + i, ?_⟩), ?_, ?_⟩
  · have := i.2
    omega
  · rw [StarChain.addFreeAll_L]
  · rw [StarChain.addFreeAll_value]
    show c.value + (∑ i : Fin (b - a), 2 ^ (a + (i : ℕ))) = c.value + (2 ^ b - 2 ^ a)
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => 2 ^ (a + i)) (b - a),
      sum_range_two_pow_add]
    have hab' : a + (b - a) = b := by omega
    rw [hab']

end StarChain

namespace StarChain

/-- Restrict a coefficient vector to the coordinates selected by `σ`. -/
def rvec {n k : ℕ} (σ : Fin k → Fin n) (v : Coef n) : Vec k := fun j => (v (σ j) : ℤ)

theorem rvec_add {n k : ℕ} (σ : Fin k → Fin n) (u v : Coef n) :
    rvec σ (u + v) = rvec σ u + rvec σ v := by
  funext j
  simp [rvec]

theorem rvec_zero {n k : ℕ} (σ : Fin k → Fin n) : rvec σ (0 : Coef n) = 0 := by
  funext j
  simp [rvec]

theorem rvec_basis_mem {n k : ℕ} (σ : Fin k → Fin n) (hσ : Function.Injective σ) (j : Fin k) :
    rvec σ (basisCoef (σ j)) = basisVec j := by
  funext l
  by_cases h : l = j
  · subst h
    simp [rvec, basisCoef, basisVec]
  · have h2 : σ l ≠ σ j := fun hh => h (hσ hh)
    simp [rvec, basisCoef, basisVec, h, h2]

theorem rvec_basis_not_mem {n k : ℕ} (σ : Fin k → Fin n) (i : Fin n)
    (h : ∀ j, σ j ≠ i) : rvec σ (basisCoef i) = 0 := by
  funext l
  simp only [rvec, basisCoef, Pi.zero_apply]
  rw [if_neg (h l)]
  simp

/-- The values of the restricted chain. -/
theorem exists_chain_rvec_aux {n : ℕ} (c : StarChain n) {k : ℕ} (σ : Fin k → Fin n)
    (hσ : Function.Injective σ) :
    ∀ t, t ≤ c.L → ∃ ch : VecAddChain k, ch.L ≤ t ∧ ∀ j : Fin t, ch.Available (rvec σ (c.a j)) := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨⟨0, fun i => i.elim0, fun i => i.elim0⟩, le_rfl, fun j => j.elim0⟩
  | succ t ih =>
    intro ht
    obtain ⟨ch, hchL, hch⟩ := ih (by omega)
    obtain ⟨x, y, hxy⟩ := c.valid t (by omega)
    have hpool : ∀ x : Fin n ⊕ Fin t, ch.Available (rvec σ (zPool c.a t x)) := by
      rintro (i | l)
      · by_cases hmem : ∃ j : Fin k, σ j = i
        · obtain ⟨j, rfl⟩ := hmem
          rw [show zPool c.a t (Sum.inl (σ j)) = basisCoef (σ j) from rfl,
            rvec_basis_mem σ hσ j]
          exact ch.available_basis j
        · rw [show zPool c.a t (Sum.inl i) = basisCoef i from rfl,
            rvec_basis_not_mem σ i (fun j hj => hmem ⟨j, hj⟩)]
          exact ch.available_zero
      · exact hch l
    obtain ⟨ch', hch'L, hext, hsum⟩ := ch.available_add (hpool x) (hpool y)
    refine ⟨ch', by omega, fun j => ?_⟩
    rcases Nat.lt_or_ge j.1 t with hj | hj
    · exact VecAddChain.Available.mono hext (hch ⟨j.1, hj⟩)
    · have hje : (j : ℕ) = t := by omega
      have hvaleq : rvec σ (c.a j.1) = rvec σ (c.a t) := by rw [hje]
      rw [hvaleq, hxy, rvec_add]
      exact hsum

/-- The output value is available to the restricted chain. -/
theorem exists_chain_rvec_val {n : ℕ} (c : StarChain n) {k : ℕ} (σ : Fin k → Fin n)
    (hσ : Function.Injective σ) :
    ∃ ch : VecAddChain k, ch.L ≤ c.L ∧ ch.Available (rvec σ c.val) := by
  obtain ⟨ch, hchL, hch⟩ := c.exists_chain_rvec_aux σ hσ c.L le_rfl
  refine ⟨ch, hchL, ?_⟩
  rw [← c.hsrc]
  rcases hsrc : c.src with i | l
  · have h1 : zPool c.a c.L (Sum.inl i) = basisCoef i := rfl
    rw [h1]
    by_cases hmem : ∃ j : Fin k, σ j = i
    · obtain ⟨j, rfl⟩ := hmem
      rw [rvec_basis_mem σ hσ j]
      exact ch.available_basis j
    · rw [rvec_basis_not_mem σ i (fun j hj => hmem ⟨j, hj⟩)]
      exact ch.available_zero
  · have h1 : zPool c.a c.L (Sum.inr l) = c.a l.1 := rfl
    rw [h1]
    exact hch l

/-- The row vector of a 0-chain, restricted to the coordinates selected by `σ`. -/
def rrow {n k : ℕ} (c : StarChain n) (σ : Fin k → Fin n) : Matrix (Fin 1) (Fin k) ℤ :=
  fun _ j => (c.val (σ j) : ℤ)

theorem chainComplexity_rrow_le {n : ℕ} (c : StarChain n) {k : ℕ} (σ : Fin k → Fin n)
    (hσ : Function.Injective σ) : chainComplexity (c.rrow σ) ≤ c.L := by
  obtain ⟨ch, hchL, hch⟩ := c.exists_chain_rvec_val σ hσ
  have hcomp : ch.Computes (c.rrow σ) := by
    intro i
    exact VecAddChain.mem_of_available hch
  calc chainComplexity (c.rrow σ) ≤ ch.L := Nat.sInf_le ⟨ch, rfl, hcomp⟩
    _ ≤ c.L := hchL

end StarChain

/-! ## Lower bound: the transposition argument -/

namespace VecAddChain

variable {n : ℕ}

/-- Every coordinate of every vector available in a chain of length `L` is at most `2^L`. -/
theorem pool_le_two_pow (c : VecAddChain n) :
    ∀ (t : ℕ) (ht : t ≤ c.L) (a : Fin n ⊕ Fin t) (j : Fin n),
      chainPool c.y t ht a j ≤ (2 : ℤ) ^ t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht a j
    rcases a with i | l
    · rw [show chainPool c.y t ht (Sum.inl i) = basisVec i from rfl]
      show (if j = i then (1 : ℤ) else 0) ≤ (2 : ℤ) ^ t
      split_ifs
      · have h1 : (1 : ℤ) ≤ (2 : ℤ) ^ t := by
          have := Nat.one_le_two_pow (n := t)
          exact_mod_cast this
        exact h1
      · have h0 : (0 : ℤ) ≤ (2 : ℤ) ^ t := by positivity
        exact h0
    · have hl : (l : ℕ) < t := l.2
      have hlt : (l : ℕ) < c.L := lt_of_lt_of_le l.2 ht
      obtain ⟨p, q, heq⟩ := c.valid ⟨l.1, hlt⟩
      have h1 : chainPool c.y l.1 (le_of_lt hlt) p j ≤ (2 : ℤ) ^ l.1 :=
        ih l.1 hl (le_of_lt hlt) p j
      have h2 : chainPool c.y l.1 (le_of_lt hlt) q j ≤ (2 : ℤ) ^ l.1 :=
        ih l.1 hl (le_of_lt hlt) q j
      rw [show chainPool c.y t ht (Sum.inr l) = c.y ⟨l.1, hlt⟩ from rfl, heq, Pi.add_apply]
      have h3 : (2 : ℤ) ^ (l.1 + 1) = (2 : ℤ) ^ l.1 + (2 : ℤ) ^ l.1 := by
        rw [pow_succ]; ring
      have h4 : (2 : ℤ) ^ (l.1 + 1) ≤ (2 : ℤ) ^ t :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      calc chainPool c.y l.1 (le_of_lt hlt) p j + chainPool c.y l.1 (le_of_lt hlt) q j
          ≤ (2 : ℤ) ^ l.1 + (2 : ℤ) ^ l.1 := add_le_add h1 h2
        _ = (2 : ℤ) ^ (l.1 + 1) := h3.symm
        _ ≤ (2 : ℤ) ^ t := h4

/-- Every coordinate of every available vector of a chain is at most `2^L`. -/
theorem available_le_two_pow (c : VecAddChain n) {v : Vec n} (hv : c.Available v) (j : Fin n) :
    v j ≤ (2 : ℤ) ^ c.L := by
  rcases hv with rfl | ⟨a, ha⟩
  · simp
  · rw [← ha]
    exact pool_le_two_pow c c.L le_rfl a j

end VecAddChain

/-- A number below `2 ^ m` has binary weight at most `m + 1`. -/
theorem nu_le_add_one_of_le_pow {m z : ℕ} (h : z ≤ 2 ^ m) : nu z ≤ m + 1 := by
  rcases Nat.lt_or_eq_of_le h with hlt | heq
  · have h' : z ≤ 2 ^ m - 1 := by omega
    have := nu_le_of_le m z h'
    omega
  · rw [heq, nu_two_pow]; omega

/-- In a vector chain the binary weight of any computed entry of a single-column matrix is at
most the length plus one: `L(x) ≥ ν(x) - 1`. -/
theorem nu_toNat_le_chainComplexity {k : ℕ} (A : Matrix (Fin k) (Fin 1) ℤ)
    (hA : ∀ i j, 0 ≤ A i j) (i : Fin k) :
    nu (A i 0).toNat ≤ chainComplexity A + 1 := by
  obtain ⟨c, hcL, hcomp⟩ := Nat.sInf_mem (chainSet_nonempty A hA)
  have hcL' : c.L = chainComplexity A := hcL
  have hav : c.Available (A i) := VecAddChain.available_of_computes hcomp i
  have hle : A i 0 ≤ (2 : ℤ) ^ c.L := VecAddChain.available_le_two_pow c hav 0
  have hnat : (A i 0).toNat ≤ 2 ^ c.L := by
    rw [Int.toNat_le]; push_cast; exact hle
  have h1 : nu (A i 0).toNat ≤ c.L + 1 := nu_le_add_one_of_le_pow hnat
  omega

/-- **Theorem 2, lower bound.** `L∗(2^n - 1) ≥ 2√n - 2`. -/
theorem theorem2_lower (N : ℕ) : 2 * Real.sqrt N - 2 ≤ starComplexity (2 ^ N - 1) := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    rw [pow_zero, Nat.sub_self, starComplexity_zero]
    norm_num
  · classical
    obtain ⟨n, c, hcL, hcval⟩ := Nat.sInf_mem (starChainSet_two_pow_sub_one_nonempty hN)
    have hweval : eval c.val = 2 ^ N - 1 := hcval
    let supp : Finset (Fin n) := Finset.univ.filter (fun i => c.val i ≠ 0)
    let k : ℕ := supp.card
    let b : ℕ := supp.sup (fun i => nu (c.val i))
    have hsuppmem : ∀ i : Fin n, i ∈ supp ↔ c.val i ≠ 0 := by
      intro i; simp [supp]
    have hne : supp.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      have hzero : ∀ i : Fin n, c.val i = 0 := by
        intro i
        by_contra hi
        have hmem : i ∈ supp := (hsuppmem i).mpr hi
        rw [hemp] at hmem
        exact absurd hmem (Finset.notMem_empty i)
      have hzv : eval c.val = 0 := by simp [eval, hzero]
      have hpos : 0 < eval c.val := by
        rw [hweval]
        exact Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
      omega
    let iso := supp.orderIsoOfFin rfl
    let σ : Fin k → Fin n := fun i => (iso i).1
    have hσmem : ∀ i, σ i ∈ supp := fun i => (iso i).2
    have hσinj : Function.Injective σ := by
      intro i j hij
      exact iso.injective (Subtype.ext hij)
    have hσsurj : ∀ i ∈ supp, ∃ j, σ j = i := by
      intro i hi
      obtain ⟨j, hj⟩ := iso.surjective ⟨i, hi⟩
      exact ⟨j, congrArg Subtype.val hj⟩
    have hA : ∀ i j, 0 ≤ (c.rrow σ) i j := fun i j => by
      show (0 : ℤ) ≤ ((c.val (σ j) : ℤ)); positivity
    have hrow : ∀ i : Fin 1, ∃ j : Fin k, (c.rrow σ) i j ≠ 0 := by
      intro i
      obtain ⟨i0, hi0⟩ := hne
      have hi0' : c.val i0 ≠ 0 := (hsuppmem i0).mp hi0
      obtain ⟨j, hj⟩ := hσsurj i0 hi0
      refine ⟨j, ?_⟩
      show ((c.val (σ j) : ℤ)) ≠ 0
      rw [hj]
      exact_mod_cast hi0'
    have hcol : ∀ j : Fin k, ∃ i : Fin 1, (c.rrow σ) i j ≠ 0 := by
      intro j
      refine ⟨0, ?_⟩
      show ((c.val (σ j) : ℤ)) ≠ 0
      exact_mod_cast (hsuppmem (σ j)).mp (hσmem j)
    have hchain : chainComplexity (c.rrow σ) ≤ c.L := StarChain.chainComplexity_rrow_le c σ hσinj
    have htrans := Circuit.chainComplexity_transpose (c.rrow σ) hA hrow hcol
    have hcolb : b ≤ chainComplexity (Matrix.transpose (c.rrow σ)) + 1 := by
      apply Finset.sup_le
      intro i hi
      obtain ⟨j, hj⟩ := hσsurj i hi
      have hnu := nu_toNat_le_chainComplexity (Matrix.transpose (c.rrow σ))
        (fun a jj => hA jj a) j
      have hcast : ((Matrix.transpose (c.rrow σ)) j 0) = ((c.val (σ j) : ℤ)) := rfl
      rw [hcast, Int.toNat_natCast] at hnu
      rw [← hj]
      exact hnu
    have hk1 : 1 ≤ k := Finset.card_pos.mpr hne
    have hNle : N ≤ k * b := by
      have hNueq : N = nu (eval c.val) := by rw [hweval, nu_two_pow_sub_one]
      rw [hNueq]
      have h1 : nu (eval c.val) ≤ ∑ i : Fin n, nu (c.val i) := by
        have hsum := nu_sum_le (Finset.univ : Finset (Fin n))
          (fun i => c.val i * 2 ^ (i : ℕ))
        rw [eval]
        refine le_trans hsum (le_of_eq ?_)
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [nu_mul_two_pow]
      refine le_trans h1 ?_
      have h2 : (∑ i : Fin n, nu (c.val i)) = ∑ i ∈ supp, nu (c.val i) := by
        refine (Finset.sum_subset (Finset.subset_univ supp) ?_).symm
        intro x _ hx
        have hx0 : c.val x = 0 := by
          by_contra hc
          exact hx ((hsuppmem x).mpr hc)
        simp [hx0]
      rw [h2]
      have h3 : ∑ i ∈ supp, nu (c.val i) ≤ ∑ i ∈ supp, b := by
        refine Finset.sum_le_sum (fun i hi => ?_)
        show nu (c.val i) ≤ supp.sup (fun j => nu (c.val j))
        exact Finset.le_sup (f := fun j => nu (c.val j)) hi
      have h4 : ∑ i ∈ supp, b = k * b := by
        rw [Finset.sum_const, smul_eq_mul]
      rw [h4] at h3
      exact h3
    have hmain : b + k ≤ chainComplexity (c.rrow σ) + 2 := by omega
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    have hb1 : 1 ≤ b := by
      rcases Nat.eq_zero_or_pos b with h | h
      · rw [h] at hNle; omega
      · exact h
    have hNr : (N : ℝ) ≤ (k : ℝ) * (b : ℝ) := by exact_mod_cast hNle
    have hbk : (N : ℝ) / (k : ℝ) ≤ (b : ℝ) := by
      rw [div_le_iff₀ hk0]; linarith
    have hsq : (0 : ℝ) ≤ (Real.sqrt (N : ℝ) - (k : ℝ)) ^ 2 := sq_nonneg _
    have hsqrt : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
    have hAM : 2 * Real.sqrt (N : ℝ) ≤ (N : ℝ) / (k : ℝ) + (k : ℝ) := by
      have hkey : 2 * Real.sqrt (N : ℝ) * (k : ℝ) ≤ (N : ℝ) + (k : ℝ) * (k : ℝ) := by
        nlinarith [hsq, hsqrt]
      have heq : (N : ℝ) / (k : ℝ) + (k : ℝ)
          = ((N : ℝ) + (k : ℝ) * (k : ℝ)) / (k : ℝ) := by
        field_simp
      rw [heq, le_div_iff₀ hk0]
      linarith
    have h1 : ((b : ℝ) + (k : ℝ)) ≤ (chainComplexity (c.rrow σ) : ℝ) + 2 := by
      have hh : ((b + k : ℕ) : ℝ) ≤ ((chainComplexity (c.rrow σ) + 2 : ℕ) : ℝ) := by
        exact_mod_cast hmain
      push_cast at hh ⊢
      linarith
    have h2 : ((chainComplexity (c.rrow σ) : ℕ) : ℝ) ≤ (c.L : ℝ) := by exact_mod_cast hchain
    have h3 : (c.L : ℝ) = (starComplexity (2 ^ N - 1) : ℝ) := by
      rw [hcL]
      rfl
    linarith

/-! ## Arithmetic parameters for the upper bound -/

theorem sq_pred : ∀ m : ℕ, (m - 1) * (m - 1) + (2 * m - 1) = m * m
  | 0 => by simp
  | j + 1 => by
    have h1 : (j + 1) - 1 = j := by omega
    have h2 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
    rw [h1, h2]
    ring

theorem exists_params (n : ℕ) (hn : 26 ≤ n) :
    ∃ m t k : ℕ, 1 ≤ m ∧ 1 ≤ t ∧ 1 ≤ k ∧ k + t = m ∧ (m + t) * k ≤ n ∧ m * m - t * t ≤ n ∧
      n ≤ m * m - (t - 1) * (t - 1) ∧ (m - 1) * (m - 1) < n ∧
      (t - 1) * (t - 1) ≤ 2 * m - 2 ∧ t ≤ 2 * m := by
  set m := Nat.sqrt (n - 1) + 1 with hm
  set t := Nat.sqrt (m * m - n) + 1 with ht
  have hm1 : (m - 1) * (m - 1) ≤ n - 1 := by
    have h := Nat.sqrt_le' (n - 1)
    rw [hm]
    simpa [Nat.pow_two] using h
  have hm2 : n - 1 < m * m := by
    have h := Nat.lt_succ_sqrt (n - 1)
    rw [hm]
    simpa [Nat.pow_two] using h
  have hlt : (m - 1) * (m - 1) < n := by omega
  have hle : n ≤ m * m := by omega
  have hm6 : 6 ≤ m := by
    rw [hm]
    have h5 : 5 ≤ Nat.sqrt (n - 1) := by
      rw [Nat.le_sqrt]
      omega
    omega
  have ht1 : (t - 1) * (t - 1) ≤ m * m - n := by
    have h := Nat.sqrt_le' (m * m - n)
    rw [ht]
    simpa [Nat.pow_two] using h
  have ht2 : m * m - n < t * t := by
    have h := Nat.lt_succ_sqrt (m * m - n)
    rw [ht]
    simpa [Nat.pow_two] using h
  have htle : t - 1 < m := by
    rw [ht]
    show (m * m - n).sqrt + 1 - 1 < m
    rw [Nat.add_sub_cancel, Nat.sqrt_lt]
    exact Nat.sub_lt (by positivity) (by omega)
  have htlem : t ≤ m := by omega
  have httm : t * t ≤ m * m := Nat.mul_le_mul htlem htlem
  have htpos : 0 < t * t := by positivity
  have hsub : m * m - t * t ≤ n := by
    have h := (Nat.sub_lt_iff_lt_add hle).mp ht2
    omega
  have hnat : n ≤ m * m - (t - 1) * (t - 1) := by
    have : n + (t - 1) * (t - 1) ≤ m * m := by omega
    omega
  have htwo : (t - 1) * (t - 1) ≤ 2 * m - 2 := by
    have h : m * m - n ≤ 2 * m - 2 := by
      have hsq := sq_pred m
      omega
    omega
  have hk1 : 1 ≤ m - t := by
    have hkey : (t - 1) * (t - 1) < (m - 1) * (m - 1) := by
      have h3 : 2 * m - 2 < (m - 1) * (m - 1) := by
        have h5 : 5 ≤ m - 1 := by omega
        have h6 : 5 * (m - 1) ≤ (m - 1) * (m - 1) := Nat.mul_le_mul_right (m - 1) h5
        omega
      omega
    have : t - 1 < m - 1 := Nat.mul_self_lt_mul_self_iff.mp hkey
    omega
  have hkt : m - t + t = m := Nat.sub_add_cancel htlem
  have hprod : (m + t) * (m - t) = m * m - t * t := by
    rw [← Nat.sq_sub_sq m t, Nat.pow_two, Nat.pow_two]
  have hmain : (m + t) * (m - t) ≤ n := by rw [hprod]; exact hsub
  exact ⟨m, t, m - t, by omega, by omega, hk1, hkt, hmain, hsub, hnat, hlt, htwo, by omega⟩

/-! ## The upper-bound chain -/

/-- Cancelling a common prefix in a difference of differences. -/
theorem sub_sub_sub (A B C : ℕ) (hCB : C ≤ B) (hBA : B ≤ A) :
    (A - C) - (A - B) = B - C := by
  omega

/-- The length bookkeeping of the upper bound, in additive form so that `omega` can handle the
subtractions: `(m+t-1) + M + B + 3 ≤ 2m + 2t + L₀(k)` whenever `k + t = m`, `M ≤ k - 1 + L₀(k)`
and `B ≤ 2t - 1`. -/
theorem len_arith {m t k M B : ℕ} (hkt : k + t = m)
    (hM : M + 1 ≤ k + natL0 k) (hB : B + 1 ≤ 2 * t) :
    (m + t - 1) + M + B + 3 ≤ 2 * m + 2 * t + natL0 k := by
  omega

/-- The 0-chain behind the upper bound of Theorem 2: the geometric sum `1 + 2^k + … + 2^(lk)` scaled
by `2^k - 1`, plus the tail `2^(m²-t²) + … + 2^(n-1)`, computes `2^n - 1` with at most
`2m + 2t + L₀(k)` additions. -/
theorem exists_upper_chain {n m t k : ℕ} (hn : 0 < n) (hkt : k + t = m) (hk : 1 ≤ k)
    (ht : 1 ≤ t)
    (hge : (m + t) * k ≤ n) (hle : m * m - t * t ≤ n)
    (hne : n ≤ m * m - (t - 1) * (t - 1)) :
    ∃ c : StarChain n, c.value = 2 ^ n - 1 ∧ c.L + 3 ≤ 2 * m + 2 * t + natL0 k := by
  have htle : t ≤ m := by omega
  have hkm : k = m - t := by omega
  obtain ⟨c1, hL1, hv1⟩ := StarChain.exists_geomChain (m + t - 1) k n hn (by
    have h1 : m + t - 1 + 1 = m + t := by omega
    rw [h1]
    exact hge)
  obtain ⟨c2, hL2, hv2⟩ := StarChain.exists_mul_two_pow_sub_one c1 hk
  obtain ⟨c3, hL3, hv3⟩ := StarChain.exists_tail c2 hle le_rfl
  have hkey : (m + t) * k = m * m - t * t := by
    rw [hkm, ← Nat.sq_sub_sq m t]
    simp [Nat.pow_two]
  have hsumind : (∑ j ∈ Finset.range (m + t - 1 + 1), 2 ^ (j * k))
      = ∑ j ∈ Finset.range (m + t), 2 ^ (j * k) := by
    have h2 : m + t - 1 + 1 = m + t := by omega
    rw [h2]
  have hgeom : (∑ j ∈ Finset.range (m + t), 2 ^ (j * k)) * (2 ^ k - 1)
      = 2 ^ (m * m - t * t) - 1 := by
    rw [Nat.mul_comm, geom_two_pow, hkey]
  have hval : (2 ^ (m * m - t * t) - 1) + (2 ^ n - 2 ^ (m * m - t * t)) = 2 ^ n - 1 := by
    have hp1 : 1 ≤ 2 ^ (m * m - t * t) := Nat.one_le_two_pow
    have hp2 : 2 ^ (m * m - t * t) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hle
    omega
  have htail : n - (m * m - t * t) ≤ 2 * t - 1 := by
    have htB : t * t ≤ m * m := Nat.mul_le_mul htle htle
    have hsp : (t - 1) * (t - 1) + (2 * t - 1) = t * t := sq_pred t
    have hB'B : (t - 1) * (t - 1) ≤ t * t := by omega
    have hd : t * t - (t - 1) * (t - 1) = 2 * t - 1 := by omega
    have hmono : n - (m * m - t * t) ≤ (m * m - (t - 1) * (t - 1)) - (m * m - t * t) :=
      Nat.sub_le_sub_right hne _
    rw [sub_sub_sub (m * m) (t * t) ((t - 1) * (t - 1)) hB'B htB, hd] at hmono
    exact hmono
  refine ⟨c3, ?_, ?_⟩
  · rw [hv3, hv2, hv1, hsumind, hgeom, hval]
  · rw [hL3, hL2, hL1]
    refine len_arith hkt ?_ ?_
    · have h7 : natL (2 ^ k - 1) ≤ k - 1 + natL0 k := lemma7 k
      omega
    · omega

/-! ## Real estimates: from the integer chain bound to the asymptotic one -/

/-- For `n ≥ 1`, `1 ≤ n^(1/4)`. -/
theorem one_le_rpow_quarter {n : ℕ} (hn : 1 ≤ n) : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := by
  have h : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  calc (1 : ℝ) = (1 : ℝ) ^ (1 / 4 : ℝ) := by simp
    _ ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by norm_num) h (by norm_num)

/-- `√√n = n^(1/4)`. -/
theorem sqrt_sqrt_eq_rpow (n : ℕ) :
    Real.sqrt (Real.sqrt (n : ℝ)) = (n : ℝ) ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  norm_num

/-- `(m-1)² < n` forces `m ≤ √n + 1`. -/
theorem cast_le_sqrt_add_one {m n : ℕ} (hm : 1 ≤ m) (h : (m - 1) * (m - 1) < n) :
    (m : ℝ) ≤ Real.sqrt (n : ℝ) + 1 := by
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hm, Nat.cast_one]
  have hnn : (0 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hsq : ((m : ℝ) - 1) ^ 2 < (n : ℝ) := by
    have h' : (((m - 1) * (m - 1) : ℕ) : ℝ) < (n : ℝ) := by exact_mod_cast h
    rw [Nat.cast_mul, hcast] at h'
    simpa [sq] using h'
  have h1 : (m : ℝ) - 1 < Real.sqrt (n : ℝ) := (Real.lt_sqrt hnn).mpr hsq
  linarith

/-- `(t-1)² ≤ 2m-2` and `m ≤ √n+1` force `t ≤ 2·n^(1/4) + 1`. -/
theorem cast_le_rpow_add_one {t m n : ℕ} (ht : 1 ≤ t) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (h : (t - 1) * (t - 1) ≤ 2 * m - 2) (hmn : (m : ℝ) ≤ Real.sqrt (n : ℝ) + 1) :
    (t : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 4 : ℝ) + 1 := by
  have hnn : (0 : ℝ) ≤ (t : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by rw [Nat.cast_sub ht, Nat.cast_one]
  have hsq : ((t : ℝ) - 1) ^ 2 ≤ 2 * (m : ℝ) - 2 := by
    have h' : (((t - 1) * (t - 1) : ℕ) : ℝ) ≤ ((2 * m - 2 : ℕ) : ℝ) := by exact_mod_cast h
    have h2 : ((2 * m - 2 : ℕ) : ℝ) = 2 * (m : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega : 2 ≤ 2 * m), Nat.cast_mul]
      push_cast
      ring
    rw [Nat.cast_mul, hcast, h2] at h'
    simpa [sq] using h'
  have hstep : (t : ℝ) - 1 ≤ Real.sqrt (2 * (m : ℝ) - 2) :=
    (Real.le_sqrt hnn (by nlinarith [sq_nonneg ((t : ℝ) - 1)])).mpr hsq
  have hmono : Real.sqrt (2 * (m : ℝ) - 2) ≤ Real.sqrt (2 * (Real.sqrt (n : ℝ) + 1)) := by
    apply Real.sqrt_le_sqrt
    linarith
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := (Real.one_le_sqrt).mpr (by exact_mod_cast hn)
  have hkey : Real.sqrt (2 * (Real.sqrt (n : ℝ) + 1)) ≤ 2 * (n : ℝ) ^ (1 / 4 : ℝ) := by
    calc Real.sqrt (2 * (Real.sqrt (n : ℝ) + 1))
        ≤ Real.sqrt (4 * Real.sqrt (n : ℝ)) := Real.sqrt_le_sqrt (by linarith)
      _ = 2 * Real.sqrt (Real.sqrt (n : ℝ)) := by
            rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
            norm_num
      _ = 2 * (n : ℝ) ^ (1 / 4 : ℝ) := by rw [sqrt_sqrt_eq_rpow]
  linarith

/-- `log₂ n ≤ 6·n^(1/4)` for `n ≥ 1`. -/
theorem logb_le_six_rpow {n : ℕ} (hn : 1 ≤ n) :
    Real.logb 2 (n : ℝ) ≤ 6 * (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : Real.log (n : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) / (1 / 4) :=
    Real.log_le_rpow_div (le_of_lt hn0) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hrp : (0 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg (le_of_lt hn0) _
  rw [Real.logb, div_le_iff₀ (by linarith : (0:ℝ) < Real.log 2)]
  nlinarith

/-- `L₀(k) ≤ 8·n^(1/4)` when `k ≤ m ≤ √n + 1`. -/
theorem natL0_le_rpow {k m n : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) (hn : 1 ≤ n)
    (hmn : (m : ℝ) ≤ Real.sqrt (n : ℝ) + 1) :
    (natL0 k : ℝ) ≤ 8 * (n : ℝ) ^ (1 / 4 : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hr1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := one_le_rpow_quarter hn
  have hlogb : Real.logb 2 (n : ℝ) ≤ 6 * (n : ℝ) ^ (1 / 4 : ℝ) := logb_le_six_rpow hn
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := (Real.one_le_sqrt).mpr (by exact_mod_cast hn)
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · have hk1' : k = 1 := by omega
    rw [hk1']
    rw [natL0_one]
    push_cast
    linarith
  · have hle1 : (natL0 k : ℝ) < 2 * Real.logb 2 (k : ℝ) := lemma4 hk2
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have hm0 : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le hk0 (by exact_mod_cast hkm)
    have hstep : Real.logb 2 (k : ℝ) ≤ Real.logb 2 (m : ℝ) :=
      (Real.logb_le_logb (by norm_num) hk0 hm0).mpr (by exact_mod_cast hkm)
    have hm2s : (m : ℝ) ≤ 2 * Real.sqrt (n : ℝ) := by linarith
    have hstep2 : Real.logb 2 (m : ℝ) ≤ Real.logb 2 (2 * Real.sqrt (n : ℝ)) :=
      (Real.logb_le_logb (by norm_num) hm0 (by positivity)).mpr hm2s
    have hsqlog : Real.logb 2 (Real.sqrt (n : ℝ)) = Real.logb 2 (n : ℝ) / 2 := by
      rw [Real.logb, Real.logb, Real.log_sqrt (le_of_lt hn0)]
      field_simp
    have hsplit : Real.logb 2 (2 * Real.sqrt (n : ℝ)) = 1 + Real.logb 2 (n : ℝ) / 2 := by
      rw [Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num), hsqlog]
    have hcomb : Real.logb 2 (k : ℝ) ≤ 1 + Real.logb 2 (n : ℝ) / 2 := by
      have h := hstep.trans hstep2
      rwa [hsplit] at h
    have : (natL0 k : ℝ) < 2 + Real.logb 2 (n : ℝ) := by
      have h2 := hle1
      linarith
    linarith

/-! ## Theorem 2 -/

/-- **Theorem 2, upper bound.** For `n ≥ 26`, `L∗(2^n - 1) ≤ 2√n + 20·n^(1/4)`. -/
theorem theorem2_upper {n : ℕ} (hn : 26 ≤ n) :
    (starComplexity (2 ^ n - 1) : ℝ) ≤ 2 * Real.sqrt (n : ℝ) + 20 * (n : ℝ) ^ (1 / 4 : ℝ) := by
  obtain ⟨m, t, k, hm1, ht1, hk1, hkt, hge, hle, hne, hlt, htwo, htm⟩ := exists_params n hn
  have hkm : k ≤ m := by omega
  obtain ⟨c, hval, hlen⟩ := exists_upper_chain (n := n) (m := m) (t := t) (k := k)
    (by omega) hkt hk1 ht1 hge hle hne
  have h1 : starComplexity (2 ^ n - 1) ≤ c.L := starComplexity_le c hval
  have h2 : (c.L : ℝ) ≤ 2 * (m : ℝ) + 2 * (t : ℝ) + (natL0 k : ℝ) := by
    have h3 : c.L ≤ 2 * m + 2 * t + natL0 k := by omega
    exact_mod_cast h3
  have hmR : (m : ℝ) ≤ Real.sqrt (n : ℝ) + 1 := cast_le_sqrt_add_one hm1 hlt
  have htR : (t : ℝ) ≤ 2 * (n : ℝ) ^ (1 / 4 : ℝ) + 1 :=
    cast_le_rpow_add_one ht1 hm1 (by omega) htwo hmR
  have hkR : (natL0 k : ℝ) ≤ 8 * (n : ℝ) ^ (1 / 4 : ℝ) :=
    natL0_le_rpow hk1 hkm (by omega) hmR
  have h4 : (starComplexity (2 ^ n - 1) : ℝ) ≤ (c.L : ℝ) := by exact_mod_cast h1
  have hr1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := one_le_rpow_quarter (by omega)
  linarith

/-- **Theorem 2.** `L∗(2^n - 1) = 2√n + O(n^(1/4))`, in the explicit form
`|L∗(2^n - 1) - 2√n| ≤ 30·n^(1/4)` for every `n`. -/
theorem theorem2 : ∃ C : ℝ, ∀ n : ℕ,
    |(starComplexity (2 ^ n - 1) : ℝ) - 2 * Real.sqrt (n : ℝ)|
      ≤ C * (n : ℝ) ^ (1 / 4 : ℝ) := by
  refine ⟨30, fun n => ?_⟩
  have hsq : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  rcases Nat.lt_or_ge n 26 with hn | hn
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [show 2 ^ 0 - 1 = 0 by norm_num, starComplexity_zero]
      norm_num
    · have h1 : (starComplexity (2 ^ n - 1) : ℝ) ≤ (n : ℝ) := by
        have h := starComplexity_two_pow_sub_one_le n (by omega : 1 ≤ n)
        have h' : (starComplexity (2 ^ n - 1) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast h
        have h'' : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
        linarith
      have hr1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := one_le_rpow_quarter (by omega)
      have hn25 : (n : ℝ) ≤ 25 := by exact_mod_cast (by omega : n ≤ 25)
      have hsqrt25 : Real.sqrt (n : ℝ) ≤ 5 := by
        calc Real.sqrt (n : ℝ) ≤ Real.sqrt 25 := Real.sqrt_le_sqrt hn25
          _ = 5 := by norm_num
      have hL0 : (0 : ℝ) ≤ (starComplexity (2 ^ n - 1) : ℝ) := Nat.cast_nonneg _
      rw [abs_le]
      constructor <;> nlinarith
  · have h1 := theorem2_upper hn
    have h2 := theorem2_lower n
    have hr1 : (1 : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) := one_le_rpow_quarter (by omega)
    rw [abs_le]
    constructor <;> nlinarith

/-- **Theorem 2**, asymptotic form: the error term is `O(n^(1/4))`. -/
theorem theorem2_isBigO :
    (fun n : ℕ => (starComplexity (2 ^ n - 1) : ℝ) - 2 * Real.sqrt (n : ℝ))
      =O[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ (1 / 4 : ℝ)) := by
  obtain ⟨C, hC⟩ := theorem2
  refine Asymptotics.IsBigO.of_bound C (Filter.Eventually.of_forall (fun n => ?_))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  exact hC n


/-! ## The relation between 0-chains and ordinary addition chains

The material of this section relates the 0-chain complexity `L∗` of Section 2 of
the paper to the ordinary additive complexity of number sets:

`L(2, 2^2, …, 2^(n-1), m) = L∗(m) + n - 1`   for `m < 2^n`,

where `L` is the ordinary addition chain length (`setL`, the minimal length of an ordinary addition
chain computing the set) and `L∗` is the 0-chain complexity (`starComplexity`).  The main results
are `setL_insert_powSet_eq` and its special case `setL_insert_powSet_two_pow_sub_one`.

Both directions of the argument of the paper are formalized.

* `exists_starChain_of_computes` (lower bound `L ≥ L∗(m) + n - 1`): an ordinary addition chain
  computing `2, 2^2, …, 2^(n-1), m` yields a 0-chain computing `m` by discarding its free steps.
  Each entry of such a chain has a representation in the basis `2^0, …, 2^(n-1)` (this is `rep`), a
  free entry being a single basis vector; deleting the free steps leaves a valid 0-chain.  The
  counting input is `nfSet_card_le`: the `n - 1` values `2, …, 2^(n-1)` occupy `n - 1` distinct
  free steps.
* `setL_le_of_starChain` (upper bound `L ≤ L∗(m) + n - 1`): a 0-chain of basis size `n` and length
  `L` yields an ordinary addition chain of length `L + (n - 1)` computing `2, 2^2, …, 2^(n-1), m`,
  by building the `n - 1` powers first and then replaying the 0-chain.
* `setL_le_starComplexity_add` turns the second direction into the bound on `setL`: a shortest
  0-chain for `m` may be assumed to have basis size exactly `n`, since the basis can be enlarged
  (`StarChain.castBasis`) and, when the basis is too large, truncated (`StarChain.truncBasis`); the
  latter is legitimate precisely because `m < 2^n`, so the coefficients of `2^n, 2^(n+1), …` in the
  output vector vanish (`Coef.eq_zero_of_eval_lt`).

The statement is restricted to `1 ≤ n` and `0 < m`: `L∗` is defined as an infimum, so `L∗(0) = 0`,
while no ordinary addition chain computes the set `{0}`.
-/

/-! ### Ordinary addition chains for finite sets of numbers -/

/-- The pool of values available at step `k` of an ordinary addition chain: the initial value `1`
together with the entries computed so far. -/
def npPool (y : ℕ → ℕ) (k : ℕ) : Option (Fin k) → ℕ
  | none => 1
  | some j => y (j : ℕ)

/-- The value of a pool element. -/
theorem npPool_none (y : ℕ → ℕ) (k : ℕ) : npPool y k none = 1 := rfl

theorem npPool_some (y : ℕ → ℕ) {k : ℕ} (j : Fin k) : npPool y k (some j) = y (j : ℕ) := rfl

/-- An ordinary addition chain `1, y 0, …, y (L-1)`: every entry is the sum of two values available
before it, namely `1` or an earlier entry. -/
structure NatAddChain where
  /-- the length of the chain, i.e. the number of additions -/
  L : ℕ
  /-- the entries of the chain -/
  y : ℕ → ℕ
  /-- every entry is the sum of two available values -/
  valid : ∀ k < L, ∃ x z : Option (Fin k), y k = npPool y k x + npPool y k z

namespace NatAddChain

/-- The chain computes every number of the finite set `S`: each element of `S` is either `1` or one
of the entries of the chain. -/
def Computes (c : NatAddChain) (S : Finset ℕ) : Prop := ∀ a ∈ S, a = 1 ∨ ∃ k < c.L, c.y k = a

/-- `Computes` is monotone in the set. -/
theorem Computes.mono {c : NatAddChain} {S T : Finset ℕ} (h : c.Computes T) (hST : S ⊆ T) :
    c.Computes S := fun a ha => h a (hST ha)

/-- The "increment" chain `1, 2, 3, …, M` of length `M - 1`, which computes every number up to
`M`. -/
def incr (M : ℕ) : NatAddChain where
  L := M - 1
  y := fun k => k + 2
  valid := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact ⟨none, none, by simp only [npPool_none]⟩
    · refine ⟨some ⟨k - 1, by omega⟩, none, ?_⟩
      rw [npPool_some, npPool_none]
      simp only [Fin.val_mk]
      omega

@[simp] theorem incr_L (M : ℕ) : (incr M).L = M - 1 := rfl

@[simp] theorem incr_y (M k : ℕ) : (incr M).y k = k + 2 := rfl

/-- The increment chain computes every number in the interval `[1, M]`. -/
theorem incr_computes (M : ℕ) {S : Finset ℕ} (h : ∀ a ∈ S, 1 ≤ a ∧ a ≤ M) :
    (incr M).Computes S := by
  intro a ha
  obtain ⟨h1, hM⟩ := h a ha
  rcases Nat.eq_or_lt_of_le h1 with h1' | h2
  · exact Or.inl h1'.symm
  · refine Or.inr ⟨a - 2, by simp only [incr_L]; omega, ?_⟩
    simp only [incr_y]
    omega

/-- Some chain computes `S`, provided `S` contains no zero. -/
theorem exists_computes (S : Finset ℕ) (h : ∀ a ∈ S, 1 ≤ a) : ∃ c : NatAddChain, c.Computes S := by
  refine ⟨incr (∑ a ∈ S, a), incr_computes _ ?_⟩
  intro a ha
  refine ⟨h a ha, Finset.single_le_sum (f := fun x => x) (fun x _ => Nat.zero_le x) ha⟩

end NatAddChain

/-- The set `2, 2^2, …, 2^(n-1)` of powers of two strictly between `1` and `2^n`. -/
def powSet (n : ℕ) : Finset ℕ := (Finset.range (n - 1)).image (fun i => 2 ^ (i + 1))

theorem mem_powSet {n a : ℕ} : a ∈ powSet n ↔ ∃ i, 1 ≤ i ∧ i < n ∧ a = 2 ^ i := by
  simp only [powSet, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i + 1, by omega, by omega, rfl⟩
  · rintro ⟨i, h1, h2, rfl⟩
    exact ⟨i - 1, by omega, by rw [Nat.sub_add_cancel h1]⟩

/-- `L(a_1, …, a_k)`: the length of a shortest ordinary addition chain computing the finite set
`S`. -/
noncomputable def setL (S : Finset ℕ) : ℕ :=
  sInf {l | ∃ c : NatAddChain, c.L = l ∧ c.Computes S}

/-- A chain computing `S` bounds `setL S` from above. -/
theorem setL_le {S : Finset ℕ} {c : NatAddChain} (h : c.Computes S) : setL S ≤ c.L :=
  Nat.sInf_le ⟨c, rfl, h⟩

/-- The set of lengths of chains computing `S` is nonempty. -/
theorem setL_nonempty {S : Finset ℕ} (h : ∀ a ∈ S, 1 ≤ a) :
    {l | ∃ c : NatAddChain, c.L = l ∧ c.Computes S}.Nonempty := by
  obtain ⟨c, hc⟩ := NatAddChain.exists_computes S h
  exact ⟨c.L, c, rfl, hc⟩

/-- A bound valid for every chain computing `S` bounds `setL S` from below. -/
theorem le_setL {S : Finset ℕ} (hS : ∀ a ∈ S, 1 ≤ a) {a : ℕ}
    (h : ∀ c : NatAddChain, c.Computes S → a ≤ c.L) : a ≤ setL S := by
  have hmem := Nat.sInf_mem (setL_nonempty hS)
  obtain ⟨c, hL, hc⟩ := hmem
  rw [setL, ← hL]
  exact h c hc

/-! ### From a 0-chain to an addition chain of the powers of two -/

namespace StarChain

variable {n : ℕ}

/-- The entries of the ordinary chain associated with a 0-chain: the `n - 1` powers
`2, 2^2, …, 2^(n-1)` come first, then the values of the 0-chain. -/
def chainFun (c : StarChain n) (k : ℕ) : ℕ :=
  if k < n - 1 then 2 ^ (k + 1) else eval (c.a (k - (n - 1)))

theorem chainFun_of_lt {c : StarChain n} {k : ℕ} (h : k < n - 1) :
    c.chainFun k = 2 ^ (k + 1) := by
  rw [chainFun, if_pos h]

theorem chainFun_of_le {c : StarChain n} {k : ℕ} (h : n - 1 ≤ k) :
    c.chainFun k = eval (c.a (k - (n - 1))) := by
  rw [chainFun, if_neg (by omega)]

/-- A pool position of the 0-chain, read as a pool position of the ordinary chain: the free power
`2^i` sits at step `i - 1` (or is the initial `1`), and an earlier chain element sits after the
`n - 1` power steps. -/
def toPool (c : StarChain n) {k j : ℕ} (hk : n - 1 ≤ k) (hj : j ≤ k - (n - 1))
    (u : Fin n ⊕ Fin j) : Option (Fin k) :=
  match u with
  | Sum.inl i => if h : (i : ℕ) = 0 then none
      else some ⟨(i : ℕ) - 1, by have hin : (i : ℕ) < n := i.isLt; omega⟩
  | Sum.inr t => some ⟨(n - 1) + (t : ℕ), by
      have ht : (t : ℕ) < j := t.isLt
      exact lt_of_lt_of_le (Nat.add_lt_add_left ht (n - 1)) (by omega)⟩

/-- The pool position of the ordinary chain carries the value of the corresponding pool element of
the 0-chain. -/
theorem npPool_toPool (c : StarChain n) (hn : 1 ≤ n) {k j : ℕ} (hk : n - 1 ≤ k)
    (hj : j ≤ k - (n - 1)) (u : Fin n ⊕ Fin j) :
    npPool c.chainFun k (c.toPool hk hj u) = eval (zPool c.a j u) := by
  rcases u with i | t
  · have hval : eval (zPool c.a j (Sum.inl i)) = 2 ^ (i : ℕ) := by
      rw [eval_zPool]
      exact Sum.elim_inl _ _ _
    rw [hval]
    show npPool c.chainFun k
      (if h : (i : ℕ) = 0 then none else some ⟨(i : ℕ) - 1, _⟩) = 2 ^ (i : ℕ)
    by_cases hi : (i : ℕ) = 0
    · rw [dif_pos hi, npPool_none, hi]
      norm_num
    · rw [dif_neg hi, npPool_some]
      simp only [Fin.val_mk]
      have hin : (i : ℕ) < n := i.isLt
      rw [chainFun_of_lt (by omega : (i : ℕ) - 1 < n - 1)]
      rw [show (i : ℕ) - 1 + 1 = (i : ℕ) by omega]
  · have hval : eval (zPool c.a j (Sum.inr t)) = eval (c.a (t : ℕ)) := rfl
    rw [hval]
    show npPool c.chainFun k (some ⟨(n - 1) + (t : ℕ), _⟩) = eval (c.a (t : ℕ))
    rw [npPool_some]
    simp only [Fin.val_mk]
    rw [chainFun_of_le (by omega : n - 1 ≤ (n - 1) + (t : ℕ))]
    rw [show (n - 1) + (t : ℕ) - (n - 1) = (t : ℕ) by omega]

/-- Every step of the associated ordinary chain is an addition of two available values. -/
theorem chainFun_valid (c : StarChain n) (hn : 1 ≤ n) :
    ∀ k < (n - 1) + c.L, ∃ x z : Option (Fin k),
      c.chainFun k = npPool c.chainFun k x + npPool c.chainFun k z := by
  intro k hk
  rcases Nat.lt_or_ge k (n - 1) with hlt | hge
  · rcases Nat.eq_zero_or_pos k with h0 | hk0
    · subst h0
      refine ⟨none, none, ?_⟩
      rw [chainFun_of_lt hlt, npPool_none]
      norm_num
    · have hk1 : k - 1 < n - 1 := by omega
      refine ⟨some ⟨k - 1, by omega⟩, some ⟨k - 1, by omega⟩, ?_⟩
      rw [npPool_some]
      rw [chainFun_of_lt hlt, chainFun_of_lt hk1]
      rw [show k - 1 + 1 = k by omega, pow_succ]
      ring
  · obtain ⟨u, v, huv⟩ := c.valid (k - (n - 1)) (by omega)
    refine ⟨c.toPool hge (le_refl _) u, c.toPool hge (le_refl _) v, ?_⟩
    rw [c.npPool_toPool hn hge (le_refl _) u, c.npPool_toPool hn hge (le_refl _) v]
    rw [chainFun_of_le hge]
    rw [huv, eval_add]

/-- The ordinary addition chain associated with a 0-chain: it has length `(n - 1) + L` and computes
the `n - 1` powers of two together with the value of the 0-chain. -/
def toChain (c : StarChain n) (hn : 1 ≤ n) : NatAddChain where
  L := (n - 1) + c.L
  y := c.chainFun
  valid := c.chainFun_valid hn

@[simp] theorem toChain_L (c : StarChain n) (hn : 1 ≤ n) :
    (c.toChain hn).L = (n - 1) + c.L := rfl

theorem toChain_y (c : StarChain n) (hn : 1 ≤ n) (k : ℕ) :
    (c.toChain hn).y k = c.chainFun k := rfl

theorem toChain_computes (c : StarChain n) (hn : 1 ≤ n) :
    (c.toChain hn).Computes (insert c.value (powSet n)) := by
  intro a ha
  rw [Finset.mem_insert] at ha
  rcases ha with rfl | ha
  · rcases hsrc : c.src with i | t
    · have hval : c.value = 2 ^ (i : ℕ) := by
        rw [value, show c.val = basisCoef i by rw [← c.hsrc, hsrc]; rfl]
        exact eval_basisCoef i
      rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hi0
      · refine Or.inl ?_
        rw [hval, h0]
        norm_num
      · refine Or.inr ⟨(i : ℕ) - 1, ?_, ?_⟩
        · rw [toChain_L]
          have hin : (i : ℕ) < n := i.isLt
          omega
        · rw [toChain_y, hval]
          show c.chainFun ((i : ℕ) - 1) = 2 ^ (i : ℕ)
          have hin : (i : ℕ) < n := i.isLt
          rw [chainFun_of_lt (by omega : (i : ℕ) - 1 < n - 1)]
          rw [show (i : ℕ) - 1 + 1 = (i : ℕ) by omega]
    · have hval : c.value = eval (c.a (t : ℕ)) := by
        rw [value, show c.val = c.a (t : ℕ) by rw [← c.hsrc, hsrc]; rfl]
      refine Or.inr ⟨(n - 1) + (t : ℕ), ?_, ?_⟩
      · rw [toChain_L]
        omega
      · rw [toChain_y]
        show c.chainFun ((n - 1) + (t : ℕ)) = c.value
        rw [chainFun_of_le (by omega : n - 1 ≤ (n - 1) + (t : ℕ))]
        rw [show (n - 1) + (t : ℕ) - (n - 1) = (t : ℕ) by omega, hval]
  · obtain ⟨i, h1, h2, rfl⟩ := mem_powSet.mp ha
    refine Or.inr ⟨i - 1, ?_, ?_⟩
    · rw [toChain_L]
      omega
    · rw [toChain_y]
      show c.chainFun (i - 1) = 2 ^ i
      rw [chainFun_of_lt (by omega : i - 1 < n - 1)]
      rw [show i - 1 + 1 = i by omega]

end StarChain

/-- **First half of the relation `L(2, 2^2, …, 2^(n-1), m) = L∗(m) + n - 1`**: a 0-chain of length
`L` computing `m` yields an ordinary addition chain of length `L + (n - 1)`. -/
theorem setL_le_of_starChain {n : ℕ} (hn : 1 ≤ n) {m : ℕ} (c : StarChain n) (hc : c.value = m) :
    setL (insert m (powSet n)) ≤ c.L + (n - 1) := by
  have h2 : setL (insert c.value (powSet n)) ≤ (c.toChain hn).L := setL_le (c.toChain_computes hn)
  rw [c.toChain_L] at h2
  rw [hc] at h2
  omega

open Classical

/-! ### The free values of a 0-chain -/

/-- A number is free for a 0-chain over the basis `2^0, …, 2^(n-1)`. -/
def IsFree (n v : ℕ) : Prop := ∃ i : Fin n, v = 2 ^ (i : ℕ)

theorem isFree_of_mem_powSet {n a : ℕ} (ha : a ∈ powSet n) : IsFree n a := by
  obtain ⟨i, h1, h2, rfl⟩ := mem_powSet.mp ha
  exact ⟨⟨i, h2⟩, rfl⟩

theorem two_le_of_mem_powSet {n a : ℕ} (ha : a ∈ powSet n) : 2 ≤ a := by
  obtain ⟨i, h1, h2, rfl⟩ := mem_powSet.mp ha
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h1

theorem powSet_card (n : ℕ) : (powSet n).card = n - 1 := by
  have hinj : Function.Injective (fun i : ℕ => 2 ^ (i + 1)) := by
    intro a b hab
    have h2 : 2 ^ (a + 1) = 2 ^ (b + 1) := hab
    have := Nat.pow_right_injective (show 2 ≤ 2 by norm_num) h2
    omega
  rw [powSet, Finset.card_image_of_injective _ hinj, Finset.card_range]

/-! ### A simple family of 0-chains and the attainment of `starComplexity` -/

namespace StarChain

/-- The chain `1, 2, 3, …, k + 1`, of length `k`, over the single free value `1`. -/
def ones : ℕ → StarChain 1
  | 0 => base (by norm_num)
  | k + 1 => (ones k).addFree ⟨0, by norm_num⟩

theorem ones_L : ∀ k, (ones k).L = k
  | 0 => rfl
  | k + 1 => by rw [ones, addFree_L, ones_L k]

theorem ones_value : ∀ k, (ones k).value = k + 1
  | 0 => by
    rw [ones, base_value]
  | k + 1 => by
    have h2 : (2 : ℕ) ^ ((⟨0, by norm_num⟩ : Fin 1) : ℕ) = 1 := rfl
    rw [ones, addFree_value, ones_value k]
    omega

end StarChain

/-- The short chain `1, 2, …, m` bounds `L∗(m)`. -/
theorem starComplexity_le_of_pos {m : ℕ} (hm : 0 < m) : starComplexity m ≤ m - 1 := by
  have h : (StarChain.ones (m - 1)).value = m := by
    rw [StarChain.ones_value]
    omega
  have h2 := starComplexity_le (StarChain.ones (m - 1)) h
  rwa [StarChain.ones_L] at h2

/-- `L∗(m)` is attained by some 0-chain when `m > 0`. -/
theorem starComplexity_attained {m : ℕ} (hm : 0 < m) :
    ∃ (n : ℕ) (c : StarChain n), c.L = starComplexity m ∧ c.value = m := by
  have hne : {l : ℕ | ∃ (n : ℕ) (c : StarChain n), c.L = l ∧ c.value = m}.Nonempty :=
    ⟨m - 1, 1, StarChain.ones (m - 1), StarChain.ones_L _, by
      rw [StarChain.ones_value]
      omega⟩
  exact Nat.sInf_mem hne

/-! ### Changing the size of the basis of a 0-chain -/

namespace Coef

variable {n n' : ℕ}

/-- Truncation of a coefficient vector to a smaller basis. -/
def trunc (hnn : n ≤ n') (v : Coef n') : Coef n := fun i => v (Fin.castLE hnn i)

theorem trunc_add (hnn : n ≤ n') (u v : Coef n') :
    trunc hnn (u + v) = trunc hnn u + trunc hnn v := rfl

theorem trunc_basisCoef (hnn : n ≤ n') (i : Fin n) :
    trunc hnn (basisCoef (Fin.castLE hnn i)) = basisCoef i := by
  funext j
  simp only [trunc, basisCoef, Fin.castLE_inj]

theorem trunc_basisCoef_eq_zero (hnn : n ≤ n') (i : Fin n') (hi : n ≤ (i : ℕ)) :
    trunc hnn (basisCoef i) = 0 := by
  funext j
  simp only [trunc, basisCoef, Pi.zero_apply]
  rw [if_neg]
  intro h
  have h1 : (Fin.castLE hnn j : ℕ) = (j : ℕ) := Fin.val_castLE hnn j
  have h2 : (Fin.castLE hnn j : ℕ) = (i : ℕ) := by rw [h]
  have h3 : (j : ℕ) < n := j.isLt
  omega

theorem eval_trunc_aux :
    ∀ (m n : ℕ) (v : Coef (n + m)),
      (∀ i : Fin (n + m), n ≤ (i : ℕ) → v i = 0) →
      eval (trunc (Nat.le_add_right n m) v) = eval v
  | 0, n, v, _ => rfl
  | m + 1, n, v, hv => by
    have hsplit : eval v = eval (fun i : Fin (n + m) => v i.castSucc)
        + v (Fin.last (n + m)) * 2 ^ (n + m) := by
      have h1 : eval v = ∑ i : Fin (n + m + 1), v i * 2 ^ (i : ℕ) := rfl
      rw [h1, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, eval]
    have hlast : v (Fin.last (n + m)) = 0 := by
      apply hv
      simp only [Fin.val_last]
      omega
    have hIH : eval (trunc (Nat.le_add_right n m) (fun i : Fin (n + m) => v i.castSucc))
        = eval (fun i : Fin (n + m) => v i.castSucc) := by
      apply eval_trunc_aux m n
      intro i hi
      exact hv i.castSucc (by simp only [Fin.val_castSucc]; omega)
    calc eval (trunc (Nat.le_add_right n (m + 1)) v)
        = eval (trunc (Nat.le_add_right n m) (fun i : Fin (n + m) => v i.castSucc)) := rfl
      _ = eval (fun i : Fin (n + m) => v i.castSucc) := hIH
      _ = eval v := by rw [hsplit, hlast]; simp

/-- Truncating a coefficient vector whose entries above the basis vanish does not change its
value. -/
theorem eval_trunc {n n' : ℕ} (hnn : n ≤ n') (v : Coef n')
    (hv : ∀ i : Fin n', n ≤ (i : ℕ) → v i = 0) : eval (trunc hnn v) = eval v := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnn
  exact eval_trunc_aux m n v hv

/-- Extension of a coefficient vector to a larger basis. -/
def cast (hnn : n ≤ n') (v : Coef n) : Coef n' :=
  fun i => if h : (i : ℕ) < n then v ⟨(i : ℕ), h⟩ else 0

theorem trunc_cast (hnn : n ≤ n') (v : Coef n) : trunc hnn (cast hnn v) = v := by
  funext i
  have h : (Fin.castLE hnn i : ℕ) = (i : ℕ) := Fin.val_castLE hnn i
  simp only [trunc, cast]
  rw [dif_pos (by rw [h]; exact i.isLt)]
  congr 1

theorem cast_add (hnn : n ≤ n') (u v : Coef n) :
    cast hnn (u + v) = cast hnn u + cast hnn v := by
  funext i
  simp only [cast, Pi.add_apply]
  split_ifs with h
  · rfl
  · rfl

theorem cast_basisCoef (hnn : n ≤ n') (i : Fin n) :
    cast hnn (basisCoef i) = basisCoef (Fin.castLE hnn i) := by
  funext j
  simp only [cast, basisCoef]
  by_cases h : (j : ℕ) < n
  · rw [dif_pos h]
    have key : (j = Fin.castLE hnn i) ↔ ((⟨(j : ℕ), h⟩ : Fin n) = i) := by
      constructor
      · intro hij
        have hv : (j : ℕ) = (i : ℕ) := by
          rw [hij, Fin.val_castLE]
        exact Fin.ext hv
      · intro hji
        have hv : (j : ℕ) = (i : ℕ) := congrArg Fin.val hji
        exact Fin.ext (by rw [Fin.val_castLE]; exact hv)
    by_cases h1 : ((⟨(j : ℕ), h⟩ : Fin n) = i)
    · rw [if_pos h1, if_pos (key.mpr h1)]
    · rw [if_neg h1, if_neg (fun hc => h1 (key.mp hc))]
  · rw [dif_neg h]
    symm
    rw [if_neg]
    intro hji
    have hv : (j : ℕ) = (i : ℕ) := by
      have := congrArg Fin.val hji
      rwa [Fin.val_castLE] at this
    omega

theorem eval_cast (hnn : n ≤ n') (v : Coef n) : eval (cast hnn v) = eval v := by
  have hvanish : ∀ i : Fin n', n ≤ (i : ℕ) → cast hnn v i = 0 := by
    intro i hi
    simp only [cast]
    rw [dif_neg (by omega)]
  rw [← eval_trunc hnn (cast hnn v) hvanish, trunc_cast hnn v]

end Coef

/-! ### From an ordinary chain to a 0-chain -/

namespace NatAddChain

variable (c : NatAddChain)

/-- A convenient choice of the first summand of step `k`. -/
noncomputable def wx (k : ℕ) (hk : k < c.L) : Option (Fin k) := Classical.choose (c.valid k hk)

/-- A convenient choice of the second summand of step `k`. -/
noncomputable def wy (k : ℕ) (hk : k < c.L) : Option (Fin k) :=
  Classical.choose (Classical.choose_spec (c.valid k hk))

theorem wval (k : ℕ) (hk : k < c.L) :
    c.y k = npPool c.y k (c.wx k hk) + npPool c.y k (c.wy k hk) :=
  Classical.choose_spec (Classical.choose_spec (c.valid k hk))

end NatAddChain

/-! ### Enumerating a finset of natural numbers -/

section Enum

variable {T : Finset ℕ}

/-- The order isomorphism from `Fin T.card` to `T`. -/
noncomputable def enumIso (T : Finset ℕ) : Fin T.card ≃o ↑T := T.orderIsoOfFin rfl

/-- The `i`-th element of the finset `T`. -/
noncomputable def enum (T : Finset ℕ) (i : Fin T.card) : ℕ := ↑(enumIso T i)

/-- The position of `k` in the enumeration of `T`. -/
noncomputable def enumIdx (T : Finset ℕ) (k : ℕ) (hk : k ∈ T) : Fin T.card :=
  (enumIso T).symm ⟨k, hk⟩

theorem enum_mem (T : Finset ℕ) (i : Fin T.card) : enum T i ∈ T := (enumIso T i).2

theorem enum_strictMono (T : Finset ℕ) : StrictMono (enum T) := by
  intro i j hij
  have h1 : enumIso T i < enumIso T j := (OrderIso.lt_iff_lt (enumIso T)).mpr hij
  exact h1

theorem enum_enumIdx (T : Finset ℕ) (k : ℕ) (hk : k ∈ T) : enum T (enumIdx T k hk) = k :=
  congrArg Subtype.val (OrderIso.apply_symm_apply (enumIso T) (⟨k, hk⟩ : ↑T))

theorem enumIdx_enum (T : Finset ℕ) (i : Fin T.card) : enumIdx T (enum T i) (enum_mem T i) = i := by
  have h : (⟨enum T i, enum_mem T i⟩ : ↑T) = enumIso T i := rfl
  rw [enumIdx, h, OrderIso.symm_apply_apply]

theorem enumIdx_lt (T : Finset ℕ) (i : Fin T.card) {j : ℕ} (hj : j ∈ T) (h : j < enum T i) :
    enumIdx T j hj < i := by
  have h1 : (⟨j, hj⟩ : ↑T) < ⟨enum T i, enum_mem T i⟩ := h
  have h2 : (⟨enum T i, enum_mem T i⟩ : ↑T) = enumIso T i := rfl
  rw [h2] at h1
  have h3 := (OrderIso.lt_iff_lt (enumIso T).symm).mpr h1
  rw [OrderIso.symm_apply_apply] at h3
  exact h3

end Enum

/-! ### Representing the values of an ordinary chain in the free basis -/

namespace Coef

/-- The coefficient vector of the free number `1 = 2^0`. -/
def one {n : ℕ} (hn : 0 < n) : Coef n := basisCoef ⟨0, hn⟩

theorem eval_one {n : ℕ} (hn : 0 < n) : eval (one hn) = 1 := by
  rw [one, eval_basisCoef, pow_zero]

/-- A coefficient vector whose value is below `2^n` has no coefficients beyond the `n`-th. -/
theorem eq_zero_of_eval_lt {n' : ℕ} {v : Coef n'} {n : ℕ} (h : eval v < 2 ^ n) :
    ∀ i : Fin n', n ≤ (i : ℕ) → v i = 0 := by
  intro i hi
  by_contra hne
  have hpos : 0 < v i := Nat.pos_of_ne_zero hne
  have hsingle : v i * 2 ^ (i : ℕ) ≤ eval v :=
    Finset.single_le_sum (f := fun j => v j * 2 ^ (j : ℕ)) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have h2 : 2 ^ n ≤ v i * 2 ^ (i : ℕ) := by
    calc 2 ^ n ≤ 2 ^ (i : ℕ) := Nat.pow_le_pow_right (by norm_num) hi
      _ = 1 * 2 ^ (i : ℕ) := (one_mul _).symm
      _ ≤ v i * 2 ^ (i : ℕ) := Nat.mul_le_mul_right _ hpos
  omega

end Coef

namespace NatAddChain

variable (c : NatAddChain)

/-- The coefficient vector of a pool element of step `k`, given the representations of the earlier
steps. -/
def zRepOf {n : ℕ} (hn : 0 < n) {k : ℕ} (rec : (j : ℕ) → j < k → Coef n) :
    Option (Fin k) → Coef n
  | none => Coef.one hn
  | some j => rec j.1 j.2

/-- The representation of the value of step `k` in the free basis `2^0, …, 2^(n-1)`: a free value is
represented by a basis vector, any other value by the sum of the representations of its two
summands. -/
noncomputable def rep (n : ℕ) (hn : 0 < n) : ℕ → Coef n :=
  WellFounded.fix (measure (fun k : ℕ => k)).wf fun k rec =>
    if hk : k < c.L then
      (if hf : IsFree n (c.y k) then basisCoef (Classical.choose hf)
       else zRepOf hn rec (c.wx k hk) + zRepOf hn rec (c.wy k hk))
    else 0

theorem rep_eq (n : ℕ) (hn : 0 < n) (k : ℕ) :
    c.rep n hn k =
      (if hk : k < c.L then
        (if hf : IsFree n (c.y k) then basisCoef (Classical.choose hf)
         else zRepOf hn (fun j _ => c.rep n hn j) (c.wx k hk)
              + zRepOf hn (fun j _ => c.rep n hn j) (c.wy k hk))
      else 0) := by
  unfold rep
  rw [WellFounded.fix_eq]
  rfl

theorem rep_of_free (n : ℕ) (hn : 0 < n) {k : ℕ} (hk : k < c.L) (hf : IsFree n (c.y k)) :
    c.rep n hn k = basisCoef (Classical.choose hf) := by
  rw [c.rep_eq n hn k, dif_pos hk, dif_pos hf]

theorem rep_of_not_free (n : ℕ) (hn : 0 < n) {k : ℕ} (hk : k < c.L) (hf : ¬ IsFree n (c.y k)) :
    c.rep n hn k = zRepOf hn (fun j _ => c.rep n hn j) (c.wx k hk)
      + zRepOf hn (fun j _ => c.rep n hn j) (c.wy k hk) := by
  rw [c.rep_eq n hn k, dif_pos hk, dif_neg hf]

theorem eval_zRepOf {n k : ℕ} (hn : 0 < n) (rec : (j : ℕ) → j < k → Coef n)
    (h : ∀ j : Fin k, eval (rec j.1 j.2) = c.y j.1) (o : Option (Fin k)) :
    eval (zRepOf hn rec o) = npPool c.y k o := by
  rcases o with _ | j
  · exact Coef.eval_one hn
  · exact h j

/-- The representation of the value of a step is the value itself. -/
theorem eval_rep (n : ℕ) (hn : 0 < n) : ∀ k, k < c.L → eval (c.rep n hn k) = c.y k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    by_cases hf : IsFree n (c.y k)
    · rw [c.rep_of_free n hn hk hf, eval_basisCoef]
      exact (Classical.choose_spec hf).symm
    · rw [c.rep_of_not_free n hn hk hf, eval_add,
        c.eval_zRepOf hn _ (fun j => ih j.1 j.2 (j.2.trans hk)) (c.wx k hk),
        c.eval_zRepOf hn _ (fun j => ih j.1 j.2 (j.2.trans hk)) (c.wy k hk),
        c.wval k hk]

end NatAddChain

/-! ### Changing the size of the free basis of a 0-chain -/

namespace StarChain

variable {n n' : ℕ}

theorem zPool_map_cast (hnn : n ≤ n') (a : ℕ → Coef n) (k : ℕ) (u : Fin n ⊕ Fin k) :
    Coef.cast hnn (zPool a k u) =
      zPool (fun j => Coef.cast hnn (a j)) k (Sum.map (Fin.castLE hnn) id u) := by
  rcases u with i | j
  · rw [Sum.map_inl]
    show Coef.cast hnn (basisCoef i) = basisCoef (Fin.castLE hnn i)
    rw [Coef.cast_basisCoef]
  · rfl

theorem zPool_map_trunc (hnn : n ≤ n') (a : ℕ → Coef n') (k : ℕ) (u : Fin n ⊕ Fin k) :
    Coef.trunc hnn (zPool a k (Sum.map (Fin.castLE hnn) id u)) =
      zPool (fun j => Coef.trunc hnn (a j)) k u := by
  rcases u with i | j
  · show Coef.trunc hnn (basisCoef (Fin.castLE hnn i)) = basisCoef i
    rw [Coef.trunc_basisCoef]
  · rfl

/-- Enlarge the free basis of a 0-chain. -/
def castBasis (hnn : n ≤ n') (c : StarChain n) : StarChain n' where
  L := c.L
  a k := Coef.cast hnn (c.a k)
  valid k hk := by
    obtain ⟨x, y, hxy⟩ := c.valid k hk
    refine ⟨Sum.map (Fin.castLE hnn) id x, Sum.map (Fin.castLE hnn) id y, ?_⟩
    rw [← zPool_map_cast hnn, ← zPool_map_cast hnn, hxy, Coef.cast_add]
  val := Coef.cast hnn c.val
  src := Sum.map (Fin.castLE hnn) id c.src
  hsrc := by rw [← zPool_map_cast hnn, c.hsrc]

theorem castBasis_L (hnn : n ≤ n') (c : StarChain n) : (c.castBasis hnn).L = c.L := rfl

theorem castBasis_value (hnn : n ≤ n') (c : StarChain n) :
    (c.castBasis hnn).value = c.value := Coef.eval_cast hnn c.val

/-- The reindexing of the basis `2^0, …, 2^(n'-1)` onto `2^0, …, 2^(n-1)` that collapses every
index at least `n` to `0`. -/
def collapse {n n' : ℕ} (hn0 : 0 < n) (i : Fin n') : Fin n :=
  if h : (i : ℕ) < n then ⟨(i : ℕ), h⟩ else ⟨0, hn0⟩

theorem collapse_of_lt {n n' : ℕ} (hn0 : 0 < n) {i : Fin n'} (h : (i : ℕ) < n) :
    collapse hn0 i = ⟨(i : ℕ), h⟩ := by
  rw [collapse, dif_pos h]

theorem collapse_of_ge {n n' : ℕ} (hn0 : 0 < n) {i : Fin n'} (h : n ≤ (i : ℕ)) :
    collapse hn0 i = ⟨0, hn0⟩ := by
  rw [collapse, dif_neg (by omega)]

/-- Rename the basis vectors along `σ`: the linear map with `2^i ↦ 2^(σ i)`. -/
def rename {n n' : ℕ} (σ : Fin n' → Fin n) (v : Coef n') : Coef n :=
  fun j => ∑ i : Fin n', if σ i = j then v i else 0

theorem rename_add {n n' : ℕ} (σ : Fin n' → Fin n) (u v : Coef n') :
    rename σ (u + v) = rename σ u + rename σ v := by
  funext j
  simp only [rename, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by split_ifs <;> simp)

theorem rename_basisCoef {n n' : ℕ} (σ : Fin n' → Fin n) (i : Fin n') :
    rename σ (basisCoef i) = basisCoef (σ i) := by
  funext j
  rw [rename]
  by_cases h : σ i = j
  · rw [Finset.sum_eq_single i]
    · rw [if_pos h]
      simp only [basisCoef]
      rw [if_pos trivial, if_pos h.symm]
    · intro b _ hb
      have h1 : (b : Fin n') = i → False := hb
      simp only [basisCoef]
      rw [if_neg hb]
      simp
    · intro hc
      exact absurd (Finset.mem_univ i) hc
  · rw [Finset.sum_eq_zero]
    · simp only [basisCoef]
      rw [if_neg (Ne.symm h)]
    · intro b _
      by_cases hb : b = i
      · subst hb
        simp only [if_neg h]
      · simp only [basisCoef]
        rw [if_neg hb]
        simp

theorem rename_collapse_trunc {n n' : ℕ} (hn0 : 0 < n) (hnn : n ≤ n') (v : Coef n')
    (hv : ∀ i : Fin n', n ≤ (i : ℕ) → v i = 0) :
    rename (collapse hn0) v = Coef.trunc hnn v := by
  funext j
  show (∑ i : Fin n', if collapse hn0 i = j then v i else 0) = v (Fin.castLE hnn j)
  rw [Finset.sum_eq_single (Fin.castLE hnn j)]
  · rw [collapse_of_lt hn0 (show ((Fin.castLE hnn j : Fin n') : ℕ) < n by
        rw [Fin.val_castLE]; exact j.2)]
    rw [if_pos (Fin.ext (Fin.val_castLE hnn j))]
  · intro b _ hb
    by_cases hbn : (b : ℕ) < n
    · rw [collapse_of_lt hn0 hbn]
      by_cases hcj : (⟨(b : ℕ), hbn⟩ : Fin n) = j
      · exfalso
        apply hb
        apply Fin.ext
        rw [Fin.val_castLE]
        exact congrArg Fin.val hcj
      · rw [if_neg hcj]
    · rw [collapse_of_ge hn0 (by omega), hv b (by omega)]
      simp
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem zPool_map_rename {n n' : ℕ} (σ : Fin n' → Fin n) (a : ℕ → Coef n') (k : ℕ)
    (u : Fin n' ⊕ Fin k) :
    rename σ (zPool a k u) = zPool (fun j => rename σ (a j)) k (Sum.map σ id u) := by
  rcases u with i | j
  · rw [Sum.map_inl]
    show rename σ (basisCoef i) = basisCoef (σ i)
    rw [rename_basisCoef]
  · rfl

/-- Truncate the free basis of a 0-chain: the free powers `2^i` with `i ≥ n` are identified with
`1`, and junk coefficients above the new basis are dropped (they may safely be identified with the
`1`-coefficient, which is what `collapse` does). -/
def truncBasis (hn0 : 0 < n) (hnn : n ≤ n') (c : StarChain n') : StarChain n where
  L := c.L
  a k := rename (collapse hn0) (c.a k)
  valid k hk := by
    obtain ⟨x, y, hxy⟩ := c.valid k hk
    refine ⟨Sum.map (collapse hn0) id x, Sum.map (collapse hn0) id y, ?_⟩
    show rename (collapse hn0) (c.a k) = zPool (fun j => rename (collapse hn0) (c.a j)) k
        (Sum.map (collapse hn0) id x)
      + zPool (fun j => rename (collapse hn0) (c.a j)) k (Sum.map (collapse hn0) id y)
    rw [← zPool_map_rename, ← zPool_map_rename, hxy, rename_add]
  val := rename (collapse hn0) c.val
  src := Sum.map (collapse hn0) id c.src
  hsrc := by
    show zPool (fun j => rename (collapse hn0) (c.a j)) c.L
      (Sum.map (collapse hn0) id c.src) = rename (collapse hn0) c.val
    rw [← zPool_map_rename, c.hsrc]

theorem truncBasis_L (hn0 : 0 < n) (hnn : n ≤ n') (c : StarChain n') :
    (c.truncBasis hn0 hnn).L = c.L := rfl

theorem truncBasis_value (hn0 : 0 < n) (hnn : n ≤ n') (c : StarChain n')
    (hv : ∀ i : Fin n', n ≤ (i : ℕ) → c.val i = 0) :
    (c.truncBasis hn0 hnn).value = c.value := by
  show eval (rename (collapse hn0) c.val) = eval c.val
  rw [rename_collapse_trunc hn0 hnn c.val hv]
  exact Coef.eval_trunc hnn c.val hv

end StarChain

/-! ### Counting the free steps of an ordinary chain -/

/-- The steps of an ordinary addition chain whose value is not a free power of two. -/
noncomputable def nfSet (n : ℕ) (c : NatAddChain) : Finset ℕ :=
  (Finset.range c.L).filter (fun k => ¬ IsFree n (c.y k))

theorem mem_nfSet {n : ℕ} {c : NatAddChain} {k : ℕ} :
    k ∈ nfSet n c ↔ k < c.L ∧ ¬ IsFree n (c.y k) := by
  simp [nfSet]

/-- The steps split into free and non-free ones. -/
theorem card_nfSet_add (n : ℕ) (c : NatAddChain) :
    (nfSet n c).card + ((Finset.range c.L).filter (fun k => IsFree n (c.y k))).card = c.L := by
  rw [nfSet, add_comm, Finset.card_filter_add_card_filter_not]
  simp

/-- A chain computing `2, 2^2, …, 2^(n-1)` has at least `n - 1` free steps. -/
theorem free_card_ge {n : ℕ} {c : NatAddChain} {m : ℕ}
    (hc : c.Computes (insert m (powSet n))) :
    n - 1 ≤ ((Finset.range c.L).filter (fun k => IsFree n (c.y k))).card := by
  have hsel : ∀ a : {a // a ∈ powSet n}, ∃ k, k < c.L ∧ c.y k = (a : ℕ) := by
    intro a
    rcases hc (a : ℕ) (Finset.mem_insert_of_mem a.2) with h1 | h
    · exfalso
      have h2 := two_le_of_mem_powSet a.2
      omega
    · exact h
  choose fe hfeL hfey using hsel
  have hg : ∀ a : {a // a ∈ powSet n}, fe a ∈
      (Finset.range c.L).filter (fun k => IsFree n (c.y k)) := by
    intro a
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hfeL a), ?_⟩
    rw [hfey a]
    exact isFree_of_mem_powSet a.2
  have hmap : Set.MapsTo fe ↑((powSet n).attach)
      ↑((Finset.range c.L).filter (fun k => IsFree n (c.y k))) := by
    intro a _
    exact hg a
  have hinj : Set.InjOn fe ↑((powSet n).attach) := by
    intro a _ b _ hab
    apply Subtype.ext
    rw [← hfey a, ← hfey b, hab]
  calc n - 1 = (powSet n).card := (powSet_card n).symm
    _ = (powSet n).attach.card := (Finset.card_attach).symm
    _ ≤ _ := Finset.card_le_card_of_injOn fe hmap hinj

/-- An ordinary chain computing `2, 2^2, …, 2^(n-1), m` has at least `n - 1` more steps than its
non-free steps. -/
theorem nfSet_card_le (n : ℕ) (c : NatAddChain) {m : ℕ}
    (hc : c.Computes (insert m (powSet n))) :
    (nfSet n c).card + (n - 1) ≤ c.L := by
  have h1 := card_nfSet_add n c
  have h2 := free_card_ge hc
  omega

/-! ### Compacting an ordinary chain into a 0-chain -/

variable {n : ℕ}

/-- The coefficient vector of the `p`-th non-free step of an ordinary chain. -/
noncomputable def nfA (hn0 : 0 < n) (c : NatAddChain) (p : ℕ) : Coef n :=
  if h : p < (nfSet n c).card then c.rep n hn0 (enum (nfSet n c) ⟨p, h⟩) else 0

theorem nfA_of_lt (hn0 : 0 < n) (c : NatAddChain) {p : ℕ} (h : p < (nfSet n c).card) :
    nfA hn0 c p = c.rep n hn0 (enum (nfSet n c) ⟨p, h⟩) := by
  rw [nfA, dif_pos h]

theorem enum_nfSet_lt (c : NatAddChain) {p : ℕ} (hp : p < (nfSet n c).card) :
    enum (nfSet n c) ⟨p, hp⟩ < c.L :=
  (mem_nfSet.mp (enum_mem (nfSet n c) ⟨p, hp⟩)).1

theorem not_isFree_enum_nfSet (c : NatAddChain) {p : ℕ} (hp : p < (nfSet n c).card) :
    ¬ IsFree n (c.y (enum (nfSet n c) ⟨p, hp⟩)) :=
  (mem_nfSet.mp (enum_mem (nfSet n c) ⟨p, hp⟩)).2

/-- A summand of the `p`-th non-free step is available in the compacted chain: a free summand is a
free value, a non-free one sits at an earlier position of the compaction. -/
theorem zRepOf_eq_zPool (hn0 : 0 < n) (c : NatAddChain) {p : ℕ} (hp : p < (nfSet n c).card)
    {k : ℕ} (hk : k = enum (nfSet n c) ⟨p, hp⟩) (o : Option (Fin k)) :
    ∃ u : Fin n ⊕ Fin p,
      NatAddChain.zRepOf hn0 (fun j _ => c.rep n hn0 j) o = zPool (nfA hn0 c) p u := by
  rcases o with _ | j
  · exact ⟨Sum.inl ⟨0, hn0⟩, rfl⟩
  · have hjL : (j : ℕ) < c.L := by
      have h2 : k < c.L := hk ▸ enum_nfSet_lt c hp
      omega
    by_cases hf : IsFree n (c.y (j : ℕ))
    · refine ⟨Sum.inl (Classical.choose hf), ?_⟩
      show c.rep n hn0 (j : ℕ) = basisCoef (Classical.choose hf)
      exact c.rep_of_free n hn0 hjL hf
    · have hjT : (j : ℕ) ∈ nfSet n c := mem_nfSet.mpr ⟨hjL, hf⟩
      have hlt : (enumIdx (nfSet n c) (j : ℕ) hjT : ℕ) < p :=
        enumIdx_lt (nfSet n c) ⟨p, hp⟩ hjT (lt_of_lt_of_eq j.isLt hk)
      refine ⟨Sum.inr ⟨(enumIdx (nfSet n c) (j : ℕ) hjT : ℕ), hlt⟩, ?_⟩
      show c.rep n hn0 (j : ℕ) = nfA hn0 c (enumIdx (nfSet n c) (j : ℕ) hjT)
      rw [nfA_of_lt hn0 c (enumIdx (nfSet n c) (j : ℕ) hjT).isLt]
      rw [show (enum (nfSet n c) ⟨((enumIdx (nfSet n c) (j : ℕ) hjT) : ℕ),
          (enumIdx (nfSet n c) (j : ℕ) hjT).isLt⟩ : ℕ) = (j : ℕ) from
        enum_enumIdx (nfSet n c) (j : ℕ) hjT]

/-- Every step of the compacted chain is an addition of two available values. -/
theorem compact_valid (hn0 : 0 < n) (c : NatAddChain) :
    ∀ p < (nfSet n c).card, ∃ x y : Fin n ⊕ Fin p,
      nfA hn0 c p = zPool (nfA hn0 c) p x + zPool (nfA hn0 c) p y := by
  intro p hp
  have hklt := enum_nfSet_lt c hp
  have hnf := not_isFree_enum_nfSet c hp
  obtain ⟨x, hx⟩ := zRepOf_eq_zPool hn0 c hp rfl (c.wx (enum (nfSet n c) ⟨p, hp⟩) hklt)
  obtain ⟨y, hy⟩ := zRepOf_eq_zPool hn0 c hp rfl (c.wy (enum (nfSet n c) ⟨p, hp⟩) hklt)
  refine ⟨x, y, ?_⟩
  rw [nfA_of_lt hn0 c hp, c.rep_of_not_free n hn0 hklt hnf, hx, hy]

/-- **An ordinary chain computing `2, 2^2, …, 2^(n-1), m` becomes, after deleting its free steps, a
0-chain of length `L - (n - 1)` computing `m`.** -/
theorem exists_starChain_of_computes {n : ℕ} (hn : 1 ≤ n) {m : ℕ} (c : NatAddChain)
    (hc : c.Computes (insert m (powSet n))) :
    ∃ c' : StarChain n, c'.value = m ∧ c'.L + (n - 1) ≤ c.L := by
  have hn0 : 0 < n := by omega
  have hcard := nfSet_card_le n c hc
  by_cases hf : IsFree n m
  · refine ⟨⟨(nfSet n c).card, nfA hn0 c, compact_valid hn0 c,
      basisCoef (Classical.choose hf), Sum.inl (Classical.choose hf), rfl⟩, ?_, hcard⟩
    show eval (basisCoef (Classical.choose hf)) = m
    rw [eval_basisCoef]
    exact (Classical.choose_spec hf).symm
  · have hm : ∃ k, k < c.L ∧ c.y k = m := by
      rcases hc m (Finset.mem_insert_self m (powSet n)) with h1 | h
      · exfalso
        apply hf
        rw [h1]
        exact ⟨⟨0, hn0⟩, rfl⟩
      · exact h
    obtain ⟨k, hkL, hky⟩ := hm
    have hkT : k ∈ nfSet n c := mem_nfSet.mpr ⟨hkL, by rw [hky]; exact hf⟩
    have hp : ((enumIdx (nfSet n c) k hkT : Fin (nfSet n c).card) : ℕ) < (nfSet n c).card :=
      (enumIdx (nfSet n c) k hkT).isLt
    have hval : nfA hn0 c (enumIdx (nfSet n c) k hkT) = c.rep n hn0 k := by
      rw [nfA_of_lt hn0 c hp]
      rw [show (enum (nfSet n c) ⟨((enumIdx (nfSet n c) k hkT) : ℕ), hp⟩ : ℕ) = k from
        enum_enumIdx (nfSet n c) k hkT]
    refine ⟨⟨(nfSet n c).card, nfA hn0 c, compact_valid hn0 c, c.rep n hn0 k,
      Sum.inr ⟨((enumIdx (nfSet n c) k hkT) : ℕ), hp⟩, ?_⟩, ?_, hcard⟩
    · show zPool (nfA hn0 c) (nfSet n c).card (Sum.inr ⟨_, hp⟩) = c.rep n hn0 k
      show nfA hn0 c ((enumIdx (nfSet n c) k hkT) : ℕ) = c.rep n hn0 k
      exact hval
    · show eval (c.rep n hn0 k) = m
      rw [c.eval_rep n hn0 k hkL, hky]

/-! ### The relation `L(2, 2^2, …, 2^(n-1), m) = L∗(m) + n - 1` -/

/-- **Lower half**: `L(2, 2^2, …, 2^(n-1), m) ≥ L∗(m) + (n - 1)`. -/
theorem starComplexity_add_le_setL {n : ℕ} (hn : 1 ≤ n) {m : ℕ} (hm0 : 0 < m) :
    starComplexity m + (n - 1) ≤ setL (insert m (powSet n)) := by
  refine le_setL (S := insert m (powSet n)) ?_ ?_
  · intro a ha
    rw [Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · omega
    · exact le_trans (by norm_num) (two_le_of_mem_powSet ha)
  · intro c hc
    obtain ⟨c', hv, hL⟩ := exists_starChain_of_computes hn c hc
    calc starComplexity m + (n - 1) ≤ c'.L + (n - 1) :=
          Nat.add_le_add_right (starComplexity_le c' hv) _
      _ ≤ c.L := hL

/-- **Upper half**: `L(2, 2^2, …, 2^(n-1), m) ≤ L∗(m) + (n - 1)`. -/
theorem setL_le_starComplexity_add {n m : ℕ} (hn : 1 ≤ n) (hm0 : 0 < m) (hm : m < 2 ^ n) :
    setL (insert m (powSet n)) ≤ starComplexity m + (n - 1) := by
  obtain ⟨n', c, hL, hv⟩ := starComplexity_attained hm0
  rcases Nat.lt_or_ge n' n with hlt | hge
  · have hnn : n' ≤ n := le_of_lt hlt
    have h1 : (c.castBasis hnn).value = m := by rw [StarChain.castBasis_value, hv]
    have h2 := setL_le_of_starChain hn (c.castBasis hnn) h1
    rw [StarChain.castBasis_L, hL] at h2
    exact h2
  · have hn0 : 0 < n := by omega
    have hvan : ∀ i : Fin n', n ≤ (i : ℕ) → c.val i = 0 := by
      apply Coef.eq_zero_of_eval_lt (n := n) (v := c.val)
      rw [show eval c.val = m from hv]
      exact hm
    have h1 : (c.truncBasis hn0 hge).value = m := by
      rw [StarChain.truncBasis_value hn0 hge c hvan, hv]
    have h2 := setL_le_of_starChain hn (c.truncBasis hn0 hge) h1
    rw [StarChain.truncBasis_L, hL] at h2
    exact h2

/-- **The relation between the ordinary additive complexity of the powers of two with `m` and the
0-chain complexity of `m`**: for `m < 2^n`,

`L(2, 2^2, …, 2^(n-1), m) = L∗(m) + n - 1`.

The proof is the two-step argument of the paper: drop the `n - 1` freely available powers of two
from an ordinary chain computing them (lower bound), and prepend them to a 0-chain (upper bound). -/
theorem setL_insert_powSet_eq {n m : ℕ} (hn : 1 ≤ n) (hm0 : 0 < m) (hm : m < 2 ^ n) :
    setL (insert m (powSet n)) = starComplexity m + (n - 1) :=
  le_antisymm (setL_le_starComplexity_add hn hm0 hm) (starComplexity_add_le_setL hn hm0)

/-- In particular, for `m = 2^n - 1` one has `L(2, 2^2, …, 2^(n-1), 2^n - 1) = L∗(2^n - 1) + n - 1`. -/
theorem setL_insert_powSet_two_pow_sub_one (hn : 1 ≤ n) :
    setL (insert (2 ^ n - 1) (powSet n)) = starComplexity (2 ^ n - 1) + (n - 1) := by
  refine setL_insert_powSet_eq hn ?_ ?_
  · have : 1 < 2 ^ n := Nat.one_lt_two_pow (by omega)
    omega
  · have : 0 < 2 ^ n := Nat.two_pow_pos n
    omega


end AchainsComplexity
