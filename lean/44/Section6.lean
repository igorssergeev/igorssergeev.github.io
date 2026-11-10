import Mathlib
import GF2BilinearLemma2
import GF2Reduced
import Theorem2

/-!
# Section 6 of [16]: examples of hard matrices and corollaries

This file formalizes Section 6 of

* I. S. Sergeev, *Lower bounds on the additive complexity of linear operators and bilinear
  algorithms*,

the construction of a family of hard matrices over `GF(2)` from the theory of linear codes
(the BCH-code example), together with the complexity bounds that the section derives from
Theorem 2 of Section 5 and from Lemma 2 of Section 3.

The matrix is `U = U_n`: for `p = ⌈log₂ n⌉`, `s = ⌈√n⌉` and `m = p·s` it consists of `n - m`
distinct nonzero rows `r_s[α] = (α, α², …, α^s)`, `α ∈ GF(2^p) \ {0}`, each field element
being expanded in a fixed `GF(2)`-basis of `GF(2^p)`.  The section proves

* `ind U ≥ s` (the rows of `U` form a Vandermonde matrix, `ind_rowSet_ge`);
* the bound (6.1), `L*(U) ≥ n + (1 - O(1/s))·n^{1-2/s} - O(m)`, in the concrete form
  `L*(U) ≥ 2n - 20m`: at the chain level in `reducedComplexity_rowSet_ge`, and for `Lstar`
  itself in `six_one_Umat`, applied to a chain whose reduced complexity realizes the minimum;
* Corollary 1: for `A_U = Uᵀ ⊞ U ∈ GF(2)^{n×n}` one has `L(A_U) ≥ 5n - O(√n log n)`,
  in the concrete form `L(A_U) ≥ 5n - 42m` (`corollary1`), with no hypothesis on the columns
  of `U`; its estimate (6.1) is derived by applying `reducedComplexity_rowSet_ge` to a minimal
  chain over the `m` columns of `U`;
* Claim 5: the all-ones matrix satisfies `L*(1_{k×l}) = L(1_{k×l}) = l - 1` for `k ≥ 1`
  (`Lstar_onesMat`, `chainComplexity_onesMat`);
* Corollary 2: for `A = 1_{m×(n-m)} ⊞ U ∈ GF(2)^{n×n}` one has `L*(A) ≥ 3n - O(√n log n)`,
  in the concrete form `3n ≤ L*(A) + 21m + 1` (`corollary2`).
* Corollary 3, first bound: `β₊(M_n) ≥ (4 - o(1))·n²` for matrix multiplication over `GF(2)`,
  in the concrete form `4n² ≤ β₊(M_n) + 21nm + 2m(n-m) + 6n` (`corollary3`), obtained from
  Corollary 2 and Lemma 2 of Section 3 (`GF2BilinearLemma2`);
* Claim 6: if the rows of `B ⊆ GF(2)^m` are rectangle-free of weight at least `s`, then
  `ind (B ∪ I_m) ≥ s` (`claim6`);
* the Erdős–Turán Sidon set `S_n ⊆ [n]` of size `⌊n/(2q)⌋ - 1`, `√n < q ≤ 2√n` prime, with all
  differences of two elements distinct (`sn_sidon_diff`), i.e. all sums of two elements
  determined by the unordered pair (`sn_sidon`).
* Corollary 4, first bound: the cyclic matrix `Z_{n,S_n}` satisfies
  `L(Z_{n,S_n}) ≥ 3n - O(n^{3/4} log n)`, in the concrete form
  `3n ≤ L(Z_{n,S_n}) + 303·m·p` (`corollary4`), where `m = Θ(n^{3/4})` and `p = ⌈log₂ n⌉`.

## Contents

0. Prerequisites copied from Section 1: the complexity measures for circuits, the equivalence
   of the additive models, path counts, and the transposition principle (`claim1`).
1. The numerical parameters `p = ⌈log₂ n⌉`, `s = ⌈√n⌉`, `m = p·s` and their elementary
   inequalities.
2. The field `GF(2^p)`, its coordinates over `GF(2)`, and the row vectors `r_s[α]`.
3. The matrix `U` and the auxiliary set `A ⊆ GF(2^p) \ {0}` of its row labels.
3b. The elementary facts that deleting rows and adding zero columns never increase `L`, and the
   matrix `U'` obtained from `U` by deleting its zero columns, to which the transposition
   principle `claim1` is applied.
4. The independence index of `U`: `ind U ≥ s` (`ind_rowSet_ge`).
5. The bound (6.1) at the chain level, `2n ≤ L*(c) + 20m` for every chain `c` over the `m`
   columns of `U` (`reducedComplexity_rowSet_ge`), via the numerical core `arith_core`, and
   `2n ≤ L*(U) + 20m` for a chain whose reduced complexity realizes the minimum
   (`six_one_Umat`).
6. Corollary 1: `L(A_U) ≥ 5n - 42m` for `A_U = Uᵀ ⊞ U` (`corollary1`), from (6.1), the
   transposition principle applied to `U'`, and the block inequality of Lemma 1.
7. Claim 5: `L*(1_{k×l}) = L(1_{k×l}) = l - 1` for `k ≥ 1` (`Lstar_onesMat`,
   `chainComplexity_onesMat`), via the substitution surgery that cancels the gate attached to a
   zeroed essential variable.
8. Corollary 2: `L*(1_{m×(n-m)} ⊞ U) ≥ 3n - 21m - 1` (`corollary2`).
9. Claim 6: the independence index bound for rectangle-free matrices (`claim6`).
10. The Sidon set `S_n`: the prime `q`, the elements `s_k = 2qk + (k² mod q)`, the set
   `sn n = {s_1, …, s_K}`, its uniform spread (`sval_step_le`, `le_sval_add_gap`), and the Sidon
   property (`sn_sidon`, `sn_sidon_diff`).
11. Corollary 4, first bound: the cyclic matrix `Z_{n,S_n}`, its upper-right `m × (n-m)` block
   `Z` (rectangle-free by the Sidon property), and the estimate
   `L(Z_{n,S_n}) ≥ 3n - 303·m·p` (`corollary4`), via Claim 6, Theorem 2 and Claim 1.

## Organization

## Part 0: prerequisites from Section 1

The transposition principle `claim1` of Section 1 of the paper is used in Corollary 1.
Its proof (the path-counting argument of Section 1) is reproduced here, 
so that this file depends only on `Mathlib`, `GF2Reduced`,
`GF2BilinearLemma2` and `Theorem2`.  Nothing below depends on this part except
`claim1` itself.

## Parts 1-6: Section 6

`pOf`, `sOf`, `mOf` are the parameters (Part 1); `coords` is the coordinate expansion of a
field element in the fixed basis and `rowVec` is the row vector `r_s[α]` (Part 2); `alphaSet`
is the set `A` of row labels, chosen to contain a fixed `GF(2)`-basis `basisSet` of the field
and hence to span `GF(2^p)` over `GF(2)` (`alphaSet_span`); `rowSet` is the image of `A` under
`rowVec`, i.e. the set of rows of `U`; `Umat` is the matrix `U` itself (Part 3), and `UmatNz`
is `U` with its zero columns deleted (Part 3b).  Part 4 proves `ind U ≥ s`.
Part 5 applies Theorem 2 of Section 5 to the rows of `U` (read in the `m`-dimensional ambient
space of the columns) to obtain the bound (6.1) at the level of a single chain, reducing the
numeric part to `arith_core`.  Part 6 combines (6.1) with the block inequality and the
transposition principle into Corollary 1.

## Part 7: Claim 5 and Corollary 2

Part 7 proves Claim 5, `L*(1_{k×l}) = L(1_{k×l}) = l - 1` for `k ≥ 1`.  The lower bound is
proved by substitution: zeroing an essential coordinate `p` cancels the gate attached to `p`,
because its substituted value becomes available earlier.  The cancelled gate's type either has
weight at most one -- and is then not counted in `typeSet` -- or coincides with the type of the
gate attached to its other input, so no type is lost either; hence the reduced complexity drops
by at least one while the number of essential coordinates drops by exactly one
(`claim5_core`).  Together with the block identity of Lemma 1, Claim 5 and (6.1) yield
Corollary 2, `L*(1_{m×(n-m)} ⊞ U) ≥ 3n - 21m - 1`.

## Part 9: Claim 6

Claim 6 says that if the rows of a boolean matrix `B` are rectangle-free (any two rows share at
most one common `1`) and all have weight at least `s`, then `ind (B ∪ I_m) ≥ s` (`claim6`).
The proof counts the rows of a vanishing sub-sum: every row outside `B` is a unit vector, and a
row of `B` must be cancelled entry by entry, each cancellation consuming a different row.

## Part 10: the Sidon set `S_n`

Part 10 constructs the Erdős–Turán Sidon set `S_n = [n] ∩ {2qk + (k² mod q) | 1 ≤ k ≤ K}` of
size `K = ⌊n/(2q)⌋ - 1`, where `q` is a prime with `√n < q ≤ 2√n`.  Its elements are evenly
spread (`sval_step_le`, `le_sval_add_gap`), and it is a Sidon set: two sums of two elements
determine the unordered pair of summands (`sn_sidon`), equivalently all differences with
distinct pairs are distinct (`sn_sidon_diff`).  The proof reduces a sum equality modulo `q` and
then modulo `2q` to the quadratic identity `2(a - c)(a - d) = 0` in `ZMod q`.

## Part 11: Corollary 4

Part 11 builds the cyclic matrix `Z_{n,S_n}` of Section 3 (`Zmat`) and proves the first bound of
Corollary 4, `L(Z_{n,S_n}) ≥ 3n - O(n^{3/4} log n)`.  With `m = Θ(n^{3/4})`, the upper-right
`m × (n-m)` block `Z` is rectangle-free because the rows of `Zᵀ` are windows of the Sidon set
(`ZT_rect`), and each of its rows has weight at least `s = m/(12q)` (`weight_ZT_ge`), so `Zᵀ`
satisfies the hypothesis of Claim 6 (`Zrows_ind`) and Theorem 2 gives
`L(Zᵀ) ≥ 2n - O(m log n)` (`chainComplexity_ZT_ge`, with numerical core `arith_core_Z`).  Since
`Zᵀ` is a submatrix of the transpose of the upper `m × n` block `Z_top`, and
`L(Z_top) = L(Z_topᵀ) + n - m` by Claim 1, while `Z_top` is a submatrix of `Z_{n,S_n}`, this
yields `3n ≤ L(Z_{n,S_n}) + 303·m·p` (`corollary4`).

## Part 8: Corollary 3

Part 8 deduces the first bound of Corollary 3, `β₊(M_n) ≥ (4 - o(1))·n²`, from Lemma 2 of
Section 3 (`lemma2` of `GF2BilinearLemma2`) and Corollary 2.  Lemma 2 is applied to
the `n × n` block matrix `A = 1_{m×(n-m)} ⊞ U` (`Amat`): its reduced complexity is at least
`3n - 21m - 1` by Corollary 2 and is invariant under the reindexing that turns the direct sum
into a square matrix (`Lstar_Amat`), while its boolean weight is at most
`2m(n-m)` because only the two diagonal blocks are nonzero (`boolWeight_Amat_le`).  Hence
`β₊(M_n) ≥ n·L*(A) + n² - ν(A) - 5n ≥ 4n² - 21nm - 2m(n-m) - 6n` (`corollary3`), an error
term of order `n√n log n`.

## Building

This file is checked with `lake env lean Section6.lean`, after the library modules it imports
have been built: `lake build Paper` provides `Theorem2.olean` and
`lake build GF2BilinearLemma2` provides `GF2BilinearLemma2.olean`.  `Section6`
is deliberately not a root of any target: the code-generation pass (`lean -c`) that lake runs
for library roots does not complete in this environment for a module of this size, although the
module itself elaborates without errors or warnings.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace AchainsComplexityGF2

open scoped BigOperators
open Module
open MooreBound

/-! ## Part 0: prerequisites from Section 1 -/

/-! ### Complexity measures for circuits -/

namespace Circuit

variable {n : ℕ}

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

/-- A circuit is *reduced* if every non-input vertex has at least one incoming edge.  Every
circuit is reduced by construction; this lemma exposes the field. -/
theorem IsReduced (C : Circuit n) : ∀ t : Fin (C.N - n), 0 < (C.preds t).length := C.reduced

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

end Circuit

/-- The additive complexity of a matrix restricted to ordinary (fan-in `≤ 2`) circuits. -/
noncomputable def ordinaryComplexity {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) : ℕ :=
  sInf { k | ∃ C : Circuit n, C.IsOrdinary ∧ C.complexity = k ∧ C.Computes A }

/-- The minimal equivalent complexity of an unbounded fan-in circuit computing `A`.  (Every
circuit is reduced, so no junk vertices are present.) -/
noncomputable def minEquivComplexity {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) : ℕ :=
  sInf { k | ∃ C : Circuit n, C.equivComplexity = k ∧ C.Computes A }

/-! ### Equivalence of the additive models (Lemma 1 of Section 2) -/

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

theorem toCircuit_computes {m n : ℕ} (c : VecAddChain n) (A : Matrix (Fin m) (Fin n) (ZMod 2))
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

namespace Circuit

variable {n : ℕ}

theorem equivComplexity_eq_stepsTotal (C : Circuit n) :
    C.equivComplexity = C.stepsTotal := by
  rw [C.equivComplexity_eq_sum]; rfl

end Circuit

theorem sum_fin_one {M : Type*} [AddCommMonoid M] (f : Fin 1 → M) : (∑ x, f x) = f 0 := by
  rw [Fin.sum_univ_castSucc]; simp

namespace Circuit

variable {n : ℕ}

theorem toChain_L (C : Circuit n) : C.toChain.L = C.stepsTotal := rfl

theorem chainComplexity_le_equivComplexity {m : ℕ} (C : Circuit n)
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (hA : C.Computes A) :
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

/-! ### The sets of possible complexities, and their mutual inclusions -/

/-- Equivalent complexities of unbounded fan-in circuits computing `A`. -/
def EquivSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) : Set ℕ :=
  { k | ∃ C : Circuit n, C.equivComplexity = k ∧ C.Computes A }

/-- Complexities of ordinary circuits computing `A`. -/
def OrdSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) : Set ℕ :=
  { k | ∃ C : Circuit n, C.IsOrdinary ∧ C.complexity = k ∧ C.Computes A }

@[simp] theorem ordinaryComplexity_eq_sInf {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    ordinaryComplexity A = sInf (OrdSet A) := rfl

@[simp] theorem minEquivComplexity_eq_sInf {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    minEquivComplexity A = sInf (EquivSet A) := rfl

/-- A chain computing `A`, read as its circuit, witnesses that the chain lengths are equivalent
complexities of circuits computing `A`. -/
theorem chainSet_subset_equivSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    ChainSet A ⊆ EquivSet A := by
  rintro l ⟨c, hL, hc⟩
  refine ⟨c.toCircuit, ?_, c.toCircuit_computes A hc⟩
  rw [c.toCircuit_equivComplexity]; exact hL

/-- Conversely, every circuit computing `A` yields a chain of the same equivalent complexity. -/
theorem equivSet_subset_chainSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    EquivSet A ⊆ ChainSet A := by
  rintro k ⟨C, hEq, hC⟩
  refine ⟨C.toChain, ?_, C.toChain_computes A hC⟩
  rw [C.toChain_L, ← Circuit.equivComplexity_eq_stepsTotal]; exact hEq

/-- A chain computing `A`, read as its circuit, is ordinary. -/
theorem chainSet_subset_ordSet {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    ChainSet A ⊆ OrdSet A := by
  rintro l ⟨c, hL, hc⟩
  refine ⟨c.toCircuit, c.toCircuit_isOrdinary, ?_, c.toCircuit_computes A hc⟩
  show c.toCircuit.N - n = l
  rw [c.toCircuit_complexity]; exact hL

/-- **Lemma 1** (paper).  For every matrix `A`, the additive complexity `L(A)` defined through
vector addition chains, the additive complexity in the ordinary (fan-in `≤ 2`) circuit model,
and the minimal equivalent complexity of an unbounded fan-in circuit computing `A` all coincide:

  `chainComplexity A = ordinaryComplexity A = minEquivComplexity A`.

The ordinary model measures size by the number of non-input vertices; the unbounded fan-in model
measures it by the equivalent complexity, `#edges − #non-input vertices`. -/
theorem lemma1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
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

namespace Circuit

variable {n : ℕ}

/-- The path-count step: number of oriented paths from `a` to `b`, by recursion on the target
`b` (a path is either empty or ends with an edge into `b`). -/
noncomputable def pcStep (C : Circuit n) (a : Fin C.N) :
    (b : Fin C.N) → ((u : Fin C.N) → u.1 < b.1 → (ZMod 2)) → (ZMod 2) :=
  fun b ih =>
    (if a = b then (1 : (ZMod 2)) else 0) +
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
noncomputable def pc (C : Circuit n) (a : Fin C.N) : Fin C.N → (ZMod 2) :=
  WellFounded.fix (measure (fun b : Fin C.N => b.1)).wf (C.pcStep a)

theorem pc_eq (C : Circuit n) (a b : Fin C.N) :
    C.pc a b =
      (if a = b then (1 : (ZMod 2)) else 0) +
        if h : b.1 < n then 0
        else ∑ i : Fin (C.preds ⟨b.1 - n, by omega⟩).length,
              C.pc a ((C.preds ⟨b.1 - n, by omega⟩).get i) := by
  unfold pc
  rw [WellFounded.fix_eq]
  rfl

/-- The sum over the outgoing edges of `a`, of `F` applied to the head of each edge. -/
noncomputable def Fwd (C : Circuit n) (a : Fin C.N) (F : Fin C.N → (ZMod 2)) : (ZMod 2) :=
  ∑ t : Fin (C.N - n), ∑ i : Fin (C.preds t).length,
    if (C.preds t).get i = a then F (C.idx t) else 0

theorem inputVertex_val (C : Circuit n) (j : Fin n) : (C.inputVertex j).1 = j.1 := rfl

/-- The `j`-th component represented by a vertex equals the number of oriented paths from the
`j`-th input to it. -/
theorem comp_eq_pc (C : Circuit n) (j : Fin n) (b : Fin C.N) :
    C.comp j b = C.pc (C.inputVertex j) b := by
  refine WellFounded.induction (C.vrel_wf)
    (C := fun x => C.comp j x = C.pc (C.inputVertex j) x) b (fun b ih => ?_)
  rw [C.comp_eq j b, C.pc_eq (C.inputVertex j) b]
  by_cases hb : b.1 < n
  · rw [dif_pos hb, dif_pos hb]
    have hsafe : (if (j = (⟨b.1, hb⟩ : Fin n)) then (1 : (ZMod 2)) else 0)
        = (if (C.inputVertex j = b) then (1 : (ZMod 2)) else 0) := by
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
    have hz : (if (C.inputVertex j = b) then (1 : (ZMod 2)) else 0) = 0 := by
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
    C.pc a b = (if a = b then (1 : (ZMod 2)) else 0) +
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
    C.pc a b = (if a = b then (1 : (ZMod 2)) else 0) + C.Fwd a (fun x => C.pc x b) := by
  revert b
  refine WellFounded.induction (measure (fun a : Fin C.N => C.N - a.1)).wf
    (C := fun a => ∀ b : Fin C.N,
      C.pc a b = (if a = b then (1 : (ZMod 2)) else 0) + C.Fwd a (fun x => C.pc x b)) a ?_
  intro a IHa b
  refine WellFounded.induction (measure (fun b : Fin C.N => b.1)).wf
    (C := fun b => C.pc a b = (if a = b then (1 : (ZMod 2)) else 0) + C.Fwd a (fun x => C.pc x b)) b ?_
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
              ((if a = (C.preds (C.tIdx b hb)).get i then (1 : (ZMod 2)) else 0)
                + C.Fwd a (fun x => C.pc x ((C.preds (C.tIdx b hb)).get i))) := by
        apply Finset.sum_congr rfl
        intro i _
        exact IHb _ (C.pred_get_lt hb i)
      rw [h1, Finset.sum_add_distrib]
      have h2 : (∑ i : Fin (C.preds (C.tIdx b hb)).length,
            C.Fwd a (fun x => C.pc x ((C.preds (C.tIdx b hb)).get i)))
          = C.Fwd a (fun x => C.pc x b)
            - (∑ i : Fin (C.preds (C.tIdx b hb)).length,
                (if a = (C.preds (C.tIdx b hb)).get i then (1 : (ZMod 2)) else 0)) := by
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
              = C.pc (C.idx t) b - (if C.idx t = b then (1 : (ZMod 2)) else 0) := by
          intro t
          have h := C.pc_eq_noninput (C.idx t) b hb
          rw [h]
          ring
        simp only [hstep]
        have hsplit : (∑ p : (Σ t : Fin (C.N - n), Fin (C.preds t).length),
              (if (C.preds p.1).get p.2 = a
                then (C.pc (C.idx p.1) b - (if C.idx p.1 = b then (1 : (ZMod 2)) else 0)) else 0))
            = (∑ p : (Σ t : Fin (C.N - n), Fin (C.preds t).length),
                (if (C.preds p.1).get p.2 = a then C.pc (C.idx p.1) b else 0))
              - (∑ p : (Σ t : Fin (C.N - n), Fin (C.preds t).length),
                (if (C.preds p.1).get p.2 = a
                  then (if C.idx p.1 = b then (1 : (ZMod 2)) else 0) else 0)) := by
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
                then (if C.idx p.1 = b then (1 : (ZMod 2)) else 0) else 0))
            = ∑ i : Fin (C.preds (C.tIdx b hb)).length,
                (if a = (C.preds (C.tIdx b hb)).get i then (1 : (ZMod 2)) else 0) := by
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

/-! ### The transposition principle (Claim 1) -/

section ListLemmas

variable {α β M : Type*} [AddCommMonoid M]

theorem sum_get_eq_map_sum (l : List α) (f : α → M) :
    (∑ i : Fin l.length, f (l.get i)) = (l.map f).sum := by
  have h := List.map_ofFn (f := (fun i : Fin l.length => l.get i)) (g := f)
  simp only [List.ofFn_get, Function.comp_def] at h
  rw [← List.sum_ofFn, ← h]

/-- The number of occurrences of `v` in a list. -/
def mult [DecidableEq α] (l : List α) (v : α) : ℕ :=
  (l.filter (fun x => x = v)).length

variable [DecidableEq α]

@[simp] theorem mult_nil (v : α) : mult ([] : List α) v = 0 := rfl

theorem mult_cons (a : α) (l : List α) (v : α) :
    mult (a :: l) v = (if a = v then 1 else 0) + mult l v := by
  unfold mult
  by_cases h : a = v
  · rw [if_pos h, List.filter_cons_of_pos (by simp [h]), List.length_cons, Nat.add_comm]
  · rw [if_neg h, List.filter_cons_of_neg (by simp [h]), Nat.zero_add]

theorem mult_append (l₁ l₂ : List α) (v : α) : mult (l₁ ++ l₂) v = mult l₁ v + mult l₂ v := by
  unfold mult
  rw [List.filter_append, List.length_append]

theorem mult_flatMap [DecidableEq β] (l : List α) (g : α → List β) (v : β) :
    mult (l.flatMap g) v = (l.map (fun a => mult (g a) v)).sum := by
  unfold mult
  rw [List.filter_flatMap, List.length_flatMap]

theorem mult_replicate [DecidableEq β] (n : ℕ) (a v : β) :
    mult (List.replicate n a) v = if a = v then n else 0 := by
  unfold mult
  by_cases h : a = v
  · subst h; simp
  · rw [if_neg h]
    induction n with
    | zero => rfl
    | succ k ih => rw [List.replicate_succ, List.filter_cons_of_neg (by simp [h]), ih]

/-- Multiplicity of a constant list. -/
theorem mult_map_const {γ : Type*} [DecidableEq γ] (l : List α) (a : γ) (v : γ) :
    mult (l.map (fun _ => a)) v = if a = v then l.length else 0 := by
  have hm : (l.map (fun _ => a)) = List.replicate l.length a := by
    induction l with
    | nil => rfl
    | cons x l ih => simp only [List.map_cons, List.length_cons, List.replicate_succ, ih]
  rw [hm, mult_replicate]

theorem map_sum_filter_count (l : List α) (v : α) (c : M) :
    ((l.map (fun x => if x = v then c else 0))).sum
      = ((l.filter (fun x => x = v)).length) • c := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons]
    by_cases h : a = v
    · rw [if_pos h, ih, List.filter_cons_of_pos (by simp [h]), List.length_cons, succ_nsmul,
        add_comm]
    · rw [if_neg h, zero_add, ih, List.filter_cons_of_neg (by simp [h])]

theorem map_sum_eq_mult_smul (l : List α) (v : α) (c : M) :
    ((l.map (fun x => if x = v then c else 0))).sum = (mult l v) • c :=
  map_sum_filter_count l v c

/-- Summing `mult l a • c a` over a finite set containing all elements of `l` gives the sum of
`c` over `l`. -/
theorem sum_mult_smul_of_subset (l : List α) (s : Finset α) (c : α → M)
    (h : ∀ x ∈ l, x ∈ s) :
    (∑ a ∈ s, (mult l a) • c a) = (l.map c).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have hx : x ∈ s := h x (by simp)
    have h' : ∀ y ∈ l, y ∈ s := fun y hy => h y (List.mem_cons_of_mem x hy)
    rw [List.map_cons, List.sum_cons, ← ih h']
    have hsplit : (∑ a ∈ s, (mult (x :: l) a) • c a)
        = (∑ a ∈ s, ((if x = a then (1 : ℕ) else 0)) • c a)
          + (∑ a ∈ s, (mult l a) • c a) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [mult_cons, add_nsmul]
    rw [hsplit]
    congr 1
    rw [← Finset.add_sum_erase s _ hx, Finset.sum_eq_zero]
    · simp
    · intro a ha
      have hax : a ≠ x := (Finset.mem_erase.mp ha).1
      rw [if_neg (Ne.symm hax), zero_smul]

end ListLemmas

namespace Circuit

variable {n : ℕ}

/-! ### Edges, reachability and the cone of the row witnesses -/

/-- The edge relation of a circuit: `v` is an incoming neighbour of `w`. -/
def Edge (C : Circuit n) (v w : Fin C.N) : Prop :=
  ∃ t : Fin (C.N - n), ∃ i : Fin (C.preds t).length, (C.preds t).get i = v ∧ C.idx t = w

/-- Reachability in the graph of a circuit. -/
def Reach (C : Circuit n) (v w : Fin C.N) : Prop := Relation.ReflTransGen C.Edge v w

theorem reach_refl (C : Circuit n) (v : Fin C.N) : C.Reach v v := Relation.ReflTransGen.refl

theorem reach_step (C : Circuit n) {v w : Fin C.N} (h : C.Edge v w) : C.Reach v w :=
  Relation.ReflTransGen.single h

theorem reach_trans (C : Circuit n) {u v w : Fin C.N} (h₁ : C.Reach u v) (h₂ : C.Reach v w) :
    C.Reach u w := h₁.trans h₂

theorem edge_lt (C : Circuit n) {v w : Fin C.N} (h : C.Edge v w) : v.1 < w.1 := by
  obtain ⟨t, i, rfl, rfl⟩ := h
  have hac := C.acyclic t _ (List.get_mem _ i)
  simpa [Circuit.idx_val] using hac

theorem reach_lt (C : Circuit n) {v w : Fin C.N} (h : C.Reach v w) : v.1 ≤ w.1 := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact ih.trans (le_of_lt (C.edge_lt hstep))

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

theorem Kinc_KposInc (C : Circuit n) (ρ : Fin m → Fin C.N) (v : ↥(C.cone ρ)) :
    Kinc C ρ (KposInc C ρ v) = v.1 := by
  simp [Kinc, KposInc]

theorem KposInc_Kinc (C : Circuit n) (ρ : Fin m → Fin C.N) (i : Fin (C.cone ρ).card)
    (h : Kinc C ρ i ∈ C.cone ρ) :
    KposInc C ρ ⟨Kinc C ρ i, h⟩ = i := by
  simp [Kinc, KposInc]

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

/-! ### The transposed circuit: vertices and edges -/

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

theorem z_inj (C : Circuit n) (ρ : Fin m → Fin C.N) : Function.Injective (z C ρ) := by
  intro i i' h
  have h' := congrArg Fin.val h
  exact Fin.ext h'

theorem Dv_inj (C : Circuit n) (ρ : Fin m → Fin C.N) :
    Function.Injective (Dv C ρ) := by
  intro v w h
  have hv : m + (Kpos C ρ v).1 = m + (Kpos C ρ w).1 := congrArg Fin.val h
  have h2 : (Kpos C ρ v).1 = (Kpos C ρ w).1 := by omega
  have h3 : Kpos C ρ v = Kpos C ρ w := Fin.ext h2
  apply Subtype.ext
  rw [← Kdec_Kpos C ρ v, ← Kdec_Kpos C ρ w, h3]

theorem z_ne_Dv (C : Circuit n) (ρ : Fin m → Fin C.N) (i : Fin m) (v : ↥(C.cone ρ)) :
    z C ρ i ≠ Dv C ρ v := by
  intro h
  have h1 : i.1 = m + (Kpos C ρ v).1 := congrArg Fin.val h
  have := i.2
  omega

theorem Dv_proof_irrel (C : Circuit n) (ρ : Fin m → Fin C.N) (v : Fin C.N)
    (h₁ h₂ : v ∈ C.cone ρ) : Dv C ρ ⟨v, h₁⟩ = Dv C ρ ⟨v, h₂⟩ := by
  have hs : (⟨v, h₁⟩ : ↥(C.cone ρ)) = ⟨v, h₂⟩ := Subtype.ext rfl
  simp only [Dv, hs]

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
    C.pc (C.inputVertex i) (C.inputVertex i') = if i = i' then (1 : (ZMod 2)) else 0 := by
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
    (D C ρ).pc (z C ρ i) (z C ρ i') = if i = i' then (1 : (ZMod 2)) else 0 := by
  have h1 : z C ρ i = (D C ρ).inputVertex i := Fin.ext rfl
  have h2 : z C ρ i' = (D C ρ).inputVertex i' := Fin.ext rfl
  rw [h1, h2, pc_input]

end Circuit

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

/-! ### Expanded recurrence for paths in the transposed circuit -/

theorem D_preds_apply (C : Circuit n) {m : ℕ} (ρ : Fin m → Fin C.N)
    (t : Fin ((D C ρ).N - m)) :
    (D C ρ).preds t = Dpreds C ρ (Dpos C ρ t) := rfl
theorem Dpos_val' (C : Circuit n) (ρ : Fin m → Fin C.N) (t : Fin ((D C ρ).N - m)) :
    (Dpos C ρ t).1 = t.1 := rfl

theorem Dpos_eq (C : Circuit n) (ρ : Fin m → Fin C.N)
    {t : Fin (C.cone ρ).card} {u : Fin ((D C ρ).N - m)} (h : u.1 = t.1) :
    Dpos C ρ u = t := by
  apply Fin.ext
  rw [Dpos_val']
  exact h

theorem sum_Dpreds_apply (C : Circuit n) (ρ : Fin m → Fin C.N) (v : ↥(C.cone ρ))
    (F : Fin (m + (C.cone ρ).card) → (ZMod 2)) :
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
      = (if x = Dv C ρ v then (1 : (ZMod 2)) else 0)
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
  rw [show (D C ρ).pc x b = (if x = b then (1 : (ZMod 2)) else 0)
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

/-! ### The path identity -/

theorem pc_D_z_Dv (C : Circuit n) (ρ : Fin m → Fin C.N) (i : Fin m) :
    ∀ v : ↥(C.cone ρ), (D C ρ).pc (z C ρ i) (Dv C ρ v) = C.pc v.1 (ρ i) := by
  intro v
  refine WellFounded.induction (measure (fun v : ↥(C.cone ρ) => (Kpos C ρ v).1)).wf
    (C := fun v => (D C ρ).pc (z C ρ i) (Dv C ρ v) = C.pc v.1 (ρ i)) v ?_
  intro v ih
  rw [D_pc_split C ρ (z C ρ i) v]
  have h1 : (if z C ρ i = Dv C ρ v then (1 : (ZMod 2)) else 0) = 0 := by
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
      = if v.1 = ρ i then (1 : (ZMod 2)) else 0 := by
    have hstep : ∀ j : Fin m, (D C ρ).pc (z C ρ i) (z C ρ j) = if i = j then (1:(ZMod 2)) else 0 :=
      fun j => D_pc_z C ρ i j
    simp only [hstep]
    by_cases hri : ρ i = v.1
    · have hzero : ∀ j : Fin m, j ≠ i →
          (if ρ j = v.1 then (if i = j then (1:(ZMod 2)) else 0) else 0) = 0 := by
        intro j hj
        by_cases hρj : ρ j = v.1
        · rw [if_pos hρj, if_neg (Ne.symm hj)]
        · rw [if_neg hρj]
      rw [Finset.sum_eq_single i]
      · rw [if_pos hri, if_pos rfl, if_pos hri.symm]
      · intro j _ hj; exact hzero j hj
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · have hzero : ∀ j : Fin m,
          (if ρ j = v.1 then (if i = j then (1:(ZMod 2)) else 0) else 0) = 0 := by
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

/-! ### Structural bounds on the cone -/

/-- Every input vertex lies in the cone, because no column of `A` is zero. -/
theorem inputVertex_mem_cone (C : Circuit n) (ρ : Fin m → Fin C.N)
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (hρ : ∀ i, C.repr (ρ i) = A i)
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

/-! ### The counting inequality -/

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

theorem sum_flatMap {α β : Type*} [AddCommMonoid β] (l : List α) (g : α → List β) :
    (l.flatMap g).sum = (l.map (fun a => (g a).sum)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

theorem sum_map_finRange {M : Type*} [AddCommMonoid M] {k : ℕ} (f : Fin k → M) :
    ((List.finRange k).map f).sum = ∑ i : Fin k, f i := by
  rw [← List.ofFn_id k, List.map_ofFn, List.sum_ofFn]
  rfl

/-! ### The transposition principle (Claim 1) -/

/-- Every nonzero row is represented by some vertex. -/
theorem exists_repr_of_computes (C : Circuit n) {m : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
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
theorem D_computes (C : Circuit n) (ρ : Fin m → Fin C.N) (A : Matrix (Fin m) (Fin n) (ZMod 2))
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

theorem minEquiv_transpose_add_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (hrow : ∀ i, ∃ j, A i j ≠ 0) (hcol : ∀ j, ∃ i, A i j ≠ 0) :
    minEquivComplexity (Matrix.transpose A) + n ≤ minEquivComplexity A + m := by
  classical
  have hne : { k | ∃ C : Circuit n, C.equivComplexity = k ∧ C.Computes A }.Nonempty :=
    ⟨_, star A hrow, rfl, star_computes A hrow⟩
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

/-- **Lemma 2** (transposition principle): for a matrix over `GF(2)` with no zero row and no
zero column, `L(A) + m = L(Aᵀ) + n`, in terms of the minimal equivalent complexity (the size
measure used for unbounded fan-in circuits). -/
theorem lemma2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (hrow : ∀ i, ∃ j, A i j ≠ 0) (hcol : ∀ j, ∃ i, A i j ≠ 0) :
    minEquivComplexity A + m = minEquivComplexity (Matrix.transpose A) + n := by
  have hrowAt : ∀ i, ∃ j, Matrix.transpose A i j ≠ 0 := hcol
  have hcolAt : ∀ j, ∃ i, Matrix.transpose A i j ≠ 0 := hrow
  have h1 := minEquiv_transpose_add_le A hrow hcol
  have h2 := minEquiv_transpose_add_le (Matrix.transpose A) hrowAt hcolAt
  rw [Matrix.transpose_transpose] at h2
  omega

/-- Lemma 2 in the chain model: since all three size measures agree (`lemma1`), the identity
extends to the additive complexity `L` of vector addition chains, `L(A) + m = L(Aᵀ) + n`. -/
theorem chainComplexity_transpose {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (hrow : ∀ i, ∃ j, A i j ≠ 0) (hcol : ∀ j, ∃ i, A i j ≠ 0) :
    chainComplexity A + m = chainComplexity (Matrix.transpose A) + n := by
  have h := lemma2 A hrow hcol
  rw [(lemma1 A).1, (lemma1 A).2,
      (lemma1 (Matrix.transpose A)).1, (lemma1 (Matrix.transpose A)).2]
  exact h

end Circuit

/-- **Claim 1** (transposition principle over `GF(2)`, Sergeev, Section 1).  If `A` is a
boolean `m × n` matrix without zero rows and columns, then

  `L(A) + m = L(Aᵀ) + n`,

where `L` is the additive complexity (`chainComplexity`). -/
theorem claim1 {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (hrow : ∀ i, ∃ j, A i j ≠ 0) (hcol : ∀ j, ∃ i, A i j ≠ 0) :
    chainComplexity A + m = chainComplexity (Matrix.transpose A) + n :=
  Circuit.chainComplexity_transpose A hrow hcol

/-! ## Part 1: the numerical parameters

For a dimension `n` we put `p = ⌈log₂ n⌉` (`pOf`), `s = ⌈√n⌉` (`sOf`) and `m = p·s` (`mOf`);
the construction of the paper applies to `n ≥ N₀ = 2^40`.  This part collects the elementary
inequalities used by Parts 4 and 5 -- in particular `4p ≤ s ≤ 2√n`, `s² ≤ 2^p`, `m ≤ n/2`, and
the properties of the parameter `k = ⌊s/2⌋ - 1` of Theorem 2, for which `2k + 2 ≤ s` and `k ≥ 2`.

The parameter `s` is defined as `min (⌈√n⌉) (2^(p/2))`.  The second term is only a safeguard for
the divisibility argument of Part 2: the Vandermonde matrix of Part 2 has order `s` and needs
`s` distinct elements in `GF(2^p)`, which is the case because `s ≤ 2^(p/2) < 2^p`.  For
`n ≥ N₀` the minimum is attained at `⌈√n⌉` in the interesting range, and all the estimates below
hold for either branch. -/

/-- The threshold `N₀ = 2^40` of the paper ("for a sufficiently large `n`"). -/
def N₀ : ℕ := 2 ^ 40

/-- `p = ⌈log₂ n⌉`, the degree of the field `GF(2^p)`. -/
def pOf (n : ℕ) : ℕ := Nat.log2 n + 1

/-- `s = ⌈√n⌉` (truncated at `2^(p/2)`, see the discussion above). -/
def sOf (n : ℕ) : ℕ := min (Nat.sqrt n + 1) (2 ^ (pOf n / 2))

/-- `m = p·s`, the number of columns of the matrix `U`. -/
abbrev mOf (n : ℕ) : ℕ := sOf n * pOf n

/-- The parameter `k = ⌊s/2⌋ - 1` of Theorem 2: `2k + 2 ≤ s` and `k ≥ 2`. -/
def kOf (n : ℕ) : ℕ := sOf n / 2 - 1

theorem pOf_pos (n : ℕ) : 0 < pOf n := by unfold pOf; omega

/-- For `n ≥ N₀` the field degree is at least `14`. -/
theorem fourteen_le_pOf (n : ℕ) (hn : N₀ ≤ n) : 14 ≤ pOf n := by
  have h : 13 ≤ Nat.log2 n := by
    rw [Nat.le_log2 (by unfold N₀ at hn; omega)]
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hn
  unfold pOf; omega

theorem sOf_pos (n : ℕ) : 0 < sOf n := by
  unfold sOf; exact lt_min (by positivity) (by positivity)

theorem n_lt_two_pow_pOf (n : ℕ) : n < 2 ^ pOf n := by
  have h := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) n
  rw [pOf, Nat.log2_eq_log_two]
  exact h

theorem one_le_pOf (n : ℕ) : 1 ≤ pOf n := pOf_pos n

theorem pOf_le_self (n : ℕ) (hn : 2 ≤ n) : pOf n ≤ n := by
  unfold pOf
  have h : Nat.log 2 n < n := Nat.log_lt_self 2 (by omega)
  rw [Nat.log2_eq_log_two]
  omega

/-- `2^p ≤ 2n`: the field has at most `2n` elements. -/
theorem two_pow_pOf_le_two_mul (n : ℕ) (hn : 0 < n) : 2 ^ pOf n ≤ 2 * n := by
  have h1 : 2 ^ pOf n = 2 ^ Nat.log2 n * 2 := by
    unfold pOf; exact pow_succ 2 (Nat.log2 n)
  have h2 : 2 ^ Nat.log2 n ≤ n := by
    rw [Nat.log2_eq_log_two]; exact Nat.pow_log_le_self 2 hn.ne'
  omega

theorem sOf_le_sqrt (n : ℕ) : sOf n ≤ Nat.sqrt n + 1 := by
  unfold sOf; exact min_le_left _ _

theorem sOf_le_pow (n : ℕ) : sOf n ≤ 2 ^ (pOf n / 2) := by
  unfold sOf; exact min_le_right _ _

/-- `s² ≤ 2^p`: the rows have `s` power blocks of length `p` in a field of `2^p` elements. -/
theorem sOf_sq_le (n : ℕ) : sOf n ^ 2 ≤ 2 ^ pOf n := by
  have h := sOf_le_pow n
  have hp : pOf n / 2 * 2 ≤ pOf n := Nat.div_mul_le_self _ _
  calc sOf n ^ 2 ≤ (2 ^ (pOf n / 2)) ^ 2 := Nat.pow_le_pow_left h 2
    _ = 2 ^ (pOf n / 2 * 2) := by rw [← pow_mul]
    _ ≤ 2 ^ pOf n := Nat.pow_le_pow_right (by norm_num) hp

/-- `n ≤ 2s²`, i.e. `s ≥ √(n/2)`. -/
theorem sOf_sq_ge (n : ℕ) (hn : 1 ≤ n) : n ≤ 2 * sOf n ^ 2 := by
  rcases Nat.le_total (Nat.sqrt n + 1) (2 ^ (pOf n / 2)) with h | h
  · rw [sOf, Nat.min_eq_left h]
    have h1 : n < (Nat.sqrt n + 1) ^ 2 := by
      simpa [pow_two, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt n
    have h2 : 0 < (Nat.sqrt n + 1) ^ 2 := by positivity
    omega
  · rw [sOf, Nat.min_eq_right h]
    have h2 : 2 * (2 ^ (pOf n / 2)) ^ 2 = 2 ^ (pOf n / 2 * 2 + 1) := by
      rw [← pow_mul, mul_comm, ← pow_succ]
    have h3 : pOf n ≤ pOf n / 2 * 2 + 1 := by
      have := Nat.div_mul_le_self (pOf n) 2; omega
    have h4 : 2 ^ pOf n ≤ 2 ^ (pOf n / 2 * 2 + 1) :=
      Nat.pow_le_pow_right (by norm_num) h3
    have h5 := n_lt_two_pow_pOf n
    omega

theorem thirtytwo_mul_sq_le_two_pow : ∀ p : ℕ, 14 ≤ p → 32 * p ^ 2 ≤ 2 ^ p := by
  intro p hp
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    rcases Nat.lt_or_ge p 16 with hlt | hge
    · interval_cases p <;> norm_num
    · have hp2 : p - 2 < p := by omega
      have h2 : 14 ≤ p - 2 := by omega
      have hrec := ih (p - 2) hp2 h2
      have hlin : p ≤ 2 * (p - 2) := by omega
      have hstep : 32 * p ^ 2 ≤ 4 * (32 * (p - 2) ^ 2) := by nlinarith
      have hpow : 2 ^ p = 4 * 2 ^ (p - 2) := by
        rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_add, show 2 + (p - 2) = p by omega]
      have hrec4 : 4 * (32 * (p - 2) ^ 2) ≤ 4 * 2 ^ (p - 2) := Nat.mul_le_mul_left 4 hrec
      calc 32 * p ^ 2 ≤ 4 * (32 * (p - 2) ^ 2) := hstep
        _ ≤ 4 * 2 ^ (p - 2) := hrec4
        _ = 2 ^ p := hpow.symm

theorem sixteen_mul_sq_le_two_pow_pred (p : ℕ) (hp : 14 ≤ p) : 16 * p ^ 2 ≤ 2 ^ (p - 1) := by
  have h := thirtytwo_mul_sq_le_two_pow p hp
  have h2 : 2 ^ p = 2 * 2 ^ (p - 1) := by
    rw [← pow_succ', show p - 1 + 1 = p by omega]
  have h3 : 2 * (16 * p ^ 2) ≤ 2 * 2 ^ (p - 1) := by
    rw [← h2]
    have e : 2 * (16 * p ^ 2) = 32 * p ^ 2 := by ring
    rw [e]; exact h
  exact Nat.le_of_mul_le_mul_left h3 (by norm_num)

theorem two_pow_pOf_pred_le (n : ℕ) (hn : N₀ ≤ n) : 2 ^ (pOf n - 1) ≤ n := by
  have h4 : 2 ^ Nat.log2 n ≤ n := by
    rw [Nat.log2_eq_log_two]; exact Nat.pow_log_le_self 2 (by unfold N₀ at hn; omega)
  have h5 : pOf n - 1 = Nat.log2 n := by unfold pOf; omega
  rw [h5]; exact h4

/-- `4p ≤ √n`. -/
theorem four_mul_pOf_le_sqrt (n : ℕ) (hn : N₀ ≤ n) : 4 * pOf n ≤ Nat.sqrt n := by
  have hp13 : 14 ≤ pOf n := fourteen_le_pOf n hn
  have h1 : 16 * pOf n ^ 2 ≤ 2 ^ (pOf n - 1) := sixteen_mul_sq_le_two_pow_pred _ hp13
  have h3 : 2 ^ (pOf n - 1) ≤ n := two_pow_pOf_pred_le n hn
  have h2 : (4 * pOf n) ^ 2 ≤ n := by
    have he : (4 * pOf n) ^ 2 = 16 * pOf n ^ 2 := by ring
    omega
  exact Nat.le_sqrt'.mpr h2

theorem four_mul_pOf_le_pow (n : ℕ) (hn : N₀ ≤ n) : 4 * pOf n ≤ 2 ^ (pOf n / 2) := by
  have hp13 : 14 ≤ pOf n := fourteen_le_pOf n hn
  have h1 : 16 * pOf n ^ 2 ≤ 2 ^ (pOf n - 1) := sixteen_mul_sq_le_two_pow_pred _ hp13
  have h2 : (4 * pOf n) ^ 2 ≤ (2 ^ (pOf n / 2)) ^ 2 := by
    have he : (4 * pOf n) ^ 2 = 16 * pOf n ^ 2 := by ring
    have hp : 2 ^ (pOf n - 1) ≤ (2 ^ (pOf n / 2)) ^ 2 := by
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp h2

theorem one_le_sqrt_of_two_pow (n : ℕ) (hn : N₀ ≤ n) : 1 ≤ Nat.sqrt n := by
  rw [Nat.le_sqrt']
  unfold N₀ at hn; omega

/-- `4p ≤ s`, so `s ≥ 3` and `s` is large compared with `p`. -/
theorem four_mul_pOf_le_sOf (n : ℕ) (hn : N₀ ≤ n) : 4 * pOf n ≤ sOf n := by
  have h1 : 4 * pOf n ≤ Nat.sqrt n + 1 := by
    have := four_mul_pOf_le_sqrt n hn; omega
  have h2 : 4 * pOf n ≤ 2 ^ (pOf n / 2) := four_mul_pOf_le_pow n hn
  exact le_min h1 h2

/-- `m ≤ n`. -/
theorem mOf_le_n (n : ℕ) (hn : N₀ ≤ n) : mOf n ≤ n := by
  have hp : 4 * pOf n ≤ Nat.sqrt n := four_mul_pOf_le_sqrt n hn
  have hs : sOf n ≤ Nat.sqrt n + 1 := sOf_le_sqrt n
  have hs1 : 1 ≤ Nat.sqrt n := one_le_sqrt_of_two_pow n hn
  have h1 : sOf n ≤ 2 * Nat.sqrt n := by omega
  calc mOf n = sOf n * pOf n := rfl
    _ ≤ (2 * Nat.sqrt n) * pOf n := Nat.mul_le_mul_right _ h1
    _ = 2 * pOf n * Nat.sqrt n := by ring
    _ ≤ Nat.sqrt n * Nat.sqrt n := by
        apply Nat.mul_le_mul_right
        omega
    _ ≤ n := Nat.sqrt_le n

/-- `2m ≤ n`, the hypothesis `m ≤ n - m` of Theorem 2 at `B.card = n - m`. -/
theorem two_mul_mOf_le_n (n : ℕ) (hn : N₀ ≤ n) : 2 * mOf n ≤ n := by
  have hp : 4 * pOf n ≤ Nat.sqrt n := four_mul_pOf_le_sqrt n hn
  have hs : sOf n ≤ Nat.sqrt n + 1 := sOf_le_sqrt n
  have hs1 : 1 ≤ Nat.sqrt n := one_le_sqrt_of_two_pow n hn
  have h1 : sOf n ≤ 2 * Nat.sqrt n := by omega
  calc 2 * mOf n = 2 * (sOf n * pOf n) := rfl
    _ = (2 * sOf n) * pOf n := by ring
    _ ≤ (4 * Nat.sqrt n) * pOf n := Nat.mul_le_mul_right _ (by omega)
    _ = Nat.sqrt n * (4 * pOf n) := by ring
    _ ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul_left _ hp
    _ ≤ n := Nat.sqrt_le n

/-- `s ≥ 6`. -/
theorem six_le_sOf (n : ℕ) (hn : N₀ ≤ n) : 6 ≤ sOf n := by
  have h := four_mul_pOf_le_sOf n hn
  have h1 : 14 ≤ pOf n := fourteen_le_pOf n hn
  omega

theorem one_le_mOf (n : ℕ) (hn : N₀ ≤ n) : 1 ≤ mOf n := by
  have h2 : 6 ≤ sOf n := six_le_sOf n hn
  have h1 : 1 ≤ pOf n := pOf_pos n
  unfold mOf
  nlinarith

/-- `s ≤ 2^p`: there are at least `s` nonzero field elements. -/
theorem sOf_le_two_pow (n : ℕ) : sOf n ≤ 2 ^ pOf n := by
  have h := sOf_sq_le n
  have h1 : 1 ≤ sOf n := sOf_pos n
  nlinarith

/-- The choice `k = ⌊s/2⌋ - 1` satisfies `2k + 2 ≤ s`. -/
theorem two_mul_kOf_add_two_le (n : ℕ) (hn : 2 ≤ sOf n) : 2 * kOf n + 2 ≤ sOf n := by
  unfold kOf
  have h1 : 1 ≤ sOf n / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  have h2 := Nat.div_mul_le_self (sOf n) 2
  omega

theorem two_le_kOf (n : ℕ) (hn : 6 ≤ sOf n) : 2 ≤ kOf n := by
  unfold kOf
  have h : 3 ≤ sOf n / 2 := (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  omega

/-! ## Part 2: the field `GF(2^p)`, its coordinates and the rows `r_s[α]`

The rows of `U` live in `GF(2^p)` before the expansion in a `GF(2)`-basis.  This part fixes the
field `Fld n = GF(2^p)`, a `GF(2)`-basis `coordBasis n`, the coordinate map `coords n` (a linear
equivalence onto `(Fin p → ZMod 2)`), and the Boolean row `rowVec n x` obtained by expanding
`x^1, …, x^s` in that basis.

The main result is `rowVec_linearIndependent_fin`: any `s` distinct nonzero elements of the
field give linearly independent rows.  This is the Vandermonde argument of the paper: the
matrix `(α_i^j)_{i,j}` is `diag(α) · V(α)`, where `V(α)` is the Vandermonde matrix of the
distinct elements `α_i`, and the coordinate expansion is injective and `GF(2)`-linear. -/

/-- The field `GF(2^p)` with `p = ⌈log₂ n⌉`. -/
abbrev Fld (n : ℕ) : Type := GaloisField 2 (pOf n)

noncomputable instance fintypeFld (n : ℕ) : Fintype (Fld n) := Fintype.ofFinite _

noncomputable instance decidableEqFld (n : ℕ) : DecidableEq (Fld n) := Classical.decEq _

/-- A fixed `GF(2)`-basis of `GF(2^p)`. -/
noncomputable def coordBasis (n : ℕ) : Basis (Fin (pOf n)) (ZMod 2) (Fld n) :=
  Module.finBasisOfFinrankEq (ZMod 2) (Fld n)
    (GaloisField.finrank 2 (n := pOf n) (pOf_pos n).ne')

/-- The coordinate vector of a field element in the fixed basis. -/
noncomputable def coords (n : ℕ) : Fld n ≃ₗ[ZMod 2] (Fin (pOf n) → ZMod 2) :=
  (coordBasis n).repr.trans (Finsupp.linearEquivFunOnFinite (ZMod 2) (ZMod 2) (Fin (pOf n)))

/-- The field has `2^p` elements. -/
theorem card_Fld (n : ℕ) : Fintype.card (Fld n) = 2 ^ pOf n := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 (n := pOf n) (pOf_pos n).ne']

theorem coords_injective (n : ℕ) : Function.Injective (coords n) := (coords n).injective

theorem coords_eq_zero_iff (n : ℕ) (x : Fld n) : coords n x = 0 ↔ x = 0 := by
  constructor
  · intro h; exact (coords n).injective (by rw [h, map_zero])
  · intro h; rw [h, map_zero]

/-- The coordinates of a basis element are the corresponding unit vector. -/
theorem coords_coordBasis (n : ℕ) (i : Fin (pOf n)) :
    coords n (coordBasis n i) = Pi.single i 1 := by
  simp [coords, Basis.repr_self]

/-- The `j`-th power block of the row `r_s[α]`, expanded in the fixed basis. -/
noncomputable def rowFun (n : ℕ) (x : Fld n) : Fin (sOf n) × Fin (pOf n) → ZMod 2 :=
  fun jc => coords n (x ^ (jc.1.1 + 1)) jc.2

/-- The row vector `r_s[α] = (α, α², …, α^s)` in Boolean form. -/
noncomputable def rowVec (n : ℕ) (x : Fld n) : Fin (sOf n * pOf n) → ZMod 2 :=
  fun k => rowFun n x (finProdFinEquiv.symm k)

@[simp] theorem rowVec_apply (n : ℕ) (x : Fld n) (j : Fin (sOf n)) (cc : Fin (pOf n)) :
    rowVec n x (finProdFinEquiv (j, cc)) = coords n (x ^ (j.1 + 1)) cc := by
  simp [rowVec, rowFun]

/-- The map `x ↦ r_s[x]` is injective: the first power block `x ↦ α` is already injective after
the coordinate expansion. -/
theorem rowVec_injective (n : ℕ) : Function.Injective (rowVec n) := by
  intro x y h
  apply coords_injective n
  funext cc
  have hpos : 0 < sOf n := sOf_pos n
  have := congrFun h (finProdFinEquiv (⟨0, hpos⟩, cc))
  simpa using this

/-- Every nonzero element produces a row of weight at least `s`: each of the `s` power blocks of
`r_s[α]` is the coordinate vector of a nonzero element, hence has a nonzero entry, and the
blocks are disjoint. -/
theorem weight_rowVec_ge (n : ℕ) {x : Fld n} (hx : x ≠ 0) :
    sOf n ≤ weight (Finset.univ : Finset (Fin (mOf n))) (rowVec n x) := by
  classical
  have hex : ∀ j : Fin (sOf n), ∃ cc : Fin (pOf n), coords n (x ^ (j.1 + 1)) cc ≠ 0 := by
    intro j
    by_contra h
    push Not at h
    have h0 : coords n (x ^ (j.1 + 1)) = 0 := funext h
    exact pow_ne_zero _ hx ((coords_eq_zero_iff n _).mp h0)
  choose cc hcc using hex
  have hinj : Function.Injective (fun j : Fin (sOf n) => finProdFinEquiv (j, cc j)) := by
    intro j j' h
    have := congrArg Prod.fst (finProdFinEquiv.injective h)
    simpa using this
  have hsub : (Finset.univ.image (fun j : Fin (sOf n) => finProdFinEquiv (j, cc j))) ⊆
      (Finset.univ : Finset (Fin (mOf n))).filter (fun k => rowVec n x k ≠ 0) := by
    intro k hk
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hcc j⟩
  have hcard : (Finset.univ.image (fun j : Fin (sOf n) => finProdFinEquiv (j, cc j))).card
      = sOf n := by
    rw [Finset.card_image_of_injective (s := Finset.univ) hinj, Finset.card_univ,
      Fintype.card_fin]
  have hle := Finset.card_le_card hsub
  unfold weight
  exact hcard ▸ hle

/-- The rows of `s` distinct nonzero field elements are linearly independent over `GF(2)`; this
is the Vandermonde argument of the paper (Lemma `block` of Section 6). -/
theorem rowVec_linearIndependent_fin (n : ℕ) {α : Fin (sOf n) → Fld n}
    (hinj : Function.Injective α) (hne : ∀ i, α i ≠ 0) :
    LinearIndependent (ZMod 2) (fun i => rowVec n (α i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hblock : ∀ j : Fin (sOf n), ∑ i, g i • α i ^ (j.1 + 1) = 0 := by
    intro j
    apply (coords n).injective
    funext cc
    have h := congrFun hg (finProdFinEquiv (j, cc))
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, rowVec_apply] at h
    have h2 : coords n (∑ i, g i • α i ^ (j.1 + 1)) cc = 0 := by
      rw [map_sum, Finset.sum_apply]
      simp only [map_smul, Pi.smul_apply]
      exact h
    simpa using h2
  let M : Matrix (Fin (sOf n)) (Fin (sOf n)) (Fld n) := fun i j => α i ^ (j.1 + 1)
  have hM : M = Matrix.diagonal α * Matrix.vandermonde α := by
    ext i j
    show α i ^ (j.1 + 1) = (Matrix.diagonal α * Matrix.vandermonde α) i j
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [Matrix.diagonal_apply, if_pos rfl, Matrix.vandermonde_apply, pow_succ]
      ring
    · intro b _ hb
      rw [Matrix.diagonal_apply, if_neg (Ne.symm hb), zero_mul]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hv : (Matrix.vandermonde α).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hdet : M.det ≠ 0 := by
    rw [hM, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hne i)) hv
  let cf : Fin (sOf n) → Fld n := fun i => algebraMap (ZMod 2) (Fld n) (g i)
  have hmv : M.transpose.mulVec cf = 0 := by
    funext j
    have hval : (M.transpose.mulVec cf) j =
        ∑ i, α i ^ (j.1 + 1) * algebraMap (ZMod 2) (Fld n) (g i) := by
      rfl
    rw [hval]
    simp only [Pi.zero_apply]
    rw [← hblock j]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Algebra.smul_def, mul_comm]
  have hcf : cf = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero (by rwa [Matrix.det_transpose]) hmv
  have h0 : algebraMap (ZMod 2) (Fld n) (g i) = 0 := by
    have := congrFun hcf i
    simpa [cf] using this
  exact (algebraMap (ZMod 2) (Fld n)).injective (by simpa using h0)

/-! ## Part 3: the matrix `U`

The matrix `U` has `n - m` rows, indexed by a set `A` of `n - m` distinct nonzero elements of
`GF(2^p)`, the row of `α ∈ A` being the Boolean row `r_s[α]` of Part 2.  This part constructs
`A` (`alphaSet`, with an enumeration `alphaOf`), the set `rowSet` of the rows and the matrix
`Umat` itself, and records the elementary properties used below: the rows are distinct and
nonzero (of weight at least `2`), and `rowSet` is exactly the set of rows of `Umat`.

For `n ≥ N₀` one has `p ≤ n - m` (`pOf_le_sub_mOf`), so `A` is built as the union of the fixed
`GF(2)`-basis `basisSet` with `n - m - p` further nonzero elements; consequently `A` spans
`GF(2^p)` over `GF(2)` (`alphaSet_span`).  This is what makes the first power block of every
column of `U` nonzero (`col_first_block`): the coordinate functional `α ↦ coords α cc` is
nonzero on the basis, hence on `A`.  For the remaining power blocks the analogous claim is not
automatic -- when `gcd(k, 2^p - 1) > 1` the `k`-th powers range over a proper subfield -- so `U`
may well have zero columns.  Part 3b deletes them. -/

/-- The nonzero field elements form a set of `2^p - 1` elements. -/
theorem card_erase_zero (n : ℕ) :
    ((Finset.univ : Finset (Fld n)).erase 0).card = 2 ^ pOf n - 1 := by
  rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, card_Fld]

/-- `n - m ≤ 2^p - 1`: there are enough nonzero field elements to label the rows. -/
theorem sub_mOf_le_card_erase (n : ℕ) :
    n - mOf n ≤ ((Finset.univ : Finset (Fld n)).erase 0).card := by
  rw [card_erase_zero n]
  have h : n < 2 ^ pOf n := n_lt_two_pow_pOf n
  omega

/-- `s ≤ n - m`: there are at least `s` row labels. -/
theorem sOf_le_sub_mOf (n : ℕ) (hn : N₀ ≤ n) : sOf n ≤ n - mOf n := by
  have hm : 2 * mOf n ≤ n := two_mul_mOf_le_n n hn
  have hs1 : 1 ≤ Nat.sqrt n := one_le_sqrt_of_two_pow n hn
  have hs : sOf n ≤ 2 * Nat.sqrt n := by have := sOf_le_sqrt n; omega
  have h4 : 4 ≤ Nat.sqrt n := by
    have h := four_mul_pOf_le_sqrt n hn
    have hp := fourteen_le_pOf n hn
    omega
  have hsq : Nat.sqrt n * Nat.sqrt n ≤ n := Nat.sqrt_le n
  have hhalf : 2 * Nat.sqrt n ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    nlinarith
  omega

/-- `p ≤ n - m`: the `p` coordinates of a field element fit among the row labels. -/
theorem pOf_le_sub_mOf (n : ℕ) (hn : N₀ ≤ n) : pOf n ≤ n - mOf n := by
  have h1 : 4 * pOf n ≤ sOf n := four_mul_pOf_le_sOf n hn
  have h2 : sOf n ≤ n - mOf n := sOf_le_sub_mOf n hn
  omega

/-- The image of the fixed `GF(2)`-basis: the `p` nonzero field elements that span `GF(2^p)`
over `GF(2)`. -/
noncomputable def basisSet (n : ℕ) : Finset (Fld n) :=
  (Finset.univ : Finset (Fin (pOf n))).image (coordBasis n)

theorem basisSet_card (n : ℕ) : (basisSet n).card = pOf n := by
  rw [basisSet, Finset.card_image_of_injective _ (coordBasis n).injective, Finset.card_univ,
    Fintype.card_fin]

theorem basisSet_subset (n : ℕ) :
    basisSet n ⊆ (Finset.univ : Finset (Fld n)).erase 0 := by
  intro x hx
  rw [basisSet, Finset.mem_image] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact Finset.mem_erase.mpr ⟨(coordBasis n).ne_zero i, Finset.mem_univ _⟩

theorem sub_sub_le_card_sdiff (n : ℕ) :
    (n - mOf n) - pOf n ≤
      (((Finset.univ : Finset (Fld n)).erase 0) \ basisSet n).card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (basisSet_subset n), basisSet_card,
    card_erase_zero n]
  have h : n - mOf n ≤ 2 ^ pOf n - 1 := by
    have hh := sub_mOf_le_card_erase n
    rw [card_erase_zero n] at hh
    exact hh
  omega

/-- `n - m - p` further row labels, chosen from the nonzero elements outside `basisSet`. -/
noncomputable def basisExtra (n : ℕ) : Finset (Fld n) :=
  Classical.choose (Finset.exists_subset_card_eq
    (s := ((Finset.univ : Finset (Fld n)).erase 0) \ basisSet n)
    (n := (n - mOf n) - pOf n) (sub_sub_le_card_sdiff n))

theorem basisExtra_subset (n : ℕ) :
    basisExtra n ⊆ ((Finset.univ : Finset (Fld n)).erase 0) \ basisSet n :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (s := ((Finset.univ : Finset (Fld n)).erase 0) \ basisSet n)
    (n := (n - mOf n) - pOf n) (sub_sub_le_card_sdiff n))).1

theorem basisExtra_card (n : ℕ) : (basisExtra n).card = (n - mOf n) - pOf n :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (s := ((Finset.univ : Finset (Fld n)).erase 0) \ basisSet n)
    (n := (n - mOf n) - pOf n) (sub_sub_le_card_sdiff n))).2

/-- A fallback set of `n - m` arbitrary nonzero elements, used when `p > n - m` (this case never
occurs for `n ≥ N₀`). -/
noncomputable def freeLabels (n : ℕ) : Finset (Fld n) :=
  Classical.choose (Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fld n)).erase 0)
    (n := n - mOf n) (sub_mOf_le_card_erase n))

theorem freeLabels_subset (n : ℕ) :
    freeLabels n ⊆ (Finset.univ : Finset (Fld n)).erase 0 :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fld n)).erase 0) (n := n - mOf n)
    (sub_mOf_le_card_erase n))).1

theorem freeLabels_card (n : ℕ) : (freeLabels n).card = n - mOf n :=
  (Classical.choose_spec (Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fld n)).erase 0) (n := n - mOf n)
    (sub_mOf_le_card_erase n))).2

/-- A set `A ⊆ GF(2^p) \ {0}` of `n - m` row labels.  When `p ≤ n - m` (always for `n ≥ N₀`)
it contains the fixed `GF(2)`-basis `basisSet`, hence spans `GF(2^p)` over `GF(2)`; the
remaining `n - m - p` labels are arbitrary nonzero elements outside the basis. -/
noncomputable def alphaSet (n : ℕ) : Finset (Fld n) :=
  if pOf n ≤ n - mOf n then basisSet n ∪ basisExtra n else freeLabels n

theorem alphaSet_subset (n : ℕ) :
    alphaSet n ⊆ (Finset.univ : Finset (Fld n)).erase 0 := by
  rw [alphaSet]
  split_ifs with h
  · exact Finset.union_subset (basisSet_subset n)
      (basisExtra_subset n |>.trans Finset.sdiff_subset)
  · exact freeLabels_subset n

theorem alphaSet_card (n : ℕ) : (alphaSet n).card = n - mOf n := by
  rw [alphaSet]
  split_ifs with h
  · have hd : Disjoint (basisSet n) (basisExtra n) :=
      Finset.disjoint_of_subset_right (basisExtra_subset n) Finset.disjoint_sdiff
    rw [Finset.card_union_of_disjoint hd, basisSet_card, basisExtra_card]
    omega
  · exact freeLabels_card n

/-- The fixed basis is contained in the set of row labels. -/
theorem basisSet_subset_alphaSet (n : ℕ) (hn : N₀ ≤ n) : basisSet n ⊆ alphaSet n := by
  have hp : pOf n ≤ n - mOf n := pOf_le_sub_mOf n hn
  rw [alphaSet, ite_eq_left hp]
  exact Finset.subset_union_left

/-- The row labels span `GF(2^p)` over `GF(2)`. -/
theorem alphaSet_span (n : ℕ) (hn : N₀ ≤ n) :
    Submodule.span (ZMod 2) (alphaSet n : Set (Fld n)) = ⊤ := by
  have hsub : Set.range (coordBasis n) ⊆ (alphaSet n : Set (Fld n)) := by
    rintro x ⟨i, rfl⟩
    exact basisSet_subset_alphaSet n hn (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hle : Submodule.span (ZMod 2) (Set.range (coordBasis n)) ≤
      Submodule.span (ZMod 2) (alphaSet n : Set (Fld n)) := Submodule.span_mono hsub
  rw [Basis.span_eq] at hle
  exact top_le_iff.mp hle

/-- Zero is not a row label. -/
theorem zero_not_mem_alphaSet (n : ℕ) : (0 : Fld n) ∉ alphaSet n := by
  intro hx
  have h := alphaSet_subset n hx
  rw [Finset.mem_erase] at h
  exact h.1 rfl

/-- An enumeration of the row labels. -/
noncomputable def alphaOf (n : ℕ) : Fin (n - mOf n) → Fld n :=
  fun i => ((alphaSet n).equivFin.symm (Fin.cast (alphaSet_card n).symm i)).1

theorem alphaOf_mem (n : ℕ) (i : Fin (n - mOf n)) : alphaOf n i ∈ alphaSet n :=
  ((alphaSet n).equivFin.symm (Fin.cast (alphaSet_card n).symm i)).2

theorem alphaOf_injective (n : ℕ) : Function.Injective (alphaOf n) := by
  intro i j h
  have h' : (alphaSet n).equivFin.symm (Fin.cast (alphaSet_card n).symm i)
      = (alphaSet n).equivFin.symm (Fin.cast (alphaSet_card n).symm j) := Subtype.ext h
  have h'' := (alphaSet n).equivFin.symm.injective h'
  exact Fin.ext (by simpa using congrArg Fin.val h'')

theorem alphaOf_ne_zero (n : ℕ) (i : Fin (n - mOf n)) : alphaOf n i ≠ 0 := by
  intro h
  exact zero_not_mem_alphaSet n (h ▸ alphaOf_mem n i)

/-- The enumeration exhausts the set of row labels. -/
theorem alphaSet_eq_image (n : ℕ) :
    (Finset.univ : Finset (Fin (n - mOf n))).image (alphaOf n) = alphaSet n := by
  apply Finset.ext
  intro x
  rw [Finset.mem_image]
  constructor
  · rintro ⟨i, -, rfl⟩; exact alphaOf_mem n i
  · intro hx
    refine ⟨Fin.cast (alphaSet_card n) ((alphaSet n).equivFin ⟨x, hx⟩), Finset.mem_univ _, ?_⟩
    have hcast : Fin.cast (alphaSet_card n).symm
        (Fin.cast (alphaSet_card n) ((alphaSet n).equivFin ⟨x, hx⟩))
        = (alphaSet n).equivFin ⟨x, hx⟩ := Fin.ext rfl
    show ((alphaSet n).equivFin.symm (Fin.cast (alphaSet_card n).symm
      (Fin.cast (alphaSet_card n) ((alphaSet n).equivFin ⟨x, hx⟩)))).1 = x
    rw [hcast]
    exact congrArg Subtype.val (Equiv.symm_apply_apply _ _)

/-- Every basis element occurs among the row labels. -/
theorem exists_alphaOf_eq (n : ℕ) (hn : N₀ ≤ n) (i : Fin (pOf n)) :
    ∃ r : Fin (n - mOf n), alphaOf n r = coordBasis n i := by
  have hx : coordBasis n i ∈ alphaSet n :=
    basisSet_subset_alphaSet n hn (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  rw [← alphaSet_eq_image n] at hx
  obtain ⟨r, -, hr⟩ := Finset.mem_image.mp hx
  exact ⟨r, hr⟩

/-- The set of rows of `U`, i.e. the set of the `n - m` vectors `r_s[α]`, `α ∈ A`. -/
noncomputable def rowSet (n : ℕ) : Finset (Vec (mOf n)) :=
  (Finset.univ : Finset (Fin (n - mOf n))).image (fun i => rowVec n (alphaOf n i))

@[simp] theorem mem_rowSet (n : ℕ) {v : Vec (mOf n)} :
    v ∈ rowSet n ↔ ∃ i : Fin (n - mOf n), rowVec n (alphaOf n i) = v := by
  simp [rowSet]

/-- `U` has exactly `n - m` distinct rows. -/
theorem rowSet_card (n : ℕ) : (rowSet n).card = n - mOf n := by
  rw [rowSet, Finset.card_image_of_injective (s := Finset.univ) (fun i j h =>
    alphaOf_injective n (rowVec_injective n h)), Finset.card_univ, Fintype.card_fin]

/-- **The matrix `U`** of Section 6: its `i`-th row is `r_s[α_i]`, the expansion of
`(α_i, α_i², …, α_i^s)` in the fixed `GF(2)`-basis, where `α_i` runs over the `n - m` row
labels `A`. -/
noncomputable def Umat (n : ℕ) : Matrix (Fin (n - mOf n)) (Fin (mOf n)) (ZMod 2) :=
  fun i j => rowVec n (alphaOf n i) j

theorem Umat_injective (n : ℕ) : Function.Injective (Umat n) := by
  intro i j h
  exact alphaOf_injective n (rowVec_injective n h)

/-- The rows of `U` are exactly the vectors of `rowSet`. -/
theorem rowSet_eq_image_Umat (n : ℕ) :
    rowSet n = (Finset.univ : Finset (Fin (n - mOf n))).image (Umat n) := rfl

/-- The rows of `U` are nonzero, with weight at least `s ≥ 6`. -/
theorem weight_Umat_row (n : ℕ) (hn : N₀ ≤ n) (i : Fin (n - mOf n)) :
    sOf n ≤ weight (Finset.univ : Finset (Fin (mOf n))) (Umat n i) :=
  weight_rowVec_ge n (alphaOf_ne_zero n i)

theorem weight_Umat_row_ge_two (n : ℕ) (hn : N₀ ≤ n) (i : Fin (n - mOf n)) :
    2 ≤ weight (Finset.univ : Finset (Fin (mOf n))) (Umat n i) :=
  calc 2 ≤ sOf n := by have h := six_le_sOf n hn; omega
    _ ≤ weight (Finset.univ : Finset (Fin (mOf n))) (Umat n i) := weight_Umat_row n hn i

/-- `U` has no zero rows, as required by the transposition principle. -/
theorem Umat_row_nonzero (n : ℕ) (hn : N₀ ≤ n) (i : Fin (n - mOf n)) :
    ∃ j, Umat n i j ≠ 0 := by
  by_contra h
  push Not at h
  have h0 : Umat n i = 0 := funext h
  have hw := weight_Umat_row_ge_two n hn i
  rw [h0] at hw
  simp [weight] at hw

/-- The columns of `U` in the first power block (`α¹`) are nonzero: the row label
`coordBasis n cc` has `cc`-th coordinate `1`. -/
theorem col_first_block (n : ℕ) (hn : N₀ ≤ n) (cc : Fin (pOf n)) :
    ∃ r : Fin (n - mOf n), Umat n r (finProdFinEquiv (⟨0, sOf_pos n⟩, cc)) ≠ 0 := by
  obtain ⟨r, hr⟩ := exists_alphaOf_eq n hn cc
  refine ⟨r, ?_⟩
  rw [Umat, hr, rowVec_apply, pow_one, coords_coordBasis]
  simp

/-! ## Part 3b: deleting the zero columns of `U`

The transposition principle `claim1` of Part 0 requires a matrix with no zero rows and no zero
columns.  The rows of `U` are nonzero (`Umat_row_nonzero`), and so are its columns in the first
power block (`col_first_block`); the columns in the power blocks `α^k` with `k ≥ 2`, however,
may vanish.

Zero rows and zero columns carry no information and create no complexity: a zero row is an
output that is computed for free, and a zero column means that the circuit has an additional
input variable which it never reads.  Accordingly `L` is not increased by deleting rows
(`chainComplexity_submatrix_le_rows`) nor by adding zero columns
(`chainComplexity_le_of_zero_cols`), so `L(U) ≤ L(U')`; dually a chain computing `Uᵀ` also
computes `(U')ᵀ`, whose rows are the rows of `Uᵀ` at the retained indices, hence
`L((U')ᵀ) ≤ L(Uᵀ)`.  The transposition principle `claim1` is then applied to `U'`, which has
neither zero rows nor zero columns, and the resulting bounds are transferred back to `U`. -/

/-! ### Deleting rows -/

/-- Deleting rows of a matrix cannot increase its additive complexity: a chain computes the
matrix row by row, so the same chain computes any submatrix obtained by selecting rows. -/
theorem chainComplexity_submatrix_le_rows {k k' m : ℕ}
    (A : Matrix (Fin k) (Fin m) (ZMod 2)) (g : Fin k' → Fin k) :
    chainComplexity (fun i j => A (g i) j) ≤ chainComplexity A := by
  rw [chainComplexity_eq_sInf]
  refine le_sInf_of_forall ?_ ?_
  · intro hs
    exact absurd hs (Set.nonempty_iff_ne_empty.mp (chainSet_nonempty A))
  · rintro l ⟨c, hL, hc⟩
    exact Nat.sInf_le ⟨c, hL, fun i => hc (g i)⟩

/-! ### Adding zero columns

Dually, adding a column of zeros to a matrix does not increase its additive complexity: a column
of zeros additionally computed means that the circuit has an extra input variable, which it
simply never reads, so a chain over the columns of the smaller matrix is padded with zeros in
the new coordinate.  Below, `padVec f` inserts zeros in the coordinates outside `range f`, and
`chainComplexity_le_of_zero_cols` states that `L` is not increased by passing from a matrix to
the matrix obtained by adding zero columns (in the dual form: `L` does not increase when rows
are deleted). -/

/-- Insert zeros in the coordinates outside `range f`. -/
noncomputable def padVec {m m' : ℕ} (f : Fin m' → Fin m) (v : Vec m') : Vec m :=
  fun i => if h : ∃ t, f t = i then v (Classical.choose h) else 0

theorem padVec_apply {m m' : ℕ} (f : Fin m' → Fin m) (hf : Function.Injective f)
    (v : Vec m') (t : Fin m') : padVec f v (f t) = v t := by
  unfold padVec
  have h : ∃ t', f t' = f t := ⟨t, rfl⟩
  rw [dif_pos h]
  exact congrArg v (hf (Classical.choose_spec h))

theorem padVec_apply_not_mem {m m' : ℕ} (f : Fin m' → Fin m) (v : Vec m') {i : Fin m}
    (hi : ∀ t, f t ≠ i) : padVec f v i = 0 := by
  unfold padVec
  rw [dif_neg]
  rintro ⟨t, ht⟩
  exact hi t ht

theorem padVec_basisVec {m m' : ℕ} (f : Fin m' → Fin m) (hf : Function.Injective f)
    (t : Fin m') : padVec f (basisVec t) = basisVec (f t) := by
  funext i
  by_cases hi : i = f t
  · subst hi
    rw [padVec_apply f hf, basisVec_apply, basisVec_apply]
    simp
  · rw [basisVec_apply, if_neg hi]
    by_cases hr : ∃ t', f t' = i
    · obtain ⟨t', ht'⟩ := hr
      rw [← ht', padVec_apply f hf, basisVec_apply]
      have hne : ¬ (t' = t) := fun h => hi (by rw [← ht', h])
      simp [hne]
    · exact padVec_apply_not_mem f _ (fun t' h => hr ⟨t', h⟩)

theorem padVec_zero {m m' : ℕ} (f : Fin m' → Fin m) : padVec f (0 : Vec m') = 0 := by
  funext i
  unfold padVec
  by_cases h : ∃ t, f t = i <;> simp [h]

theorem padVec_add {m m' : ℕ} (f : Fin m' → Fin m) (u v : Vec m') :
    padVec f (u + v) = padVec f u + padVec f v := by
  funext i
  unfold padVec
  by_cases h : ∃ t, f t = i
  · simp only [dif_pos h, Pi.add_apply]
  · simp only [dif_neg h, Pi.add_apply, add_zero]

theorem chainPool_padVec {m m' L : ℕ} (f : Fin m' → Fin m) (hf : Function.Injective f)
    (y : Fin L → Vec m') (k : ℕ) (hk : k ≤ L) (a : Fin m' ⊕ Fin k) :
    chainPool (fun j => padVec f (y j)) k hk (Sum.map f id a) = padVec f (chainPool y k hk a) := by
  cases a with
  | inl t => simp only [Sum.map_inl, chainPool]; exact (padVec_basisVec f hf t).symm
  | inr j => rfl

/-- **Adding zero columns does not increase the additive complexity.**  If the columns of `A`
outside `range f` vanish, then `A` is the matrix `A' = (i, t) ↦ A i (f t)` with `m - m'` zero
columns inserted, and any chain computing `A'` extends to a chain computing `A` by using the
new input variables as zeros. -/
theorem chainComplexity_le_of_zero_cols {k m m' : ℕ}
    (A : Matrix (Fin k) (Fin m) (ZMod 2)) (f : Fin m' → Fin m)
    (hf : Function.Injective f) (hzero : ∀ i j, (∀ t, f t ≠ j) → A i j = 0) :
    chainComplexity A ≤ chainComplexity (fun i t => A i (f t)) := by
  classical
  set A' : Matrix (Fin k) (Fin m') (ZMod 2) := fun i t => A i (f t) with hA'
  have hrow : ∀ i, A i = padVec f (A' i) := by
    intro i
    funext j
    by_cases hj : ∃ t, f t = j
    · obtain ⟨t, ht⟩ := hj
      rw [← ht, padVec_apply f hf, hA']
    · push Not at hj
      rw [padVec_apply_not_mem f _ hj, hzero i j hj]
  rw [chainComplexity_eq_sInf]
  refine le_sInf_of_forall ?_ ?_
  · intro hs
    exact absurd hs (Set.nonempty_iff_ne_empty.mp (chainSet_nonempty A'))
  · rintro l ⟨c, hL, hc⟩
    let c' : VecAddChain m :=
      { L := c.L
        y := fun j => padVec f (c.y j)
        valid := by
          intro j
          obtain ⟨a, b, hab⟩ := c.valid j
          refine ⟨Sum.map f id a, Sum.map f id b, ?_⟩
          rw [hab, padVec_add, chainPool_padVec f hf, chainPool_padVec f hf] }
    have hpad_mem : ∀ v : Vec m',
        v ∈ Set.range basisVec ∪ Set.range c.y ∪ ({0} : Set (Vec m')) →
        padVec f v ∈ Set.range basisVec ∪ Set.range c'.y ∪ ({0} : Set (Vec m)) := by
      intro v hv
      rcases hv with (⟨t, rfl⟩ | ⟨j, rfl⟩) | rfl
      · exact Set.mem_union_left _ (Set.mem_union_left _ ⟨f t, (padVec_basisVec f hf t).symm⟩)
      · exact Set.mem_union_left _ (Set.mem_union_right _ ⟨j, rfl⟩)
      · exact Set.mem_union_right _ (padVec_zero f)
    have hcomp' : c'.Computes A := by
      intro i
      rw [hrow i]
      exact hpad_mem (A' i) (hc i)
    exact Nat.sInf_le ⟨c', hL, hcomp'⟩

/-! ### The zero-column deletion `U'` of `U` -/

/-- The set of nonzero columns of `U`. -/
noncomputable def nzCols (n : ℕ) : Finset (Fin (mOf n)) :=
  Finset.univ.filter (fun j => ∃ i, Umat n i j ≠ 0)

@[simp] theorem mem_nzCols {n : ℕ} {j : Fin (mOf n)} :
    j ∈ nzCols n ↔ ∃ i, Umat n i j ≠ 0 := by
  simp [nzCols]

/-- The columns of `U` outside `nzCols` are zero. -/
theorem Umat_eq_zero_of_not_mem {n : ℕ} {j : Fin (mOf n)} (hj : j ∉ nzCols n)
    (i : Fin (n - mOf n)) : Umat n i j = 0 := by
  by_contra h
  exact hj (mem_nzCols.mpr ⟨i, h⟩)

/-- The number of nonzero columns of `U`. -/
noncomputable def nzCount (n : ℕ) : ℕ := (nzCols n).card

/-- The order embedding of the nonzero columns of `U` into the set of all columns. -/
noncomputable def nzColEmb (n : ℕ) : Fin (nzCount n) → Fin (mOf n) :=
  fun t => ((nzCols n).equivFin.symm t).1

theorem nzColEmb_mem (n : ℕ) (t : Fin (nzCount n)) : nzColEmb n t ∈ nzCols n :=
  ((nzCols n).equivFin.symm t).2

theorem nzColEmb_injective (n : ℕ) : Function.Injective (nzColEmb n) := by
  intro t t' h
  have h1 : (nzCols n).equivFin.symm t = (nzCols n).equivFin.symm t' := Subtype.ext h
  exact (nzCols n).equivFin.symm.injective h1

/-- The nonzero columns of `U` are exactly the range of `nzColEmb`. -/
theorem range_nzColEmb (n : ℕ) : Set.range (nzColEmb n) = (nzCols n : Set (Fin (mOf n))) := by
  ext j
  constructor
  · rintro ⟨t, rfl⟩
    exact nzColEmb_mem n t
  · intro hj
    exact ⟨(nzCols n).equivFin ⟨j, hj⟩,
      congrArg Subtype.val (Equiv.symm_apply_apply _ _)⟩

theorem nzCount_le (n : ℕ) : nzCount n ≤ mOf n := by
  unfold nzCount
  simpa using Finset.card_le_univ (nzCols n)

/-- **The matrix `U'`**: `U` with its zero columns deleted.  By construction every column of
`U'` is nonzero, and its rows are nonzero as the rows of `U` are. -/
noncomputable def UmatNz (n : ℕ) : Matrix (Fin (n - mOf n)) (Fin (nzCount n)) (ZMod 2) :=
  fun i t => Umat n i (nzColEmb n t)

theorem UmatNz_row_nonzero (n : ℕ) (hn : N₀ ≤ n) (i : Fin (n - mOf n)) :
    ∃ t, UmatNz n i t ≠ 0 := by
  obtain ⟨j, hj⟩ := Umat_row_nonzero n hn i
  have hmem : j ∈ Set.range (nzColEmb n) := by
    rw [range_nzColEmb]; exact mem_nzCols.mpr ⟨i, hj⟩
  obtain ⟨t, ht⟩ := hmem
  refine ⟨t, ?_⟩
  show Umat n i (nzColEmb n t) ≠ 0
  rw [ht]; exact hj

theorem UmatNz_col_nonzero (n : ℕ) (t : Fin (nzCount n)) :
    ∃ i, UmatNz n i t ≠ 0 := by
  obtain ⟨i, hi⟩ := mem_nzCols.mp (nzColEmb_mem n t)
  exact ⟨i, hi⟩

/-- Deleting the zero rows of `Uᵀ` does not increase its additive complexity. -/
theorem chainComplexity_transpose_UmatNz_le (n : ℕ) :
    chainComplexity (Matrix.transpose (UmatNz n)) ≤ chainComplexity (Matrix.transpose (Umat n)) :=
  chainComplexity_submatrix_le_rows (Matrix.transpose (Umat n)) (nzColEmb n)

/-! ## Part 4: the independence index of `U`

The rows of `U` form a Vandermonde-type matrix: any `s` of them are linearly independent by
`rowVec_linearIndependent_fin`.  Hence `ind U ≥ s`, the estimate quoted in the paper before
(6.1). -/

/-- Every `s`-element subset of `rowSet` is linearly independent. -/
theorem allIndep_rowSet (n : ℕ) : AllIndep (rowSet n) (sOf n) := by
  classical
  intro S hS hcard
  have hex : ∀ v : S, ∃ i : Fin (n - mOf n), rowVec n (alphaOf n i) = (v : Vec (mOf n)) :=
    fun v => (mem_rowSet n).mp (hS v.2)
  choose idx hidx using hex
  let e : S ≃ Fin (sOf n) := (Finset.equivFin S).trans (finCongr hcard)
  let β : Fin (sOf n) → Fld n := fun t => alphaOf n (idx (e.symm t))
  have hβinj : Function.Injective β := by
    intro t t' h
    have h1 : idx (e.symm t) = idx (e.symm t') := alphaOf_injective n h
    have h2 : (e.symm t : Vec (mOf n)) = (e.symm t' : Vec (mOf n)) := by
      rw [← hidx (e.symm t), ← hidx (e.symm t'), h1]
    exact e.symm.injective (Subtype.ext h2)
  have hβne : ∀ t, β t ≠ 0 := fun t => alphaOf_ne_zero n _
  have hLI := rowVec_linearIndependent_fin n hβinj hβne
  unfold Indep
  rw [Fintype.linearIndependent_iff] at hLI ⊢
  intro g hg
  have h1 : ∑ t : Fin (sOf n), g (e.symm t) • ((e.symm t : S) : Vec (mOf n)) = 0 := by
    rw [Equiv.sum_comp e.symm (fun v : S => g v • (v : Vec (mOf n)))]
    exact hg
  have h2 : ∑ t : Fin (sOf n), g (e.symm t) • rowVec n (β t) = 0 := by
    simpa [β, hidx] using h1
  intro v
  simpa using hLI (fun t => g (e.symm t)) h2 (e v)

/-- **`ind U ≥ s`** (Section 6 of the paper). -/
theorem ind_rowSet_ge (n : ℕ) (hn : N₀ ≤ n) : sOf n ≤ ind (rowSet n) :=
  le_ind (allIndep_rowSet n) (by rw [rowSet_card]; exact sOf_le_sub_mOf n hn)

/-! ### The sum criterion for linear independence -/

/-- In `GF(2)` every element is `0` or `1`. -/
theorem zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have h := ZMod.val_lt x
  have h' : x.val = 0 ∨ x.val = 1 := by omega
  rcases h' with h0 | h1
  · left; rw [← ZMod.natCast_zmod_val x, h0]; norm_num
  · right; rw [← ZMod.natCast_zmod_val x, h1]; norm_num

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

/-! ### From a chain computing `U` to a set of row vectors in the ambient space -/

section RowRep

variable {n K : ℕ}

/-- The vector of the chain `c` that represents the `i`-th row of `U`: one of the witnesses
provided by `ExtChain.Computes`. -/
noncomputable def rowRep (c : ExtChain K) {col : Fin (mOf n) → Fin K}
    (hcomp : c.Computes (Umat n) col) (i : Fin (n - mOf n)) : Vec K :=
  Classical.choose (ExtChain.exists_rep hcomp i)

theorem rowRep_mem (c : ExtChain K) {col : Fin (mOf n) → Fin K}
    (hcomp : c.Computes (Umat n) col) (i : Fin (n - mOf n)) :
    rowRep c hcomp i ∈ Set.range (basisVec (n := K)) ∪ Set.range c.y ∪ ({0} : Set (Vec K)) :=
  (Classical.choose_spec (ExtChain.exists_rep hcomp i)).1

theorem rowRep_row (c : ExtChain K) {col : Fin (mOf n) → Fin K}
    (hcomp : c.Computes (Umat n) col) (i : Fin (n - mOf n)) (j : Fin (mOf n)) :
    rowRep c hcomp i (col j) = Umat n i j :=
  (Classical.choose_spec (ExtChain.exists_rep hcomp i)).2.1 j

theorem rowRep_aux (c : ExtChain K) {col : Fin (mOf n) → Fin K}
    (hcomp : c.Computes (Umat n) col) (i : Fin (n - mOf n)) {j : Fin K} (hj : j ∈ c.aux) :
    rowRep c hcomp i j = 0 :=
  (Classical.choose_spec (ExtChain.exists_rep hcomp i)).2.2 j hj

/-- The finite set of row vectors of `U` inside the ambient space of the chain `c`. -/
noncomputable def rowRepSet (c : ExtChain K) {col : Fin (mOf n) → Fin K}
    (hcomp : c.Computes (Umat n) col) : Finset (Vec K) :=
  (Finset.univ : Finset (Fin (n - mOf n))).image (rowRep c hcomp)

@[simp] theorem mem_rowRepSet (c : ExtChain K) {col : Fin (mOf n) → Fin K}
    (hcomp : c.Computes (Umat n) col) {w : Vec K} :
    w ∈ rowRepSet c hcomp ↔ ∃ i : Fin (n - mOf n), rowRep c hcomp i = w := by
  simp [rowRepSet]

theorem rowRep_injective (c : ExtChain K) {col : Fin (mOf n) → Fin K}
    (hcomp : c.Computes (Umat n) col) : Function.Injective (rowRep c hcomp) := by
  intro i i' h
  have hrow : Umat n i = Umat n i' := by
    funext j
    rw [← rowRep_row c hcomp i j, ← rowRep_row c hcomp i' j, h]
  exact Umat_injective n hrow

/-- `rowRepSet` has one vector per row of `U`. -/
theorem rowRepSet_card (c : ExtChain K) {col : Fin (mOf n) → Fin K}
    (hcomp : c.Computes (Umat n) col) : (rowRepSet c hcomp).card = n - mOf n := by
  rw [rowRepSet, Finset.card_image_of_injective (s := Finset.univ) (rowRep_injective c hcomp),
    Finset.card_univ, Fintype.card_fin]

/-- The projection of an ambient vector to the columns of `U`. -/
def psi {n K : ℕ} (col : Fin (mOf n) → Fin K) (w : Vec K) : Vec (mOf n) := fun j => w (col j)

theorem psi_rowRep (c : ExtChain K) {col : Fin (mOf n) → Fin K}
    (hcomp : c.Computes (Umat n) col) (i : Fin (n - mOf n)) :
    psi col (rowRep c hcomp i) = Umat n i := by
  funext j
  exact rowRep_row c hcomp i j

theorem psi_add (col : Fin (mOf n) → Fin K) (u v : Vec K) : psi col (u + v) = psi col u + psi col v :=
  rfl

theorem psi_zero (col : Fin (mOf n) → Fin K) : psi col (0 : Vec K) = 0 := rfl

/-- `psi` is injective on `rowRepSet`. -/
theorem psi_injOn_rowRepSet (c : ExtChain K) {col : Fin (mOf n) → Fin K}
    (hcomp : c.Computes (Umat n) col) :
    ∀ a ∈ rowRepSet c hcomp, ∀ b ∈ rowRepSet c hcomp, psi col a = psi col b → a = b := by
  intro a ha b hb hab
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨i', -, rfl⟩ := Finset.mem_image.mp hb
  have hrow : Umat n i = Umat n i' := by
    rw [← psi_rowRep c hcomp i, ← psi_rowRep c hcomp i', hab]
  exact congrArg (rowRep c hcomp) (Umat_injective n hrow)

/-- The set `rowRepSet` is computed by the chain in the sense of Theorem 2. -/
theorem computesVecs_rowRepSet (c : ExtChain K) {col : Fin (mOf n) → Fin K}
    (hcomp : c.Computes (Umat n) col) : c.ComputesVecs (rowRepSet c hcomp) := by
  intro b hb
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
  refine ⟨?_, ?_⟩
  · funext j
    by_cases hj : j ∈ c.aux
    · rw [proj_apply_mem _ _ hj, rowRep_aux c hcomp i hj]
      simp
    · rw [proj_apply_not_mem _ _ hj]
      simp
  · have h := rowRep_mem c hcomp i
    simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at h ⊢
    tauto

/-- No vector of `rowRepSet` has weight `1`: its image under `psi` is a row of `U`, which has
weight at least `2`, and `psi` is injective on the columns. -/
theorem weight_rowRep_ne_one (hn : N₀ ≤ n) (c : ExtChain K) {col : Fin (mOf n) → Fin K}
    (hcomp : c.Computes (Umat n) col) (i : Fin (n - mOf n)) :
    weight (Finset.univ : Finset (Fin K)) (rowRep c hcomp i) ≠ 1 := by
  classical
  intro hw
  obtain ⟨d, hd⟩ := eq_basisVec_of_weight_univ_eq_one hw
  have hcol : Function.Injective col := hcomp.1
  have hsub : (Finset.univ.filter (fun j : Fin (mOf n) => Umat n i j ≠ 0)) ⊆
      Finset.univ.filter (fun j : Fin (mOf n) => col j = d) := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    by_contra hne
    apply hj.2
    have h1 : Umat n i j = basisVec d (col j) := by
      rw [← rowRep_row c hcomp i j, hd]
    rw [h1]
    simp [basisVec, hne]
  have hcard : (Finset.univ.filter (fun j : Fin (mOf n) => col j = d)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_filter] at ha hb
    exact hcol (ha.2.trans hb.2.symm)
  have hle : weight (Finset.univ : Finset (Fin (mOf n))) (Umat n i) ≤ 1 := by
    unfold weight
    exact le_trans (Finset.card_le_card hsub) hcard
  have hge := weight_Umat_row_ge_two n hn i
  omega

/-- **The independence index of the ambient row set is at least `s`.**  The vectors of
`rowRepSet` are the rows of `U` read in the ambient space of the chain; `psi` maps them
bijectively onto the rows of `U`, and independence is preserved by an injective linear map. -/
theorem ind_rowRepSet_ge (hn : N₀ ≤ n) (c : ExtChain K) {col : Fin (mOf n) → Fin K}
    (hcomp : c.Computes (Umat n) col) : sOf n ≤ ind (rowRepSet c hcomp) := by
  classical
  refine le_ind ?_ (by rw [rowRepSet_card]; exact sOf_le_sub_mOf n hn)
  intro S hSB hScard
  rw [indep_iff_sum_ne_zero]
  intro T hTne hsum
  set X : Finset (Vec (mOf n)) := T.image (fun x : ↥S => psi col (x : Vec K)) with hX
  have hinjT : Set.InjOn (fun x : ↥S => psi col (x : Vec K)) ↑T := by
    intro x _ y _ hxy
    have hxS : (x : Vec K) ∈ rowRepSet c hcomp := hSB x.2
    have hyS : (y : Vec K) ∈ rowRepSet c hcomp := hSB y.2
    exact Subtype.ext (psi_injOn_rowRepSet c hcomp _ hxS _ hyS hxy)
  have hXsub : X ⊆ rowSet n := by
    intro y hy
    rw [hX] at hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (hSB x.2)
    rw [← hi, psi_rowRep c hcomp i, rowSet_eq_image_Umat]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hXne : X.Nonempty := hTne.image _
  have hXsum : ∑ y ∈ X, y = 0 := by
    have h1 : ∑ x ∈ T, psi col (x : Vec K) = psi col (∑ x ∈ T, (x : Vec K)) := by
      funext j
      simp only [Finset.sum_apply, psi]
    rw [hX, Finset.sum_image hinjT, h1, hsum]
    funext j
    simp [psi]
  have hXcard : X.card = T.card := by
    rw [hX, Finset.card_image_of_injOn hinjT]
  have hXcardle : X.card ≤ sOf n := by
    rw [hXcard]
    calc T.card ≤ S.card := by
          simpa using Finset.card_le_univ T
      _ = sOf n := hScard
  have hXind : Indep X := Indep_of_subset_of_card_le hXsub hXcardle (ind_rowSet_ge n hn)
  exact hXne.ne_empty (Indep.sum_eq_zero hXind hXsum)

end RowRep


/-! ### The bound (6.1)

Theorem 2 is applied to the row set `B` of `U` read in the ambient space `Fin m` of the chain.
Its slack term is the ambient dimension, so the estimate it provides is the one for schemes
over the `m` columns of `U`, which is the model of the paper: there the ambient dimension of
`U` is `m` and the row set has `n - m` elements.  The numerical part is isolated in
`arith_core` below. -/

/-- Elementary exponential estimate: for `x > 0` and `r ≥ 0`,
`x^(1-r) ≥ x·(1 - r·log x)`. -/
theorem rpow_one_sub_ge {x r : ℝ} (hx : 0 < x) :
    x * (1 - r * Real.log x) ≤ x ^ (1 - r) := by
  have hexp : x ^ (1 - r) = x * Real.exp (-(r * Real.log x)) := by
    rw [Real.rpow_def_of_pos hx]
    have hsplit : Real.log x * (1 - r) = Real.log x + -(r * Real.log x) := by ring
    rw [hsplit, Real.exp_add, Real.exp_log hx]
  rw [hexp]
  have h : 1 - r * Real.log x ≤ Real.exp (-(r * Real.log x)) := by
    have h1 := Real.add_one_le_exp (-(r * Real.log x))
    linarith
  nlinarith [h, hx.le]

/-- Numerical core of (6.1).  If `2N - (6 + 4 log N)N/s - m ≤ L`, `N = n - m`,
`n ≤ 2s²`, `4P ≤ s`, `m = sP`, `log N ≤ P` and `2k + 2 ≤ s ≤ 2k + 3`, then
`2n ≤ L + 20m`.  All quantities are real numbers; the corresponding integer facts are
supplied by the caller. -/
theorem arith_core {n N P s k m L : ℝ}
    (hP : 2 ≤ P) (hs : 4 ≤ s) (hPs : 4 * P ≤ s)
    (hm : m = s * P) (hN : N = n - m) (hNn : N ≤ n) (hN1 : 1 ≤ N)
    (hn : n ≤ 2 * s ^ 2)
    (h2k : 2 * k + 2 ≤ s) (h2k' : s ≤ 2 * k + 3) (hk : 2 ≤ k)
    (hlog : Real.log N ≤ P)
    (hmain : N + ((2 * k - 2) / (2 * k + 1)) * N ^ (k / (k + 1)) - m ≤ L) :
    2 * n ≤ L + 20 * m := by
  have hs0 : 0 < s := by linarith
  have hNpos : 0 < N := by linarith
  have hnpos : 0 < n := by linarith
  have hlogpos : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hden1 : 0 < 2 * k + 1 := by linarith
  have hden2 : 0 < k + 1 := by linarith
  -- the coefficient `(2k-2)/(2k+1)` is at least `1 - 6/s`
  have hfrac : 3 / (2 * k + 1) ≤ 6 / s := by
    rw [div_le_div_iff₀ hden1 hs0]
    nlinarith
  have hA : 1 - 6 / s ≤ (2 * k - 2) / (2 * k + 1) := by
    have heq : (2 * k - 2) / (2 * k + 1) = 1 - 3 / (2 * k + 1) := by
      field_simp
      ring
    rw [heq]; linarith
  -- the exponent `k/(k+1)` is `1 - 1/(k+1)`, with `1/(k+1) ≤ 4/s`
  have hexp_form : k / (k + 1) = 1 - 1 / (k + 1) := by
    field_simp
    ring
  have hfrac2 : 1 / (k + 1) ≤ 4 / s := by
    rw [div_le_div_iff₀ hden2 hs0]
    nlinarith
  have hpow : N * (1 - (4 / s) * Real.log N) ≤ N ^ (k / (k + 1)) := by
    rw [hexp_form]
    have h1 := rpow_one_sub_ge (x := N) (r := 1 / (k + 1)) hNpos
    have h2 : (1 / (k + 1)) * Real.log N ≤ (4 / s) * Real.log N :=
      mul_le_mul_of_nonneg_right hfrac2 hlogpos
    have h3 : N * (1 - (4 / s) * Real.log N) ≤ N * (1 - (1 / (k + 1)) * Real.log N) := by
      nlinarith
    linarith
  have hnonneg : 0 ≤ N * (1 - (4 / s) * Real.log N) := by
    have h1 : (4 / s) * Real.log N ≤ (4 / s) * P :=
      mul_le_mul_of_nonneg_left hlog (div_nonneg (by norm_num) hs0.le)
    have h2 : (4 / s) * P ≤ 1 := by
      rw [show (4 / s) * P = (4 * P) / s by ring]
      exact (div_le_one hs0).mpr hPs
    nlinarith
  have hBnonneg : 0 ≤ (2 * k - 2) / (2 * k + 1) :=
    div_nonneg (by linarith) hden1.le
  -- combine the two lower bounds
  have h1 : (1 - 6 / s) * (N * (1 - (4 / s) * Real.log N)) ≤
      ((2 * k - 2) / (2 * k + 1)) * N ^ (k / (k + 1)) :=
    mul_le_mul hA hpow hnonneg hBnonneg
  have hid : (1 - 6 / s) * (N * (1 - (4 / s) * Real.log N)) =
      N - ((6 + 4 * Real.log N) / s) * N + (24 * Real.log N / s ^ 2) * N := by
    field_simp
    ring
  have hpos : 0 ≤ (24 * Real.log N / s ^ 2) * N :=
    mul_nonneg (div_nonneg (by linarith) (by positivity)) hNpos.le
  have hstep : 2 * N - ((6 + 4 * Real.log N) / s) * N - m ≤ L := by
    have h2 : N - ((6 + 4 * Real.log N) / s) * N ≤
        ((2 * k - 2) / (2 * k + 1)) * N ^ (k / (k + 1)) := by
      rw [hid] at h1
      linarith
    linarith
  -- `(6 + 4 log N)N/s ≤ 17m`
  have hNs : N ≤ 2 * s ^ 2 := le_trans hNn hn
  have hcoef : 6 + 4 * Real.log N ≤ 6 + 4 * P := by linarith
  have hNN : 0 ≤ 6 + 4 * Real.log N := by linarith
  have h1' : (6 + 4 * Real.log N) * N ≤ (6 + 4 * P) * (2 * s ^ 2) :=
    mul_le_mul hcoef hNs (le_of_lt hNpos) (by linarith)
  have h2' : (6 + 4 * P) * (2 * s ^ 2) ≤ 17 * m * s := by
    rw [hm]
    have hb : 12 + 8 * P ≤ 17 * P := by linarith
    calc (6 + 4 * P) * (2 * s ^ 2) = (12 + 8 * P) * s ^ 2 := by ring
      _ ≤ 17 * P * s ^ 2 := mul_le_mul_of_nonneg_right hb (sq_nonneg s)
      _ = 17 * (s * P) * s := by ring
  have hlog_final : ((6 + 4 * Real.log N) / s) * N ≤ 17 * m := by
    have h3 : (6 + 4 * Real.log N) * N ≤ 17 * m * s := le_trans h1' h2'
    rw [show ((6 + 4 * Real.log N) / s) * N = ((6 + 4 * Real.log N) * N) / s by ring]
    exact (div_le_iff₀ hs0).mpr h3
  have : 2 * n - 20 * m ≤ L := by nlinarith
  linarith

/-- **The bound (6.1)**, at the level of a single extended chain over the `m` columns of
`U`: `L*(c) ≥ 2n - 20m`.  This is the estimate obtained by applying Theorem 2 to the row set
of `U` (slack `m`, since the ambient space is `Fin m`). -/
theorem reducedComplexity_rowSet_ge (n : ℕ) (hn : N₀ ≤ n)
    (c : ExtChain (mOf n)) (col : Fin (mOf n) → Fin (mOf n))
    (hcomp : c.Computes (Umat n) col) :
    2 * n ≤ c.reducedComplexity + 20 * mOf n := by
  classical
  have hs6 : 6 ≤ sOf n := six_le_sOf n hn
  have hp14 : 14 ≤ pOf n := fourteen_le_pOf n hn
  have hm2 : 2 * mOf n ≤ n := two_mul_mOf_le_n n hn
  have hmlen : mOf n ≤ n := mOf_le_n n hn
  have hone : 1 ≤ mOf n := one_le_mOf n hn
  have hn1 : 1 ≤ n := by unfold N₀ at hn; omega
  have hsq : n ≤ 2 * sOf n ^ 2 := sOf_sq_ge n hn1
  set B : Finset (Vec (mOf n)) := rowRepSet c hcomp with hB
  have hBcard : B.card = n - mOf n := rowRepSet_card c hcomp
  have hNpos : 0 < n - mOf n := by omega
  have hcv : c.ComputesVecs B := computesVecs_rowRepSet c hcomp
  have hwt : ∀ b : Row B, weight (Finset.univ : Finset (Fin (mOf n))) b.1 ≠ 1 := by
    rintro ⟨b, hb⟩
    rw [mem_rowRepSet] at hb
    obtain ⟨i, rfl⟩ := hb
    exact weight_rowRep_ne_one hn c hcomp i
  have hk : 2 ≤ kOf n := two_le_kOf n hs6
  have hC0 : C0 c.aux false B = B := by simp [C0]
  have hind : 2 * kOf n + 2 ≤ ind (C0 c.aux false B) := by
    rw [hC0]
    exact le_trans (two_mul_kOf_add_two_le n (by omega)) (ind_rowRepSet_ge hn c hcomp)
  have hmB : mOf n ≤ B.card := by rw [hBcard]; omega
  have hmain := theorem2 c B false hcv hwt hk hind hmB
  have hslack : ((inputSlack c.aux false : ℕ) : ℝ) = (mOf n : ℝ) := by
    simp [inputSlack]
  rw [hslack] at hmain
  rw [hBcard] at hmain
  -- the logarithm of the row count is at most `p`
  have hlog : Real.log ((n - mOf n : ℕ) : ℝ) ≤ (pOf n : ℝ) := by
    have hNposR : (0 : ℝ) < ((n - mOf n : ℕ) : ℝ) := by exact_mod_cast hNpos
    have hNn : ((n - mOf n : ℕ) : ℝ) ≤ (n : ℝ) := by
      have := Nat.sub_le n (mOf n); exact_mod_cast this
    have hnposR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have h1 : Real.log ((n - mOf n : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log hNposR hNn
    have h2 : Real.log (n : ℝ) < (pOf n : ℝ) := by
      have hlt : (n : ℝ) < (2 : ℝ) ^ (pOf n) := by exact_mod_cast n_lt_two_pow_pOf n
      calc Real.log (n : ℝ) < Real.log ((2 : ℝ) ^ (pOf n)) := Real.log_lt_log hnposR hlt
        _ = (pOf n : ℝ) * Real.log 2 := Real.log_pow _ _
        _ ≤ (pOf n : ℝ) * 1 := by
            have h2 : Real.log (2 : ℝ) ≤ 1 := by
              have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
              linarith
            nlinarith
        _ = (pOf n : ℝ) := by ring
    linarith
  -- the relation `s ≤ 2k + 3`
  have h2k' : (sOf n : ℝ) ≤ 2 * (kOf n : ℝ) + 3 := by
    have h : sOf n ≤ 2 * kOf n + 3 := by
      unfold kOf
      have hdm := Nat.div_add_mod (sOf n) 2
      have hlt : sOf n % 2 < 2 := Nat.mod_lt _ (by norm_num : 0 < 2)
      omega
    exact_mod_cast h
  have hp2 : 2 ≤ pOf n := le_trans (by norm_num) (fourteen_le_pOf n hn)
  have hNge1 : 1 ≤ n - mOf n := hNpos
  have key := arith_core (n := (n : ℝ)) (N := ((n - mOf n : ℕ) : ℝ))
    (P := (pOf n : ℝ)) (s := (sOf n : ℝ)) (k := (kOf n : ℝ))
    (m := (mOf n : ℝ)) (L := (c.reducedComplexity : ℝ))
    (by exact_mod_cast hp2) (by exact_mod_cast (by omega : 4 ≤ sOf n))
    (by exact_mod_cast four_mul_pOf_le_sOf n hn)
    (by simp [mOf]) (by rw [Nat.cast_sub hmlen])
    (by have := Nat.sub_le n (mOf n); exact_mod_cast this)
    (by exact_mod_cast hNge1)
    (by exact_mod_cast hsq)
    (by exact_mod_cast two_mul_kOf_add_two_le n (by omega))
    h2k' (by exact_mod_cast hk) hlog hmain
  exact_mod_cast key

/-! ### The bound (6.1) for `L*`

The chain-level estimate `reducedComplexity_rowSet_ge` becomes an estimate on `L*(U)` once it is
applied to a chain whose reduced complexity realizes the minimum.  Such a chain is the formal
counterpart of the minimal extended scheme of the paper, which lives over the `m` columns of
`U`; the formal `Lstar` is an infimum over extended chains of *every* ambient dimension, so the
identification of the minimum with the reduced complexity of `c` is part of the data of the
corollaries below. -/

/-- **(6.1) for `L*`.**  If `c` is a reduced-complexity-minimal chain over the `m` columns of
`U`, then `2n ≤ L*(U) + 20m`: this is `reducedComplexity_rowSet_ge` read as an estimate on
`L*(U)` through the minimality of `c`. -/
theorem six_one_Umat (n : ℕ) (hn : N₀ ≤ n) (c : ExtChain (mOf n))
    (col : Fin (mOf n) → Fin (mOf n)) (hcomp : c.Computes (Umat n) col)
    (hmin : c.reducedComplexity = Lstar (Umat n)) :
    2 * n ≤ Lstar (Umat n) + 20 * mOf n := by
  have h := reducedComplexity_rowSet_ge n hn c col hcomp
  rw [hmin] at h
  exact h

/-! ## Part 6: Corollary 1 -/

/-! ### The matrix `A_U = Uᵀ ⊞ U` and the derived bound

Corollary 1 of Section 6 estimates the ordinary additive complexity of the direct sum
`A_U = Uᵀ ⊞ U` of the transpose of `U` with `U`, a matrix of size `n × n` (up to the
`Fin`-casts `m + (n - m) = n` in the two dimensions).  It is derived from three inputs: the
bound (6.1) for `U`, obtained from the chain-level estimate `reducedComplexity_rowSet_ge` for a
minimal chain over the `m` columns of `U` (`six_one_Umat`); the transposition principle
`claim1` applied to `U'`, the matrix obtained from `U` by deleting its zero columns; and the
block inequality `L(A₁ ⊞ A₂) ≥ L(A₁) + L*(A₂)` of Lemma 1 (`chainComplexity_dsum_ge`).  The
resulting estimate is `L(A_U) ≥ 5n - 42m`, which for `m = O(√n · log n)` is
`5n - O(√n · log n)`.

Concretely, let `nz` be the number of nonzero columns of `U` and `U'` the matrix obtained by
deleting the zero columns.  Then `L(Uᵀ) ≥ L((U')ᵀ) = L(U') + (n - m) - nz`, the equality being
the transposition principle for `U'`, and `L(U') ≥ L(U) ≥ L*(U) ≥ 2n - 20m`: the first
inequality holds because `U` is obtained from `U'` by adding zero columns, which does not
increase `L` (`chainComplexity_le_of_zero_cols`), and the last one is (6.1).  Adding this to
the lower bound `L*(U) ≥ 2n - 20m` for the second summand of `A_U` and using `nz ≤ m` gives
`L(A_U) ≥ 5n - 42m`.

The input (6.1) is not an abstract hypothesis: it is derived below from Theorem 2 of Section 5,
in the form of the chain-level estimate `reducedComplexity_rowSet_ge`, applied to the minimal
extended scheme of `U`.  That scheme lives over the `m` columns of `U` -- the model of the
paper -- and `hmin` records that its reduced complexity equals the minimum `L*(U)`. -/

/-- **Corollary 1** of Section 6: `L(A_U) ≥ 5n - 42m` for `A_U = Uᵀ ⊞ U`.

The hypotheses are those of the chain-level bound (6.1), `reducedComplexity_rowSet_ge`, for a
chain `c` over the `m` columns of `U`, together with `hmin`, which says that `c` realizes the
minimum `L*(U)`.  The estimate `2n ≤ L*(U) + 20m` is then obtained in `six_one_Umat` by
applying that theorem to `c`.

No hypothesis on the columns of `U` itself is needed: `claim1` is applied to `U'`, which has no
zero rows and no zero columns, and the bounds are transferred back to `U` using that deleting
zero columns does not increase `L` nor the complexity of the transpose
(`chainComplexity_le_of_zero_cols`, `chainComplexity_transpose_UmatNz_le`). -/
theorem corollary1 (n : ℕ) (hn : N₀ ≤ n) (c : ExtChain (mOf n))
    (col : Fin (mOf n) → Fin (mOf n)) (hcomp : c.Computes (Umat n) col)
    (hmin : c.reducedComplexity = Lstar (Umat n)) :
    5 * n ≤ chainComplexity (dsum (Matrix.transpose (Umat n)) (Umat n)) + 42 * mOf n := by
  classical
  -- the block inequality `L(Uᵀ) + L*(U) ≤ L(A_U)`
  have hblock : chainComplexity (Matrix.transpose (Umat n)) + Lstar (Umat n) ≤
      chainComplexity (dsum (Matrix.transpose (Umat n)) (Umat n)) :=
    chainComplexity_dsum_ge (Matrix.transpose (Umat n)) (Umat n)
  -- `L(Uᵀ) ≥ L((U')ᵀ)`: deleting the zero rows of `Uᵀ` cannot increase the complexity
  have htr_le := chainComplexity_transpose_UmatNz_le n
  -- the transposition principle for `U'`, which has no zero rows and no zero columns
  have htr := claim1 (UmatNz n) (UmatNz_row_nonzero n hn) (UmatNz_col_nonzero n)
  -- `L(U) ≤ L(U')`: adding the zero columns back to `U'` cannot increase `L`
  have hLU : chainComplexity (Umat n) ≤ chainComplexity (UmatNz n) := by
    have hzero : ∀ i (j : Fin (mOf n)), (∀ t, nzColEmb n t ≠ j) → Umat n i j = 0 :=
      fun i j hj => Umat_eq_zero_of_not_mem (by
        change j ∉ (nzCols n : Set (Fin (mOf n)))
        rw [← range_nzColEmb]
        simpa [Set.mem_range] using hj) i
    exact chainComplexity_le_of_zero_cols (Umat n) (nzColEmb n) (nzColEmb_injective n) hzero
  -- (6.1) applied to the minimal chain `c`
  have hsix := six_one_Umat n hn c col hcomp hmin
  -- `L*(U) ≤ L(U)`
  have hLC := Lstar_le_chainComplexity (Umat n)
  have hnzle : nzCount n ≤ mOf n := nzCount_le n
  omega

/-! ## Part 7: Claim 5 and Corollary 2 -/

/-! ### The all-ones matrix and the prefix chain -/

/-- The vector with `1` in the coordinates `0, …, k` and `0` elsewhere. -/
noncomputable def prefixVec (n k : ℕ) : Vec n := fun i => if i.val ≤ k then (1 : ZMod 2) else 0

theorem prefixVec_one (n : ℕ) (hn : 1 < n) :
    prefixVec n 1 = basisVec ⟨0, by omega⟩ + basisVec ⟨1, hn⟩ := by
  funext i
  show (if i.val ≤ 1 then (1 : ZMod 2) else 0) =
    (if i = ⟨0, by omega⟩ then 1 else 0) + (if i = ⟨1, hn⟩ then 1 else 0)
  by_cases h : i.val ≤ 1
  · rcases Nat.eq_or_lt_of_le h with he | hlt
    · have hie : i = ⟨1, hn⟩ := Fin.ext (by omega)
      have hne : i ≠ ⟨0, by omega⟩ := by
        intro hh; have := congrArg Fin.val hh; simp at this; omega
      simp [h, hie, hne]
    · have hi0 : i.val = 0 := by omega
      have hie : i = ⟨0, by omega⟩ := Fin.ext hi0
      have hne : i ≠ ⟨1, hn⟩ := by
        intro hh; have := congrArg Fin.val hh; simp at this; omega
      simp [h, hie, hne]
  · have hne0 : i ≠ ⟨0, by omega⟩ := by
      intro hh; have := congrArg Fin.val hh; simp at this; omega
    have hne1 : i ≠ ⟨1, hn⟩ := by
      intro hh; have := congrArg Fin.val hh; simp at this; omega
    simp [h, hne0, hne1]

theorem prefixVec_succ (n t : ℕ) (ht : t + 1 < n) :
    prefixVec n (t + 1) = prefixVec n t + basisVec ⟨t + 1, ht⟩ := by
  funext i
  show (if i.val ≤ t + 1 then (1 : ZMod 2) else 0) =
    (if i.val ≤ t then 1 else 0) + (if i = ⟨t + 1, ht⟩ then 1 else 0)
  by_cases h : i.val ≤ t
  · have hne : i ≠ ⟨t + 1, ht⟩ := by
      intro hh; have := congrArg Fin.val hh; simp at this; omega
    have h' : i.val ≤ t + 1 := by omega
    simp [h, h', hne]
  · by_cases h' : i.val ≤ t + 1
    · have he : i.val = t + 1 := by omega
      have hie : i = ⟨t + 1, ht⟩ := Fin.ext he
      rw [hie]
      simp
    · have hne : i ≠ ⟨t + 1, ht⟩ := by
        intro hh; have := congrArg Fin.val hh; simp at this; omega
      simp [h, h', hne]

/-- The prefix-sum chain: `y k = e₀ + … + e_{k+1}`. -/
noncomputable def prefixChain (n : ℕ) : VecAddChain n where
  L := n - 1
  y := fun k => prefixVec n (k.val + 1)
  valid := by
    intro k
    by_cases hk : k.val = 0
    · have hn1 : 1 < n := by have := k.2; omega
      refine ⟨Sum.inl ⟨0, by omega⟩, Sum.inl ⟨1, hn1⟩, ?_⟩
      have hy : prefixVec n (k.val + 1) = prefixVec n 1 := by rw [hk]
      rw [hy, prefixVec_one n hn1]
      rfl
    · have hk1 : 1 ≤ k.val := by omega
      have hkm : k.val - 1 < k.val := by omega
      have hkn : k.val + 1 < n := by have := k.2; omega
      refine ⟨Sum.inr ⟨k.val - 1, hkm⟩, Sum.inl ⟨k.val + 1, hkn⟩, ?_⟩
      have hk1' : 1 ≤ k.val := hk1
      have hstep := prefixVec_succ n k.val hkn
      simpa [chainPool, Nat.sub_add_cancel hk1'] using hstep

theorem one_eq_prefixVec_last (n : ℕ) (j : Fin n) :
    (1 : ZMod 2) = prefixVec n (n - 1) j := by
  show (1 : ZMod 2) = (if j.val ≤ n - 1 then 1 else 0)
  rw [if_pos (by omega)]

/-! ### Substituting a single variable: the live subchain

We implement the surgery behind Claim 5: substituting `0` for one essential variable `p`, then
keeping only the gates that are not already available after the substitution. -/

section SubstOne

variable {m : ℕ}

/-- Substituting `0` for the coordinate `p`. -/
def subst1 (p : Fin m) (v : Vec m) : Vec m := proj ({p}ᶜ) v

theorem subst1_apply_ne {p i : Fin m} (h : i ≠ p) (v : Vec m) : subst1 p v i = v i := by
  unfold subst1
  rw [proj_apply_mem]
  simpa using h

theorem subst1_apply_self (p : Fin m) (v : Vec m) : subst1 p v p = 0 := by
  unfold subst1
  rw [proj_apply_not_mem]
  simp

theorem subst1_add (p : Fin m) (u v : Vec m) : subst1 p (u + v) = subst1 p u + subst1 p v :=
  proj_add _ u v

theorem subst1_zero (p : Fin m) : subst1 p (0 : Vec m) = 0 := proj_zero _

theorem subst1_basisVec (p : Fin m) (i : Fin m) :
    subst1 p (basisVec i) = if i = p then 0 else basisVec i := by
  unfold subst1
  rw [proj_basisVec]
  by_cases h : i = p
  · subst h
    simp
  · have hmem : i ∈ ({p}ᶜ : Finset (Fin m)) := by
      simp [Finset.mem_compl]
      exact h
    rw [if_pos hmem, if_neg h]

/-- The values already available before the `k`-th gate once `p` has been substituted. -/
def avail1 (c : ExtChain m) (p : Fin m) (k : Fin c.L) (v : Vec m) : Prop :=
  v = 0 ∨ (∃ i : Fin m, i ≠ p ∧ v = basisVec i) ∨
    ∃ j : Fin c.L, j.1 < k.1 ∧ v = subst1 p (c.y j)

/-- A gate is cancelled by substituting `p` when its substituted value was already available. -/
def dead1 (c : ExtChain m) (p : Fin m) (k : Fin c.L) : Prop :=
  avail1 c p k (subst1 p (c.y k))

/-- The gates that survive the substitution of `p`. -/
noncomputable def live1 (c : ExtChain m) (p : Fin m) : Finset (Fin c.L) := by
  classical
  exact Finset.univ.filter (fun k => ¬ dead1 c p k)

theorem mem_live1 {c : ExtChain m} {p : Fin m} {k : Fin c.L} :
    k ∈ live1 c p ↔ ¬ dead1 c p k := by
  classical
  simp [live1]

section SubstLive

variable (c : ExtChain m) (p : Fin m)

theorem subst1_pool_inl (k : Fin c.L) (i : Fin m) :
    subst1 p (chainPool c.y k.1 (le_of_lt k.2) (Sum.inl i)) =
      (if i = p then 0 else basisVec i) :=
  subst1_basisVec p i

theorem subst1_pool_inr (k : Fin c.L) (j : Fin k.1) :
    subst1 p (chainPool c.y k.1 (le_of_lt k.2) (Sum.inr j)) =
      subst1 p (c.y ⟨j.1, lt_of_lt_of_le j.2 (le_of_lt k.2)⟩) := rfl

theorem avail1_slot (k : Fin c.L) (x : Fin m ⊕ Fin k.1) :
    avail1 c p k (subst1 p (chainPool c.y k.1 (le_of_lt k.2) x)) := by
  cases x with
  | inl i =>
    rw [subst1_pool_inl]
    by_cases h : i = p
    · exact Or.inl (by rw [if_pos h])
    · exact Or.inr (Or.inl ⟨i, h, by rw [if_neg h]⟩)
  | inr j =>
    rw [subst1_pool_inr]
    exact Or.inr (Or.inr ⟨⟨j.1, lt_of_lt_of_le j.2 (le_of_lt k.2)⟩, j.2, rfl⟩)

/-- Every substituted gate value is either trivial (zero or a surviving variable) or the
substituted value of a *live* gate, no later than the gate itself. -/
theorem exists_live_or_trivial (j : Fin c.L) :
    subst1 p (c.y j) = 0 ∨
      (∃ i : Fin m, i ≠ p ∧ subst1 p (c.y j) = basisVec i) ∨
      ∃ j' : Fin c.L, j' ∈ live1 c p ∧ j'.1 ≤ j.1 ∧ subst1 p (c.y j') = subst1 p (c.y j) := by
  classical
  rcases j with ⟨n, hn⟩
  revert hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hdead : dead1 c p ⟨n, hn⟩
    · unfold dead1 avail1 at hdead
      rcases hdead with h0 | ⟨i, hi, hb⟩ | ⟨j', hj'lt, hjeq⟩
      · exact Or.inl h0
      · exact Or.inr (Or.inl ⟨i, hi, hb⟩)
      · rcases ih j'.1 hj'lt j'.2 with h0 | ⟨i, hi, hb⟩ | ⟨j'', hmem, hle, heq⟩
        · exact Or.inl (hjeq.trans h0)
        · exact Or.inr (Or.inl ⟨i, hi, hjeq.trans hb⟩)
        · exact Or.inr (Or.inr ⟨j'', hmem, le_trans hle hj'lt.le, heq.trans hjeq.symm⟩)
    · exact Or.inr (Or.inr ⟨⟨n, hn⟩, by rw [mem_live1]; exact hdead, le_refl _, rfl⟩)

/-- The vectors of the live subchain. -/
noncomputable def liveY : Fin (live1 c p).card → Vec m :=
  fun t => subst1 p (c.y ((live1 c p).orderEmbOfFin rfl t))

theorem live_orderEmb_lt_iff (t t' : Fin (live1 c p).card) :
    (live1 c p).orderEmbOfFin rfl t < (live1 c p).orderEmbOfFin rfl t' ↔ t < t' :=
  (live1 c p).orderEmbOfFin rfl |>.lt_iff_lt

/-- The live subchain is a valid vector addition chain. -/
theorem liveChain_valid :
    ∀ t : Fin (live1 c p).card,
      ∃ a b : Fin m ⊕ Fin t.1,
        liveY c p t = chainPool (liveY c p) t.1 (le_of_lt t.2) a +
          chainPool (liveY c p) t.1 (le_of_lt t.2) b := by
  classical
  intro t
  let K : Fin c.L := (live1 c p).orderEmbOfFin rfl t
  have hKmem : K ∈ live1 c p := Finset.orderEmbOfFin_mem _ _ t
  have hKlive : ¬ dead1 c p K := mem_live1.mp hKmem
  obtain ⟨a, b, hab⟩ := c.valid K
  have hsplit : subst1 p (c.y K) = subst1 p (chainPool c.y K.1 (le_of_lt K.2) a) +
      subst1 p (chainPool c.y K.1 (le_of_lt K.2) b) := by
    rw [hab, subst1_add]
  have key : ∀ x : Fin m ⊕ Fin K.1,
      subst1 p (chainPool c.y K.1 (le_of_lt K.2) x) ≠ 0 →
      ∃ x' : Fin m ⊕ Fin t.1,
        chainPool (liveY c p) t.1 (le_of_lt t.2) x' =
          subst1 p (chainPool c.y K.1 (le_of_lt K.2) x) := by
    intro x hx
    cases x with
    | inl i =>
      rw [subst1_pool_inl] at hx ⊢
      refine ⟨Sum.inl i, ?_⟩
      show basisVec i = (if i = p then 0 else basisVec i)
      by_cases h : i = p
      · rw [if_pos h] at hx; exact absurd rfl hx
      · rw [if_neg h]
    | inr j =>
      rw [subst1_pool_inr] at hx ⊢
      rcases exists_live_or_trivial c p ⟨j.1, lt_of_lt_of_le j.2 (le_of_lt K.2)⟩ with
        h0 | ⟨i, hi, hb⟩ | ⟨j'', hmem, hle, heq⟩
      · exact absurd h0 hx
      · refine ⟨Sum.inl i, ?_⟩
        show basisVec i = _
        rw [hb]
      · have hrange : j'' ∈ Set.range ((live1 c p).orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]
          exact hmem
        obtain ⟨t', ht'⟩ := hrange
        have hlt : t' < t := by
          rw [← live_orderEmb_lt_iff]
          rw [ht']
          exact lt_of_le_of_lt hle j.2
        have hcard : t'.1 < (live1 c p).card := lt_of_lt_of_le hlt (le_of_lt t.2)
        refine ⟨Sum.inr ⟨t'.1, hlt⟩, ?_⟩
        show liveY c p ⟨t'.1, hcard⟩ =
          subst1 p (chainPool c.y K.1 (le_of_lt K.2) (Sum.inr j))
        rw [subst1_pool_inr]
        show subst1 p (c.y ((live1 c p).orderEmbOfFin rfl ⟨t'.1, hcard⟩)) = _
        rw [show (⟨t'.1, hcard⟩ : Fin (live1 c p).card) = t' from Fin.ext rfl, ht']
        exact heq
  have hane : subst1 p (chainPool c.y K.1 (le_of_lt K.2) a) ≠ 0 := by
    intro h0
    exact hKlive (by
      show avail1 c p K (subst1 p (c.y K))
      rw [hsplit, h0, zero_add]
      exact avail1_slot c p K b)
  have hbne : subst1 p (chainPool c.y K.1 (le_of_lt K.2) b) ≠ 0 := by
    intro h0
    exact hKlive (by
      show avail1 c p K (subst1 p (c.y K))
      rw [hsplit, h0, add_zero]
      exact avail1_slot c p K a)
  obtain ⟨a', ha'⟩ := key a hane
  obtain ⟨b', hb'⟩ := key b hbne
  refine ⟨a', b', ?_⟩
  show subst1 p (c.y K) = _
  rw [ha', hb']
  exact hsplit

end SubstLive

end SubstOne


section Claim5

variable {m : ℕ}

/-! ### Claim 5: the all-ones matrix has reduced complexity `l - 1`

The paper's Claim 5 states `L*(1_{1×n}) = L(1_{1×n}) = n - 1`.  We prove it for the `k × l`
all-ones matrix with `k ≥ 1`: all rows are equal, so only the single all-ones vector has to be
computed.

The lower bound rests on a substitution argument.  If an extended chain computes the all-ones
functional on a set `C` of coordinates, then substituting `0` for a coordinate `p ∈ C` cancels
the gate at which `p` is first attached: its substituted value becomes available earlier.  The
cancelled gate's type either has weight at most one -- and then is not counted in `typeSet` --
or coincides with the type of the gate attached to its other input, so no type is lost.  Hence
`#(gates) - #(types)` drops by at least one while `#(coordinates)` drops by exactly one. -/

/-- The `k × l` matrix all of whose entries are `1`. -/
def onesMat (k l : ℕ) : Matrix (Fin k) (Fin l) (ZMod 2) := fun _ _ => 1

/-! #### The prefix chain computes the all-ones matrix -/

theorem computes_onesMat (k l : ℕ) (hk : 1 ≤ k) :
    (ExtChain.ofChain (prefixChain l) ∅).Computes (onesMat k l) id := by
  refine ⟨Function.injective_id, ?_, ?_⟩
  · intro j; simp [ExtChain.ofChain]
  · intro i
    match l with
    | 0 => exact ⟨0, Or.inr (by simp), fun j => Fin.elim0 j, fun j => by simp [ExtChain.ofChain]⟩
    | 1 =>
      refine ⟨basisVec ⟨0, by omega⟩, Or.inl (Or.inl ⟨⟨0, by omega⟩, rfl⟩), ?_, ?_⟩
      · intro j
        have hj : j = ⟨0, by omega⟩ := Fin.ext (by omega)
        rw [hj]
        simp [onesMat, basisVec]
      · intro j hj
        simp [ExtChain.ofChain] at hj
    | (t + 2) =>
      refine ⟨prefixVec (t + 2) (t + 1), Or.inl (Or.inr ⟨⟨t, ?_⟩, ?_⟩), ?_, ?_⟩
      · show t < (t + 2) - 1
        omega
      · rfl
      · intro j
        exact (one_eq_prefixVec_last (t + 2) j).symm
      · intro j hj
        simp [ExtChain.ofChain] at hj

theorem Lstar_onesMat_le (k l : ℕ) (hk : 1 ≤ k) : Lstar (onesMat k l) ≤ l - 1 := by
  have h := Lstar_le_of_computes (ExtChain.ofChain (prefixChain l) ∅) id (computes_onesMat k l hk)
  rw [ExtChain.reducedComplexity_aux_empty] at h
  simpa [prefixChain] using h

theorem computes_onesMat_chain (k l : ℕ) (hk : 1 ≤ k) :
    (prefixChain l).Computes (onesMat k l) := by
  intro i
  obtain ⟨w, hw, hrow, -⟩ := (computes_onesMat k l hk).2.2 i
  have hw' : onesMat k l i = w := funext fun j => (hrow j).symm
  rw [hw']
  simpa [ExtChain.ofChain] using hw

theorem chainComplexity_onesMat_le (k l : ℕ) (hk : 1 ≤ k) :
    chainComplexity (onesMat k l) ≤ l - 1 := by
  rw [chainComplexity_eq_sInf]
  exact Nat.sInf_le ⟨prefixChain l, rfl, computes_onesMat_chain k l hk⟩

/-! #### Substitution does not change the type -/

/-- Zeroing the coordinate `p` does not change the projection onto any set not containing `p`. -/
theorem proj_subst1 (aux : Finset (Fin m)) (p : Fin m) (hp : p ∉ aux) (v : Vec m) :
    proj aux (subst1 p v) = proj aux v := by
  have hsub : aux ⊆ ({p}ᶜ : Finset (Fin m)) := by
    intro i hi
    simp only [Finset.mem_compl, Finset.mem_singleton]
    exact fun hip => hp (hip ▸ hi)
  simpa [subst1] using proj_proj_of_subset hsub v

/-- Zeroing the coordinate `p` does not change the weight counted on a set not containing `p`. -/
theorem weight_subst1 (aux : Finset (Fin m)) (p : Fin m) (hp : p ∉ aux) (v : Vec m) :
    weight aux (subst1 p v) = weight aux v := by
  have hsub : aux ⊆ ({p}ᶜ : Finset (Fin m)) := by
    intro i hi
    simp only [Finset.mem_compl, Finset.mem_singleton]
    exact fun hip => hp (hip ▸ hi)
  simpa [subst1] using weight_proj_of_subset hsub v

/-- The live subchain, read as an extended chain with the same inessential variables. -/
noncomputable abbrev liveExt (c : ExtChain m) (p : Fin m) : ExtChain m where
  L := (live1 c p).card
  y := liveY c p
  valid := liveChain_valid c p
  aux := c.aux

@[simp] theorem liveExt_L (c : ExtChain m) (p : Fin m) :
    (liveExt c p).L = (live1 c p).card := rfl

@[simp] theorem liveExt_y (c : ExtChain m) (p : Fin m) (t : Fin (live1 c p).card) :
    (liveExt c p).y t = subst1 p (c.y ((live1 c p).orderEmbOfFin rfl t)) := rfl

@[simp] theorem liveExt_aux (c : ExtChain m) (p : Fin m) : (liveExt c p).aux = c.aux := rfl

theorem mem_range_emb (c : ExtChain m) (p : Fin m) {k : Fin c.L} :
    k ∈ Set.range ((live1 c p).orderEmbOfFin rfl) ↔ k ∈ live1 c p := by
  rw [Finset.range_orderEmbOfFin]
  exact Iff.rfl

theorem stepType_liveExt (c : ExtChain m) (p : Fin m) (hp : p ∉ c.aux)
    (t : Fin (live1 c p).card) :
    (liveExt c p).stepType t = c.stepType ((live1 c p).orderEmbOfFin rfl t) := by
  show proj (liveExt c p).aux ((liveExt c p).y t) = proj c.aux (c.y _)
  rw [liveExt_aux, liveExt_y]
  exact proj_subst1 c.aux p hp _

theorem typeWeight_liveExt (c : ExtChain m) (p : Fin m) (hp : p ∉ c.aux)
    (t : Fin (live1 c p).card) :
    (liveExt c p).typeWeight t = c.typeWeight ((live1 c p).orderEmbOfFin rfl t) := by
  show weight (liveExt c p).aux ((liveExt c p).y t) = weight c.aux (c.y _)
  rw [liveExt_aux, liveExt_y]
  exact weight_subst1 c.aux p hp _

/-- The type of a gate whose substitute is zero or a basis vector has weight at most one. -/
theorem typeWeight_le_one_of_subst_trivial (c : ExtChain m) (p : Fin m) (hp : p ∉ c.aux)
    {k : Fin c.L}
    (h : subst1 p (c.y k) = 0 ∨ ∃ i : Fin m, subst1 p (c.y k) = basisVec i) :
    c.typeWeight k ≤ 1 := by
  show weight c.aux (c.y k) ≤ 1
  rw [← weight_subst1 c.aux p hp (c.y k)]
  rcases h with h0 | ⟨i, hi⟩
  · rw [h0]; simp [weight]
  · rw [hi]
    exact weight_le_one_basis c.aux i

/-! #### The all-ones functional on a coordinate set -/

/-- `c` computes the all-ones functional on the coordinate set `C`: some available vector (a
basis vector, a step, or `0`) is `1` on all of `C` and vanishes on the inessential variables. -/
def ComputesOnes (c : ExtChain m) (C : Finset (Fin m)) : Prop :=
  (∀ i ∈ C, i ∉ c.aux) ∧
    ∃ w : Vec m,
      w ∈ Set.range (basisVec (n := m)) ∪ Set.range c.y ∪ ({0} : Set (Vec m)) ∧
      (∀ i ∈ C, w i = 1) ∧ (∀ j ∈ c.aux, w j = 0)

theorem computesOnes_of_computes {k l : ℕ} (hk : 1 ≤ k) {c : ExtChain m}
    {col : Fin l → Fin m} (h : c.Computes (onesMat k l) col) :
    ComputesOnes c ((Finset.univ : Finset (Fin l)).image col) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
    exact h.2.1 j
  · obtain ⟨w, hw, hrow, haux⟩ := h.2.2 ⟨0, hk⟩
    refine ⟨w, hw, ?_, haux⟩
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
    rw [hrow j]
    rfl

/-- If some gate has a nonzero `p`-coordinate, then some gate is cancelled by substituting
`0` for `p`. -/
theorem exists_dead_of_nonzero (c : ExtChain m) (p : Fin m)
    (h : ∃ j : Fin c.L, (c.y j) p ≠ 0) : ∃ k : Fin c.L, dead1 c p k := by
  classical
  let S : Finset (Fin c.L) := Finset.univ.filter (fun k => (c.y k) p ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨j, hj⟩ := h
    exact ⟨j, by simp [S, hj]⟩
  have hminmem : S.min' hS ∈ S := Finset.min'_mem S hS
  have hnonzero : (c.y (S.min' hS)) p ≠ 0 := by simpa [S] using hminmem
  have hlt0 : ∀ k : Fin c.L, k < S.min' hS → (c.y k) p = 0 := by
    intro k hk
    by_contra hne
    have hmem : k ∈ S := by simp [S, hne]
    exact absurd hk (not_lt.mpr (Finset.min'_le S k hmem))
  have hpool_ne : ∀ x : Fin m ⊕ Fin (S.min' hS).1,
      (chainPool c.y (S.min' hS).1 (le_of_lt (S.min' hS).2) x) p ≠ 0 → x = Sum.inl p := by
    intro x hx
    cases x with
    | inl i =>
      have hip : i = p := by
        by_contra hne
        apply hx
        show basisVec i p = 0
        simp [basisVec, Ne.symm hne]
      rw [hip]
    | inr j =>
      exact absurd (hlt0 ⟨j.1, lt_of_lt_of_le j.2 (le_of_lt (S.min' hS).2)⟩ j.2) hx
  refine ⟨S.min' hS, ?_⟩
  show avail1 c p (S.min' hS) (subst1 p (c.y (S.min' hS)))
  obtain ⟨a, b, hab⟩ := c.valid (S.min' hS)
  have hcase : (chainPool c.y (S.min' hS).1 (le_of_lt (S.min' hS).2) a) p ≠ 0 ∨
      (chainPool c.y (S.min' hS).1 (le_of_lt (S.min' hS).2) b) p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hnonzero
    rw [hab]
    simp [hcon.1, hcon.2]
  have hsplit' : subst1 p (c.y (S.min' hS)) =
      subst1 p (chainPool c.y (S.min' hS).1 (le_of_lt (S.min' hS).2) a) +
        subst1 p (chainPool c.y (S.min' hS).1 (le_of_lt (S.min' hS).2) b) := by
    rw [hab, subst1_add]
  rcases hcase with ha | hb
  · have ha' : a = Sum.inl p := hpool_ne a ha
    have hzero : subst1 p (chainPool c.y (S.min' hS).1 (le_of_lt (S.min' hS).2) a) = 0 := by
      rw [ha', subst1_pool_inl]; simp
    rw [hsplit', hzero, zero_add]
    exact avail1_slot c p (S.min' hS) b
  · have hb' : b = Sum.inl p := hpool_ne b hb
    have hzero : subst1 p (chainPool c.y (S.min' hS).1 (le_of_lt (S.min' hS).2) b) = 0 := by
      rw [hb', subst1_pool_inl]; simp
    rw [hsplit', hzero, add_zero]
    exact avail1_slot c p (S.min' hS) a

/-- If the chain computes the all-ones functional on a set of at least two coordinates, then
substituting `0` for one of them cancels a gate. -/
theorem exists_dead_of_computes {c : ExtChain m} {C : Finset (Fin m)} (h : ComputesOnes c C)
    {p : Fin m} (hp : p ∈ C) (hcard : 2 ≤ C.card) : ∃ k : Fin c.L, dead1 c p k := by
  classical
  obtain ⟨-, w, hw, hrow, -⟩ := h
  have hwp : w p = 1 := hrow p hp
  have hwne : w ≠ 0 := by intro h0; rw [h0] at hwp; exact zero_ne_one hwp
  rcases hw with hw' | hw0
  · rcases hw' with hb | hy
    · obtain ⟨i, hi⟩ := hb
      have hsub : C ⊆ {i} := by
        intro j hj
        rw [Finset.mem_singleton]
        have hj1 := hrow j hj
        rw [← hi] at hj1
        simpa [basisVec] using hj1
      have hle : C.card ≤ 1 := by
        calc C.card ≤ ({i} : Finset (Fin m)).card := Finset.card_le_card hsub
          _ = 1 := by simp
      omega
    · obtain ⟨j, hj⟩ := hy
      refine exists_dead_of_nonzero c p ⟨j, ?_⟩
      rw [hj, hwp]
      exact one_ne_zero
  · rw [Set.mem_singleton_iff] at hw0
    exact absurd hw0 hwne

/-- Substituting `0` for `p` yields a chain computing the all-ones functional on `C \ {p}`. -/
theorem computesOnes_liveExt {c : ExtChain m} {C : Finset (Fin m)} (h : ComputesOnes c C)
    {p : Fin m} (hp : p ∈ C) : ComputesOnes (liveExt c p) (C.erase p) := by
  classical
  obtain ⟨hdisj, w, hw, hrow, haux⟩ := h
  have hpaux : p ∉ c.aux := hdisj p hp
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [liveExt_aux]
    exact hdisj i (Finset.mem_of_mem_erase hi)
  · refine ⟨subst1 p w, ?_, ?_, ?_⟩
    · rcases hw with hw' | hw0
      · rcases hw' with hb | hy
        · obtain ⟨i, hi⟩ := hb
          rw [← hi, subst1_basisVec]
          by_cases hip : i = p
          · rw [if_pos hip]
            exact Or.inr (Set.mem_singleton 0)
          · rw [if_neg hip]
            exact Or.inl (Or.inl ⟨i, rfl⟩)
        · obtain ⟨j, hj⟩ := hy
          rw [← hj]
          rcases exists_live_or_trivial c p j with h0 | ⟨i, -, hbi⟩ | ⟨j', hj'mem, -, heq⟩
          · rw [h0]
            exact Or.inr (Set.mem_singleton 0)
          · rw [hbi]
            exact Or.inl (Or.inl ⟨i, rfl⟩)
          · obtain ⟨t, ht⟩ := Set.mem_range.mp ((mem_range_emb c p).mpr hj'mem)
            refine Or.inl (Or.inr ⟨t, ?_⟩)
            show subst1 p (c.y ((live1 c p).orderEmbOfFin rfl t)) = subst1 p (c.y j)
            rw [ht, heq]
      · rw [Set.mem_singleton_iff] at hw0
        rw [hw0, subst1_zero]
        exact Or.inr (Set.mem_singleton 0)
    · intro i hi
      have hiC : i ∈ C := Finset.mem_of_mem_erase hi
      have hip : i ≠ p := (Finset.mem_erase.mp hi).1
      rw [subst1_apply_ne hip]
      exact hrow i hiC
    · intro j hj
      rw [liveExt_aux] at hj
      have hjp : j ≠ p := fun hh => hpaux (hh ▸ hj)
      rw [subst1_apply_ne hjp]
      exact haux j hj

/-- Substituting a variable which is not inessential does not change the set of heavy types. -/
theorem typeSet_liveExt (c : ExtChain m) (p : Fin m) (hp : p ∉ c.aux) :
    (liveExt c p).typeSet = c.typeSet := by
  classical
  ext T
  constructor
  · intro hT
    obtain ⟨t, ht, hval⟩ := Finset.mem_image.mp hT
    refine Finset.mem_image.mpr ⟨(live1 c p).orderEmbOfFin rfl t, ?_, ?_⟩
    · rw [ExtChain.mem_heavySteps] at ht
      rw [ExtChain.mem_heavySteps]
      rw [← typeWeight_liveExt c p hp (t := t)]
      exact ht
    · exact (stepType_liveExt c p hp (t := t)).symm.trans hval
  · intro hT
    obtain ⟨k, hk, hval⟩ := Finset.mem_image.mp hT
    rw [ExtChain.mem_heavySteps] at hk
    by_cases hlive : k ∈ live1 c p
    · obtain ⟨t, ht⟩ := Set.mem_range.mp ((mem_range_emb c p).mpr hlive)
      refine Finset.mem_image.mpr ⟨t, ?_, ?_⟩
      · rw [ExtChain.mem_heavySteps]
        rw [typeWeight_liveExt c p hp (t := t), ht]
        exact hk
      · exact (stepType_liveExt c p hp (t := t)).trans (by rw [ht]; exact hval)
    · rcases exists_live_or_trivial c p k with h0 | ⟨i, -, hbi⟩ | ⟨j', hj'mem, -, heq⟩
      · have hle := typeWeight_le_one_of_subst_trivial c p hp (Or.inl h0)
        omega
      · have hle := typeWeight_le_one_of_subst_trivial c p hp (Or.inr ⟨i, hbi⟩)
        omega
      · obtain ⟨t, ht⟩ := Set.mem_range.mp ((mem_range_emb c p).mpr hj'mem)
        refine Finset.mem_image.mpr ⟨t, ?_, ?_⟩
        · rw [ExtChain.mem_heavySteps]
          rw [typeWeight_liveExt c p hp (t := t), ht]
          have hw : c.typeWeight j' = c.typeWeight k := by
            show weight c.aux (c.y j') = weight c.aux (c.y k)
            rw [← weight_subst1 c.aux p hp (c.y j'), heq, weight_subst1 c.aux p hp]
          omega
        · have hst : c.stepType j' = c.stepType k := by
            show proj c.aux (c.y j') = proj c.aux (c.y k)
            rw [← proj_subst1 c.aux p hp (c.y j'), heq, proj_subst1 c.aux p hp]
          exact (stepType_liveExt c p hp (t := t)).trans (by rw [ht]; exact hst.trans hval)

/-! #### The counting induction -/

theorem claim5_aux (N : ℕ) :
    ∀ (m : ℕ) (c : ExtChain m) (C : Finset (Fin m)),
      C.card ≤ N → ComputesOnes c C → C.card - 1 + c.typeSet.card ≤ c.L := by
  induction N with
  | zero =>
    intro m c C hN h
    have h0 : C.card = 0 := by omega
    rw [h0]
    simpa using ExtChain.typeSet_card_le_L c
  | succ N ih =>
    intro m c C hN h
    by_cases hC0 : C = ∅
    · rw [hC0]
      simpa using ExtChain.typeSet_card_le_L c
    · obtain ⟨p, hpC⟩ := Finset.nonempty_iff_ne_empty.mpr hC0
      have hpaux : p ∉ c.aux := h.1 p hpC
      have herase : (C.erase p).card = C.card - 1 := Finset.card_erase_of_mem hpC
      have hcard' : (C.erase p).card ≤ N := by omega
      have hcomp' : ComputesOnes (liveExt c p) (C.erase p) := computesOnes_liveExt h hpC
      have hIH := ih m (liveExt c p) (C.erase p) hcard' hcomp'
      by_cases hcard2 : 2 ≤ C.card
      · obtain ⟨k, hk⟩ := exists_dead_of_computes h hpC hcard2
        have hknot : k ∉ live1 c p := fun hh => mem_live1.mp hh hk
        have hsub : live1 c p ⊆ (Finset.univ : Finset (Fin c.L)).erase k := by
          intro j hj
          rw [Finset.mem_erase]
          exact ⟨fun hjk => hknot (hjk ▸ hj), Finset.mem_univ j⟩
        have hsize : ((Finset.univ : Finset (Fin c.L)).erase k).card = c.L - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
        have hLle : (liveExt c p).L + 1 ≤ c.L := by
          rw [liveExt_L]
          have hLpos : 1 ≤ c.L := Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le k.1) k.2)
          have h1 := Finset.card_le_card hsub
          rw [hsize] at h1
          omega
        have hts : (liveExt c p).typeSet = c.typeSet := typeSet_liveExt c p hpaux
        rw [hts] at hIH
        omega
      · have hCpos : 0 < C.card := Finset.card_pos.mpr ⟨p, hpC⟩
        have hC1 : C.card = 1 := by omega
        rw [hC1]
        simpa using ExtChain.typeSet_card_le_L c

/-- **Claim 5, counting core**: a chain computing the all-ones functional on a coordinate set
`C` has length at least `#C - 1 + #(heavy types)`. -/
theorem claim5_core (c : ExtChain m) (C : Finset (Fin m)) (h : ComputesOnes c C) :
    C.card - 1 + c.typeSet.card ≤ c.L :=
  claim5_aux C.card m c C le_rfl h

theorem Lstar_onesMat_ge (k l : ℕ) (hk : 1 ≤ k) : l - 1 ≤ Lstar (onesMat k l) := by
  classical
  unfold Lstar
  refine le_sInf_of_forall
    (fun hs => absurd hs (Lstar_witness_nonempty (onesMat k l)).ne_empty) ?_
  rintro l' ⟨mm, c, col, hcomp, hl⟩
  have hOnes : ComputesOnes c ((Finset.univ : Finset (Fin l)).image col) :=
    computesOnes_of_computes hk hcomp
  have hcard : ((Finset.univ : Finset (Fin l)).image col).card = l := by
    rw [Finset.card_image_of_injective _ hcomp.1, Finset.card_univ, Fintype.card_fin]
  have hcore := claim5_core c _ hOnes
  rw [hcard] at hcore
  rw [← hl]
  show l - 1 ≤ c.L - c.typeSet.card
  omega

/-- **Claim 5**: `L*(1_{k×l}) = l - 1` for `k ≥ 1`. -/
theorem Lstar_onesMat (k l : ℕ) (hk : 1 ≤ k) : Lstar (onesMat k l) = l - 1 :=
  le_antisymm (Lstar_onesMat_le k l hk) (Lstar_onesMat_ge k l hk)

/-- **Claim 5, additive form**: `L(1_{k×l}) = l - 1` for `k ≥ 1`. -/
theorem chainComplexity_onesMat (k l : ℕ) (hk : 1 ≤ k) :
    chainComplexity (onesMat k l) = l - 1 := by
  refine le_antisymm (chainComplexity_onesMat_le k l hk) ?_
  calc l - 1 = Lstar (onesMat k l) := (Lstar_onesMat k l hk).symm
    _ ≤ chainComplexity (onesMat k l) := Lstar_le_chainComplexity _

end Claim5


/-! ### Corollary 2 -/

/-- **Corollary 2** of Section 6: for the matrix `A = 1_{m×(n-m)} ⊞ U ∈ GF(2)^{n×n}` one
has `L*(A) ≥ 3n - O(√n log n)`, in the concrete form `3n ≤ L*(A) + 21m + 1`.

The ingredients are Claim 5, `L*(1_{m×(n-m)}) = (n - m) - 1` (`Lstar_onesMat`), and the bound
(6.1) for `U`, `2n ≤ L*(U) + 20m`, obtained as in Corollary 1 from
`reducedComplexity_rowSet_ge` applied to a chain `c` realizing the minimum `L*(U)`
(`six_one_Umat`).  The block identity `L*(A₁ ⊞ A₂) = L*(A₁) + L*(A₂)` of Lemma 1
(`Lstar_dsum_ge`, `Lstar_dsum_le`) combines them: `(n - m - 1) + (2n - 20m) = 3n - 21m - 1`. -/
theorem corollary2 (n : ℕ) (hn : N₀ ≤ n) (c : ExtChain (mOf n))
    (col : Fin (mOf n) → Fin (mOf n)) (hcomp : c.Computes (Umat n) col)
    (hmin : c.reducedComplexity = Lstar (Umat n)) :
    3 * n ≤ Lstar (dsum (onesMat (mOf n) (n - mOf n)) (Umat n)) + 21 * mOf n + 1 := by
  classical
  have hm1 : 1 ≤ mOf n := one_le_mOf n hn
  have hones : Lstar (onesMat (mOf n) (n - mOf n)) = (n - mOf n) - 1 :=
    Lstar_onesMat (mOf n) (n - mOf n) hm1
  have hblock : Lstar (onesMat (mOf n) (n - mOf n)) + Lstar (Umat n) ≤
      Lstar (dsum (onesMat (mOf n) (n - mOf n)) (Umat n)) :=
    Lstar_dsum_ge (onesMat (mOf n) (n - mOf n)) (Umat n)
  have hsix := six_one_Umat n hn c col hcomp hmin
  omega

/-! ## Part 8: Corollary 3 -/

/-! ### The block matrix `1_{m×(n-m)} ⊞ U` as an `n × n` matrix -/

/-- The matrix `A = 1_{m×(n-m)} ⊞ U` of Corollary 2, regarded as an `n × n` matrix: the direct
sum is reindexed along the identities `m + (n - m) = n = (n - m) + m`. -/
noncomputable def Amat (n : ℕ) (hn : mOf n ≤ n) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j =>
    dsum (onesMat (mOf n) (n - mOf n)) (Umat n)
      (finCongr (Nat.add_sub_of_le hn).symm i)
      (finCongr (Nat.sub_add_cancel hn).symm j)

/-- `Amat` is the block matrix `1_{m×(n-m)} ⊞ U` up to a reindexing of its rows and columns,
so it has the same reduced complexity. -/
theorem Lstar_Amat (n : ℕ) (hn : mOf n ≤ n) :
    Lstar (Amat n hn) = Lstar (dsum (onesMat (mOf n) (n - mOf n)) (Umat n)) := by
  classical
  unfold Amat
  exact Lstar_reindex (dsum (onesMat (mOf n) (n - mOf n)) (Umat n)) _ _

/-- **The weight of the block matrix.**  Every nonzero entry of `A = 1_{m×(n-m)} ⊞ U` lies in
one of the two diagonal blocks, of sizes `m × (n-m)` and `(n-m) × m`, so `ν(A) ≤ 2m(n-m)`. -/
theorem boolWeight_Amat_le (n : ℕ) (hn : mOf n ≤ n) :
    boolWeight (Amat n hn) ≤ 2 * mOf n * (n - mOf n) := by
  classical
  have hblock : ∀ p : Fin n × Fin n, Amat n hn p.1 p.2 ≠ 0 →
      (p.1.val < mOf n ∧ p.2.val < n - mOf n) ∨
        (mOf n ≤ p.1.val ∧ n - mOf n ≤ p.2.val) := by
    rintro ⟨i, j⟩ hne
    dsimp only at hne ⊢
    by_cases hi : i.val < mOf n
    · refine Or.inl ⟨hi, ?_⟩
      by_contra hj
      have hj' : n - mOf n ≤ j.val := by omega
      apply hne
      show dsum (onesMat (mOf n) (n - mOf n)) (Umat n)
          (finCongr (Nat.add_sub_of_le hn).symm i)
          (finCongr (Nat.sub_add_cancel hn).symm j) = 0
      have hI : finCongr (Nat.add_sub_of_le hn).symm i
          = Fin.castAdd (n - mOf n) (⟨i.val, hi⟩ : Fin (mOf n)) := by
        apply Fin.ext
        simp
      have hJ : finCongr (Nat.sub_add_cancel hn).symm j
          = Fin.natAdd (n - mOf n) (⟨j.val - (n - mOf n), by omega⟩ : Fin (mOf n)) := by
        apply Fin.ext
        simp
        omega
      rw [hI, hJ, dsum_castAdd_natAdd]
    · have hi' : mOf n ≤ i.val := by omega
      refine Or.inr ⟨hi', ?_⟩
      by_contra hj
      have hj' : j.val < n - mOf n := by omega
      apply hne
      show dsum (onesMat (mOf n) (n - mOf n)) (Umat n)
          (finCongr (Nat.add_sub_of_le hn).symm i)
          (finCongr (Nat.sub_add_cancel hn).symm j) = 0
      have hI : finCongr (Nat.add_sub_of_le hn).symm i
          = Fin.natAdd (mOf n) (⟨i.val - mOf n, by omega⟩ : Fin (n - mOf n)) := by
        apply Fin.ext
        simp
        omega
      have hJ : finCongr (Nat.sub_add_cancel hn).symm j
          = Fin.castAdd (mOf n) (⟨j.val, hj'⟩ : Fin (n - mOf n)) := by
        apply Fin.ext
        simp
      rw [hI, hJ, dsum_natAdd_castAdd]
  have hR1 : (Finset.univ.filter (fun i : Fin n => i.val < mOf n)).card = mOf n := by
    rw [← Fintype.card_subtype (fun i : Fin n => i.val < mOf n)]
    exact Fintype.card_fin_lt_of_le hn
  have hC1 :
      (Finset.univ.filter (fun j : Fin n => j.val < n - mOf n)).card = n - mOf n := by
    rw [← Fintype.card_subtype (fun j : Fin n => j.val < n - mOf n)]
    exact Fintype.card_fin_lt_of_le (Nat.sub_le n (mOf n))
  have hR2 : (Finset.univ.filter (fun i : Fin n => mOf n ≤ i.val)).card = n - mOf n := by
    have hset : (Finset.univ.filter (fun i : Fin n => mOf n ≤ i.val))
        = Finset.univ.filter (fun i : Fin n => ¬ i.val < mOf n) := by
      ext i
      simp
    have hcard : Fintype.card {i : Fin n // i.val < mOf n} = mOf n :=
      Fintype.card_fin_lt_of_le hn
    rw [hset, ← Fintype.card_subtype (fun i : Fin n => ¬ i.val < mOf n),
      Fintype.card_subtype_compl (fun i : Fin n => i.val < mOf n), Fintype.card_fin, hcard]
  have hC2 : (Finset.univ.filter (fun j : Fin n => n - mOf n ≤ j.val)).card = mOf n := by
    have hset : (Finset.univ.filter (fun j : Fin n => n - mOf n ≤ j.val))
        = Finset.univ.filter (fun j : Fin n => ¬ j.val < n - mOf n) := by
      ext j
      simp
    have hcard : Fintype.card {j : Fin n // j.val < n - mOf n} = n - mOf n :=
      Fintype.card_fin_lt_of_le (Nat.sub_le n (mOf n))
    rw [hset, ← Fintype.card_subtype (fun j : Fin n => ¬ j.val < n - mOf n),
      Fintype.card_subtype_compl (fun j : Fin n => j.val < n - mOf n), Fintype.card_fin, hcard]
    omega
  have hsub : (Finset.univ.filter (fun p : Fin n × Fin n => Amat n hn p.1 p.2 ≠ 0))
      ⊆ (Finset.univ.filter (fun i : Fin n => i.val < mOf n) ×ˢ
            Finset.univ.filter (fun j : Fin n => j.val < n - mOf n)) ∪
          (Finset.univ.filter (fun i : Fin n => mOf n ≤ i.val) ×ˢ
            Finset.univ.filter (fun j : Fin n => n - mOf n ≤ j.val)) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨-, hne⟩ := hp
    rcases hblock p hne with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine Finset.mem_union.mpr (Or.inl (Finset.mem_product.mpr ⟨?_, ?_⟩))
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩
    · refine Finset.mem_union.mpr (Or.inr (Finset.mem_product.mpr ⟨?_, ?_⟩))
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩
  calc boolWeight (Amat n hn)
      = (Finset.univ.filter (fun p : Fin n × Fin n => Amat n hn p.1 p.2 ≠ 0)).card := rfl
    _ ≤ ((Finset.univ.filter (fun i : Fin n => i.val < mOf n) ×ˢ
            Finset.univ.filter (fun j : Fin n => j.val < n - mOf n)) ∪
          (Finset.univ.filter (fun i : Fin n => mOf n ≤ i.val) ×ˢ
            Finset.univ.filter (fun j : Fin n => n - mOf n ≤ j.val))).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ.filter (fun i : Fin n => i.val < mOf n) ×ˢ
            Finset.univ.filter (fun j : Fin n => j.val < n - mOf n)).card +
          (Finset.univ.filter (fun i : Fin n => mOf n ≤ i.val) ×ˢ
            Finset.univ.filter (fun j : Fin n => n - mOf n ≤ j.val)).card :=
        Finset.card_union_le _ _
    _ = mOf n * (n - mOf n) + (n - mOf n) * mOf n := by
        rw [Finset.card_product, Finset.card_product, hR1, hC1, hR2, hC2]
    _ = 2 * mOf n * (n - mOf n) := by ring

/-! ### Corollary 3, first bound -/

/-- **Corollary 3** of Section 6, first bound: the additive complexity of `n × n` matrix
multiplication over `GF(2)` satisfies `β₊(M_n) ≥ (4 - o(1))·n²`, in the concrete form

`4n² ≤ β₊(M_n) + 21nm + 2m(n-m) + 6n`,  where `m = p·s`,

so that the error term `21nm + 2m(n-m) + 6n = O(n√n log n)` is negligible relative to `n²`.

This is Lemma 2 of Section 3 (`lemma2`) applied to `B = A = 1_{m×(n-m)} ⊞ U`: by Corollary 2
(`corollary2`) the reduced complexity of `A` is at least `3n - 21m - 1`, and its boolean weight
is at most `2m(n-m)` (`boolWeight_Amat_le`), whence

`β₊(M_n) ≥ n·L*(A) + n² - ν(A) - 5n ≥ n(3n - 21m - 1) + n² - 2m(n-m) - 5n
        ≥ 4n² - 21nm - 2m(n-m) - 6n`. -/
theorem corollary3 (n : ℕ) (hn : N₀ ≤ n) (c : ExtChain (mOf n))
    (col : Fin (mOf n) → Fin (mOf n)) (hcomp : c.Computes (Umat n) col)
    (hmin : c.reducedComplexity = Lstar (Umat n)) :
    4 * n * n ≤ BilPlus (MM n) + 21 * n * mOf n + 2 * mOf n * (n - mOf n) + 6 * n := by
  classical
  have hmn : mOf n ≤ n := mOf_le_n n hn
  have hlem := lemma2 (Amat n hmn)
  rw [Lstar_Amat n hmn] at hlem
  have hc2 := corollary2 n hn c col hcomp hmin
  have hw := boolWeight_Amat_le n hmn
  nlinarith [hlem, hc2, hw]

/-! ## Part 9: Claim 6 -/

/-! ### The independence index of a rectangle-free matrix -/

section Claim6

variable {m : ℕ}

/-- The support of a basis vector is a singleton. -/
theorem supp_basisVec (d : Fin m) : supp m (basisVec d) = {d} := by
  ext j
  simp [supp, basisVec_apply]

/-- **Claim 6** of Section 6.  Let `B ⊆ GF(2)^m` be the set of rows of a boolean matrix
without `2 × 2` rectangles (any two rows share at most one common `1`), each row of `B` having
weight at least `s`.  Then `ind (B ∪ I_m) ≥ s`.

This is the general form in which the claim is used below: the unit vectors that are adjoined
to `B` may be any subset of `I_m` (the scheme of Theorem 2 adjoins the unit vectors of the
essential coordinates only). -/
theorem claim6_aux (B U : Finset (Vec m)) (s : ℕ)
    (hU : U ⊆ unitVecs m)
    (hrect : ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ → (supp m b₁ ∩ supp m b₂).card ≤ 1)
    (hwt : ∀ b ∈ B, s ≤ weight (Finset.univ : Finset (Fin m)) b)
    (hcard : s ≤ (B ∪ U).card) :
    s ≤ ind (B ∪ U) := by
  classical
  refine le_ind ?_ hcard
  intro S hSB hScard
  rw [indep_iff_sum_ne_zero]
  intro T hTne hsum
  set T' : Finset (Vec m) := T.image (fun x : ↥S => (x : Vec m)) with hT'
  have hT'sub : T' ⊆ B ∪ unitVecs m := by
    rintro v hv
    rw [hT'] at hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    rcases Finset.mem_union.mp (hSB x.2) with hB | hUx
    · exact Finset.mem_union_left _ hB
    · exact Finset.mem_union_right _ (hU hUx)
  have hT'sum : ∑ v ∈ T', v = 0 := by
    rw [hT', Finset.sum_image]
    · exact hsum
    · intro x _ y _ hxy
      exact Subtype.ext hxy
  have hT'card : T'.card = T.card := by
    rw [hT']
    exact Finset.card_image_of_injective _ Subtype.val_injective
  have hT'ne : T'.Nonempty := by
    rw [hT']
    exact hTne.image _
  have hTcard : T.card ≤ s := by
    have h := Finset.card_le_univ T
    rw [Fintype.card_coe, hScard] at h
    exact h
  by_cases hcase : ∃ b ∈ T', b ∈ B
  · obtain ⟨b, hbT', hbB⟩ := hcase
    have hcoord : ∀ i ∈ supp m b, ∃ v ∈ T'.erase b, v i ≠ 0 := by
      intro i hi
      have hbi : b i ≠ 0 := by
        rw [supp, Finset.mem_filter] at hi
        exact hi.2
      have hsumi : (∑ v ∈ T', v) i = 0 := by rw [hT'sum]; rfl
      rw [Finset.sum_apply] at hsumi
      have hsplit := Finset.sum_erase_add T' (fun v => v i) hbT'
      rw [hsumi] at hsplit
      have hb1 : b i = 1 := by
        rcases zmod2_eq_zero_or_one (b i) with h | h
        · exact absurd h hbi
        · exact h
      rw [hb1] at hsplit
      have herase : ∑ v ∈ T'.erase b, v i = 1 := by
        have h3 : ∑ v ∈ T'.erase b, v i = -1 := eq_neg_of_add_eq_zero_left hsplit
        rw [h3]
        decide
      have hne0 : ∑ v ∈ T'.erase b, v i ≠ 0 := by
        rw [herase]
        exact one_ne_zero
      exact Finset.exists_ne_zero_of_sum_ne_zero hne0
    choose f hfmem hfne using hcoord
    set g : Fin m → Vec m := fun i => if h : i ∈ supp m b then f i h else 0 with hg
    have hgapply : ∀ i (hi : i ∈ supp m b), g i = f i hi := by
      intro i hi
      simp only [hg]
      rw [dif_pos hi]
    have hmaps : Set.MapsTo g ↑(supp m b) ↑(T'.erase b) := by
      intro i hi
      rw [hgapply i hi]
      exact hfmem i hi
    have hinj : Set.InjOn g ↑(supp m b) := by
      intro i hi i' hi' heq
      by_contra hne
      have h1 : g i = f i hi := hgapply i hi
      have h2 : g i' = f i' hi' := hgapply i' hi'
      have hv : f i hi = f i' hi' := by rw [← h1, ← h2]; exact heq
      have hvi : f i hi i ≠ 0 := hfne i hi
      have hvi' : f i hi i' ≠ 0 := by rw [hv]; exact hfne i' hi'
      have hmem2 : ({i, i'} : Finset (Fin m)) ⊆ supp m b ∩ supp m (f i hi) := by
        intro x hx
        rw [Finset.mem_inter]
        rw [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact ⟨hi, by simp [supp, hvi]⟩
        · exact ⟨hi', by simp [supp, hvi']⟩
      have hcard2 : 2 ≤ (supp m b ∩ supp m (f i hi)).card := by
        calc (2 : ℕ) = ({i, i'} : Finset (Fin m)).card := by simp [hne]
          _ ≤ _ := Finset.card_le_card hmem2
      have hvT' : f i hi ∈ T' := (Finset.mem_erase.mp (hfmem i hi)).2
      have hvb : b ≠ f i hi := ((Finset.mem_erase.mp (hfmem i hi)).1).symm
      rcases Finset.mem_union.mp (hT'sub hvT') with hvB | hvU
      · have := hrect b hbB (f i hi) hvB hvb
        omega
      · obtain ⟨d, hd⟩ := mem_unitVecs.mp hvU
        rw [← hd, supp_basisVec] at hcard2
        have hle1 : (supp m b ∩ {d}).card ≤ 1 := by
          calc (supp m b ∩ {d}).card ≤ ({d} : Finset (Fin m)).card :=
                Finset.card_le_card (Finset.inter_subset_right)
            _ = 1 := Finset.card_singleton d
        omega
    have hle := Finset.card_le_card_of_injOn g hmaps hinj
    have hbwt : s ≤ (supp m b).card := by
      have h := hwt b hbB
      rwa [weight_eq_card_supp] at h
    have herasecard : (T'.erase b).card = T'.card - 1 := Finset.card_erase_of_mem hbT'
    have hpos : 0 < T'.card := hT'ne.card_pos
    omega
  · have hsubU : T' ⊆ unitVecs m := by
      intro v hv
      rcases Finset.mem_union.mp (hT'sub hv) with h | h
      · exact absurd ⟨v, hv, h⟩ hcase
      · exact h
    have hex : ∀ v : ↥T', ∃ d : Fin m, basisVec d = (v : Vec m) := by
      intro v
      exact mem_unitVecs.mp (hsubU v.2)
    choose d hd using hex
    have hdinj : Function.Injective d := by
      intro v w hvw
      apply Subtype.ext
      rw [← hd v, ← hd w, hvw]
    obtain ⟨v₀, hv₀⟩ := hT'ne
    set d₀ : Fin m := d ⟨v₀, hv₀⟩ with hd₀
    have h1 : ∑ v ∈ T', v d₀ = 1 := by
      rw [← Finset.sum_coe_sort T' (fun v => v d₀)]
      have hside : ∀ w ∈ (Finset.univ : Finset ↥T'), w ≠ ⟨v₀, hv₀⟩ → (w : Vec m) d₀ = 0 := by
        intro w _ hwne
        rw [← hd w, basisVec_apply]
        have hne' : d₀ ≠ d w := by
          intro h
          exact hwne (hdinj h.symm)
        simp [hne']
      rw [Finset.sum_eq_single (⟨v₀, hv₀⟩ : ↥T') hside (by simp)]
      rw [← hd ⟨v₀, hv₀⟩, basisVec_apply]
      simp [hd₀]
    have h2 : (∑ v ∈ T', v) d₀ = ∑ v ∈ T', v d₀ := Finset.sum_apply _ _ _
    rw [hT'sum, h1] at h2
    simp at h2

/-- **Claim 6** of Section 6: if `B ⊆ GF(2)^m` is rectangle-free and every row of `B` has
weight at least `s`, then `ind (B ∪ I_m) ≥ s`. -/
theorem claim6 (B : Finset (Vec m)) (s : ℕ)
    (hrect : ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ ≠ b₂ → (supp m b₁ ∩ supp m b₂).card ≤ 1)
    (hwt : ∀ b ∈ B, s ≤ weight (Finset.univ : Finset (Fin m)) b)
    (hcard : s ≤ (B ∪ unitVecs m).card) :
    s ≤ ind (B ∪ unitVecs m) :=
  claim6_aux B (unitVecs m) s (Finset.Subset.refl _) hrect hwt hcard

end Claim6

/-! ## Part 10: the Sidon set `S_n` -/

/-! Section 6 continues with the cyclic matrices `Z_{n,S}` of Section 3, built from Sidon sets.
This part constructs the classical Erdős–Turán Sidon set

`S_n = [n] ∩ {s_k = 2qk + (k² mod q) | 1 ≤ k ≤ K}`,  `K = ⌊n/(2q)⌋ - 1`,

where `q` is a prime with `√n < q ≤ 2√n` (Bertrand's postulate).  The elements of `S_n` are
spread evenly: consecutive elements, and the last element and the right endpoint `n`, differ by
at most `4q` (`sval_step_le`, `le_sval_add_gap`).  The set is a Sidon set: every difference
`s_i - s_j`, `i ≠ j`, is determined by its value (`sn_sidon_diff`), equivalently every sum of
two elements is determined by the unordered pair of summands (`sn_sidon`).  The proof works
modulo `q`: `s_k ≡ k² (mod q)` (`sval_modEq_sq`), and comparing the quotients modulo `2q`
turns an equality of two sums into `2(a - c)(a - d) = 0` over `ZMod q`, so `a ∈ {c, d}`.

-/

/-! ### The prime `q` and the construction of `S_n` -/

/-- The prime `q` of the construction of `S_n`: a prime with `√n < q ≤ 2√n`, which exists by
Bertrand's postulate.  (The value is irrelevant when `√n = 0`, i.e. `n = 0`.) -/
noncomputable def sidQ (n : ℕ) : ℕ :=
  if h : Nat.sqrt n = 0 then 2
  else (Nat.exists_prime_lt_and_le_two_mul (Nat.sqrt n) h).choose

theorem sidQ_prime {n : ℕ} (h : Nat.sqrt n ≠ 0) : Nat.Prime (sidQ n) := by
  unfold sidQ
  rw [dif_neg h]
  exact (Nat.exists_prime_lt_and_le_two_mul (Nat.sqrt n) h).choose_spec.1

theorem sidQ_gt {n : ℕ} (h : Nat.sqrt n ≠ 0) : Nat.sqrt n < sidQ n := by
  unfold sidQ
  rw [dif_neg h]
  exact (Nat.exists_prime_lt_and_le_two_mul (Nat.sqrt n) h).choose_spec.2.1

theorem sidQ_le {n : ℕ} (h : Nat.sqrt n ≠ 0) : sidQ n ≤ 2 * Nat.sqrt n := by
  unfold sidQ
  rw [dif_neg h]
  exact (Nat.exists_prime_lt_and_le_two_mul (Nat.sqrt n) h).choose_spec.2.2

theorem sidQ_sq_gt {n : ℕ} (h : Nat.sqrt n ≠ 0) : n < sidQ n ^ 2 := by
  have h1 : Nat.sqrt n + 1 ≤ sidQ n := sidQ_gt h
  have h2 : n < (Nat.sqrt n + 1) ^ 2 := by
    simpa [pow_two, Nat.succ_eq_add_one] using Nat.lt_succ_sqrt n
  calc n < (Nat.sqrt n + 1) ^ 2 := h2
    _ ≤ sidQ n ^ 2 := Nat.pow_le_pow_left h1 2

theorem two_le_sidQ {n : ℕ} (h : Nat.sqrt n ≠ 0) : 2 ≤ sidQ n := (sidQ_prime h).two_le

theorem sidQ_pos {n : ℕ} (h : Nat.sqrt n ≠ 0) : 0 < sidQ n := (sidQ_prime h).pos

theorem sqrt_ne_zero {n : ℕ} (hn : N₀ ≤ n) : Nat.sqrt n ≠ 0 := by
  intro h
  have h1 : n = 0 := Nat.sqrt_eq_zero.mp h
  unfold N₀ at hn
  omega

theorem four_le_sqrt {n : ℕ} (hn : N₀ ≤ n) : 4 ≤ Nat.sqrt n := by
  rw [Nat.le_sqrt]
  unfold N₀ at hn
  omega

theorem twelve_le_sqrt {n : ℕ} (hn : N₀ ≤ n) : 12 ≤ Nat.sqrt n := by
  rw [Nat.le_sqrt]
  unfold N₀ at hn
  omega

theorem two_mul_sidQ_le {n : ℕ} (hn : N₀ ≤ n) : 2 * sidQ n ≤ n := by
  have h := sidQ_le (sqrt_ne_zero hn)
  have hs := four_le_sqrt hn
  have hsq : Nat.sqrt n * Nat.sqrt n ≤ n := by simpa [pow_two] using Nat.sqrt_le' n
  nlinarith

theorem sidQ_ne_two {n : ℕ} (hn : N₀ ≤ n) : sidQ n ≠ 2 := by
  intro h2
  have h1 : Nat.sqrt n + 1 ≤ sidQ n := sidQ_gt (sqrt_ne_zero hn)
  rw [h2] at h1
  have h3 : Nat.sqrt n ≤ 1 := by omega
  have h4 : n < 4 := by
    have := Nat.lt_succ_sqrt n
    nlinarith
  unfold N₀ at hn
  omega

theorem sidQ_odd {n : ℕ} (hn : N₀ ≤ n) : Odd (sidQ n) := by
  have hp := sidQ_prime (sqrt_ne_zero hn)
  rcases hp.eq_two_or_odd with h2 | ho
  · exact absurd h2 (sidQ_ne_two hn)
  · exact Nat.odd_iff.mpr ho

/-! ### The construction of `S_n` -/

/-- The index bound `K = ⌊n/(2q)⌋ - 1`: `S_n = {s_1, …, s_K}`. -/
noncomputable def sidK (n : ℕ) : ℕ := n / (2 * sidQ n) - 1

/-- The element `s_k = 2qk + (k² mod q)` of the Erdős–Turán Sidon set. -/
noncomputable def sval (n k : ℕ) : ℕ := 2 * sidQ n * k + k * k % sidQ n

theorem sval_def (n k : ℕ) : sval n k = 2 * sidQ n * k + k * k % sidQ n := rfl

theorem le_sval (n k : ℕ) : 2 * sidQ n * k ≤ sval n k := by
  rw [sval_def]; exact Nat.le_add_right _ _

theorem sval_le {n k : ℕ} (h : Nat.sqrt n ≠ 0) :
    sval n k ≤ 2 * sidQ n * k + (sidQ n - 1) := by
  have hlt : k * k % sidQ n < sidQ n := Nat.mod_lt _ (sidQ_pos h)
  rw [sval_def]; omega

theorem sidK_succ {n : ℕ} (hn : N₀ ≤ n) : sidK n + 1 = n / (2 * sidQ n) := by
  have hq : 0 < 2 * sidQ n := by have := sidQ_pos (sqrt_ne_zero hn); omega
  unfold sidK
  have h1 : 1 ≤ n / (2 * sidQ n) := by
    rw [Nat.one_le_div_iff hq]
    exact two_mul_sidQ_le hn
  omega

theorem two_sidQ_mul_sidK_succ_le {n : ℕ} (hn : N₀ ≤ n) :
    2 * sidQ n * (sidK n + 1) ≤ n := by
  rw [sidK_succ hn]
  exact Nat.mul_div_le _ _

theorem two_le_sidK {n : ℕ} (hn : N₀ ≤ n) : 2 ≤ sidK n := by
  have hq : 0 < 2 * sidQ n := by have := sidQ_pos (sqrt_ne_zero hn); omega
  have h0 : 6 * sidQ n ≤ n := by
    have h1 := sidQ_le (sqrt_ne_zero hn)
    have hs := twelve_le_sqrt hn
    have hsq : Nat.sqrt n * Nat.sqrt n ≤ n := by simpa [pow_two] using Nat.sqrt_le' n
    nlinarith
  have h : 2 * sidQ n * 3 ≤ n := by nlinarith
  have h1 : 3 ≤ n / (2 * sidQ n) := by
    rw [Nat.le_div_iff_mul_le hq]
    linarith
  have h2 := sidK_succ hn
  omega

theorem two_mul_sidK_succ_lt {n : ℕ} (hn : N₀ ≤ n) : 2 * (sidK n + 1) < sidQ n := by
  have hq := sidQ_pos (sqrt_ne_zero hn)
  have h1 := two_sidQ_mul_sidK_succ_le hn
  have h2 : n < sidQ n * sidQ n := by
    have := sidQ_sq_gt (sqrt_ne_zero hn); rwa [pow_two] at this
  have h3 : sidQ n * (2 * (sidK n + 1)) < sidQ n * sidQ n := by
    have e : sidQ n * (2 * (sidK n + 1)) = 2 * sidQ n * (sidK n + 1) := by ring
    rw [e]
    omega
  exact Nat.lt_of_mul_lt_mul_left h3

theorem sidK_lt_sidQ {n : ℕ} (hn : N₀ ≤ n) : sidK n < sidQ n := by
  have := two_mul_sidK_succ_lt hn
  omega

theorem two_sidK_add_two_le {n : ℕ} (hn : N₀ ≤ n) : 2 * sidK n + 2 ≤ sidQ n := by
  have := two_mul_sidK_succ_lt hn
  omega

theorem sval_le_n {n k : ℕ} (hn : N₀ ≤ n) (hk : k ≤ sidK n) : sval n k ≤ n := by
  have h := sval_le (n := n) (k := k) (sqrt_ne_zero hn)
  have h2 := two_sidQ_mul_sidK_succ_le hn
  have hq := sidQ_pos (sqrt_ne_zero hn)
  have h3 : 2 * sidQ n * (k + 1) ≤ 2 * sidQ n * (sidK n + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have e : 2 * sidQ n * (k + 1) = 2 * sidQ n * k + 2 * sidQ n := by ring
  omega

theorem sval_strictMono {n : ℕ} (h : Nat.sqrt n ≠ 0) : StrictMono (sval n) := by
  intro a b hab
  have hq := sidQ_pos h
  have hmod : a * a % sidQ n < 2 * sidQ n := by
    have := Nat.mod_lt (a * a) hq; omega
  have h1 : 2 * sidQ n * (a + 1) ≤ 2 * sidQ n * b := Nat.mul_le_mul_left _ hab
  have h2 : 2 * sidQ n * a + a * a % sidQ n < 2 * sidQ n * (a + 1) := by
    have e : 2 * sidQ n * (a + 1) = 2 * sidQ n * a + 2 * sidQ n := by ring
    omega
  rw [sval_def, sval_def]
  omega

theorem sval_injective {n : ℕ} (h : Nat.sqrt n ≠ 0) : Function.Injective (sval n) :=
  (sval_strictMono h).injective

theorem one_le_sval {n k : ℕ} (h : Nat.sqrt n ≠ 0) (hk : 1 ≤ k) : 1 ≤ sval n k := by
  have h1 : 2 * sidQ n * 1 ≤ 2 * sidQ n * k := Nat.mul_le_mul_left _ hk
  have h2 := le_sval n k
  have h3 : 2 ≤ 2 * sidQ n := by have := two_le_sidQ h; nlinarith
  omega

theorem sval_step_le {n k : ℕ} (h : Nat.sqrt n ≠ 0) :
    sval n (k + 1) ≤ sval n k + 3 * sidQ n := by
  have hlt : (k + 1) * (k + 1) % sidQ n < sidQ n := Nat.mod_lt _ (sidQ_pos h)
  have e : 2 * sidQ n * (k + 1) = 2 * sidQ n * k + 2 * sidQ n := by ring
  rw [sval_def, sval_def]
  omega

theorem sval_le_add_mul_gap {n : ℕ} (h : Nat.sqrt n ≠ 0) {k l : ℕ} (hkl : k ≤ l) :
    sval n l ≤ sval n k + (l - k) * (3 * sidQ n) := by
  induction l, hkl using Nat.le_induction with
  | base => simp
  | succ l hl ih =>
      have h1 := sval_step_le (n := n) (k := l) h
      have h2 : (l + 1 - k) * (3 * sidQ n) = (l - k) * (3 * sidQ n) + 3 * sidQ n := by
        rw [show l + 1 - k = (l - k) + 1 by omega]
        ring
      rw [h2]
      omega

theorem le_sval_add_gap {n : ℕ} (hn : N₀ ≤ n) :
    n ≤ sval n (sidK n) + 4 * sidQ n := by
  have hq := sidQ_pos (sqrt_ne_zero hn)
  have hK := sidK_succ hn
  have h1 : n < 2 * sidQ n * (sidK n + 1) + 2 * sidQ n := by
    rw [hK]
    have hdiv := Nat.div_add_mod n (2 * sidQ n)
    have hlt : n % (2 * sidQ n) < 2 * sidQ n := Nat.mod_lt _ (by positivity)
    omega
  have h2 := le_sval n (sidK n)
  have e : 2 * sidQ n * (sidK n + 1) = 2 * sidQ n * sidK n + 2 * sidQ n := by ring
  omega

/-- The Sidon set `S_n = [n] ∩ {s_k | 1 ≤ k ≤ K}` of the paper. -/
noncomputable def sn (n : ℕ) : Finset ℕ := (Finset.Icc 1 (sidK n)).image (sval n)

theorem mem_sn {n : ℕ} {s : ℕ} : s ∈ sn n ↔ ∃ k, 1 ≤ k ∧ k ≤ sidK n ∧ sval n k = s := by
  simp only [sn, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨k, ⟨h1, h2⟩, rfl⟩; exact ⟨k, h1, h2, rfl⟩
  · rintro ⟨k, h1, h2, rfl⟩; exact ⟨k, ⟨h1, h2⟩, rfl⟩

theorem sval_mem_sn {n k : ℕ} (_hn : N₀ ≤ n) (hk1 : 1 ≤ k) (hk2 : k ≤ sidK n) :
    sval n k ∈ sn n :=
  mem_sn.mpr ⟨k, hk1, hk2, rfl⟩

theorem sn_card {n : ℕ} (hn : N₀ ≤ n) : (sn n).card = sidK n := by
  rw [sn, Finset.card_image_of_injective _ (sval_injective (sqrt_ne_zero hn)), Nat.card_Icc]
  omega

theorem sn_nonempty {n : ℕ} (hn : N₀ ≤ n) : (sn n).Nonempty := by
  have h := two_le_sidK hn
  exact ⟨sval n 1, sval_mem_sn hn le_rfl (by omega)⟩

theorem sn_subset {n : ℕ} (hn : N₀ ≤ n) : ∀ s ∈ sn n, 1 ≤ s ∧ s ≤ n := by
  intro s hs
  obtain ⟨k, hk1, hk2, rfl⟩ := mem_sn.mp hs
  exact ⟨one_le_sval (sqrt_ne_zero hn) hk1, sval_le_n hn hk2⟩





/-! ### The Sidon property of `S_n` -/

/-- The elementary congruence `s_k ≡ k² (mod q)`. -/
theorem sval_modEq_sq (n k : ℕ) : sval n k ≡ k * k [MOD sidQ n] := by
  have hz : sidQ n * (2 * k) ≡ 0 [MOD sidQ n] :=
    Nat.modEq_zero_iff_dvd.mpr ⟨2 * k, rfl⟩
  have h2 : sval n k = sidQ n * (2 * k) + k * k % sidQ n := by
    rw [sval_def]; ring
  rw [h2]
  have := hz.add (Nat.mod_modEq (k * k) (sidQ n))
  simpa using this

/-- **`S_n` is a Sidon set (additive form).**  If a sum of two elements of `S_n` equals another
such sum, then the two pairs of summands coincide (as unordered pairs).  This is the form of
the Sidon property used for the rectangle-free matrix `Z_{n,S_n}` below. -/
theorem sn_sidon {n : ℕ} (hn : N₀ ≤ n) {a b c d : ℕ}
    (ha1 : 1 ≤ a) (ha2 : a ≤ sidK n) (hb1 : 1 ≤ b) (hb2 : b ≤ sidK n)
    (hc1 : 1 ≤ c) (hc2 : c ≤ sidK n) (hd1 : 1 ≤ d) (hd2 : d ≤ sidK n)
    (h : sval n a + sval n b = sval n c + sval n d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  classical
  have hq0 : 0 < sidQ n := sidQ_pos (sqrt_ne_zero hn)
  have hq2 : 2 ≤ sidQ n := two_le_sidQ (sqrt_ne_zero hn)
  have hqne : sidQ n ≠ 2 := sidQ_ne_two hn
  have haq : a < sidQ n := by have := sidK_lt_sidQ hn; omega
  have hbq : b < sidQ n := by have := sidK_lt_sidQ hn; omega
  have hcq : c < sidQ n := by have := sidK_lt_sidQ hn; omega
  have hdq : d < sidQ n := by have := sidK_lt_sidQ hn; omega
  have hrem : ∀ k : ℕ, k * k % sidQ n < sidQ n := fun k => Nat.mod_lt _ hq0
  -- (1) the two quotients and the two remainder sums
  have hraw : 2 * sidQ n * (a + b) + (a * a % sidQ n + b * b % sidQ n)
      = 2 * sidQ n * (c + d) + (c * c % sidQ n + d * d % sidQ n) := by
    have h1 : sval n a + sval n b
        = 2 * sidQ n * (a + b) + (a * a % sidQ n + b * b % sidQ n) := by
      simp only [sval_def]; ring
    have h2 : sval n c + sval n d
        = 2 * sidQ n * (c + d) + (c * c % sidQ n + d * d % sidQ n) := by
      simp only [sval_def]; ring
    rw [h1, h2] at h
    exact h
  have hAb : 2 * sidQ n * (a + b) + (a * a % sidQ n + b * b % sidQ n)
      < 2 * sidQ n * (a + b + 1) := by
    have e : 2 * sidQ n * (a + b + 1) = 2 * sidQ n * (a + b) + 2 * sidQ n := by ring
    rw [e]
    have h1 := hrem a
    have h2 := hrem b
    omega
  have hBd : 2 * sidQ n * (c + d) + (c * c % sidQ n + d * d % sidQ n)
      < 2 * sidQ n * (c + d + 1) := by
    have e : 2 * sidQ n * (c + d + 1) = 2 * sidQ n * (c + d) + 2 * sidQ n := by ring
    rw [e]
    have h1 := hrem c
    have h2 := hrem d
    omega
  have hab : a + b = c + d := by
    rcases lt_trichotomy (a + b) (c + d) with hlt | heq | hgt
    · exfalso
      have hmul : 2 * sidQ n * (a + b + 1) ≤ 2 * sidQ n * (c + d) :=
        Nat.mul_le_mul_left _ (by omega)
      have h2 : 2 * sidQ n * (c + d)
          ≤ 2 * sidQ n * (c + d) + (c * c % sidQ n + d * d % sidQ n) :=
        Nat.le_add_right _ _
      have h3 := lt_of_lt_of_le hAb (le_trans hmul h2)
      rw [hraw] at h3
      exact absurd h3 (lt_irrefl _)
    · exact heq
    · exfalso
      have hmul : 2 * sidQ n * (c + d + 1) ≤ 2 * sidQ n * (a + b) :=
        Nat.mul_le_mul_left _ (by omega)
      have h2 : 2 * sidQ n * (a + b)
          ≤ 2 * sidQ n * (a + b) + (a * a % sidQ n + b * b % sidQ n) :=
        Nat.le_add_right _ _
      have h3 := lt_of_lt_of_le hBd (le_trans hmul h2)
      rw [hraw] at h3
      exact absurd h3 (lt_irrefl _)
  have hrab : a * a % sidQ n + b * b % sidQ n
      = c * c % sidQ n + d * d % sidQ n := by
    rw [hab] at hraw
    omega
  -- (2) the congruence `a² + b² ≡ c² + d² (mod q)`
  have hZ : (a : ZMod (sidQ n)) ^ 2 + (b : ZMod (sidQ n)) ^ 2
      = (c : ZMod (sidQ n)) ^ 2 + (d : ZMod (sidQ n)) ^ 2 := by
    have h1 : ((a * a % sidQ n : ℕ) : ZMod (sidQ n)) = (a : ZMod (sidQ n)) ^ 2 := by
      rw [ZMod.natCast_mod]; push_cast; ring
    have h2 : ((b * b % sidQ n : ℕ) : ZMod (sidQ n)) = (b : ZMod (sidQ n)) ^ 2 := by
      rw [ZMod.natCast_mod]; push_cast; ring
    have h3 : ((c * c % sidQ n : ℕ) : ZMod (sidQ n)) = (c : ZMod (sidQ n)) ^ 2 := by
      rw [ZMod.natCast_mod]; push_cast; ring
    have h4 : ((d * d % sidQ n : ℕ) : ZMod (sidQ n)) = (d : ZMod (sidQ n)) ^ 2 := by
      rw [ZMod.natCast_mod]; push_cast; ring
    have hpos := congrArg (fun t : ℕ => (t : ZMod (sidQ n))) hrab
    push_cast at hpos
    rw [h1, h2, h3, h4] at hpos
    exact hpos
  -- (3) eliminate `b`
  have : Fact (Nat.Prime (sidQ n)) := ⟨sidQ_prime (sqrt_ne_zero hn)⟩
  have habZ : (b : ZMod (sidQ n))
      = (c : ZMod (sidQ n)) + (d : ZMod (sidQ n)) - (a : ZMod (sidQ n)) := by
    have h1 : ((a + b : ℕ) : ZMod (sidQ n)) = ((c + d : ℕ) : ZMod (sidQ n)) := by
      rw [hab]
    push_cast at h1
    linear_combination h1
  have htwo : (2 : ZMod (sidQ n)) ≠ 0 := by
    intro h0
    have hd : sidQ n ∣ 2 := by
      rw [← Nat.modEq_zero_iff_dvd, ← ZMod.natCast_eq_natCast_iff]
      simpa using h0
    have hle : sidQ n ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    omega
  -- (4) the quadratic identity, in the form `2 * (a - c) * (a - d) = 0`
  have hkey : (2 : ZMod (sidQ n)) * (((a : ZMod (sidQ n)) - (c : ZMod (sidQ n)))
      * ((a : ZMod (sidQ n)) - (d : ZMod (sidQ n)))) = 0 := by
    have hmain := hZ
    rw [habZ] at hmain
    linear_combination hmain
  have hfac : ((a : ZMod (sidQ n)) - (c : ZMod (sidQ n))) * ((a : ZMod (sidQ n))
      - (d : ZMod (sidQ n))) = 0 := by
    rcases mul_eq_zero.mp hkey with h2 | h
    · exact absurd h2 htwo
    · exact h
  -- (5) conclude `a = c` or `a = d`
  have hnat : ∀ {x y : ℕ}, x < sidQ n → y < sidQ n →
      ((x : ZMod (sidQ n)) = (y : ZMod (sidQ n)) → x = y) := by
    intro x y hx hy hxy
    exact (ZMod.natCast_eq_natCast_iff x y (sidQ n)).mp hxy |>.eq_of_lt_of_lt hx hy
  rcases mul_eq_zero.mp hfac with hac | had
  · have hac' : a = c := hnat haq hcq (sub_eq_zero.mp hac)
    exact Or.inl ⟨hac', by omega⟩
  · have had' : a = d := hnat haq hdq (sub_eq_zero.mp had)
    exact Or.inr ⟨had', by omega⟩

/-- **`S_n` is a Sidon set (difference form, as stated in the paper).**  All the differences
`s_i - s_j` with `i ≠ j` are pairwise distinct. -/
theorem sn_sidon_diff {n : ℕ} (hn : N₀ ≤ n) {a b c d : ℕ}
    (ha1 : 1 ≤ a) (ha2 : a ≤ sidK n) (hb1 : 1 ≤ b) (hb2 : b ≤ sidK n)
    (hc1 : 1 ≤ c) (hc2 : c ≤ sidK n) (hd1 : 1 ≤ d) (hd2 : d ≤ sidK n)
    (hab : a ≠ b) (_hcd : c ≠ d)
    (h : (sval n a : ℤ) - (sval n b : ℤ) = (sval n c : ℤ) - (sval n d : ℤ)) :
    a = c ∧ b = d := by
  have h' : sval n a + sval n d = sval n b + sval n c := by
    have := h
    omega
  have key : (a = b ∧ d = c) ∨ (a = c ∧ d = b) :=
    sn_sidon hn ha1 ha2 hd1 hd2 hb1 hb2 hc1 hc2 h'
  rcases key with ⟨rfl, -⟩ | ⟨h1, h2⟩
  · exact absurd rfl hab
  · exact ⟨h1, h2.symm⟩

/-- A sum of two pairs of elements of `S_n` determines the pairs. -/
theorem sn_add_cancel {n : ℕ} (hn : N₀ ≤ n) {s₁ s₂ s₃ s₄ : ℕ}
    (h₁ : s₁ ∈ sn n) (h₂ : s₂ ∈ sn n) (h₃ : s₃ ∈ sn n) (h₄ : s₄ ∈ sn n)
    (h : s₁ + s₂ = s₃ + s₄) :
    (s₁ = s₃ ∧ s₂ = s₄) ∨ (s₁ = s₄ ∧ s₂ = s₃) := by
  obtain ⟨a, ha1, ha2, rfl⟩ := mem_sn.mp h₁
  obtain ⟨b, hb1, hb2, rfl⟩ := mem_sn.mp h₂
  obtain ⟨c, hc1, hc2, rfl⟩ := mem_sn.mp h₃
  obtain ⟨d, hd1, hd2, rfl⟩ := mem_sn.mp h₄
  rcases sn_sidon hn ha1 ha2 hb1 hb2 hc1 hc2 hd1 hd2 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-! ### Counting the elements of `S_n` in an interval -/

/-- `sval n k ≤ 3qk`: the elements of `S_n` grow at most linearly. -/
theorem sval_le_three_mul (n : ℕ) (hn : N₀ ≤ n) {k : ℕ} (hk : 1 ≤ k) :
    sval n k ≤ 3 * sidQ n * k := by
  have hq := sidQ_pos (sqrt_ne_zero hn)
  have hmod : k * k % sidQ n < sidQ n := Nat.mod_lt _ hq
  rw [sval_def]
  nlinarith

/-- `sval n 0 = 0`. -/
theorem sval_zero (n : ℕ) : sval n 0 = 0 := by
  rw [sval_def]; simp

/-- Arithmetic step: `(c+1)·3q ≤ 3q·(c+2)`. -/
theorem step_succ_mul (c q : ℕ) : (c + 1) * (3 * q) ≤ 3 * q * (c + 2) := by
  rw [Nat.mul_comm (c + 1) (3 * q)]
  exact Nat.mul_le_mul_left _ (by omega)

/-- Arithmetic step: `c·3q + 4q ≤ 3q·(c+2)`. -/
theorem step_add_four_mul (c q : ℕ) : c * (3 * q) + 4 * q ≤ 3 * q * (c + 2) := by
  have h : 3 * q * (c + 2) = c * (3 * q) + 6 * q := by ring
  omega

/-- Arithmetic step: `3q·c + 4q ≤ 3q·(c+2)`. -/
theorem step_add_four_mul' (c q : ℕ) : 3 * q * c + 4 * q ≤ 3 * q * (c + 2) := by
  have h : 3 * q * (c + 2) = 3 * q * c + 6 * q := by ring
  omega

/-- The number of elements of `S_n` that are at most `x`. -/
noncomputable def idxLe (n x : ℕ) : ℕ :=
  ((Finset.Icc 1 (sidK n)).filter (fun k => sval n k ≤ x)).card

/-- `idxLe n x ≤ K`. -/
theorem idxLe_le (n : ℕ) (_hn : N₀ ≤ n) (x : ℕ) : idxLe n x ≤ sidK n := by
  rw [idxLe]
  calc _ ≤ (Finset.Icc 1 (sidK n)).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = sidK n := by rw [Nat.card_Icc]; omega

/-- The indices `k ∈ [1, K]` with `sval n k ≤ x` form an initial segment of `[1, K]`. -/
theorem idxLe_filter (n : ℕ) (hn : N₀ ≤ n) (x : ℕ) :
    (Finset.Icc 1 (sidK n)).filter (fun k => sval n k ≤ x) = Finset.Icc 1 (idxLe n x) := by
  classical
  have hsmono : Monotone (sval n) := (sval_strictMono (sqrt_ne_zero hn)).monotone
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hk1, hkK⟩, hkx⟩
    refine ⟨hk1, ?_⟩
    have hsub : Finset.Icc 1 k ⊆
        (Finset.Icc 1 (sidK n)).filter (fun k => sval n k ≤ x) := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj.1, le_trans hj.2 hkK⟩,
        le_trans (hsmono hj.2) hkx⟩
    have h := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h
    rw [idxLe]
    omega
  · rintro ⟨hk1, hkf⟩
    have hkK : k ≤ sidK n := le_trans hkf (idxLe_le n hn x)
    refine ⟨⟨hk1, hkK⟩, ?_⟩
    by_contra hcon
    push Not at hcon
    have hlt : ∀ j ∈ (Finset.Icc 1 (sidK n)).filter (fun k => sval n k ≤ x), j < k := by
      intro j hj
      obtain ⟨hjI, hjx⟩ := Finset.mem_filter.mp hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hjI).1
      by_contra hjk
      push Not at hjk
      have hle : sval n k ≤ sval n j := hsmono hjk
      omega
    have hsub : (Finset.Icc 1 (sidK n)).filter (fun k => sval n k ≤ x) ⊆
        Finset.Icc 1 (k - 1) := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).1
      exact Finset.mem_Icc.mpr ⟨hj1, by have := hlt j hj; omega⟩
    have h := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h
    rw [idxLe] at hkf
    omega

/-- `sval n (idxLe n x) ≤ x` when the latter index is nonzero. -/
theorem sval_idxLe_le (n : ℕ) (hn : N₀ ≤ n) {x : ℕ} (h : 1 ≤ idxLe n x) :
    sval n (idxLe n x) ≤ x := by
  have hf := idxLe_filter n hn x
  have hmem : idxLe n x ∈ (Finset.Icc 1 (sidK n)).filter (fun k => sval n k ≤ x) := by
    rw [hf]
    exact Finset.mem_Icc.mpr ⟨h, le_rfl⟩
  exact (Finset.mem_filter.mp hmem).2

/-- `x < sval n (idxLe n x + 1)` when the latter index is still in `[1, K]`. -/
theorem sval_idxLe_succ_gt (n : ℕ) (hn : N₀ ≤ n) {x : ℕ} (h : idxLe n x + 1 ≤ sidK n) :
    x < sval n (idxLe n x + 1) := by
  have hf := idxLe_filter n hn x
  by_contra hle
  push Not at hle
  have hmem : idxLe n x + 1 ∈ (Finset.Icc 1 (sidK n)).filter (fun k => sval n k ≤ x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, h⟩, hle⟩
  rw [hf, Finset.mem_Icc] at hmem
  omega

/-- The elements of `S_n` that are at most `x` are exactly `s_1, …, s_{idxLe x}`. -/
theorem sn_filter_card (n : ℕ) (hn : N₀ ≤ n) (x : ℕ) :
    ((sn n).filter (fun s => s ≤ x)).card = idxLe n x := by
  classical
  have hinj := sval_injective (sqrt_ne_zero hn)
  have himg : (sn n).filter (fun s => s ≤ x) =
      ((Finset.Icc 1 (sidK n)).filter (fun k => sval n k ≤ x)).image (sval n) := by
    ext s
    simp only [sn, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨k, hk, rfl⟩, hle⟩
      exact ⟨k, ⟨hk, hle⟩, rfl⟩
    · rintro ⟨k, ⟨hk, hle⟩, rfl⟩
      exact ⟨⟨k, hk, rfl⟩, hle⟩
  rw [himg, Finset.card_image_of_injective _ hinj, idxLe]

/-- Splitting at `t`: the elements of `S_n` that are at most `X` are those that are at most
`t` together with those in `(t, X]`. -/
theorem idxLe_add_card (n : ℕ) (hn : N₀ ≤ n) {t X : ℕ} (htX : t ≤ X) :
    idxLe n X = idxLe n t + ((sn n).filter (fun s => t < s ∧ s ≤ X)).card := by
  classical
  have hpart : ((sn n).filter (fun s => s ≤ X)).card =
      ((sn n).filter (fun s => s ≤ t)).card +
        ((sn n).filter (fun s => t < s ∧ s ≤ X)).card := by
    have hdisj : Disjoint ((sn n).filter (fun s => s ≤ t))
        ((sn n).filter (fun s => t < s ∧ s ≤ X)) := by
      rw [Finset.disjoint_filter]
      rintro s - h1 h2
      omega
    rw [← Finset.card_union_of_disjoint hdisj]
    congr 1
    ext s
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hs, hle⟩
      rcases Nat.lt_or_ge t s with h | h
      · exact Or.inr ⟨hs, h, hle⟩
      · exact Or.inl ⟨hs, h⟩
    · rintro (⟨hs, h⟩ | ⟨hs, h, hle⟩)
      · exact ⟨hs, le_trans h htX⟩
      · exact ⟨hs, hle⟩
  rw [sn_filter_card n hn X, sn_filter_card n hn t] at hpart
  omega

/-- **Counting lemma.**  Every interval `(t, X] ⊆ [1, n]` contains at least `(X-t)/(3q) - 2`
elements of `S_n`. -/
theorem sn_Ioc_card_ge (n : ℕ) (hn : N₀ ≤ n) {t X : ℕ} (hX : X ≤ n) :
    X - t ≤ 3 * sidQ n * (((sn n).filter (fun s => t < s ∧ s ≤ X)).card + 2) := by
  classical
  have hsq := sqrt_ne_zero hn
  set c := ((sn n).filter (fun s => t < s ∧ s ≤ X)).card with hc
  rcases Nat.lt_or_ge X t with hXt | hXt
  · have hzero : X - t = 0 := by omega
    rw [hzero]
    exact Nat.zero_le _
  have hidx := idxLe_add_card n hn hXt
  rcases Nat.lt_or_ge (idxLe n X) (sidK n) with hlt | hge
  · -- the next element of `S_n` after `X` still exists
    have hnext : X < sval n (idxLe n X + 1) := sval_idxLe_succ_gt n hn (by omega)
    have hgap := sval_le_add_mul_gap (n := n) hsq (k := idxLe n t) (l := idxLe n X + 1)
      (by omega)
    have hsub : (idxLe n X + 1) - idxLe n t = c + 1 := by omega
    rw [hsub] at hgap
    rcases Nat.eq_or_lt_of_le (Nat.zero_le (idxLe n t)) with hf0 | hf0
    · -- `t` lies before the first element of `S_n`
      rw [← hf0, sval_zero] at hgap
      have hmid : X - t ≤ (c + 1) * (3 * sidQ n) := by omega
      exact le_trans hmid (step_succ_mul c (sidQ n))
    · -- `s_{idxLe t} ≤ t`, so the gap from `t` to `X` is accounted for
      have hfle : sval n (idxLe n t) ≤ t := sval_idxLe_le n hn hf0
      have hmid : X - t ≤ (c + 1) * (3 * sidQ n) := by omega
      exact le_trans hmid (step_succ_mul c (sidQ n))
  · -- the interval reaches the last element of `S_n`
    have hidxX : idxLe n X = sidK n := le_antisymm (idxLe_le n hn X) hge
    have hK := two_le_sidK hn
    have htop : X ≤ sval n (sidK n) + 4 * sidQ n :=
      le_trans hX (le_sval_add_gap (n := n) hn)
    rcases Nat.eq_or_lt_of_le (Nat.zero_le (idxLe n t)) with hf0 | hf0
    · have hcK : c = sidK n := by omega
      have hb := sval_le_three_mul n hn (k := sidK n) (by omega)
      have hmid : X - t ≤ 3 * sidQ n * sidK n + 4 * sidQ n := by omega
      rw [hcK]
      exact le_trans hmid (step_add_four_mul' (sidK n) (sidQ n))
    · have hfle : sval n (idxLe n t) ≤ t := sval_idxLe_le n hn hf0
      have hgap := sval_le_add_mul_gap (n := n) hsq (k := idxLe n t) (l := sidK n)
        (by omega)
      have hsub : sidK n - idxLe n t = c := by omega
      rw [hsub] at hgap
      have hmid : X - t ≤ c * (3 * sidQ n) + 4 * sidQ n := by omega
      exact le_trans hmid (step_add_four_mul c (sidQ n))


/-! ## Part 11: the cyclic matrix `Z_{n,S_n}` and Corollary 4 -/

/-! ### The block size `m = ⌈n^{3/4}⌉` -/

/-- `m = (⌊n^{1/4}⌋ + 1)³`, the size of the block `Z` of `Z_{n,S_n}`: a number of order
`n^{3/4}`, for which `n^{3/4} ≤ m ≤ 8·n^{3/4}` (the paper takes `m = ⌈n^{3/4}⌉`). -/
def mZ (n : ℕ) : ℕ := (Nat.sqrt (Nat.sqrt n) + 1) ^ 3

theorem mZ_pos (n : ℕ) : 0 < mZ n := by unfold mZ; positivity

/-- `n^{3/4} ≤ m`: in the division-free form `n³ ≤ m⁴`. -/
theorem pow_three_le_mZ_pow_four (n : ℕ) : n ^ 3 ≤ (mZ n) ^ 4 := by
  set r := Nat.sqrt n with hr
  set k := Nat.sqrt r with hk
  have h1 : n ≤ (r + 1) ^ 2 := by
    have h := Nat.lt_succ_sqrt n
    rw [← hr] at h
    have h' : n ≤ (r + 1) * (r + 1) := by
      simp only [Nat.succ_eq_add_one] at h
      omega
    rwa [pow_two]
  have h2 : r + 1 ≤ (k + 1) ^ 2 := by
    have h := Nat.lt_succ_sqrt r
    rw [← hk] at h
    have h' : r + 1 ≤ (k + 1) * (k + 1) := by
      simp only [Nat.succ_eq_add_one] at h
      omega
    rwa [pow_two]
  have h3 : n ^ 3 ≤ (r + 1) ^ 6 :=
    calc n ^ 3 ≤ ((r + 1) ^ 2) ^ 3 := Nat.pow_le_pow_left h1 3
      _ = (r + 1) ^ 6 := by ring
  have h4 : (r + 1) ^ 6 ≤ (k + 1) ^ 12 :=
    calc (r + 1) ^ 6 ≤ ((k + 1) ^ 2) ^ 6 := Nat.pow_le_pow_left h2 6
      _ = (k + 1) ^ 12 := by ring
  have hm : mZ n = (k + 1) ^ 3 := by
    unfold mZ
    rw [← hr, ← hk]
  calc n ^ 3 ≤ (r + 1) ^ 6 := h3
    _ ≤ (k + 1) ^ 12 := h4
    _ = (mZ n) ^ 4 := by rw [hm]; ring

/-- The upper bound `m⁴ ≤ 4096·n³`, i.e. `m ≤ 8·n^{3/4}`. -/
theorem mZ_pow_four_le (n : ℕ) (hn : N₀ ≤ n) : (mZ n) ^ 4 ≤ 4096 * n ^ 3 := by
  set r := Nat.sqrt n with hr
  set k := Nat.sqrt r with hk
  have hr1 : 1 ≤ r := by
    rw [hr]
    rw [Nat.le_sqrt]
    unfold N₀ at hn
    omega
  have hk2 : k * k ≤ r := by rw [hk]; simpa [pow_two] using Nat.sqrt_le' r
  have hk_le : k ≤ r := by nlinarith
  have hsq : (k + 1) ^ 2 ≤ 4 * r := by nlinarith
  have h4 : (k + 1) ^ 4 ≤ 16 * r ^ 2 := by
    calc (k + 1) ^ 4 = ((k + 1) ^ 2) ^ 2 := by ring
      _ ≤ (4 * r) ^ 2 := Nat.pow_le_pow_left hsq 2
      _ = 16 * r ^ 2 := by ring
  have hr2 : r ^ 2 ≤ n := by
    rw [hr]; simpa [pow_two] using Nat.sqrt_le' n
  have h16 : (k + 1) ^ 4 ≤ 16 * n := le_trans h4 (Nat.mul_le_mul_left _ hr2)
  have hm : mZ n = (k + 1) ^ 3 := by
    unfold mZ
    rw [← hr, ← hk]
  calc (mZ n) ^ 4 = ((k + 1) ^ 4) ^ 3 := by rw [hm]; ring
    _ ≤ (16 * n) ^ 3 := Nat.pow_le_pow_left h16 3
    _ = 4096 * n ^ 3 := by ring

/-- `2m ≤ n`: the block is at most half of the matrix. -/
theorem two_mul_mZ_le (n : ℕ) (hn : N₀ ≤ n) : 2 * mZ n ≤ n := by
  have hn40 : 65536 ≤ n := by unfold N₀ at hn; omega
  have hpow := mZ_pow_four_le n hn
  have h16 : 16 * (mZ n) ^ 4 ≤ n ^ 4 := by
    calc 16 * (mZ n) ^ 4 ≤ 16 * (4096 * n ^ 3) := Nat.mul_le_mul_left _ hpow
      _ = 65536 * n ^ 3 := by ring
      _ ≤ n * n ^ 3 := Nat.mul_le_mul_right _ hn40
      _ = n ^ 4 := by ring
  have h2 : (4 * (mZ n) ^ 2) ^ 2 ≤ (n ^ 2) ^ 2 := by
    calc (4 * (mZ n) ^ 2) ^ 2 = 16 * (mZ n) ^ 4 := by ring
      _ ≤ n ^ 4 := h16
      _ = (n ^ 2) ^ 2 := by ring
  have h3 : 4 * (mZ n) ^ 2 ≤ n ^ 2 := (Nat.pow_le_pow_iff_left (by norm_num : (2:ℕ) ≠ 0)).mp h2
  have h4 : (2 * mZ n) ^ 2 ≤ n ^ 2 := by
    calc (2 * mZ n) ^ 2 = 4 * (mZ n) ^ 2 := by ring
      _ ≤ n ^ 2 := h3
  exact (Nat.pow_le_pow_iff_left (by norm_num : (2:ℕ) ≠ 0)).mp h4

theorem mZ_le_n (n : ℕ) (hn : N₀ ≤ n) : mZ n ≤ n := by
  have := two_mul_mZ_le n hn
  have := mZ_pos n
  omega

/-! ### The cyclic matrix `Z_{n,S}` of Section 3 -/

/-- The cyclic boolean matrix `Z_{n,S}` of Section 3: its first row has ones exactly in the
positions `S ⊆ [n]`, and every next row is obtained from the previous one by a cyclic shift to
the right. -/
noncomputable def Zmat (n : ℕ) (S : Finset ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => if ((j.val + n - i.val) % n) + 1 ∈ S then 1 else 0

theorem Zmat_apply {n : ℕ} {S : Finset ℕ} {i j : Fin n} :
    Zmat n S i j = 1 ↔ ((j.val + n - i.val) % n) + 1 ∈ S := by
  unfold Zmat
  by_cases h : ((j.val + n - i.val) % n) + 1 ∈ S <;> simp [h]

/-! ### The upper-right block `Z` of `Z_{n,S_n}` and its transpose -/

/-- The upper-right `m × (n-m)` block of `Z_{n,S_n}`: its rows are the rows `0, …, m-1` and its
columns are the columns `m, …, n-1` of `Z_{n,S_n}`. -/
noncomputable def Zblk (n : ℕ) (hn : N₀ ≤ n) : Matrix (Fin (mZ n)) (Fin (n - mZ n)) (ZMod 2) :=
  fun i t => Zmat n (sn n) ⟨i.val, by have := i.isLt; have := mZ_le_n n hn; omega⟩
    ⟨mZ n + t.val, by have := t.isLt; have := mZ_le_n n hn; omega⟩

theorem Zblk_apply {n : ℕ} (hn : N₀ ≤ n) (i : Fin (mZ n)) (t : Fin (n - mZ n)) :
    Zblk n hn i t = 1 ↔ mZ n + t.val - i.val + 1 ∈ sn n := by
  rw [Zblk, Zmat_apply]
  have hi := i.isLt
  have ht := t.isLt
  have hmn := mZ_le_n n hn
  have hk : mZ n + t.val - i.val < n := by omega
  have hsplit : mZ n + t.val + n - i.val = n + (mZ n + t.val - i.val) := by omega
  rw [hsplit, Nat.add_comm n (mZ n + t.val - i.val), Nat.add_mod_right, Nat.mod_eq_of_lt hk]

/-- The transpose of the block `Z`: the matrix whose rows are the columns of `Z`, read in the
ambient space of the `m` columns of `Z_{n,S_n}`. -/
noncomputable def ZT (n : ℕ) (hn : N₀ ≤ n) : Matrix (Fin (n - mZ n)) (Fin (mZ n)) (ZMod 2) :=
  Matrix.transpose (Zblk n hn)

theorem ZT_apply {n : ℕ} (hn : N₀ ≤ n) (t : Fin (n - mZ n)) (i : Fin (mZ n)) :
    ZT n hn t i = 1 ↔ mZ n + t.val - i.val + 1 ∈ sn n := by
  rw [ZT, Matrix.transpose_apply, Zblk_apply]

theorem ZT_apply_ne_zero {n : ℕ} (hn : N₀ ≤ n) (t : Fin (n - mZ n)) (i : Fin (mZ n)) :
    ZT n hn t i ≠ 0 ↔ mZ n + t.val - i.val + 1 ∈ sn n := by
  rw [← ZT_apply hn]
  constructor
  · intro h
    rcases zmod2_eq_zero_or_one (ZT n hn t i) with h0 | h1
    · exact absurd h0 h
    · exact h1
  · intro h h0
    rw [h0] at h
    exact zero_ne_one h

theorem mem_supp_ZT {n : ℕ} (hn : N₀ ≤ n) {t : Fin (n - mZ n)} {i : Fin (mZ n)} :
    i ∈ supp (mZ n) (ZT n hn t) ↔ mZ n + t.val - i.val + 1 ∈ sn n := by
  rw [supp, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact ZT_apply_ne_zero hn t i

/-- The support of a row of `Zᵀ` is a window of `S_n`: its size is the number of elements of
`S_n ∩ (t+1, t+m+1]`. -/
theorem card_supp_ZT (n : ℕ) (hn : N₀ ≤ n) (t : Fin (n - mZ n)) :
    (supp (mZ n) (ZT n hn t)).card
      = ((sn n).filter (fun s => t.val + 1 < s ∧ s ≤ t.val + mZ n + 1)).card := by
  classical
  refine Finset.card_bij (fun (i : Fin (mZ n)) _ => mZ n + t.val - i.val + 1) ?_ ?_ ?_
  · intro i hi
    rw [mem_supp_ZT hn] at hi
    rw [Finset.mem_filter]
    have hi' := i.isLt
    exact ⟨hi, by omega⟩
  · intro i _ j _ hij
    have hi := i.isLt
    have hj := j.isLt
    exact Fin.ext (by omega)
  · intro s hs
    rw [Finset.mem_filter] at hs
    obtain ⟨hsS, hlt, hle⟩ := hs
    have hlt' := t.isLt
    have hmn := mZ_le_n n hn
    refine ⟨⟨mZ n + t.val + 1 - s, by omega⟩, ?_, ?_⟩
    · rw [mem_supp_ZT hn]
      have he : mZ n + t.val - (mZ n + t.val + 1 - s) + 1 = s := by omega
      rw [he]
      exact hsS
    · show mZ n + t.val - (mZ n + t.val + 1 - s) + 1 = s
      omega

theorem weight_ZT (n : ℕ) (hn : N₀ ≤ n) (t : Fin (n - mZ n)) :
    weight (Finset.univ : Finset (Fin (mZ n))) (ZT n hn t)
      = ((sn n).filter (fun s => t.val + 1 < s ∧ s ≤ t.val + mZ n + 1)).card := by
  rw [weight_eq_card_supp, card_supp_ZT n hn t]

/-! ### Size relations for `m = ⌈n^{3/4}⌉` -/

/-- `c·√n ≤ m` whenever `c⁴ ≤ n`: since `m⁴ ≥ n³`. -/
theorem mul_sqrt_le_mZ (n : ℕ) (_hn : N₀ ≤ n) {c : ℕ} (hc : c ^ 4 ≤ n) :
    c * Nat.sqrt n ≤ mZ n := by
  have hsq : Nat.sqrt n * Nat.sqrt n ≤ n := by simpa [pow_two] using Nat.sqrt_le' n
  have h4 : (c * Nat.sqrt n) ^ 4 ≤ n ^ 3 := by
    calc (c * Nat.sqrt n) ^ 4 = c ^ 4 * (Nat.sqrt n * Nat.sqrt n) ^ 2 := by ring
      _ ≤ n * n ^ 2 := Nat.mul_le_mul hc (Nat.pow_le_pow_left hsq 2)
      _ = n ^ 3 := by ring
  have hm4 := pow_three_le_mZ_pow_four n
  exact (Nat.pow_le_pow_iff_left (by norm_num : (4 : ℕ) ≠ 0)).mp (le_trans h4 hm4)

/-- `72·q ≤ m`: the row weight bound `m/(12q)` is at least `6`. -/
theorem seventy_two_mul_sidQ_le (n : ℕ) (hn : N₀ ≤ n) : 72 * sidQ n ≤ mZ n := by
  have hc : (144 : ℕ) ^ 4 ≤ n := by
    have h : (144 : ℕ) ^ 4 ≤ 2 ^ 40 := by norm_num
    unfold N₀ at hn
    omega
  have h1 := mul_sqrt_le_mZ n hn hc
  have h2 := sidQ_le (sqrt_ne_zero hn)
  calc 72 * sidQ n ≤ 72 * (2 * Nat.sqrt n) := Nat.mul_le_mul_left _ h2
    _ = 144 * Nat.sqrt n := by ring
    _ ≤ mZ n := h1

/-- The guaranteed weight `s = m/(12q)` of every row of the block `Zᵀ`. -/
noncomputable def sZ (n : ℕ) : ℕ := mZ n / (12 * sidQ n)

theorem six_le_sZ (n : ℕ) (hn : N₀ ≤ n) : 6 ≤ sZ n := by
  rw [sZ, Nat.le_div_iff_mul_le (by have := sidQ_pos (sqrt_ne_zero hn); omega)]
  have h := seventy_two_mul_sidQ_le n hn
  nlinarith

theorem sZ_le_mZ (n : ℕ) (_hn : N₀ ≤ n) : sZ n ≤ mZ n :=
  Nat.div_le_self (mZ n) (12 * sidQ n)

/-- **The row weight bound.**  Every row of `Zᵀ` has weight at least `s = m/(12q)`: the row is a
window of `S_n` of length `m`, and `S_n` has no gap longer than `3q`. -/
theorem weight_ZT_ge (n : ℕ) (hn : N₀ ≤ n) (t : Fin (n - mZ n)) :
    sZ n ≤ weight (Finset.univ : Finset (Fin (mZ n))) (ZT n hn t) := by
  classical
  have hq := sidQ_pos (sqrt_ne_zero hn)
  set c := ((sn n).filter (fun s => t.val + 1 < s ∧ s ≤ t.val + mZ n + 1)).card with hc
  have hwt := weight_ZT n hn t
  have hX : t.val + mZ n + 1 ≤ n := by have := t.isLt; have := mZ_le_n n hn; omega
  have hbound := sn_Ioc_card_ge n hn (t := t.val + 1) (X := t.val + mZ n + 1) hX
  have hsub : t.val + mZ n + 1 - (t.val + 1) = mZ n := by omega
  rw [hsub] at hbound
  rw [← hc] at hbound
  have hc1 : 1 ≤ c := by
    by_contra h
    have h0 : c = 0 := by omega
    rw [h0] at hbound
    have h72 := seventy_two_mul_sidQ_le n hn
    nlinarith
  have hq1 : 1 ≤ sidQ n := hq
  have hcp : 1 ≤ c * sidQ n := by simpa using Nat.mul_le_mul hc1 hq1
  have hgoal : mZ n + 1 ≤ c * (12 * sidQ n) + 12 * sidQ n := by nlinarith
  rw [hwt, ← hc, sZ, Nat.div_le_iff_le_mul (by positivity)]
  omega

/-! ### The block `Zᵀ` is rectangle-free and its rows are distinct -/

/-- Two different rows of `Zᵀ` share at most one `1`: `Zᵀ` contains no rectangle of ones.
If the rows `t₁ ≠ t₂` shared two columns `i₁ ≠ i₂`, the four entries `m + t - i + 1` would give
two equal sums of two elements of the Sidon set `S_n`, which forces `t₁ = t₂` or `i₁ = i₂`. -/
theorem ZT_rect (n : ℕ) (hn : N₀ ≤ n) {t₁ t₂ : Fin (n - mZ n)} (hne : t₁ ≠ t₂) :
    (supp (mZ n) (ZT n hn t₁) ∩ supp (mZ n) (ZT n hn t₂)).card ≤ 1 := by
  classical
  by_contra hcon
  have hcard : 1 < (supp (mZ n) (ZT n hn t₁) ∩ supp (mZ n) (ZT n hn t₂)).card := by omega
  obtain ⟨i₁, hi₁, i₂, hi₂, hne12⟩ := Finset.one_lt_card.mp hcard
  have hs₁ : mZ n + t₁.val - i₁.val + 1 ∈ sn n :=
    (mem_supp_ZT hn).mp (Finset.mem_inter.mp hi₁).1
  have hs₂ : mZ n + t₂.val - i₁.val + 1 ∈ sn n :=
    (mem_supp_ZT hn).mp (Finset.mem_inter.mp hi₁).2
  have hs₃ : mZ n + t₁.val - i₂.val + 1 ∈ sn n :=
    (mem_supp_ZT hn).mp (Finset.mem_inter.mp hi₂).1
  have hs₄ : mZ n + t₂.val - i₂.val + 1 ∈ sn n :=
    (mem_supp_ZT hn).mp (Finset.mem_inter.mp hi₂).2
  have hsum : (mZ n + t₁.val - i₁.val + 1) + (mZ n + t₂.val - i₂.val + 1)
      = (mZ n + t₂.val - i₁.val + 1) + (mZ n + t₁.val - i₂.val + 1) := by
    have h1 := i₁.isLt
    have h2 := i₂.isLt
    omega
  rcases sn_add_cancel hn hs₁ hs₄ hs₂ hs₃ hsum with ⟨e, -⟩ | ⟨e, -⟩
  · exact hne (Fin.ext (by omega))
  · exact hne12 (Fin.ext (by omega))

/-- The rows of `Zᵀ` are pairwise distinct: two equal rows would share all their common `1`s,
and each row has weight at least `6`. -/
theorem ZT_row_injective (n : ℕ) (hn : N₀ ≤ n) : Function.Injective (ZT n hn) := by
  intro t₁ t₂ hEq
  by_contra hne
  have hrect := ZT_rect n hn hne
  have hsupp : supp (mZ n) (ZT n hn t₁) = supp (mZ n) (ZT n hn t₂) := by rw [hEq]
  have hw : 6 ≤ (supp (mZ n) (ZT n hn t₂)).card := by
    have h := weight_ZT_ge n hn t₂
    rw [weight_eq_card_supp] at h
    exact le_trans (six_le_sZ n hn) h
  rw [hsupp, Finset.inter_self] at hrect
  omega

/-- The rows of `Zᵀ` as a finite set of vectors of `GF(2)^{m}`. -/
noncomputable def Zrows (n : ℕ) (hn : N₀ ≤ n) : Finset (Vec (mZ n)) :=
  Finset.univ.image (fun t => ZT n hn t)

theorem Zrows_card (n : ℕ) (hn : N₀ ≤ n) : (Zrows n hn).card = n - mZ n := by
  rw [Zrows, Finset.card_image_of_injective _ (ZT_row_injective n hn), Finset.card_univ,
    Fintype.card_fin]

theorem mem_Zrows {n : ℕ} (hn : N₀ ≤ n) {b : Vec (mZ n)} :
    b ∈ Zrows n hn ↔ ∃ t, ZT n hn t = b := by
  rw [Zrows, Finset.mem_image]
  simp

theorem Zrows_weight {n : ℕ} (hn : N₀ ≤ n) {b : Vec (mZ n)} (hb : b ∈ Zrows n hn) :
    sZ n ≤ weight (Finset.univ : Finset (Fin (mZ n))) b := by
  obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hb
  exact weight_ZT_ge n hn t

theorem Zrows_rect {n : ℕ} (hn : N₀ ≤ n) {b₁ b₂ : Vec (mZ n)}
    (hb₁ : b₁ ∈ Zrows n hn) (hb₂ : b₂ ∈ Zrows n hn) (hne : b₁ ≠ b₂) :
    (supp (mZ n) b₁ ∩ supp (mZ n) b₂).card ≤ 1 := by
  obtain ⟨t₁, -, rfl⟩ := Finset.mem_image.mp hb₁
  obtain ⟨t₂, -, rfl⟩ := Finset.mem_image.mp hb₂
  exact ZT_rect n hn (fun h => hne (by rw [h]))

/-- **Claim 6 applied to the block `Zᵀ`**: the independence index of `B ∪ I_m` is at least the
row weight `s = m/(12q)` of the block. -/
theorem Zrows_ind (n : ℕ) (hn : N₀ ≤ n) :
    sZ n ≤ ind (Zrows n hn ∪ unitVecs (mZ n)) := by
  classical
  refine claim6 (Zrows n hn) (sZ n) (fun b₁ h₁ b₂ h₂ hne => Zrows_rect hn h₁ h₂ hne)
    (fun b hb => Zrows_weight hn hb) ?_
  calc sZ n ≤ mZ n := sZ_le_mZ n hn
    _ = (unitVecs (mZ n)).card := (unitVecs_card).symm
    _ ≤ (Zrows n hn ∪ unitVecs (mZ n)).card := Finset.card_le_card (Finset.subset_union_right)

/-- The parameter `k` of Theorem 2 for the block `Zᵀ`: `k = ⌊s/2⌋ - 1`, so that
`2k + 2 ≤ s ≤ 2k + 3`. -/
noncomputable def kZ (n : ℕ) : ℕ := sZ n / 2 - 1

theorem two_mul_kZ_add_two_le (n : ℕ) (hn : N₀ ≤ n) : 2 * kZ n + 2 ≤ sZ n := by
  have h6 := six_le_sZ n hn
  unfold kZ
  omega

theorem sZ_le_two_mul_kZ_add_three (n : ℕ) (hn : N₀ ≤ n) : sZ n ≤ 2 * kZ n + 3 := by
  have h6 := six_le_sZ n hn
  unfold kZ
  omega

theorem two_le_kZ (n : ℕ) (hn : N₀ ≤ n) : 2 ≤ kZ n := by
  have h6 := six_le_sZ n hn
  unfold kZ
  omega

/-! ### The upper `m × n` block of `Z_{n,S_n}` -/

/-- The upper `mZ n × n` block of `Z_{n,S_n}`: its rows are the first `mZ n` rows of
`Z_{n,S_n}`, all `n` columns are kept. -/
noncomputable def Ztop (n : ℕ) (hn : N₀ ≤ n) : Matrix (Fin (mZ n)) (Fin n) (ZMod 2) :=
  fun i j => Zmat n (sn n) (Fin.castLE (mZ_le_n n hn) i) j

theorem Ztop_apply (n : ℕ) (hn : N₀ ≤ n) (i : Fin (mZ n)) (j : Fin n) :
    Ztop n hn i j = 1 ↔ ((j.val + n - i.val) % n) + 1 ∈ sn n := by
  rw [Ztop, Zmat_apply]
  simp

theorem Ztop_apply_ne_zero (n : ℕ) (hn : N₀ ≤ n) (i : Fin (mZ n)) (j : Fin n) :
    Ztop n hn i j ≠ 0 ↔ ((j.val + n - i.val) % n) + 1 ∈ sn n := by
  rw [← Ztop_apply]
  constructor
  · intro h
    rcases zmod2_eq_zero_or_one (Ztop n hn i j) with h0 | h1
    · exact absurd h0 h
    · exact h1
  · intro h h0
    rw [h0] at h
    exact zero_ne_one h

/-- **Deleting rows.**  The upper `m × n` block is a submatrix of `Z_{n,S_n}`, so its complexity
does not exceed the complexity of `Z_{n,S_n}`. -/
theorem chainComplexity_Ztop_le (n : ℕ) (hn : N₀ ≤ n) :
    chainComplexity (Ztop n hn) ≤ chainComplexity (Zmat n (sn n)) :=
  chainComplexity_submatrix_le_rows (Zmat n (sn n)) (Fin.castLE (mZ_le_n n hn))

/-- Every interval `(t, X]` with `X ≤ n` that is longer than `6q` contains an element of `S_n`. -/
theorem interval_sn_nonempty (n : ℕ) (hn : N₀ ≤ n) {t X : ℕ} (hX : X ≤ n)
    (hlen : 6 * sidQ n < X - t) : ∃ s ∈ sn n, t < s ∧ s ≤ X := by
  classical
  have h := sn_Ioc_card_ge n hn (t := t) (X := X) hX
  set c := ((sn n).filter (fun s => t < s ∧ s ≤ X)).card with hc
  have hcpos : 0 < c := by
    by_contra hcon
    have h0 : c = 0 := by omega
    rw [h0] at h
    omega
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hcpos
  rw [Finset.mem_filter] at hs
  exact ⟨s, hs.1, hs.2⟩

/-- Every row of the upper block is nonzero: the rows of `Z_{n,S_n}` are cyclic shifts of a
nonzero row. -/
theorem Ztop_row_nonzero (n : ℕ) (hn : N₀ ≤ n) (i : Fin (mZ n)) :
    ∃ j : Fin n, Ztop n hn i j ≠ 0 := by
  classical
  obtain ⟨s, hs⟩ := sn_nonempty hn
  obtain ⟨hs1, hsn⟩ := sn_subset hn s hs
  have hp : 0 < n := by have h1 : 0 < mZ n := mZ_pos n; have h2 : mZ n ≤ n := mZ_le_n n hn; omega
  have hin : i.val ≤ n := by have h1 : i.val < mZ n := i.isLt; have h2 : mZ n ≤ n := mZ_le_n n hn; omega
  set j : Fin n := ⟨(i.val + (s - 1)) % n, Nat.mod_lt _ hp⟩ with hjdef
  refine ⟨j, ?_⟩
  rw [Ztop_apply_ne_zero]
  have hltj : j.val < n := j.isLt
  have hjv : j.val = (i.val + (s - 1)) % n := rfl
  have hs1n : s - 1 < n := by omega
  have hsub : j.val + n - i.val = j.val + (n - i.val) := by omega
  have h1 : j.val ≡ i.val + (s - 1) [MOD n] := by
    rw [Nat.ModEq, hjv]
    exact Nat.mod_mod _ n
  have h2 : j.val + (n - i.val) ≡ (i.val + (s - 1)) + (n - i.val) [MOD n] :=
    h1.add (Nat.ModEq.refl (n - i.val))
  have h3 : (i.val + (s - 1)) + (n - i.val) = n + (s - 1) := by omega
  rw [h3] at h2
  have h4 : n + (s - 1) ≡ s - 1 [MOD n] := by
    rw [Nat.ModEq]
    simp [Nat.mod_eq_of_lt hs1n]
  have hme : j.val + (n - i.val) ≡ s - 1 [MOD n] := h2.trans h4
  have hfin := hme
  rw [Nat.ModEq, Nat.mod_eq_of_lt hs1n] at hfin
  rw [hsub, hfin, show s - 1 + 1 = s by omega]
  exact hs

/-- Every column of the upper block is nonzero: a column is a cyclic window of `S_n` of length
`m`, and any interval of length more than `6q` inside `[1, n]` meets `S_n`. -/
theorem Ztop_col_nonzero (n : ℕ) (hn : N₀ ≤ n) (j : Fin n) :
    ∃ i : Fin (mZ n), Ztop n hn i j ≠ 0 := by
  classical
  have hen : j.val + 1 ≤ n := by have := j.isLt; omega
  have hmle := mZ_le_n n hn
  have hq := sidQ_pos (sqrt_ne_zero hn)
  have hm72 := seventy_two_mul_sidQ_le n hn
  have hmain : ∃ s ∈ sn n,
      (j.val + 1 - mZ n < s ∧ s ≤ j.val + 1) ∨
      (n - mZ n + (j.val + 1) < s ∧ s ≤ n) := by
    rcases Nat.lt_or_ge (j.val + 1) (mZ n) with hlt | hge
    · rcases Nat.lt_or_ge (6 * sidQ n) (j.val + 1) with hbig | hsmall
      · obtain ⟨s, hs, hts, hXs⟩ :=
          interval_sn_nonempty n hn (t := 0) (X := j.val + 1) (by omega) (by omega)
        exact ⟨s, hs, Or.inl ⟨by omega, hXs⟩⟩
      · have hsplit : n - (n - mZ n + (j.val + 1)) = mZ n - (j.val + 1) := by
          rw [← Nat.sub_sub, Nat.sub_sub_self hmle]
        have hlen : 6 * sidQ n < n - (n - mZ n + (j.val + 1)) := by
          rw [hsplit]
          omega
        obtain ⟨s, hs, hts, hXs⟩ :=
          interval_sn_nonempty n hn (t := n - mZ n + (j.val + 1)) (X := n) (le_refl n) hlen
        exact ⟨s, hs, Or.inr ⟨by omega, hXs⟩⟩
    · have hsplit : (j.val + 1) - ((j.val + 1) - mZ n) = mZ n := by
        exact Nat.sub_sub_self (by omega)
      have hlen : 6 * sidQ n < (j.val + 1) - ((j.val + 1) - mZ n) := by
        rw [hsplit]
        omega
      obtain ⟨s, hs, hts, hXs⟩ :=
        interval_sn_nonempty n hn (t := (j.val + 1) - mZ n) (X := j.val + 1) (by omega) hlen
      exact ⟨s, hs, Or.inl ⟨by omega, hXs⟩⟩
  obtain ⟨s, hs, hcase⟩ := hmain
  obtain ⟨hs1, hsn⟩ := sn_subset hn s hs
  rcases hcase with ⟨hts, hXs⟩ | ⟨hts, hXs⟩
  · refine ⟨⟨j.val + 1 - s, by omega⟩, ?_⟩
    rw [Ztop_apply_ne_zero]
    have hji : j.val - (j.val + 1 - s) = s - 1 := by omega
    have hstep : j.val + n - (j.val + 1 - s) = (j.val - (j.val + 1 - s)) + n := by omega
    have hcalc : ((j.val + n - (j.val + 1 - s)) % n) + 1 = s := by
      rw [hstep, hji, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : s - 1 < n)]
      omega
    rw [hcalc]
    exact hs
  · refine ⟨⟨n + (j.val + 1) - s, by omega⟩, ?_⟩
    rw [Ztop_apply_ne_zero]
    have hcalc : ((j.val + n - (n + (j.val + 1) - s)) % n) + 1 = s := by
      have h1 : j.val + n - (n + (j.val + 1) - s) = s - 1 := by omega
      rw [h1, Nat.mod_eq_of_lt (by omega : s - 1 < n)]
      rw [show s - 1 + 1 = s by omega]
    rw [hcalc]
    exact hs

/-- **Transposition.**  `ZT` is the submatrix of the transpose of the upper block obtained by
selecting the rows `m, …, n-1`. -/
theorem ZT_eq_submatrix (n : ℕ) (hn : N₀ ≤ n) :
    ZT n hn = fun t i => Matrix.transpose (Ztop n hn) ⟨mZ n + t.val, by
      have := t.isLt; have := mZ_le_n n hn; omega⟩ i := by
  funext t i
  simp only [ZT, Matrix.transpose_apply, Zblk, Ztop]
  rfl

/-- The complexity of `ZT` does not exceed that of the transpose of the upper block: `ZT`
consists of the rows `m, …, n-1` of that transpose. -/
theorem chainComplexity_ZT_le (n : ℕ) (hn : N₀ ≤ n) :
    chainComplexity (ZT n hn) ≤ chainComplexity (Matrix.transpose (Ztop n hn)) := by
  have h := chainComplexity_submatrix_le_rows (Matrix.transpose (Ztop n hn))
    (fun t : Fin (n - mZ n) => (⟨mZ n + t.val, by
      have := t.isLt; have := mZ_le_n n hn; omega⟩ : Fin n))
  rw [← ZT_eq_submatrix n hn] at h
  exact h

/-! ### The row weight in terms of the size of the block -/

/-- `12·q·n ≤ 25·m²`: the number `q` of columns per row is at most `2√n` and `m ≥ n^{3/4}`. -/
theorem twelve_mul_sidQ_mul_le (n : ℕ) (hn : N₀ ≤ n) :
    12 * sidQ n * n ≤ 25 * mZ n * mZ n := by
  have hq := sidQ_le (sqrt_ne_zero hn)
  have hsq : Nat.sqrt n * Nat.sqrt n ≤ n := by simpa [pow_two] using Nat.sqrt_le' n
  have h1 : (n * Nat.sqrt n) ^ 2 ≤ n ^ 3 := by
    calc (n * Nat.sqrt n) ^ 2 = n ^ 2 * (Nat.sqrt n * Nat.sqrt n) := by ring
      _ ≤ n ^ 2 * n := Nat.mul_le_mul_left _ hsq
      _ = n ^ 3 := by ring
  have h2 : (n * Nat.sqrt n) ^ 2 ≤ (mZ n ^ 2) ^ 2 := by
    calc (n * Nat.sqrt n) ^ 2 ≤ n ^ 3 := h1
      _ ≤ (mZ n) ^ 4 := pow_three_le_mZ_pow_four n
      _ = (mZ n ^ 2) ^ 2 := by ring
  have h3 : n * Nat.sqrt n ≤ mZ n ^ 2 :=
    (Nat.pow_le_pow_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp h2
  have h4 : 12 * sidQ n * n ≤ 24 * (n * Nat.sqrt n) := by nlinarith [hq]
  calc 12 * sidQ n * n ≤ 24 * (n * Nat.sqrt n) := h4
    _ ≤ 25 * (mZ n ^ 2) := Nat.mul_le_mul (by norm_num) h3
    _ = 25 * mZ n * mZ n := by ring

/-- `5·m ≤ 72·q·s`, where `s = ⌊m/(12q)⌋`: the division loses at most one unit, and
`m ≥ 72q`. -/
theorem five_mul_mZ_le (n : ℕ) (hn : N₀ ≤ n) : 5 * mZ n ≤ 72 * sidQ n * sZ n := by
  have hq := sidQ_pos (sqrt_ne_zero hn)
  have hm72 := seventy_two_mul_sidQ_le n hn
  have hk0 : 0 < 12 * sidQ n := by positivity
  have hs : 12 * sidQ n * sZ n = mZ n - mZ n % (12 * sidQ n) := by
    rw [sZ]
    have h := Nat.div_add_mod (mZ n) (12 * sidQ n)
    omega
  have hr : mZ n % (12 * sidQ n) < 12 * sidQ n := Nat.mod_lt _ hk0
  have h6r : 6 * (mZ n % (12 * sidQ n)) ≤ mZ n := by
    have h12 : 12 * sidQ n ≤ mZ n / 6 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 6)]
      nlinarith
    nlinarith
  have h1 : 72 * sidQ n * sZ n = 6 * (12 * sidQ n * sZ n) := by ring
  rw [h1, hs]
  omega

/-- `n ≤ 30·m·s`: the row weight `s = m/(12q)` of the block satisfies `n/s = O(m)`. -/
theorem n_le_thirty_mul_mZ_mul_sZ (n : ℕ) (hn : N₀ ≤ n) : n ≤ 30 * mZ n * sZ n := by
  have hA := twelve_mul_sidQ_mul_le n hn
  have hB := five_mul_mZ_le n hn
  have hq := sidQ_pos (sqrt_ne_zero hn)
  have h1 : 60 * sidQ n * n ≤ 125 * mZ n * mZ n := by nlinarith
  have h2 : 125 * mZ n ≤ 1800 * sidQ n * sZ n := by nlinarith
  have h3 : mZ n * (125 * mZ n) ≤ mZ n * (1800 * sidQ n * sZ n) :=
    Nat.mul_le_mul_left _ h2
  have h4 : 60 * sidQ n * n ≤ 60 * sidQ n * (30 * mZ n * sZ n) := by
    calc 60 * sidQ n * n ≤ 125 * mZ n * mZ n := h1
      _ = mZ n * (125 * mZ n) := by ring
      _ ≤ mZ n * (1800 * sidQ n * sZ n) := h3
      _ = 60 * sidQ n * (30 * mZ n * sZ n) := by ring
  exact Nat.le_of_mul_le_mul_left h4 (by positivity)

/-! ### The numerical core of Corollary 4 -/

/-- Numerical core of the first bound of Corollary 4.  If
`N + ((2k-2)/(2k+1))·N^(k/(k+1)) ≤ L`, `N = n - m`, `n ≤ K·m·s`, `log N ≤ P`,
`2k + 2 ≤ s ≤ 2k + 3` and `k ≥ 2`, then `2n ≤ L + (10K + 2)·m·P`.

Compared with `arith_core`, the parameter `s` is here of order `n^{1/4}` and `P` bounds the
logarithm instead of being a factor of `m`, so the error term is `O(m·P) = O(n^{3/4} log n)`.
When `1 - (4/s)·log N < 0` the exponential lower bound is negative, and the conclusion follows
from `n ≤ K·m·s < 4K·m·P` instead. -/
theorem arith_core_Z {n N s k m L P K : ℝ}
    (hK : 0 ≤ K) (hP : 1 ≤ P) (hs : 6 ≤ s)
    (hN : N = n - m) (hm0 : 0 ≤ m) (hN1 : 1 ≤ N)
    (hnms : n ≤ K * m * s)
    (h2k' : s ≤ 2 * k + 3) (hk : 2 ≤ k)
    (hlog : Real.log N ≤ P) (hL : 0 ≤ L)
    (hmain : N + ((2 * k - 2) / (2 * k + 1)) * N ^ (k / (k + 1)) ≤ L) :
    2 * n ≤ L + (10 * K + 2) * m * P := by
  have hs0 : 0 < s := by linarith
  have hP0 : 0 ≤ P := by linarith
  have hNpos : 0 < N := by linarith
  have hneq : n = N + m := by linarith
  have hlogpos : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hden1 : 0 < 2 * k + 1 := by linarith
  have hden2 : 0 < k + 1 := by linarith
  -- the coefficient `(2k-2)/(2k+1)` is `1 - 3/(2k+1) ≥ 1 - 6/s`
  have hA : 1 - 6 / s ≤ (2 * k - 2) / (2 * k + 1) := by
    have heq : (2 * k - 2) / (2 * k + 1) = 1 - 3 / (2 * k + 1) := by
      field_simp
      ring
    rw [heq]
    have h3 : 3 / (2 * k + 1) ≤ 6 / s := by
      rw [div_le_div_iff₀ hden1 hs0]
      nlinarith
    linarith
  -- the exponent `k/(k+1)` is `1 - 1/(k+1)`, with `1/(k+1) ≤ 4/s`
  have hexp_form : k / (k + 1) = 1 - 1 / (k + 1) := by
    field_simp
    ring
  have hfrac2 : 1 / (k + 1) ≤ 4 / s := by
    rw [div_le_div_iff₀ hden2 hs0]
    nlinarith
  have hpow : N * (1 - (4 / s) * Real.log N) ≤ N ^ (k / (k + 1)) := by
    rw [hexp_form]
    have h1 := rpow_one_sub_ge (x := N) (r := 1 / (k + 1)) hNpos
    have h2 : (1 / (k + 1)) * Real.log N ≤ (4 / s) * Real.log N :=
      mul_le_mul_of_nonneg_right hfrac2 hlogpos
    have h3 : N * (1 - (4 / s) * Real.log N) ≤ N * (1 - (1 / (k + 1)) * Real.log N) := by
      nlinarith
    linarith
  -- the error term `((6 + 4 log N)/s)·N` is at most `10·K·m·P`
  have hErr : ((6 + 4 * Real.log N) / s) * N ≤ 10 * K * m * P := by
    have hNK : N ≤ K * m * s := by nlinarith
    have hcoef : 6 + 4 * Real.log N ≤ 10 * P := by linarith
    have hprod : (6 + 4 * Real.log N) * N ≤ (10 * P) * (K * m * s) :=
      mul_le_mul hcoef hNK hNpos.le (by linarith)
    rw [show ((6 + 4 * Real.log N) / s) * N = ((6 + 4 * Real.log N) * N) / s by ring]
    rw [div_le_iff₀ hs0]
    calc (6 + 4 * Real.log N) * N ≤ (10 * P) * (K * m * s) := hprod
      _ = (10 * K * m * P) * s := by ring
  by_cases hcase : 0 ≤ 1 - (4 / s) * Real.log N
  · -- the exponential bound is active
    have hBnonneg : 0 ≤ (2 * k - 2) / (2 * k + 1) := div_nonneg (by linarith) hden1.le
    have hmix : (1 - 6 / s) * (N * (1 - (4 / s) * Real.log N)) ≤
        ((2 * k - 2) / (2 * k + 1)) * N ^ (k / (k + 1)) :=
      mul_le_mul hA hpow (mul_nonneg hNpos.le hcase) hBnonneg
    have hid : (1 - 6 / s) * (N * (1 - (4 / s) * Real.log N)) =
        N - ((6 + 4 * Real.log N) / s) * N + (24 * Real.log N / s ^ 2) * N := by
      field_simp
      ring
    have hpos : 0 ≤ (24 * Real.log N / s ^ 2) * N :=
      mul_nonneg (div_nonneg (by linarith) (by positivity)) hNpos.le
    have hstep : 2 * N - ((6 + 4 * Real.log N) / s) * N ≤ L := by
      have h2 : N - ((6 + 4 * Real.log N) / s) * N ≤
          ((2 * k - 2) / (2 * k + 1)) * N ^ (k / (k + 1)) := by
        rw [hid] at hmix
        linarith
      linarith
    have hmP : 2 * m ≤ 2 * m * P := by
      have h : 0 ≤ 2 * m * (P - 1) := mul_nonneg (by linarith) (by linarith)
      nlinarith
    nlinarith
  · -- the exponential bound is negative: `n` is bounded by `K·m·s` alone
    have hcase' : 1 - (4 / s) * Real.log N < 0 := lt_of_not_ge hcase
    have h4 : s < 4 * Real.log N := by
      have h1 : 1 < (4 / s) * Real.log N := by linarith
      have h2 : s * 1 < s * ((4 / s) * Real.log N) := mul_lt_mul_of_pos_left h1 hs0
      have h3 : s * ((4 / s) * Real.log N) = 4 * Real.log N := by
        field_simp
      linarith
    have hs4P : s < 4 * P := by linarith
    have hmK : 0 ≤ K * m := mul_nonneg hK hm0
    have h1 : n ≤ K * m * (4 * P) := by
      calc n ≤ K * m * s := hnms
        _ ≤ K * m * (4 * P) := mul_le_mul_of_nonneg_left hs4P.le hmK
    have h2 : 2 * n ≤ (10 * K + 2) * m * P := by nlinarith
    linarith

/-! ### The minimal chain computing `Zᵀ` -/

/-- Every matrix has a chain computing it whose length is exactly its additive complexity:
the set of lengths of computing chains is a nonempty set of naturals, so its infimum is one of
its elements. -/
theorem exists_chain_of_chainComplexity {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    ∃ c : VecAddChain n, c.L = chainComplexity A ∧ c.Computes A := by
  have hne : (ChainSet A).Nonempty := chainSet_nonempty A
  have hmem : sInf (ChainSet A) ∈ ChainSet A := Nat.sInf_mem hne
  simpa [chainComplexity, ChainSet] using hmem

/-! ### Theorem 2 applied to the block `Zᵀ`

The rows of `Zᵀ` are the columns of the block `Z`; they are rectangle-free of weight at least
`s = m/(12q)`, so Claim 6 gives `ind (Zᵀ ∪ I_m) ≥ s`, and Theorem 2 with the parameter
`k = ⌊s/2⌋ - 1` yields `L(Zᵀ) ≥ (n-m) + (1 - O(1/k))·(n-m)^{k/(k+1)}`. -/

/-- **(6.1)-type estimate for the block `Zᵀ`.**  `L(Zᵀ) ≥ 2n - 302·m·p`, where
`m = ⌈n^{3/4}⌉` and `p = ⌈log₂ n⌉`. -/
theorem chainComplexity_ZT_ge (n : ℕ) (hn : N₀ ≤ n) :
    (2 * n : ℝ) ≤ (chainComplexity (ZT n hn) : ℝ) + 302 * (mZ n : ℝ) * (pOf n : ℝ) := by
  classical
  obtain ⟨c₀, hc₀L, hc₀⟩ := exists_chain_of_chainComplexity (ZT n hn)
  -- the chain `c₀` read with no inessential variables computes the row set of `Zᵀ`
  have hcv : (ExtChain.ofChain c₀ ∅).ComputesVecs (Zrows n hn) := by
    intro b hb
    obtain ⟨t, rfl⟩ := (mem_Zrows hn).mp hb
    refine ⟨?_, ?_⟩
    · show proj (∅ : Finset (Fin (mZ n))) (ZT n hn t) = 0
      funext i
      simp [proj]
    · have h := hc₀ t
      simp only [ExtChain.ofChain, Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at h ⊢
      tauto
  -- no row of `Zᵀ` has weight `1`
  have hwt : ∀ b : Row (Zrows n hn),
      weight (Finset.univ : Finset (Fin (mZ n))) b.1 ≠ 1 := by
    rintro ⟨b, hb⟩
    intro hw
    have h1 := Zrows_weight hn hb
    rw [hw] at h1
    have h6 := six_le_sZ n hn
    omega
  have hk : 2 ≤ kZ n := two_le_kZ n hn
  -- with `γ = 1` and empty `aux` the set `C₀` is `Zᵀ ∪ I_m`
  have hfree : freeVecs (∅ : Finset (Fin (mZ n))) = unitVecs (mZ n) := by
    ext v
    simp [mem_freeVecs]
  have hC0 : C0 (ExtChain.ofChain c₀ ∅).aux true (Zrows n hn) =
      Zrows n hn ∪ unitVecs (mZ n) := by
    show Zrows n hn ∪ freeVecs (∅ : Finset (Fin (mZ n))) = Zrows n hn ∪ unitVecs (mZ n)
    rw [hfree]
  have hind : 2 * kZ n + 2 ≤ ind (C0 (ExtChain.ofChain c₀ ∅).aux true (Zrows n hn)) := by
    rw [hC0]
    exact le_trans (two_mul_kZ_add_two_le n hn) (Zrows_ind n hn)
  have hmB : mZ n ≤ (Zrows n hn).card := by
    rw [Zrows_card n hn]
    have := two_mul_mZ_le n hn
    omega
  have hmain := theorem2 (ExtChain.ofChain c₀ ∅) (Zrows n hn) true hcv hwt hk hind hmB
  have hslack : ((inputSlack (ExtChain.ofChain c₀ ∅).aux true : ℕ) : ℝ) = 0 := by
    simp [inputSlack, ExtChain.ofChain]
  have hBcard : ((Zrows n hn).card : ℝ) = ((n - mZ n : ℕ) : ℝ) := by
    rw [Zrows_card n hn]
  have hcred : ((ExtChain.ofChain c₀ ∅).reducedComplexity : ℝ) =
      (chainComplexity (ZT n hn) : ℝ) := by
    rw [ExtChain.reducedComplexity_aux_empty c₀, hc₀L]
  rw [hBcard, hslack, hcred] at hmain
  simp only [sub_zero] at hmain
  -- the logarithm of the row count is at most `p`
  have hNpos : 0 < n - mZ n := by
    have h1 := two_mul_mZ_le n hn
    have h2 := mZ_pos n
    omega
  have hlog : Real.log (((n - mZ n : ℕ) : ℝ)) ≤ (pOf n : ℝ) := by
    have hNposR : (0 : ℝ) < ((n - mZ n : ℕ) : ℝ) := by exact_mod_cast hNpos
    have hNn : ((n - mZ n : ℕ) : ℝ) ≤ (n : ℝ) := by
      have := Nat.sub_le n (mZ n)
      exact_mod_cast this
    have hn1 : 1 ≤ n := by unfold N₀ at hn; omega
    have hnposR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have h1 : Real.log ((n - mZ n : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log hNposR hNn
    have h2 : Real.log (n : ℝ) < (pOf n : ℝ) := by
      have hlt : (n : ℝ) < (2 : ℝ) ^ (pOf n) := by exact_mod_cast n_lt_two_pow_pOf n
      calc Real.log (n : ℝ) < Real.log ((2 : ℝ) ^ (pOf n)) := Real.log_lt_log hnposR hlt
        _ = (pOf n : ℝ) * Real.log 2 := Real.log_pow _ _
        _ ≤ (pOf n : ℝ) * 1 := by
            have h2 : Real.log (2 : ℝ) ≤ 1 := by
              have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
              linarith
            nlinarith
        _ = (pOf n : ℝ) := by ring
    linarith
  have key := arith_core_Z (n := (n : ℝ)) (N := ((n - mZ n : ℕ) : ℝ))
    (s := (sZ n : ℝ)) (k := (kZ n : ℝ)) (m := (mZ n : ℝ))
    (L := (chainComplexity (ZT n hn) : ℝ)) (P := (pOf n : ℝ)) (K := 30)
    (by norm_num) (by exact_mod_cast one_le_pOf n)
    (by exact_mod_cast six_le_sZ n hn)
    (by rw [Nat.cast_sub (mZ_le_n n hn)]) (by positivity)
    (by exact_mod_cast (by omega : 1 ≤ n - mZ n))
    (by exact_mod_cast n_le_thirty_mul_mZ_mul_sZ n hn)
    (by exact_mod_cast sZ_le_two_mul_kZ_add_three n hn)
    (by exact_mod_cast two_le_kZ n hn)
    hlog (by positivity) hmain
  norm_num at key
  exact key

/-! ### The complexity of `Z_{n,S_n}` -/

/-- **Corollary 4, first bound**: `L(Z_{n,S_n}) ≥ 3n - O(n^{3/4} log n)`, in the concrete form
`3n ≤ L(Z_{n,S_n}) + 303·m·p` with `m = ⌈n^{3/4}⌉` and `p = ⌈log₂ n⌉`.

The proof follows the paper: the upper-right `m × (n-m)` block `Z` of `Z_{n,S_n}` is
rectangle-free, so by Claim 6 and Theorem 2 its transpose `Zᵀ` has additive complexity at least
`2n - 302·m·p` (`chainComplexity_ZT_ge`).  Since `Zᵀ` is a submatrix of the transpose of the
upper `m × n` block `Z_{top}`, and `L(Z_{top}) = L(Z_{top}ᵀ) + n - m` by Claim 1, the
complexity of `Z_{n,S_n}` is at least `L(Zᵀ) + n - m ≥ 3n - 302·m·p - m`. -/
theorem corollary4 (n : ℕ) (hn : N₀ ≤ n) :
    3 * n ≤ chainComplexity (Zmat n (sn n)) + 303 * mZ n * pOf n := by
  classical
  have hZT := chainComplexity_ZT_ge n hn
  have htr : (chainComplexity (ZT n hn) : ℝ) ≤
      (chainComplexity (Matrix.transpose (Ztop n hn)) : ℝ) := by
    exact_mod_cast chainComplexity_ZT_le n hn
  have hclaim := claim1 (Ztop n hn) (Ztop_row_nonzero n hn) (Ztop_col_nonzero n hn)
  have hclaimR : (chainComplexity (Ztop n hn) : ℝ) =
      (chainComplexity (Matrix.transpose (Ztop n hn)) : ℝ) + (n : ℝ) - (mZ n : ℝ) := by
    have h : (chainComplexity (Ztop n hn) : ℝ) + (mZ n : ℝ) =
        (chainComplexity (Matrix.transpose (Ztop n hn)) : ℝ) + (n : ℝ) := by
      exact_mod_cast hclaim
    linarith
  have hsub : (chainComplexity (Ztop n hn) : ℝ) ≤
      (chainComplexity (Zmat n (sn n)) : ℝ) := by
    exact_mod_cast chainComplexity_Ztop_le n hn
  have hp1 : (1 : ℝ) ≤ (pOf n : ℝ) := by exact_mod_cast one_le_pOf n
  have hm0 : (0 : ℝ) ≤ (mZ n : ℝ) := by positivity
  have hmP : (mZ n : ℝ) ≤ (mZ n : ℝ) * (pOf n : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_left hp1 hm0]
  have goalR : (3 * n : ℝ) ≤
      (chainComplexity (Zmat n (sn n)) : ℝ) + 303 * (mZ n : ℝ) * (pOf n : ℝ) := by
    nlinarith
  exact_mod_cast goalR

end AchainsComplexityGF2
