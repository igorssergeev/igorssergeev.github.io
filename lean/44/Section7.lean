import Mathlib
import GF2Reduced
import Theorem2

/-!
# Section 7 of [16]: Sierpinski matrices, Lemmas 5 and 6, and Corollary 6

This file formalizes the opening of Section 7 of

* I. S. Sergeev, *Lower bounds on the additive complexity of linear operators and bilinear
  algorithms*,

namely the Sierpinski (disjointness) matrices, the combinatorial measures of Boolean
functions, Lemma 5 (`\label{munk}`), Lemma 6 (`\label{ind_mu}`) and Corollary 6.

A Boolean function in `n` variables is represented by its Zhegalkin polynomial, i.e. by the
`Finset` of its monomials, each monomial being the `Finset` of the variables it contains.  The
two measures of the paper are `deg P`, the largest degree of a monomial, and `tot P`, the sum
of the degrees of all monomials; the set of monomials itself is `mon P`.

The Sierpinski matrix `D n` of size `2^n × 2^n` is indexed by the subsets of `[n]` and has
`D n I J = 1` exactly when `I` and `J` are disjoint.  `Dsub n` is the same matrix in the
`I ⊆ J` indexing (the column index is complemented), whose recursion
`D_{k+1} = [[D_k, D_k], [0, D_k]]` is the form (7.1) of the paper.

The main results of the file are

* the recursion (7.1) for `D` and `Dsub` (`D.succ_shift_shift`, `D.succ_insert_shift`,
  `D.succ_insert_insert` and their `Dsub` analogues), together with `D 0 = [1]`
  (`D.zero_apply`) and the values of `D 1` (`D.one_apply`);
* step 1 of the proof of Lemma 5: a nonzero polynomial vanishing on all vectors of weight at
  least `W` has degree larger than `n - W` (`deg_gt_of_isVanishing`);
* steps 2 and 3: the descending chain `f_k, …, f_0` obtained by zeroing a variable of maximal
  column sum and then setting all common variables to `1` (`fk`, `chain_tot`,
  `step_card_drop`), and the resulting bound `k^5 < 20 n^2 s^2` on the number `s` of monomials
  (`card_bound_of_vanishing`);
* Lemma 5: for `0 ≤ k < n` one has `μ_{n,k} > k^{5/2}/(5n)` (`lemma5`), where `μ_{n,k}` is
  the minimal number of monomials of a nonzero function vanishing on all vectors of weight at
  least `n - k` (`mu`);
* Lemma 6: every set of at most `μ_{n,k} - 1` rows of the submatrix `D_{n,k}` is linearly
  independent, i.e. `ind D_{n,k} ≥ μ_{n,k} - 1` (`lemma6`); the punctured row set obtained by
  deleting the all-ones row satisfies `ind ≥ μ_{n,k} - 2` (`ind_DkRowSetP`), which is the form
  needed by Theorem 2;
* Corollary 6: the additive complexity of `D_n` is `(3-o(1))·2^n`, i.e. for every `ε > 0` and
  all large `n` one has `(3-ε)·2^n ≤ L(D_n)` (`corollary6`).

## Contents

0. Prerequisites copied from Section 1: the complexity measures for circuits, the equivalence
   of the additive models, path counts, and the transposition principle (`claim1`).
1. Boolean vectors over `GF(2)`, their support and weight, and Zhegalkin polynomials with the
   measures `mon`, `deg`, `tot`, together with the vanishing predicate and its basic algebra.
2. The Sierpinski (disjointness) matrix `D n` and the Pascal form `Dsub n`, with the recursion
   (7.1), the base cases `n = 0, 1`, and the symmetry `D n I J = D n J I`.
3. Substituting a variable by `0`: the polynomial `substZero P i` and its effect on evaluation,
   on the total degree and on vanishing.
4. Substituting variables by `1`: the common variables `commonSet P`, the polynomial
   `substOne P C`, and its effect on evaluation, on the number of monomials and on vanishing.
5. Step 1 of Lemma 5: the degree bound `n - W < deg P` (`deg_gt_of_isVanishing`).
6. The column sums `Esum P i`, their maximiser, and `deg P ≤ Esum P (argmaxEsum P)`.
7. Step 3 of Lemma 5: Cauchy–Schwarz for `∑ i, Esum P i` and the per-step loss bound
   `j^4 < 4 n^2 |mon Q| (|mon Q| - |mon (step Q)|)`.
8. Step 2 of Lemma 5: the vanishing chain `fk` and its total-degree estimate `chain_tot`.
9. Step 3 of Lemma 5, conclusion: the sum of the per-stage losses and the numerical core
   `k^5 < 20 n^2 |mon P|^2` (`card_bound_of_vanishing`).
10. The quantity `μ_{n,k}` (`mu`) and Lemma 5 (`lemma5`, `lemma5_int`).
11. The matrix view of `D_n` and of the submatrix `D_{n,k}`; Lemma 6 (`lemma6`) and the
    independence of `μ_{n,k} - 2` rows of the punctured row set (`ind_DkRowSetP`).
12. The column count `mDk n k = ∑ j ≤ k, choose n j` is `2^{o(n)}` at `k = ⌊n/8⌋`, and the
    transpose `D_{n,k}ᵀ` is a submatrix of `D_n` (`chainComplexity_DkMat_transpose_le`).
13. Claim 1 for the submatrix (`DkMat_claim1`) and Theorem 2 applied to `D_{n,k}`
    (`Dmat_lower_bound`), giving
    `L(D_n) ≥ (2^n - 1) + (1-o(1))·(2^n - 1)^{K/(K+1)} + 2^n - 2·mDk n k`.
14. Corollary 6: choosing `k = ⌊n/8⌋` and `K ≈ μ_{n,k}/2 = Ω(n^{3/2})` gives
    `(3-o(1))·2^n ≤ L(D_n)` (`corollary6`).

## Organization

## Part 0: prerequisites from Section 1

The transposition principle `claim1` of Section 1 of the paper is used in Part 13, for the
submatrix `D_{n,k}`.  Its statement and proof (the path-counting argument of Section 1) are
reproduced, together with the complexity measures for circuits, the
equivalence of the chain and circuit models, and the path counts they rest on.  Nothing below
depends on this part except `claim1` itself.

## Parts 1–2: Boolean measures and the Sierpinski matrices

Part 1 sets up the ambient language: `BVec n = Fin n → ZMod 2` with its support and Hamming
weight, and Zhegalkin polynomials `Zheg n = Finset (Finset (Fin n))` with their evaluation
`zheval`, the monomial set `mon`, the degree `deg`, the total degree `tot`, and the predicate
`IsVanishing P W` saying that `P` vanishes on all vectors of weight at least `W`.
Part 2 defines the disjointness matrix `D n` on the index set `Finset (Fin n)`, its Pascal
form `Dsub n` (`Dsub n I J = D n I Jᶜ`), and proves the recursion (7.1) by splitting the
indices according to whether they contain the last element.

## Parts 3–4: substitution of variables

Part 3 studies `substZero P i`, the polynomial obtained by setting `x i := 0`: its evaluation
at `x` is the evaluation of `P` at the vector with coordinate `i` zeroed, its total degree
drops by `Esum P i`, and vanishing is preserved with the threshold lowered by one.  Part 4
studies `substOne P C` for a set `C` of common variables: it preserves the value of `P` on
vectors with `C ⊆ supp x`, does not increase the number of monomials, and preserves vanishing
with the threshold raised by one.

## Parts 5–7: the three steps of Lemma 5

Part 5 is step 1 of the paper: `deg P > n - W` for a nonzero `P` vanishing on all vectors of
weight at least `W` (`deg_gt_of_isVanishing`), proved by testing `P` on the characteristic
vector of a suitable set `T` and exhibiting an odd number of monomials supported in it.
Part 6 bounds the largest column sum `Esum P i` from below by `deg P` and relates the sum of
the column sums to the squared monomial degrees.  Part 7 converts the Cauchy–Schwarz estimate
into the per-step loss `j^4 < 4 n^2 |mon Q| (|mon Q| - |mon (step Q)|)` (`step_card_drop`),
where one step zeroes a variable of maximal `Esum` and then sets all common variables to `1`.

## Parts 8–9: the chain and the numerical core

Part 8 builds the chain `f_m = fk m` starting from a function vanishing above weight `n - k`
and shows that `f_m` is nonzero, vanishes above weight `n - k + m`, and has total degree at
least `(k-m)(k-m+3)/2` (`chain_tot`).  Part 9 sums the per-stage loss over the chain, uses
`k^5 ≤ 5 ∑ (j+1)^4`, and obtains `k^5 < 20 n^2 s^2` for `s = |mon P|`
(`card_bound_of_vanishing`).

## Part 10: Lemma 5

The minimum `μ_{n,k}` is defined as the infimum of the number of monomials of a nonzero
function vanishing above weight `n - k`; the defining set is nonempty because the `NOR`
function (the full powerset of monomials) qualifies.  Combining `card_bound_of_vanishing`
with `k^5 < (2√5 · n · s)^2` and `2√5 < 5` yields `μ_{n,k} > k^{5/2}/(5n)` (`lemma5`).

## Parts 11–14: Lemma 6 and Corollary 6

Part 11 re-indexes `D_n` by `Fin (2^n)` (`Dmat`) and the submatrix `D_{n,k}` likewise
(`DkMat`), and proves Lemma 6: if `s ≤ μ_{n,k} - 1` rows are linearly dependent, then some
nonzero combination `f = X^{I₁} ⊕ … ⊕ X^{I_s}` vanishes on all vectors of weight `≥ n - k` and
hence has at least `μ_{n,k}` monomials, a contradiction.  Part 12 bounds the number of columns
`mDk n k` of `D_{n,k}`: at `k = ⌊n/8⌋` it is at most `2^{9n/10}`, using
`choose n j ≤ (e n / j)^j` and a geometric-ratio estimate.  Part 13 proves Claim 1 for the
submatrix and applies Theorem 2 with a free parameter `K`; Part 14 takes
`K = (μ_{n,⌊n/8⌋} - 4)/2`, which Lemma 5 bounds below by `n^{3/2}/40960`, and finishes the
numerical comparison `(2^n-1) + (1-O(1/K))(2^n-1)^{K/(K+1)} ≥ (3-O(1/√n))·2^n`.

## Building

This file is checked with `lake env lean Section7.lean`.  It imports `Mathlib`, the reduced
complexity machinery `GF2Reduced`, and `Theorem2`; the transposition principle
`claim1` is reproduced inline in Part 0.  The file is deliberately not a root of any target in
`lakefile.toml`.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## Part 0: prerequisites from Section 1

The transposition principle `claim1` of Section 1 of the paper is applied in Part 13, to the
submatrix `D_{n,k}`.  Its proof (the path-counting argument of Section 1) is reproduced here, 
so that this file depends only on `Mathlib`, `GF2Reduced` and `Theorem2`.  
Nothing below depends on this part except `claim1` itself: the measures `deg`, `tot`, 
the matrix `D` and the quantity `μ` are defined in the `Sierpinski` namespace of Parts 1–14.
-/

namespace AchainsComplexityGF2

open scoped BigOperators

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

/-! ### Equivalence of the additive models (Lemma 1) -/

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

end AchainsComplexityGF2

open Finset
open AchainsComplexityGF2
open scoped BigOperators

namespace Sierpinski

/-! ## Boolean vectors over `GF(2)` and their weight -/

/-- Boolean vectors of length `n`: `Fin n → ZMod 2`. -/
abbrev BVec (n : ℕ) := Fin n → ZMod 2

/-- The support of a Boolean vector: the coordinates equal to `1`. -/
def supp {n : ℕ} (x : BVec n) : Finset (Fin n) := univ.filter (fun i => x i ≠ 0)

/-- The Hamming weight of a Boolean vector. -/
def wt {n : ℕ} (x : BVec n) : ℕ := (supp x).card

variable {n : ℕ}

@[simp] lemma mem_supp {x : BVec n} {i : Fin n} : i ∈ supp x ↔ x i ≠ 0 := by
  simp [supp]

lemma wt_le (x : BVec n) : wt x ≤ n := by
  simpa [wt] using Finset.card_le_univ (supp x)

lemma wt_pos_iff_exists {x : BVec n} : 0 < wt x ↔ ∃ i, x i ≠ 0 := by
  rw [wt, Finset.card_pos]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, mem_supp.1 hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, mem_supp.2 hi⟩

lemma wt_eq_zero_iff {x : BVec n} : wt x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext i
    by_contra hx
    have : 0 < wt x := wt_pos_iff_exists.2 ⟨i, hx⟩
    omega
  · intro h
    subst h
    simp [wt, supp]

/-- Every element of `ZMod 2` is `0` or `1`. -/
lemma zmod2_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 :=
  (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) a

lemma zmod2_eq_one_of_ne_zero {a : ZMod 2} (h : a ≠ 0) : a = 1 :=
  (zmod2_eq_zero_or_one a).resolve_left h

/-- The point of the Boolean cube supported on `T`. -/
def ind (T : Finset (Fin n)) : BVec n := fun i => if i ∈ T then 1 else 0

@[simp] lemma ind_apply (T : Finset (Fin n)) (i : Fin n) :
    ind T i = if i ∈ T then 1 else 0 := rfl

lemma supp_ind (T : Finset (Fin n)) : supp (ind T) = T := by
  ext i
  simp [supp, ind]

lemma wt_ind (T : Finset (Fin n)) : wt (ind T) = T.card := by
  simp [wt, supp_ind]

/-! ## Zhegalkin polynomials -/

/-- A Zhegalkin polynomial in `n` variables, represented by its set of monomials
(exponent vectors). -/
abbrev Zheg (n : ℕ) := Finset (Finset (Fin n))

/-- Evaluation of a Zhegalkin polynomial. -/
def zheval (P : Zheg n) (x : BVec n) : ZMod 2 := ∑ U ∈ P, ∏ i ∈ U, x i

/-- `mon f`: the set of monomials of the Boolean function `f`. -/
def mon (P : Zheg n) : Finset (Finset (Fin n)) := P

/-- `deg f`: the degree of the Boolean function `f`. -/
def deg (P : Zheg n) : ℕ := P.sup Finset.card

/-- `tot f`: the total degree of the Boolean function `f`. -/
def tot (P : Zheg n) : ℕ := ∑ U ∈ P, U.card

/-- `f` vanishes on all Boolean vectors of weight at least `W`. -/
def IsVanishing (P : Zheg n) (W : ℕ) : Prop := ∀ x : BVec n, W ≤ wt x → zheval P x = 0

@[simp] lemma mon_def (P : Zheg n) : mon P = P := rfl

@[simp] lemma zheval_empty (x : BVec n) : zheval (∅ : Zheg n) x = 0 := by
  simp [zheval]

lemma prod_ind (U T : Finset (Fin n)) :
    ∏ i ∈ U, ind T i = if U ⊆ T then (1 : ZMod 2) else 0 := by
  rw [show (∏ i ∈ U, ind T i) = ∏ i ∈ U, if i ∈ T then (1 : ZMod 2) else 0 from rfl]
  rw [Finset.prod_boole]
  simp [Finset.subset_iff]

/-- The Möbius-sum identity: the value of `f` at the indicator of `T` counts, modulo `2`,
the monomials of `f` contained in `T`. -/
lemma zheval_ind (P : Zheg n) (T : Finset (Fin n)) :
    zheval P (ind T) = ((P.filter (fun U => U ⊆ T)).card : ZMod 2) := by
  have h : ∀ U ∈ P, (∏ i ∈ U, ind T i) = if U ⊆ T then (1 : ZMod 2) else 0 :=
    fun U _ => prod_ind U T
  rw [zheval, Finset.sum_congr rfl h, Finset.sum_boole]

/-- A nonzero Zhegalkin polynomial is nonzero as a function: it takes the value `1`
somewhere. -/
lemma exists_zheval_eq_one {P : Zheg n} (hP : P.Nonempty) : ∃ x : BVec n, zheval P x = 1 := by
  obtain ⟨T0, hT0, hmin⟩ := Finset.exists_min_image P Finset.card hP
  refine ⟨ind T0, ?_⟩
  rw [zheval_ind]
  have hfilter : P.filter (fun U => U ⊆ T0) = {T0} := by
    ext U
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hU, hsub⟩
      by_contra hne
      have hlt : U.card < T0.card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, hne⟩)
      exact absurd (hmin U hU) (not_le.2 hlt)
    · rintro rfl
      exact ⟨hT0, Finset.Subset.refl _⟩
  rw [hfilter]
  simp

/-- Powers of `2` are zero in `ZMod 2`. -/
lemma natCast_two_pow_eq_zero {k : ℕ} (hk : 0 < k) : ((2 ^ k : ℕ) : ZMod 2) = 0 := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 hk)
  rw [pow_succ, Nat.cast_mul, ZMod.natCast_self, mul_zero]

/-- The Zhegalkin polynomial of the `NOR` function, i.e. the full powerset, evaluates to
`2 ^ wt x`. -/
lemma zheval_powerset (x : BVec n) :
    zheval ((univ : Finset (Fin n)).powerset : Zheg n) x = ((2 ^ wt x : ℕ) : ZMod 2) := by
  rw [zheval]
  have hfac : ∀ U ∈ (univ : Finset (Fin n)).powerset,
      (∏ i ∈ U, x i) = if U ⊆ supp x then (1 : ZMod 2) else 0 := by
    intro U _
    rw [show (∏ i ∈ U, x i) = ∏ i ∈ U, if i ∈ supp x then (1 : ZMod 2) else 0 from ?_]
    · rw [Finset.prod_boole]
      simp [Finset.subset_iff]
    · refine Finset.prod_congr rfl (fun i _ => ?_)
      by_cases h : i ∈ supp x
      · simp [h, zmod2_eq_one_of_ne_zero (mem_supp.1 h)]
      · have hx : x i = 0 := by
          by_contra hx
          exact h (mem_supp.2 hx)
        simp [h, hx]
  rw [Finset.sum_congr rfl hfac, Finset.sum_boole]
  congr 1
  have hpow : (univ : Finset (Fin n)).powerset.filter (fun U => U ⊆ supp x) = (supp x).powerset := by
    ext U
    simp
  rw [hpow, Finset.card_powerset]
  rfl


/-! ## Sierpinski (disjointness) matrices -/

/-- The `2^n × 2^n` Sierpinski matrix (also called the *disjointness matrix*): rows and
columns are indexed by subsets of `[n]`, and `D n I J = 1` exactly when `I` and `J` are
disjoint.  Equivalently (`Dsub`), after complementing the column index this is the matrix
with `1`s exactly at the positions `I ⊆ J`, i.e. the binary Pascal matrix. -/
def D (n : ℕ) : Matrix (Finset (Fin n)) (Finset (Fin n)) (ZMod 2) :=
  Matrix.of fun I J => if Disjoint I J then 1 else 0

namespace D

variable {n : ℕ}

@[simp] lemma apply (I J : Finset (Fin n)) : D n I J = if Disjoint I J then 1 else 0 := rfl

@[simp] lemma apply_of_disjoint {I J : Finset (Fin n)} (h : Disjoint I J) : D n I J = 1 := by
  simp [apply, h]

@[simp] lemma apply_of_not_disjoint {I J : Finset (Fin n)} (h : ¬ Disjoint I J) : D n I J = 0 := by
  simp [apply, h]

lemma eq_one_iff {I J : Finset (Fin n)} : D n I J = 1 ↔ Disjoint I J := by
  by_cases h : Disjoint I J <;> simp [h]

lemma eq_zero_iff {I J : Finset (Fin n)} : D n I J = 0 ↔ ¬ Disjoint I J := by
  by_cases h : Disjoint I J <;> simp [h]

lemma comm (I J : Finset (Fin n)) : D n I J = D n J I := by
  by_cases h : Disjoint I J
  · rw [apply_of_disjoint h, apply_of_disjoint h.symm]
  · rw [apply_of_not_disjoint h, apply_of_not_disjoint (fun hc => h hc.symm)]

lemma self (I : Finset (Fin n)) : D n I I = if I = ∅ then 1 else 0 := by
  by_cases h : I = ∅
  · subst h
    simp
  · have hnd : ¬ Disjoint I I := by
      obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 h
      exact fun hd => (Finset.disjoint_left.1 hd hi) hi
    rw [apply_of_not_disjoint hnd]
    simp [h]

/-- The matrix has `2^n` rows and `2^n` columns. -/
lemma card_index (n : ℕ) : Fintype.card (Finset (Fin n)) = 2 ^ n := by
  rw [Fintype.card_finset, Fintype.card_fin]

/-- A subset of `[n]`, viewed as a subset of `[n+1]` not containing the last element. -/
def shift {n : ℕ} (I : Finset (Fin n)) : Finset (Fin (n+1)) := I.map Fin.castSuccEmb

@[simp] lemma mem_shift {I : Finset (Fin n)} {i : Fin (n+1)} :
    i ∈ shift I ↔ ∃ j, j ∈ I ∧ Fin.castSucc j = i := Finset.mem_map

lemma last_not_mem_shift (I : Finset (Fin n)) : Fin.last n ∉ shift I := by
  rw [mem_shift]
  rintro ⟨j, -, hj⟩
  exact Fin.castSucc_ne_last j hj

@[simp] lemma shift_empty : shift (∅ : Finset (Fin n)) = ∅ := by
  simp [shift]

@[simp] lemma shift_disjoint_iff (I J : Finset (Fin n)) :
    Disjoint (shift I) (shift J) ↔ Disjoint I J := by
  rw [shift, shift, Finset.disjoint_map]

/-- The block `D_{k+1}[I, J]` with neither index containing the last element. -/
lemma succ_shift_shift (I J : Finset (Fin n)) :
    D (n+1) (shift I) (shift J) = D n I J := by
  by_cases h : Disjoint I J
  · rw [apply_of_disjoint ((shift_disjoint_iff I J).2 h), apply_of_disjoint h]
  · rw [apply_of_not_disjoint (fun hc => h ((shift_disjoint_iff I J).1 hc)), apply_of_not_disjoint h]

/-- The block `D_{k+1}[I, J]` where only the row index contains the last element. -/
lemma succ_insert_shift (I J : Finset (Fin n)) :
    D (n+1) (insert (Fin.last n) (shift I)) (shift J) = D n I J := by
  have hlast := last_not_mem_shift J
  have hd : Disjoint (insert (Fin.last n) (shift I)) (shift J) ↔ Disjoint I J := by
    rw [Finset.disjoint_insert_left, shift_disjoint_iff]
    exact ⟨fun h => h.2, fun h => ⟨hlast, h⟩⟩
  by_cases h : Disjoint I J
  · rw [apply_of_disjoint (hd.2 h), apply_of_disjoint h]
  · rw [apply_of_not_disjoint (fun hc => h (hd.1 hc)), apply_of_not_disjoint h]

/-- The block `D_{k+1}[I, J]` where both indices contain the last element: the zero block. -/
lemma succ_insert_insert (I J : Finset (Fin n)) :
    D (n+1) (insert (Fin.last n) (shift I)) (insert (Fin.last n) (shift J)) = 0 := by
  have : ¬ Disjoint (insert (Fin.last n) (shift I)) (insert (Fin.last n) (shift J)) := by
    rw [Finset.disjoint_insert_left]
    rintro ⟨h, -⟩
    exact h (Finset.mem_insert_self _ _)
  rw [apply_of_not_disjoint this]

/-- `D_0` is the `1 × 1` matrix `[1]`. -/
@[simp] lemma zero_apply (I J : Finset (Fin 0)) : D 0 I J = 1 := by
  rw [apply]
  have hI : I = ∅ := Subsingleton.elim _ _
  have hJ : J = ∅ := Subsingleton.elim _ _
  simp [hI, hJ]

/-- `D_1 = [[1, 1], [1, 0]]` in the disjointness indexing: the entry is `0` exactly when
both indices are the nonempty subset. -/
lemma one_apply (I J : Finset (Fin 1)) :
    D 1 I J = if I = Finset.univ ∧ J = Finset.univ then 0 else 1 := by
  have hcase : ∀ S : Finset (Fin 1), S = ∅ ∨ S = Finset.univ := by
    intro S
    by_cases h : (0 : Fin 1) ∈ S
    · right
      ext x
      have hx : x = 0 := Subsingleton.elim x 0
      simp [hx, h]
    · left
      ext x
      have hx : x = 0 := Subsingleton.elim x 0
      simp [hx, h]
  rcases hcase I with rfl | rfl <;> rcases hcase J with rfl | rfl <;>
    simp [apply]

end D

/-- The Sierpinski matrix in the `I ⊆ J` indexing, as in the recursion
`D_{k+1} = [[D_k, D_k], [0, D_k]]` of the paper. -/
def Dsub (n : ℕ) : Matrix (Finset (Fin n)) (Finset (Fin n)) (ZMod 2) :=
  Matrix.of fun I J => if I ⊆ J then 1 else 0

namespace Dsub

variable {n : ℕ}

@[simp] lemma apply (I J : Finset (Fin n)) : Dsub n I J = if I ⊆ J then 1 else 0 := rfl

lemma subset_compl_iff_disjoint (I J : Finset (Fin n)) : I ⊆ Jᶜ ↔ Disjoint I J := by
  rw [Finset.disjoint_left, Finset.subset_iff]
  simp [Finset.mem_compl]

/-- In the `I ⊆ J` indexing, the Sierpinski matrix is the disjointness matrix with the
column index complemented. -/
lemma eq_D_compl (I J : Finset (Fin n)) : Dsub n I J = D n I Jᶜ := by
  by_cases h : I ⊆ J
  · rw [apply, D.apply_of_disjoint ((subset_compl_iff_disjoint I Jᶜ).1 (by simpa using h))]
    simp [h]
  · have hd : ¬ Disjoint I Jᶜ := by
      intro hc
      exact h (by simpa using (subset_compl_iff_disjoint I Jᶜ).2 hc)
    rw [apply, D.apply_of_not_disjoint hd]
    simp [h]

lemma succ_shift_shift (I J : Finset (Fin n)) :
    Dsub (n+1) (D.shift I) (D.shift J) = Dsub n I J := by
  have hiff : D.shift I ⊆ D.shift J ↔ I ⊆ J := by
    rw [D.shift, D.shift, Finset.map_subset_map]
  by_cases h : I ⊆ J <;> simp [h, hiff]

lemma succ_insert_shift (I J : Finset (Fin n)) :
    Dsub (n+1) (insert (Fin.last n) (D.shift I)) (D.shift J) = 0 := by
  have hnot : ¬ insert (Fin.last n) (D.shift I) ⊆ D.shift J := by
    intro h
    exact D.last_not_mem_shift J (h (Finset.mem_insert_self _ _))
  rw [apply]
  simp [hnot]

lemma succ_shift_insert (I J : Finset (Fin n)) :
    Dsub (n+1) (D.shift I) (insert (Fin.last n) (D.shift J)) = Dsub n I J := by
  have hiff : D.shift I ⊆ insert (Fin.last n) (D.shift J) ↔ I ⊆ J := by
    constructor
    · intro h i hi
      have hi' : Fin.castSucc i ∈ D.shift I := Finset.mem_map.2 ⟨i, hi, rfl⟩
      rcases Finset.mem_insert.1 (h hi') with hlast | hj
      · exact absurd hlast (Fin.castSucc_ne_last i)
      · obtain ⟨j, hjJ, hje⟩ := Finset.mem_map.1 hj
        exact (Fin.castSucc_injective n hje) ▸ hjJ
    · intro h x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hx
      exact Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨i, h hi, rfl⟩)
  by_cases h : I ⊆ J <;> simp [h, hiff]

lemma succ_insert_insert (I J : Finset (Fin n)) :
    Dsub (n+1) (insert (Fin.last n) (D.shift I)) (insert (Fin.last n) (D.shift J)) = Dsub n I J := by
  have hiff : insert (Fin.last n) (D.shift I) ⊆ insert (Fin.last n) (D.shift J) ↔ I ⊆ J := by
    constructor
    · intro h i hi
      have hi' : Fin.castSucc i ∈ insert (Fin.last n) (D.shift I) :=
        Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨i, hi, rfl⟩)
      rcases Finset.mem_insert.1 (h hi') with hlast | hj
      · exact absurd hlast (Fin.castSucc_ne_last i)
      · obtain ⟨j, hjJ, hje⟩ := Finset.mem_map.1 hj
        exact (Fin.castSucc_injective n hje) ▸ hjJ
    · intro h x hx
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact Finset.mem_insert_self _ _
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_map.1 hx
        exact Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨i, h hi, rfl⟩)
  by_cases h : I ⊆ J <;> simp [h, hiff]

end Dsub


/-! ## Substituting a variable by `0` -/

/-- The total degree of the monomials of `P` that contain the variable `i`. -/
def Esum (P : Zheg n) (i : Fin n) : ℕ := ∑ U ∈ P, if i ∈ U then U.card else 0

/-- Substituting `x i := 0` in the Zhegalkin polynomial `P`: the monomials containing `i`
disappear, the others are unchanged. -/
def substZero (P : Zheg n) (i : Fin n) : Zheg n := P.filter (fun U => i ∉ U)

lemma mem_substZero {P : Zheg n} {i : Fin n} {U : Finset (Fin n)} :
    U ∈ substZero P i ↔ U ∈ P ∧ i ∉ U := by
  simp [substZero]

lemma tot_substZero (P : Zheg n) (i : Fin n) :
    tot (substZero P i) + Esum P i = tot P := by
  unfold tot substZero Esum
  rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun U _ => ?_)
  by_cases hi : i ∈ U <;> simp [hi]

lemma zheval_substZero (P : Zheg n) (i : Fin n) (x : BVec n) :
    zheval (substZero P i) x = zheval P (Function.update x i 0) := by
  unfold zheval substZero
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun U _ => ?_)
  split_ifs with hi
  · exact (Finset.prod_eq_zero hi (by simp)).symm
  · exact Finset.prod_congr rfl (fun j hj => by
      rw [Function.update_apply]
      simp [show j ≠ i from fun h => hi (h ▸ hj)])

lemma supp_update_zero (x : BVec n) (i : Fin n) :
    supp (Function.update x i 0) = (supp x).erase i := by
  ext j
  simp only [mem_supp, Finset.mem_erase]
  constructor
  · intro hj
    rw [Function.update_apply] at hj
    by_cases hji : j = i
    · simp [hji] at hj
    · simp [hji] at hj
      exact ⟨hji, hj⟩
  · rintro ⟨hji, hj⟩
    rw [Function.update_apply]
    simp [hji, hj]

lemma wt_update_zero_ge (x : BVec n) (i : Fin n) : wt x - 1 ≤ wt (Function.update x i 0) := by
  rw [wt, wt, supp_update_zero]
  by_cases hi : i ∈ supp x
  · have h := Finset.card_erase_add_one (a := i) (s := supp x) hi
    omega
  · rw [Finset.erase_eq_self.mpr hi]
    omega

lemma isVanishing_substZero {P : Zheg n} {W : ℕ} (h : IsVanishing P W) (i : Fin n) :
    IsVanishing (substZero P i) (W + 1) := by
  intro x hx
  rw [zheval_substZero]
  apply h
  have := wt_update_zero_ge x i
  omega

lemma card_filter_mem_add (P : Zheg n) (i : Fin n) :
    (P.filter (fun U => i ∈ U)).card + (substZero P i).card = P.card := by
  have h := Finset.card_filter_add_card_filter_not (s := P) (p := fun U => i ∈ U)
  simpa only [substZero] using h


/-! ## Substituting variables by `1` -/

/-- The set of variables that occur in *every* monomial of `P`. -/
def commonSet (P : Zheg n) : Finset (Fin n) := univ.filter (fun i => ∀ U ∈ P, i ∈ U)

@[simp] lemma mem_commonSet {P : Zheg n} {i : Fin n} :
    i ∈ commonSet P ↔ ∀ U ∈ P, i ∈ U := by
  simp [commonSet]

/-- Setting every coordinate in `C` to `1`. -/
def setOne (x : BVec n) (C : Finset (Fin n)) : BVec n := fun i => if i ∈ C then 1 else x i

@[simp] lemma setOne_apply (x : BVec n) (C : Finset (Fin n)) (i : Fin n) :
    setOne x C i = if i ∈ C then 1 else x i := rfl

lemma supp_subset_supp_setOne (x : BVec n) (C : Finset (Fin n)) :
    supp x ⊆ supp (setOne x C) := by
  intro i hi
  rw [mem_supp] at hi ⊢
  rw [setOne_apply]
  by_cases h : i ∈ C
  · simp [h]
  · simpa [h] using hi

lemma wt_le_wt_setOne (x : BVec n) (C : Finset (Fin n)) : wt x ≤ wt (setOne x C) :=
  Finset.card_le_card (supp_subset_supp_setOne x C)

/-- Substituting `1` for every variable in `C`. -/
def substOne (P : Zheg n) (C : Finset (Fin n)) : Zheg n := P.image (fun U => U \ C)

lemma mem_substOne {P : Zheg n} {C : Finset (Fin n)} {V : Finset (Fin n)} :
    V ∈ substOne P C ↔ ∃ U ∈ P, U \ C = V := by
  simp [substOne]

lemma substOne_nonempty {P : Zheg n} {C : Finset (Fin n)} (hP : P.Nonempty) :
    (substOne P C).Nonempty := hP.image _

lemma injOn_sdiff {P : Zheg n} {C : Finset (Fin n)} (hC : ∀ U ∈ P, C ⊆ U) :
    Set.InjOn (fun U => U \ C) (↑P) := by
  intro U hU V hV huv
  rw [Finset.mem_coe] at hU hV
  have huv' : U \ C = V \ C := by simpa using huv
  rw [← Finset.sdiff_union_of_subset (hC U hU), ← Finset.sdiff_union_of_subset (hC V hV), huv']

lemma card_substOne {P : Zheg n} {C : Finset (Fin n)} (hC : ∀ U ∈ P, C ⊆ U) :
    (substOne P C).card = P.card := by
  rw [substOne, Finset.card_image_of_injOn (injOn_sdiff hC)]

lemma zheval_substOne {P : Zheg n} {C : Finset (Fin n)} (hC : ∀ U ∈ P, C ⊆ U) (x : BVec n) :
    zheval (substOne P C) x = zheval P (setOne x C) := by
  rw [zheval, zheval, substOne]
  rw [Finset.sum_image (injOn_sdiff hC)]
  refine Finset.sum_congr rfl (fun U hU => ?_)
  have hCU : C ⊆ U := hC U hU
  rw [show (∏ i ∈ U, setOne x C i) = ∏ i ∈ U, (if i ∈ C then (1 : ZMod 2) else x i) from rfl]
  rw [Finset.prod_ite]
  have hfilter : U.filter (fun i => i ∈ C) = C := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hCU h, h⟩⟩
  have hfilt2 : U.filter (fun i => ¬ i ∈ C) = U \ C := by
    ext i
    simp [Finset.mem_sdiff]
  rw [hfilter, hfilt2, Finset.prod_const_one, one_mul]

lemma isVanishing_substOne {P : Zheg n} {C : Finset (Fin n)} {W : ℕ}
    (hC : ∀ U ∈ P, C ⊆ U) (h : IsVanishing P W) : IsVanishing (substOne P C) W := by
  intro x hx
  rw [zheval_substOne hC x]
  exact h (setOne x C) (le_trans hx (wt_le_wt_setOne x C))

lemma tot_substOne_le {P : Zheg n} {C : Finset (Fin n)} (hC : ∀ U ∈ P, C ⊆ U) :
    tot (substOne P C) ≤ tot P := by
  rw [substOne, tot, tot]
  rw [Finset.sum_image (injOn_sdiff hC)]
  exact Finset.sum_le_sum (fun U _ => Finset.card_le_card (Finset.sdiff_subset))

lemma commonSet_substOne {P : Zheg n} (hP : P.Nonempty) :
    commonSet (substOne P (commonSet P)) = ∅ := by
  rw [← Finset.not_nonempty_iff_eq_empty]
  rintro ⟨i, hi⟩
  rw [mem_commonSet] at hi
  have hsub : ∀ U ∈ P, i ∈ U \ commonSet P :=
    fun U hU => hi _ (mem_substOne.2 ⟨U, hU, rfl⟩)
  obtain ⟨U, hU⟩ := hP
  have hiU : i ∈ U := (Finset.mem_sdiff.1 (hsub U hU)).1
  have hiC : i ∉ commonSet P := (Finset.mem_sdiff.1 (hsub U hU)).2
  exact hiC (mem_commonSet.2 (fun V hV => (Finset.mem_sdiff.1 (hsub V hV)).1))


/-! ## Step 1 of Lemma 5: the degree bound

If a nonzero Zhegalkin polynomial vanishes on every point of weight at least `W`, then its
degree exceeds `n - W`.  Equivalently, if `deg P ≤ n - W` and `P` vanishes on all points of
weight at least `W`, then `P` is the zero polynomial. -/

/-- The number of monomials of `P` whose coordinates inside `U` all lie in `W`. -/
def countIn (P : Zheg n) (U W : Finset (Fin n)) : ℕ :=
  (P.filter (fun V => V ∩ U ⊆ W)).card

lemma countIn_eq_sum (P : Zheg n) (U W : Finset (Fin n)) :
    countIn P U W = ∑ V ∈ P, if V ∩ U ⊆ W then 1 else 0 := by
  rw [countIn, Finset.card_filter]

/-- The number of subsets of `U` that contain a fixed subset `C ⊆ U` is `2 ^ #(U \ C)`. -/
lemma card_powerset_filter_subset {U C : Finset (Fin n)} (hC : C ⊆ U) :
    ((U.powerset).filter (fun W => C ⊆ W)).card = 2 ^ (U \ C).card := by
  rw [← Finset.card_powerset (U \ C)]
  refine Finset.card_bij (fun W _ => W \ C) ?_ ?_ ?_
  · intro W hW
    simp only [Finset.mem_filter, Finset.mem_powerset] at hW ⊢
    exact Finset.sdiff_subset_sdiff hW.1 (le_rfl : C ⊆ C)
  · intro W₁ hW₁ W₂ hW₂ h
    simp only [Finset.mem_filter, Finset.mem_powerset] at hW₁ hW₂
    have e₁ : C ∪ (W₁ \ C) = W₁ := by
      rw [Finset.union_comm]; exact Finset.sdiff_union_of_subset hW₁.2
    have e₂ : C ∪ (W₂ \ C) = W₂ := by
      rw [Finset.union_comm]; exact Finset.sdiff_union_of_subset hW₂.2
    rw [← e₁, ← e₂, h]
  · intro S hS
    simp only [Finset.mem_powerset] at hS
    refine ⟨C ∪ S, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.union_subset hC (Finset.Subset.trans hS (Finset.sdiff_subset)),
        Finset.subset_union_left⟩
    · rw [Finset.union_comm C S, Finset.union_sdiff_self]
      exact Finset.sdiff_eq_self_iff_disjoint.2
        (Finset.disjoint_left.2 (fun a ha hc => (Finset.mem_sdiff.1 (hS ha)).2 hc))

lemma sum_countIn (P : Zheg n) (U : Finset (Fin n)) :
    ∑ W ∈ U.powerset, countIn P U W = ∑ V ∈ P, 2 ^ (U \ V).card := by
  have h1 : ∀ W, countIn P U W = ∑ V ∈ P, if V ∩ U ⊆ W then 1 else 0 := countIn_eq_sum P U
  rw [Finset.sum_congr rfl (fun W _ => h1 W), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun V _ => ?_)
  rw [← Finset.card_filter]
  rw [show U \ V = U \ (V ∩ U) from (Finset.sdiff_inter_self_right U V).symm]
  exact card_powerset_filter_subset Finset.inter_subset_right

/-- `2 ^ j` is even for `j ≥ 1`. -/
lemma even_two_pow_of_pos {j : ℕ} (hj : 0 < j) : Even (2 ^ j) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.1 hj)
  exact ⟨2 ^ i, by rw [pow_succ, mul_two]⟩

/-- The number of subsets containing a fixed subset is even iff that subset is proper. -/
lemma even_two_pow_card_sdiff_iff {U V : Finset (Fin n)} (h : U \ V ≠ ∅) :
    Even (2 ^ (U \ V).card) :=
  even_two_pow_of_pos (Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 h))

/-- For a monomial `U` of maximal degree in `P`, the total number of subsets `W ⊆ U`
weighted by `countIn P U W` is odd. -/
lemma odd_sum_two_pow_sdiff {P : Zheg n} {U : Finset (Fin n)} (hU : U ∈ P)
    (hmax : ∀ V ∈ P, V.card ≤ U.card) :
    Odd (∑ V ∈ P, 2 ^ (U \ V).card) := by
  have hsplit : ∑ V ∈ P, 2 ^ (U \ V).card
      = (∑ V ∈ P.erase U, 2 ^ (U \ V).card) + 1 := by
    rw [← Finset.sum_erase_add P _ hU]
    simp
  rw [hsplit]
  refine Even.add_odd (Finset.even_sum _ (fun V hV => ?_)) ⟨0, by norm_num⟩
  refine even_two_pow_card_sdiff_iff (fun h => ?_)
  have hsub : U ⊆ V := Finset.sdiff_eq_empty_iff_subset.1 h
  have hcard : V.card ≤ U.card := hmax V (Finset.mem_of_mem_erase hV)
  have hVU : V ≠ U := (Finset.mem_erase.1 hV).1
  exact hVU (Finset.eq_of_subset_of_card_le hsub hcard).symm

/-- Some `W ⊆ U` meets an odd number of monomials of `P` in its `U`-coordinates. -/
lemma exists_odd_countIn {P : Zheg n} {U : Finset (Fin n)} (hU : U ∈ P)
    (hmax : ∀ V ∈ P, V.card ≤ U.card) : ∃ W ⊆ U, Odd (countIn P U W) := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hall : ∀ W ∈ U.powerset, Even (countIn P U W) := fun W hW =>
    Nat.not_odd_iff_even.1 (hcon W (Finset.mem_powerset.1 hW))
  have hev : Even (∑ W ∈ U.powerset, countIn P U W) := Finset.even_sum _ hall
  rw [sum_countIn] at hev
  exact Nat.not_even_iff_odd.2 (odd_sum_two_pow_sdiff hU hmax) hev

lemma natCast_eq_one_of_odd {m : ℕ} (hm : Odd m) : (m : ZMod 2) = 1 := by
  obtain ⟨k, hk⟩ := hm
  have h2 : ((2 : ℕ) : ZMod 2) = 0 := ZMod.natCast_self 2
  rw [hk, Nat.cast_add, Nat.cast_mul, h2, Nat.cast_one, zero_mul, zero_add]

/-- **Step 1 of Lemma 5.**  A nonzero polynomial that vanishes on all points of weight at
least `W` has degree strictly larger than `n - W`. -/
theorem deg_gt_of_isVanishing {P : Zheg n} {W : ℕ} (hP : P.Nonempty)
    (hvan : IsVanishing P W) (hW : W ≤ n) : n - W < deg P := by
  by_contra hcon
  have hdeg : deg P ≤ n - W := Nat.le_of_not_lt hcon
  obtain ⟨U, hU, hsup⟩ := Finset.exists_mem_eq_sup P hP (fun U => U.card)
  have hUcard : U.card = deg P := by rw [deg]; exact hsup.symm
  have hmax : ∀ V ∈ P, V.card ≤ U.card := by
    intro V hV
    have := Finset.le_sup (s := P) (f := fun U => U.card) hV
    rwa [hsup] at this
  obtain ⟨W₀, hW₀sub, hodd⟩ := exists_odd_countIn hU hmax
  set T : Finset (Fin n) := W₀ ∪ (univ \ U) with hTdef
  have hTcard : T.card = W₀.card + (n - U.card) := by
    rw [hTdef, Finset.card_union_of_disjoint (by
      refine Finset.disjoint_left.2 (fun a ha hb => ?_)
      exact (Finset.mem_sdiff.1 hb).2 (hW₀sub ha)),
      Finset.card_sdiff_of_subset (Finset.subset_univ U)]
    simp
  have hwt : W ≤ wt (ind T) := by
    rw [wt_ind, hTcard]
    have : U.card ≤ n - W := by rw [hUcard]; exact hdeg
    omega
  have hz := hvan (ind T) hwt
  have hTsub : ∀ V, (V ⊆ T) ↔ (V ∩ U ⊆ W₀) := by
    intro V
    constructor
    · intro hV a ha
      have haU : a ∈ U := (Finset.mem_inter.1 ha).2
      rcases Finset.mem_union.1 (hV (Finset.mem_inter.1 ha).1) with h | h
      · exact h
      · exact absurd haU (Finset.mem_sdiff.1 h).2
    · intro hV a ha
      by_cases haU : a ∈ U
      · exact Finset.mem_union_left _ (hV (Finset.mem_inter.2 ⟨ha, haU⟩))
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨Finset.mem_univ a, haU⟩)
  have hzind : (P.filter (fun V => V ⊆ T)).card = countIn P U W₀ := by
    rw [countIn]
    congr 1
    exact Finset.filter_congr (fun V _ => hTsub V)
  have hval : ((countIn P U W₀ : ℕ) : ZMod 2) = 0 := by
    rw [← hzind, ← zheval_ind P T]
    exact hz
  rw [natCast_eq_one_of_odd hodd] at hval
  exact one_ne_zero hval


/-! ## The column sums `Esum` and their maximiser

`Esum P i` is the total degree of the monomials of `P` that contain the variable `x i`.  It
is the amount by which the total degree drops when `x i` is set to `0`. -/

lemma sum_ite_mem_card (U : Finset (Fin n)) (c : ℕ) :
    ∑ i : Fin n, (if i ∈ U then c else 0) = c * U.card := by
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, smul_eq_mul, mul_comm]

/-- The sum of all `Esum P i` is the sum of the squared monomial degrees. -/
lemma sum_Esum (P : Zheg n) : ∑ i : Fin n, Esum P i = ∑ U ∈ P, U.card * U.card := by
  simp only [Esum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun U _ => sum_ite_mem_card U U.card)

/-- `Esum P i` equals the sum of the degrees of the monomials containing `x i`. -/
lemma Esum_eq_sum_card (P : Zheg n) (i : Fin n) :
    Esum P i = ∑ U ∈ P.filter (fun U => i ∈ U), U.card := by
  rw [Esum, ← Finset.sum_filter]

/-- `Esum P i` is at most the number of monomials containing `x i` times `n`. -/
lemma Esum_le_card_filter_mul (P : Zheg n) (i : Fin n) :
    Esum P i ≤ (P.filter (fun U => i ∈ U)).card * n := by
  rw [Esum_eq_sum_card]
  calc ∑ U ∈ P.filter (fun U => i ∈ U), U.card
      ≤ ∑ U ∈ P.filter (fun U => i ∈ U), n :=
        Finset.sum_le_sum (fun U _ => by simpa using Finset.card_le_univ U)
    _ = (P.filter (fun U => i ∈ U)).card * n := by
        rw [Finset.sum_const, smul_eq_mul]

/-- A variable maximising `Esum`. -/
noncomputable def argmaxEsum (hn : 0 < n) (P : Zheg n) : Fin n :=
  (Finset.exists_mem_eq_sup (univ : Finset (Fin n)) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    (Esum P)).choose

lemma argmaxEsum_spec (hn : 0 < n) (P : Zheg n) :
    univ.sup (Esum P) = Esum P (argmaxEsum hn P) :=
  (Finset.exists_mem_eq_sup (univ : Finset (Fin n)) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    (Esum P)).choose_spec.2

lemma le_argmaxEsum (hn : 0 < n) (P : Zheg n) (i : Fin n) :
    Esum P i ≤ Esum P (argmaxEsum hn P) := by
  have h := Finset.le_sup (s := univ) (f := Esum P) (Finset.mem_univ i)
  rwa [argmaxEsum_spec hn P] at h

/-- The degree of `P` is at most the maximal column sum. -/
lemma deg_le_Esum_argmax (hn : 0 < n) {P : Zheg n} (hP : P.Nonempty) :
    deg P ≤ Esum P (argmaxEsum hn P) := by
  obtain ⟨U, hU, hUc⟩ := Finset.exists_mem_eq_sup P hP (fun U => U.card)
  have hUc' : U.card = deg P := by rw [deg]; exact hUc.symm
  rcases Finset.eq_empty_or_nonempty U with h | ⟨a, ha⟩
  · rw [← hUc', h]
    exact Nat.zero_le _
  · have h1 : U.card ≤ Esum P a := by
      have h2 : (if a ∈ U then U.card else 0) = U.card := by rw [ite_eq_left ha]
      rw [Esum, ← h2]
      exact Finset.single_le_sum (f := fun V => if a ∈ V then V.card else 0)
        (fun V _ => Nat.zero_le _) hU
    exact le_trans (hUc' ▸ h1) (le_argmaxEsum hn P a)


/-! ### Step 3 of Lemma 5: how many monomials are lost per step

`Esum P i` is the total degree of the monomials containing `x i`, i.e. the drop in `tot`
when `x i` is set to `0`.  Cauchy–Schwarz bounds the sum of the `Esum P i` from below by
`tot P ^ 2 / |mon P|`; since the maximal `Esum` is at least the average, setting `x i := 0`
for a maximising `i` removes at least `tot P ^ 2 / (n |mon P|)` monomials. -/

/-- Cauchy–Schwarz for the degrees of the monomials of `P`. -/
lemma tot_sq_le_card_mul_sum_sq (P : Zheg n) :
    (tot P) ^ 2 ≤ P.card * ∑ U ∈ P, U.card * U.card := by
  have h := sq_sum_le_card_mul_sum_sq (s := P) (f := fun U : Finset (Fin n) => U.card)
  simpa [tot, pow_two] using h

/-- The sum of the `Esum P i` is bounded by `n` times their maximum. -/
lemma sum_Esum_le_card_mul_argmax (hn : 0 < n) (P : Zheg n) :
    ∑ j : Fin n, Esum P j ≤ n * Esum P (argmaxEsum hn P) := by
  calc ∑ j : Fin n, Esum P j
      ≤ ∑ _j : Fin n, Esum P (argmaxEsum hn P) :=
        Finset.sum_le_sum (fun j _ => le_argmaxEsum hn P j)
    _ = n * Esum P (argmaxEsum hn P) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- Substituting `1` never increases the number of monomials. -/
lemma card_substOne_le (P : Zheg n) (C : Finset (Fin n)) :
    (substOne P C).card ≤ P.card := by
  rw [substOne]; exact Finset.card_image_le

/-- Substituting `0` never increases the number of monomials. -/
lemma card_substZero_le (P : Zheg n) (i : Fin n) :
    (substZero P i).card ≤ P.card := by
  rw [substZero]; exact Finset.card_le_card (Finset.filter_subset _ _)

/-- The monomials containing `x i` are exactly the ones lost when `x i` is set to `0`. -/
lemma card_filter_mem_le_card_sub (P : Zheg n) (i : Fin n) :
    (P.filter (fun U => i ∈ U)).card ≤ P.card - (substZero P i).card := by
  have h := card_filter_mem_add P i
  omega

/-- One descent step: set `x i := 0` for a variable `i` of maximal `Esum`, then set all
variables common to all remaining monomials to `1`. -/
noncomputable def step (hn : 0 < n) (Q : Zheg n) : Zheg n :=
  substOne (substZero Q (argmaxEsum hn Q)) (commonSet (substZero Q (argmaxEsum hn Q)))

/-- The number of monomials lost in one descent step exceeds `j ^ 4 / (4 n ^ 2 |mon Q|)`
whenever `tot Q > j ^ 2 / 2`. -/
lemma step_card_drop {Q : Zheg n} (hn : 0 < n) {j : ℕ} (hj : 1 ≤ j)
    (htot : j * (j + 3) ≤ 2 * tot Q) :
    j ^ 4 < 4 * n ^ 2 * Q.card * (Q.card - (step hn Q).card) := by
  have hA : (Q.filter (fun U => argmaxEsum hn Q ∈ U)).card ≤ Q.card - (step hn Q).card := by
    have h1 : (Q.filter (fun U => argmaxEsum hn Q ∈ U)).card
        ≤ Q.card - (substZero Q (argmaxEsum hn Q)).card :=
      card_filter_mem_le_card_sub Q (argmaxEsum hn Q)
    have h2 : (step hn Q).card ≤ (substZero Q (argmaxEsum hn Q)).card := by
      exact card_substOne_le _ _
    omega
  have hE : n * Esum Q (argmaxEsum hn Q) ≥ ∑ x : Fin n, Esum Q x := by
    have := sum_Esum_le_card_mul_argmax hn Q
    omega
  have hAn : Esum Q (argmaxEsum hn Q) ≤ (Q.filter (fun U => argmaxEsum hn Q ∈ U)).card * n :=
    Esum_le_card_filter_mul Q (argmaxEsum hn Q)
  have hcs := tot_sq_le_card_mul_sum_sq Q
  have hsumE : ∑ x : Fin n, Esum Q x = ∑ U ∈ Q, U.card * U.card := sum_Esum Q
  have hcard : (tot Q) ^ 2 ≤ n ^ 2 * Q.card * (Q.card - (step hn Q).card) := by
    calc (tot Q) ^ 2 ≤ Q.card * ∑ U ∈ Q, U.card * U.card := hcs
      _ = Q.card * ∑ x : Fin n, Esum Q x := by rw [hsumE]
      _ ≤ Q.card * (n * Esum Q (argmaxEsum hn Q)) := Nat.mul_le_mul_left _ hE
      _ ≤ Q.card * (n * ((Q.filter (fun U => argmaxEsum hn Q ∈ U)).card * n)) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul_left _ hAn
      _ ≤ Q.card * (n * ((Q.card - (step hn Q).card) * n)) := by
          apply Nat.mul_le_mul_left
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul_right _ hA
      _ = n ^ 2 * Q.card * (Q.card - (step hn Q).card) := by ring
  have htot2 : j ^ 2 < 2 * tot Q := by nlinarith [hj]
  have h4 : j ^ 4 < 4 * (tot Q) ^ 2 := by nlinarith [htot2]
  calc j ^ 4 < 4 * (tot Q) ^ 2 := h4
    _ ≤ 4 * (n ^ 2 * Q.card * (Q.card - (step hn Q).card)) := Nat.mul_le_mul_left 4 hcard
    _ = 4 * n ^ 2 * Q.card * (Q.card - (step hn Q).card) := by ring


/-! ## Step 2 of Lemma 5: the descending chain `f_k, f_{k-1}, …, f_0`

Starting from a function that vanishes on all points of weight at least `n - k`, we repeatedly
set the variable of maximal total degree to `0` and then set all common variables to `1`.  The
resulting functions stay nonzero, vanish on ever larger sets of points, and their total degree
drops by at least `j + 1` at the stage where `j` steps remain. -/

/-- If no variable is common to all monomials, setting a variable to `0` keeps a monomial. -/
lemma substZero_nonempty_of_commonSet_empty {Q : Zheg n} (hc : commonSet Q = ∅) (i : Fin n) :
    (substZero Q i).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hone : ∀ U ∈ Q, i ∈ U := by
    intro U hU
    by_contra hi
    have hmem : U ∈ substZero Q i := mem_substZero.2 ⟨hU, hi⟩
    rw [h] at hmem
    exact Finset.notMem_empty U hmem
  have : i ∈ commonSet Q := mem_commonSet.2 hone
  rw [hc] at this
  exact Finset.notMem_empty i this

/-- The variables common to all monomials of `P` occur in every monomial of `P`. -/
lemma commonSet_subset_monomial {P : Zheg n} {U : Finset (Fin n)} (hU : U ∈ P) :
    commonSet P ⊆ U := fun _ hi => mem_commonSet.1 hi U hU

/-- The descending chain of Lemma 5: `fk hn P m` is the function obtained from `P` after `m`
steps, i.e. `f_{k-m}` in the notation of the paper. -/
noncomputable def fk (hn : 0 < n) (P : Zheg n) : ℕ → Zheg n
  | 0 => substOne P (commonSet P)
  | m + 1 => step hn (fk hn P m)

lemma fk_zero (hn : 0 < n) (P : Zheg n) : fk hn P 0 = substOne P (commonSet P) := rfl

lemma fk_succ (hn : 0 < n) (P : Zheg n) (m : ℕ) :
    fk hn P (m + 1) = step hn (fk hn P m) := rfl

lemma card_fk_zero (hn : 0 < n) {P : Zheg n} : (fk hn P 0).card = P.card := by
  rw [fk_zero]
  exact card_substOne (fun U hU => commonSet_subset_monomial hU)

lemma card_step_le (hn : 0 < n) (Q : Zheg n) : (step hn Q).card ≤ Q.card := by
  rw [step]
  exact le_trans (card_substOne_le _ _) (card_substZero_le Q _)

/-- One step never increases the number of monomials. -/
lemma card_fk_le (hn : 0 < n) (P : Zheg n) (m : ℕ) : (fk hn P m).card ≤ P.card := by
  induction m with
  | zero => rw [fk_zero]; exact le_of_eq (card_fk_zero hn)
  | succ m ih => rw [fk_succ]; exact le_trans (card_step_le hn _) ih

lemma card_fk_succ_le (hn : 0 < n) (P : Zheg n) (m : ℕ) :
    (fk hn P (m + 1)).card ≤ (fk hn P m).card := by
  rw [fk_succ]
  exact card_step_le hn _

/-- Every function of the chain is nonzero and has no common variable. -/
lemma fk_inv (hn : 0 < n) {P : Zheg n} (hP : P.Nonempty) (m : ℕ) :
    (fk hn P m).Nonempty ∧ commonSet (fk hn P m) = ∅ := by
  induction m with
  | zero =>
      rw [fk_zero]
      exact ⟨substOne_nonempty hP, commonSet_substOne hP⟩
  | succ m ih =>
      obtain ⟨hne, hc⟩ := ih
      rw [fk_succ]
      have hsub : (substZero (fk hn P m) (argmaxEsum hn (fk hn P m))).Nonempty :=
        substZero_nonempty_of_commonSet_empty hc _
      exact ⟨substOne_nonempty hsub, commonSet_substOne hsub⟩

/-- The `m`-th function of the chain vanishes on all points of weight at least `n - k + m`. -/
lemma isVanishing_fk (hn : 0 < n) {P : Zheg n} {k : ℕ} (hvan : IsVanishing P (n - k))
    (m : ℕ) : IsVanishing (fk hn P m) (n - k + m) := by
  induction m with
  | zero =>
      rw [fk_zero, Nat.add_zero]
      exact isVanishing_substOne (fun U hU => commonSet_subset_monomial hU) hvan
  | succ m ih =>
      rw [fk_succ, step, Nat.add_succ]
      exact isVanishing_substOne (fun U hU => commonSet_subset_monomial hU)
        (isVanishing_substZero ih _)

/-- At the stage with `j` steps remaining, one step drops the total degree by at least
`j + 1`: the maximal column sum is at least `deg ≥ j + 1`, and setting the corresponding
variable to `0` reduces `tot` by exactly that column sum. -/
lemma tot_step_drop (hn : 0 < n) {Q : Zheg n} {j : ℕ} (hjn : j ≤ n)
    (hne : Q.Nonempty) (hvan : IsVanishing Q (n - j)) :
    tot (step hn Q) + (j + 1) ≤ tot Q := by
  have hdeg : j + 1 ≤ deg Q := by
    have h := deg_gt_of_isVanishing hne hvan (Nat.sub_le n j)
    have hnj : n - (n - j) = j := Nat.sub_sub_self hjn
    omega
  have hE : deg Q ≤ Esum Q (argmaxEsum hn Q) := deg_le_Esum_argmax hn hne
  have h1 : tot (substZero Q (argmaxEsum hn Q)) + Esum Q (argmaxEsum hn Q) = tot Q :=
    tot_substZero Q (argmaxEsum hn Q)
  have h2 : tot (step hn Q) ≤ tot (substZero Q (argmaxEsum hn Q)) := by
    rw [step]
    exact tot_substOne_le (fun U hU => commonSet_subset_monomial hU)
  omega

/-- The total degree of the `m`-th function of the chain, where `j = k - m` steps remain,
satisfies `j * (j + 3) ≤ 2 * tot`.  In particular `tot > j ^ 2 / 2`. -/
lemma chain_tot (hn : 0 < n) {k : ℕ} (hk : k ≤ n) {P : Zheg n} (hP : P.Nonempty)
    (hvan : IsVanishing P (n - k)) (m : ℕ) (hm : m ≤ k) :
    (k - m) * (k - m + 3) ≤ 2 * tot (fk hn P m) := by
  have hvan' : ∀ i, i ≤ k → IsVanishing (fk hn P i) (n - (k - i)) := by
    intro i hi
    have h := isVanishing_fk hn hvan i
    have he : n - k + i = n - (k - i) := by omega
    rwa [he] at h
  refine Nat.decreasingInduction'
    (P := fun m => (k - m) * (k - m + 3) ≤ 2 * tot (fk hn P m))
    (fun i hi _ ih => ?_) hm ?_
  · have hne : (fk hn P i).Nonempty := (fk_inv hn hP i).1
    have hd := tot_step_drop hn (Q := fk hn P i) (j := k - i) (by omega) hne
      (hvan' i (le_of_lt hi))
    rw [← fk_succ] at hd
    have harith : (k - i) * (k - i + 3)
        = (k - (i + 1)) * (k - (i + 1) + 3) + 2 * (k - i + 1) := by
      have hsub : k - (i + 1) = k - i - 1 := by omega
      rw [hsub]
      obtain ⟨d, hd'⟩ : ∃ d, k - i = d + 1 := ⟨k - i - 1, by omega⟩
      rw [hd']
      simp only [Nat.add_sub_cancel]
      ring
    calc (k - i) * (k - i + 3)
        = (k - (i + 1)) * (k - (i + 1) + 3) + 2 * (k - i + 1) := harith
      _ ≤ 2 * tot (fk hn P (i + 1)) + 2 * (k - i + 1) := by omega
      _ ≤ 2 * tot (fk hn P i) := by omega
  · simp


/-! ## Step 3 of Lemma 5: the Cauchy–Schwarz count and the numerical core

Summing the per-stage loss over the whole chain and using `∑ j^4 ≥ k^5 / 5` gives
`20 n² s² > k^5`, where `s` is the number of monomials of the initial function.  This is the
integer form of the estimate; `lemma5` converts it into `μ_{n,k} > k^{5/2}/(5n)`. -/

/-- `∑_{j<n} (j+1)^4 ≥ n^5/5`, integer form. -/
lemma sum_pow_five_int (k : ℕ) :
    (k : ℤ) ^ 5 ≤ 5 * ∑ j ∈ Finset.range k, (((j + 1 : ℕ) : ℤ)) ^ 4 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      push_cast at ih ⊢
      have hx : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg k
      have hkey : ((k : ℤ) + 1) ^ 5 ≤ (k : ℤ) ^ 5 + 5 * ((k : ℤ) + 1) ^ 4 := by
        nlinarith [mul_nonneg hx hx, mul_nonneg (mul_nonneg hx hx) hx]
      linarith [ih]

/-- `∑_{j<n} (j+1)^4 ≥ n^5/5`. -/
lemma sum_pow_five (k : ℕ) : k ^ 5 ≤ 5 * ∑ j ∈ Finset.range k, (j + 1) ^ 4 := by
  have h := sum_pow_five_int k
  have h' : ((k ^ 5 : ℕ) : ℤ) ≤ ((5 * ∑ j ∈ Finset.range k, (j + 1) ^ 4 : ℕ) : ℤ) := by
    push_cast
    exact h
  exact_mod_cast h'

/-- The monomial counts along the chain telescope. -/
lemma sum_range_card_drop (hn : 0 < n) (P : Zheg n) (k : ℕ) :
    ∑ i ∈ Finset.range k, ((fk hn P i).card - (fk hn P (i + 1)).card)
      = P.card - (fk hn P k).card := by
  induction k with
  | zero => simp [card_fk_zero hn]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : (fk hn P (k + 1)).card ≤ (fk hn P k).card := card_fk_succ_le hn P k
      have h2 : (fk hn P k).card ≤ P.card := card_fk_le hn P k
      omega

/-- Every stage of the chain loses more than `(k-i)^4 / (4 n² s)` monomials. -/
lemma stage_drop (hn : 0 < n) {k : ℕ} (hk : k ≤ n) {P : Zheg n} (hP : P.Nonempty)
    (hvan : IsVanishing P (n - k)) {i : ℕ} (hi : i < k) :
    (k - i) ^ 4 < 4 * n ^ 2 * P.card * ((fk hn P i).card - (fk hn P (i + 1)).card) := by
  have htot := chain_tot hn hk hP hvan i (le_of_lt hi)
  have h := step_card_drop (Q := fk hn P i) hn (j := k - i) (by omega) htot
  rw [← fk_succ] at h
  refine lt_of_lt_of_le h (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (card_fk_le hn P i)))

/-- **The numerical core of Lemma 5.**  A nonzero function in `n` variables vanishing on all
points of weight at least `n - k` has more than `k^5/(20 n²)` monomials. -/
theorem card_bound_of_vanishing (hn : 0 < n) {k : ℕ} (hk : k ≤ n) {P : Zheg n}
    (hP : P.Nonempty) (hvan : IsVanishing P (n - k)) :
    k ^ 5 < 20 * n ^ 2 * P.card ^ 2 := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have hs : 0 < P.card := Finset.card_pos.2 hP
    have h : 0 < 20 * n ^ 2 * P.card ^ 2 :=
      Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos hn 2)) (pow_pos hs 2)
    simpa using h
  · have hsum_lt : ∑ i ∈ Finset.range k, (k - i) ^ 4
        < ∑ i ∈ Finset.range k,
            4 * n ^ 2 * P.card * ((fk hn P i).card - (fk hn P (i + 1)).card) := by
      refine Finset.sum_lt_sum
        (fun i hi => le_of_lt (stage_drop hn hk hP hvan (Finset.mem_range.1 hi))) ?_
      exact ⟨0, Finset.mem_range.2 hkpos, stage_drop hn hk hP hvan hkpos⟩
    have hsum_eq : ∑ i ∈ Finset.range k,
          4 * n ^ 2 * P.card * ((fk hn P i).card - (fk hn P (i + 1)).card)
        = 4 * n ^ 2 * P.card
            * ∑ i ∈ Finset.range k, ((fk hn P i).card - (fk hn P (i + 1)).card) := by
      rw [Finset.mul_sum]
    have hle : ∑ i ∈ Finset.range k, ((fk hn P i).card - (fk hn P (i + 1)).card) ≤ P.card := by
      rw [sum_range_card_drop]
      exact Nat.sub_le _ _
    have hbound : ∑ i ∈ Finset.range k, (k - i) ^ 4 < 4 * n ^ 2 * P.card * P.card := by
      calc ∑ i ∈ Finset.range k, (k - i) ^ 4
          < ∑ i ∈ Finset.range k,
              4 * n ^ 2 * P.card * ((fk hn P i).card - (fk hn P (i + 1)).card) := hsum_lt
        _ = 4 * n ^ 2 * P.card
              * ∑ i ∈ Finset.range k, ((fk hn P i).card - (fk hn P (i + 1)).card) := hsum_eq
        _ ≤ 4 * n ^ 2 * P.card * P.card := Nat.mul_le_mul_left _ hle
    have hreflect : ∑ i ∈ Finset.range k, (k - i) ^ 4 = ∑ j ∈ Finset.range k, (j + 1) ^ 4 := by
      have h := Finset.sum_range_reflect (fun j => (k - j) ^ 4) k
      rw [← h]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' : i < k := Finset.mem_range.1 hi
      congr 1
      omega
    calc k ^ 5 ≤ 5 * ∑ j ∈ Finset.range k, (j + 1) ^ 4 := sum_pow_five k
      _ = 5 * ∑ i ∈ Finset.range k, (k - i) ^ 4 := by rw [hreflect]
      _ < 5 * (4 * n ^ 2 * P.card * P.card) := Nat.mul_lt_mul_of_pos_left hbound (by norm_num)
      _ = 20 * n ^ 2 * P.card ^ 2 := by ring

/-! ### The quantity `μ_{n,k}` and Lemma 5 -/

/-- `μ_{n,k}`: the minimal number of monomials of a nonzero Boolean function in `n` variables
that vanishes on every Boolean vector of weight at least `n - k`. -/
noncomputable def mu (n k : ℕ) : ℕ :=
  sInf {s : ℕ | ∃ P : Zheg n, P.Nonempty ∧ IsVanishing P (n - k) ∧ P.card = s}

/-- The defining set of `μ_{n,k}` is nonempty: the `NOR` function (the full powerset of
monomials) vanishes on every nonzero Boolean vector. -/
lemma mu_set_nonempty (_hn : 0 < n) {k : ℕ} (hk : k < n) :
    ({s : ℕ | ∃ P : Zheg n, P.Nonempty ∧ IsVanishing P (n - k) ∧ P.card = s}).Nonempty := by
  refine ⟨((univ : Finset (Fin n)).powerset).card, (univ : Finset (Fin n)).powerset,
    ⟨∅, by simp⟩, ?_, rfl⟩
  intro x hx
  rw [zheval_powerset]
  exact natCast_two_pow_eq_zero (by omega)

/-- A function attaining `μ_{n,k}`. -/
lemma mu_spec (hn : 0 < n) {k : ℕ} (hk : k < n) :
    ∃ P : Zheg n, P.Nonempty ∧ IsVanishing P (n - k) ∧ P.card = mu n k := by
  have hmem := Nat.sInf_mem (mu_set_nonempty hn hk)
  simpa [mu] using hmem

/-- **Lemma 5, integer form**: `20 n² μ_{n,k}² > k^5`. -/
theorem lemma5_int {n k : ℕ} (hk : k < n) : k ^ 5 < 20 * n ^ 2 * (mu n k) ^ 2 := by
  have hn : 0 < n := by omega
  obtain ⟨P, hP, hvan, hcard⟩ := mu_spec hn hk
  have h := card_bound_of_vanishing hn (le_of_lt hk) hP hvan
  rwa [hcard] at h

/-- `k^(5/2) = √(k^5)`. -/
lemma rpow_five_halves (k : ℕ) : ((k : ℝ) ^ (5 / 2 : ℝ)) = Real.sqrt ((k : ℝ) ^ 5) := by
  rw [show (5 / 2 : ℝ) = 5 * (1 / 2 : ℝ) by norm_num, Real.rpow_mul (by positivity)]
  rw [← Real.rpow_natCast]
  exact (Real.sqrt_eq_rpow ((k : ℝ) ^ 5)).symm

/-- From `k^5 < 20 n² s²` and `n, s > 0` deduce `s > k^(5/2)/(5n)`. -/
lemma real_bound_of_int (n k s : ℕ) (hn : 0 < n) (hs : 0 < s)
    (h20 : k ^ 5 < 20 * n ^ 2 * s ^ 2) :
    (k : ℝ) ^ (5 / 2 : ℝ) / (5 * n) < (s : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have h20R : ((k : ℝ)) ^ 5 < 20 * (n : ℝ) ^ 2 * (s : ℝ) ^ 2 := by exact_mod_cast h20
  have hK : Real.sqrt ((k : ℝ) ^ 5) ^ 2 = (k : ℝ) ^ 5 := Real.sq_sqrt (by positivity)
  have hsq : (2 * Real.sqrt 5 * (n : ℝ) * (s : ℝ)) ^ 2 = 20 * (n : ℝ) ^ 2 * (s : ℝ) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 5)]
    ring
  have hsqrt5 : 2 * Real.sqrt 5 < 5 := by
    have h : Real.sqrt 5 < 5 / 2 := by
      have h2 := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 5) (by norm_num : (5:ℝ) < (5/2)^2)
      rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 5/2)] at h2
    nlinarith
  have hnonneg : (0 : ℝ) ≤ 2 * Real.sqrt 5 * (n : ℝ) * (s : ℝ) := by positivity
  have hlt : Real.sqrt ((k : ℝ) ^ 5) < 2 * Real.sqrt 5 * (n : ℝ) * (s : ℝ) := by
    by_contra hcon
    push Not at hcon
    have : (2 * Real.sqrt 5 * (n : ℝ) * (s : ℝ)) ^ 2 ≤ Real.sqrt ((k : ℝ) ^ 5) ^ 2 := by
      exact pow_le_pow_left₀ hnonneg hcon 2
    rw [hsq, hK] at this
    linarith
  rw [rpow_five_halves]
  have h5n : (0 : ℝ) < 5 * (n : ℝ) := by positivity
  rw [div_lt_iff₀ h5n]
  have hns : (0 : ℝ) < (n : ℝ) * (s : ℝ) := mul_pos hnR hsR
  have h25 : 2 * Real.sqrt 5 * (n : ℝ) * (s : ℝ) < 5 * (n : ℝ) * (s : ℝ) := by
    nlinarith [hsqrt5, hns]
  linarith [hlt, h25]

/-- **Lemma 5** (`\label{munk}`): for `0 ≤ k < n`, every nonzero Boolean function in `n`
variables vanishing on all vectors of weight at least `n - k` has more than `k^(5/2)/(5n)`
monomials; equivalently `μ_{n,k} > k^(5/2)/(5n)`. -/
theorem lemma5 {n k : ℕ} (hk : k < n) :
    (k : ℝ) ^ (5 / 2 : ℝ) / (5 * n) < (mu n k : ℝ) := by
  have hn : 0 < n := by omega
  have hmu : 0 < mu n k := by
    obtain ⟨P, hP, -, hcard⟩ := mu_spec hn hk
    rw [← hcard]
    exact Finset.card_pos.2 hP
  exact real_bound_of_int n k (mu n k) hn hmu (lemma5_int hk)


/-! ## The submatrix `D_{n,k}` and Lemma 6 -/

/-- The column indices of `D_{n,k}`: the subsets of `[n]` of cardinality at most `k`. -/
abbrev ColIdx (n k : ℕ) := {J : Finset (Fin n) // J.card ≤ k}

/-- The number of columns of `D_{n,k}`, i.e. `C(n,0) + … + C(n,k)`. -/
noncomputable def mDk (n k : ℕ) : ℕ := Fintype.card (ColIdx n k)

/-- An enumeration of the columns of `D_{n,k}`. -/
noncomputable def colEquiv (n k : ℕ) : ColIdx n k ≃ Fin (mDk n k) := Fintype.equivFin _

/-- The row of `D_{n,k}` with row index `I`: its entry at the column `J` is `D n I J`. -/
noncomputable def DkRow (n k : ℕ) (I : Finset (Fin n)) : BVec (mDk n k) :=
  fun t => D n I ((colEquiv n k).symm t).1

/-- The set of rows of the submatrix `D_{n,k}`, as a set of vectors of length `mDk n k`. -/
noncomputable def DkRowSet (n k : ℕ) : Finset (BVec (mDk n k)) :=
  univ.image (DkRow n k)

@[simp] theorem mem_DkRowSet {n k : ℕ} {v : BVec (mDk n k)} :
    v ∈ DkRowSet n k ↔ ∃ I : Finset (Fin n), DkRow n k I = v := by
  simp [DkRowSet]

theorem DkRow_apply {n k : ℕ} (I : Finset (Fin n)) (J : ColIdx n k) :
    DkRow n k I (colEquiv n k J) = D n I J.1 := by
  simp [DkRow]

/-- The rows of `D_{n,k}` are distinct as soon as `k ≥ 1` (the singleton columns separate
them). -/
theorem DkRow_injective {n k : ℕ} (hk : 1 ≤ k) : Function.Injective (DkRow n k) := by
  intro I I' h
  ext i
  have hsing : ∀ L : Finset (Fin n),
      DkRow n k L (colEquiv n k ⟨{i}, by simpa using hk⟩) = D n L {i} := by
    intro L; exact DkRow_apply L ⟨{i}, by simpa using hk⟩
  have h1 : D n I {i} = D n I' {i} := by rw [← hsing I, ← hsing I', h]
  have h2 : Disjoint I {i} ↔ Disjoint I' {i} := by
    rw [← D.eq_one_iff, ← D.eq_one_iff, h1]
  simp only [Finset.disjoint_singleton_right] at h2
  simpa using h2.not

/-- The sum of the entries of `D` along a row set, as a parity count. -/
lemma sum_D_eq_card {n : ℕ} (T : Finset (Finset (Fin n))) (J : Finset (Fin n)) :
    ∑ I ∈ T, D n I J = ((T.filter (fun I => D n I J = 1)).card : ZMod 2) := by
  have h : ∀ I ∈ T, D n I J = if Disjoint I J then (1 : ZMod 2) else 0 := fun I _ => D.apply I J
  rw [Finset.sum_congr rfl h, Finset.sum_boole]
  have hfilter : T.filter (fun I => Disjoint I J) = T.filter (fun I => D n I J = 1) :=
    Finset.filter_congr (fun I _ => D.eq_one_iff.symm)
  rw [hfilter]

/-- A Boolean vector is the indicator of its support. -/
lemma ind_supp {n : ℕ} (x : BVec n) : ind (supp x) = x := by
  funext i
  by_cases h : x i = 0
  · have : i ∉ supp x := by simpa [mem_supp] using h
    simp [ind, this, h]
  · have h1 : x i = 1 := zmod2_eq_one_of_ne_zero h
    have : i ∈ supp x := mem_supp.2 h
    simp [ind, this, h1]

/-- Over `GF(2)`, a finite set of distinct vectors is linearly independent as soon as no
nonempty subfamily sums to zero. -/
theorem indep_of_sum_ne_zero {m : ℕ} {S : Finset (BVec m)}
    (h : ∀ T : Finset (BVec m), T ⊆ S → T.Nonempty → (∑ x ∈ T, x) ≠ 0) :
    MooreBound.Indep S := by
  rw [MooreBound.Indep, linearIndependent_iff']
  intro s g hsum i hi
  set T := s.filter (fun j => g j = 1) with hT
  have hcoef : ∀ j ∈ s, g j • ((j : S) : BVec m) = if g j = 1 then ((j : S) : BVec m) else 0 := by
    intro j _
    rcases zmod2_eq_zero_or_one (g j) with h0 | h1
    · rw [h0, zero_smul, ite_eq_right (by decide : ¬ (0 : ZMod 2) = 1)]
    · rw [h1, one_smul, ite_eq_left rfl]
  have hsum' : ∑ j ∈ T, ((j : S) : BVec m) = 0 := by
    rw [hT, Finset.sum_filter]
    rw [Finset.sum_congr rfl hcoef] at hsum
    exact hsum
  set T' := T.image (fun j : S => ((j : S) : BVec m)) with hT'
  have hT'sub : T' ⊆ S := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    exact j.2
  by_cases hTne : T.Nonempty
  · have hT'ne : T'.Nonempty := hTne.image _
    have hzero : ∑ x ∈ T', x = 0 := by
      rw [hT']
      rw [Finset.sum_image (f := fun x : BVec m => x) (g := fun j : S => ((j : S) : BVec m))
        (fun a _ b _ hab => Subtype.val_injective hab)]
      simpa using hsum' 
    exact absurd hzero (h T' hT'sub hT'ne)
  · rw [Finset.not_nonempty_iff_eq_empty] at hTne
    have gne : g i ≠ 1 := by
      intro h1
      have : i ∈ T := Finset.mem_filter.2 ⟨hi, h1⟩
      rw [hTne] at this
      simp at this
    rcases zmod2_eq_zero_or_one (g i) with h0 | h1
    · exact h0
    · exact absurd h1 gne

/-- **Lemma 6, independence part**: every set of at most `μ_{n,k} - 1` rows of `D_{n,k}` is
linearly independent. -/
theorem allIndep_DkRowSet {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) :
    MooreBound.AllIndep (DkRowSet n k) (mu n k - 1) := by
  intro S hS hScard
  refine indep_of_sum_ne_zero (fun T hTS hTne => ?_)
  -- the row indices of the elements of `T`
  set T' : Finset (Finset (Fin n)) := univ.filter (fun I => DkRow n k I ∈ T) with hT'def
  have himage : T'.image (DkRow n k) = T := by
    ext x
    constructor
    · intro hx
      obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hI).2
    · intro hx
      obtain ⟨I, -, hI⟩ := Finset.mem_image.mp (hS (hTS hx))
      exact Finset.mem_image.mpr
        ⟨I, Finset.mem_filter.mpr ⟨Finset.mem_univ I, hI ▸ hx⟩, hI⟩
  have hT'card : T'.card = T.card := by
    rw [← himage]
    exact (Finset.card_image_of_injective T' (DkRow_injective hk1)).symm
  have hT'ne : T'.Nonempty := by
    obtain ⟨x, hx⟩ := hTne
    rw [← himage] at hx
    obtain ⟨I, hI, -⟩ := Finset.mem_image.mp hx
    exact ⟨I, hI⟩
  -- the polynomial with monomials `T'`
  have hnotvan : ¬ IsVanishing T' (n - k) := by
    intro hvan
    have hmem : mu n k ≤ T'.card := Nat.sInf_le ⟨T', hT'ne, hvan, rfl⟩
    have hle : T.card ≤ S.card := Finset.card_le_card hTS
    have hpos : 0 < T.card := Finset.card_pos.2 hTne
    omega
  obtain ⟨σ, hσwt, hσne⟩ : ∃ σ : BVec n, n - k ≤ wt σ ∧ zheval T' σ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hnotvan hcon
  have hσone : zheval T' σ = 1 := zmod2_eq_one_of_ne_zero hσne
  -- the column of zeros of `σ`
  set J : Finset (Fin n) := univ \ supp σ with hJdef
  have hJcard : J.card ≤ k := by
    have h1 : J.card = n - wt σ := by
      rw [hJdef, Finset.card_sdiff]
      simp [wt]
    omega
  set t : Fin (mDk n k) := colEquiv n k ⟨J, hJcard⟩ with htdef
  have ht_apply : ∀ I : Finset (Fin n), DkRow n k I t = D n I J := by
    intro I; simp [DkRow, htdef]
  -- the coordinate `t` of the sum of the rows
  have hcoord : (∑ x ∈ T, x) t = 1 := by
    rw [Finset.sum_apply, ← himage]
    rw [Finset.sum_image (f := fun x : BVec (mDk n k) => x t)]
    · simp only [ht_apply]
      rw [sum_D_eq_card]
      have hfilter : T'.filter (fun I => D n I J = 1) = T'.filter (fun I => I ⊆ supp σ) := by
        refine Finset.filter_congr (fun I _ => ?_)
        rw [D.eq_one_iff, hJdef, Finset.disjoint_left]
        constructor
        · intro h i hi
          by_contra hni
          exact h hi (Finset.mem_sdiff.2 ⟨Finset.mem_univ i, hni⟩)
        · intro h i hi hJ
          rw [Finset.mem_sdiff] at hJ
          exact hJ.2 (h hi)
      rw [hfilter, ← zheval_ind, ind_supp, hσone]
    · exact fun a _ b _ hab => DkRow_injective hk1 hab
  intro hzero
  rw [hzero] at hcoord
  exact one_ne_zero hcoord.symm

/-- **Lemma 6** (`\label{ind_mu}`): the independence index of the submatrix `D_{n,k}` of `D_n`
formed by the columns indexed by sets of size at most `k` is at least `μ_{n,k} - 1`. -/
theorem lemma6 {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) :
    mu n k - 1 ≤ MooreBound.ind (DkRowSet n k) := by
  have hn : 0 < n := by omega
  refine MooreBound.le_ind (allIndep_DkRowSet hk1 hkn) ?_
  have hmu : mu n k ≤ 2 ^ n := by
    have hmem : (2 ^ n) ∈ {s : ℕ | ∃ P : Zheg n, P.Nonempty ∧ IsVanishing P (n - k) ∧ P.card = s} := by
      refine ⟨(univ : Finset (Fin n)).powerset, ⟨∅, by simp⟩, ?_, ?_⟩
      · intro x hx
        rw [zheval_powerset]
        exact natCast_two_pow_eq_zero (by omega)
      · rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
    have := Nat.sInf_le hmem
    simpa [mu] using this
  have hcard : (DkRowSet n k).card = 2 ^ n := by
    rw [DkRowSet, Finset.card_image_of_injective _ (DkRow_injective hk1), Finset.card_univ,
      Fintype.card_finset, Fintype.card_fin]
  rw [hcard]; omega


/-! ## Chunk 1: the matrix `D_n` and the submatrix `D_{n,k}` -/

/-- The enumeration of the subsets of `[n]` by `Fin (2^n)`. -/
noncomputable def setEquiv (n : ℕ) : Finset (Fin n) ≃ Fin (2 ^ n) :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_finset, Fintype.card_fin])

/-- The Sierpinski matrix `D_n` as a square matrix indexed by `Fin (2^n)`. -/
noncomputable abbrev Dmat (n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) (ZMod 2) :=
  fun i j => D n ((setEquiv n).symm i) ((setEquiv n).symm j)

theorem Dmat_apply (n : ℕ) (i j : Fin (2 ^ n)) :
    Dmat n i j = D n ((setEquiv n).symm i) ((setEquiv n).symm j) := rfl

/-- `D_n` is symmetric. -/
theorem Dmat_transpose (n : ℕ) : Matrix.transpose (Dmat n) = Dmat n := by
  funext i j
  exact D.comm _ _

/-- The matrix of the submatrix `D_{n,k}`: rows indexed by `Fin (2^n)`, columns by
`Fin (mDk n k)`. -/
noncomputable abbrev DkMat (n k : ℕ) : Matrix (Fin (2 ^ n)) (Fin (mDk n k)) (ZMod 2) :=
  fun i t => D n ((setEquiv n).symm i) ((colEquiv n k).symm t).1

theorem DkMat_apply (n k : ℕ) (i : Fin (2 ^ n)) (t : Fin (mDk n k)) :
    DkMat n k i t = DkRow n k ((setEquiv n).symm i) t := rfl

/-- The rows of `D_k` commute with the matrix view. -/
theorem DkMat_row (n k : ℕ) (I : Finset (Fin n)) :
    DkMat n k (setEquiv n I) = DkRow n k I := by
  funext t
  simp only [DkMat, DkRow, Equiv.symm_apply_apply]

/-- The rows of the submatrix, as a set of vectors. -/
theorem DkRowSet_eq_image (n k : ℕ) :
    DkRowSet n k = (univ : Finset (Fin (2 ^ n))).image (fun i => DkMat n k i) := by
  ext v
  rw [DkRowSet, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨I, -, h⟩
    exact ⟨setEquiv n I, Finset.mem_univ _, by rw [← h, DkMat_row]⟩
  · rintro ⟨i, -, h⟩
    refine ⟨(setEquiv n).symm i, Finset.mem_univ _, ?_⟩
    rw [← h, ← DkMat_row n k ((setEquiv n).symm i), Equiv.apply_symm_apply]

/-- The rows of `D_{n,k}` with the row `I = [n]` deleted.  This is the set of rows to which
Theorem 2 is applied: the full set `[n]` spans a row of weight `1`, which Theorem 2 excludes. -/
noncomputable def DkRowSetP (n k : ℕ) : Finset (BVec (mDk n k)) :=
  ((univ : Finset (Finset (Fin n))).erase (univ : Finset (Fin n))).image (DkRow n k)

theorem mem_DkRowSetP {n k : ℕ} {v : BVec (mDk n k)} :
    v ∈ DkRowSetP n k ↔ ∃ I : Finset (Fin n), I ≠ univ ∧ DkRow n k I = v := by
  rw [DkRowSetP, Finset.mem_image]
  constructor
  · rintro ⟨I, hI, h⟩
    rw [Finset.mem_erase] at hI
    exact ⟨I, hI.1, h⟩
  · rintro ⟨I, hI, h⟩
    exact ⟨I, Finset.mem_erase.mpr ⟨hI, Finset.mem_univ I⟩, h⟩

theorem DkRowSetP_subset (n k : ℕ) : DkRowSetP n k ⊆ DkRowSet n k := by
  intro v hv
  obtain ⟨I, -, h⟩ := mem_DkRowSetP.mp hv
  rw [← h]
  exact mem_DkRowSet.mpr ⟨I, rfl⟩

theorem card_DkRowSetP {n k : ℕ} (hk : 1 ≤ k) :
    (DkRowSetP n k).card = 2 ^ n - 1 := by
  rw [DkRowSetP, Finset.card_image_of_injective _ (DkRow_injective hk),
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_finset,
    Fintype.card_fin]


/-! ## Independence of the rows of `D_{n,k}` -/

theorem mu_le_two_pow {n k : ℕ} (hkn : k < n) : mu n k ≤ 2 ^ n := by
  have hmem : (2 ^ n) ∈ {s : ℕ | ∃ P : Zheg n, P.Nonempty ∧ IsVanishing P (n - k) ∧ P.card = s} := by
    refine ⟨(univ : Finset (Fin n)).powerset, ⟨∅, by simp⟩, ?_, ?_⟩
    · intro x hx
      rw [zheval_powerset]
      exact natCast_two_pow_eq_zero (by omega)
    · rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
  exact Nat.sInf_le hmem

theorem ind_DkRowSetP {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) :
    mu n k - 2 ≤ MooreBound.ind (DkRowSetP n k) := by
  refine MooreBound.le_ind (r := mu n k - 2) ?_ ?_
  · intro S hS hScard
    refine MooreBound.ind_elim (B := DkRowSet n k) (r := mu n k - 2) ?_ ?_ hScard
    · have h6 := lemma6 hk1 hkn
      omega
    · exact Subset.trans hS (DkRowSetP_subset n k)
  · rw [card_DkRowSetP hk1]
    have := mu_le_two_pow hkn
    omega

theorem two_le_weight_DkRow {n k : ℕ} (hk1 : 1 ≤ k) {I : Finset (Fin n)} (hI : I ≠ univ) :
    2 ≤ weight (univ : Finset (Fin (mDk n k))) (DkRow n k I) := by
  obtain ⟨i, hi⟩ : ∃ i : Fin n, i ∉ I := by
    by_contra h
    push Not at h
    exact hI (Finset.eq_univ_of_forall h)
  set t0 : Fin (mDk n k) := colEquiv n k ⟨(∅ : Finset (Fin n)), by simp⟩ with ht0
  set t1 : Fin (mDk n k) := colEquiv n k ⟨{i}, by rw [Finset.card_singleton]; exact hk1⟩ with ht1
  have h0 : DkRow n k I t0 = 1 := by
    rw [ht0, DkRow_apply]
    exact D.apply_of_disjoint (Finset.disjoint_empty_right I)
  have h1 : DkRow n k I t1 = 1 := by
    rw [ht1, DkRow_apply, D.eq_one_iff, Finset.disjoint_singleton_right]
    exact hi
  have htne : t0 ≠ t1 := by
    intro h
    have h2 : ((colEquiv n k).symm t0).1 = ((colEquiv n k).symm t1).1 :=
      congrArg (fun J : ColIdx n k => J.1) (by rw [h])
    rw [ht0, ht1] at h2
    simp only [Equiv.symm_apply_apply] at h2
    exact absurd (by simpa using h2.symm) (Finset.singleton_ne_empty i)
  have hsub : ({t0, t1} : Finset (Fin (mDk n k))) ⊆
      Finset.univ.filter (fun t => DkRow n k I t ≠ 0) := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [h0]; exact one_ne_zero⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [h1]; exact one_ne_zero⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair htne] at hcard
  simpa [weight] using hcard

theorem weight_DkRow_ne_one {n k : ℕ} (hk1 : 1 ≤ k) {I : Finset (Fin n)} (hI : I ≠ univ) :
    weight (univ : Finset (Fin (mDk n k))) (DkRow n k I) ≠ 1 := by
  have := two_le_weight_DkRow hk1 hI
  omega

/-! ## Counting the columns of `D_{n,k}` -/

theorem card_ColIdx (n k : ℕ) :
    Fintype.card (ColIdx n k) = ∑ j ∈ Finset.range (k + 1), n.choose j := by
  have h1 : Fintype.card (ColIdx n k) =
      ((univ : Finset (Finset (Fin n))).filter (fun J => J.card ≤ k)).card :=
    Fintype.card_subtype _
  have hstep :
      ((univ : Finset (Finset (Fin n))).filter (fun J => J.card ≤ k)).card =
        ∑ j ∈ Finset.range (k + 1),
          (((univ : Finset (Finset (Fin n))).filter (fun J => J.card ≤ k)).filter
            (fun J => J.card = j)).card :=
    Finset.card_eq_sum_card_fiberwise (f := Finset.card) (t := Finset.range (k + 1))
      (by
        intro J hJ
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hJ ⊢
        omega)
  rw [h1, hstep]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  have hjle : j ≤ k := by
    rw [Finset.mem_range] at hj
    omega
  have hfib :
      (((univ : Finset (Finset (Fin n))).filter (fun J => J.card ≤ k)).filter
          (fun J => J.card = j)) = (Finset.univ : Finset (Fin n)).powersetCard j := by
    ext J
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.mem_univ, true_and,
      Finset.subset_univ]
    omega
  rw [hfib, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]


/-! ### The column count is `2^{o(n)}` -/

/-- `C(n, j) ≤ C(n, k)` for `j ≤ k ≤ n/2`: the binomial coefficients increase up to the
middle. -/
theorem choose_mono_lower {n j k : ℕ} (hjk : j ≤ k) (hk : k ≤ n / 2) :
    n.choose j ≤ n.choose k := by
  suffices h : ∀ d, j + d ≤ n / 2 → n.choose j ≤ n.choose (j + d) from by
    have h' := h (k - j) (by omega)
    rwa [Nat.add_sub_cancel' hjk] at h'
  intro d
  induction d with
  | zero => intro _; exact le_rfl
  | succ d ih =>
      intro hd
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- `j! ≥ (j/e)^j`, from the exponential series (`e^j = ∑ j^i/i! ≥ j^j/j!`). -/
theorem factorial_ge_pow_div_exp (j : ℕ) :
    (j : ℝ) ^ j / Real.exp (j : ℝ) ≤ (j.factorial : ℝ) := by
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
  have h := Real.pow_div_factorial_le_exp (x := (j : ℝ)) hj0 j
  have hf : (0 : ℝ) < (j.factorial : ℝ) := by positivity
  rw [div_le_iff₀ hf] at h
  rw [div_le_iff₀ (Real.exp_pos _)]
  simpa [mul_comm] using h

/-- `C(n, j) ≤ (e·n/j)^j` for `j ≥ 1`. -/
theorem choose_le_exp_bound {n j : ℕ} (hj : 1 ≤ j) :
    (n.choose j : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (j : ℝ)) ^ j := by
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hden : (0 : ℝ) < (j : ℝ) ^ j / Real.exp (j : ℝ) := by positivity
  have h2 : (n : ℝ) ^ j / (j.factorial : ℝ) ≤ (n : ℝ) ^ j / ((j : ℝ) ^ j / Real.exp (j : ℝ)) :=
    div_le_div_of_nonneg_left (by positivity) hden (factorial_ge_pow_div_exp j)
  have h3 : (n : ℝ) ^ j / ((j : ℝ) ^ j / Real.exp (j : ℝ)) =
      (Real.exp 1 * (n : ℝ) / (j : ℝ)) ^ j := by
    have hexp : (Real.exp 1) ^ j = Real.exp (j : ℝ) := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [div_pow, mul_pow, hexp]
    field_simp
  exact (Nat.choose_le_pow_div j n).trans (h2.trans (le_of_eq h3))

/-- The number of columns of `D_{n,k}` is at most `(k+1)·(e·n/k)^k`. -/
theorem mDk_le_exp (n k : ℕ) (hk : 1 ≤ k) (hk2 : 2 * k ≤ n) :
    (mDk n k : ℝ) ≤ (k + 1) * (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
  rw [mDk, card_ColIdx]
  have hsum : ((∑ j ∈ Finset.range (k + 1), n.choose j : ℕ) : ℝ)
      = ∑ j ∈ Finset.range (k + 1), (n.choose j : ℝ) := by push_cast; ring
  rw [hsum]
  have hterm : ∀ j ∈ Finset.range (k + 1),
      (n.choose j : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
    intro j hj
    have hjle : j ≤ k := by simpa using hj
    have hjk : n.choose j ≤ n.choose k := choose_mono_lower hjle (by omega)
    have h1 : (n.choose j : ℝ) ≤ (n.choose k : ℝ) := by exact_mod_cast hjk
    exact h1.trans (choose_le_exp_bound (by omega))
  calc ∑ j ∈ Finset.range (k + 1), (n.choose j : ℝ)
      ≤ ∑ _j ∈ Finset.range (k + 1), (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k :=
        Finset.sum_le_sum hterm
    _ = (k + 1) * (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- `(18e)^5 ≤ 2^36`, the numerical fact behind `mDk ≤ 2^{9n/10}`. -/
theorem eighteen_exp_pow_five_le : (18 * Real.exp 1 : ℝ) ^ 5 ≤ (2 : ℝ) ^ 36 := by
  have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have h2 : 18 * Real.exp 1 < 50 := by nlinarith
  have h3 : (0 : ℝ) ≤ 18 * Real.exp 1 := by positivity
  have h4 : (18 * Real.exp 1) ^ 5 < (50 : ℝ) ^ 5 :=
    pow_lt_pow_left₀ h2 h3 (by norm_num : (5 : ℕ) ≠ 0)
  norm_num at h4 ⊢
  linarith

/-- `(18e)^{5}` in `rpow` form. -/
theorem eighteen_exp_rpow_five_le : (18 * Real.exp 1 : ℝ) ^ (5 : ℝ) ≤ (2 : ℝ) ^ (36 : ℝ) := by
  rw [show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num,
    show (36 : ℝ) = ((36 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
  exact eighteen_exp_pow_five_le

/-- `(18e)^{n/8} ≤ 2^{9n/10}`. -/
theorem eighteen_exp_rpow_le {n : ℕ} :
    (18 * Real.exp 1 : ℝ) ^ ((n : ℝ) / 8) ≤ (2 : ℝ) ^ (9 * (n : ℝ) / 10) := by
  have hx : (0 : ℝ) ≤ 18 * Real.exp 1 := by positivity
  have hx1 : (1 : ℝ) ≤ 18 * Real.exp 1 := by
    nlinarith [Real.exp_one_gt_d9]
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  rw [← Real.rpow_le_rpow_iff (Real.rpow_nonneg hx _) (Real.rpow_nonneg h2 _)
    (by norm_num : (0 : ℝ) < 40)]
  have e1 : ((18 * Real.exp 1 : ℝ) ^ ((n : ℝ) / 8)) ^ (40 : ℝ) =
      ((18 * Real.exp 1 : ℝ) ^ (5 : ℝ)) ^ (n : ℝ) := by
    rw [show ((18 * Real.exp 1 : ℝ) ^ ((n : ℝ) / 8)) ^ (40 : ℝ)
        = (18 * Real.exp 1 : ℝ) ^ (((n : ℝ) / 8) * 40) from (Real.rpow_mul hx _ _).symm,
      show ((18 * Real.exp 1 : ℝ) ^ (5 : ℝ)) ^ (n : ℝ)
        = (18 * Real.exp 1 : ℝ) ^ ((5 : ℝ) * (n : ℝ)) from (Real.rpow_mul hx _ _).symm,
      show ((n : ℝ) / 8) * 40 = (5 : ℝ) * (n : ℝ) by ring]
  have e2 : ((2 : ℝ) ^ (9 * (n : ℝ) / 10)) ^ (40 : ℝ) =
      ((2 : ℝ) ^ (36 : ℝ)) ^ (n : ℝ) := by
    rw [show ((2 : ℝ) ^ (9 * (n : ℝ) / 10)) ^ (40 : ℝ)
        = (2 : ℝ) ^ ((9 * (n : ℝ) / 10) * 40) from (Real.rpow_mul h2 _ _).symm,
      show ((2 : ℝ) ^ (36 : ℝ)) ^ (n : ℝ)
        = (2 : ℝ) ^ ((36 : ℝ) * (n : ℝ)) from (Real.rpow_mul h2 _ _).symm,
      show (9 * (n : ℝ) / 10) * 40 = (36 : ℝ) * (n : ℝ) by ring]
  rw [e1, e2]
  exact Real.rpow_le_rpow (Real.rpow_nonneg hx 5) eighteen_exp_rpow_five_le (by positivity)

/-- `mDk n k ≤ 2^{9n/10}`: the submatrix `D_{n,k}` has `2^{o(n)}` columns. -/
theorem mDk_le_two_pow {n k : ℕ} (hk : 1 ≤ k) (h8k : 8 * k ≤ n) (h9k : n ≤ 9 * k) :
    (mDk n k : ℝ) ≤ (2 : ℝ) ^ (9 * (n : ℝ) / 10) := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hnk : (n : ℝ) / (k : ℝ) ≤ 9 := by
    rw [div_le_iff₀ hkpos]
    have h : (n : ℝ) ≤ 9 * (k : ℝ) := by exact_mod_cast h9k
    linarith
  have hbase : Real.exp 1 * (n : ℝ) / (k : ℝ) ≤ 9 * Real.exp 1 := by
    have := mul_le_mul_of_nonneg_left hnk (Real.exp_pos 1).le
    calc Real.exp 1 * (n : ℝ) / (k : ℝ) = Real.exp 1 * ((n : ℝ) / (k : ℝ)) := by ring
      _ ≤ Real.exp 1 * 9 := this
      _ = 9 * Real.exp 1 := by ring
  have hk1 : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
    have h : k + 1 ≤ 2 ^ k := Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := k))
    have h' : ((k + 1 : ℕ) : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    exact h'
  have hpow : (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k ≤ (9 * Real.exp 1) ^ k :=
    pow_le_pow_left₀ (by positivity) hbase k
  calc (mDk n k : ℝ) ≤ (k + 1) * (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k :=
        mDk_le_exp n k hk (by omega)
    _ ≤ (2 : ℝ) ^ k * (9 * Real.exp 1) ^ k := by
        have h1 : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := hk1
        have h2 := hpow
        gcongr
    _ = (18 * Real.exp 1 : ℝ) ^ k := by
        rw [← mul_pow]
        ring_nf
    _ = (18 * Real.exp 1 : ℝ) ^ ((k : ℝ)) := by rw [Real.rpow_natCast]
    _ ≤ (18 * Real.exp 1 : ℝ) ^ ((n : ℝ) / 8) := by
        refine Real.rpow_le_rpow_of_exponent_le (by nlinarith [Real.exp_one_gt_d9]) ?_
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
        have h : (8 * k : ℝ) ≤ (n : ℝ) := by exact_mod_cast h8k
        nlinarith
    _ ≤ (2 : ℝ) ^ (9 * (n : ℝ) / 10) := eighteen_exp_rpow_le

/-! ### Numerical ingredients -/

/-- `mDk n k ≤ 2^n - 1`: the submatrix has fewer columns than the full matrix has rows. -/
theorem mDk_le_two_pow_sub_one {n k : ℕ} (_hk : 1 ≤ k) (hkn : k < n) :
    mDk n k ≤ 2 ^ n - 1 := by
  rw [mDk, card_ColIdx]
  have hsplit : ∑ j ∈ Finset.range (n + 1), n.choose j
      = (∑ j ∈ Finset.range (k + 1), n.choose j) + ∑ j ∈ Finset.Ico (k + 1) (n + 1), n.choose j :=
    (Finset.sum_range_add_sum_Ico (fun j => n.choose j) (by omega)).symm
  have htot : ∑ j ∈ Finset.range (n + 1), n.choose j = 2 ^ n := Nat.sum_range_choose n
  have hpos : 1 ≤ ∑ j ∈ Finset.Ico (k + 1) (n + 1), n.choose j := by
    have hmem : k + 1 ∈ Finset.Ico (k + 1) (n + 1) := by
      simp only [Finset.mem_Ico]; omega
    have h1 : n.choose (k + 1) ≤ ∑ j ∈ Finset.Ico (k + 1) (n + 1), n.choose j :=
      Finset.single_le_sum (f := fun j => n.choose j) (fun _ _ => Nat.zero_le _) hmem
    have h2 : 0 < n.choose (k + 1) := Nat.choose_pos (by omega)
    omega
  omega

/-- `√n ≥ 31` for `n ≥ 961`. -/
theorem sqrt_ge_thirty_one {n : ℕ} (hn : 961 ≤ n) : (31 : ℝ) ≤ Real.sqrt n := by
  rw [show (31 : ℝ) = Real.sqrt ((31 : ℝ) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by exact_mod_cast hn)

/-- `n/8 ≥ n/16` as real numbers, for `n ≥ 14`. -/
theorem div_eight_ge_sixteenth {n : ℕ} (hn : 14 ≤ n) : (n : ℝ) / 16 ≤ ((n / 8 : ℕ) : ℝ) := by
  have h1 : n ≤ 8 * (n / 8) + 7 := by
    have h2 := Nat.div_add_mod n 8
    have h3 := Nat.mod_lt n (by norm_num : 0 < 8)
    omega
  have h2 : (n : ℝ) ≤ 8 * ((n / 8 : ℕ) : ℝ) + 7 := by exact_mod_cast h1
  have hnR : (14 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

/-- `x^{5/2} = x^2·√x`. -/
theorem rpow_five_halves_eq (x : ℝ) (hx : 0 < x) : x ^ (5 / 2 : ℝ) = x ^ 2 * Real.sqrt x := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_add hx]
  norm_num

/-- `x^{5/2} = x^{3/2}·x`. -/
theorem rpow_five_halves_eq' (x : ℝ) (hx : 0 < x) :
    x ^ (5 / 2 : ℝ) = x ^ (3 / 2 : ℝ) * x := by
  rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.rpow_add hx, Real.rpow_one]

/-- `16^{5/2} = 1024`. -/
theorem sixteen_rpow : (16 : ℝ) ^ (5 / 2 : ℝ) = 1024 := by
  rw [show (5 / 2 : ℝ) = ((5 : ℕ) : ℝ) * (1 / 2) by norm_num,
    Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 16), Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  rw [show (16 : ℝ) ^ 5 = (1024 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- `(n/8)^{5/2} ≥ n^{5/2}/1024`, for `n ≥ 14`. -/
theorem k_rpow_ge {n : ℕ} (hn : 14 ≤ n) :
    (n : ℝ) ^ (5 / 2 : ℝ) / 1024 ≤ (((n / 8 : ℕ) : ℝ)) ^ (5 / 2 : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hk0 : (0 : ℝ) < ((n / 8 : ℕ) : ℝ) := by
    have : 0 < n / 8 := by omega
    exact_mod_cast this
  have hk : (n : ℝ) / 16 ≤ ((n / 8 : ℕ) : ℝ) := div_eight_ge_sixteenth hn
  have h1 : ((n : ℝ) / 16) ^ 2 ≤ (((n / 8 : ℕ) : ℝ)) ^ 2 := by nlinarith
  have h3 : Real.sqrt ((n : ℝ) / 16) ≤ Real.sqrt (((n / 8 : ℕ) : ℝ)) := Real.sqrt_le_sqrt hk
  have h4 : Real.sqrt ((n : ℝ) / 16) = Real.sqrt (n : ℝ) / 4 := by
    rw [Real.sqrt_div hn0.le, show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4] at h3
  have h5 : ((n : ℝ) / 16) ^ 2 = (n : ℝ) ^ 2 / 256 := by ring
  rw [rpow_five_halves_eq _ hn0, rpow_five_halves_eq _ hk0]
  have h6 : (n : ℝ) ^ 2 / 256 * (Real.sqrt (n : ℝ) / 4)
      ≤ (((n / 8 : ℕ) : ℝ)) ^ 2 * Real.sqrt (((n / 8 : ℕ) : ℝ)) := by
    refine mul_le_mul ?_ h3 (by positivity) (by positivity)
    rw [← h5]
    exact h1
  have h7 : (n : ℝ) ^ 2 * Real.sqrt (n : ℝ) / 1024
      = (n : ℝ) ^ 2 / 256 * (Real.sqrt (n : ℝ) / 4) := by ring
  linarith [h6, h7]

/-- `μ_{n,k} > k^{5/2}/(5n)`, and `μ_{n,k} - 2 ≥ k^{5/2}/(10n)` when `k^{5/2}/(5n) ≥ 4`. -/
theorem mu_sub_two_ge {n k : ℕ} (hk : k < n)
    (hA : 4 ≤ (k : ℝ) ^ (5 / 2 : ℝ) / (5 * (n : ℝ))) :
    (k : ℝ) ^ (5 / 2 : ℝ) / (10 * (n : ℝ)) ≤ ((mu n k - 2 : ℕ) : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hmu := lemma5 hk
  have hmu4 : (4 : ℝ) < (mu n k : ℝ) := lt_of_le_of_lt hA hmu
  have hmu5 : 5 ≤ mu n k := by
    have : (4 : ℕ) < mu n k := by exact_mod_cast hmu4
    omega
  have hcast : ((mu n k - 2 : ℕ) : ℝ) = (mu n k : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ mu n k)]
    norm_num
  rw [hcast]
  have hhalf : (k : ℝ) ^ (5 / 2 : ℝ) / (10 * (n : ℝ))
      = (k : ℝ) ^ (5 / 2 : ℝ) / (5 * (n : ℝ)) / 2 := by
    field_simp
    ring
  rw [hhalf]
  linarith

/-- `μ_{n, n/8} - 2 ≥ n^{3/2}/10240` for `n ≥ 1000`. -/
theorem mu_sub_two_ge_n {n : ℕ} (hn : 1000 ≤ n) :
    (n : ℝ) ^ (3 / 2 : ℝ) / 10240 ≤ ((mu n (n / 8) - 2 : ℕ) : ℝ) := by
  have hn14 : 14 ≤ n := by omega
  have hkr := k_rpow_ge hn14
  have hnR : (1000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn8 : (0 : ℝ) < ((n / 8 : ℕ) : ℝ) := by
    have : 0 < n / 8 := by omega
    exact_mod_cast this
  have hsqrt : (31 : ℝ) ≤ Real.sqrt (n : ℝ) := sqrt_ge_thirty_one (by omega)
  have h32 : (20480 : ℝ) ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hn0, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    have hmul : (1000 : ℝ) * 31 ≤ (n : ℝ) * Real.sqrt (n : ℝ) :=
      mul_le_mul hnR hsqrt (by norm_num) (by positivity)
    nlinarith [hmul]
  have hA4 : 4 ≤ (((n / 8 : ℕ) : ℝ)) ^ (5 / 2 : ℝ) / (5 * (n : ℝ)) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 5 * (n : ℝ))]
    have h5 : (n : ℝ) ^ (5 / 2 : ℝ) = (n : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) :=
      rpow_five_halves_eq' _ hn0
    have hle : (20 : ℝ) * (n : ℝ) ≤ (((n / 8 : ℕ) : ℝ)) ^ (5 / 2 : ℝ) := by
      have h1 : (n : ℝ) ^ (5 / 2 : ℝ) / 1024 ≤ (((n / 8 : ℕ) : ℝ)) ^ (5 / 2 : ℝ) := hkr
      rw [h5] at h1
      have h2 : (20 : ℝ) * (n : ℝ) ≤ ((n : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ)) / 1024 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1024)]
        nlinarith
      linarith
    nlinarith
  have hmain := mu_sub_two_ge (k := n / 8) (by omega) hA4
  have h10 : (n : ℝ) ^ (3 / 2 : ℝ) / 10240
      ≤ (((n / 8 : ℕ) : ℝ)) ^ (5 / 2 : ℝ) / (10 * (n : ℝ)) := by
    have h5 : (n : ℝ) ^ (5 / 2 : ℝ) = (n : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) :=
      rpow_five_halves_eq' _ hn0
    calc (n : ℝ) ^ (3 / 2 : ℝ) / 10240
        = ((n : ℝ) ^ (5 / 2 : ℝ) / 1024) / (10 * (n : ℝ)) := by
          rw [h5]; field_simp; ring
      _ ≤ (((n / 8 : ℕ) : ℝ)) ^ (5 / 2 : ℝ) / (10 * (n : ℝ)) :=
          div_le_div_of_nonneg_right hkr (by positivity)
  linarith

/-! ## The transpose of `D_{n,k}` as a submatrix of `D_n` -/

theorem chainComplexity_submatrix_le_rows {k k' m : ℕ}
    (A : Matrix (Fin k) (Fin m) (ZMod 2)) (g : Fin k' → Fin k) :
    chainComplexity (fun i j => A (g i) j) ≤ chainComplexity A := by
  rw [chainComplexity_eq_sInf]
  refine le_sInf_of_forall ?_ ?_
  · intro hs
    exact absurd hs (Set.nonempty_iff_ne_empty.mp (chainSet_nonempty A))
  · rintro l ⟨c, hL, hc⟩
    exact Nat.sInf_le ⟨c, hL, fun i => hc (g i)⟩

/-- The map from the columns of `D_{n,k}` to the rows/columns of `D_n` exhibiting `D_{n,k}ᵀ`
as a row-submatrix of `D_n`. -/
noncomputable def colRowEmb (n k : ℕ) : Fin (mDk n k) → Fin (2 ^ n) :=
  fun t => setEquiv n ((colEquiv n k).symm t).1

theorem DkMat_transpose_eq (n k : ℕ) :
    (fun i j => Dmat n (colRowEmb n k i) j) = Matrix.transpose (DkMat n k) := by
  funext i j
  rw [Matrix.transpose_apply, DkMat_apply, Dmat_apply, colRowEmb]
  simp only [Equiv.symm_apply_apply]
  exact D.comm _ _

/-- `D_{n,k}ᵀ` is a row-submatrix of `D_n`, so its complexity is no larger. -/
theorem chainComplexity_DkMat_transpose_le (n k : ℕ) :
    chainComplexity (Matrix.transpose (DkMat n k)) ≤ chainComplexity (Dmat n) := by
  have h := chainComplexity_submatrix_le_rows (Dmat n) (colRowEmb n k)
  rwa [DkMat_transpose_eq] at h

/-- Claim 1 (transposition) for the submatrix `D_{n,k}`. -/
theorem DkMat_claim1 (n k : ℕ) :
    chainComplexity (DkMat n k) + 2 ^ n =
      chainComplexity (Matrix.transpose (DkMat n k)) + mDk n k := by
  refine claim1 (DkMat n k) ?_ ?_
  · intro i
    refine ⟨colEquiv n k ⟨∅, by simp⟩, ?_⟩
    rw [DkMat_apply, DkRow_apply]
    simp
  · intro j
    refine ⟨setEquiv n ∅, ?_⟩
    simp only [DkMat, Equiv.symm_apply_apply]
    rw [D.apply_of_disjoint (Finset.disjoint_empty_left _)]
    exact one_ne_zero

/-! ## Theorem 2 applied to `D_{n,k}` -/

theorem exists_chain_of_chainComplexity {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    ∃ c : VecAddChain n, c.L = chainComplexity A ∧ c.Computes A := by
  have hne : (ChainSet A).Nonempty := chainSet_nonempty A
  have hmem : sInf (ChainSet A) ∈ ChainSet A := Nat.sInf_mem hne
  simpa [chainComplexity, ChainSet] using hmem

theorem zero_notMem_DkRowSetP {n k : ℕ} (hk1 : 1 ≤ k) :
    (0 : BVec (mDk n k)) ∉ DkRowSetP n k := by
  intro h0
  obtain ⟨I, hI, h⟩ := mem_DkRowSetP.mp h0
  have h2 := two_le_weight_DkRow hk1 hI
  rw [h] at h2
  simp [weight] at h2

/-- **Claim 6 estimate for `D_{n,k}`.**  Theorem 2 gives
`|B| + ((2K-2)/(2K+1))·|B|^(K/(K+1)) - m ≤ L(D_{n,k})`, where `B` is the row set of `D_{n,k}`
with the all-ones... (the full row `[n]`) removed and `m = mDk n k` is the number of columns. -/
theorem DkMat_bound {n k K : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) (hK : 2 ≤ K)
    (hmu : 2 * K + 2 ≤ mu n k - 2) :
    ((DkRowSetP n k).card : ℝ) +
        ((2 * (K : ℝ) - 2) / (2 * (K : ℝ) + 1)) *
          ((DkRowSetP n k).card : ℝ) ^ ((K : ℝ) / ((K : ℝ) + 1)) -
        (mDk n k : ℝ) ≤ (chainComplexity (DkMat n k) : ℝ) := by
  classical
  obtain ⟨c₀, hc₀L, hc₀⟩ := exists_chain_of_chainComplexity (DkMat n k)
  have hcomp : (ExtChain.ofChain c₀ ∅).ComputesVecs (DkRowSetP n k) := by
    intro b hb
    obtain ⟨I, hI, rfl⟩ := mem_DkRowSetP.mp hb
    refine ⟨?_, ?_⟩
    · show proj (∅ : Finset (Fin (mDk n k))) (DkRow n k I) = 0
      funext i; simp [proj]
    · have h := hc₀ (setEquiv n I)
      rw [DkMat_row n k I] at h
      simp only [ExtChain.ofChain, Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at h ⊢
      tauto
  have hweight : ∀ b : Row (DkRowSetP n k),
      weight (Finset.univ : Finset (Fin (mDk n k))) b.1 ≠ 1 := by
    rintro ⟨b, hb⟩
    obtain ⟨I, hI, h⟩ := mem_DkRowSetP.mp hb
    change weight (Finset.univ : Finset (Fin (mDk n k))) b ≠ 1
    rw [← h]
    exact weight_DkRow_ne_one hk1 hI
  have hdeg : 2 * K + 2 ≤
      MooreBound.ind (C0 (ExtChain.ofChain c₀ ∅).aux false (DkRowSetP n k)) := by
    have haux : (ExtChain.ofChain c₀ ∅).aux = (∅ : Finset (Fin (mDk n k))) := rfl
    rw [haux]
    have hC0 : C0 (∅ : Finset (Fin (mDk n k))) false (DkRowSetP n k) = DkRowSetP n k := by
      simp [C0]
    rw [hC0]
    exact le_trans hmu (ind_DkRowSetP hk1 hkn)
  have hmB : mDk n k ≤ (DkRowSetP n k).card := by
    rw [card_DkRowSetP hk1]
    exact mDk_le_two_pow_sub_one hk1 hkn
  have hmain := theorem2 (ExtChain.ofChain c₀ ∅) (DkRowSetP n k) false hcomp hweight hK hdeg hmB
  have hslack : (((inputSlack (ExtChain.ofChain c₀ ∅).aux false : ℕ)) : ℝ) = (mDk n k : ℝ) := by
    simp [inputSlack]
  have hcred : (((ExtChain.ofChain c₀ ∅).reducedComplexity : ℕ) : ℝ) =
      (chainComplexity (DkMat n k) : ℝ) := by
    rw [ExtChain.reducedComplexity_aux_empty c₀, hc₀L]
  rw [hslack, hcred] at hmain
  exact hmain

/-! ## The bound `L(D_n) ≥ (3-o(1))·2^n` -/

theorem Dmat_lower_bound {n k K : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) (hK : 2 ≤ K)
    (hmu : 2 * K + 2 ≤ mu n k - 2) :
    ((2 : ℝ) ^ n - 1) +
        ((2 * (K : ℝ) - 2) / (2 * (K : ℝ) + 1)) *
          ((2 : ℝ) ^ n - 1) ^ ((K : ℝ) / ((K : ℝ) + 1)) +
        (2 : ℝ) ^ n - 2 * (mDk n k : ℝ) ≤ (chainComplexity (Dmat n) : ℝ) := by
  classical
  have hcard : ((DkRowSetP n k).card : ℝ) = (2 : ℝ) ^ n - 1 := by
    rw [card_DkRowSetP hk1]
    have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_two_pow
    rw [Nat.cast_sub h1]
    push_cast
    ring
  have hmain := DkMat_bound hk1 hkn hK hmu
  rw [hcard] at hmain
  have hclaimR : (chainComplexity (DkMat n k) : ℝ) + (2 : ℝ) ^ n =
      (chainComplexity (Matrix.transpose (DkMat n k)) : ℝ) + (mDk n k : ℝ) := by
    exact_mod_cast DkMat_claim1 n k
  have hsubR : (chainComplexity (Matrix.transpose (DkMat n k)) : ℝ) ≤
      (chainComplexity (Dmat n) : ℝ) := by
    exact_mod_cast chainComplexity_DkMat_transpose_le n k
  nlinarith [hmain, hclaimR, hsubR]

/-! ### The numerical core -/

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

/-- Numerical core of Corollary 6.  If
`X + ((2K-2)/(2K+1))·X^(K/(K+1)) + M - 2m ≤ L`, `X = M - 1`, `log X ≤ n`,
`(n+3)/K ≤ ε/6`, `m ≤ (ε/3)M` and `2 ≤ (ε/6)M`, then `(3-ε)M ≤ L`. -/
theorem arith_c6 {n K : ℕ} {m X M L ε : ℝ}
    (hε : 0 < ε) (hK : 3 ≤ K)
    (hXpos : 0 < X) (hXeq : X = M - 1) (hlogX : Real.log X ≤ (n : ℝ))
    (hKeps : ((n : ℝ) + 3) / (K : ℝ) ≤ ε / 6)
    (hmain : X + ((2 * (K : ℝ) - 2) / (2 * (K : ℝ) + 1)) *
        X ^ ((K : ℝ) / ((K : ℝ) + 1)) + M - 2 * m ≤ L)
    (hmeps : m ≤ (ε / 3) * M) (hbigM : 2 ≤ (ε / 6) * M) :
    (3 - ε) * M ≤ L := by
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hcoef_eq : (2 * (K : ℝ) - 2) / (2 * (K : ℝ) + 1) = 1 - 3 / (2 * (K : ℝ) + 1) := by
    field_simp
    ring
  have hcoef : 1 - 3 / (K : ℝ) ≤ (2 * (K : ℝ) - 2) / (2 * (K : ℝ) + 1) := by
    rw [hcoef_eq]
    have h3 : 3 / (2 * (K : ℝ) + 1) ≤ 3 / (K : ℝ) := by
      exact div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 3) hKpos (by linarith)
    linarith
  have hcoef_nonneg : 0 ≤ 1 - 3 / (K : ℝ) := by
    have h : 3 / (K : ℝ) ≤ 1 := by
      rw [div_le_one hKpos]
      exact_mod_cast (by omega : 3 ≤ K)
    linarith
  have hinv : (1 : ℝ) / ((K : ℝ) + 1) ≤ ((K : ℝ))⁻¹ := by
    rw [one_div]
    exact inv_anti₀ hKpos (by linarith)
  have hrlog : (1 / ((K : ℝ) + 1)) * Real.log X ≤ (n : ℝ) / (K : ℝ) := by
    have h2 : (1 / ((K : ℝ) + 1)) * Real.log X ≤ (1 / ((K : ℝ) + 1)) * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hlogX (by positivity)
    have h3 : (1 / ((K : ℝ) + 1)) * (n : ℝ) ≤ (n : ℝ) / (K : ℝ) := by
      rw [div_eq_mul_inv]
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      calc (1 / ((K : ℝ) + 1)) * (n : ℝ) = (n : ℝ) * (1 / ((K : ℝ) + 1)) := by ring
        _ ≤ (n : ℝ) * (K : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hinv hn0
    linarith
  have hXe : X * (1 - (n : ℝ) / (K : ℝ)) ≤ X ^ ((K : ℝ) / ((K : ℝ) + 1)) := by
    have hexp : (K : ℝ) / ((K : ℝ) + 1) = 1 - 1 / ((K : ℝ) + 1) := by
      field_simp
      ring
    rw [hexp]
    have h1 := rpow_one_sub_ge (x := X) (r := 1 / ((K : ℝ) + 1)) hXpos
    have h4 : X * (1 - (n : ℝ) / (K : ℝ)) ≤ X * (1 - (1 / ((K : ℝ) + 1)) * Real.log X) := by
      nlinarith [hXpos.le, hrlog]
    linarith
  have hXe_nonneg : 0 ≤ X ^ ((K : ℝ) / ((K : ℝ) + 1)) := Real.rpow_nonneg hXpos.le _
  have hprod : X * (1 - ((n : ℝ) + 3) / (K : ℝ)) ≤
      ((2 * (K : ℝ) - 2) / (2 * (K : ℝ) + 1)) * X ^ ((K : ℝ) / ((K : ℝ) + 1)) := by
    have halg : (1 - 3 / (K : ℝ)) * (1 - (n : ℝ) / (K : ℝ)) =
        (1 - ((n : ℝ) + 3) / (K : ℝ)) + 3 * (n : ℝ) / (K : ℝ) ^ 2 := by
      field_simp
      ring
    have hnn : 0 ≤ 3 * (n : ℝ) / (K : ℝ) ^ 2 := by positivity
    have hkey : (1 - ((n : ℝ) + 3) / (K : ℝ)) ≤
        (1 - 3 / (K : ℝ)) * (1 - (n : ℝ) / (K : ℝ)) := by
      nlinarith [halg, hnn]
    calc X * (1 - ((n : ℝ) + 3) / (K : ℝ))
        ≤ X * ((1 - 3 / (K : ℝ)) * (1 - (n : ℝ) / (K : ℝ))) := by
          nlinarith [hXpos.le, hkey]
      _ = (1 - 3 / (K : ℝ)) * (X * (1 - (n : ℝ) / (K : ℝ))) := by ring
      _ ≤ (1 - 3 / (K : ℝ)) * X ^ ((K : ℝ) / ((K : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hXe hcoef_nonneg
      _ ≤ ((2 * (K : ℝ) - 2) / (2 * (K : ℝ) + 1)) * X ^ ((K : ℝ) / ((K : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hcoef hXe_nonneg
  have hstep : X * (1 - ε / 6) ≤
      ((2 * (K : ℝ) - 2) / (2 * (K : ℝ) + 1)) * X ^ ((K : ℝ) / ((K : ℝ) + 1)) := by
    have h1 : 1 - ε / 6 ≤ 1 - ((n : ℝ) + 3) / (K : ℝ) := by linarith [hKeps]
    calc X * (1 - ε / 6) ≤ X * (1 - ((n : ℝ) + 3) / (K : ℝ)) := by
          nlinarith [hXpos.le]
      _ ≤ _ := hprod
  have h2m : 2 * m ≤ (2 * ε / 3) * M := by nlinarith [hmeps]
  nlinarith [hmain, hstep, hbigM, h2m, hXeq]

/-! ### Choosing the parameters `k = n/8` and `K` -/

/-- At `k = ⌊n/8⌋` the number of columns of `D_{n,k}` is at most `2^(9n/10)`. -/
theorem mDk_eighth_le {n : ℕ} (hn : 1000 ≤ n) :
    (mDk n (n / 8) : ℝ) ≤ (2 : ℝ) ^ (9 * (n : ℝ) / 10) := by
  refine mDk_le_two_pow (k := n / 8) ?_ ?_ ?_
  · omega
  · have h : n / 8 * 8 ≤ n := Nat.div_mul_le_self n 8
    omega
  · have hmod : n % 8 ≤ 7 := by
      have := Nat.mod_lt n (by norm_num : 0 < 8)
      omega
    have hdm : 8 * (n / 8) + n % 8 = n := Nat.div_add_mod n 8
    have h7 : 7 ≤ n / 8 := by omega
    omega

/-- `n^(3/2) ≥ 122880` for `n ≥ 4096`. -/
theorem pow_three_halves_ge {n : ℕ} (hn : 4096 ≤ n) :
    (122880 : ℝ) ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have h4096 : (4096 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsqrt : (64 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have h := Real.sqrt_le_sqrt h4096
    have h64 : Real.sqrt (4096 : ℝ) = 64 := by
      rw [show (4096 : ℝ) = 64 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rwa [h64] at h
  have hsplit : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * Real.sqrt (n : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hnpos, Real.rpow_one,
      Real.sqrt_eq_rpow]
  rw [hsplit]
  nlinarith

/-- The parameter `K` fed to Theorem 2: half of `μ_{n,⌊n/8⌋} - 4`. -/
noncomputable def Kc6 (n : ℕ) : ℕ := (mu n (n / 8) - 4) / 2

theorem Kc6_spec {n : ℕ} (h : 3 ≤ Kc6 n) : 2 * Kc6 n + 2 ≤ mu n (n / 8) - 2 := by
  have hdiv : (mu n (n / 8) - 4) / 2 * 2 ≤ mu n (n / 8) - 4 :=
    Nat.div_mul_le_self (mu n (n / 8) - 4) 2
  have h6 : 6 ≤ mu n (n / 8) - 4 := by
    have h3 := (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).1 h
    omega
  simp only [Kc6] at hdiv ⊢
  omega

theorem Kc6_lower {n : ℕ} (hn : 4096 ≤ n) :
    (n : ℝ) ^ (3 / 2 : ℝ) / 40960 ≤ (Kc6 n : ℝ) := by
  have hn1000 : 1000 ≤ n := by omega
  have hmu := mu_sub_two_ge_n hn1000
  have hgt := pow_three_halves_ge hn
  have hdiv : 2 * ((mu n (n / 8) - 4) / 2) + (mu n (n / 8) - 4) % 2 = mu n (n / 8) - 4 :=
    Nat.div_add_mod (mu n (n / 8) - 4) 2
  have hmod : (mu n (n / 8) - 4) % 2 ≤ 1 := by
    have := Nat.mod_lt (mu n (n / 8) - 4) (by norm_num : 0 < 2)
    omega
  have hlow : mu n (n / 8) - 5 ≤ 2 * Kc6 n := by
    simp only [Kc6]
    omega
  have hcast : ((mu n (n / 8) - 5 : ℕ) : ℝ) ≤ 2 * (Kc6 n : ℝ) := by
    exact_mod_cast hlow
  have hmuR : (n : ℝ) ^ (3 / 2 : ℝ) / 10240 ≤ ((mu n (n / 8) : ℕ) : ℝ) := by
    have h6 : ((mu n (n / 8) - 2 : ℕ) : ℝ) ≤ ((mu n (n / 8) : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le (mu n (n / 8)) 2
    linarith
  have h5le : 5 ≤ mu n (n / 8) := by
    have h12 : (12 : ℝ) ≤ ((mu n (n / 8) : ℕ) : ℝ) := by linarith
    have h5 : (5 : ℝ) ≤ ((mu n (n / 8) : ℕ) : ℝ) := by linarith
    exact_mod_cast h5
  have h5 : ((mu n (n / 8) : ℕ) : ℝ) - 5 ≤ ((mu n (n / 8) - 5 : ℕ) : ℝ) := by
    rw [Nat.cast_sub h5le]
    norm_num
  linarith

theorem Kc6_three {n : ℕ} (hn : 4096 ≤ n) : 3 ≤ Kc6 n := by
  have hlow := Kc6_lower hn
  have hgt := pow_three_halves_ge hn
  have h3 : (3 : ℝ) ≤ (Kc6 n : ℝ) := by
    have h : (3 : ℝ) ≤ (n : ℝ) ^ (3 / 2 : ℝ) / 40960 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 40960)]
      linarith
    linarith
  exact_mod_cast h3

/-- `(n+3)/K` is at most `ε/6` once `n` is large: `K ≳ n^(3/2)/40960`. -/
theorem Kc6_eps_bound {n : ℕ} {ε : ℝ} (hε : 0 < ε) (hn : 4096 ≤ n)
    (hsq : (491520 / ε) ^ 2 ≤ (n : ℝ)) :
    ((n : ℝ) + 3) / (Kc6 n : ℝ) ≤ ε / 6 := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hgt := pow_three_halves_ge hn
  have hK := Kc6_lower hn
  have hKpos : (0 : ℝ) < (Kc6 n : ℝ) := by
    have h : (0 : ℝ) < (n : ℝ) ^ (3 / 2 : ℝ) / 40960 := by positivity
    linarith
  have hsplit3 : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * Real.sqrt (n : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hnpos, Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hsqrt : 491520 / ε ≤ Real.sqrt (n : ℝ) := by
    have h1 : Real.sqrt ((491520 / ε) ^ 2) ≤ Real.sqrt (n : ℝ) := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 491520 / ε)] at h1
  have hstep1 : ((n : ℝ) + 3) / (Kc6 n : ℝ) ≤
      ((n : ℝ) + 3) / ((n : ℝ) ^ (3 / 2 : ℝ) / 40960) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hK
  have hstep2 : ((n : ℝ) + 3) / ((n : ℝ) ^ (3 / 2 : ℝ) / 40960) =
      40960 * ((n : ℝ) + 3) / ((n : ℝ) * Real.sqrt (n : ℝ)) := by
    rw [hsplit3]
    field_simp
  have hstep3 : 40960 * ((n : ℝ) + 3) / ((n : ℝ) * Real.sqrt (n : ℝ)) ≤
      81920 / Real.sqrt (n : ℝ) := by
    have h4096 : (4096 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnum : 40960 * ((n : ℝ) + 3) ≤ 81920 * (n : ℝ) := by nlinarith
    have hden : (0 : ℝ) < (n : ℝ) * Real.sqrt (n : ℝ) := by positivity
    have h1 : 40960 * ((n : ℝ) + 3) / ((n : ℝ) * Real.sqrt (n : ℝ)) ≤
        81920 * (n : ℝ) / ((n : ℝ) * Real.sqrt (n : ℝ)) :=
      div_le_div_of_nonneg_right hnum hden.le
    have h2 : 81920 * (n : ℝ) / ((n : ℝ) * Real.sqrt (n : ℝ)) = 81920 / Real.sqrt (n : ℝ) := by
      field_simp
    linarith [h1, h2]
  have hstep4 : 81920 / Real.sqrt (n : ℝ) ≤ 81920 / (491520 / ε) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hsqrt
  have hstep5 : 81920 / (491520 / ε) = ε / 6 := by
    field_simp
    ring
  linarith [hstep1, hstep2, hstep3, hstep4, hstep5]

/-- `2^(n/10) ≥ 3/ε` for large `n`. -/
theorem two_pow_tenth_ge {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hn : 10 * Real.log (3 / ε) / Real.log 2 + 10 ≤ (n : ℝ)) :
    (3 : ℝ) / ε ≤ (2 : ℝ) ^ ((n : ℝ) / 10) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h10 : 10 * (Real.log (3 / ε) / Real.log 2 + 1) ≤ (n : ℝ) := by
    have he : 10 * (Real.log (3 / ε) / Real.log 2 + 1) =
        10 * Real.log (3 / ε) / Real.log 2 + 10 := by ring
    linarith
  have hn10 : Real.log (3 / ε) / Real.log 2 + 1 ≤ (n : ℝ) / 10 :=
    (le_div_iff₀ (by norm_num : (0 : ℝ) < 10)).2 (by rwa [mul_comm] at h10)
  have h1 : Real.log (3 / ε) + Real.log 2 ≤ Real.log 2 * ((n : ℝ) / 10) := by
    have h := mul_le_mul_of_nonneg_right hn10 hlog2.le
    have he : (Real.log (3 / ε) / Real.log 2 + 1) * Real.log 2 =
        Real.log (3 / ε) + Real.log 2 := by
      field_simp
    rw [he] at h
    rwa [mul_comm ((n : ℝ) / 10) (Real.log 2)] at h
  have h2 : Real.exp (Real.log (3 / ε) + Real.log 2) ≤
      Real.exp (Real.log 2 * ((n : ℝ) / 10)) := Real.exp_le_exp.2 h1
  have h3 : Real.exp (Real.log (3 / ε) + Real.log 2) = (3 / ε) * 2 := by
    rw [Real.exp_add, Real.exp_log (by positivity), Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [h3] at h2
  have hexp : (2 : ℝ) ^ ((n : ℝ) / 10) = Real.exp (Real.log 2 * ((n : ℝ) / 10)) :=
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) _
  rw [hexp]
  have hpos : (0 : ℝ) < 3 / ε := by positivity
  nlinarith

/-- `2^n ≥ 12/ε` for large `n`, i.e. `2 ≤ (ε/6)·2^n`. -/
theorem two_pow_ge_inv {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hn : Real.log (12 / ε) / Real.log 2 ≤ (n : ℝ)) :
    2 ≤ (ε / 6) * (2 : ℝ) ^ n := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h1 : Real.log (12 / ε) ≤ Real.log 2 * (n : ℝ) := by
    have h := mul_le_mul_of_nonneg_right hn hlog2.le
    have he : (Real.log (12 / ε) / Real.log 2) * Real.log 2 = Real.log (12 / ε) := by
      field_simp
    rw [he] at h
    rwa [mul_comm ((n : ℝ)) (Real.log 2)] at h
  have h2 : Real.exp (Real.log (12 / ε)) ≤ Real.exp (Real.log 2 * (n : ℝ)) :=
    Real.exp_le_exp.2 h1
  rw [Real.exp_log (by positivity)] at h2
  have h3 : Real.exp (Real.log 2 * (n : ℝ)) = (2 : ℝ) ^ n := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [h3] at h2
  have h4 : (ε / 6) * (12 / ε) = 2 := by
    field_simp
    ring
  calc 2 = (ε / 6) * (12 / ε) := h4.symm
    _ ≤ (ε / 6) * (2 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- The column count at `k = ⌊n/8⌋` is at most `(ε/3)·2^n` once `n` is large. -/
theorem mDk_eps_bound {n : ℕ} {ε : ℝ} (hε : 0 < ε) (hn : 1000 ≤ n)
    (hpow : (3 : ℝ) / ε ≤ (2 : ℝ) ^ ((n : ℝ) / 10)) :
    (mDk n (n / 8) : ℝ) ≤ (ε / 3) * (2 : ℝ) ^ n := by
  have hm := mDk_eighth_le hn
  have hsplit : (2 : ℝ) ^ (9 * (n : ℝ) / 10) * (2 : ℝ) ^ ((n : ℝ) / 10) = (2 : ℝ) ^ n := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have he : 9 * (n : ℝ) / 10 + (n : ℝ) / 10 = (n : ℝ) := by ring
    rw [he, Real.rpow_natCast]
  have hden : (0 : ℝ) < (2 : ℝ) ^ ((n : ℝ) / 10) := Real.rpow_pos_of_pos (by norm_num) _
  have heq : (2 : ℝ) ^ (9 * (n : ℝ) / 10) = (2 : ℝ) ^ n / (2 : ℝ) ^ ((n : ℝ) / 10) := by
    rw [eq_div_iff hden.ne']
    linarith [hsplit]
  have hgoal : (2 : ℝ) ^ n / ((3 : ℝ) / ε) = (ε / 3) * (2 : ℝ) ^ n := by
    field_simp
  calc (mDk n (n / 8) : ℝ) ≤ (2 : ℝ) ^ (9 * (n : ℝ) / 10) := hm
    _ = (2 : ℝ) ^ n / (2 : ℝ) ^ ((n : ℝ) / 10) := heq
    _ ≤ (2 : ℝ) ^ n / ((3 : ℝ) / ε) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hpow
    _ = (ε / 3) * (2 : ℝ) ^ n := hgoal

/-- `log(2^n - 1) ≤ n`. -/
theorem log_two_pow_sub_one_le {n : ℕ} (hn : 1 ≤ n) :
    Real.log ((2 : ℝ) ^ n - 1) ≤ (n : ℝ) := by
  have hpow : (1 : ℝ) < (2 : ℝ) ^ n := by
    calc (1 : ℝ) = (2 : ℝ) ^ 0 := by norm_num
      _ < (2 : ℝ) ^ n := pow_lt_pow_right₀ (by norm_num) (by omega : 0 < n)
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n - 1 := by linarith
  have h1 := Real.log_le_log hpos (by linarith : (2 : ℝ) ^ n - 1 ≤ (2 : ℝ) ^ n)
  have h2 : Real.log ((2 : ℝ) ^ n) = (n : ℝ) * Real.log 2 := Real.log_pow 2 n
  rw [h2] at h1
  have h3 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  nlinarith

/-- The threshold in Corollary 6. -/
noncomputable def c6N (ε : ℝ) : ℕ :=
  max 4096 (max (Nat.ceil ((491520 / ε) ^ 2))
    (max (Nat.ceil (10 * Real.log (3 / ε) / Real.log 2) + 10)
      (Nat.ceil (Real.log (12 / ε) / Real.log 2) + 10)))

/-- **Corollary 6**: `L(D_n) ≥ (3-o(1))·2^n`, i.e. for every `ε > 0` and all large `n`,
`(3-ε)·2^n ≤ L(D_n)`. -/
theorem corollary6 (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∀ n ≥ N, (3 - ε) * (2 : ℝ) ^ n ≤ (chainComplexity (Dmat n) : ℝ) := by
  by_cases hbig : 3 ≤ ε
  · refine ⟨0, fun n _ => ?_⟩
    have h2n : (0 : ℝ) ≤ (2 : ℝ) ^ n := by positivity
    have h0 : (3 - ε) * (2 : ℝ) ^ n ≤ 0 := by nlinarith
    have hL : (0 : ℝ) ≤ (chainComplexity (Dmat n) : ℝ) := by positivity
    linarith
  push Not at hbig
  refine ⟨c6N ε, fun n hn => ?_⟩
  have h4096 : 4096 ≤ n := le_trans (le_max_left _ _) hn
  have hA : Nat.ceil ((491520 / ε) ^ 2) ≤ n :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hn)
  have hB : Nat.ceil (10 * Real.log (3 / ε) / Real.log 2) + 10 ≤ n :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))
  have hC : Nat.ceil (Real.log (12 / ε) / Real.log 2) + 10 ≤ n :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hn))
  have hsq : (491520 / ε) ^ 2 ≤ (n : ℝ) := by
    have h1 : (491520 / ε) ^ 2 ≤ (Nat.ceil ((491520 / ε) ^ 2) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil ((491520 / ε) ^ 2) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hA
    linarith
  have hlog3 : 10 * Real.log (3 / ε) / Real.log 2 + 10 ≤ (n : ℝ) := by
    have h1 : 10 * Real.log (3 / ε) / Real.log 2 ≤
        (Nat.ceil (10 * Real.log (3 / ε) / Real.log 2) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (10 * Real.log (3 / ε) / Real.log 2) + 10 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hB
    push_cast at h2
    linarith
  have hlog12 : Real.log (12 / ε) / Real.log 2 ≤ (n : ℝ) := by
    have h1 : Real.log (12 / ε) / Real.log 2 ≤
        (Nat.ceil (Real.log (12 / ε) / Real.log 2) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (Real.log (12 / ε) / Real.log 2) + 10 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hC
    push_cast at h2
    linarith
  have hn1000 : 1000 ≤ n := by omega
  have hk1 : 1 ≤ n / 8 := by omega
  have hkn : n / 8 < n := by omega
  have hn1 : 1 ≤ n := by omega
  have hK3 : 3 ≤ Kc6 n := Kc6_three h4096
  have hKspec : 2 * Kc6 n + 2 ≤ mu n (n / 8) - 2 := Kc6_spec hK3
  have hXpos : 0 < (2 : ℝ) ^ n - 1 := by
    have h2 : (1 : ℝ) < (2 : ℝ) ^ n := by
      calc (1 : ℝ) = (2 : ℝ) ^ 0 := by norm_num
        _ < (2 : ℝ) ^ n := pow_lt_pow_right₀ (by norm_num) (by omega : 0 < n)
    linarith
  have hmain := Dmat_lower_bound (k := n / 8) (K := Kc6 n) hk1 hkn (by omega) hKspec
  have hmeps := mDk_eps_bound hε hn1000 (two_pow_tenth_ge hε hlog3)
  have hbigM := two_pow_ge_inv hε hlog12
  exact arith_c6 (K := Kc6 n) hε hK3 hXpos rfl (log_two_pow_sub_one_le hn1)
    (Kc6_eps_bound hε h4096 hsq) hmain hmeps hbigM

end Sierpinski
