module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Bool.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Order.SetNotation
public import Mathlib.Data.Set.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

/-!
# Sections 1, 2 and 4: formulas, graph measures, normal forms, linear bounds

This file collects the material of Sections 1 and 2 of I. S. Sergeev,
*Formula complexity of a linear function in a k-ary basis*,
Mathematical Notes 109 (2021), 445--458, together with the normal-form
translation between the unate basis `U_k` and the monotone basis `M_k`, and the
two elementary bounds on the complexity of the linear function from page 2 and
from Theorem 4(i).

The main definitions are:

* `UnateLin.BasisFunction`, `UnateLin.Formula`, `UnateLin.Formula.eval` and
  `UnateLin.Formula.complexity`: Boolean formulas over an arbitrary basis and
  their complexity, following the inductive definition in the paper.
* `UnateLin.complexity`: the minimum complexity `L_B(f)` of a formula over `B`
  realizing `f`.
* `UnateLin.sensitivity`: the sensitivity `s(f)` defined by (1.1).
* `UnateLin.Uk`: the maximal unate `k`-ary basis `U_k`.
* `UnateLin.khrapchenkoExponent`: the Khrapchenko exponent `χ_B` of a basis,
  defined by (1.2).
* `UnateLin.BipartiteGraph` and `UnateLin.sGraph`: a finite bipartite graph and
  its density measure `s(G)` from (2.1).
* `UnateLin.IsCover` and `UnateLin.IsMonotoneCover`: covers and monotone covers.
  The cover condition contains the paper's (missing) requirement
  `E_i = (A_i × B_i) ∩ E`.
* `UnateLin.IsGraphExponent` and `UnateLin.IsMonotoneGraphExponent`: the
  subadditivity conditions defining `χ_k` and `χ*_k`.
* `UnateLin.sT`: the generalised sensitivity `s_T(f)` used in Proposition 2.
* `UnateLin.NNF`: the negation normal form over the basis `M_k` of all `k`-ary
  monotone functions together with negation.
* `UnateLin.signFlip`, `UnateLin.Formula.toNNF`, `UnateLin.NNF.toFormula`:
  the translations showing that `U_k` and `M_k` are equivalent bases, with
  `complexity_eq_nnfComplexity` and `khrapchenkoBound_Uk` as consequences.
* `UnateLin.linearFun`, `UnateLin.sensitivity_linearFun`,
  `UnateLin.linear_lower_bound`: the linear function `l_n`, its sensitivity
  `s(l_n) = n^2`, and the lower bound `n^(2χ) ≤ L_B(l_n)` of page 2.
* `UnateLin.mintermGate`, `UnateLin.linearFun_sigma_equiv`,
  `UnateLin.exists_linearNNF`, `UnateLin.complexity_linearFun_upper_bound`:
  the `k`-ary splitting construction and Theorem 4(i),
  `L_{U_{2k}}(l_n) ≤ 2 n^(1 + 1/log₂ k)`.

Proposition 2 is proved for `NNF`, the negation-normal form of the basis `M_k`.
The paper's basis `U_k` is strictly equivalent to `M_k`; the translation is
mechanized below, and Proposition 1 transfers to `Uk k` as
`khrapchenkoBound_Uk`.

## Design notes

A basis is represented as a set of pairs `⟨k, g⟩`, where `k` is the arity and
`g : (Fin k → Bool) → Bool` is the Boolean function.  Constants are treated as
zero-complexity leaves whenever the basis contains a constant function with the
corresponding value.  Nonconstant basis functions are applied through the `app`
constructor.  The variable type is `Fin n`, so formulas are always formulas in
the variables `x_0, …, x_{n-1}`.

The minimum complexity is defined as the infimum of the complexities of all
formulas realizing `f`.  For a function not expressible in the basis this infimum
is `0` (the infimum of the empty set); statements about `L_B(f)` are therefore
restricted to expressible functions.  This keeps the definition total and avoids
carrying realizability proofs in the notation.
-/

namespace UnateLin

open scoped BigOperators

/-- Boolean functions in `n` variables. -/
abbrev BoolFun (n : ℕ) := (Fin n → Bool) → Bool

/-- A Boolean function together with its arity. -/
abbrev BasisFunction := Σ n : ℕ, BoolFun n

namespace BasisFunction

/-- A basis function is constant if it takes a single value. -/
def IsConstant (g : BasisFunction) : Prop :=
  ∃ b : Bool, ∀ x : Fin g.1 → Bool, g.2 x = b

end BasisFunction

/-- A basis contains the constant `b` if some function in the basis is constantly `b`. -/
def ConstantIn (B : Set BasisFunction) (b : Bool) : Prop :=
  ∃ g : BasisFunction, g ∈ B ∧ ∀ x : Fin g.1 → Bool, g.2 x = b

/-- Formulas over a basis `B` in the variables `x_0, …, x_{n-1}`.

This is the inductive definition from Section 1: basis constants are leaves of
complexity `0`, variables are leaves of complexity `1`, and a nonconstant basis
function of arity `k` applied to `k` formulas has complexity equal to the sum of
the complexities of its arguments. -/
inductive Formula (B : Set BasisFunction) (n : ℕ) : Type
  | const (b : Bool) (hb : ConstantIn B b) : Formula B n
  | var (i : Fin n) : Formula B n
  | app (g : BasisFunction) (hg : g ∈ B) (h : ¬ g.IsConstant)
      (args : Fin g.1 → Formula B n) : Formula B n

namespace Formula

variable {B : Set BasisFunction} {n : ℕ}

/-- The Boolean function realized by a formula under an assignment. -/
def eval : Formula B n → (Fin n → Bool) → Bool
  | const b _, _ => b
  | var i, x => x i
  | app g _ _ args, x => g.2 (fun i => eval (args i) x)

/-- The complexity of a formula: the number of variable leaves. -/
def complexity : Formula B n → ℕ
  | const _ _ => 0
  | var _ => 1
  | app g _ _ args => ∑ i : Fin g.1, complexity (args i)

@[simp]
theorem complexity_const (b : Bool) (hb : ConstantIn B b) :
    (const b hb : Formula B n).complexity = 0 := rfl

@[simp]
theorem complexity_var (i : Fin n) : (var (B := B) i).complexity = 1 := rfl

@[simp]
theorem eval_const (b : Bool) (hb : ConstantIn B b) (x : Fin n → Bool) :
    (const b hb : Formula B n).eval x = b := rfl

@[simp]
theorem eval_var (i : Fin n) (x : Fin n → Bool) :
    (var (B := B) i).eval x = x i := rfl

@[simp]
theorem complexity_app (g : BasisFunction) (hg : g ∈ B) (h : ¬ g.IsConstant)
    (args : Fin g.1 → Formula B n) :
    (app g hg h args).complexity = ∑ i : Fin g.1, (args i).complexity := rfl

@[simp]
theorem eval_app (g : BasisFunction) (hg : g ∈ B) (h : ¬ g.IsConstant)
    (args : Fin g.1 → Formula B n) (x : Fin n → Bool) :
    (app g hg h args).eval x = g.2 (fun i => (args i).eval x) := rfl

end Formula

/-- A function is expressible in a basis if some formula over the basis realizes it. -/
def Expressible (B : Set BasisFunction) {n : ℕ} (f : BoolFun n) : Prop :=
  ∃ F : Formula B n, F.eval = f

/-- The minimum complexity `L_B(f)` of a formula over `B` realizing `f`.

For a function not expressible in `B`, this is the infimum of the empty set, i.e. `0`.
All theorem statements about `L_B(f)` below assume `Expressible B f`. -/
noncomputable def complexity (B : Set BasisFunction) {n : ℕ} (f : BoolFun n) : ℕ :=
  sInf {L : ℕ | ∃ F : Formula B n, F.eval = f ∧ F.complexity = L}

/-- Any formula realizing `f` gives an upper bound on the minimum complexity. -/
theorem complexity_le_of_eval {B : Set BasisFunction} {n : ℕ} {f : BoolFun n}
    {F : Formula B n} (hF : F.eval = f) : complexity B f ≤ F.complexity := by
  unfold complexity
  exact Nat.sInf_le ⟨F, hF, rfl⟩

/-- The set of complexities of formulas realizing `f`, when nonempty. -/
theorem exists_complexity_of_expressible {B : Set BasisFunction} {n : ℕ} {f : BoolFun n}
    (h : Expressible B f) :
    ∃ L : ℕ, ∃ F : Formula B n, F.eval = f ∧ F.complexity = L := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F.complexity, F, hF, rfl⟩

/-- A constant function has complexity at most zero when the basis contains that constant. -/
theorem complexity_const_le {B : Set BasisFunction} {n : ℕ} (b : Bool)
    (hb : ConstantIn B b) : complexity B (fun _ : Fin n → Bool => b) ≤ 0 := by
  apply complexity_le_of_eval (F := Formula.const b hb)
  rfl

/-- A constant function has complexity zero when the basis contains that constant. -/
theorem complexity_const_eq_zero {B : Set BasisFunction} {n : ℕ} (b : Bool)
    (hb : ConstantIn B b) : complexity B (fun _ : Fin n → Bool => b) = 0 :=
  Nat.eq_zero_of_le_zero (complexity_const_le b hb)

/-- A projection has complexity at most one. -/
theorem complexity_proj_le (B : Set BasisFunction) {n : ℕ} (i : Fin n) :
    complexity B (fun x : Fin n → Bool => x i) ≤ 1 := by
  apply complexity_le_of_eval (F := Formula.var (B := B) i)
  rfl

/-- Hamming distance between two Boolean assignments. -/
def hammingDist {n : ℕ} (x y : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i ≠ y i).card

/-- The pairs `(x,y) ∈ N × P` at Hamming distance one. -/
def neighborPairs {n : ℕ} (N P : Finset (Fin n → Bool)) :
    Finset ((Fin n → Bool) × (Fin n → Bool)) :=
  (N.product P).filter fun q => hammingDist q.1 q.2 = 1

/-- The set of values of the ratio in the definition of sensitivity.

The subsets `N ⊆ f^{-1}(0)` and `P ⊆ f^{-1}(1)` are required to be nonempty so that
the denominator `|N| * |P|` is nonzero. -/
def sensitivityValues {n : ℕ} (f : BoolFun n) : Set ℝ :=
  {r : ℝ |
    ∃ N P : Finset (Fin n → Bool),
      N.Nonempty ∧ P.Nonempty ∧
      (∀ x ∈ N, f x = false) ∧ (∀ y ∈ P, f y = true) ∧
      r = ((neighborPairs N P).card : ℝ) ^ 2 /
          ((N.card : ℝ) * (P.card : ℝ))}

/-- The sensitivity `s(f)` of a Boolean function, equation (1.1).

It is the supremum of `|R(N,P)|^2 / (|N| * |P|)` over nonempty `N ⊆ f^{-1}(0)` and
`P ⊆ f^{-1}(1)`, where `R(N,P)` is the set of neighboring pairs.  For a function with
no such pair of subsets the supremum is `0`. -/
noncomputable def sensitivity {n : ℕ} (f : BoolFun n) : ℝ :=
  sSup (sensitivityValues f)

/-- Every value in `sensitivityValues f` is nonnegative. -/
theorem sensitivityValues_nonneg {n : ℕ} (f : BoolFun n) :
    ∀ r ∈ sensitivityValues f, 0 ≤ r := by
  rintro r ⟨N, P, -, -, -, -, rfl⟩
  positivity

/-- The sensitivity is nonnegative. -/
theorem sensitivity_nonneg {n : ℕ} (f : BoolFun n) : 0 ≤ sensitivity f := by
  unfold sensitivity
  exact Real.sSup_nonneg (sensitivityValues_nonneg f)

/-- Constant functions have sensitivity zero. -/
theorem sensitivity_const {n : ℕ} (b : Bool) :
    sensitivity (fun _ : Fin n → Bool => b) = 0 := by
  unfold sensitivity
  have h : sensitivityValues (fun _ : Fin n → Bool => b) = ∅ := by
    ext r
    constructor
    · rintro ⟨N, P, hN, hP, hz, ho, rfl⟩
      cases b
      · obtain ⟨y, hy⟩ := hP
        exact absurd (ho y hy) (by simp)
      · obtain ⟨x, hx⟩ := hN
        exact absurd (hz x hx) (by simp)
    · simp
  rw [h, Real.sSup_empty]

/-- `f` is nondecreasing in coordinate `i` when the other coordinates are fixed. -/
def NondecreasingIn {n : ℕ} (f : BoolFun n) (i : Fin n) : Prop :=
  ∀ x y : Fin n → Bool,
    (∀ j : Fin n, j ≠ i → x j = y j) → x i ≤ y i → f x ≤ f y

/-- `f` is nonincreasing in coordinate `i` when the other coordinates are fixed. -/
def NonincreasingIn {n : ℕ} (f : BoolFun n) (i : Fin n) : Prop :=
  ∀ x y : Fin n → Bool,
    (∀ j : Fin n, j ≠ i → x j = y j) → y i ≤ x i → f x ≤ f y

/-- `f` is unate in coordinate `i` if it is monotone in one of the two directions. -/
def UnateIn {n : ℕ} (f : BoolFun n) (i : Fin n) : Prop :=
  NondecreasingIn f i ∨ NonincreasingIn f i

/-- A Boolean function is unate if it is monotone (in one direction) in every variable. -/
def Unate {n : ℕ} (f : BoolFun n) : Prop :=
  ∀ i : Fin n, UnateIn f i

/-- Constant functions are unate. -/
theorem unate_const {n : ℕ} (b : Bool) : Unate (fun _ : Fin n → Bool => b) := by
  intro i
  left
  intro x y _ _
  simp

/-- Coordinate projections are unate. -/
theorem unate_proj {n : ℕ} (i : Fin n) : Unate (fun x : Fin n → Bool => x i) := by
  intro j
  by_cases h : j = i
  · subst h
    left
    intro x y hxy hle
    simpa using hle
  · left
    intro x y hxy _
    have hji : x i = y i := hxy i (Ne.symm h)
    simp [hji]

/-- Negation is unate (it is nonincreasing in its only variable). -/
theorem unate_not : Unate (fun x : Fin 1 → Bool => !x 0) := by
  intro i
  fin_cases i
  right
  intro x y _ hyx
  by_cases hx : x 0 <;> by_cases hy : y 0 <;>
    simp [hx, hy, Bool.le_iff_imp] at hyx ⊢

/-- The maximal unate `k`-ary basis `U_k`.

It consists exactly of all unate Boolean functions of arity at most `k`.  In the
paper this is the basis of all `k`-ary monotone functions together with negation;
equivalently, it is the maximal `k`-ary basis in which the linear function has
nonlinear formula complexity. -/
def Uk (k : ℕ) : Set BasisFunction :=
  {g : BasisFunction | g.1 ≤ k ∧ Unate g.2}

@[simp]
theorem mem_Uk {k : ℕ} {g : BasisFunction} :
    g ∈ Uk k ↔ g.1 ≤ k ∧ Unate g.2 := Iff.rfl

/-- The bases `U_k` are nested. -/
theorem Uk_mono {k : ℕ} : Uk k ⊆ Uk (k + 1) := by
  intro g hg
  exact ⟨Nat.le_trans hg.1 (Nat.le_succ k), hg.2⟩

/-- `U_k` is the greatest unate `k`-ary basis: every basis all of whose functions
are unate of arity at most `k` is contained in `U_k`. -/
theorem subset_Uk_of_unate {B : Set BasisFunction} {k : ℕ}
    (hB : ∀ g ∈ B, g.1 ≤ k ∧ Unate g.2) : B ⊆ Uk k := by
  intro g hg
  exact hB g hg

/-- The constants `0` and `1` are available in `U_k`. -/
theorem constantIn_Uk (k : ℕ) (b : Bool) : ConstantIn (Uk k) b := by
  refine ⟨⟨0, fun _ => b⟩, ?_, ?_⟩
  · exact ⟨Nat.zero_le k, unate_const b⟩
  · intro x
    rfl

/-- Negation belongs to `U_k` for `k ≥ 1`. -/
theorem not_mem_Uk {k : ℕ} (hk : 1 ≤ k) :
    (⟨1, fun x : Fin 1 → Bool => !x 0⟩ : BasisFunction) ∈ Uk k :=
  ⟨hk, unate_not⟩

/-- A predicate saying that `χ` satisfies the Khrapchenko inequality (1.2) for `B`. -/
def KhrapchenkoBound (B : Set BasisFunction) (χ : ℝ) : Prop :=
  ∀ (n : ℕ) (f : BoolFun n), Expressible B f →
    sensitivity f ^ χ ≤ (complexity B f : ℝ)

/-- The Khrapchenko exponent `χ_B` of a basis, equation (1.2).

It is the supremum of all real `χ` such that `L_B(f) ≥ s(f)^χ` for every function
expressible in `B`.  The paper shows that this supremum is attained and gives
two-sided bounds for `χ_{U_k}`. -/
noncomputable def khrapchenkoExponent (B : Set BasisFunction) : ℝ :=
  sSup {χ : ℝ | KhrapchenkoBound B χ}

/-- Membership in the set whose supremum defines the Khrapchenko exponent. -/
theorem mem_khrapchenkoSet {B : Set BasisFunction} {χ : ℝ} :
    χ ∈ {χ : ℝ | KhrapchenkoBound B χ} ↔ KhrapchenkoBound B χ := Iff.rfl

/-- The linear function `l_n(x_1, …, x_n) = x_1 ⊕ ⋯ ⊕ x_n`. -/
def linearFun (n : ℕ) : BoolFun n :=
  fun x => (Finset.univ.filter fun i => x i).card % 2 = 1


/-! ### Bipartite graphs and the measure `s(G)` -/

/-- A finite bipartite graph with vertex classes `A` and `B`.

The fields `left` and `right` record the two parts.  Keeping them explicit is
important for the cover definition: a subgraph may use only subsets of the two
parts, and `s(G)` maximises over subsets of those parts. -/
structure BipartiteGraph (A B : Type) where
  left : Set A
  right : Set B
  edge : A → B → Bool

namespace BipartiteGraph

variable {A B : Type}

/-- The number of edges of `G` between `X` and `Y`. -/
def edgeCount (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B) : ℕ :=
  ((X.product Y).filter fun q => G.edge q.1 q.2).card

/-- `X` and `Y` lie in the two parts of `G`. -/
def Admissible (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B) : Prop :=
  (∀ a ∈ X, a ∈ G.left) ∧ (∀ b ∈ Y, b ∈ G.right)

/-- The ratio `|E ∩ (X × Y)|² / (|X| |Y|)` from (2.1).  It is set to `0`
for nonadmissible `X`, `Y`. -/
noncomputable def ratio (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B) : ℝ := by
  classical
  exact if G.Admissible X Y then
    (G.edgeCount X Y : ℝ) ^ 2 / ((X.card : ℝ) * (Y.card : ℝ))
  else 0

variable [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- The measure `s(G)` of a finite bipartite graph, equation (2.1):
the maximum of `|E ∩ (X × Y)|² / (|X| |Y|)` over `X ⊆ A`, `Y ⊆ B`. -/
noncomputable def sGraph (G : BipartiteGraph A B) : ℝ :=
  (Finset.univ : Finset (Finset A × Finset B)).sup'
    (by exact Finset.univ_nonempty)
    (fun p => G.ratio p.1 p.2)

end BipartiteGraph

namespace BipartiteGraph

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- Every ratio is nonnegative. -/
theorem ratio_nonneg {A B : Type} (G : BipartiteGraph A B) (X : Finset A) (Y : Finset B) :
    0 ≤ G.ratio X Y := by
  classical
  unfold ratio
  split_ifs
  · positivity
  · exact le_refl 0

/-- The measure `s(G)` is nonnegative. -/
theorem sGraph_nonneg (G : BipartiteGraph A B) : 0 ≤ G.sGraph := by
  classical
  unfold sGraph
  have h := Finset.le_sup'
    (s := (Finset.univ : Finset (Finset A × Finset B)))
    (f := fun p : Finset A × Finset B => G.ratio p.1 p.2)
    (b := (∅, ∅)) (by simp)
  have h0 : G.ratio ∅ ∅ = 0 := by
    simp [ratio, Admissible, edgeCount]
  calc
    0 = G.ratio ∅ ∅ := h0.symm
    _ ≤ _ := h

/-- The maximum defining `s(G)` is attained at an admissible pair of finsets. -/
theorem exists_admissible_eq_sGraph (G : BipartiteGraph A B) :
    ∃ X : Finset A, ∃ Y : Finset B,
      G.Admissible X Y ∧ G.sGraph = G.ratio X Y := by
  classical
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Finset A × Finset B)))
    (by exact Finset.univ_nonempty)
    (fun p : Finset A × Finset B => G.ratio p.1 p.2)
  unfold sGraph
  by_cases h : G.Admissible p.1 p.2
  · exact ⟨p.1, p.2, h, hp⟩
  · have hr : G.ratio p.1 p.2 = 0 := by simp [ratio, h]
    refine ⟨∅, ∅, ?_, ?_⟩
    · exact ⟨by simp, by simp⟩
    · rw [hp, hr]
      simp [ratio, Admissible, edgeCount]

/-- The number of edges is monotone under pointwise inclusion of edge relations. -/
theorem edgeCount_le {G H : BipartiteGraph A B}
    (he : ∀ a b, H.edge a b = true → G.edge a b = true)
    (X : Finset A) (Y : Finset B) : H.edgeCount X Y ≤ G.edgeCount X Y := by
  unfold edgeCount
  apply Finset.card_le_card
  intro q hq
  simp only [Finset.mem_filter, Finset.mem_product] at hq ⊢
  exact ⟨hq.1, he q.1 q.2 hq.2⟩

/-- The ratio is monotone when the left and right parts and the edge relation
are included in those of a larger graph. -/
theorem ratio_le {G H : BipartiteGraph A B}
    (hl : H.left ⊆ G.left) (hr : H.right ⊆ G.right)
    (he : ∀ a b, H.edge a b = true → G.edge a b = true)
    (X : Finset A) (Y : Finset B) : H.ratio X Y ≤ G.ratio X Y := by
  classical
  by_cases hX : H.Admissible X Y
  · have hXG : G.Admissible X Y :=
      ⟨fun a ha => hl (hX.1 a ha), fun b hb => hr (hX.2 b hb)⟩
    have hc : H.edgeCount X Y ≤ G.edgeCount X Y := edgeCount_le he X Y
    have hcR : (H.edgeCount X Y : ℝ) ≤ (G.edgeCount X Y : ℝ) := by exact_mod_cast hc
    have hc0 : (0 : ℝ) ≤ (H.edgeCount X Y : ℝ) := by positivity
    have hsq : (H.edgeCount X Y : ℝ) ^ 2 ≤ (G.edgeCount X Y : ℝ) ^ 2 := by
      exact pow_le_pow_left₀ hc0 hcR 2
    have hden : (0 : ℝ) ≤ (X.card : ℝ) * (Y.card : ℝ) := by positivity
    simp only [ratio, if_pos hX, if_pos hXG]
    exact div_le_div_of_nonneg_right hsq hden
  · have h0 : H.ratio X Y = 0 := by simp [ratio, hX]
    rw [h0]
    exact ratio_nonneg G X Y

/-- `s(G)` is monotone under taking a subgraph in the strong sense that the
parts and the edge relation are included. -/
theorem sGraph_mono {G H : BipartiteGraph A B}
    (hl : H.left ⊆ G.left) (hr : H.right ⊆ G.right)
    (he : ∀ a b, H.edge a b = true → G.edge a b = true) :
    H.sGraph ≤ G.sGraph := by
  classical
  unfold sGraph
  apply Finset.sup'_le
  intro p _
  exact le_trans (ratio_le hl hr he p.1 p.2)
    (Finset.le_sup' (fun p : Finset A × Finset B => G.ratio p.1 p.2) (Finset.mem_univ p))

end BipartiteGraph

/-- A graph `H` has exactly the edges of `G` that join its own two parts:
`E_H = (A_H × B_H) ∩ E_G`.  This is the condition missing from the printed
definition of a cover. -/
def EdgeRestriction {A B : Type} (G H : BipartiteGraph A B) : Prop :=
  ∀ a b, H.edge a b = true ↔ G.edge a b = true ∧ a ∈ H.left ∧ b ∈ H.right

namespace BipartiteGraph

/-- All edges of `G` join vertices in its declared parts. -/
def WellFormed (G : BipartiteGraph A B) : Prop :=
  ∀ a b, G.edge a b = true → a ∈ G.left ∧ b ∈ G.right

end BipartiteGraph

/-- The graph with parts `X`, `Y` and edge relation `T` restricted to `X × Y`. -/
def graphOn {A B : Type} [DecidableEq A] [DecidableEq B]
    (T : A → B → Bool) (X : Finset A) (Y : Finset B) :
    BipartiteGraph A B where
  left := {a | a ∈ X}
  right := {b | b ∈ Y}
  edge := fun a b => T a b && decide (a ∈ X) && decide (b ∈ Y)

/-- The subgraph used in the proof of Proposition 2: keep only the edges joining
the vertices where `f` is `0` on the left and `g` is `1` on the right. -/
def coverGraph {A B : Type} (G : BipartiteGraph A B) (f : A → Bool) (g : B → Bool) :
    BipartiteGraph A B where
  left := {a | a ∈ G.left ∧ f a = false}
  right := {b | b ∈ G.right ∧ g b = true}
  edge := fun a b => G.edge a b && Bool.not (f a) && g b

namespace BipartiteGraph

variable {A B : Type}

theorem graphOn_wellFormed [DecidableEq A] [DecidableEq B]
    {T : A → B → Bool} (X : Finset A) (Y : Finset B) :
    (graphOn T X Y).WellFormed := by
  intro a b h
  simp only [graphOn, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2⟩

theorem coverGraph_left_subset (G : BipartiteGraph A B) (f : A → Bool) (g : B → Bool) :
    (coverGraph G f g).left ⊆ G.left := by
  intro a ha
  exact ha.1

theorem coverGraph_right_subset (G : BipartiteGraph A B) (f : A → Bool) (g : B → Bool) :
    (coverGraph G f g).right ⊆ G.right := by
  intro b hb
  exact hb.1

theorem coverGraph_edgeRestriction (G : BipartiteGraph A B) (f : A → Bool) (g : B → Bool)
    (hG : G.WellFormed) : EdgeRestriction G (coverGraph G f g) := by
  intro a b
  constructor
  · intro h
    simp only [coverGraph, Bool.and_eq_true] at h
    have hge : G.edge a b = true := h.1.1
    have hfa : Bool.not (f a) = true := h.1.2
    have hgb : g b = true := h.2
    have hfa' : f a = false := by simpa using hfa
    have hgb' : g b = true := hgb
    obtain ⟨ha, hb⟩ := hG a b hge
    exact ⟨hge, ⟨ha, hfa'⟩, ⟨hb, hgb'⟩⟩
  · rintro ⟨hge, ⟨ha, hfa⟩, ⟨hb, hgb⟩⟩
    simp only [coverGraph, Bool.and_eq_true]
    refine ⟨⟨hge, ?_⟩, hgb⟩
    simp [hfa]

end BipartiteGraph

/-- The graph with empty vertex classes and no edges. -/
def emptyGraph (A B : Type) : BipartiteGraph A B where
  left := ∅
  right := ∅
  edge := fun _ _ => false

/-- A family `G_1, …, G_k` is a cover of `G` if each `G_i` uses subsets of the
parts of `G`, has edge set `(A_i × B_i) ∩ E`, and the edge sets cover `E`. -/
def IsCover {A B : Type} {k : ℕ} (G : BipartiteGraph A B)
    (Gs : Fin k → BipartiteGraph A B) : Prop :=
  (∀ i, (Gs i).left ⊆ G.left) ∧
  (∀ i, (Gs i).right ⊆ G.right) ∧
  (∀ i, EdgeRestriction G (Gs i)) ∧
  (∀ a b, G.edge a b = true → ∃ i, (Gs i).edge a b = true)

/-- A cover is monotone if for every set `I` of indices one of the two sets
`A \ ⋃_{i ∈ I} A_i` and `B \ ⋃_{i ∉ I} B_i` is empty. -/
def IsMonotoneCover {A B : Type} {k : ℕ} (G : BipartiteGraph A B)
    (Gs : Fin k → BipartiteGraph A B) : Prop :=
  IsCover G Gs ∧
  ∀ I : Set (Fin k),
    (G.left \ ⋃ i ∈ I, (Gs i).left = ∅) ∨
    (G.right \ ⋃ i ∈ Iᶜ, (Gs i).right = ∅)

/-! ### Complexity exponents of bipartite graphs -/

/-- `χ` is an exponent of complexity of bipartite graphs with covers of size at
most `k`: every cover `G_1, …, G_m`, `m ≤ k`, satisfies the subadditivity
condition `∑ s(G_i)^χ ≥ s(G)^χ`.

Using "at most `k`" rather than "exactly `k`" is equivalent to the paper's
definition, because a shorter cover can be padded by empty graphs. -/
def IsGraphExponent (k : ℕ) (χ : ℝ) : Prop :=
  ∀ (m : ℕ), m ≤ k →
  ∀ (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (G : BipartiteGraph A B) (Gs : Fin m → BipartiteGraph A B),
    IsCover G Gs →
      BipartiteGraph.sGraph G ^ χ ≤ ∑ i, BipartiteGraph.sGraph (Gs i) ^ χ

/-- `χ` is an exponent of monotone complexity of bipartite graphs with covers
of size at most `k`. -/
def IsMonotoneGraphExponent (k : ℕ) (χ : ℝ) : Prop :=
  ∀ (m : ℕ), m ≤ k →
  ∀ (A B : Type) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (G : BipartiteGraph A B) (Gs : Fin m → BipartiteGraph A B),
    IsMonotoneCover G Gs →
      BipartiteGraph.sGraph G ^ χ ≤ ∑ i, BipartiteGraph.sGraph (Gs i) ^ χ

/-- The exponent `χ_k` of complexity of bipartite graphs, as the supremum of
the admissible exponents. -/
noncomputable def chi (k : ℕ) : ℝ := sSup {χ : ℝ | IsGraphExponent k χ}

/-- The exponent `χ*_k` of monotone complexity of bipartite graphs. -/
noncomputable def chiStar (k : ℕ) : ℝ := sSup {χ : ℝ | IsMonotoneGraphExponent k χ}

/-- A graph exponent is a monotone graph exponent, since every monotone cover is
a cover. -/
theorem isMonotoneGraphExponent_of_isGraphExponent {k : ℕ} {χ : ℝ}
    (h : IsGraphExponent k χ) : IsMonotoneGraphExponent k χ := by
  intro m hm A B _ _ _ _ G Gs hG
  exact h m hm A B G Gs hG.1

/-! ### The generalised sensitivity `s_T(f)` -/

/-- The bipartite graph associated with a Boolean function and a pair relation
`T`: the parts are `f^{-1}(0)` and `f^{-1}(1)`, and the edges are the pairs in
`T`. -/
def graphOfFun {n : ℕ} (T : (Fin n → Bool) → (Fin n → Bool) → Bool)
    (f : BoolFun n) : BipartiteGraph (Fin n → Bool) (Fin n → Bool) where
  left := {x | f x = false}
  right := {y | f y = true}
  edge := fun a b => T a b && Bool.not (f a) && f b

/-- The generalised sensitivity `s_T(f)` from Proposition 2:
`max |R_T(N,P)|² / (|N| |P|)` over `N ⊆ f^{-1}(0)`, `P ⊆ f^{-1}(1)`. -/
noncomputable def sT {n : ℕ} (T : (Fin n → Bool) → (Fin n → Bool) → Bool)
    (f : BoolFun n) : ℝ :=
  BipartiteGraph.sGraph (graphOfFun T f)

/-- The denominator bound `s = max_i max {s_T(x_i), s_T(¬x_i)}` from (2.2). -/
noncomputable def sVarBound (n : ℕ) (T : (Fin n → Bool) → (Fin n → Bool) → Bool) : ℝ :=
  if h : (Finset.univ : Finset (Fin n)).Nonempty then
    (Finset.univ : Finset (Fin n)).sup' h
      (fun i => max (sT T (fun x : Fin n → Bool => x i))
                    (sT T (fun x : Fin n → Bool => Bool.not (x i))))
  else 0

theorem sVarBound_eq_sup' {n : ℕ} (T : (Fin n → Bool) → (Fin n → Bool) → Bool)
    (h : (Finset.univ : Finset (Fin n)).Nonempty) :
    sVarBound n T = (Finset.univ : Finset (Fin n)).sup' h
      (fun i => max (sT T (fun x : Fin n → Bool => x i))
                    (sT T (fun x : Fin n → Bool => Bool.not (x i)))) := by
  unfold sVarBound
  exact dif_pos h

theorem sT_nonneg {n : ℕ} (T : (Fin n → Bool) → (Fin n → Bool) → Bool) (f : BoolFun n) :
    0 ≤ sT T f := BipartiteGraph.sGraph_nonneg _

theorem sVarBound_nonneg {n : ℕ} (T : (Fin n → Bool) → (Fin n → Bool) → Bool) :
    0 ≤ sVarBound n T := by
  by_cases h : (Finset.univ : Finset (Fin n)).Nonempty
  · rw [sVarBound_eq_sup' T h]
    obtain ⟨i, -⟩ := h
    have h0 : 0 ≤ max (sT T (fun x : Fin n → Bool => x i))
        (sT T (fun x : Fin n → Bool => Bool.not (x i))) :=
      le_trans (sT_nonneg T _) (le_max_left _ _)
    exact le_trans h0 (Finset.le_sup'
      (fun j => max (sT T (fun x : Fin n → Bool => x j))
                    (sT T (fun x : Fin n → Bool => Bool.not (x j))))
      (Finset.mem_univ i))
  · simp [sVarBound, h]

/-! ### Monotone gates and negation-normal-form formulas -/

/-- A monotone Boolean function of `m` arguments. -/
structure MonotoneFun (m : ℕ) where
  toFun : (Fin m → Bool) → Bool
  monotone : ∀ x y : Fin m → Bool, (∀ i, x i ≤ y i) → toFun x ≤ toFun y

namespace MonotoneFun

instance : CoeFun (MonotoneFun m) (fun _ => (Fin m → Bool) → Bool) :=
  ⟨MonotoneFun.toFun⟩

/-- If `a ≤ b` in `Bool`, then `Bool.not b ≤ Bool.not a`. -/
theorem bool_not_le_not {a b : Bool} (h : a ≤ b) : Bool.not b ≤ Bool.not a := by
  rw [Bool.le_iff_imp] at h ⊢
  intro hb
  cases a <;> cases b <;> simp_all

/-- The dual of a monotone function: `φᵈ(x) = ¬φ(¬x)`. -/
def dual (φ : MonotoneFun m) : MonotoneFun m where
  toFun x := Bool.not (φ (fun i => Bool.not (x i)))
  monotone := by
    intro x y hxy
    have hyx : (fun i => Bool.not (y i)) ≤ (fun i => Bool.not (x i)) := by
      intro i
      exact bool_not_le_not (hxy i)
    exact bool_not_le_not (φ.monotone _ _ hyx)

@[simp]
theorem dual_toFun (φ : MonotoneFun m) (x : Fin m → Bool) :
    φ.dual x = Bool.not (φ (fun i => Bool.not (x i))) := rfl

end MonotoneFun

/-- Formulas over the basis of monotone `k`-ary functions and negation, in
negation-normal form: negations occur only on variables. -/
inductive NNF (k n : ℕ) : Type
  | const (b : Bool) : NNF k n
  | var (i : Fin n) (sign : Bool) : NNF k n
  | gate (m : ℕ) (hm : m ≤ k) (φ : MonotoneFun m) (args : Fin m → NNF k n) : NNF k n

namespace NNF

variable {k n : ℕ}

/-- Evaluation of a negation-normal-form formula. -/
def eval : NNF k n → BoolFun n
  | const b => fun _ => b
  | var i sign => fun x => if sign then Bool.not (x i) else x i
  | gate _ _ φ args => fun x => φ (fun j => (args j).eval x)

/-- The complexity of a negation-normal-form formula: the number of variable
leaves. -/
def complexity : NNF k n → ℕ
  | const _ => 0
  | var _ _ => 1
  | gate _ _ _ args => ∑ j, (args j).complexity

/-- The size of a formula, used for inductions that have to remove redundant
unary identity gates. -/
def size : NNF k n → ℕ
  | const _ => 1
  | var _ _ => 1
  | gate _ _ _ args => 1 + ∑ j, (args j).size

@[simp]
theorem eval_const (b : Bool) : (const (k := k) (n := n) b).eval = fun _ => b := rfl

@[simp]
theorem eval_var (i : Fin n) (neg : Bool) :
    (var (k := k) i neg).eval = fun x => if neg then !x i else x i := rfl

@[simp]
theorem complexity_const (b : Bool) : (const (k := k) (n := n) b).complexity = 0 := rfl

@[simp]
theorem complexity_var (i : Fin n) (neg : Bool) :
    (var (k := k) i neg).complexity = 1 := rfl

/-- Negation of a negation-normal-form formula, by duality. -/
def neg : NNF k n → NNF k n
  | const b => const (Bool.not b)
  | var i b => var i (Bool.not b)
  | gate m hm φ args => gate m hm φ.dual (fun j => (args j).neg)

@[simp]
theorem eval_neg (F : NNF k n) : F.neg.eval = fun x => Bool.not (F.eval x) := by
  induction F with
  | const b =>
      funext x
      simp [neg, eval]
  | var i b =>
      funext x
      cases b <;> simp [neg, eval]
  | gate m hm φ args ih =>
      funext x
      simp only [neg, eval, MonotoneFun.dual_toFun]
      apply congrArg Bool.not
      apply congrArg φ.toFun
      funext j
      rw [ih j]
      simp

@[simp]
theorem complexity_neg (F : NNF k n) : F.neg.complexity = F.complexity := by
  induction F with
  | const b => rfl
  | var i b => rfl
  | gate m hm φ args ih =>
      simp only [neg, complexity]
      exact Finset.sum_congr rfl (fun j _ => ih j)

end NNF

/-- Constant functions have generalised sensitivity zero. -/
theorem sT_const {n : ℕ} (T : (Fin n → Bool) → (Fin n → Bool) → Bool) (b : Bool) :
    sT T (fun _ : Fin n → Bool => b) = 0 := by
  classical
  unfold sT BipartiteGraph.sGraph
  apply le_antisymm
  · apply Finset.sup'_le
    intro p _
    by_cases h : (graphOfFun T (fun _ : Fin n → Bool => b)).Admissible p.1 p.2
    · have hz : p.1 = ∅ ∨ p.2 = ∅ := by
        cases b
        · right
          ext y
          exact iff_of_false (fun hy => by
            have := h.2 y hy
            simp [graphOfFun] at this) (by simp)
        · left
          ext x
          exact iff_of_false (fun hx => by
            have := h.1 x hx
            simp [graphOfFun] at this) (by simp)
      rcases hz with h1 | h2
      · rw [h1]
        simp [BipartiteGraph.ratio, BipartiteGraph.Admissible, BipartiteGraph.edgeCount]
      · rw [h2]
        simp [BipartiteGraph.ratio, BipartiteGraph.Admissible, BipartiteGraph.edgeCount]
    · simp [BipartiteGraph.ratio, h]
  · exact BipartiteGraph.sGraph_nonneg _

/-- A variable or its negation has generalised sensitivity at most the
denominator bound `s`. -/
theorem sT_var_le {n : ℕ} (T : (Fin n → Bool) → (Fin n → Bool) → Bool) (i : Fin n)
    (sign : Bool) :
    sT T (fun x : Fin n → Bool => if sign then Bool.not (x i) else x i) ≤ sVarBound n T := by
  classical
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i, Finset.mem_univ i⟩
  rw [sVarBound_eq_sup' T hne]
  cases sign
  · change sT T (fun x : Fin n → Bool => x i) ≤ _
    exact le_trans (le_max_left _ _)
      (Finset.le_sup' (fun j => max (sT T (fun x : Fin n → Bool => x j))
        (sT T (fun x : Fin n → Bool => Bool.not (x j)))) (Finset.mem_univ i))
  · change sT T (fun x : Fin n → Bool => Bool.not (x i)) ≤ _
    exact le_trans (le_max_right _ _)
      (Finset.le_sup' (fun j => max (sT T (fun x : Fin n → Bool => x j))
        (sT T (fun x : Fin n → Bool => Bool.not (x j)))) (Finset.mem_univ i))

/-- If `A ⊆ f^{-1}(0)`, `B ⊆ f^{-1}(1)`, and `(A,B)` is a maximiser for
`s_T(f)`, then the graph on `A × B` has measure exactly `s_T(f)`. -/
theorem sGraph_graphOn_eq_sT {n : ℕ}
    (T : (Fin n → Bool) → (Fin n → Bool) → Bool) (f : BoolFun n)
    (A : Finset (Fin n → Bool)) (B : Finset (Fin n → Bool))
    (hA : ∀ a ∈ A, f a = false) (hB : ∀ b ∈ B, f b = true)
    (hmax : (graphOfFun T f).sGraph = (graphOfFun T f).ratio A B) :
    (graphOn T A B).sGraph = sT T f := by
  classical
  have hle : (graphOn T A B).sGraph ≤ (graphOfFun T f).sGraph := by
    apply BipartiteGraph.sGraph_mono
    · intro a ha
      exact hA a ha
    · intro b hb
      exact hB b hb
    · intro a b h
      simp only [graphOn, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hT, ha⟩, hb⟩ := h
      simp [graphOfFun, hT, hA a ha, hB b hb]
  have hcount : (graphOfFun T f).edgeCount A B = (graphOn T A B).edgeCount A B := by
    unfold BipartiteGraph.edgeCount
    congr 1
    apply Finset.filter_congr
    intro q hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
    simp [graphOfFun, graphOn, hA q.1 hq1, hB q.2 hq2, hq1, hq2, decide_eq_true_eq,
      Bool.and_eq_true]
  have hratio : (graphOfFun T f).ratio A B = (graphOn T A B).ratio A B := by
    have hAdm1 : (graphOfFun T f).Admissible A B := ⟨hA, hB⟩
    have hAdm2 : (graphOn T A B).Admissible A B :=
      ⟨fun a ha => ha, fun b hb => hb⟩
    simp only [BipartiteGraph.ratio, if_pos hAdm1, if_pos hAdm2, hcount]
  have hge : sT T f ≤ (graphOn T A B).sGraph := by
    calc
      sT T f = (graphOfFun T f).sGraph := rfl
      _ = (graphOfFun T f).ratio A B := hmax
      _ = (graphOn T A B).ratio A B := hratio
      _ ≤ (graphOn T A B).sGraph := by
        unfold BipartiteGraph.sGraph
        exact Finset.le_sup' (fun p : Finset (Fin n → Bool) × Finset (Fin n → Bool) =>
          (graphOn T A B).ratio p.1 p.2) (Finset.mem_univ (A, B))
  exact le_antisymm hle hge

/-- The subgraphs `G_i` constructed from the arguments of a monotone gate form a
monotone cover.  This is the combinatorial core of Proposition 2. -/
theorem coverGraph_isMonotoneCover {α : Type} {m : ℕ}
    (G : BipartiteGraph α α) (hG : G.WellFormed)
    (φ : MonotoneFun m) (fs : Fin m → α → Bool) (f : α → Bool)
    (hf : ∀ a, f a = φ (fun i => fs i a))
    (hleft : ∀ a, a ∈ G.left → f a = false)
    (hright : ∀ b, b ∈ G.right → f b = true) :
    IsMonotoneCover G (fun i => coverGraph G (fs i) (fs i)) := by
  classical
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      exact BipartiteGraph.coverGraph_left_subset G (fs i) (fs i)
    · intro i
      exact BipartiteGraph.coverGraph_right_subset G (fs i) (fs i)
    · intro i
      exact BipartiteGraph.coverGraph_edgeRestriction G (fs i) (fs i) hG
    · intro a b hab
      have hfa : f a = false := hleft a (hG a b hab).1
      have hfb : f b = true := hright b (hG a b hab).2
      have hex : ∃ i, fs i a = false ∧ fs i b = true := by
        by_contra h
        push_neg at h
        have hle : ∀ i, fs i b ≤ fs i a := by
          intro i
          cases hia : fs i a <;> cases hib : fs i b <;> simp_all
        have hmono : φ (fun i => fs i b) ≤ φ (fun i => fs i a) :=
          φ.monotone _ _ hle
        have hbad : (true : Bool) ≤ false := by
          calc
            true = f b := hfb.symm
            _ = φ (fun i => fs i b) := hf b
            _ ≤ φ (fun i => fs i a) := hmono
            _ = f a := (hf a).symm
            _ = false := hfa
        simp [Bool.le_iff_imp] at hbad
      obtain ⟨i, hia, hib⟩ := hex
      exact ⟨i, by simp [coverGraph, hab, hia, hib]⟩
  · intro I
    by_contra h
    push_neg at h
    have hAne : (G.left \ ⋃ i ∈ I, (coverGraph G (fs i) (fs i)).left).Nonempty := h.1
    have hBne : (G.right \ ⋃ i ∈ Iᶜ, (coverGraph G (fs i) (fs i)).right).Nonempty := h.2
    obtain ⟨a, haA, haNot⟩ := hAne
    obtain ⟨b, hbB, hbNot⟩ := hBne
    have hfa : f a = false := hleft a haA
    have hfb : f b = true := hright b hbB
    have hle : ∀ i, fs i b ≤ fs i a := by
      intro i
      by_cases hi : i ∈ I
      · have : fs i a = true := by
          by_contra hfalse
          have hfa' : fs i a = false := by simpa using hfalse
          apply haNot
          simp only [Set.mem_iUnion]
          exact ⟨i, hi, by simp [coverGraph, haA, hfa']⟩
        simp [this]
      · have : fs i b = false := by
          by_contra htrue
          have hfb' : fs i b = true := by simpa using htrue
          apply hbNot
          simp only [Set.mem_iUnion]
          exact ⟨i, hi, by simp [coverGraph, hbB, hfb']⟩
        simp [this]
    have hmono : φ (fun i => fs i b) ≤ φ (fun i => fs i a) :=
      φ.monotone _ _ hle
    have hbad : (true : Bool) ≤ false := by
      calc
        true = f b := hfb.symm
        _ = φ (fun i => fs i b) := hf b
        _ ≤ φ (fun i => fs i a) := hmono
        _ = f a := (hf a).symm
        _ = false := hfa
    simp [Bool.le_iff_imp] at hbad

/-- The graph `G_i` from Proposition 2 has measure at most `s_T(f_i)`. -/
theorem sGraph_coverGraph_graphOn_le_sT {n : ℕ}
    (T : (Fin n → Bool) → (Fin n → Bool) → Bool) (f : BoolFun n)
    (A B : Finset (Fin n → Bool)) :
    (coverGraph (graphOn T A B) f f).sGraph ≤ sT T f := by
  classical
  apply BipartiteGraph.sGraph_mono
  · intro a ha
    exact ha.2
  · intro b hb
    exact hb.2
  · intro a b h
    simp only [coverGraph, graphOn, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hT, -⟩, hfa⟩, hfb⟩ := h
    simp [graphOfFun, hT, hfa, hfb]

/-- Division by `s^χ` can be removed in the final step of Proposition 2. -/
theorem div_rpow_le_of_rpow_le_mul {a s L χ : ℝ} (ha : 0 ≤ a) (hs : 0 < s)
    (h : a ^ χ ≤ L * s ^ χ) : (a / s) ^ χ ≤ L := by
  rw [Real.div_rpow ha (le_of_lt hs)]
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hs χ)]
  exact h

/-- Proposition 2 in the negation-normal-form model: for an admissible monotone
graph exponent `χ`, every formula `F` satisfies
`(s_T(F)/s)^χ ≤ complexity(F)`. -/
theorem proposition2_aux {k n : ℕ}
    (T : (Fin n → Bool) → (Fin n → Bool) → Bool) (χ : ℝ) (hχpos : 0 < χ)
    (hχ : IsMonotoneGraphExponent k χ) (F : NNF k n) :
    (sT T F.eval / sVarBound n T) ^ χ ≤ (F.complexity : ℝ) := by
  classical
  by_cases hs : sVarBound n T = 0
  · rw [hs, div_zero, Real.zero_rpow (ne_of_gt hχpos)]
    positivity
  · have hs0 : 0 < sVarBound n T :=
      lt_of_le_of_ne (sVarBound_nonneg T) (Ne.symm hs)
    induction F with
    | const b =>
        rw [NNF.eval_const, sT_const, zero_div, Real.zero_rpow (ne_of_gt hχpos)]
        simp
    | var i sign =>
        have hsT : sT T (NNF.var (k := k) i sign).eval ≤ sVarBound n T := by
          simpa using sT_var_le T i sign
        have hp : sT T (NNF.var (k := k) i sign).eval ^ χ ≤
            (1 : ℝ) * sVarBound n T ^ χ := by
          rw [one_mul]
          exact Real.rpow_le_rpow (sT_nonneg T _) hsT (le_of_lt hχpos)
        calc
          (sT T (NNF.var (k := k) i sign).eval / sVarBound n T) ^ χ ≤ 1 :=
            div_rpow_le_of_rpow_le_mul (sT_nonneg T _) hs0 hp
          _ = ((NNF.var (k := k) i sign).complexity : ℝ) := by simp
    | gate m hm φ args ih =>
        let f : BoolFun n := (NNF.gate m hm φ args).eval
        let fs : Fin m → BoolFun n := fun j => (args j).eval
        have hf : ∀ a : Fin n → Bool, f a = φ (fun j => fs j a) := fun _ => rfl
        obtain ⟨A, B, hAB, hmax⟩ :=
          BipartiteGraph.exists_admissible_eq_sGraph (graphOfFun T f)
        let G : BipartiteGraph (Fin n → Bool) (Fin n → Bool) := graphOn T A B
        have hGwf : G.WellFormed := BipartiteGraph.graphOn_wellFormed A B
        have hGs : G.sGraph = sT T f :=
          sGraph_graphOn_eq_sT T f A B hAB.1 hAB.2 hmax
        have hleft : ∀ a, a ∈ G.left → f a = false := fun a ha => hAB.1 a ha
        have hright : ∀ b, b ∈ G.right → f b = true := fun b hb => hAB.2 b hb
        have hcover : IsMonotoneCover G (fun i => coverGraph G (fs i) (fs i)) :=
          coverGraph_isMonotoneCover G hGwf φ fs f hf hleft hright
        have hsub := hχ m hm (Fin n → Bool) (Fin n → Bool) G
          (fun i => coverGraph G (fs i) (fs i)) hcover
        have hterm : ∀ i : Fin m,
            (coverGraph G (fs i) (fs i)).sGraph ^ χ ≤ (sT T (fs i)) ^ χ := by
          intro i
          exact Real.rpow_le_rpow (BipartiteGraph.sGraph_nonneg _)
            (sGraph_coverGraph_graphOn_le_sT T (fs i) A B) (le_of_lt hχpos)
        have hchain : sT T f ^ χ ≤ ∑ i, sT T (fs i) ^ χ := by
          calc
            sT T f ^ χ = G.sGraph ^ χ := by rw [hGs]
            _ ≤ ∑ i, (coverGraph G (fs i) (fs i)).sGraph ^ χ := hsub
            _ ≤ ∑ i, sT T (fs i) ^ χ := Finset.sum_le_sum (fun i _ => hterm i)
        have hIH : ∀ i : Fin m,
            sT T (fs i) ^ χ ≤ ((args i).complexity : ℝ) * sVarBound n T ^ χ := by
          intro i
          have hi := ih i
          have hdiv : (sT T (fs i) / sVarBound n T) ^ χ =
              sT T (fs i) ^ χ / sVarBound n T ^ χ :=
            Real.div_rpow (sT_nonneg T _) (le_of_lt hs0) χ
          rw [hdiv] at hi
          have hspos : 0 < sVarBound n T ^ χ := Real.rpow_pos_of_pos hs0 χ
          calc
            sT T (fs i) ^ χ =
                (sT T (fs i) ^ χ / sVarBound n T ^ χ) * sVarBound n T ^ χ :=
              (div_mul_cancel₀ _ hspos.ne').symm
            _ ≤ ((args i).complexity : ℝ) * sVarBound n T ^ χ :=
              mul_le_mul_of_nonneg_right hi (le_of_lt hspos)
        have hsum : (∑ i, sT T (fs i) ^ χ) ≤
            (∑ i, ((args i).complexity : ℝ)) * sVarBound n T ^ χ := by
          calc
            (∑ i, sT T (fs i) ^ χ) ≤
                ∑ i, ((args i).complexity : ℝ) * sVarBound n T ^ χ :=
              Finset.sum_le_sum (fun i _ => hIH i)
            _ = (∑ i, ((args i).complexity : ℝ)) * sVarBound n T ^ χ :=
              (Finset.sum_mul _ _ _).symm
        have hpow : sT T f ^ χ ≤ ((NNF.gate m hm φ args).complexity : ℝ) *
            sVarBound n T ^ χ := by
          calc
            sT T f ^ χ ≤ ∑ i, sT T (fs i) ^ χ := hchain
            _ ≤ (∑ i, ((args i).complexity : ℝ)) * sVarBound n T ^ χ := hsum
            _ = ((NNF.gate m hm φ args).complexity : ℝ) * sVarBound n T ^ χ := by
              simp [NNF.complexity, Nat.cast_sum]
        exact div_rpow_le_of_rpow_le_mul (sT_nonneg T f) hs0 hpow

/-- Minimum complexity of a function over the negation-normal-form basis. -/
noncomputable def nnfComplexity (k n : ℕ) (f : BoolFun n) : ℕ :=
  sInf {L : ℕ | ∃ F : NNF k n, F.eval = f ∧ F.complexity = L}

/-- Proposition 2 in its minimum-complexity form. -/
theorem proposition2 {k n : ℕ}
    (T : (Fin n → Bool) → (Fin n → Bool) → Bool) (χ : ℝ) (hχpos : 0 < χ)
    (hχ : IsMonotoneGraphExponent k χ) {f : BoolFun n}
    (hf : ∃ F : NNF k n, F.eval = f) :
    (sT T f / sVarBound n T) ^ χ ≤ (nnfComplexity k n f : ℝ) := by
  classical
  have hne : {L : ℕ | ∃ F : NNF k n, F.eval = f ∧ F.complexity = L}.Nonempty := by
    obtain ⟨F, hF⟩ := hf
    exact ⟨F.complexity, F, hF, rfl⟩
  obtain ⟨F, hF, hL⟩ := Nat.sInf_mem hne
  have h := proposition2_aux T χ hχpos hχ F
  rw [hF] at h
  rw [hL] at h
  simpa [nnfComplexity] using h

/-- The Hamming-neighbour relation as a Boolean edge predicate. -/
def neighborRel {n : ℕ} (x y : Fin n → Bool) : Bool :=
  decide (hammingDist x y = 1)

/-- The values in the definition of sensitivity form a bounded set. -/
theorem sensitivityValues_bddAbove {n : ℕ} (f : BoolFun n) :
    BddAbove (sensitivityValues f) := by
  classical
  let g : Finset (Fin n → Bool) × Finset (Fin n → Bool) → ℝ := fun p =>
    ((neighborPairs p.1 p.2).card : ℝ) ^ 2 /
      ((p.1.card : ℝ) * (p.2.card : ℝ))
  have hsub : sensitivityValues f ⊆ Set.range g := by
    rintro r ⟨N, P, hN, hP, hz, ho, rfl⟩
    refine ⟨(N, P), ?_⟩
    simp [g]
  exact (Set.finite_range g).subset hsub |>.bddAbove

/-- For admissible `X`, `Y`, the edge count in the graph of a Boolean function
under the neighbour relation is the number of neighbouring pairs. -/
theorem edgeCount_graphOfFun_neighbor {n : ℕ} (f : BoolFun n)
    {X : Finset (Fin n → Bool)} {Y : Finset (Fin n → Bool)}
    (hX : ∀ x ∈ X, f x = false) (hY : ∀ y ∈ Y, f y = true) :
    (graphOfFun neighborRel f).edgeCount X Y = (neighborPairs X Y).card := by
  classical
  unfold BipartiteGraph.edgeCount neighborPairs
  congr 1
  apply Finset.filter_congr
  intro q hq
  obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
  simp [graphOfFun, neighborRel, hX q.1 hq1, hY q.2 hq2]

/-- The generalised sensitivity with the neighbour relation is the sensitivity
from Section 1. -/
theorem sT_neighbor_eq_sensitivity {n : ℕ} (f : BoolFun n) :
    sT neighborRel f = sensitivity f := by
  classical
  apply le_antisymm
  · obtain ⟨X, Y, hAdm, hmax⟩ :=
      BipartiteGraph.exists_admissible_eq_sGraph (graphOfFun neighborRel f)
    rw [sT, hmax]
    by_cases hX : X.Nonempty
    · by_cases hY : Y.Nonempty
      · have hval : (graphOfFun neighborRel f).ratio X Y ∈ sensitivityValues f := by
          refine ⟨X, Y, hX, hY, hAdm.1, hAdm.2, ?_⟩
          simp only [BipartiteGraph.ratio, if_pos hAdm]
          rw [edgeCount_graphOfFun_neighbor f hAdm.1 hAdm.2]
        exact le_csSup (sensitivityValues_bddAbove f) hval
      · have hzero : (graphOfFun neighborRel f).ratio X Y = 0 := by
          simp [BipartiteGraph.ratio, hAdm, hY, Finset.not_nonempty_iff_eq_empty.mp hY]
        rw [hzero]
        exact sensitivity_nonneg f
    · have hzero : (graphOfFun neighborRel f).ratio X Y = 0 := by
        simp [BipartiteGraph.ratio, hAdm, hX, Finset.not_nonempty_iff_eq_empty.mp hX]
      rw [hzero]
      exact sensitivity_nonneg f
  · apply Real.sSup_le
    · intro r hr
      obtain ⟨N, P, hN, hP, hz, ho, rfl⟩ := hr
      have hAdm : (graphOfFun neighborRel f).Admissible N P := ⟨hz, ho⟩
      have hle : (graphOfFun neighborRel f).ratio N P ≤
          (graphOfFun neighborRel f).sGraph := by
        unfold BipartiteGraph.sGraph
        exact Finset.le_sup' (fun p : Finset (Fin n → Bool) × Finset (Fin n → Bool) =>
          (graphOfFun neighborRel f).ratio p.1 p.2) (Finset.mem_univ (N, P))
      have hratio : (graphOfFun neighborRel f).ratio N P =
          ((neighborPairs N P).card : ℝ) ^ 2 / ((N.card : ℝ) * (P.card : ℝ)) := by
        simp only [BipartiteGraph.ratio, if_pos hAdm]
        rw [edgeCount_graphOfFun_neighbor f hz ho]
      simpa [sT, hratio] using hle
    · exact BipartiteGraph.sGraph_nonneg _

/-- If two assignments differ in exactly one coordinate and differ at `i`, then
they agree everywhere except `i`. -/
theorem eq_of_hammingDist_eq_one_of_ne {n : ℕ} {x y : Fin n → Bool}
    (h : hammingDist x y = 1) {i : Fin n} (hi : x i ≠ y i) :
    ∀ j, j ≠ i → x j = y j := by
  classical
  unfold hammingDist at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h
  have hmem_i : i ∈ Finset.univ.filter (fun j => x j ≠ y j) := by simp [hi]
  have hai : a = i := by
    have : i ∈ ({a} : Finset (Fin n)) := by rwa [← ha]
    have hia : i = a := by simpa using this
    exact hia.symm
  intro j hj
  by_contra hne
  have hmem_j : j ∈ Finset.univ.filter (fun j => x j ≠ y j) := by simp [hne]
  rw [ha] at hmem_j
  have : j = a := by simpa using hmem_j
  exact hj (this.trans hai)

/-- A signed projection `x ↦ x_i` or `x ↦ ¬x_i`. -/
def signedProj {n : ℕ} (i : Fin n) (sign : Bool) : BoolFun n :=
  fun x => if sign then Bool.not (x i) else x i

theorem signedProj_eq_false {n : ℕ} {i : Fin n} {sign : Bool} {x : Fin n → Bool} :
    signedProj i sign x = false ↔ (if sign then x i = true else x i = false) := by
  cases sign <;> simp [signedProj]

theorem signedProj_eq_true {n : ℕ} {i : Fin n} {sign : Bool} {x : Fin n → Bool} :
    signedProj i sign x = true ↔ (if sign then x i = false else x i = true) := by
  cases sign <;> simp [signedProj]

theorem signedProj_ne_of_false_true {n : ℕ} {i : Fin n} {sign : Bool}
    {x y : Fin n → Bool} (hx : signedProj i sign x = false)
    (hy : signedProj i sign y = true) : x i ≠ y i := by
  rw [signedProj_eq_false] at hx
  rw [signedProj_eq_true] at hy
  cases sign <;> simp_all

theorem neighborPairs_fst_injOn_signedProj {n : ℕ} (i : Fin n) (sign : Bool)
    {N P : Finset (Fin n → Bool)}
    (hN : ∀ x ∈ N, signedProj i sign x = false)
    (hP : ∀ y ∈ P, signedProj i sign y = true) :
    Set.InjOn Prod.fst (↑(neighborPairs N P) :
      Set ((Fin n → Bool) × (Fin n → Bool))) := by
  classical
  rintro ⟨x1, y1⟩ hq1 ⟨x2, y2⟩ hq2 hfst
  simp only [Prod.fst] at hfst
  subst x2
  obtain ⟨hq1prod, hq1hd⟩ := Finset.mem_filter.mp hq1
  obtain ⟨hq2prod, hq2hd⟩ := Finset.mem_filter.mp hq2
  obtain ⟨hxN, hy1P⟩ := Finset.mem_product.mp hq1prod
  obtain ⟨-, hy2P⟩ := Finset.mem_product.mp hq2prod
  have hne1 : x1 i ≠ y1 i :=
    signedProj_ne_of_false_true (hN x1 hxN) (hP y1 hy1P)
  have hne2 : x1 i ≠ y2 i :=
    signedProj_ne_of_false_true (hN x1 hxN) (hP y2 hy2P)
  have hy : y1 = y2 := by
    funext j
    by_cases hj : j = i
    · subst j
      have h1 := (signedProj_eq_true (i := i) (sign := sign) (x := y1)).mp (hP y1 hy1P)
      have h2 := (signedProj_eq_true (i := i) (sign := sign) (x := y2)).mp (hP y2 hy2P)
      cases sign <;> simp_all
    · calc
        y1 j = x1 j := (eq_of_hammingDist_eq_one_of_ne hq1hd hne1 j hj).symm
        _ = y2 j := eq_of_hammingDist_eq_one_of_ne hq2hd hne2 j hj
  rw [hy]

theorem neighborPairs_snd_injOn_signedProj {n : ℕ} (i : Fin n) (sign : Bool)
    {N P : Finset (Fin n → Bool)}
    (hN : ∀ x ∈ N, signedProj i sign x = false)
    (hP : ∀ y ∈ P, signedProj i sign y = true) :
    Set.InjOn Prod.snd (↑(neighborPairs N P) :
      Set ((Fin n → Bool) × (Fin n → Bool))) := by
  classical
  rintro ⟨x1, y1⟩ hq1 ⟨x2, y2⟩ hq2 hfst
  simp only [Prod.snd] at hfst
  subst y2
  obtain ⟨hq1prod, hq1hd⟩ := Finset.mem_filter.mp hq1
  obtain ⟨hq2prod, hq2hd⟩ := Finset.mem_filter.mp hq2
  obtain ⟨hx1N, hy1P⟩ := Finset.mem_product.mp hq1prod
  obtain ⟨hx2N, -⟩ := Finset.mem_product.mp hq2prod
  have hne1 : x1 i ≠ y1 i :=
    signedProj_ne_of_false_true (hN x1 hx1N) (hP y1 hy1P)
  have hne2 : x2 i ≠ y1 i :=
    signedProj_ne_of_false_true (hN x2 hx2N) (hP y1 hy1P)
  have hx : x1 = x2 := by
    funext j
    by_cases hj : j = i
    · subst j
      have h1 := (signedProj_eq_false (i := i) (sign := sign) (x := x1)).mp (hN x1 hx1N)
      have h2 := (signedProj_eq_false (i := i) (sign := sign) (x := x2)).mp (hN x2 hx2N)
      cases sign <;> simp_all
    · calc
        x1 j = y1 j := eq_of_hammingDist_eq_one_of_ne hq1hd hne1 j hj
        _ = x2 j := (eq_of_hammingDist_eq_one_of_ne hq2hd hne2 j hj).symm
  rw [hx]

theorem neighborPairs_card_le_left {n : ℕ} (i : Fin n) (sign : Bool)
    {N P : Finset (Fin n → Bool)}
    (hN : ∀ x ∈ N, signedProj i sign x = false)
    (hP : ∀ y ∈ P, signedProj i sign y = true) :
    (neighborPairs N P).card ≤ N.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro q hq
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
  · exact neighborPairs_fst_injOn_signedProj i sign hN hP

theorem neighborPairs_card_le_right {n : ℕ} (i : Fin n) (sign : Bool)
    {N P : Finset (Fin n → Bool)}
    (hN : ∀ x ∈ N, signedProj i sign x = false)
    (hP : ∀ y ∈ P, signedProj i sign y = true) :
    (neighborPairs N P).card ≤ P.card := by
  apply Finset.card_le_card_of_injOn Prod.snd
  · intro q hq
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).2
  · exact neighborPairs_snd_injOn_signedProj i sign hN hP

/-- A signed projection has sensitivity at most one. -/
theorem sensitivity_signedProj_le_one {n : ℕ} (i : Fin n) (sign : Bool) :
    sensitivity (signedProj i sign) ≤ 1 := by
  classical
  apply Real.sSup_le
  · rintro r ⟨N, P, hNne, hPne, hN, hP, rfl⟩
    have hcN : (neighborPairs N P).card ≤ N.card :=
      neighborPairs_card_le_left i sign hN hP
    have hcP : (neighborPairs N P).card ≤ P.card :=
      neighborPairs_card_le_right i sign hN hP
    have hcN' : ((neighborPairs N P).card : ℝ) ≤ (N.card : ℝ) := by exact_mod_cast hcN
    have hcP' : ((neighborPairs N P).card : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast hcP
    have hc0 : (0 : ℝ) ≤ (neighborPairs N P).card := by positivity
    have hsq : ((neighborPairs N P).card : ℝ) ^ 2 ≤
        (N.card : ℝ) * (P.card : ℝ) := by
      nlinarith
    have hden : 0 < (N.card : ℝ) * (P.card : ℝ) := by
      have hN0 : 0 < (N.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hNne
      have hP0 : 0 < (P.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hPne
      positivity
    exact (div_le_one hden).mpr hsq
  · norm_num

/-- A signed projection has sensitivity at least one. -/
theorem sensitivity_signedProj_ge_one {n : ℕ} (i : Fin n) (sign : Bool) :
    1 ≤ sensitivity (signedProj i sign) := by
  classical
  let x0 : Fin n → Bool := fun _ => sign
  have hzero : signedProj i sign x0 = false := by
    cases sign <;> simp [signedProj, x0]
  let y : Fin n → Bool := Function.update x0 i (Bool.not sign)
  have hy : signedProj i sign y = true := by
    cases sign <;> simp [signedProj, y, x0]
  have hhd : hammingDist x0 y = 1 := by
    unfold hammingDist
    have hset : (Finset.univ.filter (fun j => x0 j ≠ y j)) = {i} := by
      ext j
      simp [y, x0, Function.update, eq_comm]
    rw [hset]
    simp
  have hval : (1 : ℝ) ∈ sensitivityValues (signedProj i sign) := by
    refine ⟨{x0}, {y}, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · intro x hx
      rw [show x = x0 by simpa using hx]
      exact hzero
    · intro z hz
      rw [show z = y by simpa using hz]
      exact hy
    · have hfilter : (({(x0, y)} : Finset ((Fin n → Bool) × (Fin n → Bool))).filter (fun q =>
          hammingDist q.1 q.2 = 1)) = {(x0, y)} := by
        apply Finset.filter_true_of_mem
        intro q hq
        simp only [Finset.mem_singleton] at hq
        subst q
        exact hhd
      simp [neighborPairs, hfilter]
  exact le_csSup (sensitivityValues_bddAbove _) hval

theorem sensitivity_signedProj {n : ℕ} (i : Fin n) (sign : Bool) :
    sensitivity (signedProj i sign) = 1 :=
  le_antisymm (sensitivity_signedProj_le_one i sign)
    (sensitivity_signedProj_ge_one i sign)

/-- For the neighbour relation and at least one variable, the denominator bound
`s` from (2.2) equals one. -/
theorem sVarBound_neighbor_eq_one {n : ℕ} (hn : 0 < n) :
    sVarBound n neighborRel = 1 := by
  classical
  let i : Fin n := ⟨0, hn⟩
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨i, Finset.mem_univ i⟩
  rw [sVarBound_eq_sup' neighborRel hne]
  apply le_antisymm
  · apply Finset.sup'_le
    intro j _
    have h1 : sT neighborRel (fun x : Fin n → Bool => x j) = 1 := by
      rw [sT_neighbor_eq_sensitivity]
      convert sensitivity_signedProj j false using 2
      funext x
      simp [signedProj]
    have h2 : sT neighborRel (fun x : Fin n → Bool => Bool.not (x j)) = 1 := by
      rw [sT_neighbor_eq_sensitivity]
      convert sensitivity_signedProj j true using 2
      funext x
      simp [signedProj]
    simp [h1, h2]
  · have h1 : sT neighborRel (fun x : Fin n → Bool => x i) = 1 := by
      rw [sT_neighbor_eq_sensitivity]
      convert sensitivity_signedProj i false using 2
      funext x
      simp [signedProj]
    have h2 : sT neighborRel (fun x : Fin n → Bool => Bool.not (x i)) = 1 := by
      rw [sT_neighbor_eq_sensitivity]
      convert sensitivity_signedProj i true using 2
      funext x
      simp [signedProj]
    calc
      (1 : ℝ) = max (sT neighborRel (fun x : Fin n → Bool => x i))
          (sT neighborRel (fun x : Fin n → Bool => Bool.not (x i))) := by
        simp [h1, h2]
      _ ≤ (Finset.univ : Finset (Fin n)).sup' hne
          (fun j => max (sT neighborRel (fun x : Fin n → Bool => x j))
            (sT neighborRel (fun x : Fin n → Bool => Bool.not (x j)))) :=
        Finset.le_sup' (s := (Finset.univ : Finset (Fin n)))
          (f := fun j => max (sT neighborRel (fun x : Fin n → Bool => x j))
            (sT neighborRel (fun x : Fin n → Bool => Bool.not (x j))))
          (b := i) (Finset.mem_univ i)

/-- The Khrapchenko inequality for the normal-form basis: every expressible
function satisfies `s(f)^χ ≤ L(f)`. -/
def KhrapchenkoBoundNNF (k : ℕ) (χ : ℝ) : Prop :=
  ∀ (n : ℕ) (f : BoolFun n), (∃ F : NNF k n, F.eval = f) →
    sensitivity f ^ χ ≤ (nnfComplexity k n f : ℝ)

/-- The pointwise form of the second inequality in Proposition 1: every
admissible monotone graph exponent is a Khrapchenko exponent for the
normal-form basis. -/
theorem proposition1_second_pointwise {k : ℕ} (hk : 2 ≤ k) {χ : ℝ}
    (hχpos : 0 < χ) (hχ : IsMonotoneGraphExponent k χ) :
    KhrapchenkoBoundNNF k χ := by
  intro n f hf
  by_cases hn : n = 0
  · subst n
    have huniq : ∀ x : Fin 0 → Bool, x = fun _ => false := by
      intro x
      funext i
      exact Fin.elim0 i
    have hconst : f = fun _ => f (fun _ => false) := by
      funext x
      rw [huniq x]
    rw [hconst, sensitivity_const, Real.zero_rpow (ne_of_gt hχpos)]
    positivity
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have h := proposition2 neighborRel χ hχpos hχ hf
    rw [sT_neighbor_eq_sensitivity, sVarBound_neighbor_eq_one hnpos] at h
    simpa using h

/-- The pointwise content of Proposition 1: every exponent admissible for
covers of bipartite graphs is a Khrapchenko exponent for the normal-form basis.
The first inequality is `isMonotoneGraphExponent_of_isGraphExponent`; the second
is Proposition 2. -/
theorem proposition1_pointwise {k : ℕ} (hk : 2 ≤ k) {χ : ℝ}
    (hχpos : 0 < χ) (hχ : IsGraphExponent k χ) :
    KhrapchenkoBoundNNF k χ :=
  proposition1_second_pointwise hk hχpos
    (isMonotoneGraphExponent_of_isGraphExponent hχ)

/-- The graph-of-a-function identity from Section 2: for the Hamming-neighbour
relation, `s(G_f) = s(f)`. -/
theorem sGraph_graphOfFun_neighbor {n : ℕ} (f : BoolFun n) :
    (graphOfFun neighborRel f).sGraph = sensitivity f :=
  sT_neighbor_eq_sensitivity f

/-- The pointwise form of the first inequality in Proposition 1: every graph
exponent is a monotone graph exponent. -/
theorem proposition1_first_pointwise {k : ℕ} {χ : ℝ}
    (hχ : IsGraphExponent k χ) : IsMonotoneGraphExponent k χ :=
  isMonotoneGraphExponent_of_isGraphExponent hχ

/-! ### Unate functions as signed monotone functions -/

section Unate

variable {m : ℕ}

/-- Flip the coordinates of `y` where `σ` is `true`. -/
def signFlip (σ y : Fin m → Bool) : Fin m → Bool :=
  fun i => if σ i then !y i else y i

@[simp]
theorem signFlip_true {σ y : Fin m → Bool} {i : Fin m} (h : σ i = true) :
    signFlip σ y i = !y i := by
  simp [signFlip, h]

@[simp]
theorem signFlip_false {σ y : Fin m → Bool} {i : Fin m} (h : σ i = false) :
    signFlip σ y i = y i := by
  simp [signFlip, h]

/-- Flipping twice in the same coordinates is the identity. -/
theorem signFlip_flip (σ y : Fin m → Bool) : signFlip σ (signFlip σ y) = y := by
  funext i
  cases h : σ i with
  | true => simp [signFlip, h]
  | false => simp [signFlip, h]

/-- The sign vector of a unate function: `true` in the coordinates where the
function is nonincreasing. -/
noncomputable def unateSign (g : BoolFun m) (_hg : Unate g) (i : Fin m) : Bool := by
  classical
  exact if NondecreasingIn g i then false else true

/-- The sign vector records the correct monotonicity direction in each
coordinate. -/
theorem unateSign_spec {g : BoolFun m} (hg : Unate g) (i : Fin m) :
    (unateSign g hg i = false → NondecreasingIn g i) ∧
      (unateSign g hg i = true → NonincreasingIn g i) := by
  classical
  by_cases h : NondecreasingIn g i
  · have hs : unateSign g hg i = false := by simp [unateSign, h]
    rw [hs]
    exact ⟨fun _ => h, by simp⟩
  · have hin : NonincreasingIn g i := (hg i).resolve_left h
    have hs : unateSign g hg i = true := by simp [unateSign, h]
    rw [hs]
    exact ⟨by simp, fun _ => hin⟩

/-- `mixUp w x y` is `x` with the first `w` coordinates replaced by those of `y`. -/
def mixUp {m : ℕ} (w : ℕ) (x y : Fin m → Bool) : Fin m → Bool :=
  fun i => if i.val < w then y i else x i

@[simp]
theorem mixUp_zero {m : ℕ} (x y : Fin m → Bool) : mixUp 0 x y = x := by
  funext i
  simp [mixUp]

@[simp]
theorem mixUp_self {m : ℕ} (x y : Fin m → Bool) : mixUp m x y = y := by
  funext i
  simp [mixUp, i.isLt]

theorem mixUp_succ_apply_left {m : ℕ} {x y : Fin m → Bool} {w : ℕ} (hw : w < m) :
    mixUp (w + 1) x y ⟨w, hw⟩ = y ⟨w, hw⟩ := by
  simp [mixUp]

theorem mixUp_apply_left {m : ℕ} {x y : Fin m → Bool} {w : ℕ} (hw : w < m) :
    mixUp w x y ⟨w, hw⟩ = x ⟨w, hw⟩ := by
  simp [mixUp]

theorem mixUp_succ_apply_of_ne {m : ℕ} {x y : Fin m → Bool} {w : ℕ} (hw : w < m)
    {i : Fin m} (hi : i ≠ ⟨w, hw⟩) :
    mixUp (w + 1) x y i = mixUp w x y i := by
  simp only [mixUp]
  have hlt : i.val < w + 1 ↔ i.val < w := by
    constructor
    · intro h
      rcases Nat.lt_succ_iff_lt_or_eq.mp h with h' | h'
      · exact h'
      · exact absurd (Fin.ext h') hi
    · exact Nat.lt_succ_of_lt
  by_cases h : i.val < w
  · have h2 : i.val < w + 1 := hlt.mpr h
    simp [h, h2]
  · have h2 : ¬ i.val < w + 1 := fun hc => h (hlt.mp hc)
    simp [h, h2]

/-- Chaining the one-coordinate monotonicity directions of a unate function
along the path from `x` to `y`. -/
theorem chain_le {g : BoolFun m} {σ : Fin m → Bool}
    (hσ : ∀ i, (σ i = false → NondecreasingIn g i) ∧ (σ i = true → NonincreasingIn g i))
    {x y : Fin m → Bool}
    (hxy : ∀ i, (σ i = false → x i ≤ y i) ∧ (σ i = true → y i ≤ x i)) :
    g x ≤ g y := by
  have hstep : ∀ w < m, g (mixUp w x y) ≤ g (mixUp (w + 1) x y) := by
    intro w hw'
    let c : Fin m := ⟨w, hw'⟩
    by_cases hc : σ c = true
    · apply (hσ c).2 hc
      · intro i hi
        exact (mixUp_succ_apply_of_ne hw' hi).symm
      · rw [mixUp_succ_apply_left hw', mixUp_apply_left hw']
        exact (hxy c).2 hc
    · have hc' : σ c = false := by
        cases hs : σ c with
        | true => exact absurd hs hc
        | false => rfl
      apply (hσ c).1 hc'
      · intro i hi
        exact (mixUp_succ_apply_of_ne hw' hi).symm
      · rw [mixUp_apply_left hw', mixUp_succ_apply_left hw']
        exact (hxy c).1 hc'
  have key : ∀ w ≤ m, g (mixUp 0 x y) ≤ g (mixUp w x y) := by
    intro w hw
    induction w with
    | zero => exact le_rfl
    | succ w ih =>
        exact le_trans (ih (Nat.le_of_succ_le hw)) (hstep w (by omega))
  simpa using key m (le_rfl)

/-- A unate function becomes monotone after flipping the coordinates in which
it is nonincreasing. -/
noncomputable def unateMonotone (g : BoolFun m) (hg : Unate g) : MonotoneFun m where
  toFun y := g (signFlip (unateSign g hg) y)
  monotone := by
    intro y y' hyy'
    apply chain_le (hσ := unateSign_spec hg)
    intro i
    constructor
    · intro h
      simpa [signFlip, h] using hyy' i
    · intro h
      simpa [signFlip, h] using MonotoneFun.bool_not_le_not (hyy' i)

/-- Flipping back recovers the original unate function. -/
theorem unateMonotone_flip (g : BoolFun m) (hg : Unate g) (x : Fin m → Bool) :
    unateMonotone g hg (signFlip (unateSign g hg) x) = g x := by
  simp only [unateMonotone, signFlip_flip]

end Unate

/-! ### From `U_k`-formulas to negation normal form -/

/-- Negation as a basis function. -/
def notFun : BasisFunction := ⟨1, fun x => !x 0⟩

theorem notFun_mem_Uk {k : ℕ} (hk : 1 ≤ k) : notFun ∈ Uk k := not_mem_Uk hk

theorem notFun_notConstant : ¬ notFun.IsConstant := by
  rintro ⟨b, hb⟩
  have h0 : b = true := by
    simpa [notFun] using (hb (fun _ => false)).symm
  have h1 : b = false := by
    simpa [notFun] using (hb (fun _ => true)).symm
  rw [h0] at h1
  exact Bool.noConfusion h1

variable {k n : ℕ}

/-- Translate a formula over `Uk k` into negation normal form, preserving the
realized function and the complexity. -/
noncomputable def Formula.toNNF : Formula (Uk k) n → NNF k n
  | Formula.const b _ => NNF.const b
  | Formula.var i => NNF.var i false
  | Formula.app g hg _ args =>
      NNF.gate g.1 hg.1 (unateMonotone g.2 hg.2)
        (fun j => if unateSign g.2 hg.2 j then (Formula.toNNF (args j)).neg
          else Formula.toNNF (args j))

theorem Formula.toNNF_eval (F : Formula (Uk k) n) : F.toNNF.eval = F.eval := by
  induction F with
  | const b hb => rfl
  | var i => rfl
  | app g hg h args ih =>
      funext x
      have hfun : (fun j => (if unateSign g.2 hg.2 j then (Formula.toNNF (args j)).neg
            else Formula.toNNF (args j)).eval x)
          = signFlip (unateSign g.2 hg.2) (fun j => (args j).eval x) := by
        funext j
        by_cases hj : unateSign g.2 hg.2 j = true
        · simp [signFlip, hj, NNF.eval_neg, ih j]
        · have hf : unateSign g.2 hg.2 j = false := by cases hs : unateSign g.2 hg.2 j <;> simp_all
          simp [signFlip, hf, ih j]
      simp only [Formula.toNNF, NNF.eval, Formula.eval_app]
      rw [hfun, unateMonotone_flip]

theorem Formula.toNNF_complexity (F : Formula (Uk k) n) :
    F.toNNF.complexity = F.complexity := by
  induction F with
  | const b hb => rfl
  | var i => rfl
  | app g hg h args ih =>
      simp only [Formula.toNNF, NNF.complexity, Formula.complexity_app]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : unateSign g.2 hg.2 j = true
      · simp [hj, NNF.complexity_neg, ih j]
      · have hf : unateSign g.2 hg.2 j = false := by cases hs : unateSign g.2 hg.2 j <;> simp_all
        simp [hf, ih j]

/-! ### From negation normal form to `U_k`-formulas -/

/-- A monotone function is unate. -/
theorem unate_of_monotone {m : ℕ} (φ : MonotoneFun m) : Unate φ.toFun := by
  intro i
  left
  intro x y hxy hle
  apply φ.monotone
  intro j
  by_cases hj : j = i
  · subst hj
    exact hle
  · exact le_of_eq (hxy j hj)

/-- Translate a negation-normal-form formula into a formula over `Uk k`.  The
translation does not increase the complexity (constant gates are collapsed to
constant leaves). -/
noncomputable def NNF.toFormula {k : ℕ} (hk : 1 ≤ k) : NNF k n → Formula (Uk k) n
  | NNF.const b => Formula.const b (constantIn_Uk k b)
  | NNF.var i sign =>
      if sign then
        Formula.app notFun (notFun_mem_Uk hk) notFun_notConstant (fun _ => Formula.var i)
      else Formula.var i
  | NNF.gate m hm φ args =>
      if h : ∃ b : Bool, ∀ x : Fin m → Bool, φ x = b then
        Formula.const (Classical.choose h) (constantIn_Uk k _)
      else
        Formula.app ⟨m, φ.toFun⟩ ⟨hm, unate_of_monotone φ⟩
          (by
            intro hc
            exact h hc)
          (fun j => NNF.toFormula hk (args j))

theorem NNF.toFormula_eval {k : ℕ} (hk : 1 ≤ k) (G : NNF k n) :
    (G.toFormula hk).eval = G.eval := by
  induction G with
  | const b => rfl
  | var i sign =>
      funext x
      cases sign
      · rfl
      · rfl
  | gate m hm φ args ih =>
      funext x
      by_cases h : ∃ b : Bool, ∀ y : Fin m → Bool, φ y = b
      · rw [NNF.toFormula, dite_eq_left h]
        show Classical.choose h = φ.toFun (fun j => (args j).eval x)
        exact (Classical.choose_spec h _).symm
      · rw [NNF.toFormula, dite_eq_right h]
        show φ.toFun (fun j => (NNF.toFormula hk (args j)).eval x)
            = φ.toFun (fun j => (args j).eval x)
        congr 1
        funext j
        exact congrFun (ih j) x

theorem NNF.toFormula_complexity {k : ℕ} (hk : 1 ≤ k) (G : NNF k n) :
    (G.toFormula hk).complexity ≤ G.complexity := by
  induction G with
  | const b => simp [NNF.toFormula]
  | var i sign =>
      cases sign
      · simp [NNF.toFormula]
      · show (Formula.app notFun (notFun_mem_Uk hk) notFun_notConstant
            (fun _ => Formula.var i)).complexity ≤ 1
        rw [Formula.complexity_app]
        show (Finset.univ : Finset (Fin notFun.fst)).card ≤ 1
        rw [notFun]
        simp
  | gate m hm φ args ih =>
      by_cases h : ∃ b : Bool, ∀ y : Fin m → Bool, φ y = b
      · rw [NNF.toFormula, dite_eq_left h]
        simp [NNF.complexity]
      · rw [NNF.toFormula, dite_eq_right h]
        simp only [NNF.complexity]
        exact Finset.sum_le_sum (fun j _ => ih j)

/-! ### Equivalence of the minimum complexities -/

/-- The `NNF` minimum complexity is at most the `U_k` minimum complexity. -/
theorem nnfComplexity_le_complexity_Uk {k n : ℕ} {f : BoolFun n}
    (hf : Expressible (Uk k) f) : nnfComplexity k n f ≤ complexity (Uk k) f := by
  classical
  unfold nnfComplexity complexity
  obtain ⟨F, hF, hL⟩ := Nat.sInf_mem
    (s := {L : ℕ | ∃ F : Formula (Uk k) n, F.eval = f ∧ F.complexity = L})
    (exists_complexity_of_expressible hf)
  rw [← hL, ← hF]
  exact Nat.sInf_le ⟨F.toNNF, F.toNNF_eval, F.toNNF_complexity⟩

/-- The `U_k` minimum complexity is at most the `NNF` minimum complexity. -/
theorem complexity_le_nnfComplexity {k n : ℕ} (hk : 1 ≤ k) {f : BoolFun n}
    (hf : ∃ G : NNF k n, G.eval = f) :
    complexity (Uk k) f ≤ nnfComplexity k n f := by
  classical
  unfold complexity nnfComplexity
  obtain ⟨G, hG, hL⟩ := Nat.sInf_mem
    (s := {L : ℕ | ∃ G : NNF k n, G.eval = f ∧ G.complexity = L})
    (by obtain ⟨G, hG⟩ := hf; exact ⟨G.complexity, G, hG, rfl⟩)
  rw [← hL, ← hG]
  exact le_trans
    (complexity_le_of_eval (F := G.toFormula hk) (G.toFormula_eval hk))
    (G.toFormula_complexity hk)

/-- The two minimum complexities agree for functions expressible over `Uk k`. -/
theorem complexity_eq_nnfComplexity {k n : ℕ} (hk : 1 ≤ k) {f : BoolFun n}
    (hf : Expressible (Uk k) f) :
    complexity (Uk k) f = nnfComplexity k n f := by
  apply le_antisymm
  · apply complexity_le_nnfComplexity hk
    obtain ⟨F, hF⟩ := hf
    exact ⟨F.toNNF, by rw [F.toNNF_eval, hF]⟩
  · exact nnfComplexity_le_complexity_Uk hf

/-- A function is expressible over `Uk k` exactly when it has a formula in
negation normal form. -/
theorem expressible_iff_nnf {k n : ℕ} (hk : 1 ≤ k) {f : BoolFun n} :
    Expressible (Uk k) f ↔ ∃ G : NNF k n, G.eval = f := by
  constructor
  · rintro ⟨F, hF⟩
    exact ⟨F.toNNF, by rw [F.toNNF_eval, hF]⟩
  · rintro ⟨G, hG⟩
    exact ⟨G.toFormula hk, by rw [G.toFormula_eval, hG]⟩

/-- Proposition 1 for `Uk k`: every graph exponent is a Khrapchenko exponent
for the unate basis `Uk k`. -/
theorem khrapchenkoBound_Uk {k : ℕ} (hk : 2 ≤ k) {χ : ℝ} (hχpos : 0 < χ)
    (hχ : IsGraphExponent k χ) : KhrapchenkoBound (Uk k) χ := by
  intro n f hf
  obtain ⟨F, hF⟩ := hf
  have hnnf : ∃ G : NNF k n, G.eval = f := ⟨F.toNNF, by rw [F.toNNF_eval, hF]⟩
  have h := proposition1_pointwise hk hχpos hχ n f hnnf
  rw [← complexity_eq_nnfComplexity (by omega : 1 ≤ k) ⟨F, hF⟩] at h
  exact h


theorem mod_two_add_one (m : ℕ) : (m + 1) % 2 = 1 ↔ m % 2 = 0 := by omega

theorem mod_two_sub_one {m : ℕ} (hm : 0 < m) : (m - 1) % 2 = 1 ↔ m % 2 = 0 := by omega

/-- Flip the value of the assignment `x` at coordinate `i`. -/
def bitFlip {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)

theorem bitFlip_self {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    bitFlip x i i = !x i := by
  simp [bitFlip]

theorem bitFlip_of_ne {n : ℕ} {x : Fin n → Bool} {i j : Fin n} (h : j ≠ i) :
    bitFlip x i j = x j := by
  simp only [bitFlip]
  exact Function.update_of_ne h _ _

theorem bitFlip_involutive {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    bitFlip (bitFlip x i) i = x := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [bitFlip_self, bitFlip_self]
    simp
  · rw [bitFlip_of_ne hj, bitFlip_of_ne hj]

theorem bitFlip_injective {n : ℕ} (x : Fin n → Bool) : Function.Injective (bitFlip x) := by
  intro i j h
  by_contra hne
  have h2 : bitFlip x j i = x i := bitFlip_of_ne hne
  have h1 : bitFlip x i i = !x i := bitFlip_self x i
  have := congrFun h i
  rw [h1, h2] at this
  cases x i <;> simp_all

theorem bitFlip_injective_left {n : ℕ} (i : Fin n) :
    Function.Injective (fun x : Fin n → Bool => bitFlip x i) := by
  intro x y h
  have := congrArg (fun z => bitFlip z i) h
  simpa [bitFlip_involutive] using this

theorem hammingDist_symm {n : ℕ} (x y : Fin n → Bool) : hammingDist x y = hammingDist y x := by
  unfold hammingDist
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ne_comm

theorem hammingDist_bitFlip {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    hammingDist x (bitFlip x i) = 1 := by
  classical
  unfold hammingDist
  have hset : (Finset.univ.filter fun j => x j ≠ bitFlip x i j) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases hj : j = i
    · subst hj
      simp [bitFlip_self]
    · rw [bitFlip_of_ne hj]
      simp [hj]
  rw [hset]
  simp

theorem eq_bitFlip_of_hammingDist_eq_one {n : ℕ} {x y : Fin n → Bool}
    (h : hammingDist x y = 1) : ∃ i, y = bitFlip x i := by
  classical
  unfold hammingDist at h
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp h
  refine ⟨k, ?_⟩
  funext j
  by_cases hj : j = k
  · subst k
    have hmem : j ∈ Finset.univ.filter (fun i => x i ≠ y i) := by
      rw [hk]; simp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    cases hx : x j <;> cases hy : y j <;> simp_all [bitFlip_self]
  · have hnotmem : j ∉ Finset.univ.filter (fun i => x i ≠ y i) := by
      rw [hk]; simp [hj]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hnotmem
    rw [bitFlip_of_ne hj, hnotmem]

/-- The number of `true` coordinates of an assignment (`bitWeight x` is the
Hamming weight of `x`). -/
def bitWeight {n : ℕ} (x : Fin n → Bool) : ℕ := (Finset.univ.filter fun i => x i).card

theorem linearFun_eq_decide {n : ℕ} (x : Fin n → Bool) :
    linearFun n x = decide (bitWeight x % 2 = 1) := rfl

theorem bitWeight_bitFlip_of_true {n : ℕ} {x : Fin n → Bool} {i : Fin n}
    (h : x i = true) : bitWeight (bitFlip x i) = bitWeight x - 1 := by
  classical
  unfold bitWeight
  have hset : (Finset.univ.filter fun j => bitFlip x i j) =
      (Finset.univ.filter fun j => x j).erase i := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    by_cases hj : j = i
    · subst hj; simp [bitFlip_self, h]
    · rw [bitFlip_of_ne hj]; simp [hj]
  rw [hset, Finset.card_erase_of_mem (by simp [h])]

theorem bitWeight_bitFlip_of_false {n : ℕ} {x : Fin n → Bool} {i : Fin n}
    (h : x i = false) : bitWeight (bitFlip x i) = bitWeight x + 1 := by
  classical
  unfold bitWeight
  have hset : (Finset.univ.filter fun j => bitFlip x i j) =
      insert i (Finset.univ.filter fun j => x j) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hj : j = i
    · subst hj; simp [bitFlip_self, h]
    · rw [bitFlip_of_ne hj]; simp [hj]
  rw [hset, Finset.card_insert_of_notMem (by simp [h])]

theorem linearFun_bitFlip {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    linearFun n (bitFlip x i) = !linearFun n x := by
  rw [linearFun_eq_decide, linearFun_eq_decide]
  cases hx : x i
  · rw [bitWeight_bitFlip_of_false hx]
    by_cases hpar : bitWeight x % 2 = 1
    · have : ¬ ((bitWeight x + 1) % 2 = 1) := by rw [mod_two_add_one]; omega
      simp [hpar, this]
    · have : (bitWeight x + 1) % 2 = 1 := by rw [mod_two_add_one]; omega
      simp [hpar, this]
  · rw [bitWeight_bitFlip_of_true hx]
    have hpos : 0 < bitWeight x := by
      unfold bitWeight
      exact Finset.card_pos.mpr ⟨i, by simp [hx]⟩
    by_cases hpar : bitWeight x % 2 = 1
    · have : ¬ ((bitWeight x - 1) % 2 = 1) := by rw [mod_two_sub_one hpos]; omega
      simp [hpar, this]
    · have : (bitWeight x - 1) % 2 = 1 := by rw [mod_two_sub_one hpos]; omega
      simp [hpar, this]

/-- The assignments of even parity, i.e. the fibre `l_n^{-1}(0)`. -/
def evenVecs (n : ℕ) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun x => linearFun n x = false

/-- The assignments of odd parity, i.e. the fibre `l_n^{-1}(1)`. -/
def oddVecs (n : ℕ) : Finset (Fin n → Bool) :=
  Finset.univ.filter fun x => linearFun n x = true

@[simp]
theorem mem_evenVecs {n : ℕ} {x : Fin n → Bool} :
    x ∈ evenVecs n ↔ linearFun n x = false := by
  simp [evenVecs]

@[simp]
theorem mem_oddVecs {n : ℕ} {x : Fin n → Bool} :
    x ∈ oddVecs n ↔ linearFun n x = true := by
  simp [oddVecs]

theorem const_false_linearFun {n : ℕ} : linearFun n (fun _ => false) = false := by
  rw [linearFun_eq_decide]
  unfold bitWeight
  simp

theorem evenVecs_nonempty (n : ℕ) : (evenVecs n).Nonempty :=
  ⟨fun _ => false, by simp [const_false_linearFun]⟩

theorem oddVecs_nonempty {n : ℕ} (hn : 0 < n) : (oddVecs n).Nonempty := by
  refine ⟨bitFlip (fun _ => false) ⟨0, hn⟩, ?_⟩
  rw [mem_oddVecs, linearFun_bitFlip, const_false_linearFun]
  rfl

theorem bitFlip_mem_odd {n : ℕ} {x : Fin n → Bool} (hx : linearFun n x = false)
    (i : Fin n) : bitFlip x i ∈ oddVecs n := by
  rw [mem_oddVecs, linearFun_bitFlip, hx]
  rfl

theorem bitFlip_mem_even {n : ℕ} {x : Fin n → Bool} (hx : linearFun n x = true)
    (i : Fin n) : bitFlip x i ∈ evenVecs n := by
  rw [mem_evenVecs, linearFun_bitFlip, hx]
  rfl

theorem evenVecs_card_eq_oddVecs_card {n : ℕ} (hn : 0 < n) :
    (evenVecs n).card = (oddVecs n).card := by
  classical
  let i0 : Fin n := ⟨0, hn⟩
  apply le_antisymm
  · calc (evenVecs n).card = ((evenVecs n).image (fun x => bitFlip x i0)).card := by
          rw [Finset.card_image_of_injective _ (bitFlip_injective_left i0)]
      _ ≤ (oddVecs n).card := by
          apply Finset.card_le_card
          intro y hy
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
          exact bitFlip_mem_odd (mem_evenVecs.mp hx) i0
  · calc (oddVecs n).card = ((oddVecs n).image (fun x => bitFlip x i0)).card := by
          rw [Finset.card_image_of_injective _ (bitFlip_injective_left i0)]
      _ ≤ (evenVecs n).card := by
          apply Finset.card_le_card
          intro y hy
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
          exact bitFlip_mem_even (mem_oddVecs.mp hx) i0

theorem card_neighborPairs_eq_sum {n : ℕ} (N P : Finset (Fin n → Bool)) :
    (neighborPairs N P).card = ∑ x ∈ N, (P.filter (fun y => hammingDist x y = 1)).card := by
  classical
  unfold neighborPairs
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [show (∑ a ∈ N.product P, (if hammingDist a.1 a.2 = 1 then (1:ℕ) else 0))
      = ∑ x ∈ N, ∑ y ∈ P, (if hammingDist x y = 1 then (1:ℕ) else 0)
      from Finset.sum_product N P _]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem filter_hammingDist_one_eq_image {n : ℕ} (x : Fin n → Bool) :
    (Finset.univ : Finset (Fin n → Bool)).filter (fun y => hammingDist x y = 1) =
      Finset.univ.image (fun i => bitFlip x i) := by
  classical
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro hd
    obtain ⟨i, rfl⟩ := eq_bitFlip_of_hammingDist_eq_one hd
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact hammingDist_bitFlip x i

theorem card_filter_hammingDist_one {n : ℕ} (x : Fin n → Bool) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun y => hammingDist x y = 1)).card = n := by
  rw [filter_hammingDist_one_eq_image]
  rw [Finset.card_image_of_injective _ (bitFlip_injective x), Finset.card_univ, Fintype.card_fin]

theorem neighborPairs_card_le_mul_left {n : ℕ} (N P : Finset (Fin n → Bool)) :
    (neighborPairs N P).card ≤ N.card * n := by
  classical
  rw [card_neighborPairs_eq_sum]
  calc ∑ x ∈ N, (P.filter (fun y => hammingDist x y = 1)).card
      ≤ ∑ x ∈ N, n := by
        apply Finset.sum_le_sum
        intro x _
        calc (P.filter (fun y => hammingDist x y = 1)).card
            ≤ ((Finset.univ : Finset (Fin n → Bool)).filter
                (fun y => hammingDist x y = 1)).card := by
              apply Finset.card_le_card
              intro y hy
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, (Finset.mem_filter.mp hy).2⟩
          _ = n := card_filter_hammingDist_one x
    _ = N.card * n := by simp

theorem card_neighborPairs_eq_sum_right {n : ℕ} (N P : Finset (Fin n → Bool)) :
    (neighborPairs N P).card = ∑ y ∈ P, (N.filter (fun x => hammingDist x y = 1)).card := by
  classical
  unfold neighborPairs
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [show (∑ a ∈ N.product P, (if hammingDist a.1 a.2 = 1 then (1:ℕ) else 0))
      = ∑ y ∈ P, ∑ x ∈ N, (if hammingDist x y = 1 then (1:ℕ) else 0)
      from Finset.sum_product_right N P _]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem neighborPairs_card_le_mul_right {n : ℕ} (N P : Finset (Fin n → Bool)) :
    (neighborPairs N P).card ≤ P.card * n := by
  classical
  rw [card_neighborPairs_eq_sum_right]
  calc ∑ y ∈ P, (N.filter (fun x => hammingDist x y = 1)).card
      ≤ ∑ y ∈ P, n := by
        apply Finset.sum_le_sum
        intro y _
        calc (N.filter (fun x => hammingDist x y = 1)).card
            ≤ ((Finset.univ : Finset (Fin n → Bool)).filter
                (fun x => hammingDist x y = 1)).card := by
              apply Finset.card_le_card
              intro x hx
              exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, (Finset.mem_filter.mp hx).2⟩
          _ = n := by simpa only [hammingDist_symm] using card_filter_hammingDist_one y
    _ = P.card * n := by simp

theorem filter_neighbors_even_odd {n : ℕ} {x : Fin n → Bool}
    (hx : linearFun n x = false) :
    (oddVecs n).filter (fun y => hammingDist x y = 1) =
      Finset.univ.image (fun i => bitFlip x i) := by
  classical
  ext y
  simp only [Finset.mem_filter, mem_oddVecs, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, hd⟩
    obtain ⟨i, rfl⟩ := eq_bitFlip_of_hammingDist_eq_one hd
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨mem_oddVecs.mp (bitFlip_mem_odd hx i), hammingDist_bitFlip x i⟩

theorem card_filter_neighbors_even_odd {n : ℕ} {x : Fin n → Bool}
    (hx : linearFun n x = false) :
    ((oddVecs n).filter (fun y => hammingDist x y = 1)).card = n := by
  rw [filter_neighbors_even_odd hx]
  rw [Finset.card_image_of_injective _ (bitFlip_injective x), Finset.card_univ, Fintype.card_fin]

theorem card_neighborPairs_even_odd {n : ℕ} :
    (neighborPairs (evenVecs n) (oddVecs n)).card = (evenVecs n).card * n := by
  classical
  rw [card_neighborPairs_eq_sum]
  calc ∑ x ∈ evenVecs n, ((oddVecs n).filter (fun y => hammingDist x y = 1)).card
      = ∑ x ∈ evenVecs n, n := by
        apply Finset.sum_congr rfl
        intro x hx
        exact card_filter_neighbors_even_odd (mem_evenVecs.mp hx)
    _ = (evenVecs n).card * n := by simp


theorem sensitivity_linearFun_le (n : ℕ) : sensitivity (linearFun n) ≤ (n : ℝ) ^ 2 := by
  classical
  apply Real.sSup_le
  · rintro r ⟨N, P, hNne, hPne, hN, hP, rfl⟩
    have h1 : ((neighborPairs N P).card : ℝ) ≤ (N.card : ℝ) * (n : ℝ) := by
      exact_mod_cast neighborPairs_card_le_mul_left N P
    have h2 : ((neighborPairs N P).card : ℝ) ≤ (P.card : ℝ) * (n : ℝ) := by
      exact_mod_cast neighborPairs_card_le_mul_right N P
    have hNpos : 0 < (N.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hNne
    have hPpos : 0 < (P.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hPne
    have hR0 : (0 : ℝ) ≤ ((neighborPairs N P).card : ℝ) := by positivity
    have hsq : ((neighborPairs N P).card : ℝ) * ((neighborPairs N P).card : ℝ) ≤
        ((N.card : ℝ) * (n : ℝ)) * ((P.card : ℝ) * (n : ℝ)) :=
      mul_le_mul (a := ((neighborPairs N P).card : ℝ)) (b := (N.card : ℝ) * (n : ℝ))
        (c := ((neighborPairs N P).card : ℝ)) (d := (P.card : ℝ) * (n : ℝ))
        h1 h2 hR0 (le_trans hR0 h1)
    have hden : 0 < (N.card : ℝ) * (P.card : ℝ) := by positivity
    rw [div_le_iff₀ hden]
    calc ((neighborPairs N P).card : ℝ) ^ 2
        = ((neighborPairs N P).card : ℝ) * ((neighborPairs N P).card : ℝ) := by ring
      _ ≤ ((N.card : ℝ) * (n : ℝ)) * ((P.card : ℝ) * (n : ℝ)) := hsq
      _ = (n : ℝ) ^ 2 * ((N.card : ℝ) * (P.card : ℝ)) := by ring
  · positivity

theorem sensitivity_linearFun_ge {n : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ 2 ≤ sensitivity (linearFun n) := by
  classical
  have hval : (n : ℝ) ^ 2 ∈ sensitivityValues (linearFun n) := by
    refine ⟨evenVecs n, oddVecs n, evenVecs_nonempty n, oddVecs_nonempty hn,
      (fun x hx => mem_evenVecs.mp hx), (fun y hy => mem_oddVecs.mp hy), ?_⟩
    have hcard : (neighborPairs (evenVecs n) (oddVecs n)).card = (evenVecs n).card * n :=
      card_neighborPairs_even_odd
    have heq : (evenVecs n).card = (oddVecs n).card := evenVecs_card_eq_oddVecs_card hn
    have hNpos : 0 < ((evenVecs n).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr (evenVecs_nonempty n)
    have hOpos : ((oddVecs n).card : ℝ) ≠ 0 := by
      have hpos : 0 < (oddVecs n).card := Finset.card_pos.mpr (oddVecs_nonempty hn)
      exact_mod_cast (Nat.pos_iff_ne_zero.mp hpos)
    rw [hcard, heq]
    push_cast
    field_simp
  exact le_csSup (sensitivityValues_bddAbove _) hval

/-- The linear function has maximal sensitivity `s(l_n) = n^2`. -/
theorem sensitivity_linearFun (n : ℕ) : sensitivity (linearFun n) = (n : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    have h0 : linearFun 0 = fun _ => false := by
      funext x
      rw [linearFun_eq_decide]
      unfold bitWeight
      simp
    rw [h0, sensitivity_const]
    norm_num
  · exact le_antisymm (sensitivity_linearFun_le n) (sensitivity_linearFun_ge h)

/-- Page 2 of the paper: `L_B(l_n) = Ω(n^{2χ_B})`, in the sharp form
`n^{2χ} ≤ L_B(l_n)` for every exponent `χ` satisfying the Khrapchenko
inequality (1.2) for `B`.

The paper's display is the instance `χ = χ_B` (`khrapchenkoExponent B`), for
which the supremum is attained; see the footnote on page 2. -/
theorem linear_lower_bound {B : Set BasisFunction} {χ : ℝ}
    (hχ : KhrapchenkoBound B χ) {n : ℕ} (hn : 0 < n)
    (hf : Expressible B (linearFun n)) :
    (n : ℝ) ^ (2 * χ) ≤ (complexity B (linearFun n) : ℝ) := by
  have h := hχ n (linearFun n) hf
  rw [sensitivity_linearFun n] at h
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  calc (n : ℝ) ^ (2 * χ) = ((n : ℝ) ^ 2) ^ χ := by
        rw [Real.rpow_mul hn0]
        norm_num
    _ ≤ (complexity B (linearFun n) : ℝ) := h




namespace NNF

variable {k n m : ℕ}

def mapVars (σ : Fin n → Fin m) : NNF k n → NNF k m
  | const b => const b
  | var i sign => var (σ i) sign
  | gate r hr φ args => gate r hr φ (fun j => (args j).mapVars σ)

theorem mapVars_eval (σ : Fin n → Fin m) (F : NNF k n) (x : Fin m → Bool) :
    (F.mapVars σ).eval x = F.eval (fun i => x (σ i)) := by
  induction F with
  | const b => rfl
  | var i sign => rfl
  | gate r hr φ args ih =>
      show φ (fun j => ((args j).mapVars σ).eval x) = φ (fun j => (args j).eval (fun i => x (σ i)))
      congr 1
      funext j
      exact ih j

theorem mapVars_complexity (σ : Fin n → Fin m) (F : NNF k n) :
    (F.mapVars σ).complexity = F.complexity := by
  induction F with
  | const b => rfl
  | var i sign => rfl
  | gate r hr φ args ih =>
      exact Finset.sum_congr rfl (fun j _ => ih j)

end NNF

noncomputable def mintermGate {m : ℕ} (f : BoolFun m) : MonotoneFun (m + m) where
  toFun z :=
    decide (∃ a : Fin m → Bool, f a = true ∧
      ∀ i : Fin m,
        (a i = true → z (Fin.castAdd m i) = true) ∧
        (a i = false → z (Fin.natAdd m i) = true))
  monotone := by
    intro z z' hzz'
    rw [Bool.le_iff_imp]
    intro hz
    have hP : ∃ a : Fin m → Bool, f a = true ∧
        ∀ i : Fin m,
          (a i = true → z (Fin.castAdd m i) = true) ∧
          (a i = false → z (Fin.natAdd m i) = true) := by
      simpa using hz
    have hQ : ∃ a : Fin m → Bool, f a = true ∧
        ∀ i : Fin m,
          (a i = true → z' (Fin.castAdd m i) = true) ∧
          (a i = false → z' (Fin.natAdd m i) = true) := by
      obtain ⟨a, hfa, hc⟩ := hP
      refine ⟨a, hfa, fun i => ⟨?_, ?_⟩⟩
      · intro hi
        have h1 : z (Fin.castAdd m i) = true := (hc i).1 hi
        have h2 := hzz' (Fin.castAdd m i)
        rw [h1] at h2
        simpa [Bool.le_iff_imp] using h2
      · intro hi
        have h1 : z (Fin.natAdd m i) = true := (hc i).2 hi
        have h2 := hzz' (Fin.natAdd m i)
        rw [h1] at h2
        simpa [Bool.le_iff_imp] using h2
    simpa using hQ

def nnfArgs {K n m : ℕ} (G : Fin m → NNF K n) : Fin (m + m) → NNF K n :=
  Fin.addCases (fun i => G i) (fun i => (G i).neg)

theorem nnfArgs_castAdd {K n m : ℕ} (G : Fin m → NNF K n) (i : Fin m) :
    nnfArgs G (Fin.castAdd m i) = G i :=
  Fin.addCases_left i

theorem nnfArgs_natAdd {K n m : ℕ} (G : Fin m → NNF K n) (i : Fin m) :
    nnfArgs G (Fin.natAdd m i) = (G i).neg :=
  Fin.addCases_right i

theorem eval_nnfArgs_castAdd {K n m : ℕ} (G : Fin m → NNF K n) (x : Fin n → Bool)
    (i : Fin m) : (nnfArgs G (Fin.castAdd m i)).eval x = (G i).eval x := by
  rw [nnfArgs_castAdd]

theorem eval_nnfArgs_natAdd {K n m : ℕ} (G : Fin m → NNF K n) (x : Fin n → Bool)
    (i : Fin m) : (nnfArgs G (Fin.natAdd m i)).eval x = !(G i).eval x := by
  rw [nnfArgs_natAdd, NNF.eval_neg]

/-- The minterm gate computes `f` on inputs of the form `(z, ¬z)`, where the
first `m` arguments carry `z` and the last `m` arguments carry its negation. -/
theorem eval_mintermGate {K n m : ℕ} (hm : m + m ≤ K) (f : BoolFun m)
    (G : Fin m → NNF K n) (x : Fin n → Bool) :
    (NNF.gate (m + m) hm (mintermGate f) (nnfArgs G)).eval x
      = f (fun i => (G i).eval x) := by
  have hcond : ∀ a : Fin m → Bool,
      (∀ i : Fin m,
        (a i = true → (nnfArgs G (Fin.castAdd m i)).eval x = true) ∧
        (a i = false → (nnfArgs G (Fin.natAdd m i)).eval x = true))
      ↔ ∀ i, a i = (G i).eval x := by
    intro a
    constructor
    · intro hc i
      have h1 := (hc i).1
      have h2 := (hc i).2
      rw [eval_nnfArgs_castAdd] at h1
      rw [eval_nnfArgs_natAdd] at h2
      cases hai : a i
      · have hg : (G i).eval x = false := by
          have := h2 hai
          simpa using this
        simp [hg]
      · have hg : (G i).eval x = true := by
          have := h1 hai
          simpa using this
        simp [hg]
    · intro hc i
      constructor
      · intro hi
        rw [eval_nnfArgs_castAdd, ← hc i]
        exact hi
      · intro hi
        rw [eval_nnfArgs_natAdd, ← hc i, hi]
        rfl
  have heq : (∃ a : Fin m → Bool, f a = true ∧
      ∀ i : Fin m,
        (a i = true → (nnfArgs G (Fin.castAdd m i)).eval x = true) ∧
        (a i = false → (nnfArgs G (Fin.natAdd m i)).eval x = true))
      ↔ f (fun i => (G i).eval x) = true := by
    constructor
    · rintro ⟨a, hfa, hc⟩
      have ha : a = fun i => (G i).eval x := funext (fun i => (hcond a).1 hc i)
      rw [ha] at hfa
      exact hfa
    · intro h
      exact ⟨fun i => (G i).eval x, h, (hcond _).2 (fun i => rfl)⟩
  have hdec : decide (∃ a : Fin m → Bool, f a = true ∧
      ∀ i : Fin m,
        (a i = true → (nnfArgs G (Fin.castAdd m i)).eval x = true) ∧
        (a i = false → (nnfArgs G (Fin.natAdd m i)).eval x = true))
      = f (fun i => (G i).eval x) := by
    have h1 : f (fun i => (G i).eval x) = decide (f (fun i => (G i).eval x) = true) := by
      cases f (fun i => (G i).eval x) <;> rfl
    rw [h1]
    exact decide_eq_decide.mpr heq
  show mintermGate f (fun j => (nnfArgs G j).eval x) = f (fun i => (G i).eval x)
  unfold mintermGate
  exact hdec

/-- The minterm gate uses every argument twice, so its complexity is twice the
sum of the complexities of the substituted formulas. -/
theorem complexity_mintermGate {K n m : ℕ} (hm : m + m ≤ K) (f : BoolFun m)
    (G : Fin m → NNF K n) :
    (NNF.gate (m + m) hm (mintermGate f) (nnfArgs G)).complexity
      = 2 * ∑ i, (G i).complexity := by
  simp only [NNF.complexity, Fin.sum_univ_add, nnfArgs_castAdd, nnfArgs_natAdd,
    NNF.complexity_neg]
  ring




def finLtEquiv (k r : ℕ) (hr : r ≤ k) : { x : Fin k // (x : ℕ) < r } ≃ Fin r where
  toFun x := ⟨(x.1 : ℕ), x.2⟩
  invFun j := ⟨⟨(j : ℕ), lt_of_lt_of_le j.2 hr⟩, j.2⟩
  left_inv x := by
    apply Subtype.ext
    exact Fin.ext rfl
  right_inv j := Fin.ext rfl

theorem card_fin_lt (k r : ℕ) (hr : r ≤ k) :
    (Finset.univ.filter (fun i : Fin k => (i : ℕ) < r)).card = r := by
  rw [← Fintype.card_subtype (fun i : Fin k => (i : ℕ) < r)]
  rw [Fintype.card_congr (finLtEquiv k r hr), Fintype.card_fin]

theorem sum_fin_lt (k r : ℕ) (hr : r ≤ k) :
    ∑ i : Fin k, (if (i : ℕ) < r then 1 else 0) = r := by
  rw [Finset.sum_boole (p := fun i : Fin k => (i : ℕ) < r) (s := Finset.univ)]
  exact card_fin_lt k r hr

/-- The `i`-th part in the balanced `k`-part decomposition of `n`. -/
def partSize (n k : ℕ) (i : Fin k) : ℕ :=
  n / k + if (i : ℕ) < n % k then 1 else 0

/-- The balanced parts form a decomposition of `n`. -/
theorem sum_partSize {n k : ℕ} (hk : 0 < k) : ∑ i : Fin k, partSize n k i = n := by
  unfold partSize
  rw [Finset.sum_add_distrib]
  have h1 : ∑ _i : Fin k, n / k = k * (n / k) := by
    simp [Finset.sum_const, Finset.card_univ]
  rw [h1, sum_fin_lt k (n % k) (le_of_lt (Nat.mod_lt _ hk))]
  exact Nat.div_add_mod n k

theorem partSize_le {n k : ℕ} (i : Fin k) : partSize n k i ≤ n / k + 1 := by
  unfold partSize
  split <;> omega

theorem partSize_lt {n k : ℕ} (hk : 2 ≤ k) (hn : k < n) (i : Fin k) :
    partSize n k i < n := by
  set q := n / k with hqdef
  set r := n % k with hrdef
  have hdiv : n = k * q + r := by
    rw [hqdef, hrdef]
    exact (Nat.div_add_mod n k).symm
  have hq : 0 < q := by
    rw [hqdef]
    exact Nat.div_pos (le_of_lt hn) (by omega)
  have hmul : 2 * q ≤ k * q := Nat.mul_le_mul_right q hk
  have h2q : q + 1 ≤ 2 * q := by omega
  unfold partSize
  rw [← hqdef, ← hrdef]
  split_ifs <;> omega

theorem partSize_le_pow {n k d : ℕ} (hd : 0 < d) (hnd : n ≤ k ^ d)
    (i : Fin k) : partSize n k i ≤ k ^ (d - 1) := by
  set q := n / k with hqdef
  set r := n % k with hrdef
  have hp : k ^ d = k * k ^ (d - 1) := by
    rw [Nat.mul_comm k (k ^ (d - 1)), ← Nat.pow_succ k (d - 1), Nat.succ_eq_add_one,
      Nat.sub_add_cancel hd]
  have hqle : q ≤ k ^ (d - 1) := by
    rw [hqdef]
    exact Nat.div_le_of_le_mul (by rw [← hp]; exact hnd)
  unfold partSize
  rw [← hqdef, ← hrdef]
  split_ifs with hri
  · by_contra hcon
    push Not at hcon
    have hcon' : k ^ (d - 1) ≤ q := by omega
    have hmul : k * k ^ (d - 1) ≤ k * q := Nat.mul_le_mul_left k hcon'
    have hdiv : n = k * q + r := by
      rw [hqdef, hrdef]
      exact (Nat.div_add_mod n k).symm
    have hrpos : 0 < r := by omega
    omega
  · exact hqle




theorem bitWeight_sigma_equiv {n k : ℕ} {m : Fin k → ℕ}
    (e : Fin n ≃ (i : Fin k) × Fin (m i)) (x : Fin n → Bool) :
    bitWeight x = ∑ i : Fin k, bitWeight (fun j : Fin (m i) => x (e.symm ⟨i, j⟩)) := by
  classical
  unfold bitWeight
  have himg : (Finset.univ.filter (fun p : Fin n => x p)) =
      (Finset.univ.sigma (fun i : Fin k =>
        (Finset.univ.filter (fun j : Fin (m i) => x (e.symm ⟨i, j⟩))))).image
        (fun q : (i : Fin k) × Fin (m i) => e.symm q) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_sigma]
    constructor
    · intro hx
      refine ⟨e p, ?_, ?_⟩
      · simpa using hx
      · simp
    · intro hp
      obtain ⟨q, hqmem, hpq⟩ := hp
      have hq : x (e.symm q) = true := by
        simpa using hqmem
      rw [← hpq]
      exact hq
  rw [himg, Finset.card_image_of_injective _ e.symm.injective, Finset.card_sigma]

theorem linearFun_eq_odd (n : ℕ) (x : Fin n → Bool) :
    linearFun n x = decide (Odd (bitWeight x)) := by
  rw [linearFun_eq_decide, decide_eq_decide]
  exact (Nat.odd_iff).symm

theorem sum_mod_two {α : Type} (s : Finset α) (w : α → ℕ) :
    (∑ i ∈ s, w i) % 2 = (∑ i ∈ s, w i % 2) % 2 := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Nat.add_mod, ih]
      omega

theorem mod_two_eq_ite' (w : ℕ) : w % 2 = if w % 2 = 1 then 1 else 0 := by
  rcases Nat.mod_two_eq_zero_or_one w with h | h <;> simp [h]

theorem mod_two_eq_ite (w : ℕ) : w % 2 = if Odd w then 1 else 0 := by
  rcases Nat.mod_two_eq_zero_or_one w with h | h
  · have hnot : ¬ Odd w := by
      intro ho
      rw [Nat.odd_iff] at ho
      omega
    simp [h, hnot]
  · have ho : Odd w := Nat.odd_iff.mpr h
    simp [h, ho]

theorem bitWeight_decide {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    bitWeight (fun i => decide (p i)) = ∑ i : Fin n, (if p i then 1 else 0) := by
  unfold bitWeight
  rw [Finset.sum_boole (p := p) (s := Finset.univ)]
  simp

/-- The linear function splits over a decomposition `Fin n ≃ Σ i, Fin (m i)`:
the parity of `x` is the parity of the parities of the blocks. -/
theorem linearFun_sigma_equiv {n k : ℕ} {m : Fin k → ℕ}
    (e : Fin n ≃ (i : Fin k) × Fin (m i)) (x : Fin n → Bool) :
    linearFun n x = linearFun k (fun i => linearFun (m i) (fun j => x (e.symm ⟨i, j⟩))) := by
  classical
  simp only [linearFun_eq_odd]
  rw [bitWeight_sigma_equiv e x]
  rw [show bitWeight (fun i => decide (Odd (bitWeight (fun j : Fin (m i) => x (e.symm ⟨i, j⟩)))))
      = ∑ i : Fin k, (if Odd (bitWeight (fun j : Fin (m i) => x (e.symm ⟨i, j⟩))) then 1 else 0)
      from bitWeight_decide (fun i => Odd (bitWeight (fun j : Fin (m i) => x (e.symm ⟨i, j⟩))))]
  simp only [Nat.odd_iff]
  rw [decide_eq_decide]
  rw [sum_mod_two]
  rw [Finset.sum_congr rfl (fun i _ => mod_two_eq_ite' _)]

theorem linearFun_zero : linearFun 0 = fun _ => false := by
  funext x
  rw [linearFun_eq_decide]
  unfold bitWeight
  simp

theorem linearFun_one : linearFun 1 = fun x : Fin 1 → Bool => x 0 := by
  funext x
  rw [linearFun_eq_decide]
  unfold bitWeight
  have hset : (Finset.univ : Finset (Fin 1)).filter (fun i => x i) = if x 0 then {0} else ∅ := by
    ext i
    fin_cases i
    by_cases h : x 0 <;> simp [h]
  rw [hset]
  by_cases h : x 0 <;> simp [h]

/-- Formula construction behind Theorem 4(i): if `n ≤ k^d`, the linear
function `l_n` has a negation-normal-form formula over the gates of arity at most
`2k` with complexity at most `n * 2^d`. -/
theorem exists_linearNNF (k : ℕ) (hk : 2 ≤ k) (n : ℕ) :
    ∀ d : ℕ, n ≤ k ^ d →
      ∃ F : NNF (2 * k) n, F.eval = linearFun n ∧ F.complexity ≤ n * 2 ^ d := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro d hd
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn01 : n = 0 ∨ n = 1 := by omega
      rcases hn01 with rfl | rfl
      · refine ⟨NNF.const false, ?_, ?_⟩
        · rw [NNF.eval_const, linearFun_zero]
        · simp
      · refine ⟨NNF.var (k := 2 * k) 0 false, ?_, ?_⟩
        · funext x
          rw [NNF.eval_var, linearFun_one]
          simp
        · simpa using Nat.one_le_pow' d 1
    · have hd1 : 0 < d := by
        rcases Nat.eq_zero_or_pos d with h0 | h
        · subst h0
          simp at hd
          omega
        · exact h
      by_cases hnk : n ≤ k
      · refine ⟨NNF.gate (n + n) ?_ (mintermGate (linearFun n))
            (nnfArgs (fun i : Fin n => NNF.var (k := 2 * k) i false)), ?_, ?_⟩
        · omega
        · funext x
          rw [eval_mintermGate]
          congr 1
        · rw [complexity_mintermGate]
          simp only [NNF.complexity_var]
          have hsum : (∑ i : Fin n, (1 : ℕ)) = n := by simp
          rw [hsum]
          have hpow : 2 ≤ 2 ^ d := by
            have := Nat.pow_le_pow_right (by norm_num : (0:ℕ) < 2) hd1
            simpa using this
          calc 2 * n = n * 2 := by ring
            _ ≤ n * 2 ^ d := Nat.mul_le_mul_left n hpow
      · have hnk' : k < n := by omega
        have hk0 : 0 < k := by omega
        set m : Fin k → ℕ := fun i => partSize n k i with hm
        have hsum : ∑ i : Fin k, m i = n := by
          rw [hm]
          exact sum_partSize hk0
        have hex : ∀ i : Fin k,
            ∃ F : NNF (2 * k) (m i), F.eval = linearFun (m i) ∧
              F.complexity ≤ m i * 2 ^ (d - 1) := by
          intro i
          exact ih (m i) (by rw [hm]; exact partSize_lt hk hnk' i) (d - 1)
            (by rw [hm]; exact partSize_le_pow hd1 hd i)
        choose F hFeval hFcomp using hex
        let e : Fin n ≃ (i : Fin k) × Fin (m i) :=
          (finCongr hsum.symm).trans finSigmaFinEquiv.symm
        let G : Fin k → NNF (2 * k) n := fun i =>
          (F i).mapVars (fun j : Fin (m i) => e.symm ⟨i, j⟩)
        refine ⟨NNF.gate (k + k) ?_ (mintermGate (linearFun k)) (nnfArgs G), ?_, ?_⟩
        · omega
        · funext x
          rw [eval_mintermGate]
          have hG : (fun i : Fin k => (G i).eval x)
              = fun i => linearFun (m i) (fun j => x (e.symm ⟨i, j⟩)) := by
            funext i
            rw [NNF.mapVars_eval, hFeval]
          rw [hG, linearFun_sigma_equiv e x]
        · rw [complexity_mintermGate]
          have hbound : ∑ i : Fin k, (G i).complexity ≤ ∑ i : Fin k, m i * 2 ^ (d - 1) := by
            apply Finset.sum_le_sum
            intro i _
            have hcomp : (G i).complexity = (F i).complexity := NNF.mapVars_complexity _ _
            rw [hcomp]
            exact hFcomp i
          have hpd : 2 * 2 ^ (d - 1) = 2 ^ d := by
            rw [Nat.mul_comm, ← Nat.pow_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hd1]
          calc 2 * ∑ i : Fin k, (G i).complexity
              ≤ 2 * ∑ i : Fin k, m i * 2 ^ (d - 1) := Nat.mul_le_mul_left 2 hbound
            _ = 2 * ((∑ i : Fin k, m i) * 2 ^ (d - 1)) := by rw [← Finset.sum_mul]
            _ = 2 * (n * 2 ^ (d - 1)) := by rw [hsum]
            _ = n * 2 ^ d := by
                calc 2 * (n * 2 ^ (d - 1)) = n * (2 * 2 ^ (d - 1)) := by ring
                  _ = n * 2 ^ d := by rw [hpd]

theorem exists_linearNNF_log (k n : ℕ) (hk : 2 ≤ k) :
    ∃ F : NNF (2 * k) n, F.eval = linearFun n ∧
      F.complexity ≤ n * 2 ^ (Nat.log k n + 1) := by
  have hk1 : 1 < k := by omega
  have h := Nat.lt_pow_succ_log_self hk1 n
  rw [Nat.succ_eq_add_one] at h
  exact exists_linearNNF k hk n (Nat.log k n + 1) (le_of_lt h)

/-- The counting form of Theorem 4(i): `L_{U_{2k}}(l_n) ≤ n * 2^{⌈log_k n⌉}`,
written with `Nat.log k n + 1` in place of the ceiling. -/
theorem complexity_linearFun_le_log (k n : ℕ) (hk : 2 ≤ k) :
    complexity (Uk (2 * k)) (linearFun n) ≤ n * 2 ^ (Nat.log k n + 1) := by
  obtain ⟨F, hF, hc⟩ := exists_linearNNF_log k n hk
  have h1 : complexity (Uk (2 * k)) (linearFun n) ≤ nnfComplexity (2 * k) n (linearFun n) :=
    complexity_le_nnfComplexity (by omega) ⟨F, hF⟩
  have h2 : nnfComplexity (2 * k) n (linearFun n) ≤ F.complexity :=
    Nat.sInf_le ⟨F, hF, rfl⟩
  exact le_trans h1 (le_trans h2 hc)

/-- Theorem 4(i) of the paper: for `k ≥ 2` and `n ≥ 1`,
`L_{U_{2k}}(l_n) ≤ 2 n^{1 + 1/log₂ k}`.  The exponent is written as
`Real.log 2 / Real.log k`, which equals `1 / log₂ k`. -/
theorem complexity_linearFun_upper_bound (k n : ℕ) (hk : 2 ≤ k) (hn : 1 ≤ n) :
    (complexity (Uk (2 * k)) (linearFun n) : ℝ) ≤
      2 * (n : ℝ) ^ (1 + Real.log 2 / Real.log k) := by
  have hnat := complexity_linearFun_le_log k n hk
  have hcast : ((complexity (Uk (2 * k)) (linearFun n) : ℕ) : ℝ) ≤
      ((n * 2 ^ (Nat.log k n + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hk1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlogk : 0 < Real.log k := Real.log_pos hk1
  have hlogbound : (Nat.log k n : ℝ) ≤ Real.log n / Real.log k := by
    have hne : n ≠ 0 := by omega
    have hp : ((k : ℝ)) ^ (Nat.log k n) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.pow_log_le_self k hne)
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (k : ℝ) ^ Nat.log k n) hp
    rw [Real.log_pow] at hlog
    rw [le_div_iff₀ hlogk]
    linarith
  refine le_trans hcast ?_
  push_cast
  calc (n : ℝ) * 2 ^ (Nat.log k n + 1)
      = (n : ℝ) * (2 * (2 : ℝ) ^ (Nat.log k n)) := by
          rw [pow_succ]
          ring
    _ ≤ (n : ℝ) * (2 * (2 : ℝ) ^ (Real.log n / Real.log k)) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hnpos)
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hlogbound
    _ = 2 * (n : ℝ) ^ (1 + Real.log 2 / Real.log k) := by
          have hrw : (2 : ℝ) ^ (Real.log n / Real.log k) =
              (n : ℝ) ^ (Real.log 2 / Real.log k) := by
            rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
              Real.rpow_def_of_pos hnpos]
            congr 1
            field_simp
          rw [hrw, Real.rpow_add hnpos, Real.rpow_one]
          ring

end UnateLin
