import Mathlib
import GF2Reduced

/-!
# Lemma 2 of Section 3: the exact additive lower bound for matrix multiplication

For every `n × n` matrix `B` over `GF(2)` the additive complexity of matrix multiplication
satisfies the exact form of Lemma 2 of the paper:

`Bil+(MM n) ≥ n · L*(B) + n² − ν(B) − 5n`,

i.e.

`n * n + n * Lstar B ≤ boolWeight B + 5 * n + BilPlus (MM n)`

(`lemma2`).  Here `L*` is the reduced additive complexity of Section 2, `ν(B)` is the boolean
weight of `B`, and `Bil+(MM n)` is the infimum of the additive cost of a three-phase bilinear
algorithm for the matrix product.

The proof follows Section 3 of the paper.  Substituting the entries of `B` for the `X`-variables
of a bilinear algorithm for `MM n` turns the `Y`-phase into a computation of `Iₙ ⊗ B`; the
cancellation cascade charges one cancelled gate to every zero entry of `B` outside the extended
set `X_M`, while the product layer shows that `X_M` is small: every variable attached only to
multiplications reaches at least `n` products, and every product carries at most one of them,
so `n·#(X_M) ≤ µ`.  The remaining case `µ > 5n²` is settled by the routing bound `µ ≤ L(cγ)+n²`
and Theorem 1 (`L*(B) ≤ 3n`, now in `GF2Reduced`).

This file is self-contained except for `GF2Reduced`: it contains the bilinear model,
the specialization and block-diagonal identities, the cascade, the routing estimate, and the
bilinear-rank count for the `α`-ports.  No weaker form of Lemma 2 is exported; the auxiliary
statements below are the proof ingredients only.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace AchainsComplexityGF2

open scoped BigOperators

/-! ## Bilinear systems, decompositions and bilinear rank -/


/-! ### Systems of bilinear forms -/

/-- A system of `k` bilinear forms in `n` variables `X = (x₁,…,xₙ)` and `m` variables
`Y = (y₁,…,y_m)`, given by its structure tensor: `F t i j` is the coefficient of `xᵢyⱼ` in
the `t`-th form. -/
abbrev BilSystem (k n m : ℕ) := Fin k → Fin n → Fin m → ZMod 2

/-- The value of a system of bilinear forms on inputs `x`, `y`. -/
noncomputable def evalForm {k n m : ℕ} (F : BilSystem k n m) (x : Vec n) (y : Vec m) :
    Fin k → ZMod 2 :=
  fun t => ∑ i, ∑ j, F t i j * x i * y j

/-- The structure tensor of `F`, read as a `k × (n·m)` matrix (a *matricization*): rows are
the forms, columns are the monomials `xᵢyⱼ`. -/
def matricize {k n m : ℕ} (F : BilSystem k n m) : Matrix (Fin k) (Fin n × Fin m) (ZMod 2) :=
  fun t p => F t p.1 p.2

/-! ### Bilinear decompositions and bilinear rank -/

/-- A decomposition of a system of bilinear forms into `r` products
`π_s = λX_s(X) · λY_s(Y)` of a linear form `α_s` in `X` and a linear form `β_s` in `Y`,
together with the coefficients `γ` expressing every form of the system as a linear combination
of the `π_s`: `F_t = ∑_s γ_{t,s} · α_s · β_s`. -/
structure BilDecomp {k n m : ℕ} (F : BilSystem k n m) (r : ℕ) where
  /-- the linear forms in `X` used by the products -/
  alpha : Fin r → Vec n
  /-- the linear forms in `Y` used by the products -/
  beta : Fin r → Vec m
  /-- the coefficients expressing each form as a linear combination of the products -/
  gamma : Fin k → Fin r → ZMod 2
  /-- the decomposition identity -/
  rep : ∀ (t : Fin k) (i : Fin n) (j : Fin m),
    F t i j = ∑ s, gamma t s * alpha s i * beta s j

/-- A system of bilinear forms admits a decomposition into one product per monomial. -/
noncomputable def monomialDecomp {k n m : ℕ} (F : BilSystem k n m) :
    BilDecomp F (k * n * m) := by
  classical
  have hcard : k * n * m = Fintype.card ((Fin k × Fin n) × Fin m) := by
    simp [Fintype.card_prod, Fintype.card_fin]
  let e : Fin (k * n * m) ≃ (Fin k × Fin n) × Fin m :=
    hcard ▸ (Fintype.equivFin ((Fin k × Fin n) × Fin m)).symm
  refine ⟨fun s i => if (e s).1.2 = i then 1 else 0,
    fun s j => if (e s).2 = j then 1 else 0,
    fun t s => if (e s).1.1 = t then F t (e s).1.2 (e s).2 else 0, ?_⟩
  intro t i j
  rw [Finset.sum_eq_single (e.symm ((t, i), j))]
  · simp
  · intro s _ hs
    by_cases h1 : (e s).1.1 = t
    · by_cases h2 : (e s).1.2 = i
      · by_cases h3 : (e s).2 = j
        · exfalso
          exact hs (e.injective (by
            simp only [Equiv.apply_symm_apply]
            exact Prod.ext (Prod.ext h1 h2) h3))
        · simp [h3]
      · simp [h2]
    · simp [h1]
  · intro h; simp at h

/-- The *bilinear rank* of a system of bilinear forms: the least number of products
`λX_s(X) · λY_s(Y)` of linear forms whose linear combinations express every form of the
system. -/
noncomputable def bilinearRank {k n m : ℕ} (F : BilSystem k n m) : ℕ :=
  sInf { r | Nonempty (BilDecomp F r) }

/-- A decomposition with `r` products gives the upper bound `r` on the bilinear rank. -/
theorem bilinearRank_le_of_decomp {k n m : ℕ} {F : BilSystem k n m} {r : ℕ}
    (h : Nonempty (BilDecomp F r)) : bilinearRank F ≤ r :=
  Nat.sInf_le h

theorem bilinearRank_set_nonempty {k n m : ℕ} (F : BilSystem k n m) :
    { r | Nonempty (BilDecomp F r) }.Nonempty :=
  ⟨_, ⟨monomialDecomp F⟩⟩

/-- The bilinear rank is at most the number of monomials. -/
theorem bilinearRank_le_card {k n m : ℕ} (F : BilSystem k n m) :
    bilinearRank F ≤ k * n * m :=
  bilinearRank_le_of_decomp (F := F) ⟨monomialDecomp F⟩

/-- The bilinear rank is attained. -/
theorem bilinearRank_mem {k n m : ℕ} (F : BilSystem k n m) :
    Nonempty (BilDecomp F (bilinearRank F)) :=
  Nat.sInf_mem (bilinearRank_set_nonempty F)

/-- If a system has a decomposition with `r` products then its bilinear rank is at most `r`. -/
theorem bilinearRank_le {k n m : ℕ} {F : BilSystem k n m} {r : ℕ}
    (D : BilDecomp F r) : bilinearRank F ≤ r :=
  bilinearRank_le_of_decomp ⟨D⟩

/-! ### The bilinear rank is bounded below by the rank of the structure tensor -/

/-- If the rows of a matrix are linear combinations of `Fintype.card σ` fixed vectors, then its
rank is at most `Fintype.card σ`. -/
theorem rank_le_card_of_rowExpansion {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    {σ : Type*} [Fintype σ] (M : Matrix κ ι (ZMod 2))
    (u : σ → κ → ZMod 2) (v : σ → ι → ZMod 2)
    (h : ∀ t i, M t i = ∑ s, u s t * v s i) : M.rank ≤ Fintype.card σ := by
  classical
  rw [Matrix.rank_eq_finrank_span_row]
  have hsub : Submodule.span (ZMod 2) (Set.range M.row) ≤
      Submodule.span (ZMod 2) (Set.range v) := by
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    have hrow : M.row t = ∑ s, u s t • v s := by
      funext i
      rw [Matrix.row_apply, Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact h t i
    rw [hrow]
    exact Submodule.sum_mem _ (fun s _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨s, rfl⟩))
  calc Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) (Set.range M.row))
      ≤ Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) (Set.range v)) :=
        Submodule.finrank_mono hsub
    _ ≤ (Set.range v).toFinset.card := finrank_span_le_card _
    _ = (Finset.univ.image v).card := by rw [Set.toFinset_range]
    _ ≤ (Finset.univ : Finset σ).card := Finset.card_image_le
    _ = Fintype.card σ := Finset.card_univ

/-- The bilinear rank of a system is at least the rank of its structure tensor. -/
theorem bilinearRank_ge_rank {k n m : ℕ} (F : BilSystem k n m) :
    (matricize F).rank ≤ bilinearRank F := by
  classical
  rw [bilinearRank]
  refine le_sInf_of_forall ?_ ?_
  · intro hs
    exact absurd hs (Set.nonempty_iff_ne_empty.mp (bilinearRank_set_nonempty F))
  · rintro r ⟨D⟩
    have h := rank_le_card_of_rowExpansion (matricize F) (fun s t => D.gamma t s)
      (fun s (p : Fin n × Fin m) => D.alpha s p.1 * D.beta s p.2) (by
        intro t p
        show F t p.1 p.2 = _
        rw [D.rep t p.1 p.2]
        exact Finset.sum_congr rfl (fun s _ => by ring))
    simpa using h


/-! ### Matrix multiplication and the boolean weight -/

/-- The `(i,j)`-th output slot of `n × n` matrix multiplication, decoded from `Fin (n*n)`. -/
def mmOut {n : ℕ} (t : Fin (n*n)) : Fin n × Fin n := finProdFinEquiv.symm t

/-- The slot of `Fin (n*n)` encoding the input pair `(i,j)`. -/
def mmIn {n : ℕ} (p : Fin n × Fin n) : Fin (n*n) := finProdFinEquiv p

@[simp] theorem mmOut_mmIn {n : ℕ} (p : Fin n × Fin n) : mmOut (mmIn p) = p :=
  Equiv.symm_apply_apply finProdFinEquiv p

@[simp] theorem mmIn_mmOut {n : ℕ} (t : Fin (n*n)) : mmIn (mmOut t) = t :=
  Equiv.apply_symm_apply finProdFinEquiv t

/-- The system of `n²` bilinear forms of `n × n` matrix multiplication: the form in slot `t`
(decoding to `(i,j)`) is `∑_k x_{i,k} y_{k,j}`. -/
def MM (n : ℕ) : BilSystem (n*n) (n*n) (n*n) :=
  fun t p q =>
    if (mmOut t).1 = (mmOut p).1 ∧ (mmOut p).2 = (mmOut q).1 ∧
        (mmOut q).2 = (mmOut t).2 then 1 else 0

/-- `MM n` evaluated on arbitrary coefficient vectors is the matrix product
`∑ k, xf (i,k) * yf (k,j)` in slot `(i,j)`. -/
theorem evalForm_MM_general (n : ℕ) (xf yf : Vec (n*n)) (a b : Fin n) :
    evalForm (MM n) xf yf (finProdFinEquiv (a, b))
      = ∑ k, xf (finProdFinEquiv (a, k)) * yf (finProdFinEquiv (k, b)) := by
  classical
  rw [evalForm]
  have hreindex : ∀ (G : Fin (n*n) → Fin (n*n) → ZMod 2),
      (∑ p, ∑ q, G p q)
        = ∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n, G (finProdFinEquiv p) (finProdFinEquiv q) := by
    intro G
    rw [← Equiv.sum_comp (finProdFinEquiv : (Fin n × Fin n) ≃ Fin (n*n))
      (fun p : Fin (n*n) => ∑ q : Fin (n*n), G p q)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [← Equiv.sum_comp (finProdFinEquiv : (Fin n × Fin n) ≃ Fin (n*n))
      (fun q : Fin (n*n) => G (finProdFinEquiv p) q)]
  rw [hreindex]
  have hsplit1 : (∑ p : Fin n × Fin n, ∑ q : Fin n × Fin n,
      MM n (finProdFinEquiv (a, b)) (finProdFinEquiv p) (finProdFinEquiv q) *
        xf (finProdFinEquiv p) * yf (finProdFinEquiv q))
      = ∑ p1, ∑ p2, ∑ q : Fin n × Fin n,
          MM n (finProdFinEquiv (a, b)) (finProdFinEquiv (p1, p2)) (finProdFinEquiv q) *
            xf (finProdFinEquiv (p1, p2)) * yf (finProdFinEquiv q) :=
    Fintype.sum_prod_type (fun p : Fin n × Fin n => ∑ q : Fin n × Fin n,
      MM n (finProdFinEquiv (a, b)) (finProdFinEquiv p) (finProdFinEquiv q) *
        xf (finProdFinEquiv p) * yf (finProdFinEquiv q))
  rw [hsplit1]
  have hsplit2 : ∀ p1 p2,
      (∑ q : Fin n × Fin n,
          MM n (finProdFinEquiv (a, b)) (finProdFinEquiv (p1, p2)) (finProdFinEquiv q) *
            xf (finProdFinEquiv (p1, p2)) * yf (finProdFinEquiv q))
        = ∑ q1, ∑ q2,
          MM n (finProdFinEquiv (a, b)) (finProdFinEquiv (p1, p2)) (finProdFinEquiv (q1, q2)) *
            xf (finProdFinEquiv (p1, p2)) * yf (finProdFinEquiv (q1, q2)) := by
    intro p1 p2
    exact Fintype.sum_prod_type (fun q : Fin n × Fin n =>
      MM n (finProdFinEquiv (a, b)) (finProdFinEquiv (p1, p2)) (finProdFinEquiv q) *
        xf (finProdFinEquiv (p1, p2)) * yf (finProdFinEquiv q))
  simp only [hsplit2]
  have hMM : ∀ (p1 p2 q1 q2 : Fin n),
      MM n (finProdFinEquiv (a, b)) (finProdFinEquiv (p1, p2)) (finProdFinEquiv (q1, q2))
        = if a = p1 ∧ p2 = q1 ∧ q2 = b then (1 : ZMod 2) else 0 := by
    intro p1 p2 q1 q2
    simp only [MM, mmOut, mmIn, Equiv.symm_apply_apply]
  simp only [hMM]
  have hq2 : ∀ p1 p2 q1, (∑ q2 : Fin n,
        (if a = p1 ∧ p2 = q1 ∧ q2 = b then (1 : ZMod 2) else 0) *
          xf (finProdFinEquiv (p1, p2)) * yf (finProdFinEquiv (q1, q2)))
      = if a = p1 ∧ p2 = q1 then xf (finProdFinEquiv (p1, p2)) * yf (finProdFinEquiv (q1, b)) else 0 := by
    intro p1 p2 q1
    by_cases hc : a = p1 ∧ p2 = q1
    · rw [if_pos hc, Finset.sum_eq_single b]
      · rw [if_pos (show a = p1 ∧ p2 = q1 ∧ b = b from ⟨hc.1, hc.2, rfl⟩)]
        ring
      · intro q2 _ hne
        rw [if_neg (by rintro ⟨_, _, h3⟩; exact hne h3), zero_mul, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ b) h
    · rw [if_neg hc]
      refine Finset.sum_eq_zero (fun q2 _ => ?_)
      rw [if_neg (by rintro ⟨h1', h2', _⟩; exact hc ⟨h1', h2'⟩), zero_mul, zero_mul]
  have hq1 : ∀ p1 p2, (∑ q1 : Fin n,
        if a = p1 ∧ p2 = q1 then xf (finProdFinEquiv (p1, p2)) * yf (finProdFinEquiv (q1, b)) else 0)
      = if a = p1 then xf (finProdFinEquiv (p1, p2)) * yf (finProdFinEquiv (p2, b)) else 0 := by
    intro p1 p2
    by_cases ha : a = p1
    · rw [if_pos ha, Finset.sum_eq_single p2]
      · rw [if_pos (show a = p1 ∧ p2 = p2 from ⟨ha, rfl⟩)]
      · intro q1 _ hne
        rw [if_neg (by rintro ⟨_, h2'⟩; exact hne h2'.symm)]
      · intro h
        exact absurd (Finset.mem_univ p2) h
    · rw [if_neg ha]
      refine Finset.sum_eq_zero (fun q1 _ => ?_)
      rw [if_neg (by rintro ⟨h1', _⟩; exact ha h1')]
  have hp2 : ∀ p1, (∑ p2 : Fin n, if a = p1 then xf (finProdFinEquiv (p1, p2)) * yf (finProdFinEquiv (p2, b)) else 0)
      = if a = p1 then ∑ p2, xf (finProdFinEquiv (p1, p2)) * yf (finProdFinEquiv (p2, b)) else 0 := by
    intro p1
    by_cases ha : a = p1
    · rw [if_pos ha]
      refine Finset.sum_congr rfl (fun p2 _ => ?_)
      rw [if_pos ha]
    · rw [if_neg ha]
      exact Finset.sum_eq_zero (fun p2 _ => by rw [if_neg ha])
  calc ∑ p1, ∑ p2, ∑ q1, ∑ q2,
        (if a = p1 ∧ p2 = q1 ∧ q2 = b then (1 : ZMod 2) else 0) *
          xf (finProdFinEquiv (p1, p2)) * yf (finProdFinEquiv (q1, q2))
      = ∑ p1, ∑ p2, ∑ q1,
          (if a = p1 ∧ p2 = q1 then xf (finProdFinEquiv (p1, p2)) * yf (finProdFinEquiv (q1, b)) else 0) := by
        refine Finset.sum_congr rfl (fun p1 _ => Finset.sum_congr rfl (fun p2 _ =>
          Finset.sum_congr rfl (fun q1 _ => hq2 p1 p2 q1)))
    _ = ∑ p1, ∑ p2, (if a = p1 then xf (finProdFinEquiv (p1, p2)) * yf (finProdFinEquiv (p2, b)) else 0) := by
        refine Finset.sum_congr rfl (fun p1 _ => Finset.sum_congr rfl (fun p2 _ => hq1 p1 p2))
    _ = ∑ p1, (if a = p1 then ∑ p2, xf (finProdFinEquiv (p1, p2)) * yf (finProdFinEquiv (p2, b)) else 0) := by
        exact Finset.sum_congr rfl (fun p1 _ => hp2 p1)
    _ = ∑ k, xf (finProdFinEquiv (a, k)) * yf (finProdFinEquiv (k, b)) := by
        rw [Finset.sum_ite_eq]
        simp

/-- On matrix inputs, `MM n` is ordinary matrix multiplication. -/
theorem evalForm_MM (n : ℕ) (X Y : Matrix (Fin n) (Fin n) (ZMod 2)) (a b : Fin n) :
    evalForm (MM n) (fun p => X ((mmOut p).1) ((mmOut p).2))
      (fun p => Y ((mmOut p).1) ((mmOut p).2)) (mmIn (a, b)) = ∑ k, X a k * Y k b := by
  classical
  have h := evalForm_MM_general n (fun p => X ((mmOut p).1) ((mmOut p).2))
    (fun p => Y ((mmOut p).1) ((mmOut p).2)) a b
  rw [show mmIn (a, b) = finProdFinEquiv (a, b) from rfl] at *
  rw [h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show finProdFinEquiv (a, k) = mmIn (a, k) from rfl, mmOut_mmIn]
  rw [show finProdFinEquiv (k, b) = mmIn (k, b) from rfl, mmOut_mmIn]

/-- The boolean weight `ν(B)` of a boolean matrix: the number of its nonzero entries. -/
def boolWeight {n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) : ℕ :=
  (Finset.univ.filter (fun p : Fin n × Fin n => B p.1 p.2 ≠ 0)).card

/-- **Lower bound on the bilinear rank of matrix multiplication**: `n² ≤ Bil*(MM n)`.

Indeed, a decomposition of `MM n` into `r` products expresses the identity `n² × n²` matrix as a
sum of `r` rank-one matrices, so `n² = rank 1 ≤ r`. -/
theorem n_mul_n_le_bilinearRank_MM (n : ℕ) : n * n ≤ bilinearRank (MM n) := by
  classical
  rw [bilinearRank]
  refine le_sInf_of_forall ?_ ?_
  · intro hs
    exact absurd hs (Set.nonempty_iff_ne_empty.mp (bilinearRank_set_nonempty (MM n)))
  · rintro r ⟨D⟩
    have hmain : (1 : Matrix (Fin (n*n)) (Fin (n*n)) (ZMod 2)).rank ≤ r := by
      have h := rank_le_card_of_rowExpansion (1 : Matrix (Fin (n*n)) (Fin (n*n)) (ZMod 2))
        (fun s t => D.gamma t s)
        (fun s c => D.alpha s c * D.beta s (mmIn ((mmOut c).2, (mmOut c).2)))
        (by
          intro t c
          have hrep := D.rep t c (mmIn ((mmOut c).2, (mmOut c).2))
          have hMC : MM n t c (mmIn ((mmOut c).2, (mmOut c).2)) =
              (if t = c then (1 : ZMod 2) else 0) := by
            by_cases htc : t = c
            · subst htc
              simp [MM]
            · rw [if_neg htc]
              simp only [MM]
              rw [if_neg]
              rintro ⟨e1, e2, e3⟩
              rw [mmOut_mmIn] at e2 e3
              refine htc ?_
              have hpair : mmOut t = mmOut c := Prod.ext e1 e3.symm
              have := congrArg mmIn hpair
              simpa using this
          rw [Matrix.one_apply, ← hMC, hrep]
          exact Finset.sum_congr rfl (fun s _ => by ring))
      calc _ ≤ Fintype.card (Fin r) := h
        _ = r := Fintype.card_fin r
    have h1 : (1 : Matrix (Fin (n*n)) (Fin (n*n)) (ZMod 2)).rank = n * n := by
      rw [Matrix.rank_one, Fintype.card_fin]
    omega


/-! ## Specialization of a bilinear algorithm under a substitution -/

open scoped BigOperators

section Substitution

variable {r k n : ℕ}

/-- The vector substituted for the `s`-th input when the product `α_s(X)·b_s` is formed:
the lift of `α_s` when the coefficient `b_s` is `1`, and the last basis vector of
`Vec (n+1)` (which vanishes on all essential coordinates) otherwise. -/
noncomputable def substVec (α : Matrix (Fin r) (Fin n) (ZMod 2)) (b : Fin r → ZMod 2)
    (s : Fin r) : Vec (n+1) :=
  if b s = 0 ∨ α s = 0 then basisVec (Fin.last n) else emb1 (n2 := 1) (α s)

/-- The linear map on coefficient vectors induced by `substVec`: the `s`-th input of the
specialized circuit is `b_s · α_s`. -/
noncomputable def substMap (α : Matrix (Fin r) (Fin n) (ZMod 2)) (b : Fin r → ZMod 2)
    (w : Vec r) : Vec (n+1) :=
  ∑ s, w s • substVec α b s

theorem basisVec_last_apply_castAdd (n : ℕ) (j : Fin n) :
    basisVec (Fin.last n) (Fin.castAdd 1 j) = 0 := by
  have hne : Fin.castAdd 1 j ≠ Fin.last n := by
    intro hh
    have := congrArg Fin.val hh
    simp at this
    omega
  simp [basisVec, hne]

/-- The essential coordinates of the substitution agree with the product `b_s · α_s`. -/
theorem substVec_apply_castAdd (α : Matrix (Fin r) (Fin n) (ZMod 2)) (b : Fin r → ZMod 2)
    (s : Fin r) (j : Fin n) :
    substVec α b s (Fin.castAdd 1 j) = b s * α s j := by
  unfold substVec
  by_cases h : b s = 0 ∨ α s = 0
  · rw [if_pos h, basisVec_last_apply_castAdd]
    rcases h with hb | ha
    · rw [hb, zero_mul]
    · rw [ha]; simp
  · rw [if_neg h]
    have hb : b s = 1 := Circuit.zmod2_eq_one_of_ne_zero (b s) (fun hz => h (Or.inl hz))
    rw [hb, one_mul]
    simp [emb1_apply_castAdd]

theorem substMap_apply_castAdd (α : Matrix (Fin r) (Fin n) (ZMod 2)) (b : Fin r → ZMod 2)
    (w : Vec r) (j : Fin n) :
    substMap α b w (Fin.castAdd 1 j) = ∑ s, w s * (b s * α s j) := by
  simp only [substMap, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, substVec_apply_castAdd]

theorem substMap_add (α : Matrix (Fin r) (Fin n) (ZMod 2)) (b : Fin r → ZMod 2)
    (u v : Vec r) : substMap α b (u + v) = substMap α b u + substMap α b v := by
  funext j
  show (∑ s, (u + v) s • substVec α b s) j
      = (∑ s, u s • substVec α b s) j + (∑ s, v s • substVec α b s) j
  rw [Finset.sum_apply, Finset.sum_apply, Finset.sum_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem substMap_zero (α : Matrix (Fin r) (Fin n) (ZMod 2)) (b : Fin r → ZMod 2) :
    substMap α b (0 : Vec r) = 0 := by
  funext j
  show (∑ s, (0 : Vec r) s • substVec α b s) j = 0
  rw [Finset.sum_apply]
  simp

theorem substMap_basisVec (α : Matrix (Fin r) (Fin n) (ZMod 2)) (b : Fin r → ZMod 2)
    (s : Fin r) : substMap α b (basisVec s) = substVec α b s := by
  funext j
  show (∑ s', basisVec s s' • substVec α b s') j = substVec α b s j
  rw [Finset.sum_apply, Finset.sum_eq_single s]
  · simp [basisVec]
  · intro s' _ hne
    rw [basisVec_apply, if_neg hne, zero_smul, Pi.zero_apply]
  · intro h
    exact absurd (Finset.mem_univ s) h

/-! ### The composed chain -/

/-- The steps of the chain obtained by feeding the lifted `α`-chain into the `γ`-chain after
the substitution.  The first `cα.L` steps are the lifted steps of `cα`; the remaining steps
are the substituted `γ`-steps. -/
noncomputable def substSteps (cα : VecAddChain n) (cγ : VecAddChain r) (f : Fin r → Vec (n+1)) :
    Fin (cα.L + cγ.L) → Vec (n+1) :=
  Fin.append (fun j => emb1 (n2 := 1) (cα.y j)) (fun j => ∑ s, cγ.y j s • f s)

theorem substSteps_left (cα : VecAddChain n) (cγ : VecAddChain r) (f : Fin r → Vec (n+1))
    (j : Fin cα.L) :
    substSteps cα cγ f (Fin.castAdd cγ.L j) = emb1 (n2 := 1) (cα.y j) :=
  Fin.append_left _ _ j

theorem substSteps_right (cα : VecAddChain n) (cγ : VecAddChain r) (f : Fin r → Vec (n+1))
    (j : Fin cγ.L) :
    substSteps cα cγ f (Fin.natAdd cα.L j) = ∑ s, cγ.y j s • f s :=
  Fin.append_right _ _ j

/-- A substitute for the constant zero: `substVec` is available in the composed chain, at any
level `K` lying between the end of the `α`-phase and the end of the composed chain. -/
theorem substVec_pool_of_mem {cα : VecAddChain n} {cγ : VecAddChain r}
    {α : Matrix (Fin r) (Fin n) (ZMod 2)} {b : Fin r → ZMod 2} {s : Fin r}
    {K : ℕ} (hKL : cα.L ≤ K) (hKR : K ≤ cα.L + cγ.L)
    (hα : α s ∈ Set.range (basisVec (n := n)) ∪ Set.range cα.y ∪ ({0} : Set (Vec n))) :
    ∃ p : Fin (n+1) ⊕ Fin K,
      chainPool (substSteps cα cγ (substVec α b)) K hKR p = substVec α b s := by
  by_cases hb : b s = 0 ∨ α s = 0
  · refine ⟨Sum.inl (Fin.last n), ?_⟩
    simp [chainPool, substVec, hb]
  · have hsub : substVec α b s = emb1 (n2 := 1) (α s) := by simp [substVec, hb]
    rw [hsub]
    rcases hα with (h | h) | h
    · obtain ⟨i, hi⟩ := h
      refine ⟨Sum.inl (Fin.castAdd 1 i), ?_⟩
      show basisVec (Fin.castAdd 1 i) = emb1 (n2 := 1) (α s)
      rw [← emb1_basisVec i, hi]
    · obtain ⟨j, hj⟩ := h
      refine ⟨Sum.inr ⟨j.1, by omega⟩, ?_⟩
      show substSteps cα cγ (substVec α b) (Fin.castLE hKR ⟨j.1, by omega⟩) =
        emb1 (n2 := 1) (α s)
      rw [show Fin.castLE hKR ⟨j.1, by omega⟩ = Fin.castAdd cγ.L j from Fin.ext rfl]
      rw [substSteps_left, hj]
    · have hz : α s = 0 := by simpa using h
      exact absurd hz (fun h0 => hb (Or.inr h0))

/-- The substitution of a pool element of the `γ`-chain is a pool element of the composed
chain. -/
theorem substMap_chainPool {cα : VecAddChain n} {cγ : VecAddChain r}
    {α : Matrix (Fin r) (Fin n) (ZMod 2)} {b : Fin r → ZMod 2}
    (hα : ∀ s, α s ∈ Set.range (basisVec (n := n)) ∪ Set.range cα.y ∪ ({0} : Set (Vec n)))
    {K : ℕ} (hKL : cα.L ≤ K) (hKR : K ≤ cα.L + cγ.L) {jv : ℕ} (hjv : jv < cγ.L)
    (hjK : cα.L + jv ≤ K) (p : Fin r ⊕ Fin jv) :
    ∃ q : Fin (n+1) ⊕ Fin K,
      chainPool (substSteps cα cγ (substVec α b)) K hKR q =
        substMap α b (chainPool cγ.y jv (le_of_lt hjv) p) := by
  rcases p with s | m
  · rw [show chainPool cγ.y jv (le_of_lt hjv) (Sum.inl s) = basisVec s from rfl,
      substMap_basisVec]
    obtain ⟨q, hq⟩ := substVec_pool_of_mem (cγ := cγ) (α := α) (b := b) hKL hKR (hα s)
    exact ⟨q, hq⟩
  · rw [show chainPool cγ.y jv (le_of_lt hjv) (Sum.inr m) = cγ.y ⟨m.1, by omega⟩ from rfl]
    refine ⟨Sum.inr ⟨cα.L + m.1, by omega⟩, ?_⟩
    show substSteps cα cγ (substVec α b) (Fin.castLE hKR ⟨cα.L + m.1, by omega⟩) =
      substMap α b (cγ.y ⟨m.1, by omega⟩)
    rw [show Fin.castLE hKR ⟨cα.L + m.1, by omega⟩ =
      Fin.natAdd cα.L ⟨m.1, by omega⟩ from Fin.ext rfl]
    rw [substSteps_right]
    rfl

/-! ### The composed chain and the specialization bound -/

/-- Availability in the composed chain of the lift of a pool element of the beta-chain. -/
theorem emb1_chainPool_available (cβ : VecAddChain n) (cγ : VecAddChain r)
    (f : Fin r → Vec (n+1)) {K : ℕ} (hKR : K ≤ cβ.L + cγ.L)
    {jv : ℕ} (hjv : jv < cβ.L) (hjK : jv ≤ K) (p : Fin n ⊕ Fin jv) :
    ∃ q : Fin (n+1) ⊕ Fin K,
      chainPool (substSteps cβ cγ f) K hKR q =
        emb1 (n2 := 1) (chainPool cβ.y jv (le_of_lt hjv) p) := by
  rcases p with i | m
  · refine ⟨Sum.inl (Fin.castAdd 1 i), ?_⟩
    show basisVec (Fin.castAdd 1 i) = emb1 (n2 := 1) (basisVec i)
    rw [emb1_basisVec]
  · refine ⟨Sum.inr ⟨m.1, by omega⟩, ?_⟩
    show substSteps cβ cγ f (Fin.castLE hKR ⟨m.1, by omega⟩) =
      emb1 (n2 := 1) (cβ.y ⟨m.1, by omega⟩)
    rw [show Fin.castLE hKR ⟨m.1, by omega⟩ = Fin.castAdd cγ.L ⟨m.1, by omega⟩ from Fin.ext rfl]
    rw [substSteps_left]

/-- The chain obtained by substituting the constants b into the beta-chain and feeding the
result into the gamma-chain.  Its length is the sum of the lengths of the two chains. -/
noncomputable def substChain (β : Matrix (Fin r) (Fin n) (ZMod 2)) (b : Fin r → ZMod 2)
    (cβ : VecAddChain n) (cγ : VecAddChain r) (hβ : cβ.Computes β) : VecAddChain (n+1) where
  L := cβ.L + cγ.L
  y := substSteps cβ cγ (substVec β b)
  valid := by
    intro k
    induction k using Fin.addCases with
    | left j1 =>
      obtain ⟨a, bb, hab⟩ := cβ.valid j1
      have hc : (↑(Fin.castAdd cγ.L j1) : ℕ) = j1.1 := rfl
      obtain ⟨q1, h1⟩ := emb1_chainPool_available cβ cγ (substVec β b)
        (K := ↑(Fin.castAdd cγ.L j1)) (le_of_lt (Fin.castAdd cγ.L j1).2)
        (jv := j1.1) j1.2 (by omega) a
      obtain ⟨q2, h2⟩ := emb1_chainPool_available cβ cγ (substVec β b)
        (K := ↑(Fin.castAdd cγ.L j1)) (le_of_lt (Fin.castAdd cγ.L j1).2)
        (jv := j1.1) j1.2 (by omega) bb
      refine ⟨q1, q2, ?_⟩
      rw [substSteps_left, hab, emb1_add, ← h1, ← h2]
    | right j2 =>
      obtain ⟨a, bb, hab⟩ := cγ.valid j2
      have hnat : (↑(Fin.natAdd cβ.L j2) : ℕ) = cβ.L + j2.1 := rfl
      obtain ⟨q1, h1⟩ := substMap_chainPool (cα := cβ) (cγ := cγ) (α := β) (b := b)
        (hα := hβ) (K := ↑(Fin.natAdd cβ.L j2)) (by omega)
        (le_of_lt (Fin.natAdd cβ.L j2).2) (jv := j2.1) j2.2 (by omega) a
      obtain ⟨q2, h2⟩ := substMap_chainPool (cα := cβ) (cγ := cγ) (α := β) (b := b)
        (hα := hβ) (K := ↑(Fin.natAdd cβ.L j2)) (by omega)
        (le_of_lt (Fin.natAdd cβ.L j2).2) (jv := j2.1) j2.2 (by omega) bb
      refine ⟨q1, q2, ?_⟩
      rw [substSteps_right,
        show (∑ s, cγ.y j2 s • substVec β b s) = substMap β b (cγ.y j2) from rfl,
        hab, substMap_add, ← h1, ← h2]

/-- The vectors of the composed chain representing the rows of the specialized operator. -/
theorem substMap_mem_pool {k : ℕ} {β : Matrix (Fin r) (Fin n) (ZMod 2)}
    {γ : Matrix (Fin k) (Fin r) (ZMod 2)} {b : Fin r → ZMod 2}
    {cβ : VecAddChain n} {cγ : VecAddChain r}
    (hβ : cβ.Computes β) (hγ : cγ.Computes γ) (i : Fin k) :
    substMap β b (γ i) ∈ Set.range (basisVec (n := n+1)) ∪
      Set.range (substSteps cβ cγ (substVec β b)) ∪ ({0} : Set (Vec (n+1))) := by
  rcases hγ i with (h | h) | h
  · obtain ⟨s, hs⟩ := h
    rw [← hs, substMap_basisVec]
    obtain ⟨q, hq⟩ := substVec_pool_of_mem (cγ := cγ) (α := β) (b := b)
      (K := cβ.L + cγ.L) (by omega) (by omega) (hβ s)
    rw [← hq]
    rcases q with a | m
    · exact Or.inl (Or.inl ⟨a, rfl⟩)
    · exact Or.inl (Or.inr ⟨m, rfl⟩)
  · obtain ⟨j, hs⟩ := h
    rw [← hs]
    refine Or.inl (Or.inr ⟨Fin.natAdd cβ.L j, ?_⟩)
    rw [substSteps_right]
    rfl
  · rw [show γ i = 0 from h, substMap_zero]
    exact Or.inr (by simp)

/-- **Specialization of a bilinear algorithm**: if the chain `cβ` computes the `Y`-forms and the
chain `cγ` computes the output coefficients, then substituting constants `b` produces a chain
computing the linear operator `t ↦ ∑ s, γ t s · b s · β s` with `cβ.L + cγ.L` additions. -/
theorem substChain_computes {k : ℕ} {β : Matrix (Fin r) (Fin n) (ZMod 2)}
    {γ : Matrix (Fin k) (Fin r) (ZMod 2)} {b : Fin r → ZMod 2}
    {cβ : VecAddChain n} {cγ : VecAddChain r}
    (hβ : cβ.Computes β) (hγ : cγ.Computes γ) :
    (ExtChain.ofChain (substChain β b cβ cγ hβ) ∅).Computes
      (fun i j => ∑ s, γ i s * (b s * β s j)) (Fin.castAdd 1) := by
  refine ⟨?_, fun j => by simp [ExtChain.ofChain], fun i => ?_⟩
  · intro i j h
    exact Fin.ext (by simpa using congrArg Fin.val h)
  · refine ⟨substMap β b (γ i), substMap_mem_pool hβ hγ i, ?_, ?_⟩
    · intro j
      exact substMap_apply_castAdd β b (γ i) j
    · intro j hj
      simp [ExtChain.ofChain] at hj
/-- **The specialization inequality**: `L*` of the specialized operator is at most the number of
additions in the two surviving phases of the bilinear algorithm. -/
theorem Lstar_specialization {k : ℕ} {β : Matrix (Fin r) (Fin n) (ZMod 2)}
    {γ : Matrix (Fin k) (Fin r) (ZMod 2)} {b : Fin r → ZMod 2}
    {cβ : VecAddChain n} {cγ : VecAddChain r}
    (hβ : cβ.Computes β) (hγ : cγ.Computes γ) :
    Lstar (fun i j => ∑ s, γ i s * (b s * β s j)) ≤ cβ.L + cγ.L := by
  have h := Lstar_le_of_computes (ExtChain.ofChain (substChain β b cβ cγ hβ) ∅)
    (Fin.castAdd 1) (substChain_computes hβ hγ)
  rwa [ExtChain.reducedComplexity_aux_empty] at h

/-- The specialization inequality with the minimal additive complexities. -/
theorem Lstar_specialization_le {k : ℕ} (β : Matrix (Fin r) (Fin n) (ZMod 2))
    (γ : Matrix (Fin k) (Fin r) (ZMod 2)) (b : Fin r → ZMod 2) :
    Lstar (fun i j => ∑ s, γ i s * (b s * β s j)) ≤
      chainComplexity β + chainComplexity γ := by
  obtain ⟨cβ, hLβ, hβ⟩ := Nat.sInf_mem (chainSet_nonempty β)
  obtain ⟨cγ, hLγ, hγ⟩ := Nat.sInf_mem (chainSet_nonempty γ)
  have h := Lstar_specialization (b := b) hβ hγ
  rw [hLβ, hLγ] at h
  exact h

end Substitution


/-! ## Block-diagonal matrices and additivity of `L*` -/

open scoped BigOperators

/-! ### Reindexing invariance of `L*` -/

/-- A simultaneous reindexing of the rows (`e`) and the columns (`f`) of a matrix preserves
the property of being computed by an extended chain. -/
theorem ExtChain.computes_reindex {m k n k' n' : ℕ} {A : Matrix (Fin k) (Fin n) (ZMod 2)}
    {c : ExtChain m} {col : Fin n → Fin m} (hc : c.Computes A col)
    (e : Fin k' ≃ Fin k) (f : Fin n' ≃ Fin n) :
    c.Computes (fun i j => A (e i) (f j)) (fun j => col (f j)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    exact f.injective (hc.1 hij)
  · intro j
    exact hc.2.1 (f j)
  · intro i
    obtain ⟨w, hw, hval, hz⟩ := hc.2.2 (e i)
    exact ⟨w, hw, fun j => hval (f j), hz⟩

/-- `L*` is invariant under a simultaneous reindexing of the rows and the columns. -/
theorem Lstar_reindex {k n k' n' : ℕ} (A : Matrix (Fin k) (Fin n) (ZMod 2))
    (e : Fin k' ≃ Fin k) (f : Fin n' ≃ Fin n) :
    Lstar (fun i j => A (e i) (f j)) = Lstar A := by
  classical
  have hS : { l | ∃ (m : ℕ) (c : ExtChain m) (col : Fin n' → Fin m),
        c.Computes (fun i j => A (e i) (f j)) col ∧ c.reducedComplexity = l }
      = { l | ∃ (m : ℕ) (c : ExtChain m) (col : Fin n → Fin m),
        c.Computes A col ∧ c.reducedComplexity = l } := by
    ext l
    constructor
    · rintro ⟨m, c, col, hc, hl⟩
      refine ⟨m, c, fun j => col (f.symm j), ?_, hl⟩
      have h := ExtChain.computes_reindex hc (e := e.symm) (f := f.symm)
      simpa [Equiv.apply_symm_apply] using h
    · rintro ⟨m, c, col, hc, hl⟩
      exact ⟨m, c, fun j => col (f j), ExtChain.computes_reindex hc e f, hl⟩
  unfold Lstar
  rw [hS]

/-- A matrix with no rows has reduced complexity zero. -/
theorem Lstar_eq_zero_of_fin_zero {k n : ℕ} (A : Matrix (Fin k) (Fin n) (ZMod 2))
    (hk : k = 0) : Lstar A = 0 := by
  subst hk
  have hempty : (ExtChain.ofChain (⟨0, Fin.elim0, fun k => Fin.elim0 k⟩ : VecAddChain n)
      ∅).Computes A id := by
    refine ⟨Function.injective_id, ?_, ?_⟩
    · intro j
      simp [ExtChain.ofChain]
    · intro i
      exact Fin.elim0 i
  have h := Lstar_le_of_computes (ExtChain.ofChain (⟨0, Fin.elim0, fun k => Fin.elim0 k⟩ :
    VecAddChain n) ∅) id hempty
  rw [ExtChain.reducedComplexity_aux_empty] at h
  have hz : (⟨0, Fin.elim0, fun k => Fin.elim0 k⟩ : VecAddChain n).L = 0 := rfl
  omega

/-! ### Block-diagonal matrices `Iₙ ⊗ B` -/

/-- The block-diagonal matrix `Iₙ ⊗ B` with `n` diagonal blocks equal to the `m × m` matrix
`B`.  A position `t : Fin (n·m)` is decoded as the pair `(t / m, t % m)` of a block index and
an index inside the block. -/
noncomputable def kronId (n : ℕ) {m : ℕ} (B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    Matrix (Fin (n * m)) (Fin (n * m)) (ZMod 2) :=
  fun t p => if (finProdFinEquiv.symm t).1 = (finProdFinEquiv.symm p).1 then
    B (finProdFinEquiv.symm t).2 (finProdFinEquiv.symm p).2 else 0

/-- The entries of `kronId` in terms of quotient and remainder by the block size. -/
theorem kronId_apply {m : ℕ} (n : ℕ) (B : Matrix (Fin m) (Fin m) (ZMod 2)) (hm : 0 < m)
    (t p : Fin (n * m)) :
    kronId n B t p = if t.val / m = p.val / m then
      B ⟨t.val % m, Nat.mod_lt _ hm⟩ ⟨p.val % m, Nat.mod_lt _ hm⟩ else 0 := by
  unfold kronId
  have hiff : ((finProdFinEquiv.symm t).1 = (finProdFinEquiv.symm p).1) ↔
      (t.val / m = p.val / m) := by
    constructor
    · intro hh
      exact congrArg Fin.val hh
    · intro hh
      exact Fin.ext hh
  by_cases h : t.val / m = p.val / m
  · rw [if_pos (hiff.mpr h), if_pos h]
    exact congrArg₂ B (Fin.ext rfl) (Fin.ext rfl)
  · rw [if_neg (fun hh => h (hiff.mp hh)), if_neg h]
/-- Splitting off the last diagonal block: `Iₙ₊₁ ⊗ B` is the direct sum of `Iₙ ⊗ B` and `B`,
up to the canonical identification of `Fin ((n+1)·m)` with `Fin (n·m + m)`. -/
theorem kronId_succ {m : ℕ} (n : ℕ) (B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    kronId (n+1) B = fun (t p : Fin ((n+1)*m)) =>
      dsum (kronId n B) B
        ⟨t.val, lt_of_lt_of_eq t.2 (Nat.succ_mul n m)⟩
        ⟨p.val, lt_of_lt_of_eq p.2 (Nat.succ_mul n m)⟩ := by
  funext t p
  by_cases hm : m = 0
  · subst hm
    exact Fin.elim0 t
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have ht : t.val < n * m + m := lt_of_lt_of_eq t.2 (Nat.succ_mul n m)
    have hp : p.val < n * m + m := lt_of_lt_of_eq p.2 (Nat.succ_mul n m)
    rcases Nat.lt_or_ge t.val (n * m) with ht1 | ht2 <;>
      rcases Nat.lt_or_ge p.val (n * m) with hp1 | hp2
    · rw [show (⟨t.val, ht⟩ : Fin (n*m+m)) = Fin.castAdd m ⟨t.val, by omega⟩ from Fin.ext rfl,
        show (⟨p.val, hp⟩ : Fin (n*m+m)) = Fin.castAdd m ⟨p.val, by omega⟩ from Fin.ext rfl,
        dsum_castAdd_castAdd, kronId_apply (n+1) B hmpos, kronId_apply n B hmpos]
    · rw [show (⟨t.val, ht⟩ : Fin (n*m+m)) = Fin.castAdd m ⟨t.val, by omega⟩ from Fin.ext rfl,
        show (⟨p.val, hp⟩ : Fin (n*m+m)) = Fin.natAdd (n*m) ⟨p.val - n*m, by omega⟩ from
          Fin.ext (by simp only [Fin.val_natAdd, Fin.val_mk]; omega),
        dsum_castAdd_natAdd, kronId_apply (n+1) B hmpos]
      have hd1 : t.val / m < n :=
        Nat.div_lt_of_lt_mul (m := t.val) (n := m) (k := n) (by rw [Nat.mul_comm m n]; exact ht1)
      have hd2 : p.val / m = n :=
        Nat.div_eq_of_lt_le (k := n) (n := m) (m := p.val) (hp2) p.2
      rw [if_neg (by omega)]
    · rw [show (⟨t.val, ht⟩ : Fin (n*m+m)) = Fin.natAdd (n*m) ⟨t.val - n*m, by omega⟩ from
          Fin.ext (by simp only [Fin.val_natAdd, Fin.val_mk]; omega),
        show (⟨p.val, hp⟩ : Fin (n*m+m)) = Fin.castAdd m ⟨p.val, by omega⟩ from Fin.ext rfl,
        dsum_natAdd_castAdd, kronId_apply (n+1) B hmpos]
      have hd1 : t.val / m = n :=
        Nat.div_eq_of_lt_le (k := n) (n := m) (m := t.val) (ht2) t.2
      have hd2 : p.val / m < n :=
        Nat.div_lt_of_lt_mul (m := p.val) (n := m) (k := n) (by rw [Nat.mul_comm m n]; exact hp1)
      rw [if_neg (by omega)]
    · rw [show (⟨t.val, ht⟩ : Fin (n*m+m)) = Fin.natAdd (n*m) ⟨t.val - n*m, by omega⟩ from
          Fin.ext (by simp only [Fin.val_natAdd, Fin.val_mk]; omega),
        show (⟨p.val, hp⟩ : Fin (n*m+m)) = Fin.natAdd (n*m) ⟨p.val - n*m, by omega⟩ from
          Fin.ext (by simp only [Fin.val_natAdd, Fin.val_mk]; omega),
        dsum_natAdd_natAdd, kronId_apply (n+1) B hmpos]
      have hdt : t.val / m = n :=
        Nat.div_eq_of_lt_le (k := n) (n := m) (m := t.val) (ht2) t.2
      have hdp : p.val / m = n :=
        Nat.div_eq_of_lt_le (k := n) (n := m) (m := p.val) (hp2) p.2
      rw [if_pos (by omega)]
      have hmt : t.val % m = t.val - n * m := by
        rw [Nat.mod_eq_sub_mul_div, hdt, Nat.mul_comm m n]
      have hmp : p.val % m = p.val - n * m := by
        rw [Nat.mod_eq_sub_mul_div, hdp, Nat.mul_comm m n]
      rw [show (⟨t.val % m, _⟩ : Fin m) = ⟨t.val - n * m, _⟩ from Fin.ext hmt,
        show (⟨p.val % m, _⟩ : Fin m) = ⟨p.val - n * m, _⟩ from Fin.ext hmp]

/-- **Additivity of `L*` for copies of a matrix**: `L*(Iₙ ⊗ B) = n · L*(B)`. -/
theorem Lstar_kronId {m : ℕ} (n : ℕ) (B : Matrix (Fin m) (Fin m) (ZMod 2)) :
    Lstar (kronId n B) = n * Lstar B := by
  induction n with
  | zero =>
    rw [Lstar_eq_zero_of_fin_zero (kronId 0 B) (Nat.zero_mul m)]
    simp
  | succ n ih =>
    have hstep : Lstar (kronId (n+1) B) =
        Lstar (fun (t p : Fin ((n+1)*m)) =>
          dsum (kronId n B) B (finCongr (Nat.succ_mul n m) t)
            (finCongr (Nat.succ_mul n m) p)) := by
      rw [kronId_succ n B]
      congr 1
    rw [hstep, Lstar_reindex (dsum (kronId n B) B)
      (finCongr (Nat.succ_mul n m)) (finCongr (Nat.succ_mul n m)),
      (lemma1_reduced (kronId n B) B).1, ih]
    ring


/-! ## The three-phase bilinear complexity -/

open scoped BigOperators

/-! ### Semantic meaning of a bilinear decomposition -/

/-- A bilinear decomposition indeed evaluates the system: the value of each form on inputs
`x`, `y` is the linear combination (with coefficients `γ`) of the products of the values of the
linear forms `α_s` and `β_s`. -/
theorem evalForm_eq_decomp {k n m r : ℕ} {F : BilSystem k n m} (D : BilDecomp F r)
    (x : Vec n) (y : Vec m) (t : Fin k) :
    evalForm F x y t =
      ∑ s, D.gamma t s * ((∑ i, D.alpha s i * x i) * (∑ j, D.beta s j * y j)) := by
  classical
  rw [evalForm]
  calc ∑ i, ∑ j, F t i j * x i * y j
      = ∑ i, ∑ j, (∑ s, D.gamma t s * D.alpha s i * D.beta s j) * x i * y j := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
        rw [D.rep]
    _ = ∑ i, ∑ j, ∑ s, (D.gamma t s * D.alpha s i * D.beta s j) * x i * y j := by
        simp only [Finset.sum_mul]
    _ = ∑ i, ∑ s, ∑ j, (D.gamma t s * D.alpha s i * D.beta s j) * x i * y j := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ s, ∑ i, ∑ j, (D.gamma t s * D.alpha s i * D.beta s j) * x i * y j :=
        Finset.sum_comm
    _ = ∑ s, D.gamma t s * ((∑ i, D.alpha s i * x i) * (∑ j, D.beta s j * y j)) := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        calc ∑ i, ∑ j, (D.gamma t s * D.alpha s i * D.beta s j) * x i * y j
            = ∑ i, (D.gamma t s * (D.alpha s i * x i)) * (∑ j, D.beta s j * y j) := by
              refine Finset.sum_congr rfl (fun i _ => ?_)
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun j _ => by ring)
          _ = (∑ i, D.gamma t s * (D.alpha s i * x i)) * (∑ j, D.beta s j * y j) := by
              rw [Finset.sum_mul]
          _ = D.gamma t s * ((∑ i, D.alpha s i * x i) * (∑ j, D.beta s j * y j)) := by
              have h : (∑ i, D.gamma t s * (D.alpha s i * x i)) =
                  D.gamma t s * ∑ i, D.alpha s i * x i := by
                rw [Finset.mul_sum]
              rw [h]
              ring

/-- A bilinear decomposition with `r` products is a valid bilinear algorithm: it computes the
system with `r` multiplications. -/
theorem evalForm_eq_decomp_apply {k n m r : ℕ} {F : BilSystem k n m} (D : BilDecomp F r)
    (x : Vec n) (y : Vec m) :
    evalForm F x y = fun t => ∑ s, D.gamma t s *
      ((∑ i, D.alpha s i * x i) * (∑ j, D.beta s j * y j)) :=
  funext fun t => evalForm_eq_decomp D x y t

/-! ### The additive complexity `Bil+` -/

/-- The additive cost of a bilinear algorithm: the numbers of additions in the three phases,
for a decomposition into `r` products together with addition chains for its three coefficient
matrices. -/
def BilPlusSet {k n m : ℕ} (F : BilSystem k n m) : Set ℕ :=
  { l | ∃ (r : ℕ) (D : BilDecomp F r) (cα : VecAddChain n) (cβ : VecAddChain m)
        (cγ : VecAddChain r),
      cα.Computes D.alpha ∧ cβ.Computes D.beta ∧ cγ.Computes D.gamma ∧
      cα.L + cβ.L + cγ.L = l }

/-- `Bil+(F)`: the minimal number of additive operations in a bilinear algorithm computing the
system `F` (the paper's `Bil+(F)`). -/
noncomputable def BilPlus {k n m : ℕ} (F : BilSystem k n m) : ℕ :=
  sInf (BilPlusSet F)

theorem BilPlusSet_nonempty {k n m : ℕ} (F : BilSystem k n m) :
    (BilPlusSet F).Nonempty := by
  classical
  obtain ⟨cα, hα⟩ := exists_chain_computes (monomialDecomp F).alpha
  obtain ⟨cβ, hβ⟩ := exists_chain_computes (monomialDecomp F).beta
  obtain ⟨cγ, hγ⟩ := exists_chain_computes (monomialDecomp F).gamma
  exact ⟨_, k * n * m, monomialDecomp F, cα, cβ, cγ, hα, hβ, hγ, rfl⟩

/-- An explicit bilinear algorithm gives an upper bound on `Bil+`. -/
theorem BilPlus_le_of_chains {k n m r : ℕ} {F : BilSystem k n m} (D : BilDecomp F r)
    (cα : VecAddChain n) (cβ : VecAddChain m) (cγ : VecAddChain r)
    (hα : cα.Computes D.alpha) (hβ : cβ.Computes D.beta) (hγ : cγ.Computes D.gamma) :
    BilPlus F ≤ cα.L + cβ.L + cγ.L :=
  Nat.sInf_le ⟨r, D, cα, cβ, cγ, hα, hβ, hγ, rfl⟩

/-- The additive complexity is at most the sum of the minimal additive complexities of the three
phases of a decomposition. -/
theorem BilPlus_le_chainComplexity {k n m r : ℕ} {F : BilSystem k n m} (D : BilDecomp F r) :
    BilPlus F ≤ chainComplexity D.alpha + chainComplexity D.beta + chainComplexity D.gamma := by
  classical
  obtain ⟨cα, hLα, hα⟩ := Nat.sInf_mem (chainSet_nonempty D.alpha)
  obtain ⟨cβ, hLβ, hβ⟩ := Nat.sInf_mem (chainSet_nonempty D.beta)
  obtain ⟨cγ, hLγ, hγ⟩ := Nat.sInf_mem (chainSet_nonempty D.gamma)
  have h := BilPlus_le_of_chains D cα cβ cγ hα hβ hγ
  rwa [hLα, hLβ, hLγ] at h

/-! ### The multiplicative and total complexities -/

/-- `Bil*(F)`: the minimal number of multiplicative operations in a bilinear algorithm
computing the system `F`.  As the paper notes (footnote 12), this is the bilinear rank. -/
noncomputable def BilStar {k n m : ℕ} (F : BilSystem k n m) : ℕ :=
  bilinearRank F

/-- The multiplicative complexity is exactly the bilinear rank. -/
theorem BilStar_eq_bilinearRank {k n m : ℕ} (F : BilSystem k n m) :
    BilStar F = bilinearRank F := rfl

/-- A decomposition into `r` products bounds the multiplicative complexity by `r`. -/
theorem BilStar_le_of_decomp {k n m r : ℕ} {F : BilSystem k n m} (D : BilDecomp F r) :
    BilStar F ≤ r :=
  bilinearRank_le D

/-- The multiplicative complexity is attained by some decomposition. -/
theorem BilStar_mem {k n m : ℕ} (F : BilSystem k n m) :
    Nonempty (BilDecomp F (BilStar F)) :=
  bilinearRank_mem F

/-- `Bil(F)`: the total number of operations of a bilinear algorithm, the sum of the additive
and multiplicative complexities. -/
noncomputable def Bil {k n m : ℕ} (F : BilSystem k n m) : ℕ :=
  BilPlus F + BilStar F

/-- The additive complexity is a lower bound for the total complexity. -/
theorem BilPlus_le_Bil {k n m : ℕ} (F : BilSystem k n m) : BilPlus F ≤ Bil F :=
  Nat.le_add_right _ _

/-- The multiplicative complexity is a lower bound for the total complexity. -/
theorem BilStar_le_Bil {k n m : ℕ} (F : BilSystem k n m) : BilStar F ≤ Bil F :=
  Nat.le_add_left _ _

/-- **Lower bound on the multiplicative complexity of matrix multiplication**:
`n² ≤ Bil*(MM n)`.  A decomposition into `r` products writes the identity matrix as a sum of
`r` rank-one matrices, so `r ≥ n²`. -/
theorem n_mul_n_le_BilStar_MM (n : ℕ) : n * n ≤ BilStar (MM n) := by
  rw [BilStar_eq_bilinearRank]
  exact n_mul_n_le_bilinearRank_MM n


/-! ## Substituting the coefficients of `B` into `MM n` -/

/-! ### The coordinate swap of `Fin (n*n)` -/

/-- The permutation of `Fin (n*n)` exchanging the two coordinates of the encoded pair. -/
noncomputable def mmSwap (n : ℕ) : Fin (n*n) ≃ Fin (n*n) :=
  (finProdFinEquiv.symm).trans ((Equiv.prodComm (Fin n) (Fin n)).trans finProdFinEquiv)

theorem symm_mmSwap (n : ℕ) (u : Fin (n*n)) :
    finProdFinEquiv.symm (mmSwap n u) = ((mmOut u).2, (mmOut u).1) := by
  simp [mmSwap, mmOut, Equiv.trans_apply, Equiv.prodComm_apply]

theorem mmSwap_apply (n : ℕ) (u : Fin (n*n)) :
    mmSwap n u = mmIn ((mmOut u).2, (mmOut u).1) := by
  have h := congrArg finProdFinEquiv (symm_mmSwap n u)
  simpa only [mmIn, mmOut, Equiv.apply_symm_apply] using h

/-! ### Substituting the coefficients of `B` for the `X`-variables -/

/-- Substituting the entries of `B` for the variables `X` turns the system `MM n` into the
operator `Iₙ ⊗ B` on the variables `Y`, encoded as a matrix over `Fin (n*n)` (the row index
`t` is an output slot and the column index `j` a variable `Y`). -/
theorem MM_substitution {n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) (t j : Fin (n*n)) :
    (∑ p, MM n t p j * B (mmOut p).1 (mmOut p).2) =
      kronId n B (mmSwap n t) (mmSwap n j) := by
  classical
  rw [kronId, symm_mmSwap, symm_mmSwap]
  by_cases h : (mmOut t).2 = (mmOut j).2
  · rw [if_pos h]
    rw [Finset.sum_eq_single (mmIn ((mmOut t).1, (mmOut j).1))]
    · simp [MM, h]
    · intro p _ hp
      have hM : MM n t p j = 0 := by
        rw [MM]
        refine if_neg ?_
        rintro ⟨e1, e2, e3⟩
        apply hp
        have hpeq : mmOut p = ((mmOut t).1, (mmOut j).1) := Prod.ext e1.symm e2
        simpa using congrArg mmIn hpeq
      rw [hM, zero_mul]
    · intro hp
      exact absurd (Finset.mem_univ _) hp
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun p _ => ?_)
    have hM : MM n t p j = 0 := by
      rw [MM]
      refine if_neg ?_
      rintro ⟨_, _, h3⟩
      exact h h3.symm
    rw [hM, zero_mul]

/-- **The specialized operator**: substituting the entries of `B` into the `X`-variables of the
matrix product gives a matrix whose `L*` is `n · L*(B)`. -/
theorem Lstar_MM_substitution {n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Lstar (fun t j => ∑ p, MM n t p j * B (mmOut p).1 (mmOut p).2) = n * Lstar B := by
  have h : (fun t j => ∑ p, MM n t p j * B (mmOut p).1 (mmOut p).2)
      = fun t j => kronId n B (mmSwap n t) (mmSwap n j) := by
    funext t j
    exact MM_substitution B t j
  rw [h, Lstar_reindex (kronId n B) (mmSwap n) (mmSwap n), Lstar_kronId]

/-- A bilinear decomposition of `MM n`, after substituting the entries of `B` for the
`X`-variables, is the specialized linear operator `t ↦ ∑ s, γ_{t,s} · b_s · β_s` of the
`Y`-forms, where `b_s = α_s(B)` is the value of the `s`-th `X`-form on `B`. -/
theorem MM_decomp_substitution {n r : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (D : BilDecomp (MM n) r) :
    (fun i j => ∑ p, MM n i p j * B (mmOut p).1 (mmOut p).2)
      = fun i j => ∑ s, D.gamma i s *
          ((∑ p, D.alpha s p * B (mmOut p).1 (mmOut p).2) * D.beta s j) := by
  funext i j
  have h1 : (∑ p, MM n i p j * B (mmOut p).1 (mmOut p).2)
      = ∑ p, (∑ s, D.gamma i s * D.alpha s p * D.beta s j) *
          B (mmOut p).1 (mmOut p).2 := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [D.rep]
  rw [h1]
  calc ∑ p, (∑ s, D.gamma i s * D.alpha s p * D.beta s j) * B (mmOut p).1 (mmOut p).2
      = ∑ p, ∑ s, (D.gamma i s * D.alpha s p * D.beta s j) *
          B (mmOut p).1 (mmOut p).2 := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.sum_mul]
    _ = ∑ s, ∑ p, (D.gamma i s * D.alpha s p * D.beta s j) *
          B (mmOut p).1 (mmOut p).2 := Finset.sum_comm
    _ = ∑ s, D.gamma i s *
          ((∑ p, D.alpha s p * B (mmOut p).1 (mmOut p).2) * D.beta s j) := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        ring

/-- **Specialization of a bilinear algorithm for matrix multiplication**: if `cβ` and `cγ`
compute the `Y`-forms and the output coefficients of a decomposition of `MM n`, then after
substituting the entries of `B` for the `X`-variables one obtains a chain computing the
operator `Iₙ ⊗ B` with `cβ.L + cγ.L` additions.  Hence `n · L*(B) ≤ cβ.L + cγ.L`. -/
theorem Lstar_specialization_MM {n r : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (D : BilDecomp (MM n) r) (cβ : VecAddChain (n*n)) (cγ : VecAddChain r)
    (hβ : cβ.Computes D.beta) (hγ : cγ.Computes D.gamma) :
    n * Lstar B ≤ cβ.L + cγ.L := by
  have hspec := Lstar_specialization (β := D.beta) (γ := D.gamma)
    (b := fun s => ∑ p, D.alpha s p * B (mmOut p).1 (mmOut p).2) hβ hγ
  calc n * Lstar B
      = Lstar (fun t j => ∑ p, MM n t p j * B (mmOut p).1 (mmOut p).2) :=
        (Lstar_MM_substitution B).symm
    _ = Lstar (fun i j => ∑ s, D.gamma i s *
          ((∑ p, D.alpha s p * B (mmOut p).1 (mmOut p).2) * D.beta s j)) := by
        rw [MM_decomp_substitution B D]
    _ ≤ cβ.L + cγ.L := hspec

/-! ## Counting the zero entries of `B` -/


/-! ### The substitution count -/

/-- The number of zero entries of `B` in the `Fin (n*n)` encoding: `#(zeros) + ν(B) = n²`. -/
theorem card_zero_entries {n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (Finset.univ.filter (fun p : Fin (n*n) => B (mmOut p).1 (mmOut p).2 = 0)).card
      + boolWeight B = n * n := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (n*n))))
    (p := fun p : Fin (n*n) => B (mmOut p).1 (mmOut p).2 = 0)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have hset : (Finset.univ.filter (fun p : Fin (n*n) => ¬ (B (mmOut p).1 (mmOut p).2 = 0)))
      = (Finset.univ.filter (fun q : Fin n × Fin n => B q.1 q.2 ≠ 0)).image finProdFinEquiv := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hp
      refine ⟨mmOut p, by simpa using hp, ?_⟩
      show mmIn (mmOut p) = p
      exact mmIn_mmOut p
    · rintro ⟨q, hq, hqp⟩
      rw [← hqp]
      simpa [mmOut] using hq
  have hbw : (Finset.univ.filter (fun p : Fin (n*n) => ¬ (B (mmOut p).1 (mmOut p).2 = 0))).card
      = boolWeight B := by
    rw [hset, Finset.card_image_of_injective _ finProdFinEquiv.injective, boolWeight]
  rw [hbw] at h
  exact h

/-! ## Operand slots of a chain -/

variable {N : ℕ}

/-- The first operand of the additive gate producing the `k`-th vector of a chain, chosen
canonically among the decompositions guaranteed by the validity condition. -/
noncomputable def gateFst (c : VecAddChain N) (k : Fin c.L) : Fin N ⊕ Fin k.1 :=
  Classical.choose (c.valid k)

/-- The second operand of the additive gate producing the `k`-th vector of a chain. -/
noncomputable def gateSnd (c : VecAddChain N) (k : Fin c.L) : Fin N ⊕ Fin k.1 :=
  Classical.choose (Classical.choose_spec (c.valid k))

/-- The `k`-th vector of a chain is the sum of its two canonically chosen operands. -/
theorem gateFst_add_gateSnd (c : VecAddChain N) (k : Fin c.L) :
    c.y k = chainPool c.y k.1 (le_of_lt k.2) (gateFst c k) +
      chainPool c.y k.1 (le_of_lt k.2) (gateSnd c k) :=
  Classical.choose_spec (Classical.choose_spec (c.valid k))

/-- The basis vectors are pairwise distinct. -/
theorem basisVec_injective {n : ℕ} : Function.Injective (basisVec (n := n)) := by
  intro i j h
  by_contra hne
  have h1 : basisVec i i = (1 : ZMod 2) := by simp [basisVec]
  have h2 : basisVec j i = 0 := by rw [basisVec_apply, if_neg hne]
  rw [← h, h1] at h2
  exact zero_ne_one h2.symm

/-! ## The cancellation cascade: substituting zeros one at a time -/


/-! ### Substituting zeros -/

/-- Substituting `0` for the variables of `T`: the projection onto the complement of `T`. -/
def subst {m : ℕ} (T : Finset (Fin m)) (v : Vec m) : Vec m :=
  proj Tᶜ v

theorem subst_add {m : ℕ} (T : Finset (Fin m)) (u v : Vec m) :
    subst T (u + v) = subst T u + subst T v :=
  proj_add Tᶜ u v

theorem subst_zero {m : ℕ} (T : Finset (Fin m)) : subst T (0 : Vec m) = 0 :=
  proj_zero Tᶜ

/-- The substituted value of a basis vector: `0` if its variable is substituted, itself
otherwise. -/
theorem subst_basisVec {m : ℕ} (T : Finset (Fin m)) (i : Fin m) :
    subst T (basisVec i) = if i ∈ T then 0 else basisVec i := by
  unfold subst
  rw [proj_basisVec]
  by_cases h : i ∈ T
  · have h' : i ∉ Tᶜ := by simpa using h
    rw [if_neg h', if_pos h]
  · have h' : i ∈ Tᶜ := by simpa using h
    rw [if_pos h', if_neg h]

/-- Substituting a smaller set after a larger one changes nothing. -/
theorem subst_subst_of_subset {m : ℕ} {T T' : Finset (Fin m)} (h : T ⊆ T') (v : Vec m) :
    subst T' (subst T v) = subst T' v := by
  funext i
  unfold subst
  by_cases hi : i ∈ T'
  · have h1 : i ∉ T'ᶜ := by simpa using hi
    simp [proj, h1]
  · have h1 : i ∈ T'ᶜ := by simpa using hi
    have h2 : i ∉ T := fun hc => hi (h hc)
    simp [proj, h1, h2]

/-- Substituting a larger set after a smaller one: the smaller substitution is subsumed. -/
theorem subst_subst_of_subset' {m : ℕ} {T T' : Finset (Fin m)} (h : T ⊆ T') (v : Vec m) :
    subst T (subst T' v) = subst T' v := by
  funext i
  unfold subst
  by_cases hi : i ∈ T'
  · have h1 : i ∉ T'ᶜ := by simpa using hi
    simp [proj, h1]
  · have h1 : i ∈ T'ᶜ := by simpa using hi
    have h2 : i ∉ T := fun hc => hi (h hc)
    simp [proj, h1, h2]

/-! ### Cancelled gates -/

variable {N : ℕ}

/-- The vector carried by an operand slot of the `k`-th gate. -/
noncomputable def slotVal (c : VecAddChain N) (k : Fin c.L) : Fin N ⊕ Fin k.1 → Vec N :=
  chainPool c.y k.1 (le_of_lt k.2)

theorem gate_eq_slots (c : VecAddChain N) (k : Fin c.L) :
    c.y k = slotVal c k (gateFst c k) + slotVal c k (gateSnd c k) :=
  gateFst_add_gateSnd c k

/-- The values already available before the `k`-th gate after the substitution `T`: the zero
vector, the surviving variables, and the substituted values of the earlier gates. -/
def avail (c : VecAddChain N) (T : Finset (Fin N)) (k : Fin c.L) (v : Vec N) : Prop :=
  v = 0 ∨ (∃ i : Fin N, i ∉ T ∧ v = basisVec i) ∨
    (∃ j : Fin c.L, j.1 < k.1 ∧ v = subst T (c.y j))

/-- The `k`-th gate is cancelled by the substitution `T`: its value is already available. -/
def dead (c : VecAddChain N) (T : Finset (Fin N)) (k : Fin c.L) : Prop :=
  avail c T k (subst T (c.y k))

/-- The set of gates cancelled by the substitution `T`. -/
noncomputable def kills (c : VecAddChain N) (T : Finset (Fin N)) : Finset (Fin c.L) := by
  classical
  exact Finset.univ.filter (fun k => dead c T k)

theorem mem_kills {c : VecAddChain N} {T : Finset (Fin N)} {k : Fin c.L} :
    k ∈ kills c T ↔ dead c T k := by
  classical
  simp [kills]

/-- The substituted value of an operand slot is available. -/
theorem avail_slot (c : VecAddChain N) (T : Finset (Fin N)) (k : Fin c.L)
    (x : Fin N ⊕ Fin k.1) : avail c T k (subst T (slotVal c k x)) := by
  rcases x with i | j
  · have h1 : slotVal c k (Sum.inl i) = basisVec i := rfl
    rw [h1, subst_basisVec]
    by_cases h : i ∈ T
    · exact Or.inl (by simp [h])
    · exact Or.inr (Or.inl ⟨i, h, by simp [h]⟩)
  · exact Or.inr (Or.inr ⟨⟨j.1, lt_of_lt_of_le j.2 (le_of_lt k.2)⟩, j.2, rfl⟩)

/-- Availability is preserved when the substituted set grows. -/
theorem avail_mono {c : VecAddChain N} {T T' : Finset (Fin N)} (h : T ⊆ T') {k : Fin c.L}
    {v : Vec N} (hv : avail c T k v) : avail c T' k (subst T' v) := by
  rcases hv with h0 | ⟨i, hi, hiv⟩ | ⟨j, hj, hjv⟩
  · exact Or.inl (by rw [h0, subst_zero])
  · rw [hiv, subst_basisVec]
    by_cases hmem : i ∈ T'
    · exact Or.inl (by simp [hmem])
    · exact Or.inr (Or.inl ⟨i, hmem, by simp [hmem]⟩)
  · rw [hjv, subst_subst_of_subset h]
    exact Or.inr (Or.inr ⟨j, hj, rfl⟩)

/-- Cancellation is monotone: a gate cancelled by `T` stays cancelled when more variables are
substituted. -/
theorem dead_mono {c : VecAddChain N} {T T' : Finset (Fin N)} (h : T ⊆ T') {k : Fin c.L}
    (hd : dead c T k) : dead c T' k := by
  have h' := avail_mono (c := c) (k := k) h hd
  rwa [subst_subst_of_subset h] at h'

/-! ### The cascade: one new cancelled gate per attached variable -/

/-- A variable is attached to the chain after the substitution `T` if some gate that is still
live has `e_p` as an operand. -/
def attachedAt (c : VecAddChain N) (T : Finset (Fin N)) (p : Fin N) : Prop :=
  ∃ k : Fin c.L, ¬ dead c T k ∧
    (subst T (slotVal c k (gateFst c k)) = basisVec p ∨
     subst T (slotVal c k (gateSnd c k)) = basisVec p)

/-- Substituting an attached variable cancels the gate it is attached to. -/
theorem dead_insert_of_attached {c : VecAddChain N} {T : Finset (Fin N)} {p : Fin N}
    (hp : p ∉ T) {k : Fin c.L}
    (h : subst T (slotVal c k (gateFst c k)) = basisVec p ∨
         subst T (slotVal c k (gateSnd c k)) = basisVec p) :
    dead c (insert p T) k := by
  have hsub : T ⊆ insert p T := fun x hx => Finset.mem_insert_of_mem hx
  have hpT : p ∈ insert p T := Finset.mem_insert_self p T
  have hzero : ∀ x : Fin N ⊕ Fin k.1,
      subst T (slotVal c k x) = basisVec p → subst (insert p T) (slotVal c k x) = 0 := by
    intro x hx
    rw [← subst_subst_of_subset hsub (slotVal c k x), hx, subst_basisVec]
    simp [hpT]
  show avail c (insert p T) k (subst (insert p T) (c.y k))
  rw [gate_eq_slots c k, subst_add]
  rcases h with hf | hs
  · rw [hzero _ hf, zero_add]
    exact avail_slot c (insert p T) k (gateSnd c k)
  · rw [hzero _ hs, add_zero]
    exact avail_slot c (insert p T) k (gateFst c k)

theorem kills_mono {c : VecAddChain N} {T T' : Finset (Fin N)} (h : T ⊆ T') :
    kills c T ⊆ kills c T' := by
  intro k hk
  rw [mem_kills] at hk ⊢
  exact dead_mono h hk

/-- Substituting an attached variable cancels at least one *new* gate. -/
theorem kills_card_insert {c : VecAddChain N} {T : Finset (Fin N)} {p : Fin N}
    (hp : p ∉ T) (hatt : attachedAt c T p) :
    (kills c T).card + 1 ≤ (kills c (insert p T)).card := by
  obtain ⟨k, hnd, hslot⟩ := hatt
  have hkT : k ∉ kills c T := by rw [mem_kills]; exact hnd
  have hkT' : k ∈ kills c (insert p T) := by
    rw [mem_kills]
    exact dead_insert_of_attached hp hslot
  have hsub : kills c T ⊆ kills c (insert p T) :=
    kills_mono (fun x hx => Finset.mem_insert_of_mem hx)
  have h2 : insert k (kills c T) ⊆ kills c (insert p T) := Finset.insert_subset hkT' hsub
  have h1 : (insert k (kills c T)).card = (kills c T).card + 1 :=
    Finset.card_insert_of_notMem hkT
  calc (kills c T).card + 1 = (insert k (kills c T)).card := h1.symm
    _ ≤ (kills c (insert p T)).card := Finset.card_le_card h2

/-! ### The set of variables that are not charged -/

/-- The variables of `S` that are attached to no live gate at the moment they are substituted
(the variables passing to the extended set `X_M` of the paper), substituting `S` in increasing
order. -/
noncomputable def freeSet (c : VecAddChain N) (S : Finset (Fin N)) : Finset (Fin N) := by
  classical
  exact S.filter (fun p => ¬ attachedAt c (S.filter (fun q => q < p)) p)

theorem mem_freeSet {c : VecAddChain N} {S : Finset (Fin N)} {p : Fin N} :
    p ∈ freeSet c S ↔ p ∈ S ∧ ¬ attachedAt c (S.filter (fun q => q < p)) p := by
  classical
  simp [freeSet]

theorem freeSet_subset (c : VecAddChain N) (S : Finset (Fin N)) : freeSet c S ⊆ S := by
  classical
  intro p hp
  rw [mem_freeSet] at hp
  exact hp.1

/-! ### The counting theorem -/

theorem card_le_kills_add_free (c : VecAddChain N) (S : Finset (Fin N)) :
    S.card ≤ (kills c S).card + (freeSet c S).card := by
  classical
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => absurd (hlt a h) (lt_irrefl a)
    have ha_free : a ∉ freeSet c s := fun h => ha (freeSet_subset c s h)
    have hfilter_a : (insert a s).filter (fun q : Fin N => q < a) = s := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hq | hq, hlt'⟩
        · exact absurd (hq ▸ hlt') (lt_irrefl a)
        · exact hq
      · intro hq
        exact ⟨Or.inr hq, hlt q hq⟩
    have hfilter_p : ∀ p ∈ s,
        (insert a s).filter (fun q : Fin N => q < p) = s.filter (fun q : Fin N => q < p) := by
      intro p hp
      ext q
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hq | hq, hlt'⟩
        · exact absurd (hq ▸ hlt') (not_lt.mpr (le_of_lt (hlt p hp)))
        · exact ⟨hq, hlt'⟩
      · rintro ⟨hq, hlt'⟩
        exact ⟨Or.inr hq, hlt'⟩
    have hfree : freeSet c (insert a s) =
        if attachedAt c s a then freeSet c s else insert a (freeSet c s) := by
      by_cases hatt : attachedAt c s a
      · rw [if_pos hatt]
        ext p
        simp only [mem_freeSet, Finset.mem_insert, Finset.mem_filter]
        constructor
        · rintro ⟨hp, hna⟩
          rcases hp with rfl | hps
          · exact absurd hatt (by rwa [hfilter_a] at hna)
          · exact ⟨hps, by rwa [hfilter_p p hps] at hna⟩
        · rintro ⟨hps, hna⟩
          exact ⟨Or.inr hps, by rwa [hfilter_p p hps]⟩
      · rw [if_neg hatt]
        ext p
        simp only [mem_freeSet, Finset.mem_insert, Finset.mem_filter]
        constructor
        · rintro ⟨hp, hna⟩
          rcases hp with rfl | hps
          · exact Or.inl rfl
          · exact Or.inr ⟨hps, by rwa [hfilter_p p hps] at hna⟩
        · rintro (rfl | ⟨hps, hna⟩)
          · exact ⟨Or.inl rfl, by rwa [hfilter_a]⟩
          · exact ⟨Or.inr hps, by rwa [hfilter_p p hps]⟩
    have hcard : (insert a s).card = s.card + 1 := Finset.card_insert_of_notMem ha
    by_cases hatt : attachedAt c s a
    · have hk := kills_card_insert ha hatt
      have hfr : (freeSet c (insert a s)).card = (freeSet c s).card := by
        rw [hfree, if_pos hatt]
      omega
    · have hkc : (kills c s).card ≤ (kills c (insert a s)).card :=
        Finset.card_le_card (kills_mono (fun x hx => Finset.mem_insert_of_mem hx))
      have hfr : (freeSet c (insert a s)).card = (freeSet c s).card + 1 := by
        rw [hfree, if_neg hatt, Finset.card_insert_of_notMem ha_free]
      omega

/-- **The cascade count**: substituting the variables of `S` cancels all but `#(freeSet c S)` of
them. -/
theorem card_le_length_add_free (c : VecAddChain N) (S : Finset (Fin N)) :
    S.card ≤ c.L + (freeSet c S).card := by
  have h := card_le_kills_add_free c S
  have hk : (kills c S).card ≤ c.L := by
    have h' := Finset.card_le_univ (kills c S)
    simpa using h'
  omega

/-! ### The cascade count in the paper's form -/

/-- The zero entries of `B`, encoded as `Fin (n*n)`. -/
noncomputable def zeroSet {n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) : Finset (Fin (n*n)) := by
  classical
  exact Finset.univ.filter (fun p => B (mmOut p).1 (mmOut p).2 = 0)

theorem card_zeroSet {n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (zeroSet B).card + boolWeight B = n * n := by
  classical
  simpa [zeroSet] using card_zero_entries B

/-- **Lemma 2 of Section 3, exact form with the cascade.**
For a bilinear algorithm for `MM n` with `r` products whose phases are computed by the chains
`cα`, `cβ`, `cγ`,

`n² + n·L*(B) ≤ ν(B) + (L(cα) + L(cβ) + L(cγ)) + #(freeSet cα (zeroSet B))`.

The set `freeSet cα (zeroSet B)` is the paper's extended set `X_M`: substituting the zero entries
of `B` in increasing order cancels one additive gate per zero entry outside it, with no factor
`2` and no gate charged twice. -/
theorem cascade_count {n r : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (D : BilDecomp (MM n) r) (cα : VecAddChain (n*n)) (cβ : VecAddChain (n*n))
    (cγ : VecAddChain r) (hα : cα.Computes D.alpha) (hβ : cβ.Computes D.beta)
    (hγ : cγ.Computes D.gamma) :
    n * n + n * Lstar B ≤
      boolWeight B + (cα.L + cβ.L + cγ.L) + (freeSet cα (zeroSet B)).card := by
  have hZ := card_zeroSet B
  have hc := card_le_length_add_free cα (zeroSet B)
  have hs := Lstar_specialization_MM B D cβ cγ hβ hγ
  omega


/-! ## The product layer: routing products to outputs -/

open scoped BigOperators

/-! ### The inputs covered by a finite set of values -/

variable {N : ℕ}

/-- The inputs occurring in at least one of the vectors of `T`. -/
noncomputable def coveredInputs (T : Finset (Vec N)) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun q => ∃ v ∈ T, v q ≠ 0)

theorem mem_coveredInputs {T : Finset (Vec N)} {q : Fin N} :
    q ∈ coveredInputs T ↔ ∃ v ∈ T, v q ≠ 0 := by
  classical
  simp [coveredInputs]

/-- Enlarging the set of values can only enlarge the set of covered inputs. -/
theorem coveredInputs_mono {T T' : Finset (Vec N)} (h : T ⊆ T') :
    coveredInputs T ⊆ coveredInputs T' := by
  intro q hq
  rw [mem_coveredInputs] at hq ⊢
  obtain ⟨v, hv, hvq⟩ := hq
  exact ⟨v, h hv, hvq⟩

/-- A set of values that are all either `0` or variables covers at most `#T` inputs. -/
theorem card_coveredInputs_of_vars (T : Finset (Vec N))
    (hT : ∀ v ∈ T, v = 0 ∨ ∃ i, v = basisVec i) :
    (coveredInputs T).card ≤ T.card := by
  classical
  refine Finset.card_le_card_of_injOn basisVec ?_ ?_
  · intro q hq
    simp only [Finset.mem_coe] at hq
    obtain ⟨v, hv, hvq⟩ := mem_coveredInputs.mp hq
    rcases hT v hv with h0 | ⟨i, hi⟩
    · rw [h0] at hvq
      exact absurd rfl hvq
    · rw [hi] at hvq hv
      have hiq : i = q := by
        by_contra hne
        exact hvq (by rw [basisVec_apply, if_neg (Ne.symm hne)])
      rwa [hiq] at hv
  · intro a _ b _ h
    exact basisVec_injective h

/-! ### The forest count: `#inputs ≤ L + #outputs` -/

/-- The value of an operand slot of the last gate of a chain is `0`, a variable, or the value of
an earlier gate. -/
theorem chainPool_last_cases {L : ℕ} (y : Fin (L + 1) → Vec N) (x : Fin N ⊕ Fin L) :
    chainPool y L (Nat.le_succ L) x = 0 ∨
      (∃ i, chainPool y L (Nat.le_succ L) x = basisVec i) ∨
      ∃ j : Fin L, chainPool y L (Nat.le_succ L) x = y j.castSucc := by
  rcases x with i | j
  · exact Or.inr (Or.inl ⟨i, rfl⟩)
  · refine Or.inr (Or.inr ⟨j, ?_⟩)
    simp only [chainPool]
    exact congrArg y (Fin.ext rfl)

/-- **The forest count.**  Let `y₀, …, y_{L-1}` be the values of a chain of length `L`, and let
`T` be a finite set of values each of which is `0`, a variable, or one of the `y_k`.  Then the
inputs occurring in the values of `T` are at most `L + #T` in number.  Equivalently, an additive
chain with `L` additions can connect at most `L + #(outputs)` inputs with its outputs. -/
theorem card_coveredInputs_le : ∀ (L : ℕ) (y : Fin L → Vec N),
    (∀ k : Fin L, ∃ a b : Fin N ⊕ Fin k.1,
      y k = chainPool y k.1 (le_of_lt k.2) a + chainPool y k.1 (le_of_lt k.2) b) →
    ∀ T : Finset (Vec N), (∀ v ∈ T, v = 0 ∨ (∃ i, v = basisVec i) ∨ ∃ j, v = y j) →
    (coveredInputs T).card ≤ L + T.card := by
  intro L
  induction L with
  | zero =>
    intro y _ T hT
    have hT' : ∀ v ∈ T, v = 0 ∨ ∃ i, v = basisVec i := by
      intro v hv
      rcases hT v hv with h0 | hb | ⟨j, hj⟩
      · exact Or.inl h0
      · exact Or.inr hb
      · exact absurd j.2 (Nat.not_lt_zero _)
    simpa using card_coveredInputs_of_vars T hT'
  | succ L ih =>
    intro y hy T hT
    obtain ⟨a, b, hlast⟩ := hy (Fin.last L)
    have hy' : ∀ k : Fin L, ∃ a b : Fin N ⊕ Fin k.1,
        (fun j : Fin L => y j.castSucc) k =
          chainPool (fun j : Fin L => y j.castSucc) k.1 (le_of_lt k.2) a +
          chainPool (fun j : Fin L => y j.castSucc) k.1 (le_of_lt k.2) b := by
      intro k
      obtain ⟨a, b, hk⟩ := hy k.castSucc
      exact ⟨a, b, by simpa [chainPool, Fin.castSucc] using hk⟩
    by_cases hmem : y (Fin.last L) ∈ T
    · set v1 : Vec N := chainPool y L (Nat.le_succ L) a with hv1
      set v2 : Vec N := chainPool y L (Nat.le_succ L) b with hv2
      set T' : Finset (Vec N) := insert v1 (insert v2 (T.erase (y (Fin.last L)))) with hT'def
      have hvals : ∀ v : Vec N, (v = v1 ∨ v = v2) →
          v = 0 ∨ (∃ i, v = basisVec i) ∨ ∃ j : Fin L, v = y j.castSucc := by
        rintro v (rfl | rfl)
        · rw [hv1]
          exact chainPool_last_cases y a
        · rw [hv2]
          exact chainPool_last_cases y b
      have hT'mem : ∀ v ∈ T', v = 0 ∨ (∃ i, v = basisVec i) ∨ ∃ j : Fin L, v = y j.castSucc := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact hvals v1 (Or.inl rfl)
        · rcases Finset.mem_insert.mp hv with rfl | hv
          · exact hvals v2 (Or.inr rfl)
          · obtain ⟨hvne, hvT⟩ := Finset.mem_erase.mp hv
            rcases hT v hvT with h0 | hb | ⟨j, hj⟩
            · exact Or.inl h0
            · exact Or.inr (Or.inl hb)
            · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | hjlast
              · exact Or.inr (Or.inr ⟨j', hj⟩)
              · exact absurd (hj.trans (by rw [hjlast])) hvne
      have hcov : coveredInputs T ⊆ coveredInputs T' := by
        intro q hq
        rw [mem_coveredInputs] at hq ⊢
        obtain ⟨v, hv, hvq⟩ := hq
        by_cases hveq : v = y (Fin.last L)
        · have hsum : v1 q + v2 q ≠ 0 := by
            rw [hv1, hv2]
            have hvq' : y (Fin.last L) q ≠ 0 := by rwa [hveq] at hvq
            rwa [hlast] at hvq'
          by_cases h1 : v1 q = 0
          · refine ⟨v2, Finset.mem_insert_of_mem (Finset.mem_insert_self v2 _), ?_⟩
            rwa [h1, zero_add] at hsum
          · exact ⟨v1, Finset.mem_insert_self v1 _, h1⟩
        · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨hveq, hv⟩)), hvq⟩
      have hih := ih (fun j : Fin L => y j.castSucc) hy' T' hT'mem
      have hcard : T'.card ≤ T.card + 1 := by
        have he : (T.erase (y (Fin.last L))).card = T.card - 1 :=
          Finset.card_erase_of_mem hmem
        have hpos : 0 < T.card := Finset.card_pos.mpr ⟨_, hmem⟩
        have h1 : T'.card ≤ (insert v2 (T.erase (y (Fin.last L)))).card + 1 := by
          rw [hT'def]; exact Finset.card_insert_le _ _
        have h2 : (insert v2 (T.erase (y (Fin.last L)))).card
            ≤ (T.erase (y (Fin.last L))).card + 1 := Finset.card_insert_le _ _
        omega
      calc (coveredInputs T).card ≤ (coveredInputs T').card := Finset.card_le_card hcov
        _ ≤ L + T'.card := hih
        _ ≤ L + (T.card + 1) := by omega
        _ = (L + 1) + T.card := by omega
    · have hT' : ∀ v ∈ T, v = 0 ∨ (∃ i, v = basisVec i) ∨
          ∃ j : Fin L, v = y j.castSucc := by
        intro v hv
        rcases hT v hv with h0 | hb | ⟨j, hj⟩
        · exact Or.inl h0
        · exact Or.inr (Or.inl hb)
        · rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | hjlast
          · exact Or.inr (Or.inr ⟨j', hj⟩)
          · exact absurd (by rw [hjlast] at hj; rw [hj] at hv; exact hv) hmem
      have hih := ih (fun j : Fin L => y j.castSucc) hy' T hT'
      omega

/-- **A chain covers at most `L + #rows` inputs.**  For an addition chain `c` with `L` gates
computing a matrix `A` with `k` rows, at most `L + k` inputs occur anywhere in `A`. -/
theorem covered_close {k : ℕ} (c : VecAddChain N) (A : Matrix (Fin k) (Fin N) (ZMod 2))
    (hA : c.Computes A) :
    (Finset.univ.filter (fun q : Fin N => ∃ s : Fin k, A s q ≠ 0)).card ≤ c.L + k := by
  classical
  have hT : ∀ v ∈ (Finset.univ.image A : Finset (Vec N)),
      v = 0 ∨ (∃ i, v = basisVec i) ∨ ∃ j, v = c.y j := by
    intro v hv
    obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hv
    have h := hA s
    rw [Set.mem_union, Set.mem_union, Set.mem_range, Set.mem_range, Set.mem_singleton_iff] at h
    rcases h with (hb | hc) | h0
    · obtain ⟨i, hi⟩ := hb
      exact Or.inr (Or.inl ⟨i, hi.symm⟩)
    · obtain ⟨j, hj⟩ := hc
      exact Or.inr (Or.inr ⟨j, hj.symm⟩)
    · exact Or.inl h0
  have hmain := card_coveredInputs_le c.L c.y c.valid _ hT
  have hcov : (Finset.univ.filter (fun q : Fin N => ∃ s : Fin k, A s q ≠ 0)) ⊆
      coveredInputs (Finset.univ.image A : Finset (Vec N)) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨-, s, hs⟩ := hq
    exact mem_coveredInputs.mpr ⟨A s, Finset.mem_image_of_mem A (Finset.mem_univ s), hs⟩
  have hcard : (Finset.univ.image A : Finset (Vec N)).card ≤ k := by
    have := Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := A)
    simpa using this
  calc (Finset.univ.filter (fun q : Fin N => ∃ s : Fin k, A s q ≠ 0)).card
      ≤ (coveredInputs (Finset.univ.image A : Finset (Vec N))).card := Finset.card_le_card hcov
    _ ≤ c.L + (Finset.univ.image A : Finset (Vec N)).card := hmain
    _ ≤ c.L + k := by omega

/-! ### The products of a bilinear algorithm, and Theorem 1 -/

/-- **Theorem 1 applied to a square matrix**: `L*(B) ≤ 3n`. -/
theorem Lstar_le_three_mul {n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    Lstar B ≤ 3 * n := by
  have h := theorem1 B
  omega

/-- The products of a bilinear algorithm for `MM n` that contribute to at least one output
entry: the formal counterpart of the paper's `µ`, the number of multiplication elements that are
actually connected with an output. -/
noncomputable def usedProducts {n r : ℕ} (D : BilDecomp (MM n) r) : Finset (Fin r) := by
  classical
  exact Finset.univ.filter (fun s => ∃ t : Fin (n * n), D.gamma t s ≠ 0)

theorem mem_usedProducts {n r : ℕ} {D : BilDecomp (MM n) r} {s : Fin r} :
    s ∈ usedProducts D ↔ ∃ t : Fin (n * n), D.gamma t s ≠ 0 := by
  classical
  simp [usedProducts]

/-- If every product contributes to some output then all `r` products are used. -/
theorem usedProducts_card_eq {n r : ℕ} (D : BilDecomp (MM n) r)
    (hused : ∀ s : Fin r, ∃ t : Fin (n * n), D.gamma t s ≠ 0) :
    (usedProducts D).card = r := by
  classical
  have hsub : usedProducts D = Finset.univ := by
    ext s
    rw [mem_usedProducts]
    exact ⟨fun _ => Finset.mem_univ s, fun _ => hused s⟩
  rw [hsub]
  simp

/-- **The topological bound `µ ≤ L + n²`.**  In a bilinear algorithm for `MM n`, the γ-phase is an
addition chain with the `r` products as inputs and the `n²` entries of the product as outputs;
each contributing product has to be connected with some output, so at most `L(cγ) + n²` products
can contribute.  This is the paper's "at least `µ − n²` additive elements are needed just to
connect every multiplication element with some output". -/
theorem usedProducts_card_le {n r : ℕ} (D : BilDecomp (MM n) r) (cγ : VecAddChain r)
    (hγ : cγ.Computes D.gamma) :
    (usedProducts D).card ≤ cγ.L + n * n := by
  classical
  have h := covered_close (N := r) (k := n * n) cγ D.gamma hγ
  simpa [usedProducts] using h

/-- The paper's topological bound in the form `µ − n² ≤ L(cγ)`, for a decomposition all of whose
products contribute to an output. -/
theorem products_le_length_add_outputs {n r : ℕ} (D : BilDecomp (MM n) r) (cγ : VecAddChain r)
    (hγ : cγ.Computes D.gamma) (hused : ∀ s : Fin r, ∃ t : Fin (n * n), D.gamma t s ≠ 0) :
    r ≤ cγ.L + n * n := by
  have h := usedProducts_card_le D cγ hγ
  have hfull := usedProducts_card_eq D hused
  rwa [hfull] at h

/-! ### The case `µ > 5n²` -/

/-- **Lemma 2, case `µ > 5n²`.**  If the bilinear algorithm for `MM n` has more than `5n²`
contributing products, then its additive cost already exceeds `n·L*(B) + n²`: the routing bound
`µ ≤ L(cγ) + n²` and Theorem 1 (`L*(B) ≤ 3n`) give `L(cγ) ≥ µ − n² > 4n² ≥ n·L*(B) + n²`.  No
substitution count, and hence no correction term, is needed in this case. -/
theorem large_products_case {n r : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (D : BilDecomp (MM n) r) (cγ : VecAddChain r) (hγ : cγ.Computes D.gamma)
    (hr : 5 * (n * n) ≤ (usedProducts D).card) :
    n * n + n * Lstar B ≤ boolWeight B + cγ.L := by
  set m : ℕ := n * n with hm
  have hr5 : 5 * m ≤ (usedProducts D).card := hr
  have hrout : (usedProducts D).card ≤ cγ.L + m := by
    have h := usedProducts_card_le D cγ hγ
    rwa [hm]
  have hL : n * Lstar B ≤ 3 * m := by
    calc n * Lstar B ≤ n * (3 * n) := Nat.mul_le_mul_left n (Lstar_le_three_mul B)
      _ = 3 * m := by rw [hm]; ring
  have hgoal : m + n * Lstar B ≤ boolWeight B + cγ.L := by omega
  rwa [hm] at hgoal

/-! ### Assembling the two cases -/

/-- The zero entries of `B` form at most `n²` variables. -/
theorem card_freeSet_le {n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (c : VecAddChain (n * n)) : (freeSet c (zeroSet B)).card ≤ n * n := by
  have h := card_zeroSet B
  have hsub := freeSet_subset c (zeroSet B)
  have := Finset.card_le_card hsub
  omega

/-- **Lemma 2 assembled from both cases, at the level of `Bil+(MM n)`.**

The correction term is only assumed in the regime `µ ≤ 5n²` of the paper: if
`#(usedProducts D) ≤ 5n²` then the extended set `X_M = freeSet cα (zeroSet B)` of the algorithm is
assumed to have at most `C` elements (the paper's (3.2) gives `C = 10n`), and otherwise the
topological bound of `large_products_case` proves the estimate outright. -/
theorem bilplus_of_correction {n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) (C : ℕ)
    (hC : ∀ (r : ℕ) (D : BilDecomp (MM n) r) (cα : VecAddChain (n*n)) (cβ : VecAddChain (n*n))
      (cγ : VecAddChain r),
      cα.Computes D.alpha → cβ.Computes D.beta → cγ.Computes D.gamma →
      (usedProducts D).card ≤ 5 * (n * n) → (freeSet cα (zeroSet B)).card ≤ C) :
    n * n + n * Lstar B ≤ boolWeight B + C + BilPlus (MM n) := by
  obtain ⟨r, D, cα, cβ, cγ, hα, hβ, hγ, hsum⟩ :=
    Nat.sInf_mem (BilPlusSet_nonempty (MM n))
  change n * n + n * Lstar B ≤ boolWeight B + C + sInf (BilPlusSet (MM n))
  by_cases hsmall : (usedProducts D).card ≤ 5 * (n * n)
  · have h := cascade_count B D cα cβ cγ hα hβ hγ
    have hf := hC r D cα cβ cγ hα hβ hγ hsmall
    omega
  · push Not at hsmall
    have h := large_products_case B D cγ hγ (le_of_lt hsmall)
    omega

/-! ## The ports of the product layer: `n·|X_M| ≤ µ` -/

open scoped BigOperators

variable {N : ℕ}

/-! ### Substitution and availability -/

/-- A coordinate outside the substituted set is unchanged by the substitution. -/
theorem subst_apply_of_not_mem {m : ℕ} {T : Finset (Fin m)} {v : Vec m} {q : Fin m}
    (hq : q ∉ T) : subst T v q = v q := by
  unfold subst
  exact proj_apply_mem Tᶜ v (by simpa using hq)

/-! ### Isolation of a free variable -/

/-- **A free variable is isolated in the live part of the chain.**  If `p` is not attached to
any live gate for the substitution `T`, then every gate whose substituted value contains `p`
has value exactly `e_p`.  Otherwise the first gate whose value contains `p` together with
another surviving variable would exhibit `e_p` in one of its operand slots. -/
theorem subst_chain_eq_basis {c : VecAddChain N} {T : Finset (Fin N)} {p : Fin N}
    (hfree : ¬ attachedAt c T p) :
    ∀ (m : ℕ) (k : Fin c.L), k.1 = m → (subst T (c.y k)) p ≠ 0 →
      subst T (c.y k) = basisVec p := by
  intro m
  refine Nat.strongRecOn m ?_
  intro m ih k hk hv
  by_cases hdead : dead c T k
  · unfold dead avail at hdead
    rcases hdead with h0 | ⟨i, -, hiv⟩ | ⟨j, hjlt, hjv⟩
    · rw [h0] at hv
      exact absurd rfl hv
    · rw [hiv] at hv ⊢
      have hip : i = p := by
        by_contra hne
        exact hv (by rw [basisVec_apply, if_neg (Ne.symm hne)])
      rw [hip]
    · rw [hjv] at hv ⊢
      exact ih j.1 (by omega) j rfl hv
  · exfalso
    apply hfree
    refine ⟨k, hdead, ?_⟩
    have hsplit : (subst T (slotVal c k (gateFst c k))) p +
        (subst T (slotVal c k (gateSnd c k))) p ≠ 0 := by
      have h : (subst T (c.y k)) p = (subst T (slotVal c k (gateFst c k))) p +
          (subst T (slotVal c k (gateSnd c k))) p := by
        rw [gate_eq_slots c k, subst_add]
        rfl
      rw [← h]
      exact hv
    have hstep : ∀ x : Fin N ⊕ Fin k.1,
        (subst T (slotVal c k x)) p ≠ 0 → subst T (slotVal c k x) = basisVec p := by
      intro x hx
      rcases x with i | j
      · rw [show slotVal c k (Sum.inl i) = basisVec i from rfl, subst_basisVec] at hx ⊢
        by_cases hi : i ∈ T
        · simp [hi] at hx
        · rw [if_neg hi]
          congr 1
          by_contra hne
          exact hx (by rw [if_neg hi, basisVec_apply, if_neg (Ne.symm hne)])
      · have hval : slotVal c k (Sum.inr j) =
            c.y ⟨j.1, lt_of_lt_of_le j.2 (le_of_lt k.2)⟩ := rfl
        rw [hval] at hx ⊢
        exact ih j.1 (by omega) ⟨j.1, lt_of_lt_of_le j.2 (le_of_lt k.2)⟩ rfl hx
    have hdisj : (subst T (slotVal c k (gateFst c k))) p ≠ 0 ∨
        (subst T (slotVal c k (gateSnd c k))) p ≠ 0 := by
      by_contra hc
      rw [not_or] at hc
      have h1 : (subst T (slotVal c k (gateFst c k))) p = 0 := by
        by_contra h
        exact hc.1 h
      have h2 : (subst T (slotVal c k (gateSnd c k))) p = 0 := by
        by_contra h
        exact hc.2 h
      exact hsplit (by rw [h1, h2, add_zero])
    rcases hdisj with h1 | h2
    · exact Or.inl (hstep _ h1)
    · exact Or.inr (hstep _ h2)

/-- The rows computed by a chain are `0`, a basis vector, or a value of the chain. -/
theorem mem_computes_row {m : ℕ} {c : VecAddChain N}
    {A : Matrix (Fin m) (Fin N) (ZMod 2)} {s : Fin m} (h : c.Computes A) :
    A s = 0 ∨ (∃ i, A s = basisVec i) ∨ ∃ k : Fin c.L, A s = c.y k := by
  have h' := h s
  simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at h'
  rcases h' with (⟨i, hi⟩ | ⟨k, hk⟩) | h0
  · exact Or.inr (Or.inl ⟨i, hi.symm⟩)
  · exact Or.inr (Or.inr ⟨k, hk.symm⟩)
  · exact Or.inl h0

/-- A row containing a free variable is already reduced to that basis vector. -/
theorem subst_row_eq_basis_of_free {c : VecAddChain N} {T : Finset (Fin N)} {p : Fin N}
    (hpT : p ∉ T) (hfree : ¬ attachedAt c T p) {A : Vec N}
    (hA : A = 0 ∨ (∃ i, A = basisVec i) ∨ ∃ k : Fin c.L, A = c.y k)
    (hAp : A p ≠ 0) : subst T A = basisVec p := by
  rcases hA with h0 | ⟨i, hi⟩ | ⟨k, hk⟩
  · rw [h0] at hAp
    exact absurd rfl hAp
  · rw [hi, subst_basisVec]
    rw [hi] at hAp
    have hip : i = p := by
      by_contra hne
      exact hAp (by rw [basisVec_apply, if_neg (Ne.symm hne)])
    rw [hip, if_neg hpT]
  · rw [hk] at hAp ⊢
    exact subst_chain_eq_basis hfree k.1 k rfl (by rwa [subst_apply_of_not_mem hpT])

/-- **At most one variable of `X_M` per row.**  If `p` and `q` are both free for `S` and `p ≠ q`,
no row of the chain has a nonzero coefficient at both.  Assume `p < q`; the row, reduced by the
substitutions below `p`, is `e_p` and therefore vanishes at `q`. -/
theorem freeSet_row_unique {c : VecAddChain N} {S : Finset (Fin N)} {p q : Fin N}
    (hp : p ∈ freeSet c S) (hq : q ∈ freeSet c S) (hne : p ≠ q) {A : Vec N}
    (hA : A = 0 ∨ (∃ i, A = basisVec i) ∨ ∃ k : Fin c.L, A = c.y k) :
    A p = 0 ∨ A q = 0 := by
  classical
  rw [mem_freeSet] at hp hq
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · by_cases hAp : A p = 0
    · exact Or.inl hAp
    · refine Or.inr ?_
      have hpT : p ∉ S.filter (fun q => q < p) := by simp
      have hsub := subst_row_eq_basis_of_free hpT hp.2 hA hAp
      have hqT : q ∉ S.filter (fun q' => q' < p) := by
        rw [Finset.mem_filter]
        exact fun h => absurd h.2 (by omega)
      have h0 : (subst (S.filter (fun q' => q' < p)) A) q = 0 := by
        rw [hsub]
        rw [basisVec_apply, if_neg (Ne.symm hne)]
      rwa [subst_apply_of_not_mem hqT] at h0
  · by_cases hAq : A q = 0
    · exact Or.inr hAq
    · refine Or.inl ?_
      have hqT : q ∉ S.filter (fun q' => q' < q) := by simp
      have hsub := subst_row_eq_basis_of_free hqT hq.2 hA hAq
      have hpT : p ∉ S.filter (fun q' => q' < q) := by
        rw [Finset.mem_filter]
        exact fun h => absurd h.2 (by omega)
      have h0 : (subst (S.filter (fun q' => q' < q)) A) p = 0 := by
        rw [hsub]
        rw [basisVec_apply, if_neg hne]
      rwa [subst_apply_of_not_mem hpT] at h0

/-! ### The slice of matrix multiplication -/

/-- **Every variable enters at least `n` contributing products.**  Fix `p = (i,k)` and
substitute `x_p = 1`, all other `X` variables to `0`.  The decomposition `D` then expresses the
system of the `n` forms `y_{k,j}` as a sum of the products with `α_{s,p} ≠ 0`, whose bilinear
rank is `n`; hence at least `n` such products.  The rank bound is applied to the `n × n`
identity, recovered as `y_{k,j}` in the output slot `(i,j)`. -/
theorem alpha_support_used_ge {n r : ℕ} (D : BilDecomp (MM n) r) (p : Fin (n*n)) :
    n ≤ ((usedProducts D).filter (fun s => D.alpha s p ≠ 0)).card := by
  classical
  set X : Finset (Fin r) := (usedProducts D).filter (fun s => D.alpha s p ≠ 0) with hX
  let i : Fin n := (mmOut p).1
  let k : Fin n := (mmOut p).2
  have hp : mmIn (i, k) = p := mmIn_mmOut p
  have hMM : ∀ a b : Fin n, MM n (mmIn (i, a)) p (mmIn (k, b)) =
      (1 : Matrix (Fin n) (Fin n) (ZMod 2)) a b := by
    intro a b
    rw [← hp]
    simp only [MM, mmOut_mmIn, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      simp
    · have hba : ¬ b = a := fun h => hab h.symm
      simp [hab, hba]
  have hzero : ∀ a b : Fin n, ∀ s : Fin r, s ∉ X →
      D.gamma (mmIn (i, a)) s * (D.alpha s p * D.beta s (mmIn (k, b))) = 0 := by
    intro a b s hs
    rw [hX, Finset.mem_filter, not_and] at hs
    by_cases hg : D.gamma (mmIn (i, a)) s = 0
    · rw [hg, zero_mul]
    · have hsu : s ∈ usedProducts D := mem_usedProducts.mpr ⟨mmIn (i, a), hg⟩
      have ha : D.alpha s p = 0 := by
        by_contra hc
        exact hs hsu hc
      rw [ha]
      simp
  have hrep : ∀ a b : Fin n, (1 : Matrix (Fin n) (Fin n) (ZMod 2)) a b =
      ∑ s ∈ X, D.gamma (mmIn (i, a)) s * (D.alpha s p * D.beta s (mmIn (k, b))) := by
    intro a b
    rw [← hMM a b, D.rep (mmIn (i, a)) p (mmIn (k, b))]
    simp only [mul_assoc]
    exact (Finset.sum_subset (Finset.subset_univ X) (fun s _ hs => hzero a b s hs)).symm
  have hrank := rank_le_card_of_rowExpansion (M := (1 : Matrix (Fin n) (Fin n) (ZMod 2)))
    (σ := {s : Fin r // s ∈ X})
    (u := fun s a => D.gamma (mmIn (i, a)) s.1)
    (v := fun s b => D.alpha s.1 p * D.beta s.1 (mmIn (k, b)))
    (by
      intro a b
      rw [hrep a b]
      exact Finset.sum_subtype X (fun s => Iff.rfl)
        (fun s => D.gamma (mmIn (i, a)) s * (D.alpha s p * D.beta s (mmIn (k, b)))))
  calc n = (1 : Matrix (Fin n) (Fin n) (ZMod 2)).rank := by
        rw [Matrix.rank_one, Fintype.card_fin]
    _ ≤ Fintype.card {s : Fin r // s ∈ X} := hrank
    _ = X.card := by rw [Fintype.card_subtype]; simp

/-! ### The double count `n·|X_M| ≤ µ` -/

/-- **Every product contains at most one variable of `X_M`.**  A row of `α` is a value of the
chain `cα` (or a basis vector or `0`), and `freeSet_row_unique` says that two free variables
cannot both occur in such a value. -/
theorem freeSet_alpha_row_le_one {n r : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (D : BilDecomp (MM n) r) (cα : VecAddChain (n*n)) (hα : cα.Computes D.alpha)
    (s : Fin r) : ((freeSet cα (zeroSet B)).filter (fun p => D.alpha s p ≠ 0)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro p hp q hq
  simp only [Finset.mem_filter] at hp hq
  by_contra hne
  rcases freeSet_row_unique hp.1 hq.1 hne (mem_computes_row hα) with h0 | h0
  · exact hp.2 h0
  · exact hq.2 h0

/-- **The paper's estimate (3.2), sharpened: `n·|X_M| ≤ µ`.**  Every variable of `X_M` enters at
least `n` contributing products, and every product contains at most one variable of `X_M`; hence
the total number `n·|X_M|` of incidences is at most the number `µ` of products.  In particular
`n·|X_M| ≤ 2µ`. -/
theorem card_freeSet_mul_le_usedProducts {n r : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2))
    (D : BilDecomp (MM n) r) (cα : VecAddChain (n*n)) (hα : cα.Computes D.alpha) :
    (freeSet cα (zeroSet B)).card * n ≤ (usedProducts D).card := by
  classical
  set X := freeSet cα (zeroSet B) with hX
  set P := usedProducts D with hP
  have hvar : ∀ p ∈ X, n ≤ (P.filter (fun s => D.alpha s p ≠ 0)).card :=
    fun p _ => alpha_support_used_ge D p
  have hprod : ∀ s ∈ P, (X.filter (fun p => D.alpha s p ≠ 0)).card ≤ 1 :=
    fun s _ => freeSet_alpha_row_le_one B D cα hα s
  have hswap : ∑ p ∈ X, (P.filter (fun s => D.alpha s p ≠ 0)).card =
      ∑ s ∈ P, (X.filter (fun p => D.alpha s p ≠ 0)).card := by
    have h1 : ∀ p : Fin (n*n), (P.filter (fun s => D.alpha s p ≠ 0)).card =
        ∑ s ∈ P, (if D.alpha s p ≠ 0 then 1 else 0) := by
      intro p
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have h2 : ∀ s : Fin r, (X.filter (fun p => D.alpha s p ≠ 0)).card =
        ∑ p ∈ X, (if D.alpha s p ≠ 0 then 1 else 0) := by
      intro s
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    simp only [h1, h2]
    exact Finset.sum_comm
  have hsum : X.card * n ≤ ∑ p ∈ X, (P.filter (fun s => D.alpha s p ≠ 0)).card := by
    have h1 : ∑ _p ∈ X, (n : ℕ) = X.card * n := by
      rw [Finset.sum_const, smul_eq_mul]
    rw [← h1]
    exact Finset.sum_le_sum hvar
  have hb : ∑ s ∈ P, (X.filter (fun p => D.alpha s p ≠ 0)).card ≤ ∑ _s ∈ P, (1 : ℕ) :=
    Finset.sum_le_sum hprod
  have hc : (∑ _s ∈ P, (1 : ℕ)) = P.card := by
    rw [Finset.sum_const, smul_eq_mul, mul_one]
  calc X.card * n ≤ ∑ p ∈ X, (P.filter (fun s => D.alpha s p ≠ 0)).card := hsum
    _ = ∑ s ∈ P, (X.filter (fun p => D.alpha s p ≠ 0)).card := hswap
    _ ≤ ∑ _s ∈ P, (1 : ℕ) := hb
    _ = P.card := hc

/-! ## The exact form of Lemma 2 -/

 /-- **Lemma 2 of Section 3.**
`n² + n·L*(B) ≤ ν(B) + 5n + Bil+(MM n)`, i.e.
`Bil+(MM n) ≥ n·L*(B) + n² − ν(B) − 5n`.  The correction `5n` comes from `µ ≤ 5n²` together
with the sharp count `n·|X_M| ≤ µ`; outside the regime `µ ≤ 5n²` the topological bound alone
proves the estimate. -/
theorem lemma2 {n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    n * n + n * Lstar B ≤ boolWeight B + 5 * n + BilPlus (MM n) := by
  classical
  refine bilplus_of_correction B (5 * n) ?_
  intro r D cα cβ cγ hα hβ hγ hsmall
  have hx := card_freeSet_mul_le_usedProducts B D cα hα
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 := card_freeSet_le B cα
    simpa using h0
  · have h : (freeSet cα (zeroSet B)).card * n ≤ (5 * n) * n := by
      calc (freeSet cα (zeroSet B)).card * n ≤ (usedProducts D).card := hx
        _ ≤ 5 * (n * n) := hsmall
        _ = (5 * n) * n := by ring
    exact Nat.le_of_mul_le_mul_right h hn

/-- **Lemma 2 in the paper's subtracted shape.**  Over `ℤ`, where the truncated subtraction of
`ℕ` cannot distort the correction,

`n·L*(B) + n² − ν(B) − 5n ≤ Bil+(MM n)`.

This is the same statement as `lemma2`, written in the form of (3.1) with the explicit
`O(n)` term `5n`. -/
theorem lemma2_sub {n : ℕ} (B : Matrix (Fin n) (Fin n) (ZMod 2)) :
    (n : ℤ) * Lstar B + ((n : ℤ) * n - boolWeight B) - 5 * n ≤ (BilPlus (MM n) : ℤ) := by
  have h := lemma2 B
  have h' : ((n * n + n * Lstar B : ℕ) : ℤ) ≤
      ((boolWeight B + 5 * n + BilPlus (MM n) : ℕ) : ℤ) := by
    exact_mod_cast h
  push_cast at h' ⊢
  linarith

end AchainsComplexityGF2
