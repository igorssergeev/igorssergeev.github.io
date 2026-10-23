/-
# `H[n,k]` is a `B_k`-sequence in `ZMod (2^(r-2))`

Let `k >= 2` and `r = 1 + ceil(k * log_2 p_n)`, where `p_1, p_2, ...` are the odd
primes in increasing order, so that `p_n` is the `n`-th odd prime (in the file,
`oddPrime (n-1)`). For each `i` write `p_i = +- 5 ^ h_i (mod 2^r)` with
`0 <= h_i < 2^(r-2)`; such an `h_i` exists and is unique because the unit group
`(ZMod (2^r))^x` is isomorphic to `<-1> x <5>` (via `reprMap`). The lemma asserts
that the set `H[n,k] = { h_i | i = 1, ..., n }` is a `B_k`-sequence in
`ZMod (2^(r-2))`, i.e. that all `k`-fold sums of its elements are distinct.

## Main results

* `BkSet.main_lemma` : `IsBkSeq k (Hset n k hk)` -- the lemma.
* `BkSet.core` : distinct `k`-multisets have distinct sums of `h`-values.
* `BkSet.reprMap_bijective` : `(ZMod (2^r))^x ~ Fin 2 x Fin (2^(r-2))`, `(j,h) |-> (-1)^j * 5^h`.
* `BkSet.Pprod_injective` : a product of (distinct) odd primes determines its multiset.
-/
import Mathlib

open Nat

namespace BkSet

noncomputable section

/-! ## Part 1: the `±5^h` structure of `(ZMod (2^r))ˣ` -/

def fiveUnit (r : ℕ) : (ZMod (2^r))ˣ :=
  ZMod.unitOfCoprime 5 (Nat.Coprime.pow_right r (by decide))

theorem four_dvd_two_pow (r : ℕ) (hr : 2 ≤ r) : 4 ∣ 2^r := by
  rw [show (4:ℕ) = 2^2 by norm_num]
  exact pow_dvd_pow 2 hr

theorem orderOf_five (r : ℕ) (hr : 2 ≤ r) : orderOf (fiveUnit r) = 2^(r-2) := by
  have h := ZMod.orderOf_five (r - 2)
  rw [show r - 2 + 2 = r by omega] at h
  rw [← orderOf_units]
  simp only [fiveUnit, ZMod.coe_unitOfCoprime]
  exact h

theorem unitsMap_five (r : ℕ) {h : 4 ∣ 2^r} :
    ZMod.unitsMap h (fiveUnit r) = 1 := by
  apply Units.ext
  rw [ZMod.unitsMap_val, Units.val_one, fiveUnit, ZMod.coe_unitOfCoprime, ZMod.cast_natCast h]
  decide

theorem unitsMap_negOne (r : ℕ) {h : 4 ∣ 2^r} :
    ZMod.unitsMap h (-1 : (ZMod (2^r))ˣ) = -1 := by
  apply Units.ext
  rw [ZMod.unitsMap_val, Units.val_neg, Units.val_one, Units.val_neg, Units.val_one,
    ZMod.cast_neg h, ZMod.cast_one h]

def reprMap (r : ℕ) : Fin 2 × Fin (2^(r-2)) → (ZMod (2^r))ˣ :=
  fun p => (-1 : (ZMod (2^r))ˣ)^(p.1:ℕ) * (fiveUnit r)^(p.2:ℕ)

theorem reprMap_injective (r : ℕ) (hr : 2 ≤ r) : Function.Injective (reprMap r) := by
  rintro ⟨a, h⟩ ⟨b, h'⟩ hpq
  have h1 : (-1 : (ZMod 4)ˣ)^(a:ℕ) = (-1 : (ZMod 4)ˣ)^(b:ℕ) := by
    have hmap := congrArg (ZMod.unitsMap (four_dvd_two_pow r hr)) hpq
    simp only [reprMap, map_mul, map_pow, unitsMap_five, unitsMap_negOne, one_pow, mul_one] at hmap
    simpa using hmap
  have hab : a = b := by
    revert h1; fin_cases a <;> fin_cases b <;> decide
  have hh : h = h' := by
    have h5 : (fiveUnit r)^(h:ℕ) = (fiveUnit r)^(h':ℕ) := by
      have hthis := hpq
      simp only [reprMap] at hthis
      rw [hab] at hthis
      exact mul_left_cancel hthis
    have hmod : (h:ℕ) ≡ (h':ℕ) [MOD 2^(r-2)] := by
      have := pow_eq_pow_iff_modEq.mp h5
      rwa [orderOf_five r hr] at this
    exact Fin.ext (Nat.ModEq.eq_of_lt_of_lt hmod h.isLt h'.isLt)
  exact Prod.ext hab hh

theorem reprMap_bijective (r : ℕ) (hr : 2 ≤ r) : Function.Bijective (reprMap r) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨reprMap_injective r hr, ?_⟩
  haveI : NeZero (2^r) := ⟨by positivity⟩
  have hcard : Fintype.card (ZMod (2^r))ˣ = 2 * 2^(r-2) := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime_pow Nat.prime_two (by omega)]
    rw [show (2:ℕ) - 1 = 1 by norm_num, mul_one]
    rw [show 2^(r-1) = 2^(r-2) * 2 by
          rw [show r-1 = (r-2)+1 by omega, pow_add, pow_one], mul_comm]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [hcard]

theorem reprMap_surjective (r : ℕ) (hr : 2 ≤ r) : Function.Surjective (reprMap r) :=
  (reprMap_bijective r hr).2

/-! ## Part 2: odd primes -/

def oddPrime (i : ℕ) : ℕ := Nat.nth Nat.Prime (i+1)

theorem oddPrime_prime (i : ℕ) : (oddPrime i).Prime := Nat.prime_nth_prime (i+1)

theorem three_le_oddPrime (i : ℕ) : 3 ≤ oddPrime i := by
  have h := Nat.add_two_le_nth_prime (i+1)
  simp only [oddPrime]; omega

theorem oddPrime_odd (i : ℕ) : Odd (oddPrime i) :=
  (oddPrime_prime i).odd_of_ne_two (by have := three_le_oddPrime i; omega)

theorem oddPrime_strictMono : StrictMono oddPrime := by
  intro a b hab
  simp only [oddPrime]
  exact (Nat.nth_lt_nth Nat.infinite_setOfPred_prime).mpr (Nat.succ_lt_succ hab)

theorem oddPrime_injective : Function.Injective oddPrime := oddPrime_strictMono.injective

theorem oddPrime_le {i n : ℕ} (h : i < n) : oddPrime i ≤ oddPrime (n-1) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · omega
  · exact oddPrime_strictMono.monotone (by omega)

def oddPrimeUnit (r i : ℕ) : (ZMod (2^r))ˣ :=
  ZMod.unitOfCoprime (oddPrime i)
    (Nat.Coprime.pow_right r (Nat.coprime_two_right.mpr (oddPrime_odd i)))

theorem oddPrimeUnit_coe (r i : ℕ) :
    ((oddPrimeUnit r i : (ZMod (2^r))ˣ) : ZMod (2^r)) = oddPrime i :=
  ZMod.coe_unitOfCoprime _ _

theorem factorization_oddPrime_self (i : ℕ) :
    (oddPrime i).factorization (oddPrime i) = 1 :=
  (oddPrime_prime i).factorization_self

theorem factorization_oddPrime_ne {a b : ℕ} (h : a ≠ b) :
    (oddPrime a).factorization (oddPrime b) = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hd
  have heq : oddPrime b = oddPrime a :=
    (Nat.prime_dvd_prime_iff_eq (oddPrime_prime b) (oddPrime_prime a)).mp hd
  exact h (oddPrime_injective heq).symm

end
end BkSet

namespace BkSet

noncomputable section

noncomputable def reprData (r : ℕ) (hr : 2 ≤ r) (i : ℕ) : Fin 2 × Fin (2^(r-2)) :=
  Classical.choose (reprMap_surjective r hr (oddPrimeUnit r i))

theorem reprData_spec (r : ℕ) (hr : 2 ≤ r) (i : ℕ) :
    reprMap r (reprData r hr i) = oddPrimeUnit r i :=
  Classical.choose_spec (reprMap_surjective r hr (oddPrimeUnit r i))

def jj (r : ℕ) (hr : 2 ≤ r) (i : ℕ) : Fin 2 := (reprData r hr i).1
def hh (r : ℕ) (hr : 2 ≤ r) (i : ℕ) : Fin (2^(r-2)) := (reprData r hr i).2

theorem reprData_eq (r : ℕ) (hr : 2 ≤ r) (i : ℕ) :
    reprData r hr i = (jj r hr i, hh r hr i) := rfl

theorem oddPrime_repr (r : ℕ) (hr : 2 ≤ r) (i : ℕ) :
    (oddPrime i : ZMod (2^r)) = (-1)^(jj r hr i : ℕ) * (5 : ZMod (2^r))^((hh r hr i : ℕ)) := by
  have h := congrArg (fun u : (ZMod (2^r))ˣ => (u : ZMod (2^r))) (reprData_spec r hr i)
  rw [reprData_eq] at h
  simp only [reprMap, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    oddPrimeUnit_coe] at h
  exact h.symm

end
end BkSet

namespace BkSet

noncomputable section

def hz (r : ℕ) (hr : 2 ≤ r) (i : ℕ) : ZMod (2^(r-2)) := (hh r hr i : ℕ)

def jsum (r : ℕ) (hr : 2 ≤ r) (a : Multiset ℕ) : ℕ := (a.map (fun i => (jj r hr i : ℕ))).sum
def hsum (r : ℕ) (hr : 2 ≤ r) (a : Multiset ℕ) : ℕ := (a.map (fun i => (hh r hr i : ℕ))).sum
def Pprod (a : Multiset ℕ) : ℕ := (a.map oddPrime).prod

theorem cast_Pprod (r : ℕ) (hr : 2 ≤ r) (a : Multiset ℕ) :
    ((Pprod a : ℕ) : ZMod (2^r)) = (-1)^(jsum r hr a) * (5 : ZMod (2^r))^(hsum r hr a) := by
  induction a using Multiset.induction_on with
  | empty => simp [Pprod, jsum, hsum]
  | cons i a ih =>
    have hcast : ((Pprod (i ::ₘ a) : ℕ) : ZMod (2^r))
        = (oddPrime i : ZMod (2^r)) * ((Pprod a : ℕ) : ZMod (2^r)) := by
      simp only [Pprod, Multiset.map_cons, Multiset.prod_cons, Nat.cast_mul]
    rw [hcast, oddPrime_repr r hr i, ih]
    simp only [jsum, hsum, Multiset.map_cons, Multiset.sum_cons]
    rw [pow_add, pow_add]
    ring

end
end BkSet

namespace BkSet

noncomputable section

theorem Pprod_pos (a : Multiset ℕ) : 0 < Pprod a := by
  induction a using Multiset.induction_on with
  | empty => simp [Pprod]
  | cons i a ih =>
      simp only [Pprod, Multiset.map_cons, Multiset.prod_cons]
      exact Nat.mul_pos (oddPrime_prime i).pos ih

theorem factorization_Pprod (a : Multiset ℕ) (j : ℕ) :
    (Pprod a).factorization (oddPrime j) = a.count j := by
  induction a using Multiset.induction_on with
  | empty => simp [Pprod]
  | cons i a ih =>
      have h1 : Pprod (i ::ₘ a) = oddPrime i * Pprod a := by
        simp only [Pprod, Multiset.map_cons, Multiset.prod_cons]
      rw [h1, Nat.factorization_mul (oddPrime_prime i).ne_zero (Pprod_pos a).ne']
      simp only [Finsupp.add_apply]
      rcases eq_or_ne i j with h | h
      · subst h
        rw [factorization_oddPrime_self, ih, Multiset.count_cons_self]
        omega
      · rw [factorization_oddPrime_ne h, ih, Multiset.count_cons_of_ne h.symm]
        omega

theorem Pprod_injective {a b : Multiset ℕ} (h : Pprod a = Pprod b) : a = b := by
  apply Multiset.ext.mpr
  intro j
  have := congrArg (fun x : ℕ => x.factorization (oddPrime j)) h
  simpa only [factorization_Pprod] using this

theorem Pprod_bound {n k : ℕ} (a : Multiset ℕ) (ha : a.card ≤ k)
    (hall : ∀ i ∈ a, i < n) : Pprod a ≤ oddPrime (n-1)^k := by
  have key : ∀ a : Multiset ℕ, (∀ i ∈ a, i < n) → Pprod a ≤ oddPrime (n-1)^a.card := by
    intro a
    induction a using Multiset.induction_on with
    | empty => intro _; simp [Pprod]
    | cons i a ih =>
        intro h
        have hi : oddPrime i ≤ oddPrime (n-1) := oddPrime_le (h i (by simp))
        have hrec : Pprod a ≤ oddPrime (n-1)^a.card := ih (fun j hj => h j (by simp [hj]))
        simp only [Pprod, Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons] at hrec ⊢
        calc oddPrime i * (a.map oddPrime).prod
            ≤ oddPrime (n-1) * oddPrime (n-1)^a.card := Nat.mul_le_mul hi hrec
          _ = oddPrime (n-1) ^ (a.card + 1) := by rw [pow_succ]; ring
  calc Pprod a ≤ oddPrime (n-1)^a.card := key a hall
    _ ≤ oddPrime (n-1)^k := Nat.pow_le_pow_right (by have := three_le_oddPrime (n-1); omega) ha

end
end BkSet

namespace BkSet

noncomputable section

theorem cast_sum_map {N : ℕ} (a : Multiset ℕ) (f : ℕ → ℕ) :
    (a.map (fun i => (f i : ZMod N))).sum = ((a.map f).sum : ZMod N) := by
  induction a using Multiset.induction_on with
  | empty => simp
  | cons i a ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, ih,
        Nat.cast_add]

theorem hsum_hz (r : ℕ) (hr : 2 ≤ r) (a : Multiset ℕ) :
    (a.map (hz r hr)).sum = (hsum r hr a : ZMod (2^(r-2))) := by
  exact cast_sum_map a (fun i => (hh r hr i : ℕ))

theorem core (r : ℕ) (hr : 2 ≤ r) (n k : ℕ)
    (hbound : oddPrime (n-1)^k < 2^(r-1))
    (a b : Multiset ℕ) (ha : ∀ i ∈ a, i < n) (hb : ∀ j ∈ b, j < n)
    (hca : a.card ≤ k) (hcb : b.card ≤ k)
    (hsum_eq : (a.map (hz r hr)).sum = (b.map (hz r hr)).sum) : a = b := by
  have hmod : hsum r hr a ≡ hsum r hr b [MOD 2^(r-2)] := by
    have h2 := hsum_eq
    rw [hsum_hz r hr a, hsum_hz r hr b] at h2
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h2
  have hfive : (fiveUnit r)^(hsum r hr a) = (fiveUnit r)^(hsum r hr b) := by
    rw [pow_eq_pow_iff_modEq, orderOf_five r hr]; exact hmod
  have h5 : (5 : ZMod (2^r))^(hsum r hr a) = (5 : ZMod (2^r))^(hsum r hr b) := by
    have huu := congrArg (fun u : (ZMod (2^r))ˣ => (u : ZMod (2^r))) hfive
    simp only [Units.val_pow_eq_pow_val] at huu
    rwa [show ((fiveUnit r : (ZMod (2^r))ˣ) : ZMod (2^r)) = 5 from
      ZMod.coe_unitOfCoprime 5 _] at huu
  have hpa : (Pprod a : ZMod (2^r)) = (-1)^(jsum r hr a) * (5 : ZMod (2^r))^(hsum r hr b) := by
    rw [cast_Pprod r hr a, h5]
  have hpb : (Pprod b : ZMod (2^r)) = (-1)^(jsum r hr b) * (5 : ZMod (2^r))^(hsum r hr b) :=
    cast_Pprod r hr b
  have h2le : 2^(r-1) ≤ 2^r := by
    rw [show r = (r-1)+1 by omega, pow_succ']
    exact Nat.le_mul_of_pos_left _ (by norm_num : 0 < 2)
  have hba : Pprod a < 2^(r-1) := lt_of_le_of_lt (Pprod_bound a hca ha) hbound
  have hbb : Pprod b < 2^(r-1) := lt_of_le_of_lt (Pprod_bound b hcb hb) hbound
  have hlt_a : Pprod a < 2^r := lt_of_lt_of_le hba h2le
  have hlt_b : Pprod b < 2^r := lt_of_lt_of_le hbb h2le
  have h2r : 2^(r-1) + 2^(r-1) = 2^r := by
    rw [← two_mul, show (2:ℕ) * 2^(r-1) = 2^((r-1)+1) by rw [pow_succ']]
    congr 1; omega
  have hsum_lt : Pprod a + Pprod b < 2^r := by
    have := Nat.add_lt_add hba hbb; rwa [h2r] at this
  have eqcase : ((Pprod a : ℕ) : ZMod (2^r)) = ((Pprod b : ℕ) : ZMod (2^r)) → a = b := by
    intro heq
    exact Pprod_injective
      (Nat.ModEq.eq_of_lt_of_lt ((ZMod.natCast_eq_natCast_iff _ _ _).mp heq) hlt_a hlt_b)
  have negcase : ((Pprod a : ℕ) : ZMod (2^r)) = -((Pprod b : ℕ) : ZMod (2^r)) → a = b := by
    intro heq
    exfalso
    have h0 : ((Pprod a + Pprod b : ℕ) : ZMod (2^r)) = 0 := by
      rw [Nat.cast_add, heq, neg_add_cancel]
    have hdvd : 2^r ∣ Pprod a + Pprod b := (ZMod.natCast_eq_zero_iff _ _).mp h0
    have hpos : 0 < Pprod a + Pprod b := Nat.add_pos_left (Pprod_pos a) _
    exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.mpr hsum_lt)
  rcases Nat.even_or_odd (jsum r hr a) with hae | hao <;>
    rcases Nat.even_or_odd (jsum r hr b) with hbe | hbo
  · rw [hae.neg_one_pow, one_mul] at hpa
    rw [hbe.neg_one_pow, one_mul] at hpb
    exact eqcase (by rw [hpa, hpb])
  · rw [hae.neg_one_pow, one_mul] at hpa
    rw [hbo.neg_one_pow, neg_one_mul] at hpb
    exact negcase (by rw [hpa, hpb, neg_neg])
  · rw [hao.neg_one_pow, neg_one_mul] at hpa
    rw [hbe.neg_one_pow, one_mul] at hpb
    exact negcase (by rw [hpa, hpb])
  · rw [hao.neg_one_pow, neg_one_mul] at hpa
    rw [hbo.neg_one_pow, neg_one_mul] at hpb
    exact eqcase (by rw [hpa, hpb])

end
end BkSet

namespace BkSet

noncomputable section

def rOf (n k : ℕ) : ℕ :=
  1 + Nat.ceil ((k:ℝ) * Real.logb 2 ((oddPrime (n-1) : ℕ) : ℝ))

theorem rOf_sub (n k : ℕ) :
    rOf n k - 1 = Nat.ceil ((k:ℝ) * Real.logb 2 ((oddPrime (n-1) : ℕ) : ℝ)) := by
  rw [rOf]; omega

theorem rOf_bound (n k : ℕ) (hk : 1 ≤ k) :
    oddPrime (n-1)^k < 2^(rOf n k - 1) := by
  rw [rOf_sub]
  set P : ℕ := oddPrime (n-1) with hP
  set c : ℕ := Nat.ceil ((k:ℝ) * Real.logb 2 ((P:ℕ) : ℝ)) with hc
  have hPodd : Odd P := by rw [hP]; exact oddPrime_odd (n-1)
  have hP3 : 3 ≤ P := by rw [hP]; exact three_le_oddPrime (n-1)
  have hPpos : (0:ℝ) < (P:ℝ) := by exact_mod_cast (by omega : 0 < P)
  have hceil : (k:ℝ) * Real.logb 2 ((P:ℕ):ℝ) ≤ (c:ℝ) := by
    rw [hc]; exact Nat.le_ceil _
  have h2 : ((P:ℝ))^k ≤ (2:ℝ)^c := by
    have key := (Real.rpow_le_rpow_left_iff (show (1:ℝ) < 2 by norm_num)).mpr hceil
    have hkey : (2:ℝ)^((k:ℝ)*Real.logb 2 ((P:ℕ):ℝ)) = (P:ℝ)^k := by
      rw [mul_comm ((k:ℝ)) (Real.logb 2 ((P:ℕ):ℝ)),
        Real.rpow_mul (show (0:ℝ) ≤ 2 by norm_num),
        Real.rpow_logb (b := 2) (by norm_num) (by norm_num) hPpos,
        Real.rpow_natCast]
    rw [hkey, Real.rpow_natCast] at key
    exact key
  have hle : P^k ≤ 2^c := by
    have hcast : ((P^k : ℕ) : ℝ) ≤ ((2^c : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Nat.cast_pow]; exact h2
    exact_mod_cast hcast
  have hne : P^k ≠ 2^c := by
    have hodd : Odd (P^k) := hPodd.pow
    intro hcontra
    rcases Nat.eq_zero_or_pos c with hc0 | hcpos
    · rw [hc0, pow_zero] at hcontra
      have : 1 < P^k := one_lt_pow' (by omega) (by omega)
      omega
    · have hev : Even (2^c) := Even.pow_of_ne_zero (even_two) (by omega)
      rw [← hcontra] at hev
      exact (Nat.not_odd_iff_even.mpr hev) hodd
  exact lt_of_le_of_ne hle hne

end
end BkSet

namespace BkSet

noncomputable section

theorem rOf_ge_two (n k : ℕ) (hk : 1 ≤ k) : 2 ≤ rOf n k := by
  rw [rOf]
  have h1P : (1:ℝ) < ((oddPrime (n-1) : ℕ) : ℝ) :=
    by exact_mod_cast (by have := three_le_oddPrime (n-1); omega : 1 < oddPrime (n-1))
  have hlog : (0:ℝ) < Real.logb 2 ((oddPrime (n-1) : ℕ) : ℝ) :=
    Real.logb_pos (b := 2) (by norm_num) h1P
  have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hX : (0:ℝ) < (k:ℝ) * Real.logb 2 ((oddPrime (n-1) : ℕ) : ℝ) := mul_pos hk0 hlog
  have := Nat.one_le_ceil_iff.mpr hX
  omega

/-- A `k`-sum-distinct set. -/
def IsBkSeq {G : Type*} [AddCommMonoid G] (k : ℕ) (B : Finset G) : Prop :=
  ∀ s t : Multiset G, (∀ x ∈ s, x ∈ B) → (∀ x ∈ t, x ∈ B) →
    s.card = k → t.card = k → s.sum = t.sum → s = t

noncomputable def Hz (n k : ℕ) (hk : 2 ≤ k) (i : ℕ) : ZMod (2^(rOf n k - 2)) :=
  hz (rOf n k) (rOf_ge_two n k (le_trans (by norm_num) hk)) i

noncomputable def Hset (n k : ℕ) (hk : 2 ≤ k) : Finset (ZMod (2^(rOf n k - 2))) :=
  (Finset.range n).image (Hz n k hk)

theorem main_lemma (n k : ℕ) (hk : 2 ≤ k) : IsBkSeq k (Hset n k hk) := by
  have hr : 2 ≤ rOf n k := rOf_ge_two n k (le_trans (by norm_num) hk)
  have hbound : oddPrime (n-1)^k < 2^(rOf n k - 1) := rOf_bound n k (le_trans (by norm_num) hk)
  have hzf : ∀ i, hz (rOf n k) hr i = Hz n k hk i := fun i => rfl
  have hinj : ∀ i j, i < n → j < n → Hz n k hk i = Hz n k hk j → i = j := by
    intro i j hi hj hij
    have heq : (({i} : Multiset ℕ).map (hz (rOf n k) hr)).sum
             = (({j} : Multiset ℕ).map (hz (rOf n k) hr)).sum := by
      simpa [hzf] using hij
    have h := core (rOf n k) hr n k hbound {i} {j} (by simp [hi]) (by simp [hj])
        (by simp; omega) (by simp; omega) heq
    simpa using h
  intro s t hs ht hcs hct hsum
  have key : ∀ (u : Multiset (ZMod (2^(rOf n k - 2)))), (∀ x ∈ u, x ∈ Hset n k hk) →
      ∃ a : Multiset ℕ, (∀ i ∈ a, i < n) ∧ a.card = u.card ∧ (a.map (Hz n k hk)) = u := by
    intro u hu
    refine ⟨u.map (fun x => if hx : x ∈ Hset n k hk then
        Classical.choose (Finset.mem_image.mp hx) else 0), ?_, ?_, ?_⟩
    · intro i hi
      rw [Multiset.mem_map] at hi
      obtain ⟨x, hx, rfl⟩ := hi
      show (if hx : x ∈ Hset n k hk then _ else 0) < n
      rw [dif_pos (hu x hx)]
      exact Finset.mem_range.mp (Classical.choose_spec (Finset.mem_image.mp (hu x hx))).1
    · exact Multiset.card_map _ _
    · rw [Multiset.map_map]
      refine (Multiset.map_congr rfl ?_).trans (Multiset.map_id u)
      intro x hx
      show Hz n k hk (if hx : x ∈ Hset n k hk then _ else 0) = x
      rw [dif_pos (hu x hx)]
      exact (Classical.choose_spec (Finset.mem_image.mp (hu x hx))).2
  obtain ⟨a, ha_lt, ha_card, ha_map⟩ := key s hs
  obtain ⟨b, hb_lt, hb_card, hb_map⟩ := key t ht
  have hsum_ab : (a.map (hz (rOf n k) hr)).sum = (b.map (hz (rOf n k) hr)).sum := by
    have hs' : ((a.map (Hz n k hk)).sum) = ((b.map (Hz n k hk)).sum) := by
      rw [ha_map, hb_map]; exact hsum
    simpa [hzf] using hs'
  have hab := core (rOf n k) hr n k hbound a b ha_lt hb_lt
      (by rw [ha_card]; exact hcs.le) (by rw [hb_card]; exact hct.le) hsum_ab
  rw [← ha_map, ← hb_map, hab]

end
end BkSet

