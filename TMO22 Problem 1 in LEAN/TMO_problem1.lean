import Mathlib.Tactic
import Mathlib.Util.Delaborators

set_option warningAsError false

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Factorization.PrimePow

ืnamespace Nat
variable (n : Nat)

--- Definition of the divisor function d(n) = number of divisors
def num_divisor (n : Nat) :=
  Finset.card (Nat.divisors n)

def Burapha (n : Nat) :=
  --- n is Burapha iff n is non-zero, d(n) is odd, and its divisor k < l satisfies d(k) ≤ d(l)
  n > 0 ∧ Odd (num_divisor n) ∧ (∀ k l, k < l → k ∣ n → l ∣ n → num_divisor (k) ≤ num_divisor (l))

lemma mul_cancel_iff_coprime {a b c d : ℕ} (h₁ : gcd a d = 1) (h₂ : gcd b c = 1) (h₃ : a * b = c * d) : a = c := by
  apply Nat.dvd_antisymm ?_ ?_ --- It suffices to show that a | c and c | a
  · have : a ∣ c * d := by
      use b; symm; assumption
    apply Nat.Coprime.dvd_of_dvd_mul_right h₁ this
  · have : c ∣ a * b := by
      use d;
    apply Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.symm h₂) this

lemma gcd_of_gcd {k n m : ℕ} (h₁ : k ∣ m * n) (h₃ : gcd m n = 1) : gcd (gcd k m * k) (gcd k m * n) = k := by
  calc
    gcd (gcd k m * k) (gcd k m * n) = gcd (gcd (k * k) (m * k)) (gcd k m * n) :=  by
      simp
    _= gcd (gcd (k * k) (m * k)) (gcd (k * n) (m * n)) := by
      simp
    _= gcd (k * k) (gcd (m * k) (gcd (k * n) (m * n))) := by
      convert Nat.gcd_assoc ?_ ?_ ?_
    _= gcd (k * k) (gcd (gcd (m * k) (k * n)) (m * n)) := by
      congr 1
      symm
      convert Nat.gcd_assoc ?_ ?_ ?_
    _= gcd (k * k) (gcd (k) (m * n)) := by
      have : gcd (m * k) (k * n) = k :=
        calc
          gcd (m * k) (k * n) = gcd (m * k) (n * k) := by congr 1; ring
          _= (gcd m n) * k := by apply Nat.gcd_mul_right _ _
          _= k := by rw [h₃]; ring
      rw [this]
    _= gcd (k * k) (k) := by
      have : gcd (k) (m * n) = k := by
        apply Nat.gcd_eq_left_iff_dvd.mpr
        exact h₁
      rw [this]
    _= k := by
      have : k ∣ k * k := by
        use k
      convert Nat.gcd_comm ?_ ?_
      symm
      apply Nat.gcd_eq_left_iff_dvd.mpr this

lemma num_divisor_multiplicative {n m : ℕ} (h : gcd n m = 1) (nnonneg : n ≠ 0) (mnonneg : m ≠ 0) : num_divisor (n * m) = num_divisor n * num_divisor m := by
  rw [num_divisor, num_divisor, num_divisor] --- Unravel the definitions in terms of sets
  convert Finset.card_product _ _ ---It is enough to show that the cardinalities of these sets are equal
  symm
  apply Finset.card_bij ?_ ?_ ?_ ?_ --- We construct a bijection between divisors of n * m and and pairs (a, b) of divisors of n and m
  · rintro ⟨a, b⟩ ab_are_divisors
    use a * b             --- The bijection is (a, b) ↦ a * b
  --- Show that the bijection has the required domain and range
  · rintro ⟨a, b⟩ ab_are_divisors
    simp at ab_are_divisors --- Simplify the definition
    simp
    constructor
    · apply mul_dvd_mul ab_are_divisors.1.1 ab_are_divisors.2.1
    · use ab_are_divisors.1.2
  --- Show that this is injective
  · rintro ⟨a, b⟩ ab_are_divisors ⟨c, d⟩ cd_are_divisors
    simp at ab_are_divisors cd_are_divisors
    simp
    intro abeqcd --- Suppose a * b = c * d
    --- We will use the cancellation theorem if coprime. First we need the conditions
    have gcdad : gcd a d = 1 := by
        apply Nat.Coprime.coprime_dvd_left ab_are_divisors.1.1
        apply Nat.Coprime.coprime_dvd_right cd_are_divisors.2.1 h
    have gcdbc : gcd b c = 1 := by
        apply Nat.Coprime.coprime_dvd_left ab_are_divisors.2.1
        apply Nat.Coprime.symm
        apply Nat.Coprime.coprime_dvd_left cd_are_divisors.1.1 h
    constructor
    · apply mul_cancel_iff_coprime gcdad gcdbc abeqcd --- This shows a = c
    · rw [mul_comm a b, mul_comm c d] at abeqcd
      apply mul_cancel_iff_coprime gcdbc gcdad abeqcd --- By symmetry, b = d
  --- Show that this is surjective
  · intro k kdivnm --- Suppose k | n * m
    have knonneg : k ≠ 0 := by --- Divisor of nonzero number is non-zero
      simp at kdivnm
      refine Nat.pos_iff_ne_zero.mp ?_
      apply Nat.pos_of_dvd_of_pos kdivnm.1
      refine Nat.mul_pos ?_ ?_ <;> (apply Nat.pos_iff_ne_zero.mpr; assumption)
    set kn := k / (gcd k m)
    set km := k / (gcd k n)
    use (kn, km) --- Need to show that kn * km = k
    simp
    constructor
    · constructor
      · constructor
        · simp [kn]
          use (n * gcd k m)/k
          --- Show that k / gcd k m * (n * gcd k m / k) = n in natural number arithmetic
          --- We need to be careful because division is defined by rounding down.
          symm
          calc
            (k / gcd k m) * (n * gcd k m / k) = ((k / gcd k m) * (n * gcd k m))/k := by
              --- This is possible if k ∣ n * gcd k m
              symm
              convert Nat.mul_div_assoc (k / gcd k m) ?_
              have : n * gcd k m = gcd (n * k) (n * m) := by
                symm
                apply Nat.gcd_mul_left n k m
              rw [this]
              apply dvd_gcd
              · use n; ring
              simp at kdivnm
              apply kdivnm.1
            _= ((n * gcd k m) * (k / gcd k m))/k := by rw [mul_comm]
            _= ((n * gcd k m) * k )/ gcd k m /k := by
              congr; symm
              convert Nat.mul_div_assoc (n * gcd k m) ?_
              exact gcd_dvd_left k m
            _= ((n * gcd k m) * k )/ (gcd k m * k) := by
              apply Nat.div_div_eq_div_mul
            _= (n * gcd k m)/ (gcd k m) := by
              apply Nat.mul_div_mul_right
              exact Nat.zero_lt_of_ne_zero knonneg
            _= n := by
              apply Nat.mul_div_left n
              apply Nat.zero_lt_of_ne_zero (gcd_ne_zero_of_left knonneg)
        exact nnonneg
      · constructor
        · simp [km]
          use (m * gcd k n)/k
          --- Same calculation. I believe we can use WLOG here, but I don't understand it
          symm
          calc
            (k / gcd k n) * (m * gcd k n / k) = ((k / gcd k n) * (m * gcd k n))/k := by
              --- This is possible if k ∣ m * gcd k n
              symm
              convert Nat.mul_div_assoc (k / gcd k n) ?_
              have : m * gcd k n = gcd (m * k) (m * n) := by
                symm
                apply Nat.gcd_mul_left m k n
              rw [this]
              apply dvd_gcd
              · use m; ring
              simp at kdivnm
              rw [mul_comm]
              apply kdivnm.1
            _= ((m * gcd k n) * (k / gcd k n))/k := by rw [mul_comm]
            _= ((m * gcd k n) * k )/ gcd k n /k := by
              congr; symm
              convert Nat.mul_div_assoc (m * gcd k n) ?_
              exact gcd_dvd_left k n
            _= ((m * gcd k n) * k )/ (gcd k n * k) := by
              apply Nat.div_div_eq_div_mul
            _= (m * gcd k n)/ (gcd k n) := by
              apply Nat.mul_div_mul_right
              exact Nat.zero_lt_of_ne_zero knonneg
            _= m := by
              apply Nat.mul_div_left m
              apply Nat.zero_lt_of_ne_zero (gcd_ne_zero_of_left knonneg)
        · exact mnonneg
    --- Finally we show that kn * km = k; just pure computation
    simp [kn, km]
    calc
      k / gcd k m * (k / gcd k n) = (k / gcd k m * k) / gcd k n := by
        symm;
        convert Nat.mul_div_assoc ?_ (gcd_dvd_left k n)
      _= (k * (k / gcd k m)) / gcd k n := by
        congr 1; rw [← mul_comm]
      _= (k * k)/ gcd k m / gcd k n := by
        symm; congr
        convert Nat.mul_div_assoc ?_ (gcd_dvd_left k m)
      _= (k * k)/ (gcd k m * gcd k n) := by
        apply Nat.div_div_eq_div_mul
      _= (k * k)/(gcd ((gcd k m) * k) ((gcd k m)* n)) := by
        congr; symm
        apply Nat.gcd_mul_left (gcd k m) _ _
      _= (k * k) / k := by
        have : gcd ((gcd k m) * k) ((gcd k m)* n) = k := by
          simp at kdivnm
          rw [mul_comm] at kdivnm
          have : gcd n m = gcd m n := Nat.gcd_comm _ _
          rw [this] at h
          apply gcd_of_gcd (kdivnm.1) (h)
        congr;
      _= k := by
        have : k ∣ k := by use 1; ring
        apply Nat.mul_div_left _ (Nat.zero_lt_of_ne_zero knonneg)

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    apply zero_le

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn

lemma num_divisor_prime_power {p : ℕ} (k : ℕ) (hn : Nat.Prime p) : num_divisor (p ^ k) = (k + 1) := by
  induction' k using Nat.strong_induction_on with k ih
  by_cases keqzero : k =0
  · simp [keqzero] at ⊢
    rw [num_divisor, Nat.divisors_one]
    simp
  · have : 1 ≤ k := by
      exact Nat.one_le_iff_ne_zero.mpr keqzero
    have divisor : Nat.divisors (p ^ k) = insert (p ^ (k)) (Nat.divisors (p ^ (k - 1))) := by
      ext m
      constructor
      · intro mdivpk
        simp at mdivpk
        have : m ∣ p^k := mdivpk.1
        have misprimpow : ∃ i ≤ k, m = p ^ i := by
          apply (Nat.dvd_prime_pow hn).mp
          exact this
        simp
        have ⟨i,ilek,misptoipow⟩ := misprimpow
        by_cases iisk : i = k
        · left;
          rwa [← iisk]
        · right
          have : i ≠ k := by apply iisk
          have : i < k := by
            exact Nat.lt_of_le_of_ne ilek iisk
          constructor
          · apply (Nat.dvd_prime_pow hn).mpr
            use i
            constructor
            · (expose_names; exact (Nat.le_sub_one_iff_lt this_1).mpr this)
            assumption
          intro piszero
          exfalso
          have : 2 ≤ p := by
            apply (Nat.prime_def_le_sqrt.mp hn).1
          linarith
      · simp
        intro mdivpkm1
        rcases mdivpkm1 with h1 | h2
        · constructor
          · rw [h1]
          intro piszero
          exfalso
          have : 2 ≤ p := by
            apply (Nat.prime_def_le_sqrt.mp hn).1
          linarith
        · constructor
          have mdiv : m ∣ (p ^ (k - 1)) * p := by
            have ⟨foo, bar⟩ := h2
            exact Nat.dvd_mul_right_of_dvd foo p
          have ppowrw : p ^ k = p ^ (k - 1) * p := by
            (expose_names; exact Eq.symm (Nat.pow_pred_mul this))
          rw [ppowrw]
          exact mdiv
          intro piszero
          exfalso
          have : 2 ≤ p := by
            apply (Nat.prime_def_le_sqrt.mp hn).1
          linarith
    rw [num_divisor, divisor]
    convert Finset.card_insert_of_not_mem ?_
    · symm
      have h₀ : k - 1 < k := by
        exact Nat.sub_one_lt_of_lt this
      specialize ih (k-1) h₀
      rw [num_divisor] at ih
      rw [ih]
      exact Nat.sub_add_cancel this
    · simp
      intro pkdivpkminone
      have iden : p^k = p^(k - 1) * p := by exact Eq.symm (Nat.pow_pred_mul this)
      have pkminonedivpk : p ^ (k - 1) ∣ p ^ k := by
        rw [iden]
        exact Nat.dvd_mul_right (p ^ (k - 1)) p
      have : p ^ k = p^(k - 1) := by
        exact Nat.dvd_antisymm pkdivpkminone pkminonedivpk
      have : p^(k - 1) * p = p^(k -1) := by
        rwa [← iden]
      have : p = 1 := by
        have ppownotzero : p^(k-1) ≠ 0 := by
          refine pow_ne_zero (k - 1) ?_
          have pgetwo : 2 ≤ p := by
            apply (Nat.prime_def.mp hn).1
          linarith
        convert (Nat.mul_eq_left ppownotzero).mp _
        assumption
      exfalso
      have pgetwo : 2 ≤ p := by
        apply (Nat.prime_def.mp hn).1
      linarith

lemma num_divisor_eq_prod (n : ℕ) (hn : 1 ≤ n) : num_divisor n = ∏ p ∈ Nat.divisors n with Nat.Prime p, ((n.factorization p) + 1) := by
  --- Use the lemma that multiplicative function can be evaluated using factorization
  convert Nat.multiplicative_factorization _ _ _ _
  --- We show that the left and right hand sides are equal by evaluating at each prime factor
  · symm
    dsimp
    rw [Finsupp.prod]
    rw [Nat.support_factorization]
    apply Finset.prod_bij (fun x ha ↦ x) _ _
    --- In LEAN, this is done by showing first that there is a bijection between the range of both sides
    · rintro a hyp
      simp at hyp ⊢
      have ⟨⟨h1, h2⟩, h3⟩ := hyp
      exact ⟨by assumption, by assumption, by assumption⟩
    · rintro a ha
      simp at ha ⊢
      have ⟨h1, ⟨h2, h3⟩⟩ := ha
      apply num_divisor_prime_power
      exact h1
    · rintro a ha
      simp at ha ⊢
      have ⟨⟨h1, h2⟩, h3⟩ := ha
      exact ⟨by assumption, by assumption, by assumption⟩
    · rintro a₁ ha₁ a₂ ha₂
      simp
  --- We now use the fact that num_divisor is multiplicative
  · rintro x y xcy
    by_cases xoryeqzero : x = 0 ∨ y = 0
    · rcases xoryeqzero with h | h <;>
      · rw [h]
        simp
        rw [num_divisor, Nat.divisors_zero, Finset.card_eq_zero.mpr]
        ring
        rfl
    · push_neg at xoryeqzero
      have xneqzero : x ≠ 0 := xoryeqzero.1
      have yneqzero : y ≠ 0 := xoryeqzero.2
      apply num_divisor_multiplicative
      <;> assumption
  · rw [num_divisor, Nat.divisors_one]
    simp
  · linarith

---
lemma prod_odd_iff_all_odd (S : Finset ℕ) (f : ℕ → ℕ) (hS : Nonempty S) : Odd (∏ i ∈ S, f i) ↔ ∀ i ∈ S, Odd (f i) := by
  constructor
  · intro odd
    by_contra naodd
    push_neg at naodd
    have ⟨iex, ⟨iins, finotodd⟩⟩ := naodd
    have fieven : Even (f iex) := by exact Nat.not_odd_iff_even.mp finotodd
    rw [Even] at fieven
    have ⟨r, hr⟩ := fieven
    have : f iex = 2 * r := by rw [hr]; ring
    set S' := (S \ {iex}) ∪ {iex} with S'_def
    have : {iex} ⊆ S := by
      simpa
    have div1 : (∏ i ∈ {iex}, f i) ∣ (∏ i ∈ S, f i) := by
      apply Finset.prod_dvd_prod_of_subset {iex} S _ this
    have equality : ∏ i ∈ {iex}, f i = 2 * r := by
      simpa
    have div2 : 2 ∣ ∏ i ∈ {iex}, f i := by
      use r
    have divProd : 2 ∣ (∏ i ∈ S, f i) := by
      apply Nat.dvd_trans div2 div1
    have : Even (∏ i ∈ S, f i) :=
      (even_iff_exists_two_nsmul (∏ i ∈ S, f i)).mpr divProd
    have : ¬ Odd (∏ i ∈ S, f i) := Nat.not_odd_iff_even.mpr this
    contradiction
  · rintro fai
    apply Finset.prod_induction_nonempty
    · intro a b odda oddb
      have ⟨k, hk⟩ := odda
      have ⟨l, hl⟩ := oddb
      use (2 * k * l + k + l)
      rw [hk, hl]
      ring
    · exact Finset.nonempty_coe_sort.mp hS
    · intro x xS
      apply fai; exact xS

lemma prod_even_iff_exists_even (S : Finset ℕ) (f : ℕ → ℕ) (hS : Nonempty S) : Even (∏ i ∈ S, f i) ↔ ∃ i ∈ S, Even (f i) := by
  apply not_iff_not.mp
  push_neg
  have h₁ : ¬Even (∏ i ∈ S, f i) ↔ Odd (∏ i ∈ S, f i) := by
    exact Nat.not_even_iff_odd
  have h₂ : (∀ i ∈ S, ¬Even (f i)) ↔ (∀ i ∈ S, Odd (f i)) := by
    refine forall₂_congr ?_
    intro a as
    exact Nat.not_even_iff_odd
  rw [h₁]
  symm
  rw [h₂]
  symm
  convert prod_odd_iff_all_odd _ _ _
  exact hS

lemma square_iff_prime_expo_even (n : ℕ) : (∃ c, n = c^2) ↔ (∀ p ∈ {p ∈ n.divisors | Nat.Prime p}, Odd (n.factorization p + 1)) := by
  by_cases nneqzero : n = 0
  · rw [nneqzero]
    simp
    use 0
    ring
  · constructor
    · rintro ⟨c, hc, rfl⟩
      rintro p pdiv
      simp at pdiv
      have ⟨⟨pdivn, nne0⟩, pprime⟩ := pdiv
      have : (c^2).factorization = (fun x ↦ 2 * c.factorization x) := by
        convert (Nat.factorization_pow c 2)
        simp
        ext p
        simp
      have : (c ^2).factorization p = 2 * c.factorization p := by
        exact congrFun this p
      rw [this]
      use c.factorization p
    · rintro pprime
      simp at pprime
      set f := fun x ↦ (x ^ (n.factorization x / 2)) with f_def
      set S := {x ∈ n.divisors | Nat.Prime x} with S_def
      use ∏ x ∈ S, f x
      symm
      calc
        (∏ x ∈ S, f x)^ 2 = ∏ x ∈ S, ((f x) ^ 2) := by
          symm
          convert Finset.prod_pow {p ∈ n.divisors | Nat.Prime p} 2 f
        _= ∏ x ∈ S, ((fun x ↦ (x ^ ((n.factorization x / 2) * 2))) (x)):= by
          convert Finset.prod_bij (fun x ha ↦ x) ?_ ?_ ?_ ?_
          · intro a ha
            simpa
          · intro a₁ ha₁ a₂ ha₂
            simp
          · intro b ba
            use b
          · intro q ha
            rw [f_def]
            simp
            exact Eq.symm (Nat.pow_mul q (n.factorization q / 2) 2)
        _= ∏ x ∈ S, ((fun x ↦ (x ^ (n.factorization x))) (x)) := by
          simp
          convert Finset.prod_bij (fun x ha ↦ x) ?_ ?_ ?_ ?_
          · intro a ha
            simpa
          · intro a₁ ha₁ a₂ ha₂
            simp
          · intro b ba
            use b
          · intro q ha
            simp
            congr
            refine Nat.div_two_mul_two_of_even ?_
            specialize pprime q _
            · rw [S_def] at ha
              simp at ha
              exact ha.1.1
            · rw [S_def] at ha
              simp at ha
              specialize pprime nneqzero ha.2
              have ⟨c, hc⟩ := pprime
              simp at hc
              use c
              rw [hc]; ring
        _= n := by
          nth_rw 2 [(Nat.factorization_prod_pow_eq_self nneqzero).symm]
          convert Finset.prod_bij (fun x ha ↦ x) ?_ ?_ ?_ ?_
          · rintro a ha
            simp
            rw [S_def] at ha
            simp at ha
            tauto
          · intro a ha b hb
            simp
          · intro b bn
            use b
            have : b ∈ S := by simp at bn; rw [S_def]; simp; tauto
            use this
          · intro a ha
            simp

--- We need a lemma: d(n) is odd if and only if n is a perfect square
lemma num_divisor_odd_iff_square n : n > 0 → (Odd (num_divisor n) ↔ ∃ c, n = c ^ 2) := by
  by_cases none : n = 1
  · rw [none]
    intro hyp
    rw [num_divisor, Nat.divisors_one, Finset.card_singleton]
    constructor
    · intro
      use 1; ring
    · intro
      use 0; ring
  · intro nnezero
    have nge2 : 2 ≤ n := by
      refine two_le ?_ none
      linarith
    constructor --- This is an iff statements, so we break the proof into two parts
    · intro hyp --- hyp is the hypothesis that (num_divisor n) is odd
      rw [num_divisor_eq_prod] at hyp
      have : ∀ p ∈ {p ∈ n.divisors | Nat.Prime p}, Odd (n.factorization p + 1) := by
        convert (prod_odd_iff_all_odd _ _ _).mp hyp
        simp
        have ex_prime : ∃ p, p.Prime ∧ p ∣ n := by
          apply exists_prime_factor nge2
        have ⟨p, pcon1, pcon2⟩ := ex_prime
        use p
        constructor
        · exact ⟨pcon2, by linarith⟩
        · exact pcon1
      rwa [square_iff_prime_expo_even]
      linarith
    · rintro ⟨c, cisnsquare, rfl⟩
      rw [num_divisor_eq_prod, prod_odd_iff_all_odd]
      intro p pa
      use c.factorization p
      have : (c^2).factorization = (fun x ↦ 2 * c.factorization x) := by
        convert (Nat.factorization_pow c 2)
        simp
        ext p
        simp
      have : (c ^2).factorization p = 2 * c.factorization p := by
        exact congrFun this p
      rw [this]
      · have ex_prime : ∃ p, p.Prime ∧ p ∣ c^2 := by
          apply exists_prime_factor nge2
        have ⟨p, pcon⟩ := ex_prime
        use p
        simp
        have : c ≠ 0 := by exact sq_pos_iff.mp nnezero
        tauto
      · linarith

lemma gttwo {n : ℕ} (h₁ : n ≠ 0) (h₂ : n ≠ 1) : 2 ≤ n := by
  induction' n with n ih
  · contradiction
  · by_cases hyp : n = 0
    · rw [hyp]
      simp
      rw [hyp] at h₂
      apply h₂
      simp
    · by_cases hyp' : n = 1
      · rw [hyp']
      · have : 2 ≤ n := by
          apply ih
          exact hyp
          exact hyp'
        exact two_le h₁ h₂

lemma num_divisor_prime {p : ℕ} (hp : Nat.Prime p) : num_divisor p = 2 := by
  rw [num_divisor]
  rw [Nat.Prime.divisors]
  · apply Finset.card_pair
    exact Ne.symm (Nat.Prime.ne_one hp)
  · exact hp

lemma gcd_primes_eq_one {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (nq : p ≠ q) : gcd p q = 1 := by
  have gcddivp : gcd p q ∣ p := gcd_dvd_left p q
  have gcddivq : gcd p q ∣ q := gcd_dvd_right p q
  have gcdoneorp : gcd p q = 1 ∨ gcd p q = p := by
    convert (Nat.dvd_prime hp).mp gcddivp
  have noteqp : gcd p q ≠ p := by
    intro h
    rw [h] at gcddivq
    have : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp gcddivq
    contradiction
  tauto

lemma num_divisor_pq {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (nq : p ≠ q) : num_divisor (p * q) = 4 := by
  calc
    num_divisor (p * q) = num_divisor p * num_divisor q := by
      apply num_divisor_multiplicative
      · apply gcd_primes_eq_one hp hq nq
      · exact Nat.Prime.ne_zero hp
      · exact Nat.Prime.ne_zero hq
    _= 2 * 2 := by
      rw [num_divisor_prime, num_divisor_prime]
      exact hq
      exact hp
    _= 4 := by ring

lemma num_divisor_prime_sq {p : ℕ} (hp : Nat.Prime p) : num_divisor (p ^ 2) = 3 := by
  rw [num_divisor_prime_power 2 hp]

lemma primepow_divisor_ge_1 {n : ℕ} (hn : IsPrimePow n) : 1 ≤ num_divisor n  := by
  rw [IsPrimePow] at hn
  have ⟨p, k, primep, keq0, pkn⟩ := hn
  have primep' : Nat.Prime p := Prime.nat_prime primep
  rw [← pkn]
  have : num_divisor (p ^ k)≥ 1 :=
  calc
    num_divisor (p ^ k) = ∏ x ∈ Nat.divisors (p^k) with Nat.Prime x, (((p^k).factorization x) + 1) := by
      apply num_divisor_eq_prod
      apply one_le_pow_of_one_le' (Nat.Prime.one_le primep') k
    _= ∏ x ∈ {p}, (((p^k).factorization x) + 1) := by
      convert Finset.prod_bij (fun x ha ↦ x) ?_ ?_ ?_ ?_
      · intro q hq
        simp at hq ⊢
        have : q ∣ p ^ k := hq.1.1
        have qisprime : Nat.Prime q := hq.2
        have : q ∣ p := Nat.Prime.dvd_of_dvd_pow qisprime this
        have : q = p := by
          apply (Nat.prime_dvd_prime_iff_eq qisprime primep').mp this
        exact this
      · simp
      · simp
        constructor
        · constructor
          · refine Dvd.dvd.pow ?_ ?_
            · exact Nat.dvd_refl p
            · linarith
          · have : 2 ≤ p := by exact Nat.Prime.two_le primep'
            intro peq0
            linarith
        · exact primep'
      · simp
    _= ((p^k).factorization p) + 1 := by
      exact Finset.prod_singleton (fun x ↦ (p ^ k).factorization x + 1) p
    _= (k * p.factorization p) + 1 := by
      congr
      have : (p^k).factorization = (fun x ↦ k * p.factorization x) := by
        convert (Nat.factorization_pow p k)
        simp
        ext p
        simp
      have : (p ^k).factorization p = k * p.factorization p := by
        exact congrFun this p
      exact this
    _= k * 1 + 1 := by
      congr
      exact Nat.Prime.factorization_self primep'
    _≥ 1 := by linarith
  exact this

theorem main n : Burapha n ↔ (∃ k p, Nat.Prime p ∧ n = p ^ (2 * k)) := by
  constructor
  --- We prove that if Burapha n then it is a square of a prime power
  · intro Bn
    rw [Burapha] at Bn
    ---- Since n has odd number of divisor, it is a perfect square n = c^2
    have nispfsq : ∃ c, n = c ^ 2 := by apply (num_divisor_odd_iff_square n (Bn.1)).mp; apply Bn.2.1
    ---- To prove that c is a prime power, let's clear out the case when c = 1 first
    have ⟨c, neqc2⟩ := nispfsq
    have cneqzero : c ≠ 0 := by
      intro ceqzero
      rw [ceqzero] at neqc2; simp at neqc2
      linarith [Bn.1]
    by_cases hc : 1 = c
    --- The case c = 1, we choose k = 0, p = 2
    · rw [← hc] at neqc2; simp at neqc2
      use 0, 2
      constructor
      · apply Nat.prime_two
      · simpa
    --- Otherwise 2 ≤ c, and so c is a perfect square
    · have cge2 : 2 ≤ c := by
        apply gttwo
        exact cneqzero
        exact fun a ↦ hc (id (Eq.symm a))
      have ⟨nneq, nodddiv, fcon⟩ := Bn
      --- We claim that c is a prime power, by showing that only one prime divides c
      have cisPrimePow : IsPrimePow c := by
        apply (isPrimePow_iff_unique_prime_dvd).mpr
      --- c is greater than 2, so it has a prime divisor
        have ⟨p, pprime, pdivc⟩ : ∃ p, Nat.Prime p ∧ p ∣ c := by
          apply exists_prime_factor; assumption
        use p
        simp
        constructor
        · exact ⟨pprime, pdivc⟩ --- Since p divide c, this is done
        · intro q qprime qdivc --- Now let q be another prime that divides c
          by_contra qnep --- By contradiction, suppose q ≠ p
          wlog h : p < q generalizing p q -- WLOG, let p < q
          · have hnew : q < p := by
              have : (p < q) ∨ (p = q) ∨ (p > q) := by
                exact Nat.lt_trichotomy p q
              rcases this with g | g | g
              · exfalso; contradiction
              · exfalso; contrapose! qnep; exact g.symm
              · exact g
            apply this q qprime qdivc p pprime pdivc (fun a ↦ qnep (id (Eq.symm a))) hnew
          · have numdivpq : num_divisor (p * q) = 4 := by --- But num_divisor (p * q) = 4
              apply num_divisor_pq pprime qprime
              linarith
            have numdivpsq : num_divisor (q^2) = 3 := by --- and num_divisor (q ^ 2) = 3
              apply num_divisor_prime_sq qprime
            have h₁ : num_divisor (p * q) > num_divisor (q ^ 2) := by --- Hence num_divisor (p * q) > num_divisor (q ^ 2)
              rw [numdivpq, numdivpsq]
              linarith
            have h₂ : p * q < q ^ 2 :=
            calc
              p * q < q * q := by
                refine Nat.mul_lt_mul_of_pos_right h ?_
                have : 2 ≤ q := by exact Nat.Prime.two_le qprime
                linarith
              _= q^2 := by ring
            specialize fcon (p * q) (q ^ 2) h₂ --- We will show that this contradicts the second condition
            have h₃ : gcd p q = 1 := by    --- since p, q are primes, gcd(p, q) = 1
              apply gcd_primes_eq_one pprime qprime fun a ↦ qnep (id (Eq.symm a))
            have pmulq_dvdn : p * q ∣ n := by --- therefore p * q | n
              rw [neqc2]
              apply Nat.Coprime.mul_dvd_of_dvd_of_dvd h₃
              exact Dvd.dvd.pow pdivc (by linarith)
              exact Dvd.dvd.pow qdivc (by linarith)
            have h₄ : q ^ 2 ∣  n := by    ---- Since n = c^2 and q | c, we have q^2 | n
              rw [neqc2]
              exact pow_dvd_pow_of_dvd qdivc 2
            specialize fcon pmulq_dvdn h₄ ---- By (2), num_divisor (p * q) ≤ num_divisor (q ^ 2)
            rw [numdivpq, numdivpsq] at fcon --- this means 4 ≤ 3, contradiction
            linarith
      --- If c is prime power, then the rest is just algebra
      · rw [IsPrimePow] at cisPrimePow
        have ⟨p, k, pprime, keq0, con⟩ := cisPrimePow
        use k
        use p
        constructor
        · exact Prime.nat_prime pprime
        · rw [neqc2, ← con]
          ring
  --- For the converse, we show that if n is a square of prime power, then it is burapha, by showing that the two conditions are satisfied
  · intro ⟨m,⟨p, ⟨pprime, condit⟩⟩⟩
    rw [Burapha]
    --- n = 1 is Special
    by_cases P : n = 1
    · constructor
      linarith
      rw [P]
      constructor
      · rw [num_divisor, Nat.divisors_one]
        simp
      · intro k l kleql kdiv1 ldiv1
        have keq1 : k = 1 := Nat.eq_one_of_dvd_one kdiv1
        have leq1 : l = 1 := Nat.eq_one_of_dvd_one ldiv1
        rw [keq1, leq1]
    --- From now one, suppose n ≠ 1
    have ngt0 : 0 < n := by
      rw [condit]
      refine Nat.pow_pos (Nat.Prime.pos pprime)
    have nIsPrimePow : IsPrimePow n := by --- A little lemma, n is a prime power
      have : IsPrimePow (p ^ (2 * m)) := by
        refine (isPrimePow_pow_iff ?_).mpr ?_
        · by_contra h
          rw [h] at condit
          have : n = 1 := by
            rw [condit]; ring
          contradiction
        · exact Nat.Prime.isPrimePow pprime
      · rwa [condit]
    constructor
    · exact ngt0
    · constructor
      --- The number of divisor d(n) is odd by previous lemma
      · apply (num_divisor_odd_iff_square n ngt0).mpr
        use p^m
        rw [condit]
        ring
      --- We now show the second condition. If k is 1 then it is simpler
      · rintro k l kltl kdivn ldivn
        by_cases keq1 : k = 1
        · rw [keq1]
          rw [num_divisor, Nat.divisors_one]
          simp
          apply primepow_divisor_ge_1
          apply IsPrimePow.dvd nIsPrimePow ldivn
          rw [← keq1]
          linarith
        --- FInally suppose k ≠ 1
        rw [condit] at kdivn ldivn
        ---- Since k and l divides a prime power, they must be prime powers
        have ⟨ak, kisPPow⟩ : ∃ ak ≤ 2 * m, k = p ^ (ak) := (Nat.dvd_prime_pow pprime).mp kdivn
        have ⟨al, lisPPow⟩ : ∃ al ≤ 2 * m, l = p ^ (al) := (Nat.dvd_prime_pow pprime).mp ldivn
        rw [kisPPow.2, lisPPow.2]
        ---- But num_divisor(p ^ k ) = k, so we have the following values
        have numDivisork : num_divisor (p ^ ak) = ak + 1 := num_divisor_prime_power ak pprime
        have numDivisorl : num_divisor (p ^ al) = al + 1 := num_divisor_prime_power al pprime
        rw [numDivisork, numDivisorl]
        ---- It remains to show that ak + 1 ≤ al + 1, or eqivalently p ^ (ak) ≤ p^(al), since p > 1
        apply Nat.add_le_add_right
        have pgtone : 1 < p := Nat.Prime.one_lt pprime
        apply (Nat.pow_le_pow_iff_right pgtone).mp
        rw [← kisPPow.2, ← lisPPow.2]
        --- The goal is precisely k ≤ l, and we know that k < l !
        linarith
