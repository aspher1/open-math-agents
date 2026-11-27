import OMAReductions.R_Erdos535_erdos_535_R1

/-!
Arithmetic extraction for the main Erdős 535 reduction.

At each prime at most y, retain a largest fiber of the prime exponent and
remove that prime power. Each stage costs at most L + 1 in cardinality.
The resulting integers have no prime factor at most y, so N < y^(K + 1)
bounds their total prime multiplicity by K. One final largest fiber fixes
that multiplicity, at a further cost of K + 1.
-/

open ArithmeticFunction
open scoped ArithmeticFunction.Omega BigOperators

namespace OMA535Extraction

/-- A map into `0,...,L` has a fiber containing at least the average number of points. -/
lemma exists_large_fiber (A : Finset ℕ) (g : ℕ → ℕ) (L : ℕ)
    (hbound : ∀ a ∈ A, g a ≤ L) :
    ∃ e ≤ L, A.card ≤ (L + 1) * (A.filter fun a => g a = e).card := by
  classical
  obtain ⟨e, he, hmax⟩ := Finset.exists_max_image (Finset.range (L + 1))
    (fun j => (A.filter fun a => g a = j).card)
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  refine ⟨e, by simpa using Finset.mem_range.mp he, ?_⟩
  have hsub : A ⊆ (Finset.range (L + 1)).biUnion
      (fun j => A.filter fun a => g a = j) := by
    intro a ha
    refine Finset.mem_biUnion.mpr ⟨g a, Finset.mem_range.mpr ?_, ?_⟩
    · have := hbound a ha
      omega
    · exact Finset.mem_filter.mpr ⟨ha, rfl⟩
  calc
    A.card ≤ ((Finset.range (L + 1)).biUnion
        (fun j => A.filter fun a => g a = j)).card := Finset.card_le_card hsub
    _ ≤ (Finset.range (L + 1)).card * (A.filter fun a => g a = e).card := by
      apply Finset.card_biUnion_le_card_mul
      exact hmax
    _ = (L + 1) * (A.filter fun a => g a = e).card := by simp

/-- Removing the full power of a prime leaves a positive quotient not divisible by it. -/
lemma prime_quotient {a p e : ℕ} (ha : 0 < a) (hp : p.Prime)
    (he : a.factorization p = e) :
    1 ≤ a / p ^ e ∧ p ^ e * (a / p ^ e) = a ∧ ¬ p ∣ a / p ^ e := by
  have hdvd : p ^ e ∣ a := (hp.pow_dvd_iff_le_factorization ha.ne').2 (by omega)
  have hpos : 0 < a / p ^ e := Nat.div_pos (Nat.le_of_dvd ha hdvd) (pow_pos hp.pos e)
  have hcop : Nat.Coprime p (a / p ^ e) := by
    simpa only [he] using Nat.coprime_ordCompl hp ha.ne'
  exact ⟨hpos, Nat.mul_div_cancel' hdvd, hp.coprime_iff_not_dvd.mp hcop⟩

/-- Iteratively remove primes at most `y`, retaining a large fiber at every stage. -/
lemma extract_rough_family (N L : ℕ) (hNL : N < 2 ^ L) (A : Finset ℕ)
    (hA : A ⊆ Finset.Icc 1 N) (y : ℕ) :
    ∃ (s : ℕ) (B : Finset ℕ), 0 < s ∧ B ⊆ Finset.Icc 1 N ∧
      A.card ≤ (L + 1) ^ y * B.card ∧
      (∀ b ∈ B, s * b ∈ A) ∧
      (∀ p, p.Prime → p ≤ y → ∀ b ∈ B, ¬ p ∣ b) := by
  classical
  induction y with
  | zero =>
      refine ⟨1, A, by omega, hA, by simp, ?_, ?_⟩
      · intro b hb
        simpa using hb
      · intro p hp hple b hb
        have := hp.two_le
        omega
  | succ y ih =>
      obtain ⟨s, B, hs, hB, hcard, hscale, hrough⟩ := ih
      by_cases hp : (y + 1).Prime
      · have hfactor : ∀ a ∈ B, a.factorization (y + 1) ≤ L := by
          intro a ha
          apply Nat.factorization_le_of_le_pow
          calc
            a ≤ N := (Finset.mem_Icc.mp (hB ha)).2
            _ ≤ 2 ^ L := hNL.le
            _ ≤ (y + 1) ^ L := Nat.pow_le_pow_left hp.two_le L
        obtain ⟨e, _, hefiber⟩ := exists_large_fiber B
          (fun a => a.factorization (y + 1)) L hfactor
        let C := B.filter fun a => a.factorization (y + 1) = e
        let D := C.image fun a => a / (y + 1) ^ e
        have hspec : ∀ a ∈ C, 1 ≤ a / (y + 1) ^ e ∧
            (y + 1) ^ e * (a / (y + 1) ^ e) = a ∧
            ¬ (y + 1) ∣ a / (y + 1) ^ e := by
          intro a ha
          obtain ⟨haB, hae⟩ := Finset.mem_filter.mp ha
          exact prime_quotient (Finset.mem_Icc.mp (hB haB)).1 hp hae
        have hinj : Set.InjOn (fun a => a / (y + 1) ^ e) (C : Set ℕ) := by
          intro a ha b hb hab
          calc
            a = (y + 1) ^ e * (a / (y + 1) ^ e) := (hspec a ha).2.1.symm
            _ = (y + 1) ^ e * (b / (y + 1) ^ e) := congrArg (fun z => (y + 1) ^ e * z) hab
            _ = b := (hspec b hb).2.1
        have hDC : D.card = C.card := Finset.card_image_of_injOn hinj
        refine ⟨s * (y + 1) ^ e, D, Nat.mul_pos hs (pow_pos hp.pos e), ?_, ?_, ?_, ?_⟩
        · intro b hb
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
          refine Finset.mem_Icc.mpr ⟨(hspec a ha).1, ?_⟩
          exact (Nat.div_le_self _ _).trans
            (Finset.mem_Icc.mp (hB (Finset.mem_filter.mp ha).1)).2
        · calc
            A.card ≤ (L + 1) ^ y * B.card := hcard
            _ ≤ (L + 1) ^ y * ((L + 1) * C.card) := Nat.mul_le_mul_left _ hefiber
            _ = (L + 1) ^ (y + 1) * D.card := by rw [hDC, pow_succ, Nat.mul_assoc]
        · intro b hb
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
          rw [Nat.mul_assoc, (hspec a ha).2.1]
          exact hscale a (Finset.mem_filter.mp ha).1
        · intro p hprime hple b hb
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
          by_cases hpy : p = y + 1
          · simpa [hpy] using (hspec a ha).2.2
          · have hpy' : p ≤ y := by omega
            intro hdvd
            apply hrough p hprime hpy' a (Finset.mem_filter.mp ha).1
            rw [← (hspec a ha).2.1]
            exact dvd_mul_of_dvd_right hdvd _
      · refine ⟨s, B, hs, hB, ?_, hscale, ?_⟩
        · calc
            A.card ≤ (L + 1) ^ y * B.card := hcard
            _ ≤ (L + 1) ^ (y + 1) * B.card :=
              Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by omega))
        · intro p hprime hple b hb
          have hne : p ≠ y + 1 := by
            intro heq
            exact hp (heq ▸ hprime)
          exact hrough p hprime (by omega) b hb

/-- A positive integer with no small prime factor has bounded total prime multiplicity. -/
lemma omega_le_of_rough {N y K b : ℕ} (hy : 2 ≤ y) (hNK : N < y ^ (K + 1))
    (hb : b ∈ Finset.Icc 1 N)
    (hrough : ∀ p, p.Prime → p ≤ y → ¬ p ∣ b) : Ω b ≤ K := by
  have hb0 : b ≠ 0 := by have := (Finset.mem_Icc.mp hb).1; omega
  have hpow : y ^ (Ω b) ≤ b := by
    rw [cardFactors_apply]
    calc
      y ^ b.primeFactorsList.length ≤ b.primeFactorsList.prod := by
        apply List.pow_card_le_prod
        intro p hp
        have hprime := Nat.prime_of_mem_primeFactorsList hp
        have hdvd := Nat.dvd_of_mem_primeFactorsList hp
        have hlarge : ¬ p ≤ y := fun h => hrough p hprime h hdvd
        omega
      _ = b := Nat.prod_primeFactorsList hb0
  by_contra hK
  have hexp : K + 1 ≤ Ω b := by omega
  have hpow' : y ^ (K + 1) ≤ y ^ (Ω b) := Nat.pow_le_pow_right (by omega) hexp
  have hbN := (Finset.mem_Icc.mp hb).2
  omega

/-- Arithmetic extraction used in the reduction of Erdős Problem 535. -/
theorem arithmetic_extraction (N y L K : ℕ) (hy : 2 ≤ y)
    (hNL : N < 2 ^ L) (hNK : N < y ^ (K + 1))
    (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) :
    ∃ (s k : ℕ) (B : Finset ℕ), 0 < s ∧ k ≤ K ∧ Erdos535.AllBigOmega k B ∧
      A.card ≤ (L + 1) ^ y * (K + 1) * B.card ∧ ∀ b ∈ B, s * b ∈ A := by
  classical
  obtain ⟨s, C, hs, hC, hcard, hscale, hrough⟩ := extract_rough_family N L hNL A hA y
  have hΩ : ∀ b ∈ C, Ω b ≤ K := by
    intro b hb
    exact omega_le_of_rough hy hNK (hC hb) (fun p hp hpy => hrough p hp hpy b hb)
  obtain ⟨k, hk, hkfiber⟩ := exists_large_fiber C (fun b => Ω b) K hΩ
  let B := C.filter fun b => Ω b = k
  refine ⟨s, k, B, hs, hk, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨hbC, hbΩ⟩ := Finset.mem_filter.mp hb
    exact ⟨(Finset.mem_Icc.mp (hC hbC)).1, hbΩ⟩
  · calc
      A.card ≤ (L + 1) ^ y * C.card := hcard
      _ ≤ (L + 1) ^ y * ((K + 1) * B.card) := Nat.mul_le_mul_left _ hkfiber
      _ = (L + 1) ^ y * (K + 1) * B.card := (Nat.mul_assoc _ _ _).symm
  · intro b hb
    exact hscale b (Finset.mem_filter.mp hb).1

end OMA535Extraction

theorem OMA.solution : OMA.R_Erdos535_erdos_535_R1.H2 := by
  exact OMA535Extraction.arithmetic_extraction
