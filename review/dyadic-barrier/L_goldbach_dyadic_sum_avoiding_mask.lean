import Mathlib

/-- For every positive modulus W there is a modulus M coprime to W and a
residue set S of density at least 1/8 whose pairwise sums avoid every power
of two. -/

private lemma modEq_one_of_dvd_sub_one {a n m : ℕ} (hm : 1 < m) (ha : 1 ≤ a ^ n)
    (h : m ∣ a ^ n - 1) : a ^ n ≡ 1 [MOD m] := by
  rw [Nat.ModEq]
  have h1 : 1 % m = 1 := Nat.mod_eq_of_lt hm
  rw [h1]
  have hdecomp : a ^ n = (a ^ n - 1) + 1 := (Nat.sub_add_cancel ha).symm
  rw [hdecomp, Nat.add_mod, Nat.dvd_iff_mod_eq_zero.mp h]
  simp [Nat.mod_eq_of_lt hm]

/-- Every prime divisor of `2^s - 1` is congruent to `1` modulo `s`, hence is
larger than any `W < s`.  Therefore `W` and `2^s - 1` are coprime. -/
private lemma coprime_pow_sub_one {W s : ℕ} (hW : 0 < W) (hsp : Nat.Prime s)
    (hWs : W < s) : Nat.Coprime W (2 ^ s - 1) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  have hgpos : 0 < Nat.gcd W (2 ^ s - 1) := Nat.gcd_pos_of_pos_left _ hW
  have hg1 : 1 < Nat.gcd W (2 ^ s - 1) := by
    have h1 : 1 ≤ Nat.gcd W (2 ^ s - 1) := Nat.one_le_iff_ne_zero.mpr (by omega)
    omega
  let p := Nat.minFac (Nat.gcd W (2 ^ s - 1))
  have hp : Nat.Prime p := Nat.minFac_prime (by omega)
  have hpdvd : p ∣ Nat.gcd W (2 ^ s - 1) := Nat.minFac_dvd _
  have hpW : p ∣ W := hpdvd.trans (Nat.gcd_dvd_left _ _)
  have hpM : p ∣ 2 ^ s - 1 := hpdvd.trans (Nat.gcd_dvd_right _ _)
  have hp_le_W : p ≤ W := Nat.le_of_dvd hW hpW
  have hp_lt_s : p < s := lt_of_le_of_lt hp_le_W hWs
  have hspos : 0 < s := hsp.pos
  have hp_ne_two : p ≠ 2 := by
    intro hp2
    have h2dvd : 2 ∣ 2 ^ s - 1 := by simpa [hp2] using hpM
    have hle : 1 ≤ 2 ^ s := Nat.one_le_pow s 2 (by norm_num)
    have heven : Even (2 ^ s) := Nat.even_pow.mpr ⟨even_two, by omega⟩
    have hodd : Odd (2 ^ s - 1) := Nat.Even.sub_odd hle heven odd_one
    have h0 : (2 ^ s - 1) % 2 = 0 := Nat.dvd_iff_mod_eq_zero.mp h2dvd
    have h1 : (2 ^ s - 1) % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  have hp_not_dvd_two : ¬ p ∣ 2 := by
    intro h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
    have hge : 2 ≤ p := hp.two_le
    have hp2 : p = 2 := by omega
    exact hp_ne_two hp2
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h
    exact hp_not_dvd_two ((ZMod.natCast_eq_zero_iff 2 p).mp h)
  letI : Fact p.Prime := ⟨hp⟩
  have hsmod : 2 ^ s ≡ 1 [MOD p] :=
    modEq_one_of_dvd_sub_one hp.one_lt (Nat.one_le_pow s 2 (by norm_num)) hpM
  have hd1 : orderOf (2 : ZMod p) ∣ s := by
    rw [orderOf_dvd_iff_pow_eq_one]
    have hcast : ((2 : ZMod p) ^ s) = ((2 ^ s : ℕ) : ZMod p) := by
      rw [Nat.cast_pow]
      norm_num
    rw [hcast]
    simpa using (ZMod.natCast_eq_natCast_iff (2 ^ s) 1 p).mpr hsmod
  have hd2 : orderOf (2 : ZMod p) ∣ p - 1 := ZMod.orderOf_dvd_card_sub_one h2ne
  have hdvd : orderOf (2 : ZMod p) ∣ Nat.gcd s (p - 1) := Nat.dvd_gcd hd1 hd2
  have hcop_sp : Nat.Coprime s (p - 1) := by
    rw [hsp.coprime_iff_not_dvd]
    intro hd
    have hp2 : 2 ≤ p := hp.two_le
    have hpos : 0 < p - 1 := by omega
    have hle : s ≤ p - 1 := Nat.le_of_dvd hpos hd
    omega
  have hgcd1 : Nat.gcd s (p - 1) = 1 := (Nat.coprime_iff_gcd_eq_one).mp hcop_sp
  have horder1 : orderOf (2 : ZMod p) = 1 :=
    Nat.eq_one_of_dvd_one (by simpa [hgcd1] using hdvd)
  have h2eq1 : (2 : ZMod p) = 1 := orderOf_eq_one_iff.mp horder1
  have h1zero : (1 : ZMod p) = 0 := by
    have hsub : (2 : ZMod p) - 1 = 0 := sub_eq_zero.mpr h2eq1
    norm_num at hsub
  have hp_dvd_one : p ∣ 1 := (ZMod.natCast_eq_zero_iff 1 p).mp (by simpa using h1zero)
  have hp_one : p = 1 := Nat.eq_one_of_dvd_one hp_dvd_one
  have hp2 : 2 ≤ p := hp.two_le
  omega

/-- For every positive `W` there is a modulus `M` coprime to `W` and a residue
set `S` of density at least `1/8` whose pairwise sums avoid every power of two. -/

theorem PEqualNP.Outside.L_goldbach_dyadic_sum_avoiding_mask :
    ∀ W : ℕ, 0 < W →
      ∃ M : ℕ, 1 < M ∧ Nat.Coprime W M ∧
        ∃ S : Finset ℕ, S ⊆ Finset.range M ∧ M ≤ 8 * S.card ∧
          ∀ (a b k : ℕ), a ∈ S → b ∈ S → (a + b) % M ≠ (2 ^ k) % M := by
  intro W hW
  obtain ⟨s, hs_ge, hs_prime⟩ := Nat.exists_infinite_primes (max W 5 + 1)
  have hs_gt_W : W < s := by omega
  have hs_gt_5 : 5 < s := by omega
  have hs3 : 3 ≤ s := by omega
  let L : ℕ := 2 ^ (s - 3)
  let M : ℕ := 8 * L - 1
  have hL_ge : 8 ≤ L := by
    have h3 : 3 ≤ s - 3 := by omega
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (s - 3) := Nat.pow_le_pow_right (by norm_num) h3
      _ = L := rfl
  have hM_eq : M = 2 ^ s - 1 := by
    have hpow : 8 * L = 2 ^ s := by
      calc 8 * L = 2 ^ 3 * 2 ^ (s - 3) := by rw [show (8 : ℕ) = 2 ^ 3 by norm_num]
        _ = 2 ^ (s - 3) * 2 ^ 3 := by rw [mul_comm]
        _ = 2 ^ s := Nat.pow_sub_mul_pow 2 hs3
    omega
  have hM_gt_one : 1 < M := by omega
  let S : Finset ℕ := Finset.Ico (3 * L) (4 * L)
  have hS_subset : S ⊆ Finset.range M := by
    intro x hx
    simp only [S, Finset.mem_Ico] at hx
    simp only [Finset.mem_range]
    omega
  have hS_card : S.card = L := by
    simp only [S]
    rw [Nat.card_Ico]
    omega
  have hS_density : M ≤ 8 * S.card := by
    rw [hS_card]
    omega
  have hcop : Nat.Coprime W M := by
    rw [hM_eq]
    exact coprime_pow_sub_one hW hs_prime hs_gt_W
  refine ⟨M, hM_gt_one, hcop, S, hS_subset, hS_density, ?_⟩
  intro a b k ha hb
  simp only [S, Finset.mem_Ico] at ha hb
  have hsum_lt_M : a + b < M := by omega
  have hsum_mod : (a + b) % M = a + b := Nat.mod_eq_of_lt hsum_lt_M
  have hspos : 0 < s := by omega
  have hs_mod : 2 ^ s ≡ 1 [MOD M] := by
    apply modEq_one_of_dvd_sub_one hM_gt_one (Nat.one_le_pow s 2 (by norm_num))
    rw [hM_eq]
  have hk_decomp : k = s * (k / s) + k % s := (Nat.div_add_mod k s).symm
  have hpow_decomp : 2 ^ k = (2 ^ s) ^ (k / s) * 2 ^ (k % s) := by
    conv_lhs => rw [hk_decomp]
    rw [pow_add, pow_mul]
  have hmod_eq : 2 ^ k ≡ 2 ^ (k % s) [MOD M] := by
    rw [hpow_decomp]
    simpa using (hs_mod.pow (k / s)).mul (Nat.ModEq.refl (2 ^ (k % s)))
  have hklt : k % s < s := Nat.mod_lt k hspos
  have hkle : k % s ≤ s - 1 := by omega
  have hle_pow : 2 ^ (k % s) ≤ 2 ^ (s - 1) :=
    Nat.pow_le_pow_right (by norm_num) hkle
  have h4L : 2 ^ (s - 1) = 4 * L := by
    have hsp1 : s - 1 = (s - 3) + 2 := by omega
    rw [hsp1, pow_add, show (2 : ℕ) ^ 2 = 4 by norm_num]
    simp [L, mul_comm]
  have hpow_le : 2 ^ (k % s) ≤ 4 * L := by
    rw [← h4L]
    exact hle_pow
  have hltM : 2 ^ (k % s) < M := by omega
  have hmod_small : (2 ^ (k % s)) % M = 2 ^ (k % s) := Nat.mod_eq_of_lt hltM
  have hmods : (2 ^ k) % M = (2 ^ (k % s)) % M := hmod_eq
  rw [hsum_mod, hmods, hmod_small]
  omega
