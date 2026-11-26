import Mathlib

/-- For every positive modulus W and every W-periodic nonnegative baseline u,
there is a synthetic weight f with 0 <= f <= 8 u whose progression averages
track u up to a bounded discrepancy, while every dyadic pair has zero product. -/

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

private lemma mask_exists (W : ℕ) (hW : 0 < W) :
    ∃ M : ℕ, 1 < M ∧ Nat.Coprime W M ∧
      ∃ S : Finset ℕ, S ⊆ Finset.range M ∧ M ≤ 8 * S.card ∧
        ∀ (a b k : ℕ), a ∈ S → b ∈ S → (a + b) % M ≠ (2 ^ k) % M := by
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

section Counting

/-- The residue map `j ↦ (x + jW) mod M` is injective on one full period. -/
private lemma progression_residue_injOn {W M : ℕ} (hcop : Nat.Coprime W M) (x : ℕ) :
    Set.InjOn (fun j : ℕ => (x + j * W) % M) ↑(Finset.range M) := by
  intro j1 hj1 j2 hj2 h
  have hmod : x + j1 * W ≡ x + j2 * W [MOD M] := h
  have hc : j1 * W ≡ j2 * W [MOD M] :=
    Nat.ModEq.add_left_cancel (Nat.ModEq.refl x) hmod
  have hmc : M.gcd W = 1 := by
    rw [Nat.gcd_comm]
    exact (Nat.coprime_iff_gcd_eq_one).mp hcop
  have hc' : j1 ≡ j2 [MOD M] := Nat.ModEq.cancel_right_of_coprime hmc hc
  exact Nat.ModEq.eq_of_lt_of_lt hc' (Finset.mem_range.mp hj1) (Finset.mem_range.mp hj2)

/-- One full period contains exactly `S.card` hits. -/
private lemma progression_period_card {W M : ℕ} (hM : 0 < M) (hcop : Nat.Coprime W M)
    (S : Finset ℕ) (hS_sub : S ⊆ Finset.range M) (x : ℕ) :
    ((Finset.range M).filter (fun j => (x + j * W) % M ∈ S)).card = S.card := by
  let i : ℕ → ℕ := fun j => (x + j * W) % M
  have hi_inj : Set.InjOn i ↑(Finset.range M) := progression_residue_injOn hcop x
  have himg_sub : Finset.image i (Finset.range M) ⊆ Finset.range M := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨j, -, rfl⟩
    exact Finset.mem_range.mpr (Nat.mod_lt _ hM)
  have himg_eq : Finset.image i (Finset.range M) = Finset.range M := by
    apply Finset.eq_of_subset_of_card_le himg_sub
    rw [Finset.card_image_of_injOn hi_inj]
  refine Finset.card_bij (fun j _ => i j) ?_ ?_ ?_
  · intro j hj
    exact (Finset.mem_filter.mp hj).2
  · intro j1 hj1 j2 hj2 h
    exact hi_inj (Finset.mem_filter.mp hj1).1 (Finset.mem_filter.mp hj2).1 h
  · intro s hs
    have hs_range : s ∈ Finset.range M := hS_sub hs
    have hs_img : s ∈ Finset.image i (Finset.range M) := by
      rw [himg_eq]
      exact hs_range
    rcases Finset.mem_image.mp hs_img with ⟨j, hj, hji⟩
    refine ⟨j, Finset.mem_filter.mpr ⟨hj, ?_⟩, hji⟩
    change i j ∈ S
    rw [hji]
    exact hs

/-- Adding one full period adds exactly `S.card` hits. -/
private lemma progression_count_add_period {W M : ℕ} (hM : 0 < M) (hcop : Nat.Coprime W M)
    (S : Finset ℕ) (hS_sub : S ⊆ Finset.range M) (x H : ℕ) :
    Nat.count (fun j => (x + j * W) % M ∈ S) (H + M)
      = Nat.count (fun j => (x + j * W) % M ∈ S) H + S.card := by
  rw [Nat.count_add]
  congr 1
  rw [Nat.count_eq_card_filter_range]
  have harg : ∀ k, x + (H + k) * W = (x + H * W) + k * W := by
    intro k; ring
  simp only [harg]
  exact progression_period_card hM hcop S hS_sub (x + H * W)

/-- An initial segment of a period contains at most `S.card` hits. -/
private lemma progression_initial_count_le_card {W M : ℕ} (_hM : 0 < M) (hcop : Nat.Coprime W M)
    (S : Finset ℕ) (_hS_sub : S ⊆ Finset.range M) (x r : ℕ) (hr : r ≤ M) :
    Nat.count (fun j => (x + j * W) % M ∈ S) r ≤ S.card := by
  rw [Nat.count_eq_card_filter_range]
  let T := (Finset.range r).filter (fun j => (x + j * W) % M ∈ S)
  have hT_sub_M : T ⊆ Finset.range M := by
    intro j hj
    exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp (Finset.mem_filter.mp hj).1) hr)
  have hT_inj : Set.InjOn (fun j : ℕ => (x + j * W) % M) ↑T :=
    (progression_residue_injOn hcop x).mono (by intro j hj; exact hT_sub_M hj)
  have himg_sub : Finset.image (fun j : ℕ => (x + j * W) % M) T ⊆ S := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
    exact (Finset.mem_filter.mp hj).2
  calc T.card = (Finset.image (fun j : ℕ => (x + j * W) % M) T).card :=
        (Finset.card_image_of_injOn hT_inj).symm
    _ ≤ S.card := Finset.card_le_card himg_sub

/-- An initial segment of a period contains at most its own length many hits. -/
private lemma progression_initial_count_le_length {W M : ℕ} (S : Finset ℕ) (x r : ℕ) :
    Nat.count (fun j => (x + j * W) % M ∈ S) r ≤ r := by
  rw [Nat.count_eq_card_filter_range]
  calc ((Finset.range r).filter (fun j => (x + j * W) % M ∈ S)).card
      ≤ (Finset.range r).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = r := Finset.card_range r

/-- The count over `q` full periods plus an initial segment. -/
private lemma progression_count_mul_add {W M : ℕ} (hM : 0 < M) (hcop : Nat.Coprime W M)
    (S : Finset ℕ) (hS_sub : S ⊆ Finset.range M) (x q r : ℕ) :
    Nat.count (fun j => (x + j * W) % M ∈ S) (q * M + r)
      = q * S.card + Nat.count (fun j => (x + j * W) % M ∈ S) r := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [show (q + 1) * M + r = (q * M + r) + M by ring]
      rw [progression_count_add_period hM hcop S hS_sub x (q * M + r), ih]
      ring

end Counting

/-- The fixed-modulus countermodel.  For every `W` and every `W`-periodic
nonnegative baseline `u`, there is a synthetic weight `f` with `0 ≤ f ≤ 8u`
whose progression averages track `u` up to a bounded discrepancy, while every
pair of positive-weight entries summing to a power of two is killed. -/


theorem PEqualNP.Outside.L_goldbach_dyadic_progression_countermodel :
    ∀ W : ℕ, 0 < W →
      ∀ u : ℕ → ℝ, (∀ x, 0 ≤ u x) → (∀ x, u (x + W) = u x) →
        ∃ (f : ℕ → ℝ) (C : ℝ), 0 < C ∧
          (∀ x, 0 ≤ f x ∧ f x ≤ 8 * u x) ∧
          (∀ x H : ℕ,
            |(∑ j ∈ Finset.range H, f (x + j * W)) - (H : ℝ) * u x| ≤ C * u x) ∧
          ∀ a b k : ℕ, a + b = 2 ^ k → f a * f b = 0 := by
  intro W hW u hu_nonneg hu_period
  obtain ⟨M, hM1, hcop, S, hS_sub, hS_dens, hS_avoid⟩ := mask_exists W hW
  have hMpos : 0 < M := by omega
  have hScard_pos : 0 < S.card := by
    by_contra h
    have hzero : S.card = 0 := by omega
    rw [hzero, Nat.mul_zero] at hS_dens
    omega
  let c : ℝ := (M : ℝ) / (S.card : ℝ)
  let f : ℕ → ℝ := fun x => if x % M ∈ S then u x * c else 0
  have hc_pos : 0 < c := by
    dsimp [c]
    exact div_pos (by exact_mod_cast hMpos) (by exact_mod_cast hScard_pos)
  have hc_le : c ≤ 8 := by
    have hcard : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hScard_pos
    have hMle : (M : ℝ) ≤ 8 * (S.card : ℝ) := by exact_mod_cast hS_dens
    dsimp [c]
    rw [div_le_iff₀ hcard]
    linarith
  have hcS : c * (S.card : ℝ) = (M : ℝ) := by
    dsimp [c]
    exact div_mul_cancel₀ (M : ℝ) (by exact_mod_cast (ne_of_gt hScard_pos))
  have hu_mul : ∀ x j : ℕ, u (x + j * W) = u x := by
    intro x j
    induction j with
    | zero => simp
    | succ j ih =>
        have hstep : x + (j + 1) * W = (x + j * W) + W := by ring
        rw [hstep, hu_period, ih]
  refine ⟨f, (M : ℝ), by exact_mod_cast hMpos, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x % M ∈ S
    · simp only [f, hx, ite_true]
      refine ⟨mul_nonneg (hu_nonneg x) hc_pos.le, ?_⟩
      nlinarith [hu_nonneg x, hc_le]
    · simp only [f, hx, ite_false]
      exact ⟨le_refl 0, by nlinarith [hu_nonneg x]⟩
  · intro x H
    let p : ℕ → Prop := fun j => (x + j * W) % M ∈ S
    let N : ℕ := Nat.count p H
    have hNdef : N = ((Finset.range H).filter p).card := Nat.count_eq_card_filter_range p H
    have hsum : (∑ j ∈ Finset.range H, f (x + j * W)) = u x * c * (N : ℝ) := by
      calc
        (∑ j ∈ Finset.range H, f (x + j * W))
            = ∑ j ∈ Finset.range H, if p j then u x * c else 0 := by
              apply Finset.sum_congr rfl
              intro j hj
              have hux : u (x + j * W) = u x := hu_mul x j
              simp [f, p, hux]
        _ = ∑ j ∈ (Finset.range H).filter p, u x * c := by
              exact (Finset.sum_filter p (fun _ => u x * c)).symm
        _ = (N : ℝ) * (u x * c) := by
              rw [Finset.sum_const, nsmul_eq_mul, ← hNdef]
        _ = u x * c * (N : ℝ) := by ring
    have hbound : |c * (N : ℝ) - (H : ℝ)| ≤ (M : ℝ) := by
      let q := H / M
      let r := H % M
      have hH : H = q * M + r := by
        dsimp [q, r]
        rw [mul_comm]
        exact (Nat.div_add_mod H M).symm
      have hr : r < M := by
        dsimp [r]
        exact Nat.mod_lt H hMpos
      have hNdecomp : N = q * S.card + Nat.count p r := by
        dsimp [N]
        rw [hH]
        exact progression_count_mul_add hMpos hcop S hS_sub x q r
      have hNr_card : Nat.count p r ≤ S.card :=
        progression_initial_count_le_card hMpos hcop S hS_sub x r (le_of_lt hr)
      have hNr_len : Nat.count p r ≤ r := progression_initial_count_le_length S x r
      have hcN : c * (Nat.count p r : ℝ) ≤ (M : ℝ) := by
        have hcast : (Nat.count p r : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hNr_card
        have hmul := mul_le_mul_of_nonneg_left hcast hc_pos.le
        rwa [hcS] at hmul
      have hcN_nonneg : 0 ≤ c * (Nat.count p r : ℝ) :=
        mul_nonneg hc_pos.le (Nat.cast_nonneg _)
      have hq : c * ((q : ℝ) * (S.card : ℝ)) = (q : ℝ) * (M : ℝ) := by
        rw [← hcS]
        ring
      have hD : c * (N : ℝ) - (H : ℝ) = c * (Nat.count p r : ℝ) - (r : ℝ) := by
        rw [hNdecomp, hH]
        push_cast
        linarith
      have hD1 : c * (N : ℝ) - (H : ℝ) ≤ (M : ℝ) := by
        rw [hD]
        linarith [hcN]
      have hD2 : -(M : ℝ) ≤ c * (N : ℝ) - (H : ℝ) := by
        rw [hD]
        have hrM : (r : ℝ) < (M : ℝ) := by exact_mod_cast hr
        linarith [hcN_nonneg]
      exact abs_le.mpr ⟨hD2, hD1⟩
    have hfac : u x * c * (N : ℝ) - (H : ℝ) * u x
        = u x * (c * (N : ℝ) - (H : ℝ)) := by ring
    rw [hsum, hfac, abs_mul, abs_of_nonneg (hu_nonneg x)]
    calc u x * |c * (N : ℝ) - (H : ℝ)| ≤ u x * (M : ℝ) :=
          mul_le_mul_of_nonneg_left hbound (hu_nonneg x)
      _ = (M : ℝ) * u x := by ring
  · intro a b k hsum
    by_contra hne
    have ha_ne : f a ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have hb_ne : f b ≠ 0 := fun h => hne (by rw [h, mul_zero])
    have haS : a % M ∈ S := by
      by_contra hmem
      exact ha_ne (by simp [f, hmem])
    have hbS : b % M ∈ S := by
      by_contra hmem
      exact hb_ne (by simp [f, hmem])
    have hbad := hS_avoid (a % M) (b % M) k haS hbS
    apply hbad
    rw [← Nat.add_mod, hsum]
